"""
Бот, который раз в час собирает новости из источников (sources.txt),
отбирает их по словам (keywords.txt) и шлёт в Telegram-канал
в формате «Заголовок — ссылка».

Запуск: python bot.py          — обычная работа
        python bot.py --dry    — ничего не отправлять, показать, что нашлось бы
        python bot.py --check  — проверить источники: что открылось, что нет
"""

import hashlib
import html
import json
import os
import re
import sys
import time
import warnings
from calendar import timegm
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from pathlib import Path
from urllib.parse import urljoin, urlsplit, urlunsplit, parse_qsl, urlencode

import feedparser
import requests
from bs4 import BeautifulSoup, MarkupResemblesLocatorWarning

warnings.filterwarnings("ignore", category=MarkupResemblesLocatorWarning)

# ---------- Настройки ----------
# Брать новости не старше стольких часов
MAX_AGE_HOURS = 24
# Когда источник появился впервые: присылать из него новости только за последние
# N часов, остальное просто запомнить, чтобы не завалить канал
NEW_SOURCE_HOURS = 2
# True — каждая новость отдельным сообщением; False — одна подборка за час
ONE_MESSAGE_PER_NEWS = False
# Как часто отправлять подборку в канал, минут. Собирает бот чаще —
# как часто, задаётся расписанием в .github/workflows/main.yml
POST_EVERY_MINUTES = 60
# Склеивать похожие заголовки из разных изданий (одно событие — одна ссылка)
MERGE_SIMILAR = True
# Сколько ссылок помнить, чтобы не присылать повторы
SEEN_LIMIT = 60000
# --------------------------------

BASE = Path(__file__).parent
SOURCES_FILE = BASE / "sources.txt"
KEYWORDS_FILE = BASE / "keywords.txt"
CONTESTS_FILE = BASE / "contests.txt"
CONTEST_MARK = "📷 "
STATE_FILE = BASE / "state" / "seen.json"

HEADERS = {
    "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
                  "(KHTML, like Gecko) Chrome/129.0 Safari/537.36",
    "Accept-Language": "ru-RU,ru;q=0.9,en;q=0.8",
}
TIMEOUT = 12


# ---------- Файлы с настройками ----------

def read_lines(path):
    if not path.exists():
        return []
    lines = []
    for raw in path.read_text(encoding="utf-8").splitlines():
        line = raw.strip()
        if line and not line.startswith("#"):
            lines.append(line)
    return lines


def parse_source(line):
    """Строка из sources.txt -> (адрес, правило).
    Правила: "+" в начале — брать всё без фильтра; "📷" — брать только
    фотоконкурсы; без значка — через фильтр по словам."""
    rule = "filter"
    if line.startswith("+"):
        rule, line = "all", line[1:].strip()
    elif line.startswith("📷"):
        rule, line = "photo", line[len("📷"):].strip()
    m = re.search(r"https?://\S+", line)
    target = m.group(0) if m else line.split()[-1]
    return target, rule


def norm(text):
    return (text or "").lower().replace("ё", "е")


def load_keywords(path=KEYWORDS_FILE):
    """Возвращает (нужные, исключающие) — списки regex."""
    include, exclude = [], []
    for line in read_lines(path):
        target = include
        if line.startswith("-"):
            target = exclude
            line = line[1:].strip()
        if not line:
            continue
        if line.lower().startswith("re:"):
            # Для продвинутых: регулярное выражение как есть
            target.append(re.compile(line[3:].strip(), re.I))
            continue
        exact = len(line) >= 2 and line[0] == line[-1] == '"'
        words = norm(line.strip('"')).split()
        if exact:
            # В кавычках — только целые слова: "рак" не найдёт «ракета»
            pattern = r"(?<!\w)" + r"\s+".join(map(re.escape, words)) + r"(?!\w)"
        else:
            # Каждое слово ищется по началу: «красн книг» найдёт «Красную книгу»
            pattern = r"\s+".join(r"(?<!\w)" + re.escape(w) + r"\w*" for w in words)
        target.append(re.compile(pattern))
    return include, exclude


def passes(text, include, exclude, take_all):
    t = norm(text)
    if any(p.search(t) for p in exclude):
        return False
    if take_all or not include:
        return True
    return any(p.search(t) for p in include)


def is_contest(text, contests, exclude):
    t = norm(text)
    return bool(contests) and not any(p.search(t) for p in exclude) \
        and any(p.search(t) for p in contests)


# ---------- Память бота ----------

TRASH_PARAMS = ("utm_", "from", "yclid", "fbclid", "gclid", "ref", "page", "nick", "adt_")


def clean_link(url):
    """Убирает utm-метки и прочий мусор, чтобы одна новость не пришла дважды."""
    try:
        parts = urlsplit(url.strip())
        query = [(k, v) for k, v in parse_qsl(parts.query)
                 if not k.lower().startswith(TRASH_PARAMS)]
        host = parts.netloc.lower()
        if host.startswith("www."):
            host = host[4:]
        return urlunsplit(("https", host, parts.path.rstrip("/"), urlencode(query), ""))
    except Exception:
        return url.strip()


def key_of(text):
    return hashlib.sha1(text.encode("utf-8")).hexdigest()[:14]


def load_state():
    try:
        data = json.loads(STATE_FILE.read_text(encoding="utf-8"))
    except Exception:
        data = {}
    return {"links": data.get("links", []),
            "sources": set(data.get("sources", [])),
            "pending": data.get("pending", []),
            "titles": data.get("titles", []),
            "last_post": data.get("last_post", 0)}


def save_state(state):
    STATE_FILE.parent.mkdir(exist_ok=True)
    cutoff = time.time() - 48 * 3600
    STATE_FILE.write_text(json.dumps({
        "links": state["links"][-SEEN_LIMIT:],
        "sources": sorted(state["sources"]),
        "pending": state["pending"],
        "titles": [t for t in state["titles"] if t[0] > cutoff][-5000:],
        "last_post": state["last_post"],
    }, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")


# ---------- Похожие заголовки ----------

def _stem(w):
    return w[:5] if len(w) > 5 else w[:4]


# Слова-шаблоны, которые встречаются в заголовках о самом разном
STOP_WORDS = """что такое зачем почему куда сдать нужна нужно можно какие какой каких кто это
этого этот эта эти этой его её них они она оно было были будет будут стал стала стали
стало после перед около более менее через также тоже только даже уже ещё всех всего
весь вся свои своих свою которые который которая которых когда тогда если чтобы
самые самых самый самая очень много новый новые новых новая история суть интересные
интересных факты фактов факта причины последствия решения проблемы проблема способы
способов идей идеи советы совета мифов мифы чек-лист инструкция подборка подборку
лучшие лучших главные главное рассказал рассказали заявил заявили сообщил сообщили
назвал назвали выяснили выяснил считают стоит пройдёт пройдет прошёл прошла прошли
день международный всемирный года году годы январь января февраль февраля март
марта апрель апреля мая июнь июня июль июля август августа сентябрь сентября
октябрь октября ноябрь ноября декабрь декабря россии россия российские российских
москве москвы москва мире мира время время""".split()
STOP_STEMS = {_stem(norm(w)) for w in STOP_WORDS if len(w) >= 4}


def title_signature(title):
    """Набор «корней» значимых слов: «Анапы» и «Анапе» дают одно и то же."""
    words = re.findall(r"\w+", norm(title))
    return sorted({_stem(w) for w in words
                   if len(w) >= 4 and not w.isdigit() and _stem(w) not in STOP_STEMS})


def is_similar(sig, other):
    a, b = set(sig), set(other)
    if not a or not b:
        return False
    common = len(a & b)
    return common >= 3 and common / len(a | b) >= 0.5


# ---------- Сбор новостей ----------

CERTS_DIR = BASE / "certs"
_ru_bundle = None


def russian_ca_bundle():
    """Российские госсайты и банки работают на сертификатах Минцифры, которых
    нет в стандартном списке. Для них собираем список доверенных сертификатов
    с добавленным корневым сертификатом Минцифры (его скачивает расписание)."""
    global _ru_bundle
    if _ru_bundle is None:
        import certifi
        extra = sorted(CERTS_DIR.glob("*.crt")) if CERTS_DIR.exists() else []
        if not extra:
            _ru_bundle = ""
        else:
            bundle = CERTS_DIR / "bundle.pem"
            bundle.write_text(Path(certifi.where()).read_text() + "\n" +
                              "\n".join(f.read_text() for f in extra))
            _ru_bundle = str(bundle)
    return _ru_bundle


def fetch(url, **kw):
    try:
        r = requests.get(url, headers=HEADERS, timeout=TIMEOUT, **kw)
    except requests.exceptions.SSLError:
        bundle = russian_ca_bundle()
        if not bundle:
            raise
        r = requests.get(url, headers=HEADERS, timeout=TIMEOUT, verify=bundle, **kw)
    r.raise_for_status()
    if "charset" not in r.headers.get("content-type", "").lower():
        r.encoding = r.apparent_encoding
    return r


def strip_html(text):
    return html.unescape(BeautifulSoup(text or "", "html.parser").get_text(" ")).strip()


def short_title(text, limit=160):
    first = next((l.strip() for l in (text or "").splitlines() if l.strip()), "")
    return first if len(first) <= limit else first[:limit - 3].rstrip() + "…"


def entry_time(entry):
    for field in ("published_parsed", "updated_parsed"):
        value = entry.get(field)
        if value:
            return timegm(value)
    return None


def items_from_parsed_feed(feed, base_url):
    items = []
    for e in feed.entries:
        link, title = e.get("link"), strip_html(e.get("title", ""))
        if link:
            link = urljoin(base_url, link)  # у некоторых лент ссылки относительные
        if not link or not title:
            continue
        cats = " ".join(t.get("term", "") for t in e.get("tags", []) or [])
        items.append({"title": title, "link": link,
                      "text": f"{title} {strip_html(e.get('summary', ''))} {cats}",
                      "time": entry_time(e)})
    return items


def find_feed_in_html(page_url, soup):
    for link in soup.find_all("link", rel=lambda v: v and "alternate" in v):
        kind = (link.get("type") or "").lower()
        if ("rss" in kind or "atom" in kind) and link.get("href"):
            return urljoin(page_url, link["href"])
    return None


def base_domain(host):
    host = host.lower().split(":")[0]
    if host.startswith("www."):
        host = host[4:]
    parts = host.split(".")
    if len(parts) >= 3 and parts[-2] in ("co", "com", "org", "gov", "ac", "net"):
        return ".".join(parts[-3:])
    return ".".join(parts[-2:])


def looks_like_article(url, page_url):
    parts = urlsplit(url)
    if parts.scheme not in ("http", "https"):
        return False
    if base_domain(parts.netloc) != base_domain(urlsplit(page_url).netloc):
        return False
    path = parts.path.rstrip("/")
    if clean_link(url) == clean_link(page_url) or not path:
        return False
    if re.search(r"\.(jpg|jpeg|png|gif|pdf|zip|mp3|mp4)$", path, re.I):
        return False
    if re.search(r"/(tag|tags|tema|topic|author|authors|search|login|about|contacts?|"
                 r"subscribe|subscription|advert|reklama|page)(/|$)", path, re.I):
        return False
    segments = [s for s in path.split("/") if s]
    last = segments[-1] if segments else ""
    has_digits = bool(re.search(r"\d{3,}", path))
    long_slug = len(last) >= 20 or last.count("-") >= 3
    return has_digits or (len(segments) >= 2 and long_slug)


def items_from_page(page_url, soup):
    """Сайт без RSS: берём со страницы ссылки, похожие на статьи."""
    scope = soup.find("main") or soup.body or soup
    for junk in scope.find_all(["header", "nav", "footer", "script", "style", "noscript"]):
        junk.decompose()
    items, seen = [], set()
    for a in scope.find_all("a", href=True):
        url = urljoin(page_url, a["href"])
        # Если внутри ссылки есть заголовок — берём его, без рубрики и даты карточки
        inner = a.find(["h1", "h2", "h3", "h4", "h5"])
        source = inner if inner and len(inner.get_text(strip=True)) >= 15 else a
        text = re.sub(r"\s+", " ", source.get_text(" ")).strip()
        if not text:
            heading = a.find_parent(["h1", "h2", "h3", "h4"])
            text = heading.get_text(" ").strip() if heading else ""
        # Хвосты карточек: «Подробнее», время «12:12»
        text = re.sub(r"\s*(Подробнее|Читать далее|Read more)\s*$", "", text, flags=re.I)
        text = re.sub(r"\s+\d{1,2}:\d{2}$", "", text)
        if len(text) < 25 or len(text) > 300 or len(text.split()) < 4:
            continue
        if not looks_like_article(url, page_url):
            continue
        k = clean_link(url)
        if k in seen:
            continue
        seen.add(k)
        items.append({"title": short_title(text, 200), "link": url, "text": text, "time": None})
    return items


SITE_FEED = "RSS всего сайта"


def feed_fits_section(page_url, feed_url):
    """Дали адрес раздела (/esg), а на странице нашёлся RSS всего сайта?
    Тогда лучше брать ссылки со страницы раздела."""
    path = urlsplit(page_url).path.strip("/")
    if not path:
        return True
    return path.split("/")[0].lower() in feed_url.lower()


def items_from_url(url):
    """RSS -> RSS, найденный на странице -> ссылки со страницы."""
    r = fetch(url)
    feed = feedparser.parse(r.content)
    if feed.entries:
        return items_from_parsed_feed(feed, url), "RSS"
    soup = BeautifulSoup(r.content, "html.parser")
    feed_url = find_feed_in_html(url, soup)
    site_feed = None
    if feed_url:
        try:
            feed = feedparser.parse(fetch(feed_url).content)
            if feed.entries:
                found = items_from_parsed_feed(feed, feed_url)
                if feed_fits_section(url, feed_url):
                    return found, f"RSS ({feed_url})"
                site_feed = found  # лента всего сайта, а не раздела
        except Exception:
            pass
    items = items_from_page(url, soup)
    if not items and site_feed:
        return site_feed, f"{SITE_FEED} ({feed_url})"
    if not items:
        raise ValueError("на странице не нашлось ни RSS, ни ссылок на статьи "
                         "(возможно, сайт грузит новости скриптом или закрыт капчей)")
    return items, "страница"


def tg_channel_name(source):
    s = source.strip()
    if s.startswith("@"):
        return s[1:]
    m = re.match(r"^(?:https?://)?(?:www\.)?t(?:elegram)?\.me/(?:s/)?([A-Za-z0-9_]+)/?$", s)
    return m.group(1) if m else None


def items_from_telegram(channel):
    """Открытые Telegram-каналы читаем через веб-версию t.me/s/имя."""
    return parse_telegram_html(fetch(f"https://t.me/s/{channel}").text)


def parse_telegram_html(page):
    soup = BeautifulSoup(page, "html.parser")
    items = []
    for msg in soup.select("div.tgme_widget_message[data-post]"):
        if "service_message" in (msg.get("class") or []):
            continue  # «закрепил сообщение» и прочие служебные
        text_el = msg.select_one(".tgme_widget_message_text")
        if not text_el:
            continue
        for br in text_el.find_all("br"):
            br.replace_with("\n")
        text = text_el.get_text().strip()
        ts = None
        t = msg.select_one("time[datetime]")
        if t:
            try:
                ts = datetime.fromisoformat(t["datetime"]).timestamp()
            except ValueError:
                pass
        items.append({"title": short_title(text), "link": f"https://t.me/{msg['data-post']}",
                      "text": text, "time": ts})
    return items


def vk_group_name(source):
    m = re.match(r"^(?:https?://)?(?:www\.|m\.)?vk\.(?:com|ru)/([A-Za-z0-9_.]+)/?$", source.strip())
    return m.group(1) if m else None


def items_from_vk(domain):
    """Открытые сообщества ВКонтакте — через API, нужен сервисный ключ VK_TOKEN."""
    token = os.environ.get("VK_TOKEN")
    if not token:
        raise ValueError("не задан VK_TOKEN — ВКонтакте пропущен (см. README)")
    params = {"count": 20, "access_token": token, "v": "5.199"}
    m = re.match(r"^(?:club|public)(\d+)$", domain)
    if m:
        params["owner_id"] = -int(m.group(1))
    else:
        params["domain"] = domain
    data = requests.get("https://api.vk.com/method/wall.get", params=params,
                        timeout=TIMEOUT).json()
    if "error" in data:
        raise ValueError(f"VK: {data['error'].get('error_msg')}")
    items = []
    for post in data["response"]["items"]:
        text = post.get("text") or ""
        if not text and post.get("copy_history"):
            text = post["copy_history"][0].get("text") or ""
        text = re.sub(r"\[(?:club|public|id)\d+\|([^\]]+)\]", r"\1", text).strip()
        if not text:
            continue
        items.append({"title": short_title(text),
                      "link": f"https://vk.com/wall{post['owner_id']}_{post['id']}",
                      "text": text, "time": post.get("date")})
    return items


def read_source(target):
    channel = tg_channel_name(target)
    if channel:
        return items_from_telegram(channel), "Telegram"
    group = vk_group_name(target)
    if group:
        return items_from_vk(group), "ВКонтакте"
    return items_from_url(target)


# ---------- Отправка в Telegram ----------

def tg_send(token, chat_id, text):
    url = f"https://api.telegram.org/bot{token}/sendMessage"
    payload = {"chat_id": chat_id, "text": text,
               "link_preview_options": {"is_disabled": True}}
    for _ in range(5):
        r = requests.post(url, json=payload, timeout=TIMEOUT)
        if r.status_code == 429:
            time.sleep(r.json().get("parameters", {}).get("retry_after", 5) + 1)
            continue
        if not r.ok:
            raise RuntimeError(f"Telegram ответил {r.status_code}: {r.text}")
        return
    raise RuntimeError("Telegram не принял сообщение после нескольких попыток")


def build_messages(items):
    lines = [f"{it['title']} — {it['link']}" for it in items]
    if ONE_MESSAGE_PER_NEWS:
        return lines
    messages, current = [], ""
    for line in lines:
        candidate = (current + "\n\n" + line) if current else line
        if len(candidate) > 3900:
            messages.append(current)
            current = line
        else:
            current = candidate
    if current:
        messages.append(current)
    return messages


# ---------- Управление через Telegram ----------
# Администратор канала пишет боту в личку — бот меняет sources.txt и keywords.txt.

HELP_TEXT = """Что я умею. Пишите мне сюда, в личку.

Добавить источник — пришлите ссылку:
https://site.ru/rss
@имя_канала или https://t.me/имя_канала
https://vk.com/группа
Можно несколько ссылок, каждую с новой строки.
Можно просто переслать сюда пост из открытого канала.

+ ссылка — брать из источника всё, без фильтра по словам
📷 ссылка — брать только фотоконкурсы

/удалить ссылка — убрать источник
/источники — показать все источники

/слово корень — добавить слово в фильтр (например: /слово заповедн)
/минус слово — добавить исключение (например: /минус гороскоп)
/убрать слово — удалить слово или исключение из фильтра
/слова — показать слова фильтра

Я проверяю сообщения раз в 15 минут, поэтому отвечаю не сразу."""

BOT_MARK = "# --- Добавлено через бота ---"


def tg_api(token, method, **params):
    r = requests.post(f"https://api.telegram.org/bot{token}/{method}", json=params, timeout=TIMEOUT)
    data = r.json()
    if not data.get("ok"):
        raise RuntimeError(f"Telegram {method}: {data.get('description')}")
    return data["result"]


def reply(token, chat_id, text):
    for part in split_text(text):
        tg_api(token, "sendMessage", chat_id=chat_id, text=part,
               link_preview_options={"is_disabled": True})


def split_text(text, limit=3900):
    parts, cur = [], ""
    for line in text.split("\n"):
        if len(cur) + len(line) + 1 > limit:
            parts.append(cur)
            cur = ""
        cur = (cur + "\n" + line) if cur else line
    if cur:
        parts.append(cur)
    return parts


def append_line(path, line):
    text = path.read_text(encoding="utf-8") if path.exists() else ""
    if BOT_MARK not in text:
        text = text.rstrip("\n") + f"\n\n{BOT_MARK}\n"
    path.write_text(text.rstrip("\n") + "\n" + line + "\n", encoding="utf-8")


def remove_lines(path, match):
    """Удаляет из файла строки, для которых match(строка) истинно. Возвращает их."""
    lines = path.read_text(encoding="utf-8").splitlines()
    keep, removed = [], []
    for line in lines:
        s = line.strip()
        if s and not s.startswith("#") and match(s):
            removed.append(s)
        else:
            keep.append(line)
    if removed:
        path.write_text("\n".join(keep) + "\n", encoding="utf-8")
    return removed


def source_key(target):
    channel = tg_channel_name(target)
    if channel:
        return "tg:" + channel.lower()
    return clean_link(target).lower()


def describe_check(target, rule):
    """Проверяет источник сразу, чтобы ответить, работает ли он."""
    try:
        items, mode = read_source(target)
    except Exception as e:
        return False, f"не открылся: {e}"
    if not items:
        return False, "открылся, но новостей в нём не нашлось"
    sample = "\n".join(f"· {it['title']}" for it in items[:3])
    note = {"all": "беру всё, без фильтра", "photo": "беру только фотоконкурсы",
            "filter": "беру через фильтр по словам"}[rule]
    return True, f"способ: {mode}, записей сейчас: {len(items)}, {note}\n{sample}"


def cmd_add(lines_in):
    existing = {source_key(parse_source(l)[0]) for l in read_lines(SOURCES_FILE)}
    answers = []
    for raw in lines_in:
        raw = raw.strip()
        if not raw:
            continue
        target, rule = parse_source(raw)
        if not (target.startswith("http") or target.startswith("@") or "t.me/" in target):
            answers.append(f"❓ Не понял: {raw}\nПришлите ссылку или /помощь")
            continue
        if source_key(target) in existing:
            answers.append(f"Уже есть в списке: {target}")
            continue
        ok, info = describe_check(target, rule)
        if not ok:
            answers.append(f"❌ Не добавил {target}\n{info}")
            continue
        prefix = {"all": "+ ", "photo": "📷 ", "filter": ""}[rule]
        append_line(SOURCES_FILE, prefix + target)
        existing.add(source_key(target))
        answers.append(f"✅ Добавил {target}\n{info}")
    return "\n\n".join(answers)


def cmd_delete(arg):
    if not arg:
        return "Напишите ссылку после команды: /удалить https://site.ru/rss"
    key = source_key(parse_source(arg)[0])
    removed = remove_lines(SOURCES_FILE, lambda l: source_key(parse_source(l)[0]) == key)
    return f"🗑 Убрал: {removed[0]}" if removed else f"Такого источника нет в списке: {arg}"


def cmd_list_sources():
    lines = read_lines(SOURCES_FILE)
    return f"Источников: {len(lines)}\n\n" + "\n".join(lines)


def cmd_add_word(arg, minus=False):
    word = arg.strip()
    if not word:
        return "Напишите слово после команды, например: /слово заповедн"
    line = ("-" if minus else "") + word
    have = {l.strip().lower() for l in read_lines(KEYWORDS_FILE)}
    if line.lower() in have:
        return f"Уже есть: {line}"
    append_line(KEYWORDS_FILE, line)
    return (f"✅ Исключение добавлено: {word}\nНовости с этим словом больше не придут."
            if minus else f"✅ Слово добавлено: {word}")


def cmd_remove_word(arg):
    word = arg.strip().lower()
    if not word:
        return "Напишите слово после команды: /убрать заповедн"
    removed = remove_lines(KEYWORDS_FILE, lambda l: l.lower() in (word, "-" + word))
    return f"🗑 Убрал из фильтра: {', '.join(removed)}" if removed else f"Такого слова нет: {arg}"


def cmd_list_words():
    lines = read_lines(KEYWORDS_FILE)
    plus = [l for l in lines if not l.startswith("-")]
    minus = [l[1:] for l in lines if l.startswith("-")]
    return (f"Слов: {len(plus)}\n" + ", ".join(plus) +
            f"\n\nИсключения ({len(minus)}): " + ", ".join(minus))


COMMANDS = {
    "/start": "help", "/help": "help", "/помощь": "help",
    "/удалить": "del", "/del": "del",
    "/источники": "list", "/list": "list",
    "/слово": "word", "/word": "word",
    "/минус": "minus", "/minus": "minus",
    "/убрать": "unword", "/unword": "unword",
    "/слова": "words", "/words": "words",
}


def handle_message(msg):
    origin = msg.get("forward_origin") or {}
    fwd_chat = origin.get("chat") or msg.get("forward_from_chat")
    if fwd_chat:
        if fwd_chat.get("username"):
            return cmd_add([f"https://t.me/{fwd_chat['username']}"])
        return "Это закрытый канал — читать его я не могу. Подходят только открытые каналы."
    text = (msg.get("text") or msg.get("caption") or "").strip()
    if not text:
        return "Пришлите ссылку на источник или /помощь"
    first, _, rest = text.partition(" ")
    action = COMMANDS.get(first.split("@")[0].lower())
    if action == "help":
        return HELP_TEXT
    if action == "del":
        return cmd_delete(rest)
    if action == "list":
        return cmd_list_sources()
    if action in ("word", "minus"):
        return cmd_add_word(rest, minus=action == "minus")
    if action == "unword":
        return cmd_remove_word(rest)
    if action == "words":
        return cmd_list_words()
    if text.startswith("/"):
        return "Не знаю такую команду. Список команд: /помощь"
    return cmd_add(text.splitlines())


def handle_commands(token, channel_id):
    try:
        updates = tg_api(token, "getUpdates", timeout=0, allowed_updates=["message"])
    except Exception as e:
        print(f"Не смог прочитать сообщения боту: {e}")
        return
    if not updates:
        return
    try:
        admins = {m["user"]["id"] for m in tg_api(token, "getChatAdministrators", chat_id=channel_id)}
    except Exception as e:
        print(f"Не смог получить администраторов канала: {e}")
        admins = set()
    for upd in updates:
        msg = upd.get("message")
        if not msg or msg.get("chat", {}).get("type") != "private":
            continue
        user = msg.get("from", {}).get("id")
        try:
            if user not in admins:
                answer = "Мной управляют только администраторы канала."
            else:
                answer = handle_message(msg)
            print(f"Команда от {user}: {(msg.get('text') or '')[:60]!r}")
            reply(token, msg["chat"]["id"], answer)
        except Exception as e:
            print(f"Ошибка при обработке сообщения: {e}")
    # Отмечаем сообщения прочитанными, чтобы не обработать их второй раз
    tg_api(token, "getUpdates", offset=updates[-1]["update_id"] + 1, timeout=0)


# ---------- Главное ----------

def check_sources(sources):
    ok = 0
    note = {"all": ", без фильтра", "photo": ", только фотоконкурсы", "filter": ""}
    for target, rule, items, mode, err in read_all(sources):
        if err:
            print(f"\nОШИБКА  {target}\n    {err}")
            continue
        ok += 1
        print(f"\nOK  {target}\n    способ: {mode}, записей: {len(items)}{note[rule]}")
        for it in items[:3]:
            print(f"    · {it['title']} — {it['link']}")
    print(f"\nРаботает {ok} из {len(sources)}")


def read_all(sources):
    """Открывает все источники параллельно, чтобы не ждать каждый по очереди."""
    def job(line):
        target, rule = parse_source(line)
        try:
            items, mode = read_source(target)
            return target, rule, items, mode, None
        except Exception as e:
            return target, rule, [], None, e
    with ThreadPoolExecutor(max_workers=24) as pool:
        return list(pool.map(job, sources))


def main():
    dry = "--dry" in sys.argv
    token, chat_id = os.environ.get("TELEGRAM_TOKEN"), os.environ.get("CHANNEL_ID")
    if token and chat_id and not dry and "--check" not in sys.argv:
        handle_commands(token, chat_id)
    sources = read_lines(SOURCES_FILE)
    if not sources:
        print("sources.txt пуст — добавьте источники")
        return
    if "--check" in sys.argv:
        check_sources(sources)
        return

    include, exclude = load_keywords()
    contests, _ = load_keywords(CONTESTS_FILE)
    state = load_state()
    seen = set(state["links"])
    now = time.time()
    errors, found, merged = [], 0, 0

    print("Собираю новости:")
    for target, rule, items, mode, err in read_all(sources):
        if err:
            print(f"  ОШИБКА  {target}: {err}")
            errors.append(target)
            continue
        src_key = key_of(clean_link(target))
        is_new_source = src_key not in state["sources"]
        print(f"  {target}: {len(items)} ({mode}){' — новый источник' if is_new_source else ''}")
        state["sources"].add(src_key)
        max_age = (NEW_SOURCE_HOURS if is_new_source else MAX_AGE_HOURS) * 3600
        for it in items:
            k = key_of(clean_link(it["link"]))
            if k in seen:
                continue
            seen.add(k)
            state["links"].append(k)
            if it["time"] is None and is_new_source:
                continue  # у новых источников без дат всё уже лежащее считаем старым
            if it["time"] is not None and now - it["time"] > max_age:
                continue
            contest = is_contest(it["text"], contests, exclude)
            take_all = rule == "all" and not str(mode).startswith(SITE_FEED)
            if rule == "photo":
                if not contest:
                    continue
            elif not contest and not passes(it["text"], include, exclude, take_all):
                continue
            sig = title_signature(it["title"])
            if MERGE_SIMILAR and any(is_similar(sig, t[1]) for t in state["titles"]):
                merged += 1
                continue
            state["titles"].append([now, sig])
            title = (CONTEST_MARK if contest else "") + it["title"]
            state["pending"].append({"title": title, "link": it["link"],
                                     "time": it["time"] or now})
            found += 1

    print(f"Новых подходящих: {found}, склеено похожих: {merged}, "
          f"ждут отправки: {len(state['pending'])}")

    due = now - state["last_post"] >= (POST_EVERY_MINUTES - 5) * 60
    if dry:
        for m in build_messages(sorted(state["pending"], key=lambda it: it["time"])):
            print("-" * 40 + "\n" + m)
        return

    if due and state["pending"]:
        if not token or not chat_id:
            sys.exit("Не заданы TELEGRAM_TOKEN и CHANNEL_ID")
        for m in build_messages(sorted(state["pending"], key=lambda it: it["time"])):
            tg_send(token, chat_id, m)
            time.sleep(1)
        print(f"Отправлено в канал: {len(state['pending'])}")
        state["pending"] = []
    if due:
        state["last_post"] = now

    save_state(state)

    if errors and len(errors) == len(sources):
        sys.exit("Ни один источник не открылся")


if __name__ == "__main__":
    main()
