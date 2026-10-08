from http.server import BaseHTTPRequestHandler
import json

import os

import re

import time

import hashlib

import requests

import xml.etree.ElementTree as ET

from html.parser import HTMLParser

from urllib.parse import urlparse, parse_qs
from concurrent.futures import ThreadPoolExecutor, as_completed
from requests.adapters import HTTPAdapter
from urllib3.util.retry import Retry


BASE_DIR = os.path.dirname(os.path.dirname(__file__))

LAW_LIST_PATH = os.path.join(BASE_DIR, "law_list.json")

REGULATION_SUPABASE_URL = (
    os.getenv(
        "OSRIS_REGULATION_SUPABASE_URL",
        ""
    )
    .strip()
    .rstrip("/")
)

REGULATION_SUPABASE_SERVICE_ROLE_KEY = (
    os.getenv(
        "OSRIS_REGULATION_SUPABASE_SERVICE_ROLE_KEY",
        ""
    )
    .strip()
)

REGULATION_BASELINE_TABLE = (
    "osris_regulation_baselines"
)

HEADERS = {
    "User-Agent": (
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) "
        "Chrome/149.0.0.0 Safari/537.36"
    ),
    "Accept": (
        "text/html,application/xhtml+xml,"
        "application/xml;q=0.9,*/*;q=0.8"
    ),
    "Accept-Language": "zh-TW,zh;q=0.9,en;q=0.8",
    "Cache-Control": "no-cache",
    "Pragma": "no-cache"
}


def create_session():
    session = requests.Session()

    retry = Retry(
        total=2,
        connect=2,
        read=2,
        backoff_factor=0.6,
        status_forcelist=[429, 500, 502, 503, 504],
        allowed_methods=["GET"]
    )

    adapter = HTTPAdapter(
        max_retries=retry,
        pool_connections=8,
        pool_maxsize=8
    )

    session.mount("https://", adapter)
    session.mount("http://", adapter)

    return session


def strip_namespace(tag):
    """
    移除 XML namespace。

    例如：
    {http://example.com}LawModifiedDate

    轉成：
    LawModifiedDate
    """
    if "}" in tag:
        return tag.split("}", 1)[1]

    return tag


def find_xml_text(root, possible_names):
    """
    不受 XML namespace 影響，
    尋找可能的日期欄位名稱。
    """
    target_names = {
        str(name).lower()
        for name in possible_names
    }

    for element in root.iter():
        element_name = strip_namespace(
            str(element.tag)
        ).lower()

        if element_name in target_names:
            text = (element.text or "").strip()

            if text:
                return text

    return None


def normalize_law_date(raw_date):
    """
    將全國法規資料庫可能回傳的日期格式，
    統一轉成 YYYY-MM-DD。

    支援：
    20260626
    2026-06-26
    2026/06/26
    1150626
    115-06-26
    民國115年6月26日
    中華民國115年6月26日
    """
    if raw_date is None:
        return None

    value = str(raw_date).strip()

    if not value:
        return None

    value = (
        value
        .replace("中華民國", "")
        .replace("民國", "")
        .replace("年", "-")
        .replace("月", "-")
        .replace("日", "")
        .replace("/", "-")
        .replace(".", "-")
        .strip()
    )

    digits = re.sub(r"\D", "", value)

    try:
        # 西元純數字：20260626
        if len(digits) == 8:
            year = int(digits[0:4])
            month = int(digits[4:6])
            day = int(digits[6:8])

        # 民國純數字：1150626
        elif len(digits) == 7:
            year = int(digits[0:3]) + 1911
            month = int(digits[3:5])
            day = int(digits[5:7])

        else:
            parts = [
                part
                for part in re.split(r"[-\s]+", value)
                if part
            ]

            if len(parts) < 3:
                return None

            year = int(parts[0])
            month = int(parts[1])
            day = int(parts[2])

            # 民國年轉西元年
            if year < 1911:
                year += 1911

        if year < 1912 or year > 2200:
            return None

        if month < 1 or month > 12:
            return None

        if day < 1 or day > 31:
            return None

        return f"{year:04d}-{month:02d}-{day:02d}"

    except (TypeError, ValueError):
        return None


def get_law_date(pcode):
    """
    從全國法規資料庫公開法規頁面取得修正日期。
    """
    url = "https://law.moj.gov.tw/LawClass/LawAll.aspx"
    session = create_session()

    try:
        response = session.get(
            url,
            params={
                "pcode": pcode
            },
            headers=HEADERS,
            timeout=(8, 25),
            allow_redirects=True
        )

        response.raise_for_status()

        if not response.content:
            raise ValueError(
                "全國法規資料庫回傳空白內容"
            )

        response.encoding = (
            response.apparent_encoding or
            response.encoding or
            "utf-8"
        )

        html = response.text

        if not html.strip():
            raise ValueError(
                "全國法規資料庫回傳空白網頁"
            )

        if "全國法規資料庫" not in html:
            raise ValueError(
                "回傳內容不是全國法規資料庫頁面"
            )

        date_patterns = [
            (
                r"修正日期\s*[：:]?\s*"
                r"(?:中華民國\s*)?"
                r"(?:民國\s*)?"
                r"(\d{2,4})\s*年\s*"
                r"(\d{1,2})\s*月\s*"
                r"(\d{1,2})\s*日"
            ),
            (
                r"公布日期\s*[：:]?\s*"
                r"(?:中華民國\s*)?"
                r"(?:民國\s*)?"
                r"(\d{2,4})\s*年\s*"
                r"(\d{1,2})\s*月\s*"
                r"(\d{1,2})\s*日"
            ),
            (
                r"發布日期\s*[：:]?\s*"
                r"(?:中華民國\s*)?"
                r"(?:民國\s*)?"
                r"(\d{2,4})\s*年\s*"
                r"(\d{1,2})\s*月\s*"
                r"(\d{1,2})\s*日"
            )
        ]

        date_match = None

        for pattern in date_patterns:
            date_match = re.search(
                pattern,
                html,
                flags=re.IGNORECASE
            )

            if date_match:
                break

        if not date_match:
            compact_html = re.sub(
                r"<[^>]+>",
                " ",
                html
            )

            compact_html = re.sub(
                r"\s+",
                " ",
                compact_html
            )

            for pattern in date_patterns:
                date_match = re.search(
                    pattern,
                    compact_html,
                    flags=re.IGNORECASE
                )

                if date_match:
                    break

        if not date_match:
            raise ValueError(
                "法規頁面中找不到修正、公布或發布日期"
            )

        raw_year = int(date_match.group(1))
        month = int(date_match.group(2))
        day = int(date_match.group(3))

        if raw_year < 1911:
            year = raw_year + 1911
            raw_date = (
                f"民國{raw_year}年"
                f"{month:02d}月"
                f"{day:02d}日"
            )
        else:
            year = raw_year
            raw_date = (
                f"{year}年"
                f"{month:02d}月"
                f"{day:02d}日"
            )

        if year < 1912 or year > 2200:
            raise ValueError(
                f"年份超出合理範圍：{year}"
            )

        if month < 1 or month > 12:
            raise ValueError(
                f"月份格式錯誤：{month}"
            )

        if day < 1 or day > 31:
            raise ValueError(
                f"日期格式錯誤：{day}"
            )

        normalized_date = (
            f"{year:04d}-"
            f"{month:02d}-"
            f"{day:02d}"
        )

        return {
            "date": normalized_date,
            "rawDate": raw_date,
            "error": None
        }

    except requests.Timeout:
        return {
            "date": None,
            "rawDate": None,
            "error": "連線逾時"
        }

    except requests.RequestException as exc:
        response_status = None
        response_preview = None

        if exc.response is not None:
            response_status = exc.response.status_code

            try:
                response_preview = (
                    exc.response.text[:300]
                )
            except Exception:
                response_preview = None

        error_message = (
            f"HTTP 請求失敗：{str(exc)}"
        )

        if response_status is not None:
            error_message += (
                f"；狀態碼：{response_status}"
            )

        if response_preview:
            error_message += (
                f"；回傳內容：{response_preview}"
            )

        return {
            "date": None,
            "rawDate": None,
            "error": error_message
        }

    except Exception as exc:
        return {
            "date": None,
            "rawDate": None,
            "error": str(exc)
        }

    finally:
        session.close()

def extract_law_date_from_html(html):
    """
    從已取得的全國法規資料庫 HTML
    解析修正／公布／發布日期。

    不進行任何 HTTP Request。
    """

    if not html:
        return {
            "date": None,
            "rawDate": None,
            "error": "法規 HTML 為空白"
        }

    date_patterns = [
        (
            r"修正日期\s*[：:]?\s*"
            r"(?:中華民國\s*)?"
            r"(?:民國\s*)?"
            r"(\d{2,4})\s*年\s*"
            r"(\d{1,2})\s*月\s*"
            r"(\d{1,2})\s*日"
        ),
        (
            r"公布日期\s*[：:]?\s*"
            r"(?:中華民國\s*)?"
            r"(?:民國\s*)?"
            r"(\d{2,4})\s*年\s*"
            r"(\d{1,2})\s*月\s*"
            r"(\d{1,2})\s*日"
        ),
        (
            r"發布日期\s*[：:]?\s*"
            r"(?:中華民國\s*)?"
            r"(?:民國\s*)?"
            r"(\d{2,4})\s*年\s*"
            r"(\d{1,2})\s*月\s*"
            r"(\d{1,2})\s*日"
        )
    ]

    date_match = None

    for pattern in date_patterns:
        date_match = re.search(
            pattern,
            html,
            flags=re.IGNORECASE
        )

        if date_match:
            break

    if not date_match:
        compact_html = re.sub(
            r"<[^>]+>",
            " ",
            html
        )

        compact_html = re.sub(
            r"\s+",
            " ",
            compact_html
        )

        for pattern in date_patterns:
            date_match = re.search(
                pattern,
                compact_html,
                flags=re.IGNORECASE
            )

            if date_match:
                break

    if not date_match:
        return {
            "date": None,
            "rawDate": None,
            "error":
                "法規頁面中找不到修正、公布或發布日期"
        }

    try:
        raw_year = int(
            date_match.group(1)
        )

        month = int(
            date_match.group(2)
        )

        day = int(
            date_match.group(3)
        )

        if raw_year < 1911:
            year = raw_year + 1911

            raw_date = (
                f"民國{raw_year}年"
                f"{month:02d}月"
                f"{day:02d}日"
            )

        else:
            year = raw_year

            raw_date = (
                f"{year}年"
                f"{month:02d}月"
                f"{day:02d}日"
            )

        if year < 1912 or year > 2200:
            raise ValueError(
                f"年份超出合理範圍：{year}"
            )

        if month < 1 or month > 12:
            raise ValueError(
                f"月份格式錯誤：{month}"
            )

        if day < 1 or day > 31:
            raise ValueError(
                f"日期格式錯誤：{day}"
            )

        return {
            "date":
                (
                    f"{year:04d}-"
                    f"{month:02d}-"
                    f"{day:02d}"
                ),

            "rawDate":
                raw_date,

            "error":
                None
        }

    except Exception as exc:
        return {
            "date": None,
            "rawDate": None,
            "error": str(exc)
        }

class LawArticleHTMLParser(HTMLParser):
    """
    從全國法規資料庫「所有條文」頁面，
    擷取每一條正式條文。

    不依賴 BeautifulSoup，
    避免增加目前 Vercel Python 後端的套件依賴。
    """

    def __init__(self):
        super().__init__(
            convert_charrefs=True
        )

        self.articles = []

        self.current_article_no = None
        self.current_parts = []

        self.in_article_link = False
        self.article_link_parts = []

        self.skip_depth = 0
        self.stopped = False


    def handle_starttag(
        self,
        tag,
        attrs
    ):
        if self.stopped:
            return

        tag = str(tag).lower()

        if tag in {
            "script",
            "style",
            "noscript"
        }:
            self.skip_depth += 1
            return

        if self.skip_depth > 0:
            return

        attrs_dict = dict(attrs)

        if tag == "a":
            href = str(
                attrs_dict.get(
                    "href",
                    ""
                )
            )

            # 全國法規資料庫每一條條號
            # 會連向 LawSingle.aspx?flno=...
            #
            # 只把這種連結辨識為真正條文標題，
            # 避免內文中的「第五條」等文字
            # 被誤判成新的條文。
            if (
                "LawSingle.aspx" in href and
                "flno=" in href.lower()
            ):
                self.in_article_link = True
                self.article_link_parts = []

        if (
            self.current_article_no and
            tag in {
                "br",
                "p",
                "li",
                "div"
            }
        ):
            self.current_parts.append(
                "\n"
            )


    def handle_endtag(
        self,
        tag
    ):
        tag = str(tag).lower()

        if tag in {
            "script",
            "style",
            "noscript"
        }:
            if self.skip_depth > 0:
                self.skip_depth -= 1

            return

        if (
            self.skip_depth > 0 or
            self.stopped
        ):
            return

        if (
            tag == "a" and
            self.in_article_link
        ):
            article_label = (
                "".join(
                    self.article_link_parts
                )
                .strip()
            )

            match = re.search(
                r"第\s*(\d+(?:-\d+)?)\s*條",
                article_label
            )

            if match:
                self._finish_current_article()

                self.current_article_no = (
                    f"第 {match.group(1)} 條"
                )

                self.current_parts = []

            self.in_article_link = False
            self.article_link_parts = []

        if (
            self.current_article_no and
            tag in {
                "p",
                "li",
                "div"
            }
        ):
            self.current_parts.append(
                "\n"
            )


    def handle_data(
        self,
        data
    ):
        if (
            self.skip_depth > 0 or
            self.stopped
        ):
            return

        value = str(
            data or ""
        )

        stripped = value.strip()

        if self.in_article_link:
            self.article_link_parts.append(
                value
            )

            return

        if not self.current_article_no:
            return

        # 已經進入條文區後，
        # 遇到頁尾導覽即停止收集，
        # 避免最後一條吃到網站 Footer。
        if stripped in {
            "最新訊息",
            "訂閱電子報"
        }:
            self._finish_current_article()
            self.stopped = True
            return

        # 編、章、節標題不屬於前一條正文。
        if re.fullmatch(
            r"第\s*[一二三四五六七八九十百千0-9]+\s*[編章節]",
            stripped
        ):
            return

        if stripped:
            self.current_parts.append(
                value
            )


    def close(self):
        super().close()

        if not self.stopped:
            self._finish_current_article()


    def _finish_current_article(self):
        if not self.current_article_no:
            return

        raw_text = "".join(
            self.current_parts
        )

        lines = []

        for line in raw_text.splitlines():
            normalized_line = re.sub(
                r"[ \t\u3000]+",
                " ",
                line
            ).strip()

            if normalized_line:
                lines.append(
                    normalized_line
                )

        article_text = "\n".join(
            lines
        ).strip()

        if article_text:
            self.articles.append({
                "no":
                    self.current_article_no,

                "text":
                    article_text
            })

        self.current_article_no = None
        self.current_parts = []


def get_law_articles(pcode):
    """
    從全國法規資料庫取得指定 PCode
    目前最新版的完整正式條文。
    """

    normalized_pcode = str(
        pcode or ""
    ).strip().upper()

    if not normalized_pcode:
        return {
            "articles": [],
            "sourceUrl": None,
            "error": "缺少 PCode"
        }

    url = (
        "https://law.moj.gov.tw/"
        "LawClass/LawAll.aspx"
    )

    source_url = (
        f"{url}?pcode="
        f"{normalized_pcode}"
    )

    session = create_session()

    try:
        response = session.get(
            url,
            params={
                "pcode":
                    normalized_pcode
            },
            headers=HEADERS,
            timeout=(8, 25),
            allow_redirects=True
        )

        response.raise_for_status()

        if not response.content:
            raise ValueError(
                "全國法規資料庫回傳空白內容"
            )

        response.encoding = (
            response.apparent_encoding or
            response.encoding or
            "utf-8"
        )

        html = response.text

        if not html.strip():
            raise ValueError(
                "全國法規資料庫回傳空白網頁"
            )

        if "全國法規資料庫" not in html:
            raise ValueError(
                "回傳內容不是全國法規資料庫頁面"
            )

        parser = LawArticleHTMLParser()

        parser.feed(
            html
        )

        parser.close()

        articles = (
            parser.articles
        )

        if not articles:
            raise ValueError(
                "法規頁面中找不到正式條文"
            )

        return {
            "articles":
                articles,

            "sourceUrl":
                source_url,

            "error":
                None
        }

    except requests.Timeout:
        return {
            "articles": [],
            "sourceUrl":
                source_url,
            "error":
                "取得完整條文連線逾時"
        }

    except requests.RequestException as exc:
        return {
            "articles": [],
            "sourceUrl":
                source_url,
            "error":
                f"取得完整條文 HTTP 請求失敗：{str(exc)}"
        }

    except Exception as exc:
        return {
            "articles": [],
            "sourceUrl":
                source_url,
            "error":
                str(exc)
        }

    finally:
        session.close()


def get_law_snapshot(pcode):
    """
    建立單一法規目前正式 Snapshot。

    同一個 LawAll.aspx Request
    同時解析：
    1. 最新修正／公布日期
    2. 完整正式條文

    避免同一部法規重複向官方網站請求兩次。
    """

    normalized_pcode = str(
        pcode or ""
    ).strip().upper()

    if not normalized_pcode:
        return {
            "success": False,
            "pcode": "",
            "date": None,
            "articles": [],
            "articleCount": 0,
            "sourceUrl": None,
            "error": "缺少 PCode"
        }

    url = (
        "https://law.moj.gov.tw/"
        "LawClass/LawAll.aspx"
    )

    source_url = (
        f"{url}?pcode="
        f"{normalized_pcode}"
    )

    session = create_session()

    try:
        response = session.get(
            url,
            params={
                "pcode":
                    normalized_pcode
            },
            headers=HEADERS,
            timeout=(8, 25),
            allow_redirects=True
        )

        response.raise_for_status()

        if not response.content:
            raise ValueError(
                "全國法規資料庫回傳空白內容"
            )

        response.encoding = (
            response.apparent_encoding or
            response.encoding or
            "utf-8"
        )

        html = response.text

        if not html.strip():
            raise ValueError(
                "全國法規資料庫回傳空白網頁"
            )

        if "全國法規資料庫" not in html:
            raise ValueError(
                "回傳內容不是全國法規資料庫頁面"
            )

        # 同一份 HTML 解析日期
        date_result = (
            extract_law_date_from_html(
                html
            )
        )

        if not date_result["date"]:
            return {
                "success": False,
                "pcode":
                    normalized_pcode,
                "date": None,
                "articles": [],
                "articleCount": 0,
                "sourceUrl":
                    source_url,
                "error":
                    date_result["error"]
            }

        # 同一份 HTML 解析完整條文
        parser = LawArticleHTMLParser()

        parser.feed(
            html
        )

        parser.close()

        articles = parser.articles

        if not articles:
            raise ValueError(
                "法規頁面中找不到正式條文"
            )

        return {
            "success": True,
            "pcode":
                normalized_pcode,
            "date":
                date_result["date"],
            "articles":
                articles,
            "articleCount":
                len(articles),
            "sourceUrl":
                source_url,
            "error":
                None
        }

    except requests.Timeout:
        return {
            "success": False,
            "pcode":
                normalized_pcode,
            "date": None,
            "articles": [],
            "articleCount": 0,
            "sourceUrl":
                source_url,
            "error":
                "取得法規 Snapshot 連線逾時"
        }

    except requests.RequestException as exc:
        return {
            "success": False,
            "pcode":
                normalized_pcode,
            "date": None,
            "articles": [],
            "articleCount": 0,
            "sourceUrl":
                source_url,
            "error":
                (
                    "取得法規 Snapshot HTTP 請求失敗："
                    f"{str(exc)}"
                )
        }

    except Exception as exc:
        return {
            "success": False,
            "pcode":
                normalized_pcode,
            "date": None,
            "articles": [],
            "articleCount": 0,
            "sourceUrl":
                source_url,
            "error":
                str(exc)
        }

    finally:
        session.close()

def build_articles_hash(articles):
    """
    對條文內容建立穩定 SHA-256。

    未來除了日期之外，
    也可以判斷實際條文內容是否改變。
    """

    normalized = json.dumps(
        articles,
        ensure_ascii=False,
        sort_keys=True,
        separators=(
            ",",
            ":"
        )
    )

    return hashlib.sha256(
        normalized.encode("utf-8")
    ).hexdigest()


def upsert_regulation_baseline(
    pcode,
    law_name,
    snapshot
):
    """
    將指定法規 Snapshot
    寫入 osris_regulation_baselines。

    R1-B2-B 階段用途：
    建立第一份 baseline。

    目前不處理 pending diff。
    """

    if not REGULATION_SUPABASE_URL:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_URL"
        )

    if not REGULATION_SUPABASE_SERVICE_ROLE_KEY:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_SERVICE_ROLE_KEY"
        )

    normalized_pcode = str(
        pcode or ""
    ).strip().upper()

    normalized_name = str(
        law_name or ""
    ).strip()

    if not normalized_pcode:
        raise ValueError(
            "缺少 PCode"
        )

    if not snapshot.get("success"):
        raise ValueError(
            snapshot.get("error") or
            "Snapshot 無效"
        )

    articles = snapshot.get(
        "articles",
        []
    )

    if not isinstance(
        articles,
        list
    ) or not articles:
        raise ValueError(
            "Snapshot 沒有有效條文"
        )

    articles_hash = (
        build_articles_hash(
            articles
        )
    )

    payload = {
        "pcode":
            normalized_pcode,

        "law_name":
            normalized_name,

        "baseline_date":
            snapshot.get("date"),

        "baseline_articles":
            articles,

        "baseline_hash":
            articles_hash,

        "pending_date":
            None,

        "pending_articles":
            None,

        "pending_diff":
            None,

        "pending_hash":
            None,

        "status":
            "baseline_ready",

        "source_url":
            snapshot.get(
                "sourceUrl"
            ),

        "last_error":
            None,

        "last_synced_at":
            time.strftime(
                "%Y-%m-%dT%H:%M:%SZ",
                time.gmtime()
            ),

        "updated_at":
            time.strftime(
                "%Y-%m-%dT%H:%M:%SZ",
                time.gmtime()
            )
    }

    url = (
        f"{REGULATION_SUPABASE_URL}"
        f"/rest/v1/"
        f"{REGULATION_BASELINE_TABLE}"
        f"?on_conflict=pcode"
    )

    headers = {
        "apikey":
            REGULATION_SUPABASE_SERVICE_ROLE_KEY,

        "Content-Type":
            "application/json",

        "Prefer":
            "resolution=merge-duplicates,"
            "return=representation"
    }

    response = requests.post(
        url,
        headers=headers,
        json=payload,
        timeout=(8, 25)
    )

    if not response.ok:
        raise RuntimeError(
            "Supabase baseline 寫入失敗："
            f"HTTP {response.status_code}；"
            f"{response.text[:500]}"
        )

    try:
        result = response.json()

    except ValueError:
        result = []

    return {
        "success":
            True,

        "pcode":
            normalized_pcode,

        "baselineDate":
            snapshot.get("date"),

        "articleCount":
            len(articles),

        "baselineHash":
            articles_hash,

        "data":
            result
    }

def get_regulation_baseline_for_diff(pcode):
    """
    取得指定法規目前正式 Baseline。

    供自動新舊條文比對使用。
    """

    if not REGULATION_SUPABASE_URL:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_URL"
        )

    if not REGULATION_SUPABASE_SERVICE_ROLE_KEY:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_SERVICE_ROLE_KEY"
        )

    normalized_pcode = str(
        pcode or ""
    ).strip().upper()

    if not normalized_pcode:
        return None

    url = (
        f"{REGULATION_SUPABASE_URL}"
        f"/rest/v1/"
        f"{REGULATION_BASELINE_TABLE}"
    )

    headers = {
        "apikey":
            REGULATION_SUPABASE_SERVICE_ROLE_KEY,

        "Accept":
            "application/json"
    }

    response = requests.get(
        url,
        headers=headers,
        params={
            "pcode":
                f"eq.{normalized_pcode}",

            "select":
                (
                    "pcode,"
                    "law_name,"
                    "baseline_date,"
                    "baseline_articles,"
                    "baseline_hash,"
                    "pending_date,"
                    "pending_hash,"
                    "status"
                ),

            "limit":
                "1"
        },
        timeout=(8, 20)
    )

    if not response.ok:
        raise RuntimeError(
            "Supabase baseline 查詢失敗："
            f"HTTP {response.status_code}；"
            f"{response.text[:500]}"
        )

    try:
        rows = response.json()

    except ValueError:
        rows = []

    if (
        isinstance(rows, list) and
        len(rows) > 0
    ):
        return rows[0]

    return None

def regulation_article_sort_key(article_no):
    """
    將：
    第 10 條
    第 10-1 條
    第 11 條

    轉成可以穩定排序的 tuple。
    """

    value = str(
        article_no or ""
    )

    match = re.search(
        r"第\s*(\d+)"
        r"(?:-(\d+))?"
        r"\s*條",
        value
    )

    if not match:
        return (
            999999,
            999999,
            value
        )

    main_no = int(
        match.group(1)
    )

    sub_no = (
        int(match.group(2))
        if match.group(2)
        else 0
    )

    return (
        main_no,
        sub_no,
        value
    )

def build_regulation_diff(
    baseline_articles,
    current_articles
):
    """
    比對 Baseline 與官方最新版條文。

    回傳：
    added
    removed
    modified

    完全由程式比對，
    不使用 AI 判斷實際條文差異。
    """

    old_articles = (
        baseline_articles
        if isinstance(
            baseline_articles,
            list
        )
        else []
    )

    new_articles = (
        current_articles
        if isinstance(
            current_articles,
            list
        )
        else []
    )

    old_map = {
        str(
            item.get(
                "no",
                ""
            )
        ).strip():
            str(
                item.get(
                    "text",
                    ""
                )
            ).strip()

        for item in old_articles
        if isinstance(item, dict)
    }

    new_map = {
        str(
            item.get(
                "no",
                ""
            )
        ).strip():
            str(
                item.get(
                    "text",
                    ""
                )
            ).strip()

        for item in new_articles
        if isinstance(item, dict)
    }

    changed_rows = []

    all_article_numbers = set(
        old_map.keys()
    ) | set(
        new_map.keys()
    )

    ordered_article_numbers = sorted(
        all_article_numbers,
        key=regulation_article_sort_key
    )

    for article_no in ordered_article_numbers:

        old_text = old_map.get(
            article_no
        )

        new_text = new_map.get(
            article_no
        )

        if (
            old_text is None and
            new_text is not None
        ):
            changed_rows.append({
                "no":
                    article_no,

                "changeType":
                    "added",

                "old":
                    "",

                "new":
                    new_text,

                "note":
                    "新增條文"
            })

            continue

        if (
            old_text is not None and
            new_text is None
        ):
            changed_rows.append({
                "no":
                    article_no,

                "changeType":
                    "removed",

                "old":
                    old_text,

                "new":
                    "",

                "note":
                    "刪除條文"
            })

            continue

        if old_text != new_text:
            changed_rows.append({
                "no":
                    article_no,

                "changeType":
                    "modified",

                "old":
                    old_text,

                "new":
                    new_text,

                "note":
                    "條文內容修正"
            })

    return changed_rows

def save_regulation_pending_diff(
    pcode,
    snapshot,
    pending_diff
):
    """
    將最新版 Snapshot 與 Diff
    保存到目前 Baseline 紀錄的 pending 區。

    不覆蓋 baseline。
    """

    normalized_pcode = str(
        pcode or ""
    ).strip().upper()

    articles = snapshot.get(
        "articles",
        []
    )

    pending_hash = (
        build_articles_hash(
            articles
        )
    )

    now_iso = time.strftime(
        "%Y-%m-%dT%H:%M:%SZ",
        time.gmtime()
    )

    payload = {
        "pending_date":
            snapshot.get(
                "date"
            ),

        "pending_articles":
            articles,

        "pending_diff":
            pending_diff,

        "pending_hash":
            pending_hash,

        "status":
            "pending_review",

        "source_url":
            snapshot.get(
                "sourceUrl"
            ),

        "last_error":
            None,

        "last_synced_at":
            now_iso,

        "updated_at":
            now_iso
    }

    url = (
        f"{REGULATION_SUPABASE_URL}"
        f"/rest/v1/"
        f"{REGULATION_BASELINE_TABLE}"
    )

    headers = {
        "apikey":
            REGULATION_SUPABASE_SERVICE_ROLE_KEY,

        "Content-Type":
            "application/json",

        "Prefer":
            "return=representation"
    }

    response = requests.patch(
        url,
        headers=headers,
        params={
            "pcode":
                f"eq.{normalized_pcode}"
        },
        json=payload,
        timeout=(8, 25)
    )

    if not response.ok:
        raise RuntimeError(
            "Supabase pending diff 寫入失敗："
            f"HTTP {response.status_code}；"
            f"{response.text[:500]}"
        )

    try:
        result = response.json()

    except ValueError:
        result = []

    return {
        "success":
            True,

        "pendingDate":
            snapshot.get(
                "date"
            ),

        "pendingHash":
            pending_hash,

        "changedCount":
            len(
                pending_diff
            ),

        "data":
            result
    }

def analyze_regulation_update(pcode):
    """
    對單一法規執行：

    Baseline
    VS
    官方最新 Snapshot

    有異動：
    → 建立 pending diff

    無異動：
    → 不修改 Baseline。
    """

    normalized_pcode = str(
        pcode or ""
    ).strip().upper()

    baseline = (
        get_regulation_baseline_for_diff(
            normalized_pcode
        )
    )

    if not baseline:
        return {
            "success":
                False,

            "pcode":
                normalized_pcode,

            "status":
                "baseline_missing",

            "changed":
                False,

            "changedCount":
                0,

            "diff":
                [],

            "error":
                "找不到此法規的 Baseline"
        }

    snapshot = (
        get_law_snapshot(
            normalized_pcode
        )
    )

    if not snapshot.get(
        "success"
    ):
        return {
            "success":
                False,

            "pcode":
                normalized_pcode,

            "status":
                "snapshot_error",

            "changed":
                False,

            "changedCount":
                0,

            "diff":
                [],

            "error":
                snapshot.get(
                    "error"
                )
        }

    baseline_articles = (
        baseline.get(
            "baseline_articles"
        ) or []
    )

    baseline_hash = (
        baseline.get(
            "baseline_hash"
        ) or
        build_articles_hash(
            baseline_articles
        )
    )

    current_hash = (
        build_articles_hash(
            snapshot.get(
                "articles",
                []
            )
        )
    )

    baseline_date = str(
        baseline.get(
            "baseline_date"
        ) or ""
    )

    current_date = str(
        snapshot.get(
            "date"
        ) or ""
    )

    if (
        baseline_hash == current_hash and
        baseline_date == current_date
    ):
        return {
            "success":
                True,

            "pcode":
                normalized_pcode,

            "lawName":
                baseline.get(
                    "law_name"
                ),

            "status":
                "no_change",

            "changed":
                False,

            "baselineDate":
                baseline_date,

            "currentDate":
                current_date,

            "changedCount":
                0,

            "diff":
                [],

            "error":
                None
        }

    pending_diff = (
        build_regulation_diff(
            baseline_articles,
            snapshot.get(
                "articles",
                []
            )
        )
    )

    save_result = (
        save_regulation_pending_diff(
            normalized_pcode,
            snapshot,
            pending_diff
        )
    )

    return {
        "success":
            True,

        "pcode":
            normalized_pcode,

        "lawName":
            baseline.get(
                "law_name"
            ),

        "status":
            "pending_review",

        "changed":
            True,

        "baselineDate":
            baseline_date,

        "currentDate":
            current_date,

        "changedCount":
            len(
                pending_diff
            ),

        "diff":
            pending_diff,

        "pendingHash":
            save_result.get(
                "pendingHash"
            ),

        "error":
            None
    }    

def normalize_regulation_date(value):
    """
    將日期統一驗證為 YYYY-MM-DD。
    """

    normalized_date = str(
        value or ""
    ).strip()

    if not normalized_date:
        return None

    try:
        time.strptime(
            normalized_date,
            "%Y-%m-%d"
        )

    except ValueError:
        return None

    return normalized_date

def get_regulation_state_list():
    """
    取得全部法規目前中央狀態。

    CurrentDate：
    有 pending_review 時使用 pending_date，
    否則使用正式 baseline_date。

    LastReviewedDate：
    最近一次完成鑑別／同步鑑別日期。
    """

    if not REGULATION_SUPABASE_URL:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_URL"
        )

    if not REGULATION_SUPABASE_SERVICE_ROLE_KEY:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_SERVICE_ROLE_KEY"
        )

    url = (
        f"{REGULATION_SUPABASE_URL}"
        f"/rest/v1/"
        f"{REGULATION_BASELINE_TABLE}"
    )

    headers = {
        "apikey":
            REGULATION_SUPABASE_SERVICE_ROLE_KEY,

        "Accept":
            "application/json"
    }

    response = requests.get(
        url,
        headers=headers,
        params={
            "select":
                (
                    "pcode,"
                    "law_name,"
                    "baseline_date,"
                    "pending_date,"
                    "last_reviewed_date,"
                    "status"
                ),

            "order":
                "pcode.asc"
        },
        timeout=(8, 20)
    )

    if not response.ok:
        raise RuntimeError(
            "Supabase 中央法規狀態查詢失敗："
            f"HTTP {response.status_code}；"
            f"{response.text[:500]}"
        )

    try:
        rows = response.json()

    except ValueError:
        rows = []

    if not isinstance(
        rows,
        list
    ):
        rows = []

    result = []

    for row in rows:

        status = str(
            row.get(
                "status"
            ) or ""
        ).strip()

        baseline_date = (
            row.get(
                "baseline_date"
            )
        )

        pending_date = (
            row.get(
                "pending_date"
            )
        )

        has_pending = (
            status == "pending_review" and
            bool(
                pending_date
            )
        )

        current_date = (
            pending_date
            if has_pending
            else baseline_date
        )

        result.append({
            "Pcode":
                row.get(
                    "pcode"
                ),

            "Name":
                row.get(
                    "law_name"
                ),

            "CurrentDate":
                current_date,

            "BaselineDate":
                baseline_date,

            "PendingDate":
                pending_date,

            "LastReviewedDate":
                row.get(
                    "last_reviewed_date"
                ),

            "Status":
                status,

            "HasPending":
                has_pending
        })

    return {
        "success":
            True,

        "count":
            len(
                result
            ),

        "data":
            result,

        "error":
            None
    }

def update_regulation_review_date(
    pcode,
    review_date
):
    """
    更新單一法規的中央最近鑑別日期。

    不修改：
    baseline
    pending
    法規條文
    """

    if not REGULATION_SUPABASE_URL:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_URL"
        )

    if not REGULATION_SUPABASE_SERVICE_ROLE_KEY:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_SERVICE_ROLE_KEY"
        )

    normalized_pcode = str(
        pcode or ""
    ).strip().upper()

    normalized_date = (
        normalize_regulation_date(
            review_date
        )
    )

    if not normalized_pcode:
        return {
            "success":
                False,

            "pcode":
                "",

            "error":
                "缺少 PCode"
        }

    if not normalized_date:
        return {
            "success":
                False,

            "pcode":
                normalized_pcode,

            "error":
                "鑑別日期格式錯誤"
        }

    now_iso = time.strftime(
        "%Y-%m-%dT%H:%M:%SZ",
        time.gmtime()
    )

    url = (
        f"{REGULATION_SUPABASE_URL}"
        f"/rest/v1/"
        f"{REGULATION_BASELINE_TABLE}"
    )

    headers = {
        "apikey":
            REGULATION_SUPABASE_SERVICE_ROLE_KEY,

        "Content-Type":
            "application/json",

        "Prefer":
            "return=representation"
    }

    response = requests.patch(
        url,
        headers=headers,
        params={
            "pcode":
                f"eq.{normalized_pcode}"
        },
        json={
            "last_reviewed_date":
                normalized_date,

            "updated_at":
                now_iso
        },
        timeout=(8, 25)
    )

    if not response.ok:
        raise RuntimeError(
            "Supabase 鑑別日期更新失敗："
            f"HTTP {response.status_code}；"
            f"{response.text[:500]}"
        )

    try:
        rows = response.json()

    except ValueError:
        rows = []

    if (
        not isinstance(
            rows,
            list
        ) or
        len(rows) == 0
    ):
        return {
            "success":
                False,

            "pcode":
                normalized_pcode,

            "error":
                "找不到此法規的中央 Baseline"
        }

    return {
        "success":
            True,

        "pcode":
            normalized_pcode,

        "lastReviewedDate":
            normalized_date,

        "error":
            None
    }

def get_regulation_pending_list():
    """
    取得目前所有等待人工鑑別的法規。

    僅從 Supabase 讀取，
    不重新連線全國法規資料庫。
    """

    if not REGULATION_SUPABASE_URL:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_URL"
        )

    if not REGULATION_SUPABASE_SERVICE_ROLE_KEY:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_SERVICE_ROLE_KEY"
        )

    url = (
        f"{REGULATION_SUPABASE_URL}"
        f"/rest/v1/"
        f"{REGULATION_BASELINE_TABLE}"
    )

    headers = {
        "apikey":
            REGULATION_SUPABASE_SERVICE_ROLE_KEY,

        "Accept":
            "application/json"
    }

    response = requests.get(
        url,
        headers=headers,
        params={
            "status":
                "eq.pending_review",

            "select":
                (
                    "pcode,"
                    "law_name,"
                    "baseline_date,"
                    "pending_date,"
                    "pending_diff,"
                    "pending_hash,"
                    "status"
                ),

            "order":
                (
                    "pending_date.desc.nullslast,"
                    "pcode.asc"
                )
        },
        timeout=(8, 20)
    )

    if not response.ok:
        raise RuntimeError(
            "Supabase Pending 清單查詢失敗："
            f"HTTP {response.status_code}；"
            f"{response.text[:500]}"
        )

    try:
        rows = response.json()

    except ValueError:
        rows = []

    if not isinstance(
        rows,
        list
    ):
        rows = []

    result = []

    for row in rows:

        pending_diff = (
            row.get(
                "pending_diff"
            )
        )

        if not isinstance(
            pending_diff,
            list
        ):
            pending_diff = []

        result.append({
            "Pcode":
                row.get(
                    "pcode"
                ),

            "Name":
                row.get(
                    "law_name"
                ),

            "BaselineDate":
                row.get(
                    "baseline_date"
                ),

            "PendingDate":
                row.get(
                    "pending_date"
                ),

            "PendingHash":
                row.get(
                    "pending_hash"
                ),

            "ChangedCount":
                len(
                    pending_diff
                ),

            "Status":
                row.get(
                    "status"
                )
        })

    return {
        "success":
            True,

        "count":
            len(
                result
            ),

        "data":
            result,

        "error":
            None
    }

def get_regulation_pending_detail(pcode):
    """
    取得指定法規目前 Pending 詳細資料。

    提供給前端鑑別工作台：
    舊條文
    新條文
    異動類型
    異動說明
    """

    if not REGULATION_SUPABASE_URL:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_URL"
        )

    if not REGULATION_SUPABASE_SERVICE_ROLE_KEY:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_SERVICE_ROLE_KEY"
        )

    normalized_pcode = str(
        pcode or ""
    ).strip().upper()

    if not normalized_pcode:
        return {
            "success":
                False,

            "pcode":
                "",

            "hasPending":
                False,

            "status":
                "invalid_pcode",

            "error":
                "缺少 PCode"
        }

    url = (
        f"{REGULATION_SUPABASE_URL}"
        f"/rest/v1/"
        f"{REGULATION_BASELINE_TABLE}"
    )

    headers = {
        "apikey":
            REGULATION_SUPABASE_SERVICE_ROLE_KEY,

        "Accept":
            "application/json"
    }

    response = requests.get(
        url,
        headers=headers,
        params={
            "pcode":
                f"eq.{normalized_pcode}",

            "select":
                (
                    "pcode,"
                    "law_name,"
                    "baseline_date,"
                    "pending_date,"
                    "pending_diff,"
                    "pending_hash,"
                    "status,"
                    "source_url"
                ),

            "limit":
                "1"
        },
        timeout=(8, 20)
    )

    if not response.ok:
        raise RuntimeError(
            "Supabase Pending 詳情查詢失敗："
            f"HTTP {response.status_code}；"
            f"{response.text[:500]}"
        )

    try:
        rows = response.json()

    except ValueError:
        rows = []

    if (
        not isinstance(
            rows,
            list
        ) or
        len(rows) == 0
    ):
        return {
            "success":
                False,

            "pcode":
                normalized_pcode,

            "hasPending":
                False,

            "status":
                "baseline_missing",

            "error":
                "找不到此法規的 Baseline"
        }

    row = rows[0]

    pending_diff = (
        row.get(
            "pending_diff"
        )
    )

    if not isinstance(
        pending_diff,
        list
    ):
        pending_diff = []

    has_pending = (
        str(
            row.get(
                "status"
            ) or ""
        ) == "pending_review"
        and
        bool(
            row.get(
                "pending_date"
            )
        )
        and
        bool(
            row.get(
                "pending_hash"
            )
        )
    )

    return {
        "success":
            True,

        "pcode":
            normalized_pcode,

        "lawName":
            row.get(
                "law_name"
            ),

        "hasPending":
            has_pending,

        "status":
            row.get(
                "status"
            ),

        "baselineDate":
            row.get(
                "baseline_date"
            ),

        "pendingDate":
            row.get(
                "pending_date"
            ),

        "pendingHash":
            row.get(
                "pending_hash"
            ),

        "changedCount":
            len(
                pending_diff
            ),

        "diff":
            pending_diff,

        "sourceUrl":
            row.get(
                "source_url"
            ),

        "error":
            None
    }    

def get_regulation_pending_for_approval(pcode):
    """
    取得指定法規目前等待人工確認的 Pending 資料。

    僅供「完成鑑別 → 升格 Baseline」使用。
    """

    if not REGULATION_SUPABASE_URL:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_URL"
        )

    if not REGULATION_SUPABASE_SERVICE_ROLE_KEY:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_SERVICE_ROLE_KEY"
        )

    normalized_pcode = str(
        pcode or ""
    ).strip().upper()

    if not normalized_pcode:
        return None

    url = (
        f"{REGULATION_SUPABASE_URL}"
        f"/rest/v1/"
        f"{REGULATION_BASELINE_TABLE}"
    )

    headers = {
        "apikey":
            REGULATION_SUPABASE_SERVICE_ROLE_KEY,

        "Accept":
            "application/json"
    }

    response = requests.get(
        url,
        headers=headers,
        params={
            "pcode":
                f"eq.{normalized_pcode}",

            "select":
                (
                    "pcode,"
                    "law_name,"
                    "baseline_date,"
                    "pending_date,"
                    "pending_articles,"
                    "pending_diff,"
                    "pending_hash,"
                    "status"
                ),

            "limit":
                "1"
        },
        timeout=(8, 20)
    )

    if not response.ok:
        raise RuntimeError(
            "Supabase pending 查詢失敗："
            f"HTTP {response.status_code}；"
            f"{response.text[:500]}"
        )

    try:
        rows = response.json()

    except ValueError:
        rows = []

    if (
        isinstance(rows, list) and
        len(rows) > 0
    ):
        return rows[0]

    return None

def promote_regulation_pending_to_baseline(
    pcode
):
    """
    將人工確認完成的 Pending
    正式升格為下一版 Baseline。

    安全原則：
    1. 沒有 pending_review 時不做任何修改。
    2. 升格前重新驗證 pending_hash。
    3. 使用 pending_hash + status 作為條件，
       避免確認期間資料被新版同步取代。
    """

    normalized_pcode = str(
        pcode or ""
    ).strip().upper()

    if not normalized_pcode:
        return {
            "success":
                False,

            "pcode":
                "",

            "promoted":
                False,

            "status":
                "invalid_pcode",

            "error":
                "缺少 PCode"
        }

    pending = (
        get_regulation_pending_for_approval(
            normalized_pcode
        )
    )

    if not pending:
        return {
            "success":
                False,

            "pcode":
                normalized_pcode,

            "promoted":
                False,

            "status":
                "baseline_missing",

            "error":
                "找不到此法規的 Baseline"
        }

    pending_date = (
        pending.get(
            "pending_date"
        )
    )

    pending_articles = (
        pending.get(
            "pending_articles"
        )
    )

    pending_hash = str(
        pending.get(
            "pending_hash"
        ) or ""
    ).strip()

    current_status = str(
        pending.get(
            "status"
        ) or ""
    ).strip()

    # 沒有 Pending 時採冪等處理：
    # 重複按完成鑑別也不會破壞 Baseline。

    if (
        current_status != "pending_review" or
        not pending_date or
        not isinstance(
            pending_articles,
            list
        ) or
        not pending_articles or
        not pending_hash
    ):
        return {
            "success":
                True,

            "pcode":
                normalized_pcode,

            "lawName":
                pending.get(
                    "law_name"
                ),

            "promoted":
                False,

            "status":
                "no_pending",

            "baselineDate":
                pending.get(
                    "baseline_date"
                ),

            "error":
                None
        }

    calculated_hash = (
        build_articles_hash(
            pending_articles
        )
    )

    if calculated_hash != pending_hash:
        return {
            "success":
                False,

            "pcode":
                normalized_pcode,

            "lawName":
                pending.get(
                    "law_name"
                ),

            "promoted":
                False,

            "status":
                "pending_integrity_error",

            "error":
                (
                    "Pending 條文內容與 "
                    "pending_hash 不一致，"
                    "已停止升格"
                )
        }

    now_iso = time.strftime(
        "%Y-%m-%dT%H:%M:%SZ",
        time.gmtime()
    )

    payload = {
        "baseline_date":
            pending_date,

        "baseline_articles":
            pending_articles,

        "baseline_hash":
            pending_hash,

        "pending_date":
            None,

        "pending_articles":
            None,

        "pending_diff":
            None,

        "pending_hash":
            None,

        "status":
            "baseline_ready",

        "last_error":
            None,

        "updated_at":
            now_iso
    }

    url = (
        f"{REGULATION_SUPABASE_URL}"
        f"/rest/v1/"
        f"{REGULATION_BASELINE_TABLE}"
    )

    headers = {
        "apikey":
            REGULATION_SUPABASE_SERVICE_ROLE_KEY,

        "Content-Type":
            "application/json",

        "Prefer":
            "return=representation"
    }

    response = requests.patch(
        url,
        headers=headers,
        params={
            "pcode":
                f"eq.{normalized_pcode}",

            "status":
                "eq.pending_review",

            "pending_hash":
                f"eq.{pending_hash}"
        },
        json=payload,
        timeout=(8, 25)
    )

    if not response.ok:
        raise RuntimeError(
            "Supabase Baseline 升格失敗："
            f"HTTP {response.status_code}；"
            f"{response.text[:500]}"
        )

    try:
        rows = response.json()

    except ValueError:
        rows = []

    if (
        not isinstance(
            rows,
            list
        ) or
        len(rows) == 0
    ):
        return {
            "success":
                False,

            "pcode":
                normalized_pcode,

            "lawName":
                pending.get(
                    "law_name"
                ),

            "promoted":
                False,

            "status":
                "pending_changed",

            "error":
                (
                    "Pending 資料在確認期間已變更，"
                    "請重新載入後再完成鑑別"
                )
        }

    return {
        "success":
            True,

        "pcode":
            normalized_pcode,

        "lawName":
            pending.get(
                "law_name"
            ),

        "promoted":
            True,

        "status":
            "baseline_ready",

        "previousBaselineDate":
            pending.get(
                "baseline_date"
            ),

        "baselineDate":
            pending_date,

        "approvedChangedCount":
            len(
                pending.get(
                    "pending_diff"
                ) or []
            ),

        "error":
            None
    }    

def get_existing_regulation_baseline(pcode):
    """
    檢查指定 PCode 是否已經存在 Baseline。

    只讀取必要欄位，
    不下載完整 baseline_articles。
    """

    if not REGULATION_SUPABASE_URL:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_URL"
        )

    if not REGULATION_SUPABASE_SERVICE_ROLE_KEY:
        raise RuntimeError(
            "缺少 OSRIS_REGULATION_SUPABASE_SERVICE_ROLE_KEY"
        )

    normalized_pcode = str(
        pcode or ""
    ).strip().upper()

    if not normalized_pcode:
        return None

    url = (
        f"{REGULATION_SUPABASE_URL}"
        f"/rest/v1/"
        f"{REGULATION_BASELINE_TABLE}"
    )

    headers = {
        "apikey":
            REGULATION_SUPABASE_SERVICE_ROLE_KEY,

        "Accept":
            "application/json"
    }

    response = requests.get(
        url,
        headers=headers,
        params={
            "pcode":
                f"eq.{normalized_pcode}",

            "select":
                (
                    "pcode,"
                    "law_name,"
                    "baseline_date,"
                    "status"
                ),

            "limit":
                "1"
        },
        timeout=(8, 20)
    )

    if not response.ok:
        raise RuntimeError(
            "Supabase baseline 查詢失敗："
            f"HTTP {response.status_code}；"
            f"{response.text[:500]}"
        )

    try:
        rows = response.json()

    except ValueError:
        rows = []

    if (
        isinstance(rows, list) and
        len(rows) > 0
    ):
        return rows[0]

    return None

def initialize_one_regulation_baseline(law):
    """
    建立單一法規初始 Baseline。

    已存在：
    → 跳過，不覆蓋。

    不存在：
    → 取得官方 Snapshot
    → 建立 Baseline。
    """

    pcode = str(
        law.get(
            "pcode",
            ""
        )
    ).strip().upper()

    law_name = str(
        law.get(
            "name",
            ""
        )
    ).strip()

    if not pcode:
        return {
            "Pcode": "",
            "Name":
                law_name,
            "Success":
                False,
            "Action":
                "failed",
            "Date":
                None,
            "ArticleCount":
                0,
            "Error":
                "law_list.json 缺少 pcode"
        }

    try:
        existing = (
            get_existing_regulation_baseline(
                pcode
            )
        )

        if existing:
            return {
                "Pcode":
                    pcode,

                "Name":
                    (
                        existing.get(
                            "law_name"
                        ) or
                        law_name
                    ),

                "Success":
                    True,

                "Action":
                    "skipped",

                "Date":
                    existing.get(
                        "baseline_date"
                    ),

                "ArticleCount":
                    None,

                "Error":
                    None
            }

        snapshot = (
            get_law_snapshot(
                pcode
            )
        )

        if not snapshot.get(
            "success"
        ):
            return {
                "Pcode":
                    pcode,

                "Name":
                    law_name,

                "Success":
                    False,

                "Action":
                    "failed",

                "Date":
                    snapshot.get(
                        "date"
                    ),

                "ArticleCount":
                    0,

                "Error":
                    (
                        snapshot.get(
                            "error"
                        ) or
                        "Snapshot 建立失敗"
                    )
            }

        save_result = (
            upsert_regulation_baseline(
                pcode,
                law_name,
                snapshot
            )
        )

        return {
            "Pcode":
                pcode,

            "Name":
                law_name,

            "Success":
                True,

            "Action":
                "created",

            "Date":
                save_result.get(
                    "baselineDate"
                ),

            "ArticleCount":
                save_result.get(
                    "articleCount"
                ),

            "Error":
                None
        }

    except Exception as exc:
        return {
            "Pcode":
                pcode,

            "Name":
                law_name,

            "Success":
                False,

            "Action":
                "failed",

            "Date":
                None,

            "ArticleCount":
                0,

            "Error":
                str(exc)
        }

def analyze_one_regulation_batch(law):
    """
    批次執行單一法規的新舊條文比對。

    完整 Diff 已保存到 Supabase pending_diff，
    批次回傳只提供摘要，
    避免一次回傳大量完整條文。
    """

    pcode = str(
        law.get(
            "pcode",
            ""
        )
    ).strip().upper()

    law_name = str(
        law.get(
            "name",
            ""
        )
    ).strip()

    if not pcode:
        return {
            "Pcode": "",
            "Name":
                law_name,
            "Success":
                False,
            "Status":
                "invalid_pcode",
            "Changed":
                False,
            "BaselineDate":
                None,
            "CurrentDate":
                None,
            "ChangedCount":
                0,
            "Error":
                "law_list.json 缺少 pcode"
        }

    try:
        result = (
            analyze_regulation_update(
                pcode
            )
        )

        return {
            "Pcode":
                pcode,

            "Name":
                (
                    result.get(
                        "lawName"
                    ) or
                    law_name
                ),

            "Success":
                bool(
                    result.get(
                        "success"
                    )
                ),

            "Status":
                result.get(
                    "status"
                ),

            "Changed":
                bool(
                    result.get(
                        "changed"
                    )
                ),

            "BaselineDate":
                result.get(
                    "baselineDate"
                ),

            "CurrentDate":
                result.get(
                    "currentDate"
                ),

            "ChangedCount":
                int(
                    result.get(
                        "changedCount"
                    ) or 0
                ),

            "Error":
                result.get(
                    "error"
                )
        }

    except Exception as exc:
        return {
            "Pcode":
                pcode,

            "Name":
                law_name,

            "Success":
                False,

            "Status":
                "error",

            "Changed":
                False,

            "BaselineDate":
                None,

            "CurrentDate":
                None,

            "ChangedCount":
                0,

            "Error":
                str(exc)
        }

def fetch_one_law(law):
    pcode = str(
        law.get("pcode", "")
    ).strip().upper()

    name = str(
        law.get("name", "")
    ).strip()

    if not pcode:
        return {
            "Pcode": "",
            "Name": name,
            "LastUpdate": None,
            "RawDate": None,
            "Success": False,
            "Error": "law_list.json 缺少 pcode"
        }

    fetch_result = get_law_date(pcode)

    return {
        "Pcode": pcode,
        "Name": name,
        "LastUpdate": fetch_result["date"],
        "RawDate": fetch_result["rawDate"],
        "Success": bool(fetch_result["date"]),
        "Error": fetch_result["error"]
    }


class handler(BaseHTTPRequestHandler):
    def send_json(self, status_code, payload):
        body = json.dumps(
            payload,
            ensure_ascii=False
        ).encode("utf-8")

        self.send_response(status_code)

        self.send_header(
            "Content-Type",
            "application/json; charset=utf-8"
        )

        self.send_header(
            "Access-Control-Allow-Origin",
            "*"
        )

        self.send_header(
            "Access-Control-Allow-Methods",
            "GET, OPTIONS"
        )

        self.send_header(
            "Access-Control-Allow-Headers",
            "Content-Type"
        )

        # 避免瀏覽器或平台使用舊同步資料
        self.send_header(
            "Cache-Control",
            "no-store, no-cache, must-revalidate, max-age=0"
        )

        self.send_header(
            "Pragma",
            "no-cache"
        )

        self.send_header(
            "Expires",
            "0"
        )

        self.end_headers()
        self.wfile.write(body)

    def do_OPTIONS(self):
        self.send_response(204)

        self.send_header(
            "Access-Control-Allow-Origin",
            "*"
        )

        self.send_header(
            "Access-Control-Allow-Methods",
            "GET, OPTIONS"
        )

        self.send_header(
            "Access-Control-Allow-Headers",
            "Content-Type"
        )

        self.end_headers()

    def do_GET(self):

        started_at = time.time()

        try:
            parsed_url = urlparse(
                self.path
            )

            query = parse_qs(
                parsed_url.query
            )

            mode = str(
                query.get(
                    "mode",
                    [""]
                )[0]
            ).strip().lower()

            # R1-B1：
            # 單一 PCode 完整條文 Snapshot 測試。
            #
            # 不影響目前既有智能同步。
            if mode == "snapshot":

                pcode = str(
                    query.get(
                        "pcode",
                        [""]
                    )[0]
                ).strip().upper()

                if not pcode:
                    self.send_json(
                        400,
                        {
                            "success":
                                False,

                            "error":
                                "缺少 pcode"
                        }
                    )

                    return

                snapshot = (
                    get_law_snapshot(
                        pcode
                    )
                )

                self.send_json(
                    200
                    if snapshot["success"]
                    else 502,
                    snapshot
                )

                return

            if mode == "baseline":

                pcode = str(
                    query.get(
                        "pcode",
                        [""]
                    )[0]
                ).strip().upper()

                law_name = str(
                    query.get(
                        "name",
                        [""]
                    )[0]
                ).strip()

                if not pcode:
                    self.send_json(
                        400,
                        {
                            "success":
                                False,

                            "error":
                                "缺少 pcode"
                        }
                    )

                    return

                snapshot = (
                    get_law_snapshot(
                        pcode
                    )
                )

                if not snapshot["success"]:
                    self.send_json(
                        502,
                        snapshot
                    )

                    return

                try:
                    save_result = (
                        upsert_regulation_baseline(
                            pcode,
                            law_name,
                            snapshot
                        )
                    )

                    self.send_json(
                        200,
                        save_result
                    )

                except Exception as exc:
                    self.send_json(
                        500,
                        {
                            "success":
                                False,

                            "pcode":
                                pcode,

                            "error":
                                str(exc)
                        }
                    )

                return

            if mode == "diff":

                pcode = str(
                    query.get(
                        "pcode",
                        [""]
                    )[0]
                ).strip().upper()

                if not pcode:
                    self.send_json(
                        400,
                        {
                            "success":
                                False,

                            "error":
                                "缺少 pcode"
                        }
                    )

                    return

                try:
                    result = (
                        analyze_regulation_update(
                            pcode
                        )
                    )

                    self.send_json(
                        200
                        if result.get(
                            "success"
                        )
                        else 500,
                        result
                    )

                except Exception as exc:
                    self.send_json(
                        500,
                        {
                            "success":
                                False,

                            "pcode":
                                pcode,

                            "error":
                                str(exc)
                        }
                    )

                return

            if mode == "approve":

                pcode = str(
                    query.get(
                        "pcode",
                        [""]
                    )[0]
                ).strip().upper()

                review_date_raw = str(
                    query.get(
                        "review_date",
                        [""]
                    )[0]
                ).strip()

                review_date = None

                if review_date_raw:
                    review_date = (
                        normalize_regulation_date(
                            review_date_raw
                        )
                    )

                    if not review_date:
                        self.send_json(
                            400,
                            {
                                "success":
                                    False,

                                "pcode":
                                    pcode,

                                "error":
                                    (
                                        "review_date "
                                        "必須為 YYYY-MM-DD"
                                    )
                            }
                        )

                        return

                if not pcode:
                    self.send_json(
                        400,
                        {
                            "success":
                                False,

                            "error":
                                "缺少 pcode"
                        }
                    )

                    return

                try:
                    result = (
                        promote_regulation_pending_to_baseline(
                            pcode
                        )
                    )

                    # 若前端有傳入 review_date，
                    # 在 Baseline 處理成功後，
                    # 同步保存中央最近鑑別日期。
                    if (
                        result.get(
                            "success"
                        ) and
                        review_date
                    ):
                        review_result = (
                            update_regulation_review_date(
                                pcode,
                                review_date
                            )
                        )

                        if not review_result.get(
                            "success"
                        ):
                            result = {
                                "success":
                                    False,

                                "pcode":
                                    pcode,

                                "promoted":
                                    result.get(
                                        "promoted",
                                        False
                                    ),

                                "status":
                                    "review_date_failed",

                                "error":
                                    review_result.get(
                                        "error"
                                    )
                            }

                        else:
                            result[
                                "lastReviewedDate"
                            ] = (
                                review_result.get(
                                    "lastReviewedDate"
                                )
                            )

                    status_code = 200

                    if not result.get(
                        "success"
                    ):
                        if (
                            result.get(
                                "status"
                            ) == "pending_changed"
                        ):
                            status_code = 409

                        else:
                            status_code = 500

                    self.send_json(
                        status_code,
                        result
                    )

                except Exception as exc:
                    self.send_json(
                        500,
                        {
                            "success":
                                False,

                            "pcode":
                                pcode,

                            "promoted":
                                False,

                            "error":
                                str(exc)
                        }
                    )

                return

            if mode == "state-list":

                try:
                    result = (
                        get_regulation_state_list()
                    )

                    self.send_json(
                        200,
                        result
                    )

                except Exception as exc:
                    self.send_json(
                        500,
                        {
                            "success":
                                False,

                            "count":
                                0,

                            "data":
                                [],

                            "error":
                                str(exc)
                        }
                    )

                return

            if mode == "pending-list":

                try:
                    result = (
                        get_regulation_pending_list()
                    )

                    self.send_json(
                        200,
                        result
                    )

                except Exception as exc:
                    self.send_json(
                        500,
                        {
                            "success":
                                False,

                            "count":
                                0,

                            "data":
                                [],

                            "error":
                                str(exc)
                        }
                    )

                return

            if mode == "pending":

                pcode = str(
                    query.get(
                        "pcode",
                        [""]
                    )[0]
                ).strip().upper()

                if not pcode:
                    self.send_json(
                        400,
                        {
                            "success":
                                False,

                            "hasPending":
                                False,

                            "error":
                                "缺少 pcode"
                        }
                    )

                    return

                try:
                    result = (
                        get_regulation_pending_detail(
                            pcode
                        )
                    )

                    status_code = (
                        200
                        if result.get(
                            "success"
                        )
                        else 404
                    )

                    self.send_json(
                        status_code,
                        result
                    )

                except Exception as exc:
                    self.send_json(
                        500,
                        {
                            "success":
                                False,

                            "pcode":
                                pcode,

                            "hasPending":
                                False,

                            "error":
                                str(exc)
                        }
                    )

                return

            if mode == "baseline-all":

                if not os.path.exists(
                    LAW_LIST_PATH
                ):
                    self.send_json(
                        500,
                        {
                            "success":
                                False,

                            "error":
                                (
                                    "找不到法規清單檔案："
                                    f"{LAW_LIST_PATH}"
                                )
                        }
                    )

                    return

                with open(
                    LAW_LIST_PATH,
                    "r",
                    encoding="utf-8"
                ) as file:
                    baseline_law_list = json.load(
                        file
                    )

                if not isinstance(
                    baseline_law_list,
                    list
                ):
                    self.send_json(
                        500,
                        {
                            "success":
                                False,

                            "error":
                                "law_list.json 最外層必須是陣列"
                        }
                    )

                    return

                baseline_results = []

                with ThreadPoolExecutor(
                    max_workers=2
                ) as executor:

                    future_map = {
                        executor.submit(
                            initialize_one_regulation_baseline,
                            law
                        ): law
                        for law in baseline_law_list
                    }

                    for future in as_completed(
                        future_map
                    ):
                        source_law = (
                            future_map[
                                future
                            ]
                        )

                        try:
                            result = future.result()

                        except Exception as exc:
                            result = {
                                "Pcode":
                                    str(
                                        source_law.get(
                                            "pcode",
                                            ""
                                        )
                                    )
                                    .strip()
                                    .upper(),

                                "Name":
                                    source_law.get(
                                        "name",
                                        ""
                                    ),

                                "Success":
                                    False,

                                "Action":
                                    "failed",

                                "Date":
                                    None,

                                "ArticleCount":
                                    0,

                                "Error":
                                    str(exc)
                            }

                        baseline_results.append(
                            result
                        )

                baseline_order_map = {
                    str(
                        law.get(
                            "pcode",
                            ""
                        )
                    )
                    .strip()
                    .upper():
                        index

                    for index, law
                    in enumerate(
                        baseline_law_list
                    )
                }

                baseline_results.sort(
                    key=lambda item:
                        baseline_order_map.get(
                            item.get(
                                "Pcode",
                                ""
                            ),
                            999999
                        )
                )

                created_count = sum(
                    1
                    for item
                    in baseline_results
                    if (
                        item.get(
                            "Success"
                        ) and
                        item.get(
                            "Action"
                        ) == "created"
                    )
                )

                skipped_count = sum(
                    1
                    for item
                    in baseline_results
                    if (
                        item.get(
                            "Success"
                        ) and
                        item.get(
                            "Action"
                        ) == "skipped"
                    )
                )

                failed_count = sum(
                    1
                    for item
                    in baseline_results
                    if not item.get(
                        "Success"
                    )
                )

                self.send_json(
                    200,
                    {
                        "success":
                            failed_count == 0,

                        "count":
                            len(
                                baseline_results
                            ),

                        "createdCount":
                            created_count,

                        "skippedCount":
                            skipped_count,

                        "failedCount":
                            failed_count,

                        "elapsedSeconds":
                            round(
                                time.time()
                                - started_at,
                                2
                            ),

                        "data":
                            baseline_results
                    }
                )

                return

            if mode == "diff-all":

                if not os.path.exists(
                    LAW_LIST_PATH
                ):
                    self.send_json(
                        500,
                        {
                            "success":
                                False,

                            "error":
                                (
                                    "找不到法規清單檔案："
                                    f"{LAW_LIST_PATH}"
                                )
                        }
                    )

                    return

                with open(
                    LAW_LIST_PATH,
                    "r",
                    encoding="utf-8"
                ) as file:
                    diff_law_list = (
                        json.load(
                            file
                        )
                    )

                if not isinstance(
                    diff_law_list,
                    list
                ):
                    self.send_json(
                        500,
                        {
                            "success":
                                False,

                            "error":
                                (
                                    "law_list.json "
                                    "最外層必須是陣列"
                                )
                        }
                    )

                    return

                diff_results = []

                # 完整條文同步與 Diff
                # 同時最多處理 2 部法規。
                #
                # 每一部法規只向官方網站
                # 發出一次 Snapshot Request。
                with ThreadPoolExecutor(
                    max_workers=2
                ) as executor:

                    future_map = {
                        executor.submit(
                            analyze_one_regulation_batch,
                            law
                        ): law

                        for law in diff_law_list
                    }

                    for future in as_completed(
                        future_map
                    ):
                        source_law = (
                            future_map[
                                future
                            ]
                        )

                        try:
                            result = (
                                future.result()
                            )

                        except Exception as exc:
                            result = {
                                "Pcode":
                                    str(
                                        source_law.get(
                                            "pcode",
                                            ""
                                        )
                                    )
                                    .strip()
                                    .upper(),

                                "Name":
                                    source_law.get(
                                        "name",
                                        ""
                                    ),

                                "Success":
                                    False,

                                "Status":
                                    "error",

                                "Changed":
                                    False,

                                "BaselineDate":
                                    None,

                                "CurrentDate":
                                    None,

                                "ChangedCount":
                                    0,

                                "Error":
                                    str(exc)
                            }

                        diff_results.append(
                            result
                        )

                diff_order_map = {
                    str(
                        law.get(
                            "pcode",
                            ""
                        )
                    )
                    .strip()
                    .upper():
                        index

                    for index, law
                    in enumerate(
                        diff_law_list
                    )
                }

                diff_results.sort(
                    key=lambda item:
                        diff_order_map.get(
                            item.get(
                                "Pcode",
                                ""
                            ),
                            999999
                        )
                )

                changed_law_count = sum(
                    1
                    for item
                    in diff_results
                    if (
                        item.get(
                            "Success"
                        ) and
                        item.get(
                            "Changed"
                        )
                    )
                )

                no_change_count = sum(
                    1
                    for item
                    in diff_results
                    if (
                        item.get(
                            "Success"
                        ) and
                        item.get(
                            "Status"
                        ) == "no_change"
                    )
                )

                failed_count = sum(
                    1
                    for item
                    in diff_results
                    if not item.get(
                        "Success"
                    )
                )

                total_changed_articles = sum(
                    int(
                        item.get(
                            "ChangedCount"
                        ) or 0
                    )
                    for item
                    in diff_results
                    if item.get(
                        "Success"
                    )
                )

                self.send_json(
                    200,
                    {
                        "success":
                            failed_count == 0,

                        "count":
                            len(
                                diff_results
                            ),

                        "changedLawCount":
                            changed_law_count,

                        "noChangeCount":
                            no_change_count,

                        "failedCount":
                            failed_count,

                        "totalChangedArticles":
                            total_changed_articles,

                        "elapsedSeconds":
                            round(
                                time.time()
                                - started_at,
                                2
                            ),

                        "data":
                            diff_results
                    }
                )

                return

            if not os.path.exists(LAW_LIST_PATH):
                raise FileNotFoundError(
                    f"找不到法規清單檔案：{LAW_LIST_PATH}"
                )

            with open(
                LAW_LIST_PATH,
                "r",
                encoding="utf-8"
            ) as file:
                law_list = json.load(file)

            if not isinstance(law_list, list):
                raise ValueError(
                    "law_list.json 最外層必須是陣列"
                )

            results = []

            # 同時最多三筆，避免請求過密或被限制
            with ThreadPoolExecutor(
                max_workers=3
            ) as executor:

                future_map = {
                    executor.submit(
                        fetch_one_law,
                        law
                    ): law
                    for law in law_list
                }

                for future in as_completed(future_map):
                    source_law = future_map[future]

                    try:
                        result = future.result()

                    except Exception as exc:
                        result = {
                            "Pcode": source_law.get(
                                "pcode",
                                ""
                            ),
                            "Name": source_law.get(
                                "name",
                                ""
                            ),
                            "LastUpdate": None,
                            "RawDate": None,
                            "Success": False,
                            "Error": (
                                "工作執行失敗："
                                f"{str(exc)}"
                            )
                        }

                    results.append(result)

            # 依 law_list.json 原始順序排列
            order_map = {
                str(
                    law.get("pcode", "")
                ).strip().upper(): index
                for index, law in enumerate(law_list)
            }

            results.sort(
                key=lambda item: order_map.get(
                    item["Pcode"],
                    999999
                )
            )

            success_count = sum(
                1
                for item in results
                if item["Success"]
            )

            failed_count = (
                len(results) - success_count
            )

            failed_items = [
                {
                    "Pcode": item["Pcode"],
                    "Name": item["Name"],
                    "Error": item["Error"]
                }
                for item in results
                if not item["Success"]
            ]

            self.send_json(
                200,
                {
                    "success": success_count > 0,
                    "count": len(results),
                    "successCount": success_count,
                    "failedCount": failed_count,
                    "updatedAt": time.strftime(
                        "%Y-%m-%d %H:%M:%S"
                    ),
                    "elapsedSeconds": round(
                        time.time() - started_at,
                        2
                    ),
                    "data": results,
                    "failedItems": failed_items
                }
            )

        except Exception as exc:
            self.send_json(
                500,
                {
                    "success": False,
                    "count": 0,
                    "successCount": 0,
                    "failedCount": 0,
                    "error": str(exc),
                    "data": [],
                    "failedItems": []
                }
            )
