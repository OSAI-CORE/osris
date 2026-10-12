from http.server import BaseHTTPRequestHandler
import json

import os

import re

import time

import hashlib
import base64
import hmac

import requests

import xml.etree.ElementTree as ET

from html.parser import HTMLParser
from html import escape as html_escape
from difflib import SequenceMatcher

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

# =========================================================
# OSAI Core 中央權限
# =========================================================
#
# 與 Supabase：
# osai-system-access
#
# 共用相同的 Session HMAC Secret。
#
# Secret 僅存在 Vercel Backend Environment，
# 絕不可傳到前端。
# =========================================================

OSAI_ACCESS_SESSION_SECRET = (
    os.getenv(
        "OSAI_ACCESS_SESSION_SECRET",
        ""
    )
    .strip()
)

OSAI_ACCESS_SYSTEM_TYPE = (
    "regulation-identification"
)

OSAI_ACCESS_CREDENTIALS_TABLE = (
    "osai_access_credentials"
)

OSAI_ACCESS_SETTINGS_TABLE = (
    "osai_system_access_settings"
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

# =========================================================
# OSAI Core Session 驗證
# =========================================================

class RegulationAccessError(
    Exception
):
    def __init__(
        self,
        status_code,
        code
    ):
        super().__init__(
            str(code)
        )

        self.status_code = int(
            status_code
        )

        self.code = str(
            code
        )


def decode_base64url_bytes(
    value
):
    normalized = str(
        value or ""
    ).strip()

    padding = (
        "=" *
        (
            (
                4 -
                len(normalized) % 4
            ) % 4
        )
    )

    return (
        base64.urlsafe_b64decode(
            (
                normalized +
                padding
            ).encode(
                "ascii"
            )
        )
    )


def verify_osai_session_token(
    token
):
    """
    驗證 OSAI Core
    osai-system-access 所簽發的 Session。

    Token 格式：
    base64url(payload)
    .
    HMAC-SHA256(signature)
    """

    if not OSAI_ACCESS_SESSION_SECRET:
        raise RuntimeError(
            "OSAI_ACCESS_SESSION_SECRET_MISSING"
        )

    normalized_token = str(
        token or ""
    ).strip()

    parts = normalized_token.split(
        "."
    )

    if len(parts) != 2:
        raise RegulationAccessError(
            401,
            "SYSTEM_SESSION_INVALID"
        )

    payload_part = parts[0]
    signature_part = parts[1]

    try:
        actual_signature = (
            decode_base64url_bytes(
                signature_part
            )
        )

    except Exception:
        raise RegulationAccessError(
            401,
            "SYSTEM_SESSION_INVALID"
        )

    expected_signature = (
        hmac.new(
            OSAI_ACCESS_SESSION_SECRET
                .encode(
                    "utf-8"
                ),
            payload_part.encode(
                "utf-8"
            ),
            hashlib.sha256
        )
        .digest()
    )

    if not hmac.compare_digest(
        actual_signature,
        expected_signature
    ):
        raise RegulationAccessError(
            401,
            "SYSTEM_SESSION_INVALID"
        )

    try:
        payload = json.loads(
            decode_base64url_bytes(
                payload_part
            ).decode(
                "utf-8"
            )
        )

    except Exception:
        raise RegulationAccessError(
            401,
            "SYSTEM_SESSION_INVALID"
        )

    if not isinstance(
        payload,
        dict
    ):
        raise RegulationAccessError(
            401,
            "SYSTEM_SESSION_INVALID"
        )

    if (
        int(
            payload.get(
                "version"
            ) or 0
        ) != 1
    ):
        raise RegulationAccessError(
            401,
            "SYSTEM_SESSION_INVALID"
        )

    role = str(
        payload.get(
            "role"
        ) or ""
    ).strip().lower()

    if role not in (
        "admin",
        "editor"
    ):
        raise RegulationAccessError(
            401,
            "SYSTEM_SESSION_INVALID"
        )

    system_type = str(
        payload.get(
            "system_type"
        ) or ""
    ).strip()

    if (
        system_type !=
        OSAI_ACCESS_SYSTEM_TYPE
    ):
        raise RegulationAccessError(
            403,
            "SYSTEM_SESSION_MISMATCH"
        )

    try:
        expires_at = int(
            payload.get(
                "exp"
            ) or 0
        )

    except (
        TypeError,
        ValueError
    ):
        expires_at = 0

    # OSAI Core Token 的 exp
    # 使用 JavaScript Date.now()，
    # 因此單位為毫秒。
    now_ms = int(
        time.time() *
        1000
    )

    if expires_at <= now_ms:
        raise RegulationAccessError(
            401,
            "SYSTEM_SESSION_EXPIRED"
        )

    try:
        revision = int(
            payload.get(
                "revision"
            ) or 0
        )

    except (
        TypeError,
        ValueError
    ):
        revision = 0

    if revision <= 0:
        raise RegulationAccessError(
            401,
            "SYSTEM_SESSION_INVALID"
        )

    return payload


def get_osai_access_credentials_state():
    """
    取得中央 Admin / Editor
    目前正式 revision。

    用途：
    密碼變更後立即讓舊 Session 失效。
    """

    if (
        not REGULATION_SUPABASE_URL or
        not REGULATION_SUPABASE_SERVICE_ROLE_KEY
    ):
        raise RuntimeError(
            "REGULATION_SUPABASE_CONFIG_MISSING"
        )

    url = (
        f"{REGULATION_SUPABASE_URL}"
        f"/rest/v1/"
        f"{OSAI_ACCESS_CREDENTIALS_TABLE}"
    )

    response = requests.get(
        url,
        headers={
            "apikey":
                REGULATION_SUPABASE_SERVICE_ROLE_KEY,

            "Accept":
                "application/json"
        },
        params={
            "id":
                "eq.global",

            "select":
                (
                    "admin_revision,"
                    "editor_revision"
                ),

            "limit":
                "1"
        },
        timeout=(
            8,
            20
        )
    )

    if not response.ok:
        raise RuntimeError(
            "OSAI_ACCESS_CREDENTIALS_QUERY_FAILED:"
            f"{response.status_code}"
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
        raise RuntimeError(
            "OSAI_ACCESS_CREDENTIALS_NOT_FOUND"
        )

    return rows[0]


def get_osai_system_access_setting():
    """
    取得法規系統目前：
    - editor_enabled
    - system_revision
    """

    url = (
        f"{REGULATION_SUPABASE_URL}"
        f"/rest/v1/"
        f"{OSAI_ACCESS_SETTINGS_TABLE}"
    )

    response = requests.get(
        url,
        headers={
            "apikey":
                REGULATION_SUPABASE_SERVICE_ROLE_KEY,

            "Accept":
                "application/json"
        },
        params={
            "system_type":
                (
                    "eq."
                    f"{OSAI_ACCESS_SYSTEM_TYPE}"
                ),

            "select":
                (
                    "editor_enabled,"
                    "system_revision"
                ),

            "limit":
                "1"
        },
        timeout=(
            8,
            20
        )
    )

    if not response.ok:
        raise RuntimeError(
            "OSAI_ACCESS_SETTINGS_QUERY_FAILED:"
            f"{response.status_code}"
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
        raise RuntimeError(
            "OSAI_ACCESS_SETTINGS_NOT_FOUND"
        )

    return rows[0]


def validate_osai_access_session(
    authorization_header,
    allowed_roles
):
    """
    驗證：
    1. Bearer Token
    2. HMAC Signature
    3. Token Expiry
    4. system_type
    5. Admin / Editor revision
    6. Editor Enabled / system_revision
    7. 此 API 所允許角色
    """

    authorization = str(
        authorization_header or ""
    ).strip()

    if not authorization.lower().startswith(
        "bearer "
    ):
        raise RegulationAccessError(
            401,
            "SYSTEM_SESSION_INVALID"
        )

    token = authorization[
        7:
    ].strip()

    if not token:
        raise RegulationAccessError(
            401,
            "SYSTEM_SESSION_INVALID"
        )

    session = (
        verify_osai_session_token(
            token
        )
    )

    role = str(
        session.get(
            "role"
        ) or ""
    ).strip().lower()

    normalized_allowed_roles = {
        str(
            item
        )
        .strip()
        .lower()

        for item in (
            allowed_roles or []
        )
    }

    if (
        role not in
        normalized_allowed_roles
    ):
        if (
            normalized_allowed_roles ==
            {
                "admin"
            }
        ):
            raise RegulationAccessError(
                403,
                "ADMIN_PERMISSION_REQUIRED"
            )

        raise RegulationAccessError(
            403,
            "SYSTEM_PERMISSION_REQUIRED"
        )

    credentials = (
        get_osai_access_credentials_state()
    )

    if role == "admin":

        expected_revision = int(
            credentials.get(
                "admin_revision"
            ) or 0
        )

        if (
            int(
                session.get(
                    "revision"
                ) or 0
            ) !=
            expected_revision
        ):
            raise RegulationAccessError(
                401,
                "SYSTEM_SESSION_EXPIRED"
            )

    elif role == "editor":

        expected_revision = int(
            credentials.get(
                "editor_revision"
            ) or 0
        )

        if (
            int(
                session.get(
                    "revision"
                ) or 0
            ) !=
            expected_revision
        ):
            raise RegulationAccessError(
                401,
                "SYSTEM_SESSION_EXPIRED"
            )

        setting = (
            get_osai_system_access_setting()
        )

        if (
            setting.get(
                "editor_enabled"
            ) is not True
        ):
            raise RegulationAccessError(
                403,
                "EDITOR_DISABLED"
            )

        try:
            token_system_revision = int(
                session.get(
                    "system_revision"
                ) or 0
            )

            current_system_revision = int(
                setting.get(
                    "system_revision"
                ) or 0
            )

        except (
            TypeError,
            ValueError
        ):
            token_system_revision = 0
            current_system_revision = -1

        if (
            token_system_revision <= 0 or
            token_system_revision !=
                current_system_revision
        ):
            raise RegulationAccessError(
                401,
                "SYSTEM_SESSION_EXPIRED"
            )

    return session

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

def build_regulation_highlight_html(
    old_text,
    new_text
):
    """
    將單一條文的舊版與新版內容，
    轉換成鑑別工作台原有的紅綠差異格式。

    保留：
    - 未異動文字
    - 完整條文內容

    自動加入：
    <del>刪除文字</del>
    <ins>新增文字</ins>

    官方文字會先 HTML Escape，
    避免條文本身的特殊字元
    被瀏覽器當成 HTML 執行。
    """

    old_value = str(
        old_text or ""
    )

    new_value = str(
        new_text or ""
    )

    matcher = SequenceMatcher(
        None,
        old_value,
        new_value,
        autojunk=False
    )

    html_parts = []

    for (
        tag,
        old_start,
        old_end,
        new_start,
        new_end
    ) in matcher.get_opcodes():

        old_piece = html_escape(
            old_value[
                old_start:
                old_end
            ],
            quote=False
        )

        new_piece = html_escape(
            new_value[
                new_start:
                new_end
            ],
            quote=False
        )

        if tag == "equal":

            html_parts.append(
                new_piece
            )

        elif tag == "replace":

            if old_piece:
                html_parts.append(
                    f"<del>{old_piece}</del>"
                )

            if new_piece:
                html_parts.append(
                    f"<ins>{new_piece}</ins>"
                )

        elif tag == "delete":

            if old_piece:
                html_parts.append(
                    f"<del>{old_piece}</del>"
                )

        elif tag == "insert":

            if new_piece:
                html_parts.append(
                    f"<ins>{new_piece}</ins>"
                )

    return "".join(
        html_parts
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

    同時產生：
    newHtml

    newHtml：
    供目前鑑別工作台直接使用，
    自動以 <del> / <ins>
    顯示真正刪除與新增的文字。

    原始 old / new 仍完整保留，
    不影響 Baseline、Pending
    與後續版本升格。
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
        if isinstance(
            item,
            dict
        )
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
        if isinstance(
            item,
            dict
        )
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

    for article_no in (
        ordered_article_numbers
    ):

        old_text = old_map.get(
            article_no
        )

        new_text = new_map.get(
            article_no
        )

        # -----------------------------------------------------
        # 新增條文
        # -----------------------------------------------------

        if (
            old_text is None and
            new_text is not None
        ):

            safe_new_text = html_escape(
                new_text,
                quote=False
            )

            changed_rows.append({
                "no":
                    article_no,

                "changeType":
                    "added",

                "old":
                    "",

                "new":
                    new_text,

                "newHtml":
                    (
                        f"<ins>"
                        f"{safe_new_text}"
                        f"</ins>"
                    ),

                "note":
                    "新增條文"
            })

            continue

        # -----------------------------------------------------
        # 刪除條文
        # -----------------------------------------------------

        if (
            old_text is not None and
            new_text is None
        ):

            safe_old_text = html_escape(
                old_text,
                quote=False
            )

            changed_rows.append({
                "no":
                    article_no,

                "changeType":
                    "removed",

                "old":
                    old_text,

                "new":
                    "",

                "newHtml":
                    (
                        f"<del>"
                        f"{safe_old_text}"
                        f"</del>"
                    ),

                "note":
                    "刪除條文"
            })

            continue

        # -----------------------------------------------------
        # 修改條文
        # -----------------------------------------------------

        if old_text != new_text:

            highlighted_html = (
                build_regulation_highlight_html(
                    old_text,
                    new_text
                )
            )

            changed_rows.append({
                "no":
                    article_no,

                "changeType":
                    "modified",

                "old":
                    old_text,

                "new":
                    new_text,

                "newHtml":
                    highlighted_html,

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
                f"eq.{normalized_pcode}",

            "status":
                "eq.baseline_ready"
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

            "status":
                "pending_changed",

            "error":
                (
                    "法規狀態在完成鑑別期間已變更，"
                    "請重新載入比對詳情後再完成鑑別"
                )
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

def update_all_regulation_review_dates(
    review_date,
    monitored_pcodes=None
):
    """
    將目前法規 Baseline 表內所有法規的
    最近鑑別／登錄日同步為指定日期。

    僅修改：
    last_reviewed_date
    updated_at

    不修改：
    baseline
    pending
    status
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

    normalized_date = (
        normalize_regulation_date(
            review_date
        )
    )

    if not normalized_date:
        return {
            "success":
                False,

            "updatedCount":
                0,

            "lastReviewedDate":
                None,

            "error":
                "鑑別日期格式錯誤"
        }

    # ---------------------------------------------------------
    # 若前端有傳入目前監控 PCode，
    # 本次「同步鑑別」只允許作用於這些法規。
    #
    # monitored_pcodes = None
    # → 保留舊版全部 Baseline 相容模式。
    # ---------------------------------------------------------

    target_pcodes = None

    if monitored_pcodes is not None:

        if (
            not isinstance(
                monitored_pcodes,
                list
            ) or
            len(monitored_pcodes) == 0
        ):
            return {
                "success":
                    False,

                "status":
                    "invalid_scope",

                "updatedCount":
                    0,

                "lastReviewedDate":
                    None,

                "error":
                    "目前沒有可同步鑑別的監控法規"
            }

        normalized_pcodes = []

        seen_pcodes = set()

        for item in monitored_pcodes:

            pcode = str(
                item or ""
            ).strip().upper()

            if not re.fullmatch(
                r"[A-Z]\d{7}",
                pcode
            ):
                return {
                    "success":
                        False,

                    "status":
                        "invalid_scope",

                    "updatedCount":
                        0,

                    "lastReviewedDate":
                        None,

                    "error":
                        (
                            "同步鑑別範圍包含無效 PCode："
                            f"{pcode or '空白'}"
                        )
                }

            if pcode in seen_pcodes:
                continue

            seen_pcodes.add(
                pcode
            )

            normalized_pcodes.append(
                pcode
            )

        target_pcodes = (
            normalized_pcodes
        )

        # -----------------------------------------------------
        # 同步鑑別前確認：
        # 目前所有監控法規都必須已有中央 Baseline。
        #
        # 新法規若尚未執行第一次智能同步，
        # 不能直接被標示成「今日已鑑別」。
        # -----------------------------------------------------

        state_result = (
            get_regulation_state_list()
        )

        state_items = (
            state_result.get(
                "data",
                []
            )
            if isinstance(
                state_result,
                dict
            )
            else []
        )

        if not isinstance(
            state_items,
            list
        ):
            state_items = []

        existing_pcodes = {
            str(
                item.get(
                    "Pcode"
                ) or ""
            )
            .strip()
            .upper()

            for item in state_items

            if isinstance(
                item,
                dict
            )
        }

        missing_pcodes = [
            pcode
            for pcode in target_pcodes
            if pcode not in existing_pcodes
        ]

        if missing_pcodes:
            return {
                "success":
                    False,

                "status":
                    "baseline_missing",

                "updatedCount":
                    0,

                "missingCount":
                    len(
                        missing_pcodes
                    ),

                "missingPcodes":
                    missing_pcodes,

                "lastReviewedDate":
                    None,

                "error":
                    (
                        "目前有新增法規尚未建立中央 Baseline，"
                        "請先執行智能同步"
                    )
            }

    # ---------------------------------------------------------
    # 同步所有鑑別日期前，
    # 必須先確認目前沒有任何等待人工確認的 Pending。
    #
    # 只要仍有一部 pending_review：
    # → 整批不更新
    # → 避免尚未人工閱讀的新法規
    #   被誤標記為「今日已完成鑑別」。
    # ---------------------------------------------------------

    pending_result = (
        get_regulation_pending_list()
    )

    pending_items = (
        pending_result.get(
            "data",
            []
        )
        if isinstance(
            pending_result,
            dict
        )
        else []
    )

    if not isinstance(
        pending_items,
        list
    ):
        pending_items = []

    # ---------------------------------------------------------
    # 新資料驅動架構：
    #
    # 歷史 Baseline 即使仍保留於 Supabase，
    # 只要已不在目前監控 laws，
    # 就不應阻止目前監控法規同步鑑別。
    # ---------------------------------------------------------

    if target_pcodes is not None:

        target_pcode_set = set(
            target_pcodes
        )

        pending_items = [
            item
            for item in pending_items

            if (
                isinstance(
                    item,
                    dict
                ) and
                str(
                    item.get(
                        "Pcode"
                    ) or ""
                )
                .strip()
                .upper()
                in target_pcode_set
            )
        ]

    if pending_items:
        pending_pcodes = [
            str(
                item.get(
                    "Pcode"
                ) or ""
            )
            .strip()
            .upper()

            for item in pending_items

            if isinstance(
                item,
                dict
            )
        ]

        pending_pcodes = [
            pcode
            for pcode in pending_pcodes
            if pcode
        ]

        return {
            "success":
                False,

            "status":
                "pending_exists",

            "updatedCount":
                0,

            "pendingCount":
                len(
                    pending_items
                ),

            "pendingPcodes":
                pending_pcodes,

            "lastReviewedDate":
                None,

            "error":
                (
                    f"目前仍有 {len(pending_items)} 部法規"
                    "等待人工完成鑑別，"
                    "因此本次未同步任何法規的鑑別日期"
                )
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

    # ---------------------------------------------------------
    # 有明確監控範圍：
    # → 只更新目前 laws 中的 PCode。
    #
    # 沒有傳範圍：
    # → 保留舊版全部 Baseline 相容模式。
    #
    # status=baseline_ready：
    # → 即使 Pending 在前置檢查後突然產生，
    #   也不會更新該 Pending 法規的鑑別日期。
    # ---------------------------------------------------------

    pcode_filter = (
        (
            "in.(" +
            ",".join(
                target_pcodes
            ) +
            ")"
        )
        if target_pcodes is not None
        else "not.is.null"
    )

    response = requests.patch(
        url,
        headers=headers,
        params={
            "pcode":
                pcode_filter,

            "status":
                "eq.baseline_ready"
        },
        json={
            "last_reviewed_date":
                normalized_date,

            "updated_at":
                now_iso
        },
        timeout=(8, 30)
    )

    if not response.ok:
        raise RuntimeError(
            "Supabase 全部鑑別日期更新失敗："
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

    updated_count = len(
        rows
    )

    # ---------------------------------------------------------
    # 若有指定目前監控範圍，
    # 但實際更新筆數不同，
    # 代表前置檢查後中央狀態又發生變化。
    #
    # 前端此時不能把全部日期一起改掉。
    # ---------------------------------------------------------

    if (
        target_pcodes is not None and
        updated_count !=
            len(target_pcodes)
    ):
        return {
            "success":
                False,

            "status":
                "state_changed",

            "updatedCount":
                updated_count,

            "expectedCount":
                len(
                    target_pcodes
                ),

            "lastReviewedDate":
                None,

            "error":
                (
                    "同步鑑別期間中央法規狀態已變更，"
                    "請重新整理後再執行"
                )
        }

    return {
        "success":
            True,

        "updatedCount":
            updated_count,

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
    pcode,
    expected_pending_hash=None,
    expected_pending_state=None
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

    expected_hash = str(
        expected_pending_hash or ""
    ).strip()

    expected_state = str(
        expected_pending_state or ""
    ).strip().lower()

    current_has_pending = (
        current_status == "pending_review" and
        bool(
            pending_date
        ) and
        isinstance(
            pending_articles,
            list
        ) and
        bool(
            pending_articles
        ) and
        bool(
            pending_hash
        )
    )

    # ---------------------------------------------------------
    # 鎖定使用者實際看到的 Pending 狀態
    #
    # expected_state = "pending"
    # → 使用者看到 Pending，必須確認 Hash 相同。
    #
    # expected_state = "none"
    # → 使用者看到沒有 Pending，
    #   此時若中央突然出現 Pending，也必須阻止。
    #
    # expected_state 未傳入：
    # → 保留舊版 expected_pending_hash 相容行為。
    # ---------------------------------------------------------

    pending_expectation_changed = False

    if expected_state == "none":

        pending_expectation_changed = (
            current_has_pending
        )

    elif expected_state == "pending":

        pending_expectation_changed = (
            not expected_hash or
            not current_has_pending or
            pending_hash != expected_hash
        )

    elif expected_hash:

        # 向下相容舊版前端。
        pending_expectation_changed = (
            not current_has_pending or
            pending_hash != expected_hash
        )

    if pending_expectation_changed:
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
                    "鑑別工作台所檢視的法規狀態已變更，"
                    "請重新載入比對詳情後再完成鑑別"
                )
        }

    # 沒有 Pending 時採冪等處理：
    # 重複按完成鑑別也不會破壞 Baseline。

    if not current_has_pending:
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
        # -----------------------------------------------------
        # 每次批次智能同步前，
        # 先確認這部法規是否已有中央 Baseline。
        #
        # 已存在：
        # → initialize_one_regulation_baseline 只會 skipped，
        #   絕不覆蓋既有 Baseline。
        #
        # 不存在：
        # → 自動向全國法規資料庫取得目前正式版本，
        #   建立第一份 Baseline。
        # -----------------------------------------------------

        baseline_result = (
            initialize_one_regulation_baseline(
                law
            )
        )

        if not baseline_result.get(
            "Success"
        ):
            return {
                "Pcode":
                    pcode,

                "Name":
                    (
                        baseline_result.get(
                            "Name"
                        ) or
                        law_name
                    ),

                "Success":
                    False,

                "Status":
                    "baseline_init_failed",

                "Changed":
                    False,

                "BaselineDate":
                    None,

                "CurrentDate":
                    baseline_result.get(
                        "Date"
                    ),

                "ChangedCount":
                    0,

                "Error":
                    (
                        baseline_result.get(
                            "Error"
                        ) or
                        "Baseline 初始化失敗"
                    )
            }

        # -----------------------------------------------------
        # 新法規第一次進入系統：
        #
        # 剛建立的 Baseline 本身就是目前官方最新版，
        # 因此這次不再重複向官方網站抓第二次，
        # 也不建立假 Pending。
        # -----------------------------------------------------

        if (
            baseline_result.get(
                "Action"
            ) == "created"
        ):
            initialized_date = (
                baseline_result.get(
                    "Date"
                )
            )

            return {
                "Pcode":
                    pcode,

                "Name":
                    (
                        baseline_result.get(
                            "Name"
                        ) or
                        law_name
                    ),

                "Success":
                    True,

                "Status":
                    "baseline_initialized",

                "Changed":
                    False,

                "BaselineDate":
                    initialized_date,

                "CurrentDate":
                    initialized_date,

                "ChangedCount":
                    0,

                "Error":
                    None
            }

        # 既有法規：
        # 繼續執行原本 Baseline VS 官方最新版。
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

    def get_allowed_cors_origin(
        self
    ):
        """
        /api/sync-laws 使用相對網址，
        正式情況應為同來源請求。

        只有 Origin 與目前 Host 相同時，
        才回傳 CORS Header。
        """

        origin = str(
            self.headers.get(
                "Origin",
                ""
            )
            or ""
        ).strip()

        if not origin:
            return ""

        host = str(
            self.headers.get(
                "Host",
                ""
            )
            or ""
        ).strip().lower()

        try:
            parsed_origin = (
                urlparse(
                    origin
                )
            )

        except Exception:
            return ""

        if (
            parsed_origin.scheme not in
            (
                "http",
                "https"
            )
        ):
            return ""

        if (
            parsed_origin.netloc
                .strip()
                .lower() !=
            host
        ):
            return ""

        return origin

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

        cors_origin = (
            self.get_allowed_cors_origin()
        )

        if cors_origin:
            self.send_header(
                "Access-Control-Allow-Origin",
                cors_origin
            )

            self.send_header(
                "Vary",
                "Origin"
            )

        self.send_header(
            "Access-Control-Allow-Methods",
            "GET, POST, OPTIONS"
        )

        self.send_header(
            "Access-Control-Allow-Headers",
            (
                "Content-Type, "
                "Authorization"
            )
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

    def require_osai_roles(
        self,
        allowed_roles
    ):
        """
        驗證目前 /api/sync-laws
        寫入型操作的中央 Session。
        """

        try:
            return (
                validate_osai_access_session(
                    self.headers.get(
                        "Authorization",
                        ""
                    ),
                    allowed_roles
                )
            )

        except RegulationAccessError as exc:

            self.send_json(
                exc.status_code,
                {
                    "success":
                        False,

                    "error":
                        exc.code
                }
            )

            return None

        except Exception as exc:

            print(
                "OSAI API Session 驗證失敗：",
                str(exc)
            )

            self.send_json(
                503,
                {
                    "success":
                        False,

                    "error":
                        "ACCESS_STATE_UNAVAILABLE"
                }
            )

            return None

    def do_OPTIONS(self):

        request_origin = str(
            self.headers.get(
                "Origin",
                ""
            )
            or ""
        ).strip()

        cors_origin = (
            self.get_allowed_cors_origin()
        )

        # 有 Origin，
        # 但不是目前網站本身，
        # 直接拒絕跨來源呼叫。
        if (
            request_origin and
            not cors_origin
        ):
            self.send_response(
                403
            )

            self.end_headers()

            return

        self.send_response(
            204
        )

        if cors_origin:
            self.send_header(
                "Access-Control-Allow-Origin",
                cors_origin
            )

            self.send_header(
                "Vary",
                "Origin"
            )

        self.send_header(
            "Access-Control-Allow-Methods",
            "GET, POST, OPTIONS"
        )

        self.send_header(
            "Access-Control-Allow-Headers",
            (
                "Content-Type, "
                "Authorization"
            )
        )

        self.end_headers()

    def do_POST(self):
        """
        寫入型 Regulation API。

        外部 POST：
        JSON Body
            ↓
        轉成目前既有 query 介面
            ↓
        共用原本成熟的 mode 處理流程

        這樣不需要重寫：
        - baseline
        - diff
        - approve
        - review-all
        - diff-all

        等既有邏輯。
        """

        try:
            content_type = str(
                self.headers.get(
                    "Content-Type",
                    ""
                )
                or ""
            ).lower()

            if (
                "application/json"
                not in content_type
            ):
                self.send_json(
                    415,
                    {
                        "success":
                            False,

                        "error":
                            "POST 請求必須使用 application/json"
                    }
                )

                return

            content_length_text = str(
                self.headers.get(
                    "Content-Length",
                    "0"
                )
                or "0"
            ).strip()

            try:
                content_length = int(
                    content_length_text
                )

            except ValueError:
                content_length = 0

            if content_length <= 0:
                self.send_json(
                    400,
                    {
                        "success":
                            False,

                        "error":
                            "POST Body 不能為空白"
                    }
                )

                return

            # 目前最多約 100 部法規，
            # 1 MB 已遠高於實際需要。
            if content_length > (
                1024 *
                1024
            ):
                self.send_json(
                    413,
                    {
                        "success":
                            False,

                        "error":
                            "POST Body 超過允許大小"
                    }
                )

                return

            raw_body = (
                self.rfile.read(
                    content_length
                )
            )

            try:
                payload = json.loads(
                    raw_body.decode(
                        "utf-8"
                    )
                )

            except (
                UnicodeDecodeError,
                json.JSONDecodeError
            ):
                self.send_json(
                    400,
                    {
                        "success":
                            False,

                        "error":
                            "POST JSON 格式錯誤"
                    }
                )

                return

            if not isinstance(
                payload,
                dict
            ):
                self.send_json(
                    400,
                    {
                        "success":
                            False,

                        "error":
                            "POST JSON 最外層必須為物件"
                    }
                )

                return

            mode = str(
                payload.get(
                    "mode",
                    ""
                )
                or ""
            ).strip().lower()

            # 只有真正寫入型 API
            # 可以使用 POST。
            allowed_post_modes = {
                "baseline",
                "baseline-all",
                "diff",
                "diff-all",
                "approve",
                "review-all"
            }

            if mode not in (
                allowed_post_modes
            ):
                self.send_json(
                    405,
                    {
                        "success":
                            False,

                        "error":
                            "此 API 不接受 POST"
                    }
                )

                return

            # -------------------------------------------------
            # 將 JSON Body 暫時轉成
            # parse_qs 相同的：
            #
            # {
            #   "mode": ["diff-all"],
            #   "laws": ["[...]"]
            # }
            #
            # 供既有成熟 mode 邏輯共用。
            # -------------------------------------------------

            post_query = {}

            for (
                key,
                value
            ) in payload.items():

                normalized_key = str(
                    key or ""
                ).strip()

                if not normalized_key:
                    continue

                if isinstance(
                    value,
                    (
                        list,
                        dict
                    )
                ):
                    normalized_value = (
                        json.dumps(
                            value,
                            ensure_ascii=False
                        )
                    )

                elif value is None:
                    normalized_value = ""

                elif isinstance(
                    value,
                    bool
                ):
                    normalized_value = (
                        "true"
                        if value
                        else "false"
                    )

                else:
                    normalized_value = str(
                        value
                    )

                post_query[
                    normalized_key
                ] = [
                    normalized_value
                ]

            self._post_query = (
                post_query
            )

            self._request_method = (
                "POST"
            )

            # 共用既有完整處理流程。
            self.do_GET()

        except Exception as exc:
            self.send_json(
                500,
                {
                    "success":
                        False,

                    "error":
                        str(exc)
                }
            )

        finally:
            if hasattr(
                self,
                "_post_query"
            ):
                delattr(
                    self,
                    "_post_query"
                )

            if hasattr(
                self,
                "_request_method"
            ):
                delattr(
                    self,
                    "_request_method"
                )

    def do_GET(self):

        started_at = time.time()

        try:
            # -------------------------------------------------
            # 正常 GET：
            # → 從 URL Query String 取得資料。
            #
            # POST：
            # → do_POST 已解析 JSON Body，
            #   暫存於 _post_query。
            # -------------------------------------------------

            post_query = getattr(
                self,
                "_post_query",
                None
            )

            if isinstance(
                post_query,
                dict
            ):
                query = post_query

                request_method = (
                    "POST"
                )

            else:
                parsed_url = urlparse(
                    self.path
                )

                query = parse_qs(
                    parsed_url.query
                )

                request_method = (
                    "GET"
                )

            mode = str(
                query.get(
                    "mode",
                    [""]
                )[0]
            ).strip().lower()

            # =================================================
            # 生產 API 權限 Gate
            # =================================================
            #
            # 讀取型：
            # snapshot
            # state-list
            # pending-list
            # pending
            #
            # 維持 Viewer 可讀。
            #
            # 寫入型則必須有正式
            # OSAI Core Session。
            # =================================================

            protected_mode_roles = {
                "baseline":
                    {
                        "admin"
                    },

                "baseline-all":
                    {
                        "admin"
                    },

                "diff":
                    {
                        "admin",
                        "editor"
                    },

                "diff-all":
                    {
                        "admin",
                        "editor"
                    },

                "approve":
                    {
                        "admin",
                        "editor"
                    },

                "review-all":
                    {
                        "admin"
                    }
            }

            required_roles = (
                protected_mode_roles.get(
                    mode
                )
            )

            if required_roles is not None:

                # ---------------------------------------------
                # 所有 protected / 寫入型 mode
                # 一律禁止外部 GET。
                #
                # 即使有合法 Session，
                # 網址列也不能執行寫入操作。
                # ---------------------------------------------

                if (
                    request_method !=
                    "POST"
                ):
                    self.send_json(
                        405,
                        {
                            "success":
                                False,

                            "error":
                                "METHOD_NOT_ALLOWED",

                            "message":
                                (
                                    "此操作僅允許使用 POST"
                                )
                        }
                    )

                    return

                access_session = (
                    self.require_osai_roles(
                        required_roles
                    )
                )

                if access_session is None:
                    return

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

                expected_pending_hash = str(
                    query.get(
                        "expected_pending_hash",
                        [""]
                    )[0]
                ).strip()

                expected_pending_state = str(
                    query.get(
                        "expected_pending_state",
                        [""]
                    )[0]
                ).strip().lower()

                if expected_pending_state not in (
                    "",
                    "pending",
                    "none"
                ):
                    self.send_json(
                        400,
                        {
                            "success":
                                False,

                            "pcode":
                                pcode,

                            "error":
                                (
                                    "expected_pending_state "
                                    "必須為 pending 或 none"
                                )
                        }
                    )

                    return

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
                            pcode,
                            expected_pending_hash or None,
                            expected_pending_state or None
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
                                    (
                                        "pending_changed"
                                        if review_result.get(
                                            "status"
                                        ) == "pending_changed"
                                        else "review_date_failed"
                                    ),

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

            if mode == "review-all":

                monitored_pcodes = None

                monitored_pcodes_text = str(
                    query.get(
                        "pcodes",
                        [""]
                    )[0]
                    or ""
                ).strip()

                if monitored_pcodes_text:

                    try:
                        monitored_pcodes = (
                            json.loads(
                                monitored_pcodes_text
                            )
                        )

                    except json.JSONDecodeError:
                        self.send_json(
                            400,
                            {
                                "success":
                                    False,

                                "updatedCount":
                                    0,

                                "error":
                                    "同步鑑別法規範圍格式錯誤"
                            }
                        )

                        return

                review_date_raw = str(
                    query.get(
                        "review_date",
                        [""]
                    )[0]
                ).strip()

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

                            "updatedCount":
                                0,

                            "lastReviewedDate":
                                None,

                            "error":
                                (
                                    "review_date "
                                    "必須為 YYYY-MM-DD"
                                )
                        }
                    )

                    return

                try:
                    result = (
                        update_all_regulation_review_dates(
                            review_date,
                            monitored_pcodes
                        )
                    )
                    if result.get(
                        "success"
                    ):
                        status_code = 200

                    elif result.get(
                        "status"
                    ) in (
                        "pending_exists",
                        "baseline_missing",
                        "state_changed"
                    ):
                        status_code = 409

                    elif result.get(
                        "status"
                    ) == "invalid_scope":
                        status_code = 400

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

                            "updatedCount":
                                0,

                            "lastReviewedDate":
                                review_date,

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

                # -------------------------------------------------
                # 新架構：
                #
                # 正常前端會將「目前正在監控的 laws」
                # 直接傳給後端。
                #
                # 因此：
                # - 新增法規不需要改 law_list.json
                # - 刪除法規會自然退出同步範圍
                # - Cloud Workspace / JSON 的結構仍由前端資料決定
                #
                # 若沒有傳 laws：
                # 才退回既有 law_list.json，
                # 保留維護與舊版相容能力。
                # -------------------------------------------------

                requested_laws_text = str(
                    query.get(
                        "laws",
                        [""]
                    )[0]
                    or ""
                ).strip()

                if requested_laws_text:

                    try:
                        requested_laws = (
                            json.loads(
                                requested_laws_text
                            )
                        )

                    except json.JSONDecodeError:
                        self.send_json(
                            400,
                            {
                                "success":
                                    False,

                                "error":
                                    "目前法規監控清單格式錯誤"
                            }
                        )

                        return

                    if (
                        not isinstance(
                            requested_laws,
                            list
                        ) or
                        len(
                            requested_laws
                        ) == 0
                    ):
                        self.send_json(
                            400,
                            {
                                "success":
                                    False,

                                "error":
                                    "目前沒有可同步的法規監控項目"
                            }
                        )

                        return

                    if (
                        len(
                            requested_laws
                        ) > 100
                    ):
                        self.send_json(
                            400,
                            {
                                "success":
                                    False,

                                "error":
                                    "單次智能同步法規數量超過上限"
                            }
                        )

                        return

                    diff_law_list = []

                    seen_pcodes = set()

                    for (
                        law_index,
                        source_law
                    ) in enumerate(
                        requested_laws,
                        start=1
                    ):

                        if not isinstance(
                            source_law,
                            dict
                        ):
                            self.send_json(
                                400,
                                {
                                    "success":
                                        False,

                                    "error":
                                        (
                                            f"第 {law_index} 筆"
                                            "法規資料格式錯誤"
                                        )
                                }
                            )

                            return

                        pcode = str(
                            source_law.get(
                                "pcode",
                                ""
                            )
                        ).strip().upper()

                        law_name = str(
                            source_law.get(
                                "name",
                                ""
                            )
                        ).strip()

                        if not re.fullmatch(
                            r"[A-Z]\d{7}",
                            pcode
                        ):
                            self.send_json(
                                400,
                                {
                                    "success":
                                        False,

                                    "error":
                                        (
                                            f"第 {law_index} 筆法規 "
                                            f"PCode 格式錯誤："
                                            f"{pcode or '空白'}"
                                        )
                                }
                            )

                            return

                        if not law_name:
                            self.send_json(
                                400,
                                {
                                    "success":
                                        False,

                                    "error":
                                        (
                                            f"第 {law_index} 筆"
                                            "法規名稱不能空白"
                                        )
                                }
                            )

                            return

                        if pcode in seen_pcodes:
                            self.send_json(
                                400,
                                {
                                    "success":
                                        False,

                                    "error":
                                        (
                                            "法規監控清單存在重複 "
                                            f"PCode：{pcode}"
                                        )
                                }
                            )

                            return

                        seen_pcodes.add(
                            pcode
                        )

                        diff_law_list.append(
                            {
                                "pcode":
                                    pcode,

                                "name":
                                    law_name
                            }
                        )

                else:
                    # ---------------------------------------------
                    # 舊版／維護模式：
                    # 未傳入前端 laws 時，
                    # 仍可使用既有 law_list.json。
                    # ---------------------------------------------

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

                initialized_count = sum(
                    1
                    for item
                    in diff_results
                    if (
                        item.get(
                            "Success"
                        ) and
                        item.get(
                            "Status"
                        ) ==
                        "baseline_initialized"
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

                        "initializedCount":
                            initialized_count,

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
