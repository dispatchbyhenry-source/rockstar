import ast
import atexit
import base64
import hmac
import io
import json
import os
import secrets
import shutil
import smtplib
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timedelta
from email.message import EmailMessage
from functools import wraps

import certifi
import psycopg
import ssl
from dotenv import load_dotenv
from flask import Flask, Response, abort, flash, g, has_request_context, jsonify, redirect, render_template, request, session, url_for
from PIL import Image, ImageOps, UnidentifiedImageError
from psycopg import IntegrityError
from psycopg.errors import InFailedSqlTransaction
from psycopg.rows import dict_row
from psycopg_pool import ConnectionPool, PoolTimeout
from itsdangerous import BadSignature, SignatureExpired, URLSafeTimedSerializer
from i18n import (
    LANGUAGES,
    LANGUAGE_TO_ZONE,
    ZONE_DEFAULT_LANGUAGE,
    currency_for_country,
    language_for_country,
    language_from_accept_header,
    translate,
)
from markupsafe import Markup
from werkzeug.exceptions import RequestEntityTooLarge
from werkzeug.security import check_password_hash, generate_password_hash
from werkzeug.utils import secure_filename

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
load_dotenv(os.path.join(BASE_DIR, ".env"))

DATABASE_URL = os.environ.get(
    "DATABASE_URL",
    "postgresql://arshop:arshop@127.0.0.1:5432/ar_shopping_world",
)
UPLOAD_ROOT = os.path.join(BASE_DIR, "static", "images")
ALLOWED_EXTENSIONS = {"jpg", "jpeg", "png", "webp"}
PRODUCT_IMAGE_SIZE = 1200
PRODUCT_IMAGE_SLOTS = 5
MAX_PRODUCT_BYTES = 2 * 1024 * 1024
DEFAULT_CATEGORIES = ["Shoes", "Pants", "Shirts", "Jackets", "Wallets", "Purses", "Belts"]

ADMIN_PASSWORD_MIN = 10
ADMIN_SESSION_MINUTES = int(os.environ.get("ADMIN_SESSION_MINUTES") or 30)
LOGIN_MAX_ATTEMPTS = int(os.environ.get("LOGIN_MAX_ATTEMPTS") or 5)
LOGIN_WINDOW_SECONDS = int(os.environ.get("LOGIN_WINDOW_SECONDS") or 900)
FORCE_HTTPS = (os.environ.get("FORCE_HTTPS") or "").strip().lower() in {"1", "true", "yes"}
SESSION_COOKIE_SECURE = (os.environ.get("SESSION_COOKIE_SECURE") or "").strip().lower() in {"1", "true", "yes"}
TRUST_PROXY = (os.environ.get("TRUST_PROXY") or "").strip().lower() in {"1", "true", "yes"}
DB_POOL_MIN = max(1, int(os.environ.get("DB_POOL_MIN") or 1))
DB_POOL_MAX = max(DB_POOL_MIN, int(os.environ.get("DB_POOL_MAX") or 4))
SHOP_NAV_TTL = max(5, int(os.environ.get("SHOP_NAV_TTL") or 45))

app = Flask(__name__)
app.config.update(
    SECRET_KEY=os.environ.get("SECRET_KEY") or secrets.token_hex(32),
    MAX_CONTENT_LENGTH=12 * 1024 * 1024,
    # Product forms with multiple gender panels post many size/colour fields.
    # Werkzeug 3 defaults (1000 parts / 500KB) reject those saves.
    MAX_FORM_PARTS=int(os.environ.get("MAX_FORM_PARTS") or 50000),
    MAX_FORM_MEMORY_SIZE=int(os.environ.get("MAX_FORM_MEMORY_SIZE") or 10 * 1024 * 1024),
    DB_INITIALIZED=False,
    TEMPLATES_AUTO_RELOAD=True,
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=SESSION_COOKIE_SECURE,
    PERMANENT_SESSION_LIFETIME=timedelta(minutes=ADMIN_SESSION_MINUTES),
)

if TRUST_PROXY:
    from werkzeug.middleware.proxy_fix import ProxyFix

    app.wsgi_app = ProxyFix(app.wsgi_app, x_for=1, x_proto=1, x_host=1)

ADMIN_USERNAME = os.environ.get("ADMIN_USERNAME", "admin")
ADMIN_PASSWORD_HASH = os.environ.get("ADMIN_PASSWORD_HASH", "")
ADMIN_EMAIL = os.environ.get("ADMIN_EMAIL", "").strip()
LOGIN_ATTEMPTS = {}

CURRENCIES = {"EUR": (1 / 302, "EUR"), "USD": (1 / 278, "USD"), "PKR": (1, "PKR")}
CLOTHES_SIZES = ["XXS", "XS", "S", "M", "L", "XL", "XXL", "3XL", "4XL", "5XL", "6XL", "7XL"]
SHOE_SIZES = [str(number) for number in range(24, 48)]
ACCESSORY_SIZES = [f"{number}cm" for number in range(10, 51)]
SIZE_MAP = {
    "Clothes": CLOTHES_SIZES,
    "Shoes": SHOE_SIZES,
    "Accessories": ACCESSORY_SIZES,
    "Sports": CLOTHES_SIZES,
    "Others": [],
}
ALL_CATALOG_SIZES = CLOTHES_SIZES + SHOE_SIZES + ACCESSORY_SIZES
PRESET_SIZES = CLOTHES_SIZES
PRESET_COLORS = [
    "Black",
    "White",
    "Grey",
    "Navy",
    "Blue",
    "Red",
    "Green",
    "Beige",
    "Brown",
    "Pink",
    "Yellow",
    "Orange",
    "Purple",
    "Cream",
    "Khaki",
]
PRODUCT_TYPES = ["Clothes", "Shoes", "Accessories", "Sports", "Others"]
SIZE_GROUPS = ["Male", "Female", "Unisex", "Child"]
MAIN_CATEGORIES = ["Men", "Women", "Kids", "Unisex"]
AUDIENCES = (
    ("men", "Men", "Male"),
    ("women", "Women", "Female"),
    ("kids", "Kids", "Child"),
    ("unisex", "Unisex", "Unisex"),
)
PRODUCT_GENDERS = (
    ("Male", "Men"),
    ("Female", "Women"),
    ("Child", "Kids"),
    ("Unisex", "Unisex"),
    ("Others", "Others"),
)
GENDER_VALUES = [value for value, _label in PRODUCT_GENDERS]
GENDER_LABELS = dict(PRODUCT_GENDERS)
# Product gender → shop main-category filter (Men/Women/Kids/Unisex).
GENDER_TO_MAIN = {
    "Male": "Men",
    "Female": "Women",
    "Child": "Kids",
    "Unisex": "Unisex",
}
SUB_CATEGORIES = {
    "Clothes": ["Shirts", "Pants", "Jackets", "Hoodies", "Dresses", "Coats", "Tops"],
    "Shoes": ["Sneakers", "Boots", "Formal", "Sandals", "Sports"],
    "Accessories": ["Wallets", "Purses", "Belts", "Bags", "Hats", "Scarves"],
    "Sports": ["Sportswear", "Jerseys", "Kits", "Equipment"],
    "Others": ["Others"],
}
CONDITIONS = [
    ("new_with_tag", "New with tag"),
    ("new_without_tag", "New without tag"),
    ("used", "Used"),
]
CONDITION_LABELS = dict(CONDITIONS)
REGION_OPTIONS = [
    ("europe_america", "Show only in Europe and America"),
    ("pakistan", "Show in Pakistan"),
    ("germany", "Show only in Germany"),
    ("europe_uk", "Show in Europe and UK"),
    ("germany_pakistan", "Show in Germany and Pakistan"),
    ("all", "Show in all regions"),
]
REGION_VISIBLE_ZONES = {
    "europe_america": {"Germany", "Europe", "Canada/USA"},
    "pakistan": {"Pakistan"},
    "germany": {"Germany"},
    "europe_uk": {"Europe"},
    "germany_pakistan": {"Germany", "Pakistan"},
}
EUR_TO_STORE = 302
SHOP_PRODUCT_COLUMNS = ", ".join(
    [
        "id",
        "name",
        "category",
        "price",
        "old_price",
        "badge",
        "rating",
        "reviews_count",
        "likes",
        "sku",
        "image",
        "sizes",
        "colors",
        "stock",
        "active",
        "colors_json",
        "sizes_json",
        "amazon_url",
        "etsy_url",
        "ebay_url",
        "discount_percent",
        "weight",
        "pakistan_price",
        "pakistan_discount_percent",
        "condition",
        "main_category",
        "main_categories",
        "sub_category",
        "sub_categories",
        "sub_category_2",
        "sub_category_3",
        "sub_category_4",
        "product_type",
        "size_group",
        "genders",
        "gender_offers",
        "packing_weight",
        "region_visibility",
        "product_tags",
        "product_hashtags",
        "featured",
        "deal_of_week",
        "new_arrival",
        "is_draft",
        "listed_by",
        "brand",
        "volume_discounts",
        "pakistan_volume_discounts",
        "fulfillment",
    ]
)
NAV_PRODUCT_COLUMNS = ", ".join(
    [
        "id",
        "category",
        "main_category",
        "main_categories",
        "sub_category",
        "sub_categories",
        "sub_category_2",
        "sub_category_3",
        "sub_category_4",
        "region_visibility",
    ]
)
_db_pool = None
_db_pool_lock = threading.Lock()
_shop_nav_cache = {}
_shop_nav_lock = threading.Lock()
WEIGHT_LIMIT_KG = 5
VIRTUAL_COLOR = "Digital"
VIRTUAL_SIZE = "Digital"
PRODUCT_TAX_PERCENT = 19
DEFAULT_SHIPPING_ZONES = [
    {"name": "Germany", "key": "germany", "unit": "EUR", "under": 10, "over": 10, "express_under": 20, "express_over": 20},
    {"name": "Europe", "key": "europe", "unit": "EUR", "under": 20, "over": 30, "express_under": 35, "express_over": 50},
    {"name": "Canada/USA", "key": "canada_usa", "unit": "EUR", "under": 30, "over": 60, "express_under": 55, "express_over": 90},
    {"name": "Pakistan", "key": "pakistan", "unit": "PKR", "under": 600, "over": 1000, "express_under": 1200, "express_over": 1800},
]
ZONE_NAMES = [zone["name"] for zone in DEFAULT_SHIPPING_ZONES]
ZONE_CURRENCY = {"Germany": "EUR", "Europe": "EUR", "Canada/USA": "USD", "Pakistan": "PKR"}
COUNTRY_CODE_TO_ZONE = {
    "PK": "Pakistan",
    "DE": "Germany",
    "US": "Canada/USA",
    "CA": "Canada/USA",
    "AT": "Europe",
    "BE": "Europe",
    "BG": "Europe",
    "CH": "Europe",
    "CY": "Europe",
    "CZ": "Europe",
    "DK": "Europe",
    "EE": "Europe",
    "ES": "Europe",
    "FI": "Europe",
    "FR": "Europe",
    "GB": "Europe",
    "GR": "Europe",
    "HR": "Europe",
    "HU": "Europe",
    "IE": "Europe",
    "IT": "Europe",
    "LT": "Europe",
    "LU": "Europe",
    "LV": "Europe",
    "MT": "Europe",
    "NL": "Europe",
    "NO": "Europe",
    "PL": "Europe",
    "PT": "Europe",
    "RO": "Europe",
    "SE": "Europe",
    "SI": "Europe",
    "SK": "Europe",
    "UK": "Europe",
    "UA": "Europe",
    "TR": "Europe",
    "IS": "Europe",
    "LI": "Germany",
    "MD": "Europe",
    "AD": "Europe",
    "MC": "Europe",
    "SM": "Europe",
    "VA": "Europe",
}
CURRENCY_TO_ZONE = {"PKR": "Pakistan", "EUR": "Europe", "USD": "Canada/USA"}
ADDRESS_ZONE_HINTS = (
    ("pakistan", "Pakistan"),
    ("islamabad", "Pakistan"),
    ("karachi", "Pakistan"),
    ("lahore", "Pakistan"),
    ("deutschland", "Germany"),
    ("germany", "Germany"),
    ("berlin", "Germany"),
    ("munich", "Germany"),
    ("united states", "Canada/USA"),
    ("u.s.a", "Canada/USA"),
    ("u.s.", "Canada/USA"),
    ("usa", "Canada/USA"),
    ("canada", "Canada/USA"),
    ("united kingdom", "Europe"),
    ("england", "Europe"),
    ("scotland", "Europe"),
    ("france", "Europe"),
    ("italy", "Europe"),
    ("spain", "Europe"),
    ("netherlands", "Europe"),
    ("belgium", "Europe"),
    ("austria", "Europe"),
    ("sweden", "Europe"),
    ("norway", "Europe"),
    ("poland", "Europe"),
    ("portugal", "Europe"),
    ("ireland", "Europe"),
    ("switzerland", "Europe"),
)
DEFAULT_FAQS = [
    ("How do I choose the right size?", "Each product shows available colours and sizes with remaining stock. Choose a colour first, then a size."),
    ("Which currencies can I use?", "Prices can be viewed in EUR, USD, or PKR. Choose your preferred currency in the header."),
    ("Can I check a market price first?", "Yes. Product pages include Check price on other platforms when Amazon, Etsy or eBay links are available."),
    ("How can I contact support?", "Use the Contact page and our team will receive your message through the secure backend."),
]

PRODUCTS = [
    ("Slim-Fit Stretch Denim Jeans", "Pants", 3499, 4200, "-17% OFF", 4.8, 32, "AR-PNT-01", "https://images.unsplash.com/photo-1542272604-780c36856842?w=800", "30,32,34,36", "Dark Indigo,Washed Black", "Premium cotton denim with comfortable stretch and reinforced stitching.", 20),
    ("Tailored Cotton Chino Trousers", "Pants", 2899, 3500, "HOT", 4.7, 19, "AR-PNT-02", "https://images.unsplash.com/photo-1624378439575-d8705ad7ae80?w=800", "30,32,34", "Olive Green,Khaki Tan", "Modern tapered chinos made from combed cotton twill.", 20),
    ("Royal Oxford Formal Cotton Shirt", "Shirts", 2299, 2800, "NEW", 4.9, 54, "AR-SHR-01", "https://images.unsplash.com/photo-1596755094514-f87e34085b2c?w=800", "Small,Medium,Large,Extra Large", "Pure White,Sky Blue", "Luxury long-staple cotton oxford shirt with an executive collar.", 20),
    ("Modern Stretch Pique Polo Shirt", "Shirts", 1899, 2200, "POPULAR", 4.5, 21, "AR-SHR-02", "https://images.unsplash.com/photo-1602810318383-e386cc2a3ccf?w=800", "Medium,Large,Extra Large", "Navy Blue,Maroon", "Breathable knit polo with active stretch and moisture control.", 20),
    ("Genuine Cowhide Biker Leather Jacket", "Jackets", 8999, 11500, "-22% OFF", 5.0, 88, "AR-JKT-01", "https://images.unsplash.com/photo-1551028719-00167b16eac5?w=800", "Medium,Large,Extra Large,Double Extra Large", "Obsidian Black,Antique Brown", "Full-grain cowhide jacket with YKK zips and quilted lining.", 20),
    ("Tactical Windproof Bomber Jacket", "Jackets", 5499, 6500, "FEATURED", 4.6, 14, "AR-JKT-02", "https://images.unsplash.com/photo-1548883354-7622d03aca27?w=800", "Small,Medium,Large", "Army Green,Matte Black", "Water-repellent shell with thermal insulation and storm cuffs.", 20),
    ("Minimalist RFID Leather Bifold Wallet", "Wallets", 1499, 1999, "BESTSELLER", 4.8, 43, "AR-WLT-01", "https://images.unsplash.com/photo-1627123424574-724758594e93?w=800", "Standard Pocket", "Tan Brown,Classic Black", "Handcrafted leather wallet with RFID protection.", 20),
    ("Luxury Structured Designer Purse", "Purses", 4999, 6200, "-19% OFF", 4.9, 37, "AR-PRS-01", "https://images.unsplash.com/photo-1584917865442-de89df76afd3?w=800", "Medium Tote", "Burgundy Red,Nude Beige", "Genuine leather handbag with gold-tone hardware.", 20),
    ("Reversible Full-Grain Leather Belt", "Belts", 1299, 1650, "2-IN-1", 4.7, 29, "AR-BLT-01", "https://images.unsplash.com/photo-1553062407-98eeb64c6a62?w=800", "32-34 Waist,36-38 Waist", "Black/Brown Reversible", "Dual-sided leather belt with rotatable alloy buckle.", 20),
    ("Velocity Knit Running Shoes", "Shoes", 5999, 7200, "NEW", 4.9, 61, "AR-SHO-01", "https://images.unsplash.com/photo-1542291026-7eec264c27ff?w=800", "40,41,42,43,44", "Crimson Red,Midnight Black", "Responsive knit running shoes with cushioned grip sole.", 20),
    ("Classic Leather Court Sneakers", "Shoes", 6799, 7900, "TOP RATED", 4.8, 47, "AR-SHO-02", "https://images.unsplash.com/photo-1525966222134-fcfa99b8ae77?w=800", "39,40,41,42,43", "White/Red,Black/Red", "Premium everyday court sneakers with soft leather upper.", 20),
]

GALLERY_IMAGES = {
    "Shoes": [
        "https://images.unsplash.com/photo-1542291026-7eec264c27ff?w=1000",
        "https://images.unsplash.com/photo-1525966222134-fcfa99b8ae77?w=1000",
        "https://images.unsplash.com/photo-1460353581641-37baddab0fa2?w=1000",
    ],
    "Pants": [
        "https://images.unsplash.com/photo-1542272604-780c36856842?w=1000",
        "https://images.unsplash.com/photo-1473966968600-fa801b869a1a?w=1000",
    ],
    "Shirts": [
        "https://images.unsplash.com/photo-1596755094514-f87e34085b2c?w=1000",
        "https://images.unsplash.com/photo-1603252109303-2751441dd157?w=1000",
    ],
    "Jackets": [
        "https://images.unsplash.com/photo-1551028719-00167b16eac5?w=1000",
        "https://images.unsplash.com/photo-1548883354-7622d03aca27?w=1000",
    ],
}


class CursorResult:
    def __init__(self, cursor, lastrowid=None):
        self._cursor = cursor
        self.lastrowid = lastrowid

    def fetchone(self):
        return self._cursor.fetchone()

    def fetchall(self):
        return self._cursor.fetchall()

    def __iter__(self):
        return iter(self._cursor)


class Database:
    """Thin PostgreSQL wrapper that keeps SQLite-style ? placeholders."""

    def __init__(self, conn):
        self._conn = conn

    def execute(self, sql, params=None):
        cursor = self._conn.execute(sql.replace("?", "%s"), params or ())
        lastrowid = None
        stripped = sql.lstrip().upper()
        if stripped.startswith("INSERT") and "RETURNING" not in stripped and "ON CONFLICT" not in stripped:
            self._conn.execute("SAVEPOINT lastval_lookup")
            try:
                lastrowid = self._conn.execute("SELECT lastval() AS id").fetchone()["id"]
                self._conn.execute("RELEASE SAVEPOINT lastval_lookup")
            except Exception:
                self._conn.execute("ROLLBACK TO SAVEPOINT lastval_lookup")
                lastrowid = None
        return CursorResult(cursor, lastrowid)

    def executemany(self, sql, seq_of_params):
        with self._conn.cursor() as cursor:
            cursor.executemany(sql.replace("?", "%s"), seq_of_params)
        return self

    def commit(self):
        self._conn.commit()

    def rollback(self):
        self._conn.rollback()

    def close(self):
        self._conn.close()


def get_pool():
    global _db_pool
    if _db_pool is None:
        with _db_pool_lock:
            if _db_pool is None:
                _db_pool = ConnectionPool(
                    conninfo=DATABASE_URL,
                    min_size=DB_POOL_MIN,
                    max_size=DB_POOL_MAX,
                    timeout=30,
                    kwargs={"row_factory": dict_row},
                    open=True,
                    name="arshop",
                )
    return _db_pool


def close_pool():
    global _db_pool
    with _db_pool_lock:
        pool = _db_pool
        _db_pool = None
    if pool is not None:
        try:
            pool.close()
        except Exception:
            pass


atexit.register(close_pool)


def invalidate_shop_nav_cache():
    with _shop_nav_lock:
        _shop_nav_cache.clear()


def rollback_db():
    try:
        get_db().rollback()
    except Exception:
        pass


def friendly_product_error(error):
    text = str(error)
    if "products_sku_key" in text:
        sku = (request.form.get("sku") or "").strip()
        if sku:
            return f"SKU {sku} is already used by another product. Choose a unique SKU."
        return "That SKU is already used by another product. Choose a unique SKU."
    return text


def get_db():
    if "db" not in g:
        try:
            conn = get_pool().getconn()
        except (psycopg.OperationalError, PoolTimeout) as error:
            raise RuntimeError(
                "Could not connect to PostgreSQL. Start the database "
                "(docker compose up -d) and check DATABASE_URL in .env."
            ) from error
        g.db_conn = conn
        g.db = Database(conn)
    return g.db


@app.teardown_appcontext
def close_db(_error=None):
    g.pop("db", None)
    conn = g.pop("db_conn", None)
    if conn is None:
        return
    try:
        if not conn.closed:
            conn.rollback()
        get_pool().putconn(conn)
    except Exception:
        try:
            if not conn.closed:
                conn.close()
        except Exception:
            pass


def table_exists(table):
    row = get_db().execute(
        """
        SELECT 1 AS ok
        FROM information_schema.tables
        WHERE table_schema = 'public' AND table_name = ?
        """,
        (table,),
    ).fetchone()
    return bool(row)


def ensure_columns(table, columns):
    if not table_exists(table):
        return
    db = get_db()
    existing = {
        row["column_name"]
        for row in db.execute(
            """
            SELECT column_name
            FROM information_schema.columns
            WHERE table_schema = 'public' AND table_name = ?
            """,
            (table,),
        ).fetchall()
    }
    for column, definition in columns.items():
        if column not in existing:
            db.execute(f"ALTER TABLE {table} ADD COLUMN {column} {definition}")


def table_columns(table):
    return {
        row["column_name"]
        for row in get_db().execute(
            """
            SELECT column_name
            FROM information_schema.columns
            WHERE table_schema = 'public' AND table_name = ?
            """,
            (table,),
        ).fetchall()
    }


def default_sub_category_names():
    names = []
    seen = set()
    for group in SUB_CATEGORIES.values():
        for name in group:
            if name not in seen:
                seen.add(name)
                names.append(name)
    return names


def main_category_names(db=None):
    database = db or get_db()
    rows = database.execute("SELECT name FROM main_categories ORDER BY id").fetchall()
    return [row["name"] for row in rows] or list(MAIN_CATEGORIES)


def migrate_sub_categories_to_main(db):
    cols = table_columns("sub_categories")
    if not cols:
        return
    if "main_category" not in cols:
        db.execute("ALTER TABLE sub_categories ADD COLUMN main_category TEXT")
        cols.add("main_category")
    mains = main_category_names(db)
    main_set = set(mains)
    rows = db.execute("SELECT * FROM sub_categories ORDER BY id").fetchall()
    names = []
    seen = set()
    for row in rows:
        name = (row.get("name") or "").strip()
        if name and name not in seen:
            seen.add(name)
            names.append(name)
    if not names:
        names = default_sub_category_names()
    needs_rebuild = "product_type" in cols or any((row.get("main_category") or "") not in main_set for row in rows)
    if needs_rebuild:
        db.execute("ALTER TABLE sub_categories DROP CONSTRAINT IF EXISTS sub_categories_name_product_type_key")
        db.execute("ALTER TABLE sub_categories DROP CONSTRAINT IF EXISTS sub_categories_name_main_category_key")
        db.execute("DROP INDEX IF EXISTS sub_categories_name_product_type_key")
        db.execute("DROP INDEX IF EXISTS sub_categories_name_main_category_key")
        if "product_type" in cols:
            db.execute("ALTER TABLE sub_categories DROP COLUMN IF EXISTS product_type")
            cols.discard("product_type")
        db.execute("DELETE FROM sub_categories")
        for main in mains:
            for name in names:
                db.execute("INSERT INTO sub_categories (name, main_category) VALUES (?,?)", (name, main))
        db.execute("UPDATE sub_categories SET main_category='Unisex' WHERE main_category IS NULL OR main_category=''")
        db.execute("ALTER TABLE sub_categories ALTER COLUMN main_category SET NOT NULL")
    db.execute(
        "CREATE UNIQUE INDEX IF NOT EXISTS sub_categories_name_main_category_key ON sub_categories (name, main_category)"
    )


def seed_sub_categories(db):
    mains = main_category_names(db)
    names = default_sub_category_names()
    if not db.execute("SELECT 1 AS ok FROM sub_categories LIMIT 1").fetchone():
        db.executemany(
            "INSERT INTO sub_categories (name, main_category) VALUES (?,?)",
            [(name, main) for main in mains for name in names],
        )
    for main in mains:
        db.execute(
            "INSERT INTO sub_categories (name, main_category) VALUES (?,?) ON CONFLICT (name, main_category) DO NOTHING",
            ("Others", main),
        )


def colors_from_legacy(colors_text, stock):
    names = [part.strip() for part in (colors_text or "").split(",") if part.strip()]
    if not names:
        return [{"name": "Default", "quantity": int(stock or 0)}]
    per = max(int(stock or 0) // len(names), 0)
    remainder = max(int(stock or 0) - per * len(names), 0)
    colors = [{"name": name, "quantity": per} for name in names[:10]]
    if colors:
        colors[0]["quantity"] += remainder
    return colors


def sizes_from_legacy(sizes_text):
    return [part.strip() for part in (sizes_text or "").split(",") if part.strip()]


def catalog_sizes_for(product_type):
    return SIZE_MAP.get(product_type, CLOTHES_SIZES)


def clean_size_name(raw):
    extra = (raw or "").strip()[:20]
    if not extra:
        return ""
    allowed = set("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789./+-")
    if any(char not in allowed for char in extra):
        return ""
    return extra


def parse_removed_sizes(prefix=""):
    removed = []
    for part in (request.form.get(f"{prefix}removed_sizes") or "").replace("\n", ",").split(","):
        extra = clean_size_name(part)
        if extra and extra not in removed:
            removed.append(extra)
    return set(removed)


def parse_size_form(prefix=""):
    product_type = request.form.get("product_type", "Clothes")
    allowed = catalog_sizes_for(product_type)
    removed = parse_removed_sizes(prefix)
    sizes = [size for size in allowed if request.form.get(f"{prefix}size_{size}") and size not in removed]
    extras = list(request.form.getlist(f"{prefix}extra_size"))
    extras.extend((request.form.get(f"{prefix}custom_sizes") or "").replace("\n", ",").split(","))
    extras.extend((request.form.get(f"{prefix}custom_shoe_sizes") or "").replace("\n", ",").split(","))
    extras.extend((request.form.get(f"{prefix}bulk_sizes") or "").replace("\n", ",").split(","))
    marker = f"{prefix}size_"
    for key, value in request.form.items():
        if key.startswith(marker) and key != f"{prefix}size_group" and value:
            extras.append(key[len(marker):])
    for extra in extras:
        extra = clean_size_name(extra)
        if extra and extra not in sizes and extra not in removed:
            sizes.append(extra)
    return sizes


def parse_color_form(prefix=""):
    selected_sizes = parse_size_form(prefix)
    colors = []
    for index in range(1, 11):
        name = request.form.get(f"{prefix}color_name_{index}", "").strip()[:40]
        if not name:
            continue
        size_stock = {}
        for size in selected_sizes:
            try:
                size_stock[size] = max(int(request.form.get(f"{prefix}color_stock_{index}_{size}", 0) or 0), 0)
            except ValueError:
                size_stock[size] = 0
        colors.append({"name": name, "quantity": sum(size_stock.values()), "sizes": size_stock})
    return colors


def parse_keyword_list(raw, limit=10, hashtag=False):
    items = []
    seen = set()
    for part in (raw or "").split(","):
        word = part.strip()[:40]
        if not word:
            continue
        if hashtag:
            word = word.lstrip("#").replace(" ", "")
            if not word:
                continue
            word = f"#{word}"
        key = word.lower()
        if key in seen:
            continue
        seen.add(key)
        items.append(word)
        if len(items) >= limit:
            break
    return items


def keywords_from_stored(raw):
    if isinstance(raw, (list, tuple)):
        return [str(part).strip() for part in raw if str(part).strip()]
    return [part.strip() for part in (raw or "").split(",") if part.strip()]


def parse_marketplace_urls():
    return {
        "amazon_url": request.form.get("amazon_url", "").strip()[:500],
        "etsy_url": request.form.get("etsy_url", "").strip()[:500],
        "ebay_url": request.form.get("ebay_url", "").strip()[:500],
    }


def product_image_name(index):
    return "main.jpg" if index == 1 else f"{index}.jpg"


def form_payload_bytes():
    if not has_request_context():
        return 0
    return sum(len(value.encode("utf-8")) for values in request.form.listvalues() for value in values)


def square_product_image(image):
    try:
        image = ImageOps.exif_transpose(image) or image
    except Exception:
        pass
    if image.mode in {"RGBA", "LA"} or (image.mode == "P" and "transparency" in image.info):
        rgba = image.convert("RGBA")
        background = Image.new("RGB", rgba.size, (255, 255, 255))
        background.paste(rgba, mask=rgba.split()[-1])
        image = background
    else:
        image = image.convert("RGB")
    try:
        image = ImageOps.autocontrast(image, cutoff=1)
    except ValueError:
        pass
    width, height = image.size
    side = max(width, height)
    canvas = Image.new("RGB", (side, side), (255, 255, 255))
    canvas.paste(image, ((side - width) // 2, (side - height) // 2))
    return canvas.resize((PRODUCT_IMAGE_SIZE, PRODUCT_IMAGE_SIZE), Image.Resampling.LANCZOS)


def jpeg_bytes(image, quality):
    buffer = io.BytesIO()
    image.save(buffer, format="JPEG", quality=quality, optimize=True)
    return buffer.getvalue()


def load_upload_image(uploaded):
    if not uploaded or not uploaded.filename:
        return None
    extension = secure_filename(uploaded.filename).rsplit(".", 1)[-1].lower() if "." in uploaded.filename else ""
    if extension not in ALLOWED_EXTENSIONS:
        raise ValueError("Images must be JPG, JPEG, PNG, or WEBP files.")
    uploaded.stream.seek(0)
    try:
        image = Image.open(uploaded.stream)
        image.load()
    except (UnidentifiedImageError, OSError) as error:
        raise ValueError("One of the files is not a valid image.") from error
    return square_product_image(image)


def encode_images_within_limit(prepared, kept_bytes, text_bytes):
    for quality in (85, 75, 65, 55, 45):
        encoded = [(index, jpeg_bytes(image, quality)) for index, image in prepared]
        total = text_bytes + kept_bytes + sum(len(data) for _, data in encoded)
        if total <= MAX_PRODUCT_BYTES:
            return encoded
    raise ValueError("This product cannot exceed 2 MB including images. Use fewer or simpler photos.")


def stored_product_images(product_id):
    if not product_id:
        return []
    return get_db().execute(
        "SELECT slot, byte_size FROM product_images WHERE product_id=? ORDER BY slot",
        (product_id,),
    ).fetchall() or []


def product_image_url(product_id, slot, byte_size=0):
    return f"/product-image/{int(product_id)}/{int(slot)}?v={int(byte_size or 0)}"


def upsert_product_image(product_id, slot, data, content_type="image/jpeg"):
    get_db().execute(
        """
        INSERT INTO product_images (product_id, slot, content_type, bytes, byte_size)
        VALUES (?,?,?,?,?)
        ON CONFLICT (product_id, slot) DO UPDATE SET
            content_type=EXCLUDED.content_type,
            bytes=EXCLUDED.bytes,
            byte_size=EXCLUDED.byte_size
        """,
        (product_id, slot, content_type, data, len(data)),
    )


def migrate_disk_product_images(product_id, sku):
    if not product_id or not sku or stored_product_images(product_id):
        return
    migrated = False
    for slot in range(1, PRODUCT_IMAGE_SLOTS + 1):
        path = os.path.join(UPLOAD_ROOT, sku, product_image_name(slot))
        if not os.path.isfile(path):
            continue
        with open(path, "rb") as handle:
            data = handle.read()
        if not data:
            continue
        upsert_product_image(product_id, slot, data)
        migrated = True
    if migrated:
        get_db().commit()


def apply_product_gallery(item, gallery_map=None):
    sku = item.get("sku") or ""
    product_id = item.get("id")
    if gallery_map is not None:
        db_images = gallery_map.get(product_id) or gallery_map.get(int(product_id or 0)) or []
    else:
        migrate_disk_product_images(product_id, sku)
        db_images = stored_product_images(product_id)
    if db_images:
        item["gallery"] = [product_image_url(product_id, row["slot"], row["byte_size"]) for row in db_images]
    else:
        local_gallery = []
        image_folder = os.path.join(UPLOAD_ROOT, sku) if sku else ""
        if image_folder:
            for filename in [product_image_name(index) for index in range(1, PRODUCT_IMAGE_SLOTS + 1)]:
                if os.path.exists(os.path.join(image_folder, filename)):
                    local_gallery.append(f"/static/images/{sku}/{filename}")
        fallback_image = item.get("image") or ""
        item["gallery"] = [
            url
            for url in (
                local_gallery
                or ([fallback_image] + [image for image in GALLERY_IMAGES.get(item["category"], []) if image != fallback_image][:2])
            )
            if url
        ]
    item["image"] = item["gallery"][0] if item["gallery"] else (item.get("image") or "")
    return item


def product_image_disk_path(sku, slot):
    if not sku:
        return ""
    return os.path.join(UPLOAD_ROOT, sku, product_image_name(slot))


def delete_product_image_slot(product_id, slot, sku=None):
    get_db().execute("DELETE FROM product_images WHERE product_id=? AND slot=?", (product_id, slot))
    path = product_image_disk_path(sku, slot)
    if path and os.path.isfile(path):
        try:
            os.remove(path)
        except OSError:
            pass


def refresh_product_cover_image(product_id):
    db = get_db()
    first = db.execute(
        "SELECT slot, byte_size FROM product_images WHERE product_id=? ORDER BY slot LIMIT 1",
        (product_id,),
    ).fetchone()
    db.execute(
        "UPDATE products SET image=? WHERE id=?",
        (product_image_url(product_id, first["slot"], first["byte_size"]) if first else "", product_id),
    )


def save_product_images(product_id, sku=None, slots=PRODUCT_IMAGE_SLOTS):
    if not product_id:
        raise ValueError("Product must be saved before images can be stored.")
    slots = min(slots or PRODUCT_IMAGE_SLOTS, PRODUCT_IMAGE_SLOTS)
    db = get_db()
    db.execute("DELETE FROM product_images WHERE product_id=? AND slot>?", (product_id, PRODUCT_IMAGE_SLOTS))
    existing = {row["slot"]: row["byte_size"] for row in stored_product_images(product_id)}
    if sku and not existing:
        for index in range(1, slots + 1):
            path = product_image_disk_path(sku, index)
            if path and os.path.isfile(path):
                existing[index] = os.path.getsize(path)
    deleted = {
        index
        for index in range(1, slots + 1)
        if request.form.get(f"delete_image_{index}")
    }
    prepared = []
    assigned = set()
    for index in range(1, slots + 1):
        field = "main_image" if index == 1 else f"image_{index}"
        image = load_upload_image(request.files.get(field))
        if image:
            prepared.append((index, image))
            assigned.add(index)
            deleted.discard(index)
    batch_images = []
    for uploaded in request.files.getlist("product_images"):
        image = load_upload_image(uploaded)
        if image:
            batch_images.append(image)
    empty_slots = [
        index
        for index in range(1, slots + 1)
        if index not in assigned and (index in deleted or index not in existing)
    ]
    overflow_slots = [
        index for index in range(1, slots + 1) if index not in assigned and index not in empty_slots
    ]
    for image in batch_images:
        if not empty_slots and not overflow_slots:
            break
        index = empty_slots.pop(0) if empty_slots else overflow_slots.pop(0)
        prepared.append((index, image))
        assigned.add(index)
        deleted.discard(index)
    for index in deleted:
        delete_product_image_slot(product_id, index, sku)
        existing.pop(index, None)
    text_bytes = form_payload_bytes()
    kept_bytes = sum(size for slot, size in existing.items() if slot not in assigned)
    if not prepared:
        if text_bytes + kept_bytes > MAX_PRODUCT_BYTES:
            raise ValueError("This product cannot exceed 2 MB including images.")
        refresh_product_cover_image(product_id)
        return
    encoded = encode_images_within_limit(prepared, kept_bytes, text_bytes)
    for index, data in encoded:
        upsert_product_image(product_id, index, data)
    refresh_product_cover_image(product_id)


def save_listing_images(listing_id):
    folder = os.path.join(UPLOAD_ROOT, f"listing-{listing_id}")
    os.makedirs(folder, exist_ok=True)
    prepared = []
    for index in range(1, 4):
        image = load_upload_image(request.files.get(f"image_{index}"))
        if image:
            prepared.append((index, image))
    text_bytes = form_payload_bytes()
    kept_bytes = 0
    for index in range(1, 4):
        if any(item[0] == index for item in prepared):
            continue
        path = os.path.join(folder, f"{index}.jpg")
        if os.path.isfile(path):
            kept_bytes += os.path.getsize(path)
    saved = [f"/static/images/listing-{listing_id}/{index}.jpg" for index in range(1, 4) if os.path.isfile(os.path.join(folder, f"{index}.jpg"))]
    if not prepared:
        if text_bytes + kept_bytes > MAX_PRODUCT_BYTES:
            raise ValueError("This listing cannot exceed 2 MB including images.")
        return saved
    encoded = encode_images_within_limit(prepared, kept_bytes, text_bytes)
    for index, data in encoded:
        with open(os.path.join(folder, f"{index}.jpg"), "wb") as handle:
            handle.write(data)
        path = f"/static/images/listing-{listing_id}/{index}.jpg"
        if path not in saved:
            saved.append(path)
    return sorted(set(saved))


def init_db():
    db = get_db()
    statements = [
        """
        CREATE TABLE IF NOT EXISTS products (
            id SERIAL PRIMARY KEY,
            name TEXT NOT NULL,
            category TEXT NOT NULL,
            price DOUBLE PRECISION NOT NULL,
            old_price DOUBLE PRECISION,
            badge TEXT,
            rating DOUBLE PRECISION DEFAULT 0,
            reviews_count INTEGER DEFAULT 0,
            sku TEXT UNIQUE,
            image TEXT,
            sizes TEXT,
            colors TEXT,
            description TEXT,
            stock INTEGER NOT NULL DEFAULT 20,
            active INTEGER DEFAULT 1,
            colors_json TEXT,
            sizes_json TEXT,
            amazon_url TEXT,
            etsy_url TEXT,
            ebay_url TEXT
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS reviews (
            id SERIAL PRIMARY KEY,
            product_id INTEGER NOT NULL REFERENCES products(id),
            name TEXT NOT NULL,
            rating INTEGER NOT NULL CHECK (rating BETWEEN 1 AND 5),
            body TEXT NOT NULL,
            created_at TEXT NOT NULL
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS contacts (
            id SERIAL PRIMARY KEY,
            user_id INTEGER,
            name TEXT NOT NULL,
            email TEXT NOT NULL,
            message TEXT NOT NULL,
            created_at TEXT NOT NULL
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS listings (
            id SERIAL PRIMARY KEY,
            user_id INTEGER,
            seller_name TEXT NOT NULL,
            title TEXT NOT NULL,
            category TEXT NOT NULL,
            price DOUBLE PRECISION NOT NULL,
            description TEXT NOT NULL,
            images_json TEXT,
            created_at TEXT NOT NULL
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS orders (
            id SERIAL PRIMARY KEY,
            customer_name TEXT NOT NULL,
            email TEXT NOT NULL,
            address TEXT NOT NULL,
            country TEXT NOT NULL DEFAULT 'Germany',
            payment_method TEXT NOT NULL DEFAULT 'pay_on_delivery',
            currency TEXT NOT NULL,
            total DOUBLE PRECISION NOT NULL,
            shipping DOUBLE PRECISION NOT NULL DEFAULT 0,
            items TEXT NOT NULL,
            created_at TEXT NOT NULL
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS users (
            id SERIAL PRIMARY KEY,
            name TEXT NOT NULL,
            email TEXT NOT NULL UNIQUE,
            password_hash TEXT NOT NULL,
            created_at TEXT NOT NULL
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS categories (
            id SERIAL PRIMARY KEY,
            name TEXT NOT NULL UNIQUE
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS shipping_rates (
            zone TEXT PRIMARY KEY,
            unit TEXT NOT NULL,
            under_value DOUBLE PRECISION NOT NULL,
            over_value DOUBLE PRECISION NOT NULL
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS main_categories (
            id SERIAL PRIMARY KEY,
            name TEXT NOT NULL UNIQUE
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS sub_categories (
            id SERIAL PRIMARY KEY,
            name TEXT NOT NULL,
            main_category TEXT NOT NULL,
            UNIQUE (name, main_category)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS sub_categories_2 (
            id SERIAL PRIMARY KEY,
            name TEXT NOT NULL,
            main_category TEXT NOT NULL,
            sub_category TEXT NOT NULL,
            UNIQUE (name, main_category, sub_category)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS sub_categories_3 (
            id SERIAL PRIMARY KEY,
            name TEXT NOT NULL,
            main_category TEXT NOT NULL,
            sub_category TEXT NOT NULL,
            sub_category_2 TEXT NOT NULL,
            UNIQUE (name, main_category, sub_category, sub_category_2)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS sub_categories_4 (
            id SERIAL PRIMARY KEY,
            name TEXT NOT NULL,
            main_category TEXT NOT NULL,
            sub_category TEXT NOT NULL,
            sub_category_2 TEXT NOT NULL,
            sub_category_3 TEXT NOT NULL,
            UNIQUE (name, main_category, sub_category, sub_category_2, sub_category_3)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS pl_users (
            id SERIAL PRIMARY KEY,
            username TEXT NOT NULL UNIQUE,
            display_name TEXT NOT NULL,
            password_hash TEXT NOT NULL,
            created_at TEXT NOT NULL
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS brands (
            id SERIAL PRIMARY KEY,
            name TEXT NOT NULL UNIQUE
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS faqs (
            id SERIAL PRIMARY KEY,
            question TEXT NOT NULL,
            answer TEXT NOT NULL,
            sort_order INTEGER NOT NULL DEFAULT 0
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS product_images (
            id SERIAL PRIMARY KEY,
            product_id INTEGER NOT NULL REFERENCES products(id) ON DELETE CASCADE,
            slot INTEGER NOT NULL CHECK (slot BETWEEN 1 AND 5),
            content_type TEXT NOT NULL DEFAULT 'image/jpeg',
            bytes BYTEA NOT NULL,
            byte_size INTEGER NOT NULL CHECK (byte_size > 0 AND byte_size <= 2097152),
            UNIQUE (product_id, slot)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS partner_applications (
            id SERIAL PRIMARY KEY,
            user_id INTEGER,
            kind TEXT NOT NULL,
            full_name TEXT NOT NULL,
            email TEXT NOT NULL,
            contact TEXT NOT NULL,
            country TEXT NOT NULL,
            product_name TEXT,
            product_type TEXT,
            interest TEXT,
            sell_country TEXT,
            platforms TEXT,
            store_link TEXT,
            status TEXT NOT NULL DEFAULT 'pending',
            reviewed_at TEXT,
            created_at TEXT NOT NULL
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS partner_application_images (
            id SERIAL PRIMARY KEY,
            application_id INTEGER NOT NULL REFERENCES partner_applications(id) ON DELETE CASCADE,
            slot INTEGER NOT NULL CHECK (slot BETWEEN 1 AND 5),
            content_type TEXT NOT NULL DEFAULT 'image/jpeg',
            bytes BYTEA NOT NULL,
            byte_size INTEGER NOT NULL CHECK (byte_size > 0 AND byte_size <= 2097152),
            UNIQUE (application_id, slot)
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS store_settings (
            key TEXT PRIMARY KEY,
            value TEXT NOT NULL DEFAULT ''
        )
        """,
        """
        CREATE TABLE IF NOT EXISTS pl_password_requests (
            id SERIAL PRIMARY KEY,
            username TEXT NOT NULL,
            display_name TEXT,
            password_hash TEXT NOT NULL,
            status TEXT NOT NULL DEFAULT 'pending',
            created_at TEXT NOT NULL,
            reviewed_at TEXT
        )
        """,
    ]
    for statement in statements:
        db.execute(statement)
    db.commit()

    ensure_columns(
        "orders",
        {
            "country": "TEXT NOT NULL DEFAULT 'Germany'",
            "payment_method": "TEXT NOT NULL DEFAULT 'pay_on_delivery'",
            "shipping": "DOUBLE PRECISION NOT NULL DEFAULT 0",
            "tax": "DOUBLE PRECISION NOT NULL DEFAULT 0",
            "status": "TEXT NOT NULL DEFAULT 'new'",
            "tracking_carrier": "TEXT",
            "tracking_number": "TEXT",
            "payment_status": "TEXT NOT NULL DEFAULT 'unpaid'",
            "payment_reference": "TEXT",
            "payment_amount": "DOUBLE PRECISION",
            "payment_currency": "TEXT",
        },
    )
    ensure_columns(
        "products",
        {
            "stock": "INTEGER NOT NULL DEFAULT 20",
            "colors_json": "TEXT",
            "sizes_json": "TEXT",
            "amazon_url": "TEXT",
            "etsy_url": "TEXT",
            "ebay_url": "TEXT",
            "discount_percent": "DOUBLE PRECISION NOT NULL DEFAULT 0",
            "weight": "DOUBLE PRECISION NOT NULL DEFAULT 0",
            "shipping_json": "TEXT",
            "pakistan_price": "DOUBLE PRECISION NOT NULL DEFAULT 0",
            "pakistan_discount_percent": "DOUBLE PRECISION NOT NULL DEFAULT 0",
            "condition": "TEXT NOT NULL DEFAULT 'new_with_tag'",
            "main_category": "TEXT NOT NULL DEFAULT 'Unisex'",
            "main_categories": "TEXT",
            "sub_category": "TEXT",
            "sub_categories": "TEXT",
            "sub_category_2": "TEXT",
            "sub_category_3": "TEXT",
            "sub_category_4": "TEXT",
            "product_type": "TEXT NOT NULL DEFAULT 'Clothes'",
            "size_group": "TEXT NOT NULL DEFAULT 'Unisex'",
            "genders": "TEXT",
            "gender_offers": "TEXT",
            "packing_weight": "DOUBLE PRECISION NOT NULL DEFAULT 0",
            "region_visibility": "TEXT NOT NULL DEFAULT 'all'",
            "product_tags": "TEXT",
            "product_hashtags": "TEXT",
            "likes": "INTEGER NOT NULL DEFAULT 0",
            "featured": "INTEGER NOT NULL DEFAULT 0",
            "deal_of_week": "INTEGER NOT NULL DEFAULT 0",
            "new_arrival": "INTEGER NOT NULL DEFAULT 0",
            "is_draft": "INTEGER NOT NULL DEFAULT 0",
            "listed_by": "TEXT NOT NULL DEFAULT 'admin'",
            "brand": "TEXT",
            "volume_discounts": "TEXT",
            "pakistan_volume_discounts": "TEXT",
            "fulfillment": "TEXT NOT NULL DEFAULT 'physical'",
        },
    )
    ensure_columns("users", {"country": "TEXT", "firebase_uid": "TEXT", "auth_provider": "TEXT"})
    ensure_columns("contacts", {"user_id": "INTEGER"})
    ensure_columns(
        "listings",
        {
            "user_id": "INTEGER",
            "images_json": "TEXT",
            "status": "TEXT NOT NULL DEFAULT 'pending'",
            "reviewed_at": "TEXT",
            "product_id": "INTEGER",
        },
    )
    ensure_columns(
        "product_listings",
        {
            "picture_main": "TEXT",
            "picture_2": "TEXT",
            "picture_3": "TEXT",
            "pictures_extra": "TEXT[]",
        },
    )

    if not db.execute("SELECT 1 AS ok FROM categories LIMIT 1").fetchone():
        db.executemany("INSERT INTO categories (name) VALUES (?)", [(name,) for name in DEFAULT_CATEGORIES])
    if not db.execute("SELECT 1 AS ok FROM main_categories LIMIT 1").fetchone():
        db.executemany("INSERT INTO main_categories (name) VALUES (?)", [(name,) for name in MAIN_CATEGORIES])
    migrate_sub_categories_to_main(db)
    seed_sub_categories(db)
    if not db.execute("SELECT 1 AS ok FROM faqs LIMIT 1").fetchone():
        db.executemany(
            "INSERT INTO faqs (question, answer, sort_order) VALUES (?,?,?)",
            [(question, answer, index) for index, (question, answer) in enumerate(DEFAULT_FAQS)],
        )

    for zone in DEFAULT_SHIPPING_ZONES:
        db.execute(
            """
            INSERT INTO shipping_rates (zone, unit, under_value, over_value)
            VALUES (?,?,?,?)
            ON CONFLICT (zone) DO NOTHING
            """,
            (zone["name"], zone["unit"], zone["under"], zone["over"]),
        )

    if not db.execute("SELECT 1 AS ok FROM products LIMIT 1").fetchone():
        for row in PRODUCTS:
            name, category, price, old_price, badge, rating, reviews_count, sku, image, sizes, colors, description, stock = row
            color_rows = colors_from_legacy(colors, stock)
            size_rows = sizes_from_legacy(sizes)
            db.execute(
                """
                INSERT INTO products (
                    name, category, price, old_price, badge, rating, reviews_count, sku, image,
                    sizes, colors, description, stock, colors_json, sizes_json
                ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
                """,
                (
                    name,
                    category,
                    price,
                    old_price,
                    badge,
                    rating,
                    reviews_count,
                    sku,
                    image,
                    sizes,
                    colors,
                    description,
                    stock,
                    json.dumps(color_rows),
                    json.dumps(size_rows),
                ),
            )
        db.executemany(
            "INSERT INTO reviews (product_id,name,rating,body,created_at) VALUES (?,?,?,?,?)",
            [
                (10, "Sarah Williams", 5, "The fit is spot-on and the red colour looks even better in person.", "2026-08-10"),
                (10, "Daniel Cooper", 5, "Light, comfortable and genuinely supportive for daily runs.", "2026-08-12"),
                (5, "Ahmed Hassan", 5, "Excellent stitching and a premium leather finish.", "2026-08-08"),
            ],
        )

    for row in db.execute("SELECT id, sizes, colors, stock, colors_json, sizes_json FROM products").fetchall():
        updates = {}
        if not row["colors_json"]:
            updates["colors_json"] = json.dumps(colors_from_legacy(row["colors"], row["stock"]))
        if not row["sizes_json"]:
            updates["sizes_json"] = json.dumps(sizes_from_legacy(row["sizes"]))
        if updates:
            db.execute(
                f"UPDATE products SET {', '.join(f'{key}=?' for key in updates)} WHERE id=?",
                (*updates.values(), row["id"]),
            )
    db.commit()
    for statement in (
        "CREATE INDEX IF NOT EXISTS products_active_idx ON products (active)",
        "CREATE INDEX IF NOT EXISTS products_active_id_idx ON products (active, id DESC)",
        "CREATE INDEX IF NOT EXISTS products_main_category_idx ON products (main_category)",
        "CREATE INDEX IF NOT EXISTS products_sub_category_idx ON products (sub_category)",
        "CREATE INDEX IF NOT EXISTS products_brand_idx ON products (brand)",
        "CREATE INDEX IF NOT EXISTS products_listed_by_idx ON products (listed_by)",
        "CREATE INDEX IF NOT EXISTS products_featured_idx ON products (featured)",
        "CREATE INDEX IF NOT EXISTS products_new_arrival_idx ON products (new_arrival)",
        "CREATE INDEX IF NOT EXISTS products_is_draft_idx ON products (is_draft)",
        "CREATE INDEX IF NOT EXISTS product_images_product_id_idx ON product_images (product_id)",
        "CREATE UNIQUE INDEX IF NOT EXISTS users_firebase_uid_key ON users (firebase_uid) WHERE firebase_uid IS NOT NULL AND firebase_uid <> ''",
        "CREATE UNIQUE INDEX IF NOT EXISTS orders_payment_reference_key ON orders (payment_reference) WHERE payment_reference IS NOT NULL AND payment_reference <> ''",
    ):
        try:
            db.execute(statement)
        except Exception:
            rollback_db()
    db.commit()


def current_user():
    user_id = session.get("user_id")
    if not user_id:
        return None
    return get_db().execute("SELECT * FROM users WHERE id=?", (user_id,)).fetchone()


def login_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if not session.get("user_id"):
            flash("Please sign in or create a profile to continue.", "error")
            return redirect(url_for("login", next=request.path))
        return view(*args, **kwargs)

    return wrapped


def admin_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if not session.get("is_admin"):
            flash("Please sign in to access the admin dashboard.", "error")
            return redirect(url_for("admin_login"))
        return view(*args, **kwargs)

    return wrapped


def client_ip():
    forwarded = (request.headers.get("X-Forwarded-For") or "").split(",")[0].strip()
    return forwarded or (request.remote_addr or "unknown")


def staff_path(path=None):
    path = path or request.path
    return path.startswith("/admin") or path.startswith("/pl")


def ensure_csrf_token():
    token = session.get("_csrf")
    if not token:
        token = secrets.token_urlsafe(32)
        session["_csrf"] = token
    return token


def csrf_field():
    return Markup(f'<input type="hidden" name="csrf_token" value="{ensure_csrf_token()}">')


def csrf_ok():
    expected = session.get("_csrf") or ""
    supplied = request.form.get("csrf_token") or request.headers.get("X-CSRF-Token") or ""
    return bool(expected) and hmac.compare_digest(expected, supplied)


def login_attempt_key(scope):
    return f"{scope}:{client_ip()}"


def login_locked(scope):
    key = login_attempt_key(scope)
    now = time.time()
    hits = [stamp for stamp in LOGIN_ATTEMPTS.get(key, []) if now - stamp < LOGIN_WINDOW_SECONDS]
    LOGIN_ATTEMPTS[key] = hits
    return len(hits) >= LOGIN_MAX_ATTEMPTS


def record_login_failure(scope):
    LOGIN_ATTEMPTS.setdefault(login_attempt_key(scope), []).append(time.time())


def clear_login_failures(scope):
    LOGIN_ATTEMPTS.pop(login_attempt_key(scope), None)


def expire_staff_sessions():
    now = time.time()
    limit = ADMIN_SESSION_MINUTES * 60
    if session.get("is_admin"):
        seen = float(session.get("admin_seen_at") or 0)
        if seen and now - seen > limit:
            session.pop("is_admin", None)
            session.pop("admin_seen_at", None)
            flash("Admin session expired. Please sign in again.", "error")
        else:
            session["admin_seen_at"] = now
    if session.get("is_pl"):
        seen = float(session.get("pl_seen_at") or 0)
        if seen and now - seen > limit:
            session.pop("is_pl", None)
            session.pop("pl_username", None)
            session.pop("pl_display_name", None)
            session.pop("pl_seen_at", None)
            flash("Listing team session expired. Please sign in again.", "error")
        else:
            session["pl_seen_at"] = now


def mail_config():
    email = current_admin_email()
    password = get_setting("mail_password") or os.environ.get("MAIL_PASSWORD") or ""
    return {
        "mail_server": get_setting("mail_server") or os.environ.get("MAIL_SERVER") or "smtp.gmail.com",
        "mail_port": get_setting("mail_port") or os.environ.get("MAIL_PORT") or "587",
        "mail_username": get_setting("mail_username") or os.environ.get("MAIL_USERNAME") or email,
        "mail_from": get_setting("mail_from") or os.environ.get("MAIL_FROM") or email,
        "mail_use_tls": get_setting("mail_use_tls") or os.environ.get("MAIL_USE_TLS") or "1",
        "mail_password": password,
        "mail_password_set": bool(password.strip()),
    }


def mail_ready():
    cfg = mail_config()
    return bool(current_admin_email() and cfg["mail_server"] and cfg["mail_password_set"])


def admin_security_notes():
    notes = []
    if (ADMIN_USERNAME or "").strip().lower() == "admin":
        notes.append("Change ADMIN_USERNAME in .env from the default admin.")
    if not mail_ready():
        notes.append("Save a Gmail app password under Email service so password reset and merchant codes can be emailed.")
    if not SESSION_COOKIE_SECURE and FORCE_HTTPS:
        notes.append("Turn on SESSION_COOKIE_SECURE=1 when the store is served over HTTPS.")
    return notes


def get_setting(key, default=""):
    try:
        row = get_db().execute("SELECT value FROM store_settings WHERE key=?", (key,)).fetchone()
    except Exception:
        rollback_db()
        return default
    if not row:
        return default
    return row["value"] or default


def set_setting(key, value):
    db = get_db()
    db.execute(
        """
        INSERT INTO store_settings (key, value) VALUES (?, ?)
        ON CONFLICT (key) DO UPDATE SET value=EXCLUDED.value
        """,
        (key, value or ""),
    )
    db.commit()


FOOTER_FIELD_TYPES = ("text", "textarea", "email", "link")
FOOTER_FIELDS_MAX = 20
FOOTER_DEFAULT_BRAND = "AR Shopping World"
FOOTER_DEFAULT_EMAIL = "support@arshoppingworld.com"


def safe_footer_url(url):
    value = (url or "").strip()
    if not value:
        return False
    if value.startswith("/") and not value.startswith("//"):
        return True
    lower = value.lower()
    return lower.startswith(("http://", "https://", "mailto:"))


def normalize_footer_field(entry):
    if not isinstance(entry, dict):
        return None
    field_type = (entry.get("type") or "text").strip().lower()
    if field_type not in FOOTER_FIELD_TYPES:
        field_type = "text"
    label = str(entry.get("label") or "").strip()[:80]
    value = str(entry.get("value") or "").strip()
    if field_type == "textarea":
        value = value[:500]
    elif field_type == "link":
        value = value[:300]
    else:
        value = value[:200]
    return {"type": field_type, "label": label, "value": value}


def normalize_footer_fields(entries):
    fields = []
    for entry in entries or []:
        item = normalize_footer_field(entry)
        if not item:
            continue
        # Drop completely empty rows.
        if not item["label"] and not item["value"]:
            continue
        fields.append(item)
        if len(fields) >= FOOTER_FIELDS_MAX:
            break
    return fields


def legacy_footer_fields():
    """Build dynamic fields from the older fixed footer keys (one-time migration)."""
    fields = []
    blurb = (get_setting("footer_blurb") or "").strip()
    if blurb:
        fields.append({"type": "textarea", "label": "About", "value": blurb})
    email = (get_setting("footer_email") or "").strip()
    if email:
        fields.append({"type": "email", "label": "Email", "value": email})
    hours = (get_setting("footer_hours") or "").strip()
    if hours:
        fields.append({"type": "text", "label": "Hours", "value": hours})
    for index in range(1, 4):
        label = (get_setting(f"footer_link_{index}_label") or "").strip()
        url = (get_setting(f"footer_link_{index}_url") or "").strip()
        if label and url:
            fields.append({"type": "link", "label": label, "value": url})
    if fields:
        return normalize_footer_fields(fields)
    return [
        {"type": "textarea", "label": "About", "value": ""},
        {"type": "email", "label": "Email", "value": FOOTER_DEFAULT_EMAIL},
        {"type": "text", "label": "Hours", "value": ""},
    ]


def load_footer_fields():
    raw = get_setting("footer_fields_json", "")
    if raw:
        try:
            parsed = json.loads(raw)
            if isinstance(parsed, list):
                return normalize_footer_fields(parsed)
        except (TypeError, json.JSONDecodeError):
            pass
    return legacy_footer_fields()


def footer_settings_for_admin():
    return {
        "footer_brand": get_setting("footer_brand", FOOTER_DEFAULT_BRAND),
        "footer_copyright": get_setting("footer_copyright", ""),
        "fields": load_footer_fields(),
        "field_types": FOOTER_FIELD_TYPES,
        "fields_max": FOOTER_FIELDS_MAX,
    }


def footer_view():
    brand = (get_setting("footer_brand") or "").strip() or FOOTER_DEFAULT_BRAND
    copyright_line = (get_setting("footer_copyright") or "").strip()
    fields = load_footer_fields()
    about_fields = [item for item in fields if item["type"] == "textarea" and item["value"]]
    contact_fields = [
        item
        for item in fields
        if item["type"] in {"text", "email"} and item["value"]
    ]
    links = [
        {"label": item["label"] or item["value"], "url": item["value"]}
        for item in fields
        if item["type"] == "link" and item["label"] and item["value"] and safe_footer_url(item["value"])
    ]
    # Prefer first about/email for template convenience / defaults.
    blurb = about_fields[0]["value"] if about_fields else ""
    email = next((item["value"] for item in contact_fields if item["type"] == "email"), "") or FOOTER_DEFAULT_EMAIL
    hours = next((item["value"] for item in contact_fields if item["type"] == "text" and (item["label"] or "").lower() == "hours"), "")
    if not hours:
        hours = next((item["value"] for item in contact_fields if item["type"] == "text"), "")
    return {
        "brand": brand,
        "blurb": blurb,
        "about_fields": about_fields,
        "email": email,
        "hours": hours,
        "contact_fields": contact_fields,
        "copyright": copyright_line,
        "links": links,
        "fields": fields,
    }


def save_footer_from_form():
    brand = (request.form.get("footer_brand") or "").strip()[:80]
    copyright_line = (request.form.get("footer_copyright") or "").strip()[:200]
    types = request.form.getlist("footer_field_type")
    labels = request.form.getlist("footer_field_label")
    values = request.form.getlist("footer_field_value")
    count = max(len(types), len(labels), len(values))
    if count > FOOTER_FIELDS_MAX:
        raise ValueError(f"You can add at most {FOOTER_FIELDS_MAX} footer fields.")
    fields = []
    for index in range(count):
        field_type = (types[index] if index < len(types) else "text") or "text"
        label = labels[index] if index < len(labels) else ""
        value = values[index] if index < len(values) else ""
        item = normalize_footer_field({"type": field_type, "label": label, "value": value})
        if not item:
            continue
        if not item["label"] and not item["value"]:
            continue
        if item["type"] == "link":
            if not item["label"] or not item["value"]:
                raise ValueError("Each footer link needs both a label and a URL, or remove that row.")
            if not safe_footer_url(item["value"]):
                raise ValueError("Footer links must be a site path (/…), http(s) URL, or mailto: link.")
        if item["type"] == "email" and item["value"] and "@" not in item["value"]:
            raise ValueError("Enter a valid email for email fields, or clear that row.")
        fields.append(item)
    set_setting("footer_brand", brand)
    set_setting("footer_copyright", copyright_line)
    set_setting("footer_fields_json", json.dumps(fields))


def current_admin_password_hash():
    return get_setting("admin_password_hash") or ADMIN_PASSWORD_HASH


def current_admin_email():
    return (get_setting("admin_email") or ADMIN_EMAIL or "").strip().lower()


MERCHANT_SETTING_KEYS = (
    "paypal_business_email",
    "paypal_client_id",
    "paypal_secret",
    "paypal_sandbox",
    "bank_account_name",
    "bank_name",
    "bank_iban",
    "bank_swift",
    "easypaisa_account_name",
    "easypaisa_number",
    "jazzcash_account_name",
    "jazzcash_number",
    "stripe_publishable_key",
    "stripe_secret",
    "klarna_merchant_id",
    "klarna_username",
    "klarna_secret",
    "apple_pay_merchant_id",
    "zelle_account_name",
    "zelle_handle",
)
MERCHANT_SECRET_KEYS = ("paypal_secret", "stripe_secret", "klarna_secret")
MERCHANT_VERIFY_MINUTES = 10


def merchant_settings():
    return {key: get_setting(key) for key in MERCHANT_SETTING_KEYS}


def setting_filled(data, *keys):
    return any((data.get(key) or "").strip() for key in keys)


def paypal_merchant_ready(settings=None):
    data = settings or merchant_settings()
    return bool((data.get("paypal_client_id") or "").strip() and (data.get("paypal_secret") or "").strip())


def bank_merchant_ready(settings=None):
    return setting_filled(settings or merchant_settings(), "bank_iban", "bank_account_name")


def easypaisa_ready(settings=None):
    return setting_filled(settings or merchant_settings(), "easypaisa_number", "easypaisa_account_name")


def jazzcash_ready(settings=None):
    return setting_filled(settings or merchant_settings(), "jazzcash_number", "jazzcash_account_name")


def stripe_ready(settings=None):
    data = settings or merchant_settings()
    return bool((data.get("stripe_secret") or "").strip())


def klarna_ready(settings=None):
    return setting_filled(settings or merchant_settings(), "klarna_merchant_id", "klarna_username")


def apple_pay_ready(settings=None):
    return setting_filled(settings or merchant_settings(), "apple_pay_merchant_id")


def zelle_ready(settings=None):
    return setting_filled(settings or merchant_settings(), "zelle_handle", "zelle_account_name")


def merchant_ready_flags(settings=None):
    data = settings or merchant_settings()
    return {
        "paypal_ready": paypal_merchant_ready(data),
        "bank_ready": bank_merchant_ready(data),
        "easypaisa_ready": easypaisa_ready(data),
        "jazzcash_ready": jazzcash_ready(data),
        "stripe_ready": stripe_ready(data),
        "klarna_ready": klarna_ready(data),
        "apple_pay_ready": apple_pay_ready(data),
        "zelle_ready": zelle_ready(data),
    }


def checkout_zone_name():
    country = checkout_data().get("country")
    if country in ZONE_NAMES:
        return country
    return customer_zone_name()


def allowed_payment_methods(zone=None):
    zone = zone or checkout_zone_name()
    pakistan = zone == "Pakistan"
    methods = ["pay_on_delivery", "bank_transfer"]
    flags = merchant_ready_flags()
    if flags["paypal_ready"]:
        methods.append("paypal")
    if pakistan:
        if flags["easypaisa_ready"]:
            methods.append("easypaisa")
        if flags["jazzcash_ready"]:
            methods.append("jazzcash")
    else:
        if flags["stripe_ready"]:
            methods.append("stripe")
        if flags["klarna_ready"]:
            methods.append("klarna")
        if flags["apple_pay_ready"]:
            methods.append("apple_pay")
        if flags["zelle_ready"]:
            methods.append("zelle")
    return methods


def pending_pl_password_requests():
    try:
        return get_db().execute(
            "SELECT * FROM pl_password_requests WHERE status='pending' ORDER BY id DESC"
        ).fetchall()
    except Exception:
        rollback_db()
        return []


def admin_reset_serializer():
    return URLSafeTimedSerializer(app.config["SECRET_KEY"], salt="admin-password-reset")


def mask_email(email):
    email = (email or "").strip()
    if "@" not in email:
        return email
    name, domain = email.split("@", 1)
    shown = name[:1] or "*"
    return f"{shown}***@{domain}"


def admin_password_ok(password):
    password_hash = current_admin_password_hash()
    return bool(password_hash and check_password_hash(password_hash, password or ""))


def merchant_payload_from_form():
    email = request.form.get("paypal_business_email", "").strip().lower()[:120]
    zelle = request.form.get("zelle_handle", "").strip()[:80]
    if email and "@" not in email:
        return None, "Enter a valid PayPal business email, or leave it blank."
    if zelle and "@" in zelle and zelle.count("@") != 1:
        return None, "Enter a valid Zelle email or mobile number, or leave it blank."
    payload = {
        "paypal_business_email": email,
        "paypal_client_id": request.form.get("paypal_client_id", "").strip()[:200],
        "paypal_sandbox": "1" if request.form.get("paypal_sandbox") else "",
        "bank_account_name": request.form.get("bank_account_name", "").strip()[:120],
        "bank_name": request.form.get("bank_name", "").strip()[:120],
        "bank_iban": request.form.get("bank_iban", "").strip()[:80],
        "bank_swift": request.form.get("bank_swift", "").strip()[:40],
        "easypaisa_account_name": request.form.get("easypaisa_account_name", "").strip()[:120],
        "easypaisa_number": request.form.get("easypaisa_number", "").strip()[:40],
        "jazzcash_account_name": request.form.get("jazzcash_account_name", "").strip()[:120],
        "jazzcash_number": request.form.get("jazzcash_number", "").strip()[:40],
        "stripe_publishable_key": request.form.get("stripe_publishable_key", "").strip()[:200],
        "klarna_merchant_id": request.form.get("klarna_merchant_id", "").strip()[:120],
        "klarna_username": request.form.get("klarna_username", "").strip()[:200],
        "apple_pay_merchant_id": request.form.get("apple_pay_merchant_id", "").strip()[:120],
        "zelle_account_name": request.form.get("zelle_account_name", "").strip()[:120],
        "zelle_handle": zelle,
    }
    for secret_key in MERCHANT_SECRET_KEYS:
        secret = request.form.get(secret_key, "").strip()
        if secret:
            payload[secret_key] = secret[:200]
    return payload, None


def apply_merchant_payload(payload):
    for key, value in payload.items():
        if key in MERCHANT_SECRET_KEYS and not value:
            continue
        set_setting(key, value)


def pending_merchant_verify():
    data = session.get("merchant_verify")
    if not isinstance(data, dict):
        return None
    try:
        expires = datetime.fromisoformat(data.get("expires") or "")
    except ValueError:
        session.pop("merchant_verify", None)
        return None
    if expires < datetime.utcnow():
        session.pop("merchant_verify", None)
        session.modified = True
        return None
    return data


def start_merchant_verify(payload):
    if not current_admin_email():
        return False, "Set an admin email first so a verification code can be sent."
    code = f"{secrets.randbelow(1_000_000):06d}"
    sent, error = send_admin_email_result(
        "Confirm merchant changes — AR Shopping World",
        (
            f"Your merchant verification code is {code}.\n\n"
            f"It expires in {MERCHANT_VERIFY_MINUTES} minutes. "
            "If you did not ask to change store merchants, ignore this email.\n"
        ),
    )
    if not sent:
        return False, error or "The verification email could not be sent."
    session["merchant_verify"] = {
        "code_hash": generate_password_hash(code),
        "expires": (datetime.utcnow() + timedelta(minutes=MERCHANT_VERIFY_MINUTES)).isoformat(),
        "payload": payload,
        "sent_to": mask_email(current_admin_email()),
    }
    session.modified = True
    return True, None


def send_admin_email_result(subject, body, to=None):
    recipient = (to or current_admin_email() or "").strip()
    cfg = mail_config()
    server = (cfg["mail_server"] or "").strip()
    username = (cfg["mail_username"] or "").strip()
    password = cfg["mail_password"] or ""
    sender = (cfg["mail_from"] or username or recipient).strip()
    if not recipient:
        return False, "Set an admin email first."
    if not server:
        return False, "Set the mail server in Email service."
    if not password:
        return False, "Save a Gmail app password in Email service."
    try:
        port = int(cfg["mail_port"] or 587)
        use_tls = str(cfg["mail_use_tls"]).strip().lower() not in {"0", "false", "no"}
        message = EmailMessage()
        message["Subject"] = subject
        message["From"] = sender
        message["To"] = recipient
        message.set_content(body)
        with smtplib.SMTP(server, port, timeout=20) as smtp:
            if use_tls:
                smtp.starttls()
            if username:
                smtp.login(username, password)
            smtp.send_message(message)
    except Exception:
        return False, "The email could not be sent. Check the Gmail address and app password."
    return True, None


def send_admin_email(subject, body, to=None):
    sent, _error = send_admin_email_result(subject, body, to)
    return sent


@app.before_request
def setup():
    if request.endpoint == "static":
        return None
    if FORCE_HTTPS and (request.headers.get("X-Forwarded-Proto") or request.scheme) != "https":
        return redirect(request.url.replace("http://", "https://", 1), 301)
    if not app.config["DB_INITIALIZED"]:
        init_db()
        app.config["DB_INITIALIZED"] = True
    session.setdefault("currency", "EUR")
    session.setdefault("language", "en")
    session.setdefault("cart", {})
    session.setdefault("liked", [])
    session.setdefault("checkout", {})
    auto_localize_visitor()
    expire_staff_sessions()
    ensure_csrf_token()
    if request.method == "POST" and staff_path() and not csrf_ok():
        flash("That form expired or was not trusted. Refresh the page and try again.", "error")
        if request.path.startswith("/pl"):
            return redirect(request.referrer or url_for("pl_login"))
        return redirect(request.referrer or url_for("admin_login"))


@app.after_request
def security_headers(response):
    response.headers.setdefault("X-Content-Type-Options", "nosniff")
    response.headers.setdefault("X-Frame-Options", "SAMEORIGIN")
    response.headers.setdefault("Referrer-Policy", "strict-origin-when-cross-origin")
    response.headers.setdefault("Permissions-Policy", "camera=(), microphone=(), geolocation=()")
    if FORCE_HTTPS or SESSION_COOKIE_SECURE:
        response.headers.setdefault("Strict-Transport-Security", "max-age=31536000; includeSubDomains")
    return response


@app.context_processor
def helpers():
    user = current_user()
    return {
        "currencies": CURRENCIES,
        "languages": LANGUAGES,
        "currency": session["currency"],
        "language": session["language"],
        "pakistan_customer": pakistan_customer(),
        "customer_region": customer_zone_name(),
        "customer_location_source": customer_location()["source"],
        "shipping_regions": ZONE_NAMES,
        "cart_count": sum(session["cart"].values()),
        "is_admin": session.get("is_admin", False),
        "is_pl": session.get("is_pl", False),
        "pl_display_name": session.get("pl_display_name", ""),
        "current_user": user,
        "liked_ids": liked_product_ids(),
        "shop_nav": shop_category_tree(),
        "audiences": AUDIENCES,
        "product_genders": PRODUCT_GENDERS,
        "selected_who": selected_audience_key(),
        "shop_url": shop_url,
        "selected_main": request.args.get("main", ""),
        "selected_sub": request.args.get("sub", ""),
        "selected_sale": request.args.get("sale", "").strip() in {"1", "true", "yes"},
        "selected_new": request.args.get("new", "").strip() in {"1", "true", "yes"},
        "tax_percent": PRODUCT_TAX_PERCENT,
        "csrf_token": ensure_csrf_token(),
        "csrf_field": csrf_field,
        "t": lambda key, **kwargs: translate(key, session.get("language") or "en", **kwargs),
        "footer": footer_view(),
    }


def selected_audience_key():
    who = (request.args.get("who") or "").strip().lower()
    return who if who in {key for key, _label, _group in AUDIENCES} else ""


def shop_url(**kwargs):
    who = selected_audience_key()
    if who and "who" not in kwargs:
        kwargs["who"] = who
    clean = {key: value for key, value in kwargs.items() if value not in (None, "", False)}
    return url_for("products", **clean)


def parse_volume_discounts_stored(raw):
    if isinstance(raw, list):
        data = raw
    else:
        try:
            data = json.loads(raw or "[]")
        except (TypeError, json.JSONDecodeError):
            data = []
    tiers = []
    seen = set()
    for entry in data if isinstance(data, list) else []:
        if not isinstance(entry, dict):
            continue
        try:
            minimum = int(entry.get("min", 0) or 0)
            percent = float(entry.get("percent", 0) or 0)
        except (TypeError, ValueError):
            continue
        if minimum < 1 or minimum in seen:
            continue
        seen.add(minimum)
        tiers.append({"min": minimum, "percent": max(0.0, min(100.0, percent))})
    tiers.sort(key=lambda tier: tier["min"])
    return tiers


def parse_volume_discounts_form(prefix="volume"):
    tiers = []
    seen = set()
    for index in range(1, 6):
        try:
            minimum = int(request.form.get(f"{prefix}_min_{index}", 0) or 0)
        except ValueError:
            minimum = 0
        try:
            percent = float(request.form.get(f"{prefix}_percent_{index}", 0) or 0)
        except ValueError:
            percent = 0
        if minimum < 1 or minimum in seen:
            continue
        seen.add(minimum)
        tiers.append({"min": minimum, "percent": max(0.0, min(100.0, percent))})
    tiers.sort(key=lambda tier: tier["min"])
    return tiers


def volume_percent_for(tiers, quantity):
    percent = 0.0
    for tier in tiers or []:
        if quantity >= int(tier.get("min") or 0):
            percent = float(tier.get("percent") or 0)
    return percent


def clamp_percent(value):
    try:
        return max(0.0, min(100.0, float(value or 0)))
    except (TypeError, ValueError):
        return 0.0


def apply_percent(amount, percent):
    return round(float(amount or 0) * (100 - clamp_percent(percent)) / 100, 2)


def product_tax(net_amount):
    return round(float(net_amount or 0) * PRODUCT_TAX_PERCENT / 100, 2)


def price_with_tax(net_amount):
    net = round(float(net_amount or 0), 2)
    return round(net + product_tax(net), 2)


def priced_volume_tiers(tiers, base_price):
    rows = []
    for tier in tiers or []:
        percent = float(tier.get("percent") or 0)
        unit_price = round(float(base_price or 0) * (100 - percent) / 100, 2)
        tax_amount = product_tax(unit_price)
        rows.append(
            {
                "min": int(tier["min"]),
                "percent": percent,
                "unit_price": unit_price,
                "tax_amount": tax_amount,
                "unit_price_with_tax": round(unit_price + tax_amount, 2),
            }
        )
    return rows


def volume_form_slots(existing=None):
    slots = list(existing or [])
    defaults = [{"min": 1, "percent": 0}, {"min": 5, "percent": 0}, {"min": 20, "percent": 0}]
    if not slots:
        slots = defaults
    while len(slots) < 3:
        slots.append({"min": "", "percent": 0})
    return slots[:5]


def product(row, gallery_map=None):
    item = dict(row) if not isinstance(row, dict) else dict(row)
    try:
        item["color_rows"] = json.loads(item.get("colors_json") or "[]")
    except json.JSONDecodeError:
        item["color_rows"] = colors_from_legacy(item.get("colors"), item.get("stock"))
    if not isinstance(item.get("color_rows"), list):
        item["color_rows"] = colors_from_legacy(item.get("colors"), item.get("stock"))
    item["color_rows"] = [entry for entry in item["color_rows"] if isinstance(entry, dict)]
    try:
        item["size_rows"] = json.loads(item.get("sizes_json") or "[]")
    except json.JSONDecodeError:
        item["size_rows"] = sizes_from_legacy(item.get("sizes"))
    if not isinstance(item.get("size_rows"), list):
        item["size_rows"] = sizes_from_legacy(item.get("sizes"))
    for entry in item["color_rows"]:
        if not isinstance(entry.get("sizes"), dict):
            sizes = item["size_rows"] or ["Standard"]
            quantity = max(int(entry.get("quantity", 0)), 0)
            per_size, remainder = divmod(quantity, len(sizes))
            entry["sizes"] = {
                size: per_size + (1 if index < remainder else 0)
                for index, size in enumerate(sizes)
            }
        entry["quantity"] = sum(max(int(value or 0), 0) for value in entry["sizes"].values())
    item["sizes"] = [str(size) for size in item["size_rows"] if str(size).strip()]
    item["size_rows"] = item["sizes"]
    item["colors"] = [entry.get("name") or "Default" for entry in item["color_rows"]]
    item["stock"] = sum(int(entry.get("quantity", 0) or 0) for entry in item["color_rows"])
    apply_product_gallery(item, gallery_map=gallery_map)
    item["amazon_url"] = item.get("amazon_url") or ""
    item["etsy_url"] = item.get("etsy_url") or ""
    item["ebay_url"] = item.get("ebay_url") or ""
    try:
        weight = max(0.0, float(item.get("weight") or 0))
    except (TypeError, ValueError):
        weight = 0.0
    item["gender_offers"] = parse_gender_offers(item.get("gender_offers"))
    item["product_volume_discounts"] = parse_volume_discounts_stored(item.get("volume_discounts"))
    item["product_pakistan_volume_discounts"] = parse_volume_discounts_stored(item.get("pakistan_volume_discounts"))
    item["volume_discounts"] = list(item["product_volume_discounts"])
    item["pakistan_volume_discounts"] = list(item["product_pakistan_volume_discounts"])
    chosen_gender = choose_offer_gender(item)
    item["offer_gender"] = chosen_gender
    item["offer_label"] = GENDER_LABELS.get(chosen_gender, "")
    if chosen_gender:
        apply_stored_offer(item, item["gender_offers"][chosen_gender])
    original_price = float(item.get("price") or 0)
    try:
        pakistan_original = max(0.0, float(item.get("pakistan_price") or 0))
    except (TypeError, ValueError):
        pakistan_original = 0.0
    item["weight"] = weight
    item["original_price"] = original_price
    item["price"] = original_price
    item["pakistan_original_price"] = pakistan_original
    item["pakistan_price"] = pakistan_original
    item["discount_percent"] = 0
    item["pakistan_discount_percent"] = 0
    item["display_discount_percent"] = 0
    item["volume_discounts"] = parse_volume_discounts_stored(item.get("volume_discounts"))
    item["pakistan_volume_discounts"] = parse_volume_discounts_stored(item.get("pakistan_volume_discounts"))
    if pakistan_customer() and pakistan_original > 0:
        item["display_original_price"] = pakistan_original
        item["display_price"] = pakistan_original
        active_volume = item["pakistan_volume_discounts"] or item["volume_discounts"]
    else:
        item["display_original_price"] = original_price
        item["display_price"] = original_price
        active_volume = item["volume_discounts"]
    item["active_volume_discounts"] = active_volume
    item["volume_tiers"] = priced_volume_tiers(active_volume, item["display_price"])
    item["volume_max_percent"] = max((tier["percent"] for tier in active_volume), default=0)
    item["tax_percent"] = PRODUCT_TAX_PERCENT
    item["tax_amount"] = product_tax(item["display_price"])
    item["display_price_with_tax"] = price_with_tax(item["display_price"])
    item["display_original_price_with_tax"] = price_with_tax(item["display_original_price"])
    discounted_tiers = [tier for tier in item["volume_tiers"] if tier.get("percent")]
    item["volume_from_price"] = min((tier["unit_price"] for tier in discounted_tiers), default=item["display_price"])
    item["volume_from_price_with_tax"] = min(
        (tier["unit_price_with_tax"] for tier in discounted_tiers),
        default=item["display_price_with_tax"],
    )
    item["shipping"] = normalize_product_shipping(item.get("shipping_json"))
    try:
        packing_weight = max(0.0, float(item.get("packing_weight") or 0))
    except (TypeError, ValueError):
        packing_weight = 0.0
    item["packing_weight"] = packing_weight
    item["ship_weight"] = weight + packing_weight
    item["product_type"] = item.get("product_type") or inferred_product_type(item.get("category"))
    item["main_categories"] = product_main_names(item)
    item["main_category"] = item["main_categories"][0]
    item["main_categories_label"] = " · ".join(item["main_categories"])
    item["sub_categories"] = product_sub_category_names(item)
    item["sub_category"] = item["sub_categories"][0] if item["sub_categories"] else ""
    item["sub_categories_label"] = " · ".join(item["sub_categories"])
    item["sub_category_2"] = (item.get("sub_category_2") or "").strip()
    item["sub_category_3"] = (item.get("sub_category_3") or "").strip()
    item["sub_category_4"] = (item.get("sub_category_4") or "").strip()
    item["genders"] = product_gender_groups(item)
    item["size_group"] = item["genders"][0] if item["genders"] else "Unisex"
    item["gender_label"] = " · ".join(
        label for value, label in PRODUCT_GENDERS if value in item["genders"]
    )
    item["condition"] = item.get("condition") or "new_with_tag"
    item["condition_label"] = CONDITION_LABELS.get(item["condition"], "New with tag")
    item["region_visibility"] = item.get("region_visibility") or "all"
    item["has_marketplace_links"] = bool(item["amazon_url"] or item["etsy_url"] or item["ebay_url"])
    item["product_tags"] = keywords_from_stored(item.get("product_tags"))
    item["product_hashtags"] = keywords_from_stored(item.get("product_hashtags"))
    item["tags_text"] = ", ".join(item["product_tags"])
    item["hashtags_text"] = ", ".join(item["product_hashtags"])
    try:
        item["likes"] = max(0, int(item.get("likes") or 0))
    except (TypeError, ValueError):
        item["likes"] = 0
    try:
        item["rating"] = max(0.0, min(5.0, float(item.get("rating") or 0)))
    except (TypeError, ValueError):
        item["rating"] = 0.0
    item["price_eur"] = round(original_price / EUR_TO_STORE, 2) if original_price else 0
    try:
        item["featured"] = 1 if int(item.get("featured") or 0) else 0
    except (TypeError, ValueError):
        item["featured"] = 0
    try:
        item["deal_of_week"] = 1 if int(item.get("deal_of_week") or 0) else 0
    except (TypeError, ValueError):
        item["deal_of_week"] = 0
    try:
        item["new_arrival"] = 1 if int(item.get("new_arrival") or 0) else 0
    except (TypeError, ValueError):
        item["new_arrival"] = 0
    try:
        item["is_draft"] = 1 if int(item.get("is_draft") or 0) else 0
    except (TypeError, ValueError):
        item["is_draft"] = 0
    item["stars"] = star_display(item["rating"])
    item["listed_by"] = (item.get("listed_by") or "admin").strip() or "admin"
    item["brand"] = (item.get("brand") or "").strip()
    item["fulfillment"] = "virtual" if (item.get("fulfillment") or "") == "virtual" else "physical"
    item["is_virtual"] = item["fulfillment"] == "virtual"
    return item


def star_display(rating):
    try:
        filled = int(round(float(rating or 0)))
    except (TypeError, ValueError):
        filled = 0
    filled = max(0, min(5, filled))
    return "★" * filled + "☆" * (5 - filled)


def liked_product_ids():
    ids = []
    for value in session.get("liked") or []:
        try:
            ids.append(int(value))
        except (TypeError, ValueError):
            continue
    return ids


def listing_images(listing):
    try:
        images = json.loads((listing or {}).get("images_json") or "[]")
    except (TypeError, json.JSONDecodeError, AttributeError):
        images = []
    if not isinstance(images, list):
        return []
    return [url for url in images if url]


def listing_view(row):
    item = dict(row) if not isinstance(row, dict) else dict(row)
    item["images"] = listing_images(item)
    item["status"] = item.get("status") or "pending"
    return item


def upsert_partner_image(application_id, slot, data, content_type="image/jpeg"):
    get_db().execute(
        """
        INSERT INTO partner_application_images (application_id, slot, content_type, bytes, byte_size)
        VALUES (?,?,?,?,?)
        ON CONFLICT (application_id, slot) DO UPDATE SET
            content_type=EXCLUDED.content_type,
            bytes=EXCLUDED.bytes,
            byte_size=EXCLUDED.byte_size
        """,
        (application_id, slot, content_type, data, len(data)),
    )


def save_partner_images(application_id):
    prepared = []
    for index in range(1, PRODUCT_IMAGE_SLOTS + 1):
        image = load_upload_image(request.files.get(f"image_{index}"))
        if image:
            prepared.append((index, image))
    if not prepared:
        raise ValueError("Please upload at least one product image.")
    encoded = encode_images_within_limit(prepared, 0, form_payload_bytes())
    for index, data in encoded:
        upsert_partner_image(application_id, index, data)


def partner_image_urls(application_id):
    rows = get_db().execute(
        "SELECT slot, byte_size FROM partner_application_images WHERE application_id=? ORDER BY slot",
        (application_id,),
    ).fetchall() or []
    return [f"/partner-image/{application_id}/{row['slot']}?v={row['byte_size']}" for row in rows]


def partner_application_view(row):
    item = dict(row) if not isinstance(row, dict) else dict(row)
    item["images"] = partner_image_urls(item["id"])
    item["status"] = item.get("status") or "pending"
    item["kind_label"] = "Sell on our website" if item.get("kind") == "seller" else "Dropshipper"
    return item


def parse_order_items(raw):
    if isinstance(raw, list):
        return raw
    if not raw:
        return []
    for loader in (json.loads, ast.literal_eval):
        try:
            data = loader(raw)
        except (TypeError, ValueError, SyntaxError, json.JSONDecodeError):
            continue
        if isinstance(data, list):
            return data
    return []


def listing_category_fields(category):
    name = (category or "").strip()
    for product_type, names in SUB_CATEGORIES.items():
        if name == product_type:
            return product_type, names[0]
        if name in names:
            return product_type, name
    return "Clothes", name or "Tops"


def approve_seller_listing(listing_id):
    db = get_db()
    listing = db.execute("SELECT * FROM listings WHERE id=?", (listing_id,)).fetchone()
    if not listing:
        raise ValueError("Listing not found.")
    if listing.get("status") == "approved" and listing.get("product_id"):
        return listing["product_id"]
    images = listing_images(listing)
    if not images:
        raise ValueError("This listing has no images to publish.")
    product_type, sub_category = listing_category_fields(listing["category"])
    sku = f"SELL-{listing_id}"
    if db.execute("SELECT id FROM products WHERE sku=?", (sku,)).fetchone():
        sku = f"SELL-{listing_id}-{int(datetime.utcnow().timestamp())}"
    store_price = round(max(0.01, float(listing["price"] or 0)) * 278, 2)
    color_rows = [{"name": "Default", "quantity": 1, "sizes": {"Standard": 1}}]
    size_rows = ["Standard"]
    cursor = db.execute(
        """
        INSERT INTO products (
            name,category,price,rating,reviews_count,likes,sku,image,sizes,colors,
            description,stock,active,colors_json,sizes_json,condition,main_category,
            sub_category,product_type,size_group,region_visibility,featured,deal_of_week,listed_by
        ) VALUES (?,?,?,0,0,0,?,?,?,?,?,1,1,?,?,?,?,?,?,?,?,0,0,?)
        RETURNING id
        """,
        (
            listing["title"][:100],
            sub_category,
            store_price,
            sku,
            images[0],
            "Standard",
            "Default",
            listing["description"][:3000],
            json.dumps(color_rows),
            json.dumps(size_rows),
            "used",
            "Unisex",
            sub_category,
            product_type,
            "Unisex",
            "all",
            "admin",
        ),
    )
    product_id = cursor.fetchone()["id"]
    dest = os.path.join(UPLOAD_ROOT, sku)
    os.makedirs(dest, exist_ok=True)
    for index, url in enumerate(images[:PRODUCT_IMAGE_SLOTS], start=1):
        src = os.path.join(BASE_DIR, str(url).lstrip("/"))
        if not os.path.exists(src):
            continue
        target = "main.jpg" if index == 1 else f"{index}.jpg"
        shutil.copy2(src, os.path.join(dest, target))
        with open(os.path.join(dest, target), "rb") as handle:
            upsert_product_image(product_id, index, handle.read())
    first = db.execute(
        "SELECT byte_size FROM product_images WHERE product_id=? AND slot=1",
        (product_id,),
    ).fetchone()
    if first:
        db.execute(
            "UPDATE products SET image=? WHERE id=?",
            (product_image_url(product_id, 1, first["byte_size"]), product_id),
        )
    db.execute(
        "UPDATE listings SET status=?, reviewed_at=?, product_id=? WHERE id=?",
        ("approved", datetime.utcnow().isoformat(), product_id, listing_id),
    )
    db.commit()
    invalidate_shop_nav_cache()
    return product_id


def fetch_product(product_id):
    row = get_db().execute("SELECT * FROM products WHERE id=? AND active=1", (product_id,)).fetchone()
    if not row:
        abort(404)
    item = product(row)
    if not item_visible_in_region(item):
        abort(404)
    return item


def inferred_product_type(category):
    name = category or ""
    for product_type, options in SUB_CATEGORIES.items():
        if name == product_type or name in options:
            return product_type
    if name == "Shoes":
        return "Shoes"
    if name in {"Wallets", "Purses", "Belts"}:
        return "Accessories"
    return "Clothes"


def item_visible_in_region(item):
    visibility = item.get("region_visibility") or "all"
    if visibility == "all":
        return True
    allowed = REGION_VISIBLE_ZONES.get(visibility) or set()
    return customer_zone_name() in allowed


def product_gallery_map(product_ids):
    ids = []
    for value in product_ids:
        try:
            ids.append(int(value))
        except (TypeError, ValueError):
            continue
    if not ids:
        return {}
    rows = get_db().execute(
        f"SELECT product_id, slot, byte_size FROM product_images WHERE product_id IN ({','.join('?' for _ in ids)}) ORDER BY slot",
        tuple(ids),
    ).fetchall() or []
    grouped = {}
    for row in rows:
        grouped.setdefault(row["product_id"], []).append(row)
    return grouped


def visible_catalog(rows):
    raw_rows = list(rows or [])
    gallery_map = product_gallery_map(row["id"] for row in raw_rows)
    return [item for item in (product(row, gallery_map=gallery_map) for row in raw_rows) if item_visible_in_region(item)]


def load_nav_catalog():
    sql = f"SELECT {NAV_PRODUCT_COLUMNS} FROM products WHERE active=1"
    try:
        rows = get_db().execute(sql).fetchall()
    except InFailedSqlTransaction:
        rollback_db()
        rows = get_db().execute(sql).fetchall()
    return [dict(row) for row in rows if item_visible_in_region(row)]


def product_main_names(item):
    names = []
    raw = (item or {}).get("main_categories")
    if isinstance(raw, list):
        names = [str(name).strip() for name in raw if str(name).strip()]
    elif isinstance(raw, str) and raw.strip():
        try:
            parsed = json.loads(raw)
            if isinstance(parsed, list):
                names = [str(name).strip() for name in parsed if str(name).strip()]
        except json.JSONDecodeError:
            names = []
    primary = str((item or {}).get("main_category") or "").strip()
    if primary and primary not in names:
        names.insert(0, primary)
    unique = []
    for name in names:
        if name not in unique:
            unique.append(name)
    return unique or ["Unisex"]


def product_gender_groups(item):
    names = []
    raw = (item or {}).get("genders")
    if isinstance(raw, list):
        names = [str(name).strip() for name in raw if str(name).strip() in GENDER_VALUES]
    elif isinstance(raw, str) and raw.strip():
        try:
            parsed = json.loads(raw)
            if isinstance(parsed, list):
                names = [str(name).strip() for name in parsed if str(name).strip() in GENDER_VALUES]
        except json.JSONDecodeError:
            names = []
    primary = str((item or {}).get("size_group") or "").strip()
    if primary in GENDER_VALUES and primary not in names:
        names.insert(0, primary)
    unique = []
    for name in names:
        if name not in unique:
            unique.append(name)
    return unique or ["Unisex"]


def parse_gender_offers(raw):
    if isinstance(raw, dict):
        data = raw
    else:
        try:
            data = json.loads(raw or "{}")
        except (TypeError, json.JSONDecodeError):
            data = {}
    if not isinstance(data, dict):
        return {}
    offers = {}
    for key, value in data.items():
        if key not in GENDER_VALUES or not isinstance(value, dict):
            continue
        colors = [entry for entry in (value.get("colors") or []) if isinstance(entry, dict)]
        sizes = [str(size) for size in (value.get("sizes") or []) if str(size).strip()]
        try:
            price = float(value.get("price") or 0)
        except (TypeError, ValueError):
            price = 0
        try:
            pakistan_price = max(0.0, float(value.get("pakistan_price") or 0))
        except (TypeError, ValueError):
            pakistan_price = 0
        try:
            virtual_stock = max(0, int(value.get("virtual_stock") or 0))
        except (TypeError, ValueError):
            virtual_stock = 0
        entry = {
            "price": price,
            "pakistan_price": pakistan_price,
            "sizes": sizes,
            "colors": colors,
            "virtual_stock": virtual_stock,
        }
        if "volume_discounts" in value:
            entry["volume_discounts"] = parse_volume_discounts_stored(value.get("volume_discounts"))
        if "pakistan_volume_discounts" in value:
            entry["pakistan_volume_discounts"] = parse_volume_discounts_stored(value.get("pakistan_volume_discounts"))
        if "volume_enabled" in value:
            entry["volume_enabled"] = bool(value.get("volume_enabled"))
        offers[key] = entry
    return offers


def volume_tiers_have_discount(tiers):
    return any(float(tier.get("percent") or 0) > 0 for tier in (tiers or []))


def offer_volume_enabled(offer, volume=None, pakistan_volume=None):
    if isinstance(offer, dict) and "volume_enabled" in offer:
        return bool(offer.get("volume_enabled"))
    return volume_tiers_have_discount(volume) or volume_tiers_have_discount(pakistan_volume)


def apply_stored_offer(item, offer):
    item["price"] = float(offer.get("price") or 0)
    item["pakistan_price"] = float(offer.get("pakistan_price") or 0)
    colors = [entry for entry in (offer.get("colors") or []) if isinstance(entry, dict)]
    sizes = [str(size) for size in (offer.get("sizes") or []) if str(size).strip()] or ["Standard"]
    for entry in colors:
        if not isinstance(entry.get("sizes"), dict):
            quantity = max(int(entry.get("quantity") or 0), 0)
            entry["sizes"] = {sizes[0]: quantity}
        entry["quantity"] = sum(max(int(value or 0), 0) for value in entry["sizes"].values())
    if colors:
        item["color_rows"] = colors
        item["colors"] = [entry.get("name") or "Default" for entry in colors]
        item["stock"] = sum(int(entry.get("quantity") or 0) for entry in colors)
    item["size_rows"] = sizes
    item["sizes"] = sizes
    fallback_volume = item.get("product_volume_discounts")
    if fallback_volume is None:
        fallback_volume = parse_volume_discounts_stored(item.get("volume_discounts"))
    fallback_pakistan = item.get("product_pakistan_volume_discounts")
    if fallback_pakistan is None:
        fallback_pakistan = parse_volume_discounts_stored(item.get("pakistan_volume_discounts"))
    if "volume_enabled" in offer and not offer.get("volume_enabled"):
        item["volume_discounts"] = []
        item["pakistan_volume_discounts"] = []
    else:
        if "volume_discounts" in offer:
            item["volume_discounts"] = list(offer.get("volume_discounts") or [])
        else:
            item["volume_discounts"] = list(fallback_volume or [])
        if "pakistan_volume_discounts" in offer:
            item["pakistan_volume_discounts"] = list(offer.get("pakistan_volume_discounts") or [])
        else:
            item["pakistan_volume_discounts"] = list(fallback_pakistan or [])


def refresh_display_prices(item):
    original_price = float(item.get("price") or 0)
    try:
        pakistan_original = max(0.0, float(item.get("pakistan_price") or 0))
    except (TypeError, ValueError):
        pakistan_original = 0.0
    item["original_price"] = original_price
    item["price"] = original_price
    item["price_eur"] = round(original_price / EUR_TO_STORE, 2)
    item["pakistan_original_price"] = pakistan_original
    item["pakistan_price"] = pakistan_original
    volume = parse_volume_discounts_stored(item.get("volume_discounts"))
    item["volume_discounts"] = volume
    pakistan_volume = parse_volume_discounts_stored(item.get("pakistan_volume_discounts"))
    item["pakistan_volume_discounts"] = pakistan_volume
    if pakistan_customer() and pakistan_original > 0:
        item["display_original_price"] = pakistan_original
        item["display_price"] = pakistan_original
        active = pakistan_volume or volume
    else:
        item["display_original_price"] = original_price
        item["display_price"] = original_price
        active = volume
    item["active_volume_discounts"] = active
    item["volume_tiers"] = priced_volume_tiers(active, item["display_price"])
    item["volume_max_percent"] = max((tier["percent"] for tier in active), default=0)
    item["tax_amount"] = product_tax(item["display_price"])
    item["display_price_with_tax"] = price_with_tax(item["display_price"])
    item["display_original_price_with_tax"] = price_with_tax(item["display_original_price"])


def choose_offer_gender(item):
    offers = item.get("gender_offers") or {}
    if not offers:
        return ""
    group = ""
    if has_request_context():
        who = selected_audience_key()
        group = next((audience_group for key, _label, audience_group in AUDIENCES if key == who), "")
    if group in offers:
        return group
    for name in product_gender_groups(item):
        if name in offers:
            return name
    return next(iter(offers))


def split_cart_key(cart_key):
    parts = str(cart_key).split(":")
    item_id = parts[0] if parts else ""
    selected_size = parts[1] if len(parts) > 1 else "Standard"
    gender = ""
    if len(parts) >= 4 and parts[-1] in GENDER_VALUES:
        gender = parts[-1]
        selected_color = ":".join(parts[2:-1]) or "Default"
    else:
        selected_color = ":".join(parts[2:]) if len(parts) > 2 else "Default"
    return item_id, selected_size, selected_color, gender


def use_cart_offer(item, gender):
    offers = item.get("gender_offers") or {}
    if not gender or gender not in offers or gender == item.get("offer_gender"):
        return
    apply_stored_offer(item, offers[gender])
    item["offer_gender"] = gender
    item["offer_label"] = GENDER_LABELS.get(gender, "")
    refresh_display_prices(item)


def gender_offer_slots(item):
    stored = {}
    selected = []
    product_type = None
    is_virtual = False
    product_volume = None
    product_pakistan_volume = None
    if item:
        raw = item.get("gender_offers")
        stored = raw if isinstance(raw, dict) else parse_gender_offers(raw)
        selected = item.get("genders") if isinstance(item.get("genders"), list) else product_gender_groups(item)
        product_type = item.get("product_type")
        is_virtual = bool(item.get("is_virtual"))
        product_volume = item.get("product_volume_discounts")
        if product_volume is None:
            product_volume = parse_volume_discounts_stored(item.get("volume_discounts"))
        product_pakistan_volume = item.get("product_pakistan_volume_discounts")
        if product_pakistan_volume is None:
            product_pakistan_volume = parse_volume_discounts_stored(item.get("pakistan_volume_discounts"))
    slots = []
    for group, label in PRODUCT_GENDERS:
        offer = stored.get(group)
        if offer is None and item and group in selected and not stored:
            sizes = [] if is_virtual else list(item.get("size_rows") or [])
            colors = [] if is_virtual else list(item.get("color_rows") or [])
            price = float(item.get("original_price") or item.get("price") or 0)
            pakistan = float(item.get("pakistan_original_price") or 0)
            virtual_stock = int(item.get("stock") or 0) if is_virtual else 0
            volume = product_volume
            pakistan_volume = product_pakistan_volume
        elif offer:
            sizes = [] if is_virtual else [size for size in offer.get("sizes") or [] if size != VIRTUAL_SIZE]
            colors = [] if is_virtual else list(offer.get("colors") or [])
            price = float(offer.get("price") or 0)
            pakistan = float(offer.get("pakistan_price") or 0)
            virtual_stock = int(offer.get("virtual_stock") or 0)
            if is_virtual and not virtual_stock and offer.get("colors"):
                virtual_stock = int(offer["colors"][0].get("quantity") or 0)
            volume = offer["volume_discounts"] if "volume_discounts" in offer else product_volume
            pakistan_volume = (
                offer["pakistan_volume_discounts"] if "pakistan_volume_discounts" in offer else product_pakistan_volume
            )
        else:
            sizes, colors, price, pakistan, virtual_stock = [], [], 0, 0, 0
            volume, pakistan_volume = None, None
        sizes = [size for size in sizes if size != VIRTUAL_SIZE]
        extras = [size for size in sizes if size not in catalog_sizes_for(product_type or "Clothes")]
        volume_enabled = offer_volume_enabled(offer, volume, pakistan_volume)
        slots.append(
            {
                "group": group,
                "label": label,
                "prefix": f"g{group}_",
                "price_eur": round(price / EUR_TO_STORE, 2) if price else "",
                "pakistan_price": pakistan if pakistan else "",
                "virtual_stock": virtual_stock if virtual_stock else "",
                "size_slots_by_type": size_slots_by_type(sizes, product_type),
                "extra_sizes": extras,
                "custom_sizes": ", ".join(extras),
                "color_slots": empty_color_slots(colors, extras),
                "selected_colors": [
                    str(entry.get("name") or "").strip()
                    for entry in (colors or [])
                    if str(entry.get("name") or "").strip()
                ],
                "volume_enabled": volume_enabled,
                "volume_slots": volume_form_slots(volume if volume_enabled else None),
                "pakistan_volume_slots": volume_form_slots(pakistan_volume if volume_enabled else None),
                "open": bool(item and group in selected),
            }
        )
    return slots


def parse_gender_offer_form(gender, is_virtual):
    prefix = f"g{gender}_"
    try:
        price_eur = float(request.form.get(f"{prefix}price", 0) or 0)
    except ValueError:
        price_eur = 0
    try:
        pakistan_price = max(0.0, float(request.form.get(f"{prefix}pakistan_price", 0) or 0))
    except ValueError:
        pakistan_price = 0
    price = round(max(0.0, price_eur) * EUR_TO_STORE, 2)
    volume_enabled = bool(request.form.get(f"{prefix}volume_enabled"))
    if volume_enabled:
        volume_discounts = parse_volume_discounts_form(f"g{gender}_volume")
        pakistan_volume_discounts = parse_volume_discounts_form(f"g{gender}_pk_volume")
    else:
        volume_discounts = []
        pakistan_volume_discounts = []
    if is_virtual:
        try:
            quantity = max(0, int(float(request.form.get(f"{prefix}virtual_stock", 0) or 0)))
        except ValueError:
            quantity = 0
        return {
            "price": price,
            "pakistan_price": pakistan_price,
            "sizes": [VIRTUAL_SIZE],
            "colors": [{"name": VIRTUAL_COLOR, "quantity": quantity, "sizes": {VIRTUAL_SIZE: quantity}}],
            "virtual_stock": quantity,
            "volume_enabled": volume_enabled,
            "volume_discounts": volume_discounts,
            "pakistan_volume_discounts": pakistan_volume_discounts,
        }
    return {
        "price": price,
        "pakistan_price": pakistan_price,
        "sizes": parse_size_form(prefix),
        "colors": parse_color_form(prefix),
        "virtual_stock": 0,
        "volume_enabled": volume_enabled,
        "volume_discounts": volume_discounts,
        "pakistan_volume_discounts": pakistan_volume_discounts,
    }


def product_sub_category_names(item):
    names = []
    raw = (item or {}).get("sub_categories")
    if isinstance(raw, list):
        names = [str(name).strip() for name in raw if str(name).strip()]
    elif isinstance(raw, str) and raw.strip():
        try:
            parsed = json.loads(raw)
            if isinstance(parsed, list):
                names = [str(name).strip() for name in parsed if str(name).strip()]
        except json.JSONDecodeError:
            names = []
    primary = str((item or {}).get("sub_category") or (item or {}).get("category") or "").strip()
    if primary and primary not in names:
        names.insert(0, primary)
    unique = []
    for name in names:
        if name not in unique:
            unique.append(name)
    return unique


def product_sub_category(item):
    names = product_sub_category_names(item)
    return names[0] if names else ""


def product_sub_category_2(item):
    return (item.get("sub_category_2") or "").strip()


def product_sub_category_3(item):
    return (item.get("sub_category_3") or "").strip()


def product_sub_category_4(item):
    return (item.get("sub_category_4") or "").strip()


def category_path(item):
    parts = [" / ".join(product_main_names(item))]
    subs = product_sub_category_names(item)
    if subs:
        parts.append(" / ".join(subs))
    for part in (
        product_sub_category_2(item),
        product_sub_category_3(item),
        product_sub_category_4(item),
    ):
        if part:
            parts.append(part)
    return " · ".join(parts)


def shop_category_tree(items=None):
    if items is None:
        zone = customer_zone_name()
        now = time.time()
        with _shop_nav_lock:
            cached = _shop_nav_cache.get(zone)
            if cached and now - cached[0] < SHOP_NAV_TTL:
                return cached[1]
        tree = build_shop_category_tree(load_nav_catalog())
        with _shop_nav_lock:
            _shop_nav_cache[zone] = (now, tree)
        return tree
    return build_shop_category_tree(items)


def build_shop_category_tree(items):
    mains = load_main_categories()
    grouped = {name: [] for name in mains}
    sub2_map = {name: {} for name in mains}
    sub3_map = {name: {} for name in mains}
    sub4_map = {name: {} for name in mains}
    fallback = mains[0] if mains else "Unisex"
    has_products = {name: False for name in mains}
    for item in items:
        item_mains = [name for name in product_main_names(item) if name in grouped] or ([fallback] if fallback in grouped else [])
        subs = [name for name in product_sub_category_names(item) if name]
        sub = subs[0] if subs else ""
        sub2 = product_sub_category_2(item)
        sub3 = product_sub_category_3(item)
        sub4 = product_sub_category_4(item)
        for main in item_mains:
            has_products[main] = True
            for sub_name in subs:
                if sub_name not in grouped[main]:
                    grouped[main].append(sub_name)
            if sub and sub2:
                sub2_map[main].setdefault(sub, [])
                if sub2 not in sub2_map[main][sub]:
                    sub2_map[main][sub].append(sub2)
            if sub and sub2 and sub3:
                sub3_map[main].setdefault(sub, {}).setdefault(sub2, [])
                if sub3 not in sub3_map[main][sub][sub2]:
                    sub3_map[main][sub][sub2].append(sub3)
            if sub and sub2 and sub3 and sub4:
                sub4_map[main].setdefault(sub, {}).setdefault(sub2, {}).setdefault(sub3, [])
                if sub4 not in sub4_map[main][sub][sub2][sub3]:
                    sub4_map[main][sub][sub2][sub3].append(sub4)
    return [
        {
            "name": name,
            "subs": sorted(grouped[name]),
            "sub2_map": {key: sorted(values) for key, values in sub2_map[name].items()},
            "sub3_map": {
                sub: {sub2: sorted(values) for sub2, values in groups.items()}
                for sub, groups in sub3_map[name].items()
            },
            "sub4_map": {
                sub: {
                    sub2: {sub3: sorted(values) for sub3, values in sub3_groups.items()}
                    for sub2, sub3_groups in groups.items()
                }
                for sub, groups in sub4_map[name].items()
            },
        }
        for name in mains
        if has_products.get(name)
    ]


def matches_shop_filter(item, main="", sub="", sub2="", sub3="", sub4="", category=""):
    item_mains = product_main_names(item)
    item_subs = product_sub_category_names(item)
    item_sub = item_subs[0] if item_subs else ""
    item_sub2 = product_sub_category_2(item)
    item_sub3 = product_sub_category_3(item)
    item_sub4 = product_sub_category_4(item)
    if main and main not in item_mains:
        return False
    if sub and sub not in item_subs:
        return False
    if sub2 and ((sub and sub != item_sub) or item_sub2 != sub2):
        return False
    if sub3 and ((sub and sub != item_sub) or item_sub3 != sub3):
        return False
    if sub4 and ((sub and sub != item_sub) or item_sub4 != sub4):
        return False
    if category and category != "All":
        return category in {
            item.get("category"),
            *item_subs,
            item_sub2,
            item_sub3,
            item_sub4,
            item.get("product_type"),
            *item_mains,
        }
    return True


def client_ip():
    forwarded = (request.headers.get("X-Forwarded-For") or "").split(",")[0].strip()
    return forwarded or request.headers.get("X-Real-IP") or request.remote_addr or ""


def is_local_ip(ip):
    return (
        not ip
        or ip in {"127.0.0.1", "::1", "localhost"}
        or ip.startswith("127.")
        or ip.startswith("192.168.")
        or ip.startswith("10.")
        or ip.startswith("172.16.")
    )


def lookup_ip_country():
    cached = session.get("ip_country")
    if cached is not None:
        return cached
    cf_country = (request.headers.get("CF-IPCountry") or "").upper()
    if cf_country and cf_country not in {"XX", "T1"}:
        session["ip_country"] = cf_country
        return cf_country
    ip = client_ip()
    if is_local_ip(ip):
        session["ip_country"] = ""
        return ""
    try:
        url = f"http://ip-api.com/json/{ip}?fields=status,countryCode"
        with urllib.request.urlopen(url, timeout=1.5) as response:
            data = json.loads(response.read().decode("utf-8"))
        session["ip_country"] = (data.get("countryCode") or "").upper() if data.get("status") == "success" else ""
    except (urllib.error.URLError, TimeoutError, ValueError, json.JSONDecodeError, OSError):
        session["ip_country"] = ""
    return session.get("ip_country") or ""


def zone_from_address(text):
    blob = f" {(text or '').lower()} "
    for hint, zone in ADDRESS_ZONE_HINTS:
        if f" {hint} " in blob or blob.strip().endswith(hint) or blob.strip().startswith(hint):
            return zone
        if hint in blob:
            return zone
    return ""


def zone_from_accept_language():
    header = request.headers.get("Accept-Language") or ""
    for part in header.split(","):
        code = part.split(";")[0].strip().lower()
        if code.startswith("ur") or code.endswith("-pk"):
            return "Pakistan"
        if code.startswith("de") or code.endswith("-de"):
            return "Germany"
        if code.endswith("-us") or code.endswith("-ca"):
            return "Canada/USA"
    language = language_from_accept_header(header)
    return LANGUAGE_TO_ZONE.get(language) or ""


def apply_region(zone, set_language=False):
    if zone not in ZONE_NAMES:
        return
    session["region"] = zone
    session["currency"] = ZONE_CURRENCY.get(zone, session.get("currency", "EUR"))
    if set_language:
        session["language"] = ZONE_DEFAULT_LANGUAGE.get(zone) or session.get("language") or "en"
    elif zone == "Pakistan" and session.get("language") not in LANGUAGES:
        session["language"] = "en"
    if zone == "Pakistan" and not session.get("locale_chosen"):
        session["language"] = "en"


def apply_country_locale(country_code):
    code = (country_code or "").upper()
    if not code:
        return False
    zone = COUNTRY_CODE_TO_ZONE.get(code)
    language = language_for_country(code)
    currency = currency_for_country(code, ZONE_CURRENCY.get(zone, "EUR") if zone else "EUR")
    if zone:
        apply_region(zone)
    if language in LANGUAGES:
        session["language"] = language
    if currency in CURRENCIES:
        session["currency"] = currency
    return bool(zone or language)


def auto_localize_visitor():
    if not session.get("locale_chosen") and session.get("region") == "Pakistan":
        session["language"] = "en"
    if session.get("locale_chosen") or session.get("locale_applied"):
        return
    if apply_country_locale(lookup_ip_country()):
        session["locale_applied"] = True
        return
    language = language_from_accept_header(request.headers.get("Accept-Language") or "")
    if language in LANGUAGES:
        session["language"] = language
        zone = LANGUAGE_TO_ZONE.get(language)
        if zone:
            apply_region(zone)
            if zone == "Pakistan" and not session.get("locale_chosen"):
                session["language"] = "en"
        elif language == "en":
            apply_region("Canada/USA" if session.get("currency") == "USD" else "Europe")
        session["locale_applied"] = True
        return
    session["locale_applied"] = True


def customer_location():
    if not has_request_context():
        return {"zone": "Europe", "source": "default"}
    if getattr(g, "customer_location", None):
        return g.customer_location
    address_zone = zone_from_address(request.form.get("address", ""))
    profile_zone = ""
    user = current_user()
    if user:
        profile_zone = (user.get("country") or "").strip()
        if profile_zone not in ZONE_NAMES:
            profile_zone = ""
    explicit = (session.get("region") or "").strip()
    if explicit not in ZONE_NAMES:
        explicit = ""
    ip_code = lookup_ip_country()
    ip_zone = COUNTRY_CODE_TO_ZONE.get(ip_code, "")
    language_zone = LANGUAGE_TO_ZONE.get(session.get("language"), "")
    accept_zone = zone_from_accept_language()
    currency_zone = CURRENCY_TO_ZONE.get(session.get("currency"), "")
    if session.get("language") == "de" and session.get("currency") == "EUR":
        currency_zone = "Germany"
    if address_zone:
        result = {"zone": address_zone, "source": "delivery address"}
    elif explicit:
        result = {"zone": explicit, "source": "your selected region"}
    elif profile_zone:
        result = {"zone": profile_zone, "source": "your profile"}
    elif ip_zone:
        result = {"zone": ip_zone, "source": "your IP location"}
    elif accept_zone:
        result = {"zone": accept_zone, "source": "browser language"}
    elif language_zone:
        result = {"zone": language_zone, "source": "site language"}
    elif currency_zone:
        result = {"zone": currency_zone, "source": "currency"}
    else:
        result = {"zone": "Europe", "source": "default"}
    g.customer_location = result
    return result


def customer_zone_name():
    return customer_location()["zone"]


def pakistan_customer():
    return customer_zone_name() == "Pakistan"


def category_names():
    return [row["name"] for row in get_db().execute("SELECT name FROM categories ORDER BY name").fetchall()]


def load_brands():
    if "brands" not in g:
        try:
            rows = get_db().execute("SELECT name FROM brands ORDER BY name").fetchall()
            g.brands = [row["name"] for row in rows]
        except Exception:
            rollback_db()
            g.brands = []
    return g.brands


def ensure_brand_name(name):
    brand = (name or "").strip()[:80]
    if not brand:
        return ""
    existing = {entry.lower(): entry for entry in load_brands()}
    if brand.lower() in existing:
        return existing[brand.lower()]
    try:
        get_db().execute("INSERT INTO brands (name) VALUES (?)", (brand,))
        get_db().commit()
    except IntegrityError:
        rollback_db()
    if "brands" in g:
        del g.brands
    return brand


def load_main_categories():
    if "main_categories" not in g:
        try:
            rows = get_db().execute("SELECT name FROM main_categories ORDER BY id").fetchall()
            names = [row["name"] for row in rows]
            g.main_categories = names or list(MAIN_CATEGORIES)
        except Exception:
            get_db().rollback()
            g.main_categories = list(MAIN_CATEGORIES)
    return g.main_categories


def load_sub_categories():
    if "sub_categories" not in g:
        mains = load_main_categories()
        grouped = {name: [] for name in mains}
        try:
            rows = get_db().execute("SELECT name, main_category FROM sub_categories ORDER BY id").fetchall()
            for row in rows:
                grouped.setdefault(row["main_category"], []).append(row["name"])
        except Exception:
            get_db().rollback()
            rows = []
        if not any(grouped.values()):
            names = default_sub_category_names()
            grouped = {name: list(names) for name in mains}
        g.sub_categories = grouped
    return g.sub_categories


def load_sub_categories_2():
    if "sub_categories_2" not in g:
        grouped = {}
        try:
            rows = get_db().execute(
                "SELECT name, main_category, sub_category FROM sub_categories_2 ORDER BY id"
            ).fetchall()
            for row in rows:
                grouped.setdefault(row["main_category"], {}).setdefault(row["sub_category"], []).append(row["name"])
        except Exception:
            get_db().rollback()
        g.sub_categories_2 = grouped
    return g.sub_categories_2


def load_sub_categories_3():
    if "sub_categories_3" not in g:
        grouped = {}
        try:
            rows = get_db().execute(
                "SELECT name, main_category, sub_category, sub_category_2 FROM sub_categories_3 ORDER BY id"
            ).fetchall()
            for row in rows:
                grouped.setdefault(row["main_category"], {}).setdefault(row["sub_category"], {}).setdefault(
                    row["sub_category_2"], []
                ).append(row["name"])
        except Exception:
            get_db().rollback()
        g.sub_categories_3 = grouped
    return g.sub_categories_3


def load_sub_categories_4():
    if "sub_categories_4" not in g:
        grouped = {}
        try:
            rows = get_db().execute(
                """
                SELECT name, main_category, sub_category, sub_category_2, sub_category_3
                FROM sub_categories_4 ORDER BY id
                """
            ).fetchall()
            for row in rows:
                grouped.setdefault(row["main_category"], {}).setdefault(row["sub_category"], {}).setdefault(
                    row["sub_category_2"], {}
                ).setdefault(row["sub_category_3"], []).append(row["name"])
        except Exception:
            get_db().rollback()
        g.sub_categories_4 = grouped
    return g.sub_categories_4


def staff_home():
    if session.get("is_admin"):
        return url_for("admin_dashboard")
    if session.get("is_pl"):
        return url_for("pl_dashboard")
    return url_for("home")


def staff_product_image_delete_url(product_id, slot):
    if not product_id:
        return ""
    if session.get("is_admin"):
        return url_for("admin_product_image_delete", product_id=int(product_id), slot=int(slot))
    if session.get("is_pl"):
        return url_for("pl_product_image_delete", product_id=int(product_id), slot=int(slot))
    return ""


def remove_saved_product_image(product_id, slot, sku=None):
    if slot < 1 or slot > PRODUCT_IMAGE_SLOTS:
        raise ValueError("Choose a valid image to delete.")
    delete_product_image_slot(product_id, slot, sku)
    refresh_product_cover_image(product_id)
    get_db().commit()


def product_image_slots(item=None):
    item = item or {}
    product_id = item.get("id")
    sku = item.get("sku") or ""
    stored = {row["slot"]: row["byte_size"] for row in stored_product_images(product_id)}
    slots = []
    for index in range(1, PRODUCT_IMAGE_SLOTS + 1):
        url = ""
        if product_id and index in stored:
            url = product_image_url(product_id, index, stored[index])
        else:
            filename = product_image_name(index)
            path = os.path.join(UPLOAD_ROOT, sku, filename) if sku else ""
            if sku and os.path.exists(path):
                url = f"/static/images/{sku}/{filename}?v={int(os.path.getmtime(path))}"
        slots.append(
            {
                "index": index,
                "field": "main_image" if index == 1 else f"image_{index}",
                "label": "Image 1 (main)" if index == 1 else f"Image {index}",
                "url": url,
                "delete_url": staff_product_image_delete_url(product_id, index) if url and product_id else "",
            }
        )
    return slots


def extra_sizes_of(item=None):
    if not item:
        return []
    catalog = set(catalog_sizes_for(item.get("product_type") or "Clothes"))
    extras = []
    for size in item.get("size_rows") or []:
        if size not in catalog and size not in extras:
            extras.append(size)
    return extras


def empty_color_slots(existing=None, extra_sizes=None):
    existing = existing or []
    extra_sizes = extra_sizes or []
    all_sizes = list(ALL_CATALOG_SIZES)
    for size in extra_sizes:
        if size not in all_sizes:
            all_sizes.append(size)
    slots = [{"name": "", "sizes": {size: "" for size in all_sizes}} for _ in range(10)]
    for index, entry in enumerate(existing[:10]):
        slots[index] = {
            "name": entry.get("name", ""),
            "sizes": {size: entry.get("sizes", {}).get(size, "") for size in all_sizes},
        }
    return slots


def empty_size_slots(existing=None, product_type="Clothes", include_extras=False):
    existing = existing or []
    catalog = catalog_sizes_for(product_type)
    slots = [{"name": size, "selected": size in existing, "extra": False} for size in catalog]
    if include_extras:
        for size in existing:
            if size not in catalog:
                slots.append({"name": size, "selected": True, "extra": True})
    return slots


def size_slots_by_type(existing=None, product_type=None):
    existing = existing or []
    return {
        type_name: empty_size_slots(existing, type_name, include_extras=(type_name == product_type))
        for type_name in PRODUCT_TYPES
    }


def default_product_shipping():
    return {
        zone["key"]: {
            "name": zone["name"],
            "unit": zone["unit"],
            "under": zone["under"],
            "over": zone["over"],
            "express_under": zone["express_under"],
            "express_over": zone["express_over"],
        }
        for zone in DEFAULT_SHIPPING_ZONES
    }


def normalize_product_shipping(raw):
    if isinstance(raw, str):
        try:
            raw = json.loads(raw or "{}")
        except json.JSONDecodeError:
            raw = {}
    raw = raw or {}
    defaults = default_product_shipping()
    shipping = {}
    for zone in DEFAULT_SHIPPING_ZONES:
        entry = raw.get(zone["key"]) or raw.get(zone["name"]) or {}
        fallback = defaults[zone["key"]]
        values = {}
        for field in ("under", "over", "express_under", "express_over"):
            try:
                values[field] = max(0.0, float(entry.get(field, fallback[field])))
            except (TypeError, ValueError):
                values[field] = fallback[field]
        shipping[zone["key"]] = {
            "name": zone["name"],
            "key": zone["key"],
            "unit": zone["unit"],
            **values,
            "under_label": shipping_label(values["under"], zone["unit"]),
            "over_label": shipping_label(values["over"], zone["unit"]),
            "express_under_label": shipping_label(values["express_under"], zone["unit"]),
            "express_over_label": shipping_label(values["express_over"], zone["unit"]),
            "under_store": store_shipping_amount(values["under"], zone["unit"]),
            "over_store": store_shipping_amount(values["over"], zone["unit"]),
            "express_under_store": store_shipping_amount(values["express_under"], zone["unit"]),
            "express_over_store": store_shipping_amount(values["express_over"], zone["unit"]),
        }
    return shipping


def product_shipping_slots(existing=None):
    return list(normalize_product_shipping(existing).values())


def parse_product_shipping_form():
    shipping = {}
    for zone in DEFAULT_SHIPPING_ZONES:
        values = {}
        for field in ("under", "over", "express_under", "express_over"):
            try:
                values[field] = max(0.0, float(request.form.get(f"ship_{field}_{zone['key']}", 0) or 0))
            except ValueError:
                values[field] = 0
        shipping[zone["key"]] = {"name": zone["name"], "unit": zone["unit"], **values}
    return shipping


def blank_product_shipping():
    return {
        zone["key"]: {
            "name": zone["name"],
            "unit": zone["unit"],
            "under": 0,
            "over": 0,
            "express_under": 0,
            "express_over": 0,
        }
        for zone in DEFAULT_SHIPPING_ZONES
    }


@app.route("/")
def home():
    db = get_db()
    products = visible_catalog(
        db.execute(
            f"SELECT {SHOP_PRODUCT_COLUMNS} FROM products WHERE active=1 AND COALESCE(is_draft,0)=0 ORDER BY id DESC"
        ).fetchall()
    )
    flagged_deals = [item for item in products if item.get("deal_of_week")]
    deal = flagged_deals[0] if flagged_deals else next((item for item in products if item["product_type"] == "Shoes"), products[0] if products else None)
    featured = [item for item in products if item.get("featured")] or products[:8]
    new_arrivals = [item for item in products if item.get("new_arrival")][:8]
    testimonials = db.execute(
        """
        SELECT reviews.name, reviews.rating, reviews.body, products.name AS product_name
        FROM reviews JOIN products ON products.id=reviews.product_id
        ORDER BY reviews.id DESC LIMIT 3
        """
    ).fetchall()
    faqs = db.execute("SELECT * FROM faqs ORDER BY sort_order, id").fetchall()
    return render_template(
        "home.html",
        products=featured,
        new_arrivals=new_arrivals,
        deal=deal,
        testimonials=testimonials,
        faqs=faqs,
    )


def product_in_stock_sizes(item):
    names = []
    for color in item.get("color_rows") or []:
        sizes = color.get("sizes") if isinstance(color.get("sizes"), dict) else {}
        for size, quantity in sizes.items():
            try:
                qty = int(quantity or 0)
            except (TypeError, ValueError):
                qty = 0
            label = str(size).strip()
            if qty > 0 and label and label not in names:
                names.append(label)
    for size in item.get("sizes") or []:
        label = str(size).strip()
        if label and label not in names:
            names.append(label)
    return names


def is_specialty_size(name):
    text = str(name or "").upper().replace(" ", "")
    if any(token in text for token in ("3XL", "4XL", "5XL", "6XL", "7XL", "XXXL")):
        return True
    if "CM" in text:
        return True
    return text.endswith("Y") and any(char.isdigit() for char in text)


def product_brand_name(item):
    return (item.get("brand") or "").strip()


def product_eur_price(item):
    try:
        return float(item.get("display_price_with_tax") or 0) / EUR_TO_STORE
    except (TypeError, ValueError):
        return 0.0


def unique_sorted(values):
    seen = []
    for value in values:
        text = str(value or "").strip()
        if text and text not in seen:
            seen.append(text)
    return sorted(seen, key=lambda item: (item.lower(), item))


@app.route("/products")
def products():
    main = request.args.get("main", "").strip()
    sub = request.args.get("sub", "").strip()
    sub2 = request.args.get("sub2", "").strip()
    sub3 = request.args.get("sub3", "").strip()
    sub4 = request.args.get("sub4", "").strip()
    category = request.args.get("category", "All").strip() or "All"
    search = request.args.get("search", "").strip()
    sort = request.args.get("sort", "").strip()
    size_filter = request.args.get("size", "").strip()
    colour_filter = request.args.get("colour", "").strip()
    price_filter = request.args.get("price", "").strip()
    campaign = request.args.get("campaign", "").strip()
    brand_filter = request.args.get("brand", "").strip()
    specialty_filter = request.args.get("specialty", "").strip()
    if main not in load_main_categories():
        main = ""
    query, args = f"SELECT {SHOP_PRODUCT_COLUMNS} FROM products WHERE active=1 AND COALESCE(is_draft,0)=0", []
    if search:
        query += " AND (name ILIKE ? OR category ILIKE ? OR description ILIKE ? OR COALESCE(sub_category,'') ILIKE ? OR COALESCE(sub_categories,'') ILIKE ? OR COALESCE(sub_category_2,'') ILIKE ? OR COALESCE(sub_category_3,'') ILIKE ? OR COALESCE(sub_category_4,'') ILIKE ? OR COALESCE(main_category,'') ILIKE ? OR COALESCE(main_categories,'') ILIKE ? OR COALESCE(product_tags,'') ILIKE ? OR COALESCE(product_hashtags,'') ILIKE ?)"
        args.extend([f"%{search}%"] * 12)
    catalog = visible_catalog(get_db().execute(query + " ORDER BY id DESC", args).fetchall())
    rows = [item for item in catalog if matches_shop_filter(item, main, sub, sub2, sub3, sub4, category)]
    who = selected_audience_key()
    audience_label = next((label for key, label, _group in AUDIENCES if key == who), "")
    if who:
        audience_group = next(group for key, _label, group in AUDIENCES if key == who)
        rows = [item for item in rows if audience_group in (item.get("genders") or [])]
    sale = request.args.get("sale", "").strip() in {"1", "true", "yes"} or campaign == "sale"
    newest = request.args.get("new", "").strip() in {"1", "true", "yes"}
    if sale or campaign == "sale":
        rows = [item for item in rows if item.get("volume_max_percent")]
        sale = True
    if campaign == "deal":
        rows = [item for item in rows if item.get("deal_of_week")]
    if newest:
        flagged = [item for item in rows if item.get("new_arrival")]
        rows = flagged or rows[:16]
    facet_source = rows
    if size_filter:
        rows = [item for item in rows if size_filter in product_in_stock_sizes(item)]
    if specialty_filter:
        rows = [item for item in rows if specialty_filter in product_in_stock_sizes(item)]
    if colour_filter:
        rows = [item for item in rows if colour_filter in (item.get("colors") or [])]
    if brand_filter:
        rows = [item for item in rows if product_brand_name(item) == brand_filter]
    if price_filter == "0-25":
        rows = [item for item in rows if product_eur_price(item) < 25]
    elif price_filter == "25-50":
        rows = [item for item in rows if 25 <= product_eur_price(item) < 50]
    elif price_filter == "50-100":
        rows = [item for item in rows if 50 <= product_eur_price(item) < 100]
    elif price_filter == "100-":
        rows = [item for item in rows if product_eur_price(item) >= 100]
    if sort == "price_asc":
        rows.sort(key=product_eur_price)
    elif sort == "price_desc":
        rows.sort(key=product_eur_price, reverse=True)
    elif sort == "rating":
        rows.sort(key=lambda item: float(item.get("rating") or 0), reverse=True)
    else:
        rows.sort(key=lambda item: int(item.get("id") or 0), reverse=True)
    all_sizes = unique_sorted(size for item in facet_source for size in product_in_stock_sizes(item))
    current_group = next((group for group in shop_category_tree(catalog) if group["name"] == main), None)
    current_sub2s = current_group["sub2_map"].get(sub, []) if current_group and sub else []
    current_sub3s = current_group["sub3_map"].get(sub, {}).get(sub2, []) if current_group and sub and sub2 else []
    current_sub4s = (
        current_group["sub4_map"].get(sub, {}).get(sub2, {}).get(sub3, [])
        if current_group and sub and sub2 and sub3
        else []
    )
    title_parts = [
        part
        for part in (
            audience_label or None,
            "SALE" if sale else None,
            "New arrivals" if newest else None,
            main,
            sub if sub else None,
            sub2 if sub2 else None,
            sub3 if sub3 else None,
            sub4 if sub4 else None,
            category if category != "All" and not main and not sub else None,
        )
        if part
    ]

    def catalog_url(**overrides):
        payload = {
            "who": who,
            "main": main,
            "sub": sub,
            "sub2": sub2,
            "sub3": sub3,
            "sub4": sub4,
            "search": search,
            "sale": "1" if sale and campaign != "deal" else "",
            "new": "1" if newest else "",
            "sort": sort,
            "size": size_filter,
            "colour": colour_filter,
            "price": price_filter,
            "campaign": campaign,
            "brand": brand_filter,
            "specialty": specialty_filter,
            "category": category if category and category != "All" else "",
        }
        payload.update(overrides)
        return url_for(
            "products",
            **{key: value for key, value in payload.items() if value not in (None, "", False)},
        )

    return render_template(
        "products.html",
        products=rows,
        selected_main=main,
        selected_sub=sub,
        selected_sub2=sub2,
        selected_sub3=sub3,
        selected_sub4=sub4,
        selected=category,
        selected_sale=sale,
        selected_new=newest,
        search=search,
        current_subs=(current_group["subs"] if current_group else []),
        current_sub2s=current_sub2s,
        current_sub3s=current_sub3s,
        current_sub4s=current_sub4s,
        catalog_title=" · ".join(title_parts),
        catalog_url=catalog_url,
        selected_sort=sort,
        selected_size=size_filter,
        selected_colour=colour_filter,
        selected_price=price_filter,
        selected_campaign=campaign,
        selected_brand=brand_filter,
        selected_specialty=specialty_filter,
        filter_sizes=all_sizes,
        filter_colours=unique_sorted(color for item in facet_source for color in (item.get("colors") or [])),
        filter_brands=unique_sorted(product_brand_name(item) for item in facet_source if product_brand_name(item)),
        filter_specialty=[size for size in all_sizes if is_specialty_size(size)],
    )


@app.route("/product-image/<int:product_id>/<int:slot>")
def product_image(product_id, slot):
    if slot < 1 or slot > PRODUCT_IMAGE_SLOTS:
        abort(404)
    row = get_db().execute(
        "SELECT bytes, content_type FROM product_images WHERE product_id=? AND slot=?",
        (product_id, slot),
    ).fetchone()
    if not row or not row.get("bytes"):
        abort(404)
    data = row["bytes"]
    if isinstance(data, memoryview):
        data = data.tobytes()
    response = Response(bytes(data), mimetype=row.get("content_type") or "image/jpeg")
    response.headers["Cache-Control"] = "public, max-age=86400"
    return response


@app.route("/partner-image/<int:application_id>/<int:slot>")
def partner_image(application_id, slot):
    if slot < 1 or slot > PRODUCT_IMAGE_SLOTS:
        abort(404)
    application = get_db().execute("SELECT * FROM partner_applications WHERE id=?", (application_id,)).fetchone()
    if not application:
        abort(404)
    user = current_user()
    if not session.get("is_admin") and (not user or user["id"] != application.get("user_id")):
        abort(404)
    row = get_db().execute(
        "SELECT bytes, content_type FROM partner_application_images WHERE application_id=? AND slot=?",
        (application_id, slot),
    ).fetchone()
    if not row or not row.get("bytes"):
        abort(404)
    data = row["bytes"]
    if isinstance(data, memoryview):
        data = data.tobytes()
    response = Response(bytes(data), mimetype=row.get("content_type") or "image/jpeg")
    response.headers["Cache-Control"] = "public, max-age=86400"
    return response


@app.route("/product/<int:product_id>")
def product_detail(product_id):
    item = fetch_product(product_id)
    db = get_db()
    reviews = db.execute("SELECT * FROM reviews WHERE product_id=? ORDER BY id DESC", (product_id,)).fetchall()
    others = visible_catalog(
        db.execute(
            f"SELECT {SHOP_PRODUCT_COLUMNS} FROM products WHERE id!=? AND active=1 ORDER BY id DESC LIMIT 24",
            (product_id,),
        ).fetchall()
    )
    same_sub = [
        other
        for other in others
        if product_sub_category(other) == product_sub_category(item)
    ]
    same_main = [
        other
        for other in others
        if set(product_main_names(other)) & set(product_main_names(item)) and other not in same_sub
    ]
    related = (same_sub + same_main)[:4]
    return render_template("product_detail.html", product=item, reviews=reviews, related=related)


@app.post("/product/<int:product_id>/like")
def like_product(product_id):
    fetch_product(product_id)
    liked = liked_product_ids()
    db = get_db()
    if product_id in liked:
        liked.remove(product_id)
        db.execute("UPDATE products SET likes=GREATEST(likes-1,0) WHERE id=?", (product_id,))
        flash("Like removed.", "success")
    else:
        liked.append(product_id)
        db.execute("UPDATE products SET likes=likes+1 WHERE id=?", (product_id,))
        flash("Thanks for the like.", "success")
    db.commit()
    session["liked"] = liked
    return redirect(request.referrer or url_for("product_detail", product_id=product_id))


@app.post("/product/<int:product_id>/review")
def add_review(product_id):
    fetch_product(product_id)
    name, body = request.form.get("name", "").strip(), request.form.get("body", "").strip()
    try:
        rating = int(request.form.get("rating", 0))
    except ValueError:
        rating = 0
    if not name or not body or rating not in range(1, 6):
        flash("Please enter a name, a 1–5 rating, and your review.", "error")
    else:
        db = get_db()
        db.execute(
            "INSERT INTO reviews (product_id,name,rating,body,created_at) VALUES (?,?,?,?,?)",
            (product_id, name, rating, body, datetime.utcnow().strftime("%Y-%m-%d")),
        )
        db.execute(
            "UPDATE products SET reviews_count=reviews_count+1, rating=ROUND((((rating*reviews_count)+?)::numeric)/(reviews_count+1),1) WHERE id=?",
            (rating, product_id),
        )
        db.commit()
        flash("Thank you — your review is live.", "success")
    return redirect(url_for("product_detail", product_id=product_id) + "#reviews")


@app.post("/cart/add/<int:product_id>")
def add_cart(product_id):
    item = fetch_product(product_id)
    gender = (request.form.get("offer_gender") or "").strip()
    offers = item.get("gender_offers") or {}
    if gender in offers:
        apply_stored_offer(item, offers[gender])
        item["offer_gender"] = gender
        item["offer_label"] = GENDER_LABELS.get(gender, "")
    elif offers:
        gender = item.get("offer_gender") or ""
    else:
        gender = ""
    if item.get("is_virtual"):
        selected_size = VIRTUAL_SIZE
        selected_color = VIRTUAL_COLOR
        variant_stock = int(item.get("stock") or 0)
    else:
        selected_size = request.form.get("size", item["sizes"][0] if item["sizes"] else "Standard")
        selected_color = request.form.get("color", item["colors"][0] if item["colors"] else "Default")
        if item["sizes"] and selected_size not in item["sizes"]:
            flash("Please select a valid size.", "error")
            return redirect(url_for("product_detail", product_id=product_id))
        if item["colors"] and selected_color not in item["colors"]:
            flash("Please select a valid colour.", "error")
            return redirect(url_for("product_detail", product_id=product_id))
        color = next((entry for entry in item["color_rows"] if entry["name"] == selected_color), None)
        variant_stock = int(color["sizes"].get(selected_size, 0)) if color else 0
    try:
        quantity = int(request.form.get("quantity", 1) or 1)
    except ValueError:
        quantity = 1
    quantity = max(1, quantity)
    key = f"{product_id}:{selected_size}:{selected_color}"
    if gender:
        key = f"{key}:{gender}"
    if variant_stock <= 0:
        flash("This product is currently out of stock." if item.get("is_virtual") else f"{selected_color} in size {selected_size} is currently out of stock.", "error")
        return redirect(url_for("product_detail", product_id=product_id))
    cart = session["cart"]
    new_quantity = cart.get(key, 0) + quantity
    if new_quantity > variant_stock:
        flash(
            f"Only {variant_stock} left." if item.get("is_virtual") else f"Only {variant_stock} left in {selected_color}, size {selected_size}.",
            "error",
        )
        return redirect(url_for("product_detail", product_id=product_id))
    cart[key] = new_quantity
    session["cart"] = cart
    if item.get("is_virtual"):
        flash(f"{item['name']} added to your cart.", "success")
    else:
        flash(f"{item['name']} ({selected_color} / {selected_size}) added to your cart.", "success")
    if request.form.get("intent") == "buy":
        return redirect(url_for("cart"))
    return redirect(request.referrer or url_for("cart"))


@app.post("/cart/remove/<int:product_id>")
def remove_cart(product_id):
    cart = session["cart"]
    cart.pop(request.form.get("cart_key", ""), None)
    session["cart"] = cart
    return redirect(url_for("cart"))


@app.post("/cart/update")
def update_cart():
    cart = session["cart"]
    key = request.form.get("cart_key", "")
    if key not in cart:
        return redirect(url_for("cart"))
    action = request.form.get("action", "")
    try:
        current = int(cart[key])
    except (TypeError, ValueError):
        current = 1
    if action == "inc":
        current += 1
    elif action == "dec":
        current -= 1
    else:
        try:
            current = int(request.form.get("quantity", current) or current)
        except ValueError:
            pass
    if current <= 0:
        cart.pop(key, None)
        session["cart"] = cart
        return redirect(url_for("cart"))
    item_id, selected_size, selected_color, gender = split_cart_key(key)
    row = get_db().execute("SELECT * FROM products WHERE id=?", (item_id,)).fetchone()
    if row:
        item = product(row)
        use_cart_offer(item, gender)
        if item.get("is_virtual"):
            variant_stock = int(item.get("stock") or 0)
        else:
            color = next((entry for entry in item["color_rows"] if entry["name"] == selected_color), None)
            variant_stock = int(color["sizes"].get(selected_size, 0)) if color else 0
        if current > variant_stock:
            flash(
                f"Only {variant_stock} left." if item.get("is_virtual") else f"Only {variant_stock} left in {selected_color}, size {selected_size}.",
                "error",
            )
            current = max(1, variant_stock) if variant_stock else 0
        if current <= 0:
            cart.pop(key, None)
            session["cart"] = cart
            return redirect(url_for("cart"))
    cart[key] = current
    session["cart"] = cart
    return redirect(url_for("cart"))


def cart_items():
    items, total, tax = [], 0, 0
    quantities = {}
    parsed = []
    for cart_key, quantity in session["cart"].items():
        item_id, selected_size, selected_color, gender = split_cart_key(cart_key)
        row = get_db().execute("SELECT * FROM products WHERE id=?", (item_id,)).fetchone()
        if row:
            parsed.append((cart_key, int(quantity), item_id, selected_size, selected_color, gender, row))
            qty_key = f"{item_id}:{gender or ''}"
            quantities[qty_key] = quantities.get(qty_key, 0) + int(quantity)
    for cart_key, quantity, item_id, selected_size, selected_color, gender, row in parsed:
        item = product(row)
        use_cart_offer(item, gender)
        if gender:
            item["offer_gender"] = gender
            item["offer_label"] = GENDER_LABELS.get(gender, item.get("offer_label") or "")
        volume_qty = quantities.get(f"{item_id}:{gender or ''}", quantity)
        percent = volume_percent_for(item.get("active_volume_discounts") or item.get("volume_discounts"), volume_qty)
        unit_price = apply_percent(item["display_price"], percent)
        unit_tax = product_tax(unit_price)
        item["quantity"] = quantity
        item["selected_size"] = selected_size
        item["selected_color"] = selected_color
        item["cart_key"] = cart_key
        item["volume_percent"] = percent
        item["display_price"] = unit_price
        item["tax_percent"] = PRODUCT_TAX_PERCENT
        item["unit_tax"] = unit_tax
        item["tax_amount"] = unit_tax * quantity
        item["display_price_with_tax"] = round(unit_price + unit_tax, 2)
        item["subtotal"] = unit_price * quantity
        item["subtotal_with_tax"] = item["subtotal"] + item["tax_amount"]
        item["line_weight"] = float(item.get("ship_weight") or item.get("weight") or 0) * quantity
        total += item["subtotal"]
        tax += item["tax_amount"]
        items.append(item)
    return items, total, tax


def cart_weight_kg(items):
    return round(sum(float(item.get("line_weight") or 0) for item in items), 2)


def shipping_label(value, unit):
    if unit == "EUR":
        return f"€{value:g}"
    return f"Rs {value:,.0f}"


def store_shipping_amount(value, unit):
    amount = float(value)
    return amount * EUR_TO_STORE if unit == "EUR" else amount


def load_shipping_zones():
    rows = get_db().execute("SELECT zone, unit, under_value, over_value FROM shipping_rates").fetchall()
    by_name = {row["zone"]: row for row in rows}
    zones = []
    for default in DEFAULT_SHIPPING_ZONES:
        row = by_name.get(default["name"], default)
        unit = row["unit"] if "unit" in row else default["unit"]
        under = float(row["under_value"] if "under_value" in row else default["under"])
        over = float(row["over_value"] if "over_value" in row else default["over"])
        zones.append(
            {
                "name": default["name"],
                "key": default["key"],
                "unit": unit,
                "under": under,
                "over": over,
                "under_label": shipping_label(under, unit),
                "over_label": shipping_label(over, unit),
                "under_store": store_shipping_amount(under, unit),
                "over_store": store_shipping_amount(over, unit),
            }
        )
    return zones


def shipping_zone_map():
    return {zone["name"]: zone for zone in load_shipping_zones()}


def shipping_options(items, weight_kg, method="standard"):
    if isinstance(items, list) and not items:
        items = [{"shipping": normalize_product_shipping(blank_product_shipping())}]
        weight_kg = 0
    heavy = weight_kg > WEIGHT_LIMIT_KG
    express = method == "express"
    options = []
    sources = items or [None]
    for zone in DEFAULT_SHIPPING_ZONES:
        standard_amount = None
        express_amount = None
        labels = None
        for item in sources:
            rate = ((item or {}).get("shipping") or normalize_product_shipping(None))[zone["key"]]
            standard = rate["over_store"] if heavy else rate["under_store"]
            express_price = rate["express_over_store"] if heavy else rate["express_under_store"]
            if standard_amount is None or standard > standard_amount:
                standard_amount = standard
                labels = rate
            if express_amount is None or express_price > express_amount:
                express_amount = express_price
                if labels is None:
                    labels = rate
        amount = express_amount if express else standard_amount
        current_label = (
            labels["express_over_label"] if express and heavy
            else labels["express_under_label"] if express
            else labels["over_label"] if heavy
            else labels["under_label"]
        )
        options.append(
            {
                "name": zone["name"],
                "key": zone["key"],
                "unit": zone["unit"],
                "under_label": labels["under_label"],
                "over_label": labels["over_label"],
                "express_under_label": labels["express_under_label"],
                "express_over_label": labels["express_over_label"],
                "standard_amount": standard_amount,
                "express_amount": express_amount,
                "current_label": current_label,
                "amount": amount,
            }
        )
    region = customer_zone_name()
    matched = [option for option in options if option["name"] == region]
    return matched or options[:1]


def shipping_quote(items, subtotal, country, method="standard"):
    physical = [item for item in items if not item.get("is_virtual")]
    if items and not physical:
        lang = (session.get("language") or "en") if has_request_context() else "en"
        return 0, translate("digital_delivery", lang), 0
    weight_kg = cart_weight_kg(physical)
    options = shipping_options(physical, weight_kg, method)
    zone = next((entry for entry in options if entry["name"] == country), options[0])
    lang = (session.get("language") or "en") if has_request_context() else "en"
    band = translate("over_5kg" if weight_kg > WEIGHT_LIMIT_KG else "under_5kg", lang)
    speed = translate("express" if method == "express" else "standard", lang)
    label = translate(
        "delivery_summary",
        lang,
        zone=zone["name"],
        speed=speed,
        price=zone["current_label"],
        band=band,
        kg=f"{weight_kg:g}",
    )
    return zone["amount"], label, weight_kg


def reserve_order_stock(db, items):
    for cart_item in items:
        row = db.execute("SELECT * FROM products WHERE id=? FOR UPDATE", (cart_item["id"],)).fetchone()
        if not row:
            raise ValueError(f"{cart_item['name']} is no longer available.")
        current = product(row)
        offers = current.get("gender_offers") or {}
        gender = cart_item.get("offer_gender") or ""
        if gender and gender in offers:
            apply_stored_offer(current, offers[gender])
        color = next(
            (entry for entry in current["color_rows"] if entry["name"] == cart_item["selected_color"]),
            None,
        )
        available = int(color["sizes"].get(cart_item["selected_size"], 0)) if color else 0
        if available < cart_item["quantity"]:
            raise ValueError(
                f"Only {available} of {cart_item['name']} in "
                f"{cart_item['selected_color']} / {cart_item['selected_size']} remain."
            )
        color["sizes"][cart_item["selected_size"]] = available - cart_item["quantity"]
        color["quantity"] = sum(color["sizes"].values())
        if gender and gender in offers:
            offers[gender]["colors"] = current["color_rows"]
            offers[gender]["sizes"] = current["size_rows"]
            if current.get("is_virtual"):
                offers[gender]["virtual_stock"] = sum(int(entry.get("quantity") or 0) for entry in current["color_rows"])
            total_stock = 0
            for offer in offers.values():
                for entry in offer.get("colors") or []:
                    total_stock += int(entry.get("quantity") or 0)
            primary = (current.get("genders") or ["Unisex"])[0]
            if gender == primary:
                db.execute(
                    "UPDATE products SET colors_json=?, sizes_json=?, stock=?, gender_offers=? WHERE id=?",
                    (
                        json.dumps(current["color_rows"]),
                        json.dumps(current["size_rows"]),
                        total_stock,
                        json.dumps(offers),
                        cart_item["id"],
                    ),
                )
            else:
                db.execute(
                    "UPDATE products SET stock=?, gender_offers=? WHERE id=?",
                    (total_stock, json.dumps(offers), cart_item["id"]),
                )
            continue
        total_stock = sum(entry["quantity"] for entry in current["color_rows"])
        db.execute(
            "UPDATE products SET colors_json=?, stock=? WHERE id=?",
            (json.dumps(current["color_rows"]), total_stock, cart_item["id"]),
        )


PAYMENT_LABELS = {
    "pay_on_delivery": "Pay on delivery",
    "bank_transfer": "Bank transfer",
    "paypal": "PayPal",
    "easypaisa": "EasyPaisa",
    "jazzcash": "JazzCash",
    "stripe": "Card / Stripe",
    "klarna": "Klarna",
    "apple_pay": "Apple Pay",
    "zelle": "Zelle",
}


def translated_payment_label(method):
    method = method or ""
    key = f"pay_{method}"
    lang = (session.get("language") or "en") if has_request_context() else "en"
    label = translate(key, lang)
    if label == key:
        return PAYMENT_LABELS.get(method, method)
    return label
ORDER_STATUSES = ("new", "processing", "shipped")
TRACKING_CARRIERS = ("dhl", "hermes")
TRACKING_URLS = {
    "dhl": "https://www.dhl.com/de-en/home/tracking.html?tracking-id={number}",
    "hermes": "https://www.myhermes.de/empfangen/sendungsverfolgung/?trackingID={number}",
}


def tracking_url(carrier, number):
    number = (number or "").strip()
    carrier = (carrier or "").strip().lower()
    template = TRACKING_URLS.get(carrier)
    if not number or not template:
        return ""
    return template.format(number=number)


def parse_order_datetime(raw):
    if not raw:
        return None
    text = str(raw).strip().replace("Z", "")
    try:
        return datetime.fromisoformat(text)
    except ValueError:
        return None


def order_amount_eur(order):
    total = float(order.get("total") or 0)
    currency = order.get("currency") or "EUR"
    rate = CURRENCIES.get(currency, CURRENCIES["EUR"])[0]
    store_amount = total / rate if rate else 0
    return round(store_amount * CURRENCIES["EUR"][0], 2)


def build_sales_overview(rows):
    orders = [order_record(row) for row in rows]
    now = datetime.utcnow()
    month_start = now.replace(day=1, hour=0, minute=0, second=0, microsecond=0)
    week_ago = now - timedelta(days=7)
    status_counts = {status: 0 for status in ORDER_STATUSES}
    daily = {}
    for offset in range(13, -1, -1):
        daily[(now - timedelta(days=offset)).date().isoformat()] = 0.0
    revenue = 0.0
    month_revenue = 0.0
    week_revenue = 0.0
    for order in orders:
        amount = order_amount_eur(order)
        revenue += amount
        status = order["status"] if order["status"] in status_counts else "new"
        status_counts[status] += 1
        created = parse_order_datetime(order.get("created_at"))
        if not created:
            continue
        if created >= month_start:
            month_revenue += amount
        if created >= week_ago:
            week_revenue += amount
        day = created.date().isoformat()
        if day in daily:
            daily[day] += amount
    count = len(orders)
    return {
        "revenue_eur": round(revenue, 2),
        "month_revenue_eur": round(month_revenue, 2),
        "week_revenue_eur": round(week_revenue, 2),
        "order_count": count,
        "average_eur": round(revenue / count, 2) if count else 0.0,
        "status_counts": status_counts,
        "daily_labels": [datetime.fromisoformat(day).strftime("%d %b") for day in daily],
        "daily_values": [round(value, 2) for value in daily.values()],
    }


def order_record(row):
    order = dict(row) if not isinstance(row, dict) else dict(row)
    items = parse_order_items(order.get("items"))
    order["line_items"] = items
    order["status"] = order.get("status") or "new"
    order["status_index"] = ORDER_STATUSES.index(order["status"]) if order["status"] in ORDER_STATUSES else 0
    order["tracking_carrier"] = (order.get("tracking_carrier") or "").strip().lower()
    order["tracking_number"] = (order.get("tracking_number") or "").strip()
    order["tracking_url"] = tracking_url(order["tracking_carrier"], order["tracking_number"])
    order["tracking_label"] = order["tracking_carrier"].upper() if order["tracking_carrier"] in TRACKING_CARRIERS else ""
    net = sum(float(item.get("subtotal") or 0) for item in items if isinstance(item, dict))
    tax = float(order.get("tax") or 0)
    if not tax:
        tax = sum(float(item.get("tax_amount") or 0) for item in items if isinstance(item, dict))
    shipping = float(order.get("shipping") or 0)
    total = float(order.get("total") or 0)
    order["items_subtotal"] = net if net else max(0.0, round(total - tax - shipping, 2))
    order["tax"] = tax
    order["shipping"] = shipping
    order["payment_label"] = translated_payment_label(order.get("payment_method"))
    order["payment_status"] = (order.get("payment_status") or "unpaid").strip() or "unpaid"
    order["payment_reference"] = (order.get("payment_reference") or "").strip()
    return order


def checkout_data():
    data = session.get("checkout")
    if not isinstance(data, dict):
        data = {}
        session["checkout"] = data
    return data


def save_checkout(**fields):
    data = checkout_data()
    data.update(fields)
    session["checkout"] = data
    session.modified = True
    return data


def safe_next(default):
    target = (request.values.get("next") or "").strip()
    if target.startswith("/") and not target.startswith("//") and "://" not in target:
        return target
    return default


def checkout_quote(shipping_method=None):
    items, total, items_tax = cart_items()
    data = checkout_data()
    shipping_method = shipping_method or data.get("shipping_method") or "standard"
    if shipping_method not in {"standard", "express"}:
        shipping_method = "standard"
    country = data.get("country") or customer_zone_name()
    if country not in ZONE_NAMES:
        country = customer_zone_name()
    shipping, shipping_label, weight_kg = shipping_quote(items, total, country, shipping_method)
    physical = [item for item in items if not item.get("is_virtual")]
    shipping_tax = product_tax(shipping)
    tax = round(items_tax + shipping_tax, 2)
    return {
        "items": items,
        "total": total,
        "items_tax": items_tax,
        "shipping_tax": shipping_tax,
        "tax": tax,
        "shipping": shipping,
        "shipping_label": shipping_label,
        "grand_total": total + tax + shipping,
        "selected_country": country,
        "shipping_method": shipping_method,
        "cart_weight": weight_kg,
        "shipping_zones": shipping_options(physical, weight_kg, shipping_method),
        "heavy_order": weight_kg > WEIGHT_LIMIT_KG,
        "checkout": data,
        "merchants": merchant_settings(),
        "pakistan_checkout": country == "Pakistan",
        **merchant_ready_flags(),
    }


def require_checkout_cart():
    items, _, _ = cart_items()
    if not items:
        flash("Add items to your cart before checkout.", "error")
        return redirect(url_for("cart"))
    return None


def checkout_account_ready():
    return bool(session.get("user_id") or checkout_data().get("guest"))


def checkout_details_ready():
    data = checkout_data()
    return bool(
        data.get("name")
        and data.get("email")
        and data.get("address")
        and data.get("shipping_method") in {"standard", "express"}
    )


def checkout_payment_ready():
    return checkout_data().get("payment_method") in allowed_payment_methods()


@app.route("/cart")
def cart():
    return render_template("cart.html", **checkout_quote())


@app.route("/checkout/account", methods=["GET", "POST"])
def checkout_account():
    blocked = require_checkout_cart()
    if blocked:
        return blocked
    if session.get("user_id"):
        save_checkout(guest=False)
        return redirect(url_for("checkout_details"))
    if request.method == "POST":
        save_checkout(guest=True)
        return redirect(url_for("checkout_details"))
    return render_template("checkout_account.html", **checkout_quote())


@app.route("/checkout/details", methods=["GET", "POST"])
def checkout_details():
    blocked = require_checkout_cart()
    if blocked:
        return blocked
    if not checkout_account_ready():
        return redirect(url_for("checkout_account"))
    user = current_user()
    data = checkout_data()
    if user:
        save_checkout(
            guest=False,
            name=data.get("name") or user.get("name") or "",
            email=data.get("email") or user.get("email") or "",
        )
    if request.method == "POST":
        name = request.form.get("name", "").strip()[:100]
        email = request.form.get("email", "").strip().lower()[:120]
        address = request.form.get("address", "").strip()
        shipping_method = request.form.get("shipping_method", "standard")
        if shipping_method not in {"standard", "express"}:
            shipping_method = "standard"
        if not name or not email or not address:
            flash("Enter your name, email, and delivery address.", "error")
        else:
            address_zone = zone_from_address(address)
            if address_zone:
                apply_region(address_zone)
                g.customer_location = None
            country = customer_zone_name()
            save_checkout(
                name=name,
                email=email,
                address=address,
                shipping_method=shipping_method,
                country=country,
            )
            return redirect(url_for("checkout_payment"))
    return render_template("checkout_details.html", **checkout_quote())


@app.route("/checkout/payment", methods=["GET", "POST"])
def checkout_payment():
    blocked = require_checkout_cart()
    if blocked:
        return blocked
    if not checkout_account_ready():
        return redirect(url_for("checkout_account"))
    if not checkout_details_ready():
        return redirect(url_for("checkout_details"))
    if request.method == "POST":
        payment_method = request.form.get("payment_method", "")
        if payment_method not in allowed_payment_methods():
            flash("Choose a payment method.", "error")
        else:
            save_checkout(payment_method=payment_method)
            return redirect(url_for("checkout_summary"))
    return render_template("checkout_payment.html", **checkout_quote())


def customer_charge(store_amount, currency):
    currency = (currency or "EUR").upper()
    if currency not in CURRENCIES:
        currency = "EUR"
    amount = round(float(store_amount) * CURRENCIES[currency][0] + 1e-9, 2)
    if amount <= 0:
        raise ValueError("This order total cannot be charged.")
    return amount, currency


def minor_units(amount):
    return int(round(float(amount) * 100))


def payment_snapshot(quote, data):
    items = []
    for item in quote["items"]:
        items.append(
            {
                "id": item.get("id"),
                "name": item.get("name") or "Item",
                "quantity": int(item.get("quantity") or 1),
                "selected_color": item.get("selected_color") or "",
                "selected_size": item.get("selected_size") or "",
                "subtotal": float(item.get("subtotal") or 0),
                "tax_amount": float(item.get("tax_amount") or 0),
                "subtotal_with_tax": float(item.get("subtotal_with_tax") or 0),
                "is_virtual": bool(item.get("is_virtual")),
                "volume_percent": item.get("volume_percent") or 0,
            }
        )
    country = data.get("country") if data.get("country") in ZONE_NAMES else quote["selected_country"]
    amount, currency = customer_charge(quote["grand_total"], session.get("currency") or "EUR")
    return {
        "items": items,
        "name": (data.get("name") or "")[:100],
        "email": (data.get("email") or "")[:120],
        "address": data.get("address") or "",
        "country": country,
        "shipping": float(quote["shipping"] or 0),
        "tax": float(quote["tax"] or 0),
        "store_total": float(quote["grand_total"] or 0),
        "currency": currency,
        "charge_amount": amount,
        "payment_method": data.get("payment_method") or "",
    }


def provider_error_text(payload, fallback):
    if isinstance(payload, dict):
        err = payload.get("error")
        if isinstance(err, dict) and err.get("message"):
            return str(err["message"])[:180]
        if payload.get("error_description"):
            return str(payload["error_description"])[:180]
        details = payload.get("details")
        if isinstance(details, list) and details and isinstance(details[0], dict):
            return str(details[0].get("description") or fallback)[:180]
        if payload.get("message"):
            return str(payload["message"])[:180]
    return fallback


def http_json(method, url, headers=None, body=None, form=None):
    headers = dict(headers or {})
    data = None
    if form is not None:
        data = urllib.parse.urlencode(form, doseq=True).encode()
        headers.setdefault("Content-Type", "application/x-www-form-urlencoded")
    elif body is not None:
        data = json.dumps(body).encode()
        headers.setdefault("Content-Type", "application/json")
    req = urllib.request.Request(url, data=data, headers=headers, method=method)
    try:
        with urllib.request.urlopen(req, timeout=25, context=ssl.create_default_context(cafile=certifi.where())) as response:
            raw = response.read().decode()
            return (json.loads(raw) if raw else {}), None
    except urllib.error.HTTPError as error:
        raw = error.read().decode(errors="replace")
        try:
            payload = json.loads(raw) if raw else {}
        except json.JSONDecodeError:
            payload = {}
        return None, payload or {"message": "Payment service rejected the request."}
    except urllib.error.URLError:
        return None, {"message": "Payment service could not be reached."}


def remember_payment(provider, reference, snapshot):
    session["payment_pending"] = {"provider": provider, "reference": reference, "snapshot": snapshot}
    session.modified = True


def pending_payment(provider, reference):
    pending = session.get("payment_pending")
    if not isinstance(pending, dict):
        return None
    if pending.get("provider") != provider or pending.get("reference") != reference:
        return None
    snapshot = pending.get("snapshot")
    return snapshot if isinstance(snapshot, dict) else None


def clear_paid_checkout():
    session["cart"] = {}
    session["checkout"] = {}
    session.pop("payment_pending", None)
    session.modified = True


def insert_shop_order(snapshot, payment_status, payment_reference, payment_amount, payment_currency, require_stock=False):
    db = get_db()
    if payment_reference:
        existing = db.execute(
            "SELECT id FROM orders WHERE payment_reference=?",
            (payment_reference,),
        ).fetchone()
        if existing:
            clear_paid_checkout()
            return existing["id"], ""
    stock_warning = ""
    try:
        reserve_order_stock(db, snapshot["items"])
    except ValueError as error:
        db.rollback()
        if require_stock:
            raise
        stock_warning = str(error)
    try:
        db.execute(
        """
        INSERT INTO orders (
            customer_name,email,address,country,payment_method,currency,total,shipping,tax,status,items,created_at,
            payment_status,payment_reference,payment_amount,payment_currency
        ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
        """,
        (
            snapshot.get("name"),
            snapshot.get("email"),
            snapshot.get("address"),
            snapshot.get("country"),
            snapshot.get("payment_method"),
            snapshot.get("currency") or session.get("currency") or "EUR",
            snapshot.get("store_total"),
            snapshot.get("shipping") or 0,
            snapshot.get("tax") or 0,
            "new",
            json.dumps(snapshot.get("items") or []),
            datetime.utcnow().isoformat(),
            payment_status,
            payment_reference or None,
            payment_amount,
            payment_currency or None,
        ),
        )
    except IntegrityError:
        db.rollback()
        clear_paid_checkout()
        return None, ""
    db.commit()
    clear_paid_checkout()
    return None, stock_warning


def finish_paid_order(snapshot, reference, amount, currency):
    _order_id, stock_warning = insert_shop_order(snapshot, "paid", reference, amount, currency)
    if stock_warning:
        flash(
            "Payment received, but stock changed while you were paying. We saved the order and will contact you.",
            "error",
        )
    else:
        flash("Payment received. Your order is placed.", "success")
    return redirect(url_for("home"))


def start_stripe_checkout(snapshot):
    settings = merchant_settings()
    secret = (settings.get("stripe_secret") or "").strip()
    if not secret:
        raise ValueError("Add the Stripe secret key in Admin Settings before taking card payments.")
    token = secrets.token_urlsafe(16)
    success_url = url_for("checkout_stripe_success", _external=True) + "?session_id={CHECKOUT_SESSION_ID}"
    cancel_url = url_for("checkout_stripe_cancel", _external=True)
    names = ", ".join(item["name"] for item in snapshot["items"][:6])[:120] or "AR Shopping World order"
    items_meta = json.dumps(snapshot["items"])
    if len(items_meta) > 450:
        items_meta = "[]"
    payload, error = http_json(
        "POST",
        "https://api.stripe.com/v1/checkout/sessions",
        headers={"Authorization": f"Bearer {secret}"},
        form=[
            ("mode", "payment"),
            ("success_url", success_url),
            ("cancel_url", cancel_url),
            ("customer_email", snapshot.get("email") or ""),
            ("client_reference_id", token),
            ("line_items[0][quantity]", "1"),
            ("line_items[0][price_data][currency]", snapshot["currency"].lower()),
            ("line_items[0][price_data][unit_amount]", str(minor_units(snapshot["charge_amount"]))),
            ("line_items[0][price_data][product_data][name]", "AR Shopping World order"),
            ("line_items[0][price_data][product_data][description]", names),
            ("metadata[token]", token),
            ("metadata[amount]", str(minor_units(snapshot["charge_amount"]))),
            ("metadata[currency]", snapshot["currency"].lower()),
            ("metadata[name]", snapshot.get("name") or ""),
            ("metadata[email]", snapshot.get("email") or ""),
            ("metadata[country]", snapshot.get("country") or ""),
            ("metadata[address]", (snapshot.get("address") or "")[:450]),
            ("metadata[shipping]", str(snapshot.get("shipping") or 0)),
            ("metadata[tax]", str(snapshot.get("tax") or 0)),
            ("metadata[store_total]", str(snapshot.get("store_total") or 0)),
            ("metadata[items]", items_meta),
        ],
    )
    if error or not payload or not payload.get("url") or not payload.get("id"):
        raise ValueError(provider_error_text(error, "Stripe could not start the card payment."))
    remember_payment("stripe", payload["id"], snapshot)
    return payload["url"]


def load_stripe_session(session_id):
    secret = (merchant_settings().get("stripe_secret") or "").strip()
    if not secret or not session_id:
        return None, "Card payment could not be confirmed."
    payload, error = http_json(
        "GET",
        "https://api.stripe.com/v1/checkout/sessions/" + urllib.parse.quote(session_id, safe=""),
        headers={"Authorization": f"Bearer {secret}"},
    )
    if error or not payload:
        return None, provider_error_text(error, "Card payment could not be confirmed.")
    return payload, None


def paypal_api_base(settings=None):
    settings = settings or merchant_settings()
    if (settings.get("paypal_sandbox") or "").strip() == "1":
        return "https://api-m.sandbox.paypal.com"
    return "https://api-m.paypal.com"


def paypal_access_token(settings=None):
    settings = settings or merchant_settings()
    client_id = (settings.get("paypal_client_id") or "").strip()
    secret = (settings.get("paypal_secret") or "").strip()
    if not client_id or not secret:
        return None, "Add the PayPal client ID and secret in Admin Settings before taking PayPal payments."
    encoded = base64.b64encode(f"{client_id}:{secret}".encode()).decode()
    payload, error = http_json(
        "POST",
        paypal_api_base(settings) + "/v1/oauth2/token",
        headers={"Authorization": f"Basic {encoded}"},
        form=[("grant_type", "client_credentials")],
    )
    token = (payload or {}).get("access_token")
    if error or not token:
        text = provider_error_text(error, "PayPal could not be reached. Check the client ID, secret, and sandbox setting.")
        if "authentication" in text.lower() or "invalid_client" in text.lower():
            return None, "PayPal rejected the client ID or secret. If these are sandbox keys, tick Use PayPal sandbox in Admin Settings."
        return None, text
    return token, None


def start_paypal_checkout(snapshot):
    token, error = paypal_access_token()
    if error:
        raise ValueError(error)
    payload, error = http_json(
        "POST",
        paypal_api_base() + "/v2/checkout/orders",
        headers={"Authorization": f"Bearer {token}"},
        body={
            "intent": "CAPTURE",
            "purchase_units": [
                {
                    "description": "AR Shopping World order",
                    "amount": {
                        "currency_code": snapshot["currency"],
                        "value": f"{snapshot['charge_amount']:.2f}",
                    },
                }
            ],
            "payment_source": {
                "paypal": {
                    "experience_context": {
                        "brand_name": "AR Shopping World",
                        "shipping_preference": "NO_SHIPPING",
                        "user_action": "PAY_NOW",
                        "return_url": url_for("checkout_paypal_return", _external=True),
                        "cancel_url": url_for("checkout_paypal_cancel", _external=True),
                    }
                }
            },
        },
    )
    if error or not payload:
        raise ValueError(provider_error_text(error, "PayPal could not start the payment."))
    approve = ""
    for link in payload.get("links") or []:
        if link.get("rel") in {"payer-action", "approve"} and link.get("href"):
            approve = link["href"]
            if link.get("rel") == "payer-action":
                break
    order_id = payload.get("id") or ""
    if not approve or not order_id:
        raise ValueError("PayPal did not return a payment page.")
    remember_payment("paypal", order_id, snapshot)
    return approve


def paypal_order(order_id, token):
    payload, error = http_json(
        "GET",
        paypal_api_base() + "/v2/checkout/orders/" + urllib.parse.quote(order_id, safe=""),
        headers={"Authorization": f"Bearer {token}"},
    )
    if error or not payload:
        return None, provider_error_text(error, "PayPal payment could not be confirmed.")
    return payload, None


def paypal_capture_amount(order_payload):
    units = order_payload.get("purchase_units") or []
    if not units:
        return None, None, None
    captures = ((units[0].get("payments") or {}).get("captures") or [])
    if not captures:
        return None, None, None
    capture = captures[0]
    amount = (capture.get("amount") or {})
    try:
        value = round(float(amount.get("value") or 0), 2)
    except (TypeError, ValueError):
        value = 0
    return capture.get("id") or "", value, (amount.get("currency_code") or "").upper()


def capture_paypal_order(order_id):
    token, error = paypal_access_token()
    if error:
        return None, error
    current, error = paypal_order(order_id, token)
    if error:
        return None, error
    if (current.get("status") or "") == "COMPLETED":
        return current, None
    payload, error = http_json(
        "POST",
        paypal_api_base() + "/v2/checkout/orders/" + urllib.parse.quote(order_id, safe="") + "/capture",
        headers={"Authorization": f"Bearer {token}", "Content-Type": "application/json"},
        body={},
    )
    if error or not payload:
        return None, provider_error_text(error, "PayPal could not capture the payment.")
    return payload, None


def amounts_match(expected, paid):
    return abs(float(expected) - float(paid)) < 0.02


@app.route("/checkout/summary", methods=["GET", "POST"])
def checkout_summary():
    blocked = require_checkout_cart()
    if blocked:
        return blocked
    if not checkout_account_ready():
        return redirect(url_for("checkout_account"))
    if not checkout_details_ready():
        return redirect(url_for("checkout_details"))
    if not checkout_payment_ready():
        return redirect(url_for("checkout_payment"))
    quote = checkout_quote()
    data = checkout_data()
    if request.method == "POST":
        method = data.get("payment_method")
        if method in {"stripe", "paypal"}:
            try:
                snapshot = payment_snapshot(quote, data)
                target = start_stripe_checkout(snapshot) if method == "stripe" else start_paypal_checkout(snapshot)
            except ValueError as error:
                flash(str(error), "error")
            else:
                return redirect(target)
        else:
            try:
                snapshot = payment_snapshot(quote, data)
            except ValueError as error:
                flash(str(error), "error")
            else:
                try:
                    insert_shop_order(snapshot, "unpaid", None, None, snapshot.get("currency"), require_stock=True)
                except ValueError as error:
                    rollback_db()
                    flash(str(error), "error")
                else:
                    flash("Order placed successfully. We will contact you shortly.", "success")
                    return redirect(url_for("home"))
    quote["payment_label"] = translated_payment_label(data.get("payment_method"))
    return render_template("checkout_summary.html", **quote)


def snapshot_from_stripe(paid):
    meta = paid.get("metadata") or {}
    details = paid.get("customer_details") or {}
    try:
        items = json.loads(meta.get("items") or "[]")
    except json.JSONDecodeError:
        items = []
    if not isinstance(items, list):
        items = []
    try:
        store_total = float(meta.get("store_total") or 0)
        shipping = float(meta.get("shipping") or 0)
        tax = float(meta.get("tax") or 0)
    except (TypeError, ValueError):
        store_total, shipping, tax = 0, 0, 0
    amount = int(paid.get("amount_total") or 0) / 100
    return {
        "items": items,
        "name": (details.get("name") or meta.get("name") or "Customer")[:100],
        "email": (details.get("email") or meta.get("email") or "")[:120],
        "address": meta.get("address") or "",
        "country": meta.get("country") or "",
        "shipping": shipping,
        "tax": tax,
        "store_total": store_total,
        "currency": (paid.get("currency") or meta.get("currency") or "EUR").upper(),
        "charge_amount": round(amount, 2),
        "payment_method": "stripe",
    }


@app.route("/checkout/stripe/success")
def checkout_stripe_success():
    session_id = (request.args.get("session_id") or "").strip()
    paid, error = load_stripe_session(session_id)
    if error or not paid or paid.get("payment_status") != "paid":
        flash(error or "Card payment was not completed. No order was saved.", "error")
        return redirect(url_for("checkout_summary"))
    snapshot = pending_payment("stripe", session_id) or snapshot_from_stripe(paid)
    paid_amount = int(paid.get("amount_total") or 0)
    paid_currency = (paid.get("currency") or "").upper()
    if not snapshot.get("email"):
        flash(f"Payment received, but the checkout expired. Contact support with reference stripe:{session_id}.", "error")
        return redirect(url_for("home"))
    if paid_amount != minor_units(snapshot["charge_amount"]) or paid_currency != snapshot["currency"]:
        flash(f"Payment received, but it did not match the checkout. Contact support with reference stripe:{session_id}.", "error")
        return redirect(url_for("home"))
    return finish_paid_order(snapshot, f"stripe:{session_id}", snapshot["charge_amount"], snapshot["currency"])


@app.route("/checkout/stripe/cancel")
def checkout_stripe_cancel():
    session.pop("payment_pending", None)
    session.modified = True
    flash("Card payment was cancelled. Your cart is still here.", "error")
    return redirect(url_for("checkout_summary"))


@app.route("/checkout/paypal/return")
def checkout_paypal_return():
    order_id = (request.args.get("token") or "").strip()
    snapshot = pending_payment("paypal", order_id)
    if not snapshot:
        flash("PayPal payment was not completed. No order was saved.", "error")
        return redirect(url_for("checkout_summary"))
    captured, error = capture_paypal_order(order_id)
    if error or not captured or (captured.get("status") or "") != "COMPLETED":
        flash(error or "PayPal payment was not completed. No order was saved.", "error")
        return redirect(url_for("checkout_summary"))
    capture_id, amount, currency = paypal_capture_amount(captured)
    if not capture_id or currency != snapshot["currency"] or not amounts_match(snapshot["charge_amount"], amount):
        flash(f"The PayPal payment did not match this order. Contact support with reference paypal:{order_id}.", "error")
        return redirect(url_for("home"))
    return finish_paid_order(snapshot, f"paypal:{capture_id}", amount, currency)


@app.route("/checkout/paypal/cancel")
def checkout_paypal_cancel():
    session.pop("payment_pending", None)
    session.modified = True
    flash("PayPal payment was cancelled. Your cart is still here.", "error")
    return redirect(url_for("checkout_summary"))


def firebase_public_config():
    api_key = (os.environ.get("FIREBASE_API_KEY") or "").strip()
    auth_domain = (os.environ.get("FIREBASE_AUTH_DOMAIN") or "").strip()
    project_id = (os.environ.get("FIREBASE_PROJECT_ID") or "").strip()
    app_id = (os.environ.get("FIREBASE_APP_ID") or "").strip()
    if not (api_key and auth_domain and project_id and app_id):
        return None
    config = {
        "apiKey": api_key,
        "authDomain": auth_domain,
        "projectId": project_id,
        "appId": app_id,
    }
    bucket = (os.environ.get("FIREBASE_STORAGE_BUCKET") or "").strip()
    sender = (os.environ.get("FIREBASE_MESSAGING_SENDER_ID") or "").strip()
    if bucket:
        config["storageBucket"] = bucket
    if sender:
        config["messagingSenderId"] = sender
    measurement = (os.environ.get("FIREBASE_MEASUREMENT_ID") or "").strip()
    if measurement:
        config["measurementId"] = measurement
    return config


def firebase_admin_app():
    try:
        import firebase_admin
        from firebase_admin import credentials
    except ImportError:
        return None
    try:
        return firebase_admin.get_app()
    except ValueError:
        pass
    raw = (os.environ.get("FIREBASE_SERVICE_ACCOUNT_JSON") or "").strip()
    path = (os.environ.get("FIREBASE_SERVICE_ACCOUNT_FILE") or "").strip()
    if path and not os.path.isabs(path):
        path = os.path.join(BASE_DIR, path)
    try:
        if raw:
            cred = credentials.Certificate(json.loads(raw))
        elif path and os.path.isfile(path):
            cred = credentials.Certificate(path)
        else:
            return None
        return firebase_admin.initialize_app(cred)
    except (ValueError, OSError, json.JSONDecodeError):
        return None


def firebase_admin_ready():
    return firebase_admin_app() is not None


def verify_firebase_id_token(token):
    if firebase_admin_ready():
        from firebase_admin import auth as firebase_auth

        return firebase_auth.verify_id_token(token)
    config = firebase_public_config()
    if not config:
        raise RuntimeError("Firebase is not configured.")
    from urllib.parse import quote

    url = "https://identitytoolkit.googleapis.com/v1/accounts:lookup?key=" + quote(config["apiKey"])
    body = json.dumps({"idToken": token}).encode()
    req = urllib.request.Request(url, data=body, headers={"Content-Type": "application/json"}, method="POST")
    try:
        with urllib.request.urlopen(req, timeout=15) as response:
            payload = json.loads(response.read().decode())
    except urllib.error.HTTPError as exc:
        raise ValueError(exc.read().decode(errors="ignore") or "invalid token") from exc
    accounts = payload.get("users") or []
    if not accounts:
        raise ValueError("no user")
    account = accounts[0]
    provider = "password"
    for info in account.get("providerUserInfo") or []:
        provider = (info.get("providerId") or provider)[:40]
        break
    return {
        "uid": account.get("localId") or "",
        "email": account.get("email") or "",
        "email_verified": bool(account.get("emailVerified")),
        "name": account.get("displayName") or "",
        "firebase": {"sign_in_provider": provider},
    }


def same_site_next(value, default):
    target = (value or "").strip()
    if target.startswith("/") and not target.startswith("//") and "://" not in target:
        return target
    return default


def shopper_from_firebase(decoded):
    uid = (decoded.get("uid") or "").strip()
    email = (decoded.get("email") or "").strip().lower()[:120]
    if not uid or not email or "@" not in email:
        return None, "This sign-in has no email address."
    if not decoded.get("email_verified"):
        return None, "Verify your email first. Open the message from Firebase, then sign in again."
    provider = ((decoded.get("firebase") or {}).get("sign_in_provider") or "password")[:40]
    name = (decoded.get("name") or email.split("@", 1)[0])[:100]
    db = get_db()
    user = db.execute("SELECT * FROM users WHERE firebase_uid=?", (uid,)).fetchone()
    if not user:
        user = db.execute("SELECT * FROM users WHERE email=?", (email,)).fetchone()
        if user and user.get("firebase_uid") and user["firebase_uid"] != uid:
            return None, "That email is already linked to a different sign-in."
        if user:
            db.execute(
                "UPDATE users SET firebase_uid=?, auth_provider=? WHERE id=?",
                (uid, provider, user["id"]),
            )
        else:
            db.execute(
                """
                INSERT INTO users (name, email, password_hash, created_at, firebase_uid, auth_provider)
                VALUES (?,?,?,?,?,?)
                """,
                (name, email, generate_password_hash(secrets.token_urlsafe(32)), datetime.utcnow().isoformat(), uid, provider),
            )
        db.commit()
        user = db.execute("SELECT * FROM users WHERE firebase_uid=?", (uid,)).fetchone()
    elif user.get("auth_provider") != provider:
        db.execute("UPDATE users SET auth_provider=? WHERE id=?", (provider, user["id"]))
        db.commit()
        user = db.execute("SELECT * FROM users WHERE id=?", (user["id"],)).fetchone()
    if not user:
        return None, "The shop could not open your profile."
    session["user_id"] = user["id"]
    save_checkout(guest=False, name=user.get("name") or name, email=user.get("email") or email)
    return user, None


@app.post("/auth/firebase")
def auth_firebase():
    if not firebase_public_config():
        return jsonify(ok=False, error="Firebase web keys are not configured."), 503
    if login_locked("shopper"):
        return jsonify(ok=False, error="Too many sign-in attempts. Try again later."), 429
    if not csrf_ok():
        return jsonify(ok=False, error="Refresh the page and try again."), 400
    payload = request.get_json(silent=True) or {}
    token = (payload.get("id_token") or "").strip()
    if not token:
        return jsonify(ok=False, error="Missing sign-in token."), 400
    try:
        decoded = verify_firebase_id_token(token)
    except Exception:
        record_login_failure("shopper")
        return jsonify(ok=False, error="That sign-in could not be verified. Try again."), 401
    try:
        user, error = shopper_from_firebase(decoded)
    except IntegrityError:
        rollback_db()
        return jsonify(ok=False, error="An account with that email already exists. Sign in instead."), 409
    if error or not user:
        return jsonify(ok=False, error=error or "Sign-in failed."), 403
    clear_login_failures("shopper")
    return jsonify(ok=True, redirect=same_site_next(payload.get("next"), url_for("profile")))


@app.route("/register", methods=["GET", "POST"])
def register():
    next_url = safe_next(url_for("profile"))
    if session.get("user_id"):
        return redirect(next_url)
    firebase = firebase_public_config()
    if firebase:
        return render_template(
            "auth_register.html",
            next=next_url,
            firebase=firebase,
            firebase_server=True,
        )
    if request.method == "POST":
        name = request.form.get("name", "").strip()[:100]
        email = request.form.get("email", "").strip().lower()[:120]
        password = request.form.get("password", "")
        if not name or not email or len(password) < 6:
            flash("Enter your name, email, and a password with at least 6 characters.", "error")
        else:
            try:
                db = get_db()
                db.execute(
                    "INSERT INTO users (name,email,password_hash,created_at) VALUES (?,?,?,?)",
                    (name, email, generate_password_hash(password), datetime.utcnow().isoformat()),
                )
                db.commit()
                user = db.execute("SELECT id FROM users WHERE email=?", (email,)).fetchone()
                session["user_id"] = user["id"]
                save_checkout(guest=False, name=name, email=email)
                flash("Your profile is ready.", "success")
                return redirect(next_url)
            except IntegrityError:
                flash("An account with that email already exists. Please sign in.", "error")
    return render_template("auth_register.html", next=next_url, firebase=None, firebase_server=False)


@app.route("/login", methods=["GET", "POST"])
def login():
    next_url = safe_next(url_for("profile"))
    firebase = firebase_public_config()
    signed_out = request.args.get("signed_out") == "1"
    if session.get("user_id") and not signed_out:
        return redirect(next_url)
    if firebase:
        return render_template(
            "auth_login.html",
            next=next_url,
            firebase=firebase,
            firebase_server=True,
            signed_out=signed_out,
        )
    if request.method == "POST":
        email = request.form.get("email", "").strip().lower()
        password = request.form.get("password", "")
        user = get_db().execute("SELECT * FROM users WHERE email=?", (email,)).fetchone()
        if user and check_password_hash(user["password_hash"], password):
            if user.get("firebase_uid"):
                flash("This profile uses Firebase. Sign in with email, Google, or Facebook.", "error")
                return redirect(url_for("login", next=next_url))
            session["user_id"] = user["id"]
            save_checkout(guest=False, name=user.get("name") or "", email=user.get("email") or "")
            flash("Welcome back.", "success")
            return redirect(next_url)
        flash("Incorrect email or password.", "error")
    return render_template("auth_login.html", next=next_url, firebase=None, firebase_server=False, signed_out=False)


@app.post("/logout")
def logout():
    session.pop("user_id", None)
    flash("You have been signed out.", "success")
    if firebase_public_config():
        return redirect(url_for("login", signed_out=1))
    return redirect(url_for("home"))


@app.route("/profile", methods=["GET", "POST"])
@login_required
def profile():
    user = current_user()
    if request.method == "POST":
        name = request.form.get("name", "").strip()[:100]
        email = request.form.get("email", "").strip().lower()[:120]
        password = request.form.get("password", "")
        if user.get("firebase_uid"):
            email = (user.get("email") or "").strip().lower()
            password = ""
        if not name or not email:
            flash("Name and email are required.", "error")
        else:
            try:
                db = get_db()
                if password and len(password) < 6:
                    flash("New password must be at least 6 characters.", "error")
                else:
                    country = request.form.get("country", "").strip()
                    if country not in ZONE_NAMES:
                        country = user.get("country") or customer_zone_name()
                    apply_region(country)
                    if password:
                        db.execute(
                            "UPDATE users SET name=?, email=?, password_hash=?, country=? WHERE id=?",
                            (name, email, generate_password_hash(password), country, user["id"]),
                        )
                    else:
                        db.execute("UPDATE users SET name=?, email=?, country=? WHERE id=?", (name, email, country, user["id"]))
                    db.commit()
                    flash("Profile updated.", "success")
                    return redirect(url_for("profile"))
            except IntegrityError:
                flash("That email is already in use.", "error")
        user = current_user()
    db = get_db()
    orders = [order_record(row) for row in db.execute("SELECT * FROM orders WHERE email=? ORDER BY id DESC", (user["email"],)).fetchall()]
    listings = [listing_view(row) for row in db.execute("SELECT * FROM listings WHERE user_id=? ORDER BY id DESC", (user["id"],)).fetchall()]
    return render_template(
        "profile.html",
        user=user,
        orders=orders,
        listings=listings,
        firebase=firebase_public_config() if user.get("firebase_uid") else None,
    )


@app.route("/sell")
@login_required
def sell():
    user = current_user()
    if request.args.get("seller") == "no":
        flash("You chose not to sell your products on our website.", "success")
    if request.args.get("dropship") == "no":
        flash("You chose not to dropship our products.", "success")
    applications = [
        partner_application_view(row)
        for row in get_db().execute(
            "SELECT * FROM partner_applications WHERE user_id=? ORDER BY id DESC",
            (user["id"],),
        ).fetchall()
    ]
    return render_template("sell.html", user=user, applications=applications)


@app.route("/sell/seller", methods=["GET", "POST"])
@login_required
def sell_seller():
    user = current_user()
    if request.method == "POST":
        fields = {
            "full_name": request.form.get("full_name", "").strip()[:100],
            "email": request.form.get("email", "").strip()[:120],
            "contact": request.form.get("contact", "").strip()[:40],
            "country": request.form.get("country", "").strip()[:80],
            "product_name": request.form.get("product_name", "").strip()[:100],
            "product_type": request.form.get("product_type", "").strip(),
        }
        if not all(fields.values()) or fields["product_type"] not in PRODUCT_TYPES:
            flash("Please complete every field and choose a product type.", "error")
        else:
            db = get_db()
            try:
                cursor = db.execute(
                    """
                    INSERT INTO partner_applications (
                        user_id, kind, full_name, email, contact, country,
                        product_name, product_type, created_at, status
                    ) VALUES (?,?,?,?,?,?,?,?,?,?)
                    RETURNING id
                    """,
                    (
                        user["id"],
                        "seller",
                        fields["full_name"],
                        fields["email"],
                        fields["contact"],
                        fields["country"],
                        fields["product_name"],
                        fields["product_type"],
                        datetime.utcnow().isoformat(),
                        "pending",
                    ),
                )
                application_id = cursor.fetchone()["id"]
                save_partner_images(application_id)
                db.commit()
                flash("Your application was submitted. Please wait for admin approval.", "success")
                return redirect(url_for("sell"))
            except ValueError as error:
                rollback_db()
                flash(str(error), "error")
            except IntegrityError as error:
                rollback_db()
                flash(friendly_product_error(error), "error")
    return render_template(
        "sell_seller.html",
        user=user,
        product_types=PRODUCT_TYPES,
        countries=ZONE_NAMES,
    )


@app.route("/sell/dropship", methods=["GET", "POST"])
@login_required
def sell_dropship():
    user = current_user()
    if request.method == "POST":
        fields = {
            "interest": request.form.get("interest", "").strip()[:300],
            "full_name": request.form.get("full_name", "").strip()[:100],
            "sell_country": request.form.get("sell_country", "").strip()[:80],
            "platforms": request.form.get("platforms", "").strip()[:200],
            "store_link": request.form.get("store_link", "").strip()[:400],
            "email": request.form.get("email", "").strip()[:120],
            "contact": request.form.get("contact", "").strip()[:40],
            "country": request.form.get("country", "").strip()[:80] or request.form.get("sell_country", "").strip()[:80],
        }
        required = ("interest", "full_name", "sell_country", "platforms", "email", "contact")
        if any(not fields[key] for key in required):
            flash("Please complete every required field.", "error")
        else:
            db = get_db()
            try:
                db.execute(
                    """
                    INSERT INTO partner_applications (
                        user_id, kind, full_name, email, contact, country,
                        interest, sell_country, platforms, store_link, created_at, status
                    ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?)
                    """,
                    (
                        user["id"],
                        "dropshipper",
                        fields["full_name"],
                        fields["email"],
                        fields["contact"],
                        fields["country"] or fields["sell_country"],
                        fields["interest"],
                        fields["sell_country"],
                        fields["platforms"],
                        fields["store_link"],
                        datetime.utcnow().isoformat(),
                        "pending",
                    ),
                )
                db.commit()
                flash("Your dropshipper application was submitted. Please wait for admin approval.", "success")
                return redirect(url_for("sell"))
            except IntegrityError as error:
                rollback_db()
                flash(friendly_product_error(error), "error")
    return render_template("sell_dropship.html", user=user, countries=ZONE_NAMES)


@app.route("/contact", methods=["GET", "POST"])
@login_required
def contact():
    user = current_user()
    if request.method == "POST":
        message = request.form.get("message", "").strip()
        if not message:
            flash("Please enter your message.", "error")
        else:
            get_db().execute(
                "INSERT INTO contacts (user_id,name,email,message,created_at) VALUES (?,?,?,?,?)",
                (user["id"], user["name"], user["email"], message, datetime.utcnow().isoformat()),
            )
            get_db().commit()
            flash("Your message has been sent to our support team.", "success")
            return redirect(url_for("contact"))
    return render_template("contact.html", user=user)


@app.post("/preferences")
def preferences():
    currency, language = request.form.get("currency"), request.form.get("language")
    region = request.form.get("region", "").strip()
    old_currency = session.get("currency")
    old_language = session.get("language")
    old_region = session.get("region")
    session["locale_chosen"] = True
    if currency in CURRENCIES:
        session["currency"] = currency
    if language in LANGUAGES:
        session["language"] = language
        if language == "ur":
            session["currency"] = "PKR"
    if region in ZONE_NAMES and region != old_region:
        apply_region(region)
    elif currency in CURRENCIES and currency != old_currency:
        inferred = "Germany" if currency == "EUR" and session.get("language") == "de" else CURRENCY_TO_ZONE.get(currency)
        if inferred:
            session["region"] = inferred
    elif language in LANGUAGES and language != old_language:
        if language == "ur":
            session["region"] = "Pakistan"
        elif LANGUAGE_TO_ZONE.get(language):
            session["region"] = LANGUAGE_TO_ZONE[language]
            session["currency"] = ZONE_CURRENCY.get(session["region"], session.get("currency", "EUR"))
    return redirect(request.referrer or url_for("home"))


@app.get("/api/products")
def api_products():
    return jsonify(visible_catalog(get_db().execute(f"SELECT {SHOP_PRODUCT_COLUMNS} FROM products WHERE active=1").fetchall()))


@app.route("/admin/login", methods=["GET", "POST"])
def admin_login():
    if request.method == "POST":
        if login_locked("admin-login"):
            flash("Too many sign-in attempts. Wait 15 minutes and try again.", "error")
        else:
            username = request.form.get("username", "")
            password = request.form.get("password", "")
            password_hash = current_admin_password_hash()
            if not password_hash:
                flash("Admin password hash is not configured. Set ADMIN_PASSWORD_HASH in .env.", "error")
            elif username == ADMIN_USERNAME and check_password_hash(password_hash, password):
                clear_login_failures("admin-login")
                session["is_admin"] = True
                session["admin_seen_at"] = time.time()
                session["_csrf"] = secrets.token_urlsafe(32)
                flash("Welcome to the admin dashboard.", "success")
                return redirect(url_for("admin_dashboard"))
            else:
                record_login_failure("admin-login")
                flash("Incorrect username or password.", "error")
    return render_template("admin_login.html")


@app.route("/admin/forgot-password", methods=["GET", "POST"])
def admin_forgot_password():
    if request.method == "POST":
        if login_locked("admin-reset"):
            flash("Too many reset attempts. Wait 15 minutes and try again.", "error")
            return redirect(url_for("admin_forgot_password"))
        record_login_failure("admin-reset")
        username = request.form.get("username", "").strip()
        if username == ADMIN_USERNAME and current_admin_email():
            token = admin_reset_serializer().dumps(ADMIN_USERNAME)
            reset_url = url_for("admin_reset_password", token=token, _external=True)
            try:
                sent = send_admin_email(
                    "Reset your AR Shopping World admin password",
                    f"Use this link within 1 hour to reset the admin password:\n\n{reset_url}\n",
                )
            except Exception:
                sent = False
            if sent:
                flash("If that admin account exists, a reset email has been sent.", "success")
            elif current_admin_email():
                flash("The reset email could not be sent. Save a Gmail app password in Settings → Email service.", "error")
            else:
                flash("If that admin account exists, a reset email has been sent.", "success")
        else:
            flash("If that admin account exists, a reset email has been sent.", "success")
        return redirect(url_for("admin_forgot_password"))
    return render_template("admin_forgot_password.html")


@app.route("/admin/reset-password/<token>", methods=["GET", "POST"])
def admin_reset_password(token):
    try:
        username = admin_reset_serializer().loads(token, max_age=3600)
    except (BadSignature, SignatureExpired):
        flash("This reset link is invalid or has expired.", "error")
        return redirect(url_for("admin_forgot_password"))
    if username != ADMIN_USERNAME:
        flash("This reset link is invalid or has expired.", "error")
        return redirect(url_for("admin_forgot_password"))
    if request.method == "POST":
        password = request.form.get("password", "")
        confirm = request.form.get("confirm_password", "")
        if len(password) < ADMIN_PASSWORD_MIN:
            flash(f"New password must be at least {ADMIN_PASSWORD_MIN} characters.", "error")
        elif password != confirm:
            flash("The new passwords do not match.", "error")
        else:
            set_setting("admin_password_hash", generate_password_hash(password))
            flash("Admin password updated. Sign in with the new password.", "success")
            return redirect(url_for("admin_login"))
    return render_template("admin_reset_password.html")


@app.post("/admin/logout")
@admin_required
def admin_logout():
    session.pop("is_admin", None)
    session.pop("admin_seen_at", None)
    flash("You have been signed out.", "success")
    return redirect(url_for("home"))


@app.get("/admin")
@admin_required
def admin_dashboard():
    db = get_db()
    all_orders = db.execute("SELECT * FROM orders ORDER BY id DESC").fetchall()
    order_count = len(all_orders)
    q = (request.args.get("q") or "").strip()
    all_products = [product(row) for row in db.execute("SELECT * FROM products ORDER BY id DESC").fetchall()]
    live_products = [item for item in all_products if not item.get("is_draft") and staff_product_matches(item, q)]
    draft_products = [
        item
        for item in all_products
        if item.get("is_draft") and (item.get("listed_by") or "admin") == "admin" and staff_product_matches(item, q)
    ]
    return render_template(
        "admin_dashboard.html",
        products=live_products,
        draft_products=draft_products,
        product_search=q,
        orders=all_orders[:20],
        order_count=order_count,
        sales=build_sales_overview(all_orders),
        reviews=db.execute(
            """
            SELECT reviews.*, products.name AS product_name
            FROM reviews JOIN products ON products.id=reviews.product_id
            ORDER BY reviews.id DESC LIMIT 20
            """
        ).fetchall(),
        contacts=db.execute("SELECT * FROM contacts ORDER BY id DESC LIMIT 20").fetchall(),
        listings=[listing_view(row) for row in db.execute("SELECT * FROM listings ORDER BY id DESC LIMIT 50").fetchall()],
        categories=db.execute("SELECT * FROM categories ORDER BY name").fetchall(),
        shipping_zones=load_shipping_zones(),
        faqs=db.execute("SELECT * FROM faqs ORDER BY sort_order, id").fetchall(),
        pending_password_requests=len(pending_pl_password_requests()),
        listing_team=listing_team_monitor(),
        security_notes=admin_security_notes(),
    )


@app.get("/admin/listing-team/<username>")
@admin_required
def admin_listing_team_member(username):
    member = listing_team_member(username)
    if not member:
        abort(404)
    q = (request.args.get("q") or "").strip()
    products = [
        product(row)
        for row in get_db().execute(
            "SELECT * FROM products WHERE LOWER(listed_by)=LOWER(?) ORDER BY id DESC",
            (member["username"],),
        ).fetchall()
    ]
    products = [item for item in products if staff_product_matches(item, q)]
    return render_template(
        "admin_listing_team.html",
        member=member,
        products=products,
        product_search=q,
    )


@app.route("/admin/settings", methods=["GET", "POST"])
@admin_required
def admin_settings():
    if request.method == "POST":
        action = request.form.get("action", "").strip()
        if action == "email":
            email = request.form.get("admin_email", "").strip().lower()[:120]
            if not admin_password_ok(request.form.get("current_password", "")):
                flash("Current admin password is incorrect.", "error")
            elif email and "@" not in email:
                flash("Enter a valid admin email.", "error")
            else:
                set_setting("admin_email", email)
                flash("Admin email saved.", "success")
        elif action == "password":
            current = request.form.get("current_password", "")
            password = request.form.get("password", "")
            confirm = request.form.get("confirm_password", "")
            password_hash = current_admin_password_hash()
            if not password_hash or not check_password_hash(password_hash, current):
                flash("Current admin password is incorrect.", "error")
            elif len(password) < ADMIN_PASSWORD_MIN:
                flash(f"New password must be at least {ADMIN_PASSWORD_MIN} characters.", "error")
            elif password != confirm:
                flash("The new passwords do not match.", "error")
            else:
                set_setting("admin_password_hash", generate_password_hash(password))
                flash("Admin password updated.", "success")
        elif action == "merchants":
            if not admin_password_ok(request.form.get("current_password", "")):
                flash("Current admin password is incorrect.", "error")
            else:
                payload, error = merchant_payload_from_form()
                if error:
                    flash(error, "error")
                else:
                    sent, error = start_merchant_verify(payload)
                    if sent:
                        flash("A verification code was sent to the admin email. Enter the code and your password to apply the merchant changes.", "success")
                    else:
                        flash(error, "error")
        elif action == "merchants_resend":
            pending = pending_merchant_verify()
            if not pending:
                flash("There is no merchant change waiting for verification.", "error")
            elif not admin_password_ok(request.form.get("current_password", "")):
                flash("Current admin password is incorrect.", "error")
            else:
                sent, error = start_merchant_verify(pending.get("payload") or {})
                if sent:
                    flash("A new verification code was sent to the admin email.", "success")
                else:
                    flash(error, "error")
        elif action == "merchants_confirm":
            pending = pending_merchant_verify()
            code = request.form.get("verify_code", "").strip()
            if not pending:
                flash("The merchant verification code has expired. Start the change again.", "error")
            elif not admin_password_ok(request.form.get("current_password", "")):
                flash("Current admin password is incorrect.", "error")
            elif not code or not check_password_hash(pending.get("code_hash") or "", code):
                flash("The verification code is incorrect.", "error")
            else:
                apply_merchant_payload(pending.get("payload") or {})
                session.pop("merchant_verify", None)
                session.modified = True
                flash("Merchant details saved.", "success")
        elif action == "merchants_cancel":
            session.pop("merchant_verify", None)
            session.modified = True
            flash("Merchant change cancelled.", "success")
        elif action == "mail":
            if not admin_password_ok(request.form.get("current_password", "")):
                flash("Current admin password is incorrect.", "error")
            else:
                server = request.form.get("mail_server", "").strip()[:120] or "smtp.gmail.com"
                port = request.form.get("mail_port", "").strip() or "587"
                username = request.form.get("mail_username", "").strip()[:120]
                sender = request.form.get("mail_from", "").strip()[:120]
                password = request.form.get("mail_password", "").strip()
                try:
                    if int(port) < 1:
                        raise ValueError("port")
                except ValueError:
                    flash("Enter a valid mail port, such as 587.", "error")
                else:
                    set_setting("mail_server", server)
                    set_setting("mail_port", str(port))
                    set_setting("mail_username", username)
                    set_setting("mail_from", sender)
                    set_setting("mail_use_tls", "1")
                    if password:
                        set_setting("mail_password", password)
                    flash("Email service saved. Send a test email to confirm Gmail accepts the app password.", "success")
        elif action == "mail_test":
            if not admin_password_ok(request.form.get("current_password", "")):
                flash("Current admin password is incorrect.", "error")
            else:
                sent, error = send_admin_email_result(
                    "Test email — AR Shopping World",
                    "This is a test email from AR Shopping World. Mail is working.\n",
                )
                if sent:
                    flash(f"Test email sent to {mask_email(current_admin_email())}.", "success")
                else:
                    flash(error or "The test email could not be sent.", "error")
        elif action == "pl_create":
            username = request.form.get("pl_username", "")
            display_name = request.form.get("pl_display_name", "")
            password = request.form.get("pl_password", "")
            confirm = request.form.get("pl_confirm_password", "")
            if len(password) < 6:
                flash("Listing team password must be at least 6 characters.", "error")
            elif password != confirm:
                flash("The listing team passwords do not match.", "error")
            else:
                try:
                    existing = find_pl_user(username)
                    upsert_pl_user(username, display_name, password)
                    if existing:
                        flash(f"Listing team account updated for {username.strip().lower()}.", "success")
                    else:
                        flash(f"Listing team account created for {username.strip().lower()}. They can sign in at /pl/login.", "success")
                except ValueError as error:
                    flash(str(error), "error")
        elif action == "pl_set_password":
            user_id = request.form.get("pl_user_id", type=int)
            password = request.form.get("pl_password", "")
            confirm = request.form.get("pl_confirm_password", "")
            row = get_db().execute("SELECT * FROM pl_users WHERE id=?", (user_id,)).fetchone() if user_id else None
            if not row:
                flash("That listing team account was not found.", "error")
            elif len(password) < 6:
                flash("Listing team password must be at least 6 characters.", "error")
            elif password != confirm:
                flash("The listing team passwords do not match.", "error")
            else:
                get_db().execute(
                    "UPDATE pl_users SET password_hash=? WHERE id=?",
                    (generate_password_hash(password), row["id"]),
                )
                get_db().commit()
                flash(f"Password updated for {row['username']}. They can sign in with the new password.", "success")
        elif action == "pl_delete":
            user_id = request.form.get("pl_user_id", type=int)
            row = get_db().execute("SELECT * FROM pl_users WHERE id=?", (user_id,)).fetchone() if user_id else None
            if not admin_password_ok(request.form.get("current_password", "")):
                flash("Current admin password is incorrect.", "error")
            elif not row:
                flash("That listing team account was not found.", "error")
            else:
                get_db().execute("DELETE FROM pl_users WHERE id=?", (row["id"],))
                get_db().commit()
                flash(f"Listing team account {row['username']} deleted.", "success")
        elif action == "footer":
            try:
                save_footer_from_form()
                flash("Footer saved. Shoppers will see the new text on the next page load.", "success")
            except ValueError as error:
                flash(str(error), "error")
        return redirect(url_for("admin_settings"))
    requests = get_db().execute("SELECT * FROM pl_password_requests ORDER BY id DESC LIMIT 30").fetchall()
    return render_template(
        "admin_settings.html",
        admin_username=ADMIN_USERNAME,
        admin_email=current_admin_email(),
        password_requests=requests,
        pl_users=list_pl_users(),
        pl_env_username=(PL_USERNAME or "").strip(),
        merchants=merchant_settings(),
        merchant_verify=pending_merchant_verify(),
        mail=mail_config(),
        mail_ready=mail_ready(),
        footer_settings=footer_settings_for_admin(),
        **merchant_ready_flags(),
    )


@app.post("/admin/settings/pl-password/<int:request_id>/approve")
@admin_required
def admin_approve_pl_password(request_id):
    db = get_db()
    row = db.execute("SELECT * FROM pl_password_requests WHERE id=?", (request_id,)).fetchone()
    if not row or row["status"] != "pending":
        flash("That password request is no longer pending.", "error")
        return redirect(url_for("admin_settings"))
    existing = find_pl_user(row["username"])
    display_name = row["display_name"] or (existing["display_name"] if existing else row["username"])
    if existing:
        db.execute(
            "UPDATE pl_users SET password_hash=?, display_name=? WHERE id=?",
            (row["password_hash"], display_name, existing["id"]),
        )
    else:
        db.execute(
            "INSERT INTO pl_users (username, display_name, password_hash, created_at) VALUES (?,?,?,?)",
            (row["username"], display_name, row["password_hash"], datetime.utcnow().isoformat()),
        )
    db.execute(
        "UPDATE pl_password_requests SET status='approved', reviewed_at=? WHERE id=?",
        (datetime.utcnow().isoformat(), request_id),
    )
    db.commit()
    flash(f"Password change approved for {row['username']}.", "success")
    return redirect(url_for("admin_settings"))


@app.post("/admin/settings/pl-password/<int:request_id>/reject")
@admin_required
def admin_reject_pl_password(request_id):
    db = get_db()
    row = db.execute("SELECT * FROM pl_password_requests WHERE id=?", (request_id,)).fetchone()
    if not row or row["status"] != "pending":
        flash("That password request is no longer pending.", "error")
        return redirect(url_for("admin_settings"))
    db.execute(
        "UPDATE pl_password_requests SET status='rejected', reviewed_at=? WHERE id=?",
        (datetime.utcnow().isoformat(), request_id),
    )
    db.commit()
    flash(f"Password change rejected for {row['username']}.", "success")
    return redirect(url_for("admin_settings"))


@app.get("/admin/orders")
@admin_required
def admin_orders():
    db = get_db()
    query = (request.args.get("q") or "").strip()
    if query:
        like = f"%{query}%"
        rows = db.execute(
            """
            SELECT * FROM orders
            WHERE CAST(id AS TEXT) = ?
               OR CAST(id AS TEXT) ILIKE ?
               OR customer_name ILIKE ?
               OR email ILIKE ?
            ORDER BY id DESC
            """,
            (query, like, like, like),
        ).fetchall()
    else:
        rows = db.execute("SELECT * FROM orders ORDER BY id DESC").fetchall()
    return render_template(
        "admin_orders.html",
        orders=[order_record(row) for row in rows],
        query=query,
        order_count=db.execute("SELECT COUNT(*) AS n FROM orders").fetchone()["n"],
    )


@app.route("/admin/orders/<int:order_id>", methods=["GET", "POST"])
@admin_required
def admin_order_view(order_id):
    db = get_db()
    row = db.execute("SELECT * FROM orders WHERE id=?", (order_id,)).fetchone()
    if not row:
        abort(404)
    if request.method == "POST":
        status = (request.form.get("status") or "").strip()
        carrier = (request.form.get("tracking_carrier") or "").strip().lower()
        number = (request.form.get("tracking_number") or "").strip()[:80]
        if carrier and carrier not in TRACKING_CARRIERS:
            carrier = ""
        if status not in ORDER_STATUSES:
            flash("Choose a valid order status.", "error")
        elif status == "shipped" and (not carrier or not number):
            flash("Shipped orders need a DHL or Hermes tracking number.", "error")
        else:
            db.execute(
                "UPDATE orders SET status=?, tracking_carrier=?, tracking_number=? WHERE id=?",
                (status, carrier or None, number, order_id),
            )
            db.commit()
            flash("Order status updated.", "success")
            return redirect(url_for("admin_order_view", order_id=order_id))
    return render_template(
        "admin_order_view.html",
        order=order_record(row),
        statuses=ORDER_STATUSES,
        carriers=TRACKING_CARRIERS,
    )


@app.post("/admin/listing/<int:listing_id>/approve")
@admin_required
def admin_listing_approve(listing_id):
    try:
        product_id = approve_seller_listing(listing_id)
        flash(f"Listing approved and published to the shop as product #{product_id}.", "success")
    except ValueError as error:
        flash(str(error), "error")
    return redirect(url_for("admin_dashboard"))


@app.post("/admin/listing/<int:listing_id>/reject")
@admin_required
def admin_listing_reject(listing_id):
    get_db().execute(
        "UPDATE listings SET status=?, reviewed_at=? WHERE id=?",
        ("rejected", datetime.utcnow().isoformat(), listing_id),
    )
    get_db().commit()
    flash("Listing rejected.", "success")
    return redirect(url_for("admin_dashboard"))


@app.get("/admin/partners")
@admin_required
def admin_partners():
    applications = [
        partner_application_view(row)
        for row in get_db().execute("SELECT * FROM partner_applications ORDER BY id DESC").fetchall()
    ]
    return render_template("admin_partners.html", applications=applications)


@app.post("/admin/partners/<int:application_id>/approve")
@admin_required
def admin_partner_approve(application_id):
    get_db().execute(
        "UPDATE partner_applications SET status=?, reviewed_at=? WHERE id=?",
        ("approved", datetime.utcnow().isoformat(), application_id),
    )
    get_db().commit()
    flash("Partner application approved.", "success")
    return redirect(url_for("admin_partners"))


@app.post("/admin/partners/<int:application_id>/reject")
@admin_required
def admin_partner_reject(application_id):
    get_db().execute(
        "UPDATE partner_applications SET status=?, reviewed_at=? WHERE id=?",
        ("rejected", datetime.utcnow().isoformat(), application_id),
    )
    get_db().commit()
    flash("Partner application rejected.", "success")
    return redirect(url_for("admin_partners"))


@app.route("/admin/faqs", methods=["GET", "POST"])
@admin_required
def admin_faqs():
    db = get_db()
    if request.method == "POST":
        action = request.form.get("action")
        question = request.form.get("question", "").strip()[:200]
        answer = request.form.get("answer", "").strip()[:2000]
        try:
            faq_id = int(request.form.get("faq_id", 0) or 0)
        except ValueError:
            faq_id = 0
        if action == "add" and question and answer:
            next_order = db.execute("SELECT COALESCE(MAX(sort_order),0)+1 AS n FROM faqs").fetchone()["n"]
            db.execute("INSERT INTO faqs (question,answer,sort_order) VALUES (?,?,?)", (question, answer, next_order))
            db.commit()
            flash("FAQ added.", "success")
        elif action == "save" and faq_id and question and answer:
            db.execute("UPDATE faqs SET question=?, answer=? WHERE id=?", (question, answer, faq_id))
            db.commit()
            flash("FAQ updated.", "success")
        elif action == "delete" and faq_id:
            db.execute("DELETE FROM faqs WHERE id=?", (faq_id,))
            db.commit()
            flash("FAQ deleted.", "success")
        else:
            flash("Please complete the question and answer.", "error")
        return redirect(url_for("admin_faqs"))
    return render_template(
        "manage_faqs.html",
        faqs=db.execute("SELECT * FROM faqs ORDER BY sort_order, id").fetchall(),
        back_url=url_for("admin_dashboard"),
    )


@app.route("/admin/brands", methods=["GET", "POST"])
@admin_required
def admin_brands():
    if request.method == "POST":
        handle_brand_form()
        return redirect(url_for("admin_brands"))
    return render_template(
        "manage_brands.html",
        brands=get_db().execute("SELECT * FROM brands ORDER BY name").fetchall(),
        back_url=url_for("admin_dashboard"),
        save_url=url_for("admin_brands"),
    )


@app.route("/admin/main-categories", methods=["GET", "POST"])
@admin_required
def admin_main_categories():
    if request.method == "POST":
        handle_main_category_form()
        return redirect(url_for("admin_main_categories"))
    return render_template(
        "manage_main_categories.html",
        categories=get_db().execute("SELECT * FROM main_categories ORDER BY id").fetchall(),
        back_url=url_for("admin_dashboard"),
        save_url=url_for("admin_main_categories"),
    )


@app.route("/admin/sub-categories", methods=["GET", "POST"])
@admin_required
def admin_sub_categories():
    if request.method == "POST":
        handle_sub_category_form()
        return redirect(url_for("admin_sub_categories"))
    return render_template(
        "manage_sub_categories.html",
        categories=get_db().execute("SELECT * FROM sub_categories ORDER BY main_category, id").fetchall(),
        main_categories=load_main_categories(),
        back_url=url_for("admin_dashboard"),
        save_url=url_for("admin_sub_categories"),
    )


@app.route("/admin/sub-categories-2", methods=["GET", "POST"])
@admin_required
def admin_sub_categories_2():
    if request.method == "POST":
        handle_sub_category_2_form()
        return redirect(url_for("admin_sub_categories_2"))
    return render_template(
        "manage_sub_categories_2.html",
        categories=get_db().execute("SELECT * FROM sub_categories_2 ORDER BY main_category, sub_category, id").fetchall(),
        main_categories=load_main_categories(),
        sub_categories=load_sub_categories(),
        back_url=url_for("admin_dashboard"),
        save_url=url_for("admin_sub_categories_2"),
    )


@app.route("/admin/sub-categories-3", methods=["GET", "POST"])
@admin_required
def admin_sub_categories_3():
    if request.method == "POST":
        handle_sub_category_3_form()
        return redirect(url_for("admin_sub_categories_3"))
    return render_template(
        "manage_sub_categories_3.html",
        categories=get_db().execute(
            "SELECT * FROM sub_categories_3 ORDER BY main_category, sub_category, sub_category_2, id"
        ).fetchall(),
        main_categories=load_main_categories(),
        sub_categories=load_sub_categories(),
        sub_categories_2=load_sub_categories_2(),
        back_url=url_for("admin_dashboard"),
        save_url=url_for("admin_sub_categories_3"),
    )


@app.route("/admin/sub-categories-4", methods=["GET", "POST"])
@admin_required
def admin_sub_categories_4():
    if request.method == "POST":
        handle_sub_category_4_form()
        return redirect(url_for("admin_sub_categories_4"))
    return render_template(
        "manage_sub_categories_4.html",
        categories=get_db().execute(
            "SELECT * FROM sub_categories_4 ORDER BY main_category, sub_category, sub_category_2, sub_category_3, id"
        ).fetchall(),
        main_categories=load_main_categories(),
        sub_categories=load_sub_categories(),
        sub_categories_2=load_sub_categories_2(),
        sub_categories_3=load_sub_categories_3(),
        back_url=url_for("admin_dashboard"),
        save_url=url_for("admin_sub_categories_4"),
    )


@app.post("/admin/shipping")
@admin_required
def admin_shipping():
    db = get_db()
    try:
        for zone in DEFAULT_SHIPPING_ZONES:
            under = float(request.form.get(f"under_{zone['key']}", 0) or 0)
            over = float(request.form.get(f"over_{zone['key']}", 0) or 0)
            if under < 0 or over < 0:
                raise ValueError("Shipping prices cannot be negative.")
            db.execute(
                """
                INSERT INTO shipping_rates (zone, unit, under_value, over_value)
                VALUES (?,?,?,?)
                ON CONFLICT (zone) DO UPDATE SET under_value=EXCLUDED.under_value, over_value=EXCLUDED.over_value
                """,
                (zone["name"], zone["unit"], under, over),
            )
        db.commit()
        flash("Shipping charges updated.", "success")
    except ValueError:
        flash("Enter valid shipping prices for every region.", "error")
    return redirect(url_for("admin_dashboard") + "#shipping")


@app.post("/admin/categories")
@admin_required
def admin_categories():
    action = request.form.get("action")
    db = get_db()
    if action == "add":
        name = request.form.get("name", "").strip()[:40]
        if not name:
            flash("Category name is required.", "error")
        else:
            try:
                db.execute("INSERT INTO categories (name) VALUES (?)", (name,))
                db.commit()
                flash("Category added.", "success")
            except IntegrityError:
                flash("That category already exists.", "error")
    elif action == "rename":
        category_id = request.form.get("category_id")
        name = request.form.get("name", "").strip()[:40]
        row = db.execute("SELECT * FROM categories WHERE id=?", (category_id,)).fetchone()
        if not row or not name:
            flash("Valid category and new name are required.", "error")
        else:
            try:
                db.execute("UPDATE categories SET name=? WHERE id=?", (name, category_id))
                db.execute("UPDATE products SET category=? WHERE category=?", (name, row["name"]))
                db.commit()
                flash("Category updated.", "success")
            except IntegrityError:
                flash("That category name already exists.", "error")
    elif action == "delete":
        category_id = request.form.get("category_id")
        row = db.execute("SELECT * FROM categories WHERE id=?", (category_id,)).fetchone()
        if not row:
            flash("Category not found.", "error")
        else:
            in_use = db.execute("SELECT COUNT(*) AS count FROM products WHERE category=?", (row["name"],)).fetchone()["count"]
            if in_use:
                flash("Cannot delete a category that still has products.", "error")
            else:
                db.execute("DELETE FROM categories WHERE id=?", (category_id,))
                db.commit()
                flash("Category deleted.", "success")
    return redirect(url_for("admin_dashboard") + "#categories")


def save_named_category(table, name, extra=None):
    name = (name or "").strip()[:40]
    if not name:
        raise ValueError("Category name is required.")
    columns = ["name"]
    values = [name]
    if extra:
        columns.extend(extra.keys())
        values.extend(extra.values())
    get_db().execute(
        f"INSERT INTO {table} ({', '.join(columns)}) VALUES ({', '.join('?' for _ in values)})",
        tuple(values),
    )


def handle_brand_form():
    action = request.form.get("action")
    db = get_db()
    if action == "add":
        name = (request.form.get("name") or "").strip()[:80]
        if not name:
            flash("Brand name is required.", "error")
            return
        try:
            db.execute("INSERT INTO brands (name) VALUES (?)", (name,))
            db.commit()
            flash("Brand added.", "success")
        except IntegrityError:
            db.rollback()
            flash("That brand already exists.", "error")
    elif action == "rename":
        brand_id = request.form.get("brand_id")
        name = (request.form.get("name") or "").strip()[:80]
        row = db.execute("SELECT * FROM brands WHERE id=?", (brand_id,)).fetchone()
        if not row or not name:
            flash("Valid brand and new name are required.", "error")
            return
        try:
            db.execute("UPDATE brands SET name=? WHERE id=?", (name, brand_id))
            db.execute("UPDATE products SET brand=? WHERE brand=?", (name, row["name"]))
            db.commit()
            flash("Brand updated.", "success")
        except IntegrityError:
            db.rollback()
            flash("That brand name already exists.", "error")
    elif action == "delete":
        brand_id = request.form.get("brand_id")
        row = db.execute("SELECT * FROM brands WHERE id=?", (brand_id,)).fetchone()
        if not row:
            flash("Brand not found.", "error")
            return
        in_use = db.execute("SELECT COUNT(*) AS count FROM products WHERE brand=?", (row["name"],)).fetchone()["count"]
        if in_use:
            flash("Cannot delete a brand that is still used on products.", "error")
            return
        db.execute("DELETE FROM brands WHERE id=?", (brand_id,))
        db.commit()
        flash("Brand deleted.", "success")


def handle_main_category_form():
    action = request.form.get("action")
    db = get_db()
    if action == "add":
        try:
            new_name = (request.form.get("name") or "").strip()[:40]
            save_named_category("main_categories", new_name)
            existing_subs = [
                row["name"]
                for row in db.execute("SELECT DISTINCT name FROM sub_categories ORDER BY name").fetchall()
            ]
            for sub_name in existing_subs:
                db.execute(
                    "INSERT INTO sub_categories (name, main_category) VALUES (?,?) ON CONFLICT (name, main_category) DO NOTHING",
                    (sub_name, new_name),
                )
            db.commit()
            flash("Main category added.", "success")
        except ValueError as error:
            flash(str(error), "error")
        except IntegrityError:
            db.rollback()
            flash("That main category already exists.", "error")
    elif action == "rename":
        category_id = request.form.get("category_id")
        name = (request.form.get("name") or "").strip()[:40]
        row = db.execute("SELECT * FROM main_categories WHERE id=?", (category_id,)).fetchone()
        if not row or not name:
            flash("Valid main category and new name are required.", "error")
        else:
            try:
                db.execute("UPDATE main_categories SET name=? WHERE id=?", (name, category_id))
                db.execute("UPDATE products SET main_category=? WHERE main_category=?", (name, row["name"]))
                for product_row in db.execute("SELECT id, main_category, main_categories FROM products").fetchall():
                    names = [item if item != row["name"] else name for item in product_main_names(product_row)]
                    db.execute(
                        "UPDATE products SET main_categories=? WHERE id=?",
                        (json.dumps(names), product_row["id"]),
                    )
                db.execute("UPDATE sub_categories SET main_category=? WHERE main_category=?", (name, row["name"]))
                db.execute("UPDATE sub_categories_2 SET main_category=? WHERE main_category=?", (name, row["name"]))
                db.execute("UPDATE sub_categories_3 SET main_category=? WHERE main_category=?", (name, row["name"]))
                db.execute("UPDATE sub_categories_4 SET main_category=? WHERE main_category=?", (name, row["name"]))
                db.commit()
                flash("Main category updated.", "success")
            except IntegrityError:
                db.rollback()
                flash("That main category name already exists.", "error")
    elif action == "delete":
        category_id = request.form.get("category_id")
        row = db.execute("SELECT * FROM main_categories WHERE id=?", (category_id,)).fetchone()
        if not row:
            flash("Main category not found.", "error")
        else:
            in_use = sum(
                1
                for product_row in db.execute("SELECT main_category, main_categories FROM products").fetchall()
                if row["name"] in product_main_names(product_row)
            )
            if in_use:
                flash("Cannot delete a main category that still has products.", "error")
            else:
                db.execute("DELETE FROM sub_categories_4 WHERE main_category=?", (row["name"],))
                db.execute("DELETE FROM sub_categories_3 WHERE main_category=?", (row["name"],))
                db.execute("DELETE FROM sub_categories_2 WHERE main_category=?", (row["name"],))
                db.execute("DELETE FROM sub_categories WHERE main_category=?", (row["name"],))
                db.execute("DELETE FROM main_categories WHERE id=?", (category_id,))
                db.commit()
                flash("Main category deleted.", "success")
    invalidate_shop_nav_cache()


def handle_sub_category_form():
    action = request.form.get("action")
    db = get_db()
    mains = load_main_categories()
    if action == "add":
        main_category = request.form.get("main_category", "").strip()
        if main_category not in mains:
            flash("Choose a main category for the sub category.", "error")
            return
        try:
            save_named_category("sub_categories", request.form.get("name"), {"main_category": main_category})
            db.commit()
            flash("Sub category added.", "success")
        except ValueError as error:
            flash(str(error), "error")
        except IntegrityError:
            db.rollback()
            flash("That sub category already exists for this main category.", "error")
    elif action == "rename":
        category_id = request.form.get("category_id")
        name = (request.form.get("name") or "").strip()[:40]
        main_category = request.form.get("main_category", "").strip()
        row = db.execute("SELECT * FROM sub_categories WHERE id=?", (category_id,)).fetchone()
        if not row or not name or main_category not in mains:
            flash("Valid sub category, main category, and new name are required.", "error")
        else:
            try:
                db.execute(
                    "UPDATE sub_categories SET name=?, main_category=? WHERE id=?",
                    (name, main_category, category_id),
                )
                db.execute(
                    "UPDATE products SET sub_category=?, category=? WHERE sub_category=? AND main_category=?",
                    (name, name, row["name"], row["main_category"]),
                )
                db.execute(
                    "UPDATE sub_categories_2 SET sub_category=?, main_category=? WHERE sub_category=? AND main_category=?",
                    (name, main_category, row["name"], row["main_category"]),
                )
                db.execute(
                    "UPDATE sub_categories_3 SET sub_category=?, main_category=? WHERE sub_category=? AND main_category=?",
                    (name, main_category, row["name"], row["main_category"]),
                )
                db.execute(
                    "UPDATE sub_categories_4 SET sub_category=?, main_category=? WHERE sub_category=? AND main_category=?",
                    (name, main_category, row["name"], row["main_category"]),
                )
                db.commit()
                flash("Sub category updated.", "success")
            except IntegrityError:
                db.rollback()
                flash("That sub category already exists for this main category.", "error")
    elif action == "delete":
        category_id = request.form.get("category_id")
        row = db.execute("SELECT * FROM sub_categories WHERE id=?", (category_id,)).fetchone()
        if not row:
            flash("Sub category not found.", "error")
        else:
            in_use = db.execute(
                "SELECT COUNT(*) AS count FROM products WHERE (sub_category=? OR category=?) AND main_category=?",
                (row["name"], row["name"], row["main_category"]),
            ).fetchone()["count"]
            if in_use:
                flash("Cannot delete a sub category that still has products.", "error")
            else:
                db.execute(
                    "DELETE FROM sub_categories_4 WHERE sub_category=? AND main_category=?",
                    (row["name"], row["main_category"]),
                )
                db.execute(
                    "DELETE FROM sub_categories_3 WHERE sub_category=? AND main_category=?",
                    (row["name"], row["main_category"]),
                )
                db.execute(
                    "DELETE FROM sub_categories_2 WHERE sub_category=? AND main_category=?",
                    (row["name"], row["main_category"]),
                )
                db.execute("DELETE FROM sub_categories WHERE id=?", (category_id,))
                db.commit()
                flash("Sub category deleted.", "success")


def handle_sub_category_2_form():
    action = request.form.get("action")
    db = get_db()
    mains = load_main_categories()
    subs = load_sub_categories()
    if action == "add":
        main_category = request.form.get("main_category", "").strip()
        sub_category = request.form.get("sub_category", "").strip()
        if main_category not in mains or sub_category not in subs.get(main_category, []):
            flash("Choose a main category and its sub category first.", "error")
            return
        try:
            save_named_category(
                "sub_categories_2",
                request.form.get("name"),
                {"main_category": main_category, "sub_category": sub_category},
            )
            db.commit()
            flash("Sub category 2 added.", "success")
        except ValueError as error:
            flash(str(error), "error")
        except IntegrityError:
            db.rollback()
            flash("That sub category 2 already exists under this sub category.", "error")
    elif action == "rename":
        category_id = request.form.get("category_id")
        name = (request.form.get("name") or "").strip()[:40]
        main_category = request.form.get("main_category", "").strip()
        sub_category = request.form.get("sub_category", "").strip()
        row = db.execute("SELECT * FROM sub_categories_2 WHERE id=?", (category_id,)).fetchone()
        if not row or not name or main_category not in mains or sub_category not in subs.get(main_category, []):
            flash("Valid main category, sub category, and new name are required.", "error")
        else:
            try:
                db.execute(
                    "UPDATE sub_categories_2 SET name=?, main_category=?, sub_category=? WHERE id=?",
                    (name, main_category, sub_category, category_id),
                )
                db.execute(
                    """
                    UPDATE products SET sub_category_2=?
                    WHERE sub_category_2=? AND sub_category=? AND main_category=?
                    """,
                    (name, row["name"], row["sub_category"], row["main_category"]),
                )
                db.execute(
                    """
                    UPDATE sub_categories_3 SET sub_category_2=?, main_category=?, sub_category=?
                    WHERE sub_category_2=? AND sub_category=? AND main_category=?
                    """,
                    (name, main_category, sub_category, row["name"], row["sub_category"], row["main_category"]),
                )
                db.execute(
                    """
                    UPDATE sub_categories_4 SET sub_category_2=?, main_category=?, sub_category=?
                    WHERE sub_category_2=? AND sub_category=? AND main_category=?
                    """,
                    (name, main_category, sub_category, row["name"], row["sub_category"], row["main_category"]),
                )
                db.commit()
                flash("Sub category 2 updated.", "success")
            except IntegrityError:
                db.rollback()
                flash("That sub category 2 already exists under this sub category.", "error")
    elif action == "delete":
        category_id = request.form.get("category_id")
        row = db.execute("SELECT * FROM sub_categories_2 WHERE id=?", (category_id,)).fetchone()
        if not row:
            flash("Sub category 2 not found.", "error")
        else:
            in_use = db.execute(
                """
                SELECT COUNT(*) AS count FROM products
                WHERE sub_category_2=? AND sub_category=? AND main_category=?
                """,
                (row["name"], row["sub_category"], row["main_category"]),
            ).fetchone()["count"]
            if in_use:
                flash("Cannot delete a sub category 2 that still has products.", "error")
            else:
                db.execute(
                    """
                    DELETE FROM sub_categories_4
                    WHERE sub_category_2=? AND sub_category=? AND main_category=?
                    """,
                    (row["name"], row["sub_category"], row["main_category"]),
                )
                db.execute(
                    """
                    DELETE FROM sub_categories_3
                    WHERE sub_category_2=? AND sub_category=? AND main_category=?
                    """,
                    (row["name"], row["sub_category"], row["main_category"]),
                )
                db.execute("DELETE FROM sub_categories_2 WHERE id=?", (category_id,))
                db.commit()
                flash("Sub category 2 deleted.", "success")


def handle_sub_category_3_form():
    action = request.form.get("action")
    db = get_db()
    mains = load_main_categories()
    subs = load_sub_categories()
    sub2s = load_sub_categories_2()
    if action == "add":
        main_category = request.form.get("main_category", "").strip()
        sub_category = request.form.get("sub_category", "").strip()
        sub_category_2 = request.form.get("sub_category_2", "").strip()
        if (
            main_category not in mains
            or sub_category not in subs.get(main_category, [])
            or sub_category_2 not in sub2s.get(main_category, {}).get(sub_category, [])
        ):
            flash("Choose a main category, sub category, and sub category 2 first.", "error")
            return
        try:
            save_named_category(
                "sub_categories_3",
                request.form.get("name"),
                {
                    "main_category": main_category,
                    "sub_category": sub_category,
                    "sub_category_2": sub_category_2,
                },
            )
            db.commit()
            flash("Sub category 3 added.", "success")
        except ValueError as error:
            flash(str(error), "error")
        except IntegrityError:
            db.rollback()
            flash("That sub category 3 already exists under this sub category 2.", "error")
    elif action == "rename":
        category_id = request.form.get("category_id")
        name = (request.form.get("name") or "").strip()[:40]
        main_category = request.form.get("main_category", "").strip()
        sub_category = request.form.get("sub_category", "").strip()
        sub_category_2 = request.form.get("sub_category_2", "").strip()
        row = db.execute("SELECT * FROM sub_categories_3 WHERE id=?", (category_id,)).fetchone()
        if (
            not row
            or not name
            or main_category not in mains
            or sub_category not in subs.get(main_category, [])
            or sub_category_2 not in sub2s.get(main_category, {}).get(sub_category, [])
        ):
            flash("Valid parents and a new name are required.", "error")
        else:
            try:
                db.execute(
                    """
                    UPDATE sub_categories_3
                    SET name=?, main_category=?, sub_category=?, sub_category_2=?
                    WHERE id=?
                    """,
                    (name, main_category, sub_category, sub_category_2, category_id),
                )
                db.execute(
                    """
                    UPDATE products SET sub_category_3=?
                    WHERE sub_category_3=? AND sub_category_2=? AND sub_category=? AND main_category=?
                    """,
                    (name, row["name"], row["sub_category_2"], row["sub_category"], row["main_category"]),
                )
                db.execute(
                    """
                    UPDATE sub_categories_4
                    SET sub_category_3=?, sub_category_2=?, sub_category=?, main_category=?
                    WHERE sub_category_3=? AND sub_category_2=? AND sub_category=? AND main_category=?
                    """,
                    (
                        name,
                        sub_category_2,
                        sub_category,
                        main_category,
                        row["name"],
                        row["sub_category_2"],
                        row["sub_category"],
                        row["main_category"],
                    ),
                )
                db.commit()
                flash("Sub category 3 updated.", "success")
            except IntegrityError:
                db.rollback()
                flash("That sub category 3 already exists under this sub category 2.", "error")
    elif action == "delete":
        category_id = request.form.get("category_id")
        row = db.execute("SELECT * FROM sub_categories_3 WHERE id=?", (category_id,)).fetchone()
        if not row:
            flash("Sub category 3 not found.", "error")
        else:
            in_use = db.execute(
                """
                SELECT COUNT(*) AS count FROM products
                WHERE sub_category_3=? AND sub_category_2=? AND sub_category=? AND main_category=?
                """,
                (row["name"], row["sub_category_2"], row["sub_category"], row["main_category"]),
            ).fetchone()["count"]
            if in_use:
                flash("Cannot delete a sub category 3 that still has products.", "error")
            else:
                db.execute(
                    """
                    DELETE FROM sub_categories_4
                    WHERE sub_category_3=? AND sub_category_2=? AND sub_category=? AND main_category=?
                    """,
                    (row["name"], row["sub_category_2"], row["sub_category"], row["main_category"]),
                )
                db.execute("DELETE FROM sub_categories_3 WHERE id=?", (category_id,))
                db.commit()
                flash("Sub category 3 deleted.", "success")


def handle_sub_category_4_form():
    action = request.form.get("action")
    db = get_db()
    mains = load_main_categories()
    subs = load_sub_categories()
    sub2s = load_sub_categories_2()
    sub3s = load_sub_categories_3()
    if action == "add":
        main_category = request.form.get("main_category", "").strip()
        sub_category = request.form.get("sub_category", "").strip()
        sub_category_2 = request.form.get("sub_category_2", "").strip()
        sub_category_3 = request.form.get("sub_category_3", "").strip()
        if (
            main_category not in mains
            or sub_category not in subs.get(main_category, [])
            or sub_category_2 not in sub2s.get(main_category, {}).get(sub_category, [])
            or sub_category_3 not in sub3s.get(main_category, {}).get(sub_category, {}).get(sub_category_2, [])
        ):
            flash("Choose all parent categories first.", "error")
            return
        try:
            save_named_category(
                "sub_categories_4",
                request.form.get("name"),
                {
                    "main_category": main_category,
                    "sub_category": sub_category,
                    "sub_category_2": sub_category_2,
                    "sub_category_3": sub_category_3,
                },
            )
            db.commit()
            flash("Sub category 4 added.", "success")
        except ValueError as error:
            flash(str(error), "error")
        except IntegrityError:
            db.rollback()
            flash("That sub category 4 already exists under this sub category 3.", "error")
    elif action == "rename":
        category_id = request.form.get("category_id")
        name = (request.form.get("name") or "").strip()[:40]
        main_category = request.form.get("main_category", "").strip()
        sub_category = request.form.get("sub_category", "").strip()
        sub_category_2 = request.form.get("sub_category_2", "").strip()
        sub_category_3 = request.form.get("sub_category_3", "").strip()
        row = db.execute("SELECT * FROM sub_categories_4 WHERE id=?", (category_id,)).fetchone()
        if (
            not row
            or not name
            or main_category not in mains
            or sub_category not in subs.get(main_category, [])
            or sub_category_2 not in sub2s.get(main_category, {}).get(sub_category, [])
            or sub_category_3 not in sub3s.get(main_category, {}).get(sub_category, {}).get(sub_category_2, [])
        ):
            flash("Valid parents and a new name are required.", "error")
        else:
            try:
                db.execute(
                    """
                    UPDATE sub_categories_4
                    SET name=?, main_category=?, sub_category=?, sub_category_2=?, sub_category_3=?
                    WHERE id=?
                    """,
                    (name, main_category, sub_category, sub_category_2, sub_category_3, category_id),
                )
                db.execute(
                    """
                    UPDATE products SET sub_category_4=?
                    WHERE sub_category_4=? AND sub_category_3=? AND sub_category_2=? AND sub_category=? AND main_category=?
                    """,
                    (
                        name,
                        row["name"],
                        row["sub_category_3"],
                        row["sub_category_2"],
                        row["sub_category"],
                        row["main_category"],
                    ),
                )
                db.commit()
                flash("Sub category 4 updated.", "success")
            except IntegrityError:
                db.rollback()
                flash("That sub category 4 already exists under this sub category 3.", "error")
    elif action == "delete":
        category_id = request.form.get("category_id")
        row = db.execute("SELECT * FROM sub_categories_4 WHERE id=?", (category_id,)).fetchone()
        if not row:
            flash("Sub category 4 not found.", "error")
        else:
            in_use = db.execute(
                """
                SELECT COUNT(*) AS count FROM products
                WHERE sub_category_4=? AND sub_category_3=? AND sub_category_2=? AND sub_category=? AND main_category=?
                """,
                (row["name"], row["sub_category_3"], row["sub_category_2"], row["sub_category"], row["main_category"]),
            ).fetchone()["count"]
            if in_use:
                flash("Cannot delete a sub category 4 that still has products.", "error")
            else:
                db.execute("DELETE FROM sub_categories_4 WHERE id=?", (category_id,))
                db.commit()
                flash("Sub category 4 deleted.", "success")


def save_product_from_form(product_id=None):
    fields = {
        key: request.form.get(key, "").strip()
        for key in (
            "name",
            "sku",
            "description",
            "condition",
            "main_category",
            "sub_category",
            "sub_category_2",
            "sub_category_3",
            "sub_category_4",
            "product_type",
            "size_group",
            "region_visibility",
        )
    }
    fields["name"] = fields["name"][:100]
    fields["description"] = fields["description"][:3000]
    fields["sku"] = fields["sku"][:50]
    marketplace = parse_marketplace_urls()
    color_rows = parse_color_form()
    size_rows = parse_size_form()
    shipping_rows = parse_product_shipping_form()
    product_tags = parse_keyword_list(request.form.get("product_tags", ""))
    product_hashtags = parse_keyword_list(request.form.get("product_hashtags", ""), hashtag=True)
    tags_stored = ",".join(product_tags)
    hashtags_stored = ",".join(product_hashtags)
    try:
        price_eur = float(request.form.get("price", 0))
    except ValueError:
        price_eur = 0
    price = round(price_eur * EUR_TO_STORE, 2)
    try:
        weight = float(request.form.get("weight", 0) or 0)
    except ValueError:
        weight = 0
    try:
        packing_weight = float(request.form.get("packing_weight", 0) or 0)
    except ValueError:
        packing_weight = 0
    try:
        pakistan_price = float(request.form.get("pakistan_price", 0) or 0)
    except ValueError:
        pakistan_price = 0
    discount_percent = 0
    pakistan_discount_percent = 0
    try:
        rating = float(request.form.get("rating", 0) or 0)
    except ValueError:
        rating = 0
    try:
        likes = int(float(request.form.get("likes", 0) or 0))
    except ValueError:
        likes = 0
    weight = max(0.0, weight)
    packing_weight = max(0.0, packing_weight)
    pakistan_price = max(0.0, pakistan_price)
    rating = max(0.0, min(5.0, rating))
    likes = max(0, likes)
    featured = 1 if request.form.get("featured") else 0
    deal_of_week = 1 if request.form.get("deal_of_week") else 0
    new_arrival = 1 if request.form.get("new_arrival") else 0
    save_as_draft = (request.form.get("save_mode") or "").strip().lower() == "draft"
    stock = sum(entry["quantity"] for entry in color_rows)
    fulfillment = (request.form.get("fulfillment") or "physical").strip().lower()
    if fulfillment not in {"physical", "virtual"}:
        raise ValueError("Choose physical or virtual.")
    is_virtual = fulfillment == "virtual"
    if is_virtual:
        weight = 0
        packing_weight = 0
        fields["brand"] = ""
        shipping_rows = blank_product_shipping()
    selected_mains = []
    for name in request.form.getlist("main_category"):
        name = (name or "").strip()
        if name and name not in selected_mains:
            selected_mains.append(name)
    selected_genders = []
    for name in request.form.getlist("gender"):
        name = (name or "").strip()
        if name in GENDER_VALUES and name not in selected_genders:
            selected_genders.append(name)
    if not save_as_draft and not selected_genders:
        raise ValueError("Select at least one product gender.")
    if not selected_genders:
        selected_genders = ["Unisex"]
    # Selecting Men/Women/Kids/Unisex genders also lists the product under those shop filters.
    for gender in selected_genders:
        main_name = GENDER_TO_MAIN.get(gender)
        if main_name and main_name not in selected_mains:
            selected_mains.append(main_name)
    if not save_as_draft and not selected_mains:
        raise ValueError("Select at least one main category or a Men/Women/Kids/Unisex gender.")
    if selected_mains:
        fields["main_category"] = selected_mains[0]
    elif save_as_draft:
        fields["main_category"] = (fields.get("main_category") or "").strip()
    else:
        fields["main_category"] = (fields.get("main_category") or "Unisex").strip()
    fields["main_categories_json"] = json.dumps(
        selected_mains or ([fields["main_category"]] if fields["main_category"] else [])
    )
    selected_subs = []
    for name in request.form.getlist("sub_category"):
        name = (name or "").strip()
        if name and name not in selected_subs:
            selected_subs.append(name)
    fields["sub_category"] = selected_subs[0] if selected_subs else ""
    fields["sub_categories_json"] = json.dumps(selected_subs)
    fields["sub_category_2"] = (fields.get("sub_category_2") or "").strip()
    fields["sub_category_3"] = (fields.get("sub_category_3") or "").strip()
    fields["sub_category_4"] = (fields.get("sub_category_4") or "").strip()
    if not fields["sub_category_2"]:
        fields["sub_category_3"] = ""
        fields["sub_category_4"] = ""
    elif not fields["sub_category_3"]:
        fields["sub_category_4"] = ""
    fields["size_group"] = selected_genders[0]
    fields["genders_json"] = json.dumps(selected_genders)
    offers = {}
    for gender in selected_genders:
        offers[gender] = parse_gender_offer_form(gender, is_virtual)
    fields["gender_offers_json"] = json.dumps(offers)
    primary_offer = offers[selected_genders[0]]
    price = primary_offer["price"]
    pakistan_price = primary_offer["pakistan_price"]
    color_rows = primary_offer["colors"]
    size_rows = primary_offer["sizes"]
    volume_discounts = list(primary_offer.get("volume_discounts") or [])
    pakistan_volume_discounts = list(primary_offer.get("pakistan_volume_discounts") or [])
    if is_virtual:
        stock = sum(int(offer["virtual_stock"]) for offer in offers.values())
    else:
        stock = sum(int(entry["quantity"]) for offer in offers.values() for entry in offer["colors"])
    if not save_as_draft and any(offer["price"] <= 0 for offer in offers.values()):
        raise ValueError("Enter a price for each selected gender.")
    if not save_as_draft and is_virtual and any(offer["virtual_stock"] <= 0 for offer in offers.values()):
        raise ValueError("Enter a quantity for each selected gender.")
    if not save_as_draft and not is_virtual and any(not offer["sizes"] or not offer["colors"] for offer in offers.values()):
        raise ValueError("Enter sizes and colours for each selected gender.")
    allowed_subs = []
    for main_name in selected_mains:
        for option in load_sub_categories().get(main_name, []):
            if option not in allowed_subs:
                allowed_subs.append(option)
    allowed_sub2s = []
    for main_name in selected_mains:
        for option in load_sub_categories_2().get(main_name, {}).get(fields["sub_category"], []):
            if option not in allowed_sub2s:
                allowed_sub2s.append(option)
    allowed_sub3s = []
    for main_name in selected_mains:
        for option in (
            load_sub_categories_3()
            .get(main_name, {})
            .get(fields["sub_category"], {})
            .get(fields["sub_category_2"], [])
        ):
            if option not in allowed_sub3s:
                allowed_sub3s.append(option)
    allowed_sub4s = []
    for main_name in selected_mains:
        for option in (
            load_sub_categories_4()
            .get(main_name, {})
            .get(fields["sub_category"], {})
            .get(fields["sub_category_2"], {})
            .get(fields["sub_category_3"], [])
        ):
            if option not in allowed_sub4s:
                allowed_sub4s.append(option)
    if save_as_draft:
        # Drafts: every field optional. Only soft placeholders for NOT NULL / uniqueness.
        if not fields["name"]:
            fields["name"] = "Untitled draft"
        if not fields["description"]:
            fields["description"] = ""
        fields["sku"] = fields["sku"] or None
        if fields["product_type"] not in PRODUCT_TYPES:
            fields["product_type"] = "Clothes"
        if fields["condition"] not in CONDITION_LABELS:
            fields["condition"] = "new_with_tag"
        if fields["region_visibility"] not in {key for key, _ in REGION_OPTIONS}:
            fields["region_visibility"] = "all"
    elif (
        not fields["name"]
        or not fields["sku"]
        or not fields["description"]
        or not fields["condition"]
        or not fields["main_category"]
        or not fields["sub_category"]
        or not fields["product_type"]
        or not fields["region_visibility"]
        or price <= 0
        or (not is_virtual and (not fields["size_group"] or not color_rows or not size_rows))
        or (is_virtual and stock <= 0)
    ):
        if is_virtual and stock <= 0:
            raise ValueError("Enter a quantity for this virtual product.")
        if (
            len(selected_subs) < 1
            and fields["name"]
            and fields["sku"]
            and fields["description"]
            and fields["condition"]
            and fields["main_category"]
            and fields["product_type"]
            and price > 0
        ):
            raise ValueError("Select at least one sub category.")
        raise ValueError("Complete name, SKU, condition, sub categories, product type, size, description, price, colours, and stock.")
    if not save_as_draft:
        if fields["product_type"] not in PRODUCT_TYPES:
            raise ValueError("Choose Clothes, Shoes, Accessories, Sports, or Others.")
        if fields["main_category"] not in load_main_categories():
            raise ValueError("Choose a valid main category.")
        if any(name not in load_main_categories() for name in selected_mains):
            raise ValueError("Choose a valid main category.")
        if len(selected_subs) < 1:
            raise ValueError("Select at least one sub category.")
        if any(name not in allowed_subs for name in selected_subs):
            raise ValueError("Choose valid sub categories for the selected main categories.")
        if fields["sub_category_4"] and (not fields["sub_category_2"] or not fields["sub_category_3"]):
            raise ValueError("Choose sub category 2 and 3 before sub category 4, or leave 4 empty.")
        if fields["sub_category_3"] and not fields["sub_category_2"]:
            raise ValueError("Choose sub category 2 before sub category 3, or leave 3 empty.")
        if fields["sub_category_2"] and fields["sub_category_2"] not in allowed_sub2s:
            raise ValueError("Choose a valid sub category 2 for this sub category.")
        if fields["sub_category_3"] and fields["sub_category_3"] not in allowed_sub3s:
            raise ValueError("Choose a valid sub category 3 for this sub category 2.")
        if fields["sub_category_4"] and fields["sub_category_4"] not in allowed_sub4s:
            raise ValueError("Choose a valid sub category 4 for this sub category 3.")
        if not is_virtual and fields["size_group"] not in GENDER_VALUES:
            raise ValueError("Select at least one product gender.")
        if fields["condition"] not in CONDITION_LABELS:
            raise ValueError("Choose a product condition.")
        if fields["region_visibility"] not in {key for key, _ in REGION_OPTIONS}:
            raise ValueError("Choose where this product should be shown.")
    if is_virtual:
        fields["brand"] = ""
    else:
        listed_brand = (request.form.get("brand") or "").strip()[:80]
        # Keep legacy brand_custom if an older form still posts it.
        custom_brand = (request.form.get("brand_custom") or "").strip()[:80]
        brand = listed_brand or custom_brand
        fields["brand"] = ensure_brand_name(brand) if brand else ""
    category = fields["sub_category"] or fields["main_category"] or "Draft"
    listed_by = current_listing_owner()
    db = get_db()
    if fields["sku"]:
        sku_owner = db.execute("SELECT id FROM products WHERE sku=?", (fields["sku"],)).fetchone()
        if sku_owner and (product_id is None or sku_owner["id"] != product_id):
            raise ValueError(f"SKU {fields['sku']} is already used by another product. Choose a unique SKU.")
    elif not save_as_draft:
        raise ValueError("SKU is required to publish.")
    colors_legacy = ",".join(entry["name"] for entry in color_rows)
    sizes_legacy = ",".join(size_rows)
    extra_fields = (
        fields["condition"],
        fields["main_category"],
        fields["main_categories_json"],
        fields["sub_category"],
        fields["sub_categories_json"],
        fields["sub_category_2"] or None,
        fields["sub_category_3"] or None,
        fields["sub_category_4"] or None,
        fields["product_type"],
        fields["size_group"],
        fields["genders_json"],
        packing_weight,
        fields["region_visibility"],
        tags_stored,
        hashtags_stored,
        fields["brand"] or None,
    )
    is_draft = 1 if save_as_draft else 0
    was_draft = False
    if product_id is not None:
        existing = db.execute("SELECT is_draft FROM products WHERE id=?", (product_id,)).fetchone()
        if not existing:
            raise ValueError("That product was not found.")
        try:
            was_draft = bool(int(existing["is_draft"] or 0))
        except (TypeError, ValueError):
            was_draft = False
    if save_as_draft:
        active = 0
    elif product_id is None or was_draft:
        # New products and drafts that are published should appear in the shop.
        active = 1
    else:
        active = 1 if request.form.get("active") else 0
    if product_id is None:
        cursor = db.execute(
            """
            INSERT INTO products (
                name,category,price,rating,reviews_count,likes,sku,image,sizes,colors,
                description,stock,active,colors_json,sizes_json,amazon_url,etsy_url,ebay_url,
                discount_percent,weight,shipping_json,pakistan_price,pakistan_discount_percent,
                condition,main_category,main_categories,sub_category,sub_categories,sub_category_2,sub_category_3,sub_category_4,product_type,size_group,genders,packing_weight,region_visibility,
                product_tags,product_hashtags,brand,featured,deal_of_week,new_arrival,is_draft,listed_by,volume_discounts,pakistan_volume_discounts,fulfillment,gender_offers
            ) VALUES (?,?,?,?,0,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
            RETURNING id
            """,
            (
                fields["name"],
                category,
                price,
                rating,
                likes,
                fields["sku"],
                "",
                sizes_legacy,
                colors_legacy,
                fields["description"],
                stock,
                active,
                json.dumps(color_rows),
                json.dumps(size_rows),
                marketplace["amazon_url"],
                marketplace["etsy_url"],
                marketplace["ebay_url"],
                discount_percent,
                weight,
                json.dumps(shipping_rows),
                pakistan_price,
                pakistan_discount_percent,
                *extra_fields,
                featured,
                deal_of_week,
                new_arrival,
                is_draft,
                listed_by,
                json.dumps(volume_discounts),
                json.dumps(pakistan_volume_discounts),
                fulfillment,
                fields["gender_offers_json"],
            ),
        )
        product_id = cursor.fetchone()["id"]
    else:
        db.execute(
            """
            UPDATE products SET
                name=?, category=?, price=?, rating=?, likes=?, sku=?, sizes=?, colors=?,
                description=?, stock=?, active=?, colors_json=?, sizes_json=?,
                amazon_url=?, etsy_url=?, ebay_url=?, discount_percent=?, weight=?, shipping_json=?,
                pakistan_price=?, pakistan_discount_percent=?, condition=?, main_category=?, main_categories=?,
                sub_category=?, sub_categories=?, sub_category_2=?, sub_category_3=?, sub_category_4=?, product_type=?, size_group=?, genders=?, packing_weight=?, region_visibility=?,
                product_tags=?, product_hashtags=?, brand=?, featured=?, deal_of_week=?, new_arrival=?, is_draft=?, volume_discounts=?, pakistan_volume_discounts=?, fulfillment=?, gender_offers=?
            WHERE id=?
            """,
            (
                fields["name"],
                category,
                price,
                rating,
                likes,
                fields["sku"],
                sizes_legacy,
                colors_legacy,
                fields["description"],
                stock,
                active,
                json.dumps(color_rows),
                json.dumps(size_rows),
                marketplace["amazon_url"],
                marketplace["etsy_url"],
                marketplace["ebay_url"],
                discount_percent,
                weight,
                json.dumps(shipping_rows),
                pakistan_price,
                pakistan_discount_percent,
                *extra_fields,
                featured,
                deal_of_week,
                new_arrival,
                is_draft,
                json.dumps(volume_discounts),
                json.dumps(pakistan_volume_discounts),
                fulfillment,
                fields["gender_offers_json"],
                product_id,
            ),
        )
    if deal_of_week:
        db.execute("UPDATE products SET deal_of_week=0 WHERE id!=?", (product_id,))
    save_product_images(product_id, fields["sku"], slots=PRODUCT_IMAGE_SLOTS)
    db.commit()
    invalidate_shop_nav_cache()
    return product_id


def product_form_context(item=None):
    existing_sizes = item["size_rows"] if item else []
    extra_sizes = extra_sizes_of(item)
    return {
        "product": item,
        "product_types": PRODUCT_TYPES,
        "brands": load_brands(),
        "main_categories": load_main_categories(),
        "sub_categories": load_sub_categories(),
        "sub_categories_2": load_sub_categories_2(),
        "sub_categories_3": load_sub_categories_3(),
        "sub_categories_4": load_sub_categories_4(),
        "size_groups": SIZE_GROUPS,
        "conditions": CONDITIONS,
        "region_options": REGION_OPTIONS,
        "color_slots": empty_color_slots(item["color_rows"] if item else None, extra_sizes),
        "size_slots_by_type": size_slots_by_type(existing_sizes, item.get("product_type") if item else None),
        "shipping_slots": product_shipping_slots(item.get("shipping") if item else None),
        "extra_sizes": extra_sizes,
        "custom_sizes": ", ".join(extra_sizes),
        "custom_shoe_sizes": ", ".join(extra_sizes) if item and item.get("product_type") == "Shoes" else "",
        "image_slots": product_image_slots(item),
        "dashboard_url": staff_home(),
        "price_eur": item["price_eur"] if item else "",
        "volume_slots": volume_form_slots(item.get("volume_discounts") if item else None),
        "pakistan_volume_slots": volume_form_slots(item.get("pakistan_volume_discounts") if item else None),
        "gender_offer_slots": gender_offer_slots(item),
        "preset_colors": PRESET_COLORS,
        "gender_to_main": GENDER_TO_MAIN,
    }


def staff_product_matches(item, query):
    needle = (query or "").strip().lower()
    if not needle:
        return True
    return needle in (item.get("name") or "").lower() or needle in (item.get("sku") or "").lower()


def copy_product_as_draft(source_id, listed_by="admin", require_owner=None):
    db = get_db()
    row = db.execute("SELECT * FROM products WHERE id=?", (source_id,)).fetchone()
    if not row:
        raise ValueError("That product was not found.")
    source = dict(row)
    owner = product_listed_by(source)
    if require_owner is not None and owner != require_owner:
        raise ValueError("You can only copy your own products.")
    owner_name = (listed_by or "admin").strip() or "admin"
    base_sku = (source.get("sku") or f"COPY-{source_id}")[:40]
    new_sku = f"{base_sku}-COPY"
    suffix = 2
    while db.execute("SELECT id FROM products WHERE sku=?", (new_sku,)).fetchone():
        new_sku = f"{base_sku}-C{suffix}"
        suffix += 1
        if suffix > 99:
            new_sku = f"COPY-{source_id}-{secrets.token_hex(3)}"
            break
    cursor = db.execute(
        """
        INSERT INTO products (
            name,category,price,rating,reviews_count,likes,sku,image,sizes,colors,
            description,stock,active,colors_json,sizes_json,amazon_url,etsy_url,ebay_url,
            discount_percent,weight,shipping_json,pakistan_price,pakistan_discount_percent,
            condition,main_category,main_categories,sub_category,sub_categories,sub_category_2,sub_category_3,sub_category_4,
            product_type,size_group,genders,packing_weight,region_visibility,product_tags,product_hashtags,brand,
            featured,deal_of_week,new_arrival,is_draft,listed_by,volume_discounts,pakistan_volume_discounts,fulfillment,gender_offers
        )
        SELECT
            name,category,price,rating,0,likes,?, '',sizes,colors,
            description,stock,0,colors_json,sizes_json,amazon_url,etsy_url,ebay_url,
            discount_percent,weight,shipping_json,pakistan_price,pakistan_discount_percent,
            condition,main_category,main_categories,sub_category,sub_categories,sub_category_2,sub_category_3,sub_category_4,
            product_type,size_group,genders,packing_weight,region_visibility,product_tags,product_hashtags,brand,
            0,0,COALESCE(new_arrival,0),1,?,volume_discounts,pakistan_volume_discounts,fulfillment,gender_offers
        FROM products WHERE id=?
        RETURNING id
        """,
        (new_sku, owner_name, source_id),
    )
    new_id = cursor.fetchone()["id"]
    for image in db.execute(
        "SELECT slot, content_type, bytes, byte_size FROM product_images WHERE product_id=? ORDER BY slot",
        (source_id,),
    ).fetchall():
        db.execute(
            """
            INSERT INTO product_images (product_id, slot, content_type, bytes, byte_size)
            VALUES (?,?,?,?,?)
            """,
            (new_id, image["slot"], image["content_type"], image["bytes"], image["byte_size"]),
        )
    db.execute(
        "UPDATE products SET name=? WHERE id=?",
        (f"{source.get('name') or 'Product'} (copy)", new_id),
    )
    refresh_product_cover_image(new_id)
    db.commit()
    invalidate_shop_nav_cache()
    return new_id


def copy_product_as_admin_draft(source_id):
    return copy_product_as_draft(source_id, listed_by="admin")


@app.route("/admin/product/new", methods=["GET", "POST"])
@admin_required
def admin_product_new():
    if request.method == "POST":
        try:
            saved_id = save_product_from_form()
            if (request.form.get("save_mode") or "").strip().lower() == "draft":
                flash("Draft saved. You can keep editing and save again anytime.", "success")
                return redirect(url_for("admin_product_edit", product_id=saved_id))
            flash("Product created successfully.", "success")
            return redirect(url_for("admin_dashboard"))
        except (IntegrityError, ValueError) as error:
            rollback_db()
            flash(f"Product was not saved: {friendly_product_error(error)}", "error")
    return render_template("admin_product_form.html", **product_form_context())


@app.route("/admin/product/<int:product_id>/edit", methods=["GET", "POST"])
@admin_required
def admin_product_edit(product_id):
    db = get_db()
    row = db.execute("SELECT * FROM products WHERE id=?", (product_id,)).fetchone()
    if not row:
        abort(404)
    item = product(row)
    if request.method == "POST":
        try:
            save_product_from_form(product_id=product_id)
            if (request.form.get("save_mode") or "").strip().lower() == "draft":
                flash("Draft updated. You can keep editing and save again anytime.", "success")
                return redirect(url_for("admin_product_edit", product_id=product_id))
            flash("Product updated successfully.", "success")
            return redirect(url_for("admin_dashboard"))
        except (IntegrityError, ValueError) as error:
            rollback_db()
            flash(f"Product was not updated: {friendly_product_error(error)}", "error")
            item = product(db.execute("SELECT * FROM products WHERE id=?", (product_id,)).fetchone())
    return render_template("admin_product_form.html", **product_form_context(item))


@app.post("/admin/product/<int:product_id>/copy-draft")
@admin_required
def admin_product_copy_draft(product_id):
    try:
        new_id = copy_product_as_admin_draft(product_id)
        flash("Copied to your drafts. Edit the draft, then publish when ready.", "success")
        return redirect(url_for("admin_product_edit", product_id=new_id))
    except (IntegrityError, ValueError) as error:
        rollback_db()
        flash(str(error) if isinstance(error, ValueError) else "Could not copy that product.", "error")
        return redirect(request.referrer or url_for("admin_dashboard"))


@app.post("/admin/product/<int:product_id>/image/<int:slot>/delete")
@admin_required
def admin_product_image_delete(product_id, slot):
    db = get_db()
    row = db.execute("SELECT * FROM products WHERE id=?", (product_id,)).fetchone()
    if not row:
        abort(404)
    remove_saved_product_image(product_id, slot, row["sku"])
    flash("Image deleted.", "success")
    return redirect(url_for("admin_product_edit", product_id=product_id))


def delete_product_record(product_id, listed_by=None):
    db = get_db()
    row = db.execute("SELECT * FROM products WHERE id=?", (product_id,)).fetchone()
    if not row:
        raise ValueError("That product was not found.")
    if listed_by is not None and product_listed_by(row) != listed_by:
        raise ValueError("That product was not found.")
    db.execute("DELETE FROM reviews WHERE product_id=?", (product_id,))
    db.execute("DELETE FROM product_images WHERE product_id=?", (product_id,))
    if table_exists("listings"):
        db.execute("UPDATE listings SET product_id=NULL WHERE product_id=?", (product_id,))
    sku = row.get("sku") or ""
    if sku:
        folder = os.path.join(UPLOAD_ROOT, sku)
        if os.path.isdir(folder):
            shutil.rmtree(folder, ignore_errors=True)
    if listed_by is not None:
        db.execute("DELETE FROM products WHERE id=? AND listed_by=?", (product_id, listed_by))
    else:
        db.execute("DELETE FROM products WHERE id=?", (product_id,))
    db.commit()
    invalidate_shop_nav_cache()


@app.post("/admin/product/<int:product_id>/delete")
@admin_required
def admin_product_delete(product_id):
    try:
        delete_product_record(product_id)
        flash("Product deleted.", "success")
    except ValueError as error:
        rollback_db()
        flash(str(error), "error")
    except IntegrityError:
        rollback_db()
        flash("This product could not be deleted because other records still depend on it.", "error")
    return redirect(url_for("admin_dashboard"))


@app.post("/admin/review/<int:review_id>/delete")
@admin_required
def admin_review_delete(review_id):
    get_db().execute("DELETE FROM reviews WHERE id=?", (review_id,))
    get_db().commit()
    flash("Review deleted.", "success")
    return redirect(url_for("admin_dashboard"))


@app.errorhandler(404)
def not_found(_):
    return render_template("404.html"), 404


@app.errorhandler(RequestEntityTooLarge)
def upload_too_large(_):
    flash(
        "That save was too large for the server form limit. Use fewer images (max 5, product under 2 MB), "
        "or try again — multi-gender listings need a higher form-parts limit.",
        "error",
    )
    return redirect(request.referrer or url_for("home")), 413



def parse_pg_array(text):
    return [item.strip() for item in (text or "").split(",") if item.strip()]



def save_pl_images(listing_id, existing=None):
    existing = dict(existing) if existing else {}
    folder = os.path.join(UPLOAD_ROOT, f"pl-{listing_id}")
    os.makedirs(folder, exist_ok=True)

    def handle(field, filename_base, existing_value):
        uploaded = request.files.get(field)
        if not uploaded or not uploaded.filename:
            return existing_value
        extension = secure_filename(uploaded.filename).rsplit(".", 1)[-1].lower() if "." in uploaded.filename else ""
        if extension not in ALLOWED_EXTENSIONS:
            raise ValueError("Images must be JPG, JPEG, PNG, or WEBP files.")
        filename = f"{filename_base}.jpg"
        uploaded.save(os.path.join(folder, filename))
        return f"/static/images/pl-{listing_id}/{filename}"

    picture_main = handle("main_image", "main", existing.get("picture_main"))
    picture_2 = handle("image_2", "2", existing.get("picture_2"))
    picture_3 = handle("image_3", "3", existing.get("picture_3"))

    extra = existing.get("pictures_extra") or []
    if isinstance(extra, str):
        try:
            extra = json.loads(extra)
        except json.JSONDecodeError:
            extra = [part.strip() for part in extra.split(",") if part.strip()]
    pictures_extra = list(extra)
    while len(pictures_extra) < 7:
        pictures_extra.append(None)
    for index in range(4, 11):
        pos = index - 4
        result = handle(f"image_{index}", str(index), pictures_extra[pos])
        pictures_extra[pos] = result
    pictures_extra = [p for p in pictures_extra if p]

    return picture_main, picture_2, picture_3, pictures_extra


def save_listing_from_form(listing_id=None):
    form = request.form
    name = form.get("product_name", "").strip()[:100]
    sku = form.get("sku", "").strip()[:50]
    condition = form.get("condition", "").strip()
    main_category = form.get("main_category", "").strip()[:100]
    sub_category = form.get("sub_category", "").strip()[:100]
    product_type = form.get("product_type", "").strip()
    size_group = form.get("size_group", "").strip()
    size_value = form.get("size_value", "").strip()[:20]
    region_visibility = form.get("region_visibility", "").strip()
    shipping_method = form.get("shipping_method", "").strip()
    description = form.get("description", "").strip()[:3000]

    def to_float(key, default=0):
        try:
            return float(form.get(key, default) or default)
        except ValueError:
            return default

    product_weight_kg = to_float("product_weight_kg")
    packing_weight_kg = to_float("packing_weight_kg")
    price_europe_eur = to_float("price_europe_eur")
    discount_europe_percent = to_float("discount_europe_percent")
    price_pakistan_pkr = to_float("price_pakistan_pkr")
    discount_pakistan_percent = to_float("discount_pakistan_percent")
    shipping_cost_germany = to_float("shipping_cost_germany")
    shipping_cost_europe = to_float("shipping_cost_europe")
    shipping_cost_america = to_float("shipping_cost_america")
    shipping_cost_pakistan = to_float("shipping_cost_pakistan")
    express_shipping_charge = to_float("express_shipping_charge", 10)

    colours = parse_pg_array(form.get("colours", ""))
    product_tags = parse_pg_array(form.get("product_tags", ""))
    product_hashtags = parse_pg_array(form.get("product_hashtags", ""))

    link_ebay = form.get("link_ebay", "").strip()[:500]
    link_etsy = form.get("link_etsy", "").strip()[:500]
    link_amazon = form.get("link_amazon", "").strip()[:500]

    if not name or not sku:
        raise ValueError("Product name and SKU are required.")

    db = get_db()

    if listing_id is None:
        cursor = db.execute(
            """
            INSERT INTO product_listings (
                product_name, sku, condition, main_category, sub_category, product_type,
                product_weight_kg, packing_weight_kg, size_group, size_value, colours,
                price_europe_eur, discount_europe_percent, price_pakistan_pkr, discount_pakistan_percent,
                region_visibility, shipping_cost_germany, shipping_cost_europe, shipping_cost_america,
                shipping_cost_pakistan, express_shipping_charge, shipping_method, description,
                product_tags, product_hashtags, link_ebay, link_etsy, link_amazon
            ) VALUES (?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?,?)
            RETURNING id
            """,
            (
                name, sku, condition, main_category, sub_category, product_type,
                product_weight_kg, packing_weight_kg, size_group, size_value, colours,
                price_europe_eur, discount_europe_percent, price_pakistan_pkr, discount_pakistan_percent,
                region_visibility, shipping_cost_germany, shipping_cost_europe, shipping_cost_america,
                shipping_cost_pakistan, express_shipping_charge, shipping_method, description,
                product_tags, product_hashtags, link_ebay, link_etsy, link_amazon,
            ),
        )
        new_id = cursor.fetchone()["id"]
        picture_main, picture_2, picture_3, pictures_extra = save_pl_images(new_id)
        db.execute(
            "UPDATE product_listings SET picture_main=?, picture_2=?, picture_3=?, pictures_extra=? WHERE id=?",
            (picture_main, picture_2, picture_3, pictures_extra, new_id),
        )
    else:
        existing_row = db.execute(
            "SELECT picture_main, picture_2, picture_3, pictures_extra FROM product_listings WHERE id=?",
            (listing_id,),
        ).fetchone()
        picture_main, picture_2, picture_3, pictures_extra = save_pl_images(listing_id, existing=existing_row)
        db.execute(
            """
            UPDATE product_listings SET
                product_name=?, sku=?, condition=?, main_category=?, sub_category=?, product_type=?,
                product_weight_kg=?, packing_weight_kg=?, size_group=?, size_value=?, colours=?,
                price_europe_eur=?, discount_europe_percent=?, price_pakistan_pkr=?, discount_pakistan_percent=?,
                region_visibility=?, shipping_cost_germany=?, shipping_cost_europe=?, shipping_cost_america=?,
                shipping_cost_pakistan=?, express_shipping_charge=?, shipping_method=?, description=?,
                product_tags=?, product_hashtags=?, link_ebay=?, link_etsy=?, link_amazon=?,
                picture_main=?, picture_2=?, picture_3=?, pictures_extra=?, updated_at=now()
            WHERE id=?
            """,
            (
                name, sku, condition, main_category, sub_category, product_type,
                product_weight_kg, packing_weight_kg, size_group, size_value, colours,
                price_europe_eur, discount_europe_percent, price_pakistan_pkr, discount_pakistan_percent,
                region_visibility, shipping_cost_germany, shipping_cost_europe, shipping_cost_america,
                shipping_cost_pakistan, express_shipping_charge, shipping_method, description,
                product_tags, product_hashtags, link_ebay, link_etsy, link_amazon,
                picture_main, picture_2, picture_3, pictures_extra,
                listing_id,
            ),
        )
    db.commit()


@app.route("/admin/listings")
@admin_required
def admin_listings():
    db = get_db()
    listings = db.execute("SELECT * FROM product_listings ORDER BY id DESC").fetchall()
    return render_template("admin_listings.html", listings=listings)


@app.route("/admin/listings/new", methods=["GET", "POST"])
@admin_required
def admin_listing_new():
    if request.method == "POST":
        try:
            save_listing_from_form()
            flash("Listing created successfully.", "success")
            return redirect(url_for("admin_listings"))
        except (IntegrityError, ValueError) as error:
            rollback_db()
            flash(f"Listing was not saved: {error}", "error")
    return render_template("admin_listing_form.html", listing=None)


@app.route("/admin/listings/<int:listing_id>/edit", methods=["GET", "POST"])
@admin_required
def admin_listing_edit(listing_id):
    db = get_db()
    row = db.execute("SELECT * FROM product_listings WHERE id=?", (listing_id,)).fetchone()
    if not row:
        abort(404)
    if request.method == "POST":
        try:
            save_listing_from_form(listing_id=listing_id)
            flash("Listing updated successfully.", "success")
            return redirect(url_for("admin_listings"))
        except (IntegrityError, ValueError) as error:
            rollback_db()
            flash(f"Listing was not updated: {error}", "error")
            row = db.execute("SELECT * FROM product_listings WHERE id=?", (listing_id,)).fetchone()
    return render_template("admin_listing_form.html", listing=row)


@app.post("/admin/listings/<int:listing_id>/delete")
@admin_required
def admin_listing_delete(listing_id):
    db = get_db()
    db.execute("DELETE FROM product_listings WHERE id=?", (listing_id,))
    db.commit()
    flash("Listing deleted.", "success")
    return redirect(url_for("admin_listings"))



PL_USERNAME = os.environ.get("PL_USERNAME", "")
PL_PASSWORD_HASH = os.environ.get("PL_PASSWORD_HASH", "")


def list_pl_users():
    return get_db().execute(
        "SELECT id, username, display_name, created_at FROM pl_users ORDER BY display_name, username"
    ).fetchall()


def listing_team_monitor():
    counts = {}
    for row in get_db().execute(
        """
        SELECT listed_by,
               COUNT(*) AS total,
               SUM(CASE WHEN COALESCE(active, 0)=1 THEN 1 ELSE 0 END) AS live
        FROM products
        WHERE COALESCE(listed_by, '') NOT IN ('', 'admin')
        GROUP BY listed_by
        """
    ).fetchall():
        username = (row["listed_by"] or "").strip()
        if not username:
            continue
        counts[username.lower()] = {
            "username": username,
            "total": int(row["total"] or 0),
            "live": int(row["live"] or 0),
        }
    members = []
    seen = set()
    for user in list_pl_users():
        username = (user["username"] or "").strip()
        key = username.lower()
        if not username or key in seen:
            continue
        seen.add(key)
        stats = counts.get(key) or {"total": 0, "live": 0}
        members.append(
            {
                "username": username,
                "display_name": (user.get("display_name") or username).strip() or username,
                "has_account": True,
                "total": stats["total"],
                "live": stats["live"],
            }
        )
    env_username = (PL_USERNAME or "").strip()
    if env_username and env_username.lower() not in seen:
        stats = counts.get(env_username.lower()) or {"total": 0, "live": 0}
        members.append(
            {
                "username": env_username,
                "display_name": "Listing team",
                "has_account": False,
                "total": stats["total"],
                "live": stats["live"],
            }
        )
        seen.add(env_username.lower())
    for key, stats in counts.items():
        if key in seen:
            continue
        members.append(
            {
                "username": stats["username"],
                "display_name": stats["username"],
                "has_account": False,
                "total": stats["total"],
                "live": stats["live"],
            }
        )
        seen.add(key)
    members.sort(key=lambda item: ((item["display_name"] or "").lower(), item["username"].lower()))
    return members


def listing_team_member(username):
    username = (username or "").strip()
    if not username or username.lower() == "admin":
        return None
    for member in listing_team_monitor():
        if member["username"].lower() == username.lower():
            return member
    return None


def find_pl_user(username):
    username = (username or "").strip().lower()
    if not username:
        return None
    return get_db().execute("SELECT * FROM pl_users WHERE LOWER(username)=?", (username,)).fetchone()


def authenticate_pl(username, password):
    row = find_pl_user(username)
    if row and check_password_hash(row["password_hash"], password):
        return row
    env_username = (PL_USERNAME or "").strip()
    if env_username and PL_PASSWORD_HASH and username.strip() == env_username and check_password_hash(PL_PASSWORD_HASH, password):
        return {"username": env_username, "display_name": "Listing team"}
    return None


def upsert_pl_user(username, display_name, password):
    username = (username or "").strip().lower()
    display_name = (display_name or "").strip()[:80]
    slug = username.replace("_", "").replace(".", "").replace("-", "")
    if not username or not display_name or not password:
        raise ValueError("Username, display name, and password are required.")
    if len(username) > 40 or not slug.isalnum():
        raise ValueError("Username can use letters, numbers, dots, hyphens and underscores only.")
    db = get_db()
    password_hash = generate_password_hash(password)
    existing = find_pl_user(username)
    if existing:
        db.execute(
            "UPDATE pl_users SET display_name=?, password_hash=? WHERE id=?",
            (display_name, password_hash, existing["id"]),
        )
    else:
        db.execute(
            "INSERT INTO pl_users (username, display_name, password_hash, created_at) VALUES (?,?,?,?)",
            (username, display_name, password_hash, datetime.utcnow().isoformat()),
        )
    db.commit()


def current_listing_owner():
    if session.get("is_pl"):
        return (session.get("pl_username") or "").strip() or "listing-team"
    return "admin"


def product_listed_by(row):
    if not row:
        return "admin"
    owner = (row.get("listed_by") if isinstance(row, dict) else None) or "admin"
    return str(owner).strip() or "admin"


def pl_can_manage(row):
    username = (session.get("pl_username") or "").strip()
    return bool(username) and product_listed_by(row) == username


def fetch_pl_owned_product(product_id):
    row = get_db().execute("SELECT * FROM products WHERE id=?", (product_id,)).fetchone()
    if not row or not pl_can_manage(row):
        abort(404)
    return row


def pl_required(view):
    @wraps(view)
    def wrapped(*args, **kwargs):
        if not session.get("is_pl"):
            flash("Please sign in to access the listing team dashboard.", "error")
            return redirect(url_for("pl_login"))
        return view(*args, **kwargs)

    return wrapped


@app.route("/pl/login", methods=["GET", "POST"])
def pl_login():
    if request.method == "POST":
        if login_locked("pl-login"):
            flash("Too many sign-in attempts. Wait 15 minutes and try again.", "error")
        else:
            username = request.form.get("username", "")
            password = request.form.get("password", "")
            user = authenticate_pl(username, password)
            if user:
                clear_login_failures("pl-login")
                session["is_pl"] = True
                session["pl_username"] = user["username"]
                session["pl_display_name"] = user.get("display_name") or user["username"]
                session["pl_seen_at"] = time.time()
                session["_csrf"] = secrets.token_urlsafe(32)
                flash(f"Welcome, {session['pl_display_name']}.", "success")
                return redirect(url_for("pl_dashboard"))
            record_login_failure("pl-login")
            flash("Incorrect username or password.", "error")
    return render_template("pl_login.html")


@app.post("/pl/logout")
@pl_required
def pl_logout():
    session.pop("is_pl", None)
    session.pop("pl_username", None)
    session.pop("pl_display_name", None)
    session.pop("pl_seen_at", None)
    flash("You have been signed out.", "success")
    return redirect(url_for("pl_login"))


@app.route("/pl")
@pl_required
def pl_dashboard():
    db = get_db()
    username = (session.get("pl_username") or "").strip()
    q = (request.args.get("q") or "").strip()
    owned = [
        product(row)
        for row in db.execute("SELECT * FROM products WHERE listed_by=? ORDER BY id DESC", (username,)).fetchall()
    ]
    products = [item for item in owned if not item.get("is_draft") and staff_product_matches(item, q)]
    draft_products = [item for item in owned if item.get("is_draft") and staff_product_matches(item, q)]
    pending = db.execute(
        "SELECT * FROM pl_password_requests WHERE username=? AND status='pending' ORDER BY id DESC LIMIT 1",
        (username,),
    ).fetchone()
    return render_template(
        "pl_dashboard.html",
        products=products,
        draft_products=draft_products,
        product_search=q,
        pending_password_request=pending,
    )


@app.route("/pl/password-request", methods=["GET", "POST"])
@pl_required
def pl_password_request():
    username = (session.get("pl_username") or "").strip()
    display_name = session.get("pl_display_name") or username
    pending = get_db().execute(
        "SELECT * FROM pl_password_requests WHERE username=? AND status='pending' ORDER BY id DESC LIMIT 1",
        (username,),
    ).fetchone()
    if request.method == "POST":
        current = request.form.get("current_password", "")
        password = request.form.get("password", "")
        confirm = request.form.get("confirm_password", "")
        if not authenticate_pl(username, current):
            flash("Current password is incorrect.", "error")
        elif len(password) < 6:
            flash("New password must be at least 6 characters.", "error")
        elif password != confirm:
            flash("The new passwords do not match.", "error")
        else:
            db = get_db()
            if pending:
                db.execute(
                    "UPDATE pl_password_requests SET password_hash=?, display_name=?, created_at=? WHERE id=?",
                    (generate_password_hash(password), display_name, datetime.utcnow().isoformat(), pending["id"]),
                )
            else:
                db.execute(
                    """
                    INSERT INTO pl_password_requests (username, display_name, password_hash, status, created_at)
                    VALUES (?,?,?,'pending',?)
                    """,
                    (username, display_name, generate_password_hash(password), datetime.utcnow().isoformat()),
                )
            db.commit()
            flash("Password change request sent to admin. It will apply after approval.", "success")
            return redirect(url_for("pl_dashboard"))
    return render_template("pl_password_request.html", pending_password_request=pending)


@app.route("/pl/main-categories", methods=["GET", "POST"])
@pl_required
def pl_main_categories():
    if request.method == "POST":
        handle_main_category_form()
        return redirect(url_for("pl_main_categories"))
    return render_template(
        "manage_main_categories.html",
        categories=get_db().execute("SELECT * FROM main_categories ORDER BY id").fetchall(),
        back_url=url_for("pl_dashboard"),
        save_url=url_for("pl_main_categories"),
    )


@app.route("/pl/sub-categories", methods=["GET", "POST"])
@pl_required
def pl_sub_categories():
    if request.method == "POST":
        handle_sub_category_form()
        return redirect(url_for("pl_sub_categories"))
    return render_template(
        "manage_sub_categories.html",
        categories=get_db().execute("SELECT * FROM sub_categories ORDER BY main_category, id").fetchall(),
        main_categories=load_main_categories(),
        back_url=url_for("pl_dashboard"),
        save_url=url_for("pl_sub_categories"),
    )


@app.route("/pl/sub-categories-2", methods=["GET", "POST"])
@pl_required
def pl_sub_categories_2():
    if request.method == "POST":
        handle_sub_category_2_form()
        return redirect(url_for("pl_sub_categories_2"))
    return render_template(
        "manage_sub_categories_2.html",
        categories=get_db().execute("SELECT * FROM sub_categories_2 ORDER BY main_category, sub_category, id").fetchall(),
        main_categories=load_main_categories(),
        sub_categories=load_sub_categories(),
        back_url=url_for("pl_dashboard"),
        save_url=url_for("pl_sub_categories_2"),
    )


@app.route("/pl/sub-categories-3", methods=["GET", "POST"])
@pl_required
def pl_sub_categories_3():
    if request.method == "POST":
        handle_sub_category_3_form()
        return redirect(url_for("pl_sub_categories_3"))
    return render_template(
        "manage_sub_categories_3.html",
        categories=get_db().execute(
            "SELECT * FROM sub_categories_3 ORDER BY main_category, sub_category, sub_category_2, id"
        ).fetchall(),
        main_categories=load_main_categories(),
        sub_categories=load_sub_categories(),
        sub_categories_2=load_sub_categories_2(),
        back_url=url_for("pl_dashboard"),
        save_url=url_for("pl_sub_categories_3"),
    )


@app.route("/pl/sub-categories-4", methods=["GET", "POST"])
@pl_required
def pl_sub_categories_4():
    if request.method == "POST":
        handle_sub_category_4_form()
        return redirect(url_for("pl_sub_categories_4"))
    return render_template(
        "manage_sub_categories_4.html",
        categories=get_db().execute(
            "SELECT * FROM sub_categories_4 ORDER BY main_category, sub_category, sub_category_2, sub_category_3, id"
        ).fetchall(),
        main_categories=load_main_categories(),
        sub_categories=load_sub_categories(),
        sub_categories_2=load_sub_categories_2(),
        sub_categories_3=load_sub_categories_3(),
        back_url=url_for("pl_dashboard"),
        save_url=url_for("pl_sub_categories_4"),
    )


@app.route("/pl/new", methods=["GET", "POST"])
@pl_required
def pl_listing_new():
    if request.method == "POST":
        try:
            saved_id = save_product_from_form()
            if (request.form.get("save_mode") or "").strip().lower() == "draft":
                flash("Draft saved. You can keep editing and save again anytime.", "success")
                return redirect(url_for("pl_listing_edit", product_id=saved_id))
            flash("Product created successfully.", "success")
            return redirect(url_for("pl_dashboard"))
        except (IntegrityError, ValueError) as error:
            rollback_db()
            flash(f"Product was not saved: {friendly_product_error(error)}", "error")
    return render_template("admin_product_form.html", **product_form_context())


@app.route("/pl/<int:product_id>/edit", methods=["GET", "POST"])
@pl_required
def pl_listing_edit(product_id):
    row = fetch_pl_owned_product(product_id)
    item = product(row)
    if request.method == "POST":
        try:
            save_product_from_form(product_id=product_id)
            if (request.form.get("save_mode") or "").strip().lower() == "draft":
                flash("Draft updated. You can keep editing and save again anytime.", "success")
                return redirect(url_for("pl_listing_edit", product_id=product_id))
            flash("Product updated successfully.", "success")
            return redirect(url_for("pl_dashboard"))
        except (IntegrityError, ValueError) as error:
            rollback_db()
            flash(f"Product was not updated: {friendly_product_error(error)}", "error")
            item = product(fetch_pl_owned_product(product_id))
    return render_template("admin_product_form.html", **product_form_context(item))


@app.post("/pl/<int:product_id>/copy-draft")
@pl_required
def pl_listing_copy_draft(product_id):
    username = (session.get("pl_username") or "").strip()
    if not username:
        flash("Please sign in to the listing team dashboard.", "error")
        return redirect(url_for("pl_login"))
    try:
        # Ensure the source belongs to this PL user before copying.
        fetch_pl_owned_product(product_id)
        new_id = copy_product_as_draft(
            product_id,
            listed_by=username,
            require_owner=username,
        )
        flash("Copied to your drafts. Edit the draft, then publish when ready.", "success")
        return redirect(url_for("pl_listing_edit", product_id=new_id))
    except (IntegrityError, ValueError) as error:
        rollback_db()
        flash(str(error) if isinstance(error, ValueError) else "Could not copy that product.", "error")
        return redirect(request.referrer or url_for("pl_dashboard"))


@app.post("/pl/<int:product_id>/image/<int:slot>/delete")
@pl_required
def pl_product_image_delete(product_id, slot):
    row = fetch_pl_owned_product(product_id)
    remove_saved_product_image(product_id, slot, row["sku"])
    flash("Image deleted.", "success")
    return redirect(url_for("pl_listing_edit", product_id=product_id))


@app.post("/pl/<int:product_id>/delete")
@pl_required
def pl_listing_delete(product_id):
    try:
        delete_product_record(product_id, listed_by=session.get("pl_username"))
        flash("Product deleted.", "success")
    except ValueError as error:
        rollback_db()
        flash(str(error), "error")
    except IntegrityError:
        rollback_db()
        flash("This product could not be deleted because other records still depend on it.", "error")
    return redirect(url_for("pl_dashboard"))


if __name__ == "__main__":
    # Prefer: gunicorn -c gunicorn.conf.py app:app
    app.run(debug=False, host="127.0.0.1", port=int(os.environ.get("PORT", 5001)))
