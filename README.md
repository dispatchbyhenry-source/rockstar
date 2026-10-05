# AR Shopping World

Flask storefront for shoes, apparel, leather goods, workwear, sports, and related catalog items. Shoppers browse a red-themed site, add sized/coloured stock to a cart, and place orders. Staff (admin and product listing / PL) manage catalog, partners, and fulfilment. Data lives in **PostgreSQL**. The UI is Jinja templates plus Tailwind CDN.

This document describes **what the product is for**, **who uses it**, **how pieces connect**, and **how a request actually runs**.

---

## What it is for

| Use | What happens |
|-----|----------------|
| Browse and buy | Home, catalog filters, product pages, likes, reviews, cart, 5-step checkout |
| Regional selling | Products can be limited to Germany, Europe/UK, Germany+Pakistan, Pakistan, Europe+America, or all zones |
| Pricing | Store amounts are PKR-like units; EUR ≈ amount ÷ 302, USD ÷ 278; **19% tax** on product and shipping nets |
| Partners | Signed-in customers apply as **seller** or **dropship**; admin approves; they do not auto-publish SKUs |
| Operations | Admin products, orders, FAQs, categories (5 levels), merchant payment *details*, PL password requests |
| PL team | Separate login; only products with `listed_by` = their username |

Checkout **records** a payment method and creates an order. It does **not** charge Stripe, PayPal, or Klarna APIs.

---

## How the system is connected

```
Browser
  │  HTML (Jinja) · session cookie · /static · /product-image/…
  ▼
nginx (VPS) ── optional; TLS + static files
  ▼
Gunicorn (gthread workers) → Flask (app.py)
  │  psycopg connection pool · cached shop nav (~45s)
  ▼
PostgreSQL  (same machine or same region as the app)
  products, product_images (BYTEA), orders, users,
  partner_applications, categories…, settings, reviews, FAQs
```

| Piece | Role |
|--------|------|
| `app.py` | Routes, sessions, SQL, images, mail, checkout |
| `gunicorn.conf.py` | Production server: bind `127.0.0.1:5001`, workers/threads |
| `templates/` | Shop, checkout, admin, PL |
| `static/images/` | Optional on-disk photos (legacy / fallback); live gallery usually from DB |
| `i18n.py` | Languages, country → language/zone/currency |
| `i18n_storefront.py` | Shopper copy (`t('key')`) |
| `docker-compose.yml` | Local Postgres 16 (`arshop` / `ar_shopping_world` on port 5432) |
| `.env` | `DATABASE_URL`, admin hash, mail, secrets — **do not commit** |
| Gmail SMTP | Contact, admin reset, merchant-verify helpers (needs App Password) |

Python deps: Flask 3, python-dotenv, psycopg (with pool), Pillow, gunicorn. Run with **Gunicorn**, not the Flask development server.

---

## Actors and what they can do

### Shopper (guest or registered)

- Home: hero, category groups, deal of the week, featured products, FAQs, testimonials  
- Catalog `/products` with main / sub / sub2 / sub3 / sub4, sale, new, search  
- Product: gallery, volume discounts, colour then size stock, add to cart / buy now, reviews, likes, optional Amazon/Etsy/eBay “check price”  
- Language in the header (`POST /preferences`); region/currency follow locale (no region/currency dropdowns)  
- Cart in the **session** (not a DB cart)  
- Checkout: guest **or** login/register → address & shipping → payment choice → summary → order  
- Sign-in: Firebase email (verification link sent by Firebase), Google, or Facebook when `FIREBASE_*` is set. Until then, the shop password form still works. Admin and PL do not use Firebase. Gmail SMTP stays for admin reset and merchant codes.  
- Profile: orders by email, partner applications, listings if any  
- Contact form (login required)  
- Become a Partner (`/sell`): Yes/No seller and dropship applications  

Condition (new/used) is stored for staff; it is **not** shown to shoppers.

### Admin (`/admin/login`)

Env username + `ADMIN_PASSWORD_HASH`. Session timeout, CSRF on staff POSTs, login rate limit.

- Dashboard: sales/orders, listings, contacts  
- Products CRUD, unique SKU, images (max **5**, auto-rotated and fitted to **1200×1200**, **2 MB** each), volume prices, Pakistan prices, shipping per zone, `region_visibility`, featured / deal  
- Orders: status, tracking carrier/number  
- Partner applications approve/reject  
- (Legacy) seller `listings` approve → can publish as a product  
- FAQs, main + four sub-category trees  
- Settings: mail test, merchant PayPal/bank/EasyPaisa/JazzCash/Stripe/Apple Pay/Zelle/Klarna fields, PL accounts, PL password request approve/reject  
- Forgot password via token email if mail is configured  

### PL (`/pl/login`)

Separate staff users. They see **only** `products.listed_by = <pl username>`. They can manage those products and the same category trees. Password change is requested to admin, not self-serve.

---

## Request lifecycle (how it works on each click)

1. **`before_request`**: skip static; optional HTTPS redirect; **`init_db()` once** (create/alter tables, seed); default session (`currency` EUR, `language` en, cart, likes, checkout); **`auto_localize_visitor()`** (IP `ip-api.com` once, or `Accept-Language`); staff session expiry; CSRF token.  
2. **`get_db()`**: new `psycopg.connect(DATABASE_URL)` stored on Flask `g`; closed at teardown.  
3. **Route** loads rows (`SELECT * FROM products` is common).  
4. **`product()`** parses colours/sizes JSON, tax, volume tiers, **`apply_product_gallery()`** (query `product_images` per product).  
5. **`visible_catalog`**: drop items whose `region_visibility` does not include the shopper zone.  
6. **Context processor** injects `t()`, cart count, `shop_nav` (**full catalog again** for the Products mega-menu), language list.  
7. **HTML** loads Tailwind/Font Awesome/Google Fonts from CDNs.  
8. **Images**: `<img src="/product-image/<id>/<slot>">` reads BYTEA from Postgres and streams JPEG/PNG/WebP.

Shopper zone is resolved from delivery address, saved region, profile country, IP, browser language, then defaults (often Europe/Germany).

---

## Catalog and stock

- **Main categories** (e.g. Men, Women, Kids, Unisex, plus Sports/Others/Fashion as configured).  
- **Sub categories 1–4** form the mega-menu and catalog chips.  
- **Product types**: Clothes, Shoes, Accessories, Sports, Others — drive size lists.  
- **Stock**: per colour, only **ticked sizes** with quantities. Cart lines are `product_id` + colour + size.  
- **Volume discounts**: unit price falls at quantity thresholds; Pakistan can have its own price list.  
- **Weight**: product + packing; shipping **under/over 5 kg**, standard vs express, per zone (Germany, Europe, Canada/USA, Pakistan).  

---

## Checkout and orders

```
Cart → /checkout/account → /checkout/details → /checkout/payment → /checkout/summary
```

1. Guest continues without an account, or login/register then details.  
2. Name, email, address (address text can switch shipping zone), standard/express.  
3. Payment radios: always **pay on delivery** and **bank transfer** if bank details exist; **PayPal** if merchant email/client id set; **EasyPaisa/JazzCash** only for Pakistan zone; **Stripe, Klarna, Apple Pay, Zelle** for non-Pakistan when credentials are filled.  
4. Place order: **reserve stock**, `INSERT INTO orders`, clear cart and checkout session, flash success.

Orders store name, email, address, zone, payment **label**, currency, totals, tax, shipping, line items as text, status (`new` and later tracking). **No PSP webhook.** Admin fulfilment is manual.

---

## Partners (Become a Partner)

Must be logged in.

- **Seller**: application + optional photos (`partner_application_images`). Admin approves the **application**, not an automatic catalog SKU.  
- **Dropship**: interest and sell-country. Same approve/reject queue.  

Older **listings** table still exists for signed-in sell-listing approve→product; the current shopper path is partner applications.

---

## Internationalization

- Header language `<select>` posts to `/preferences`.  
- First visit: country from IP (skipped on localhost) or `Accept-Language` (e.g. Spain → Spanish, EUR, Europe).  
- `translate(key, language)` uses `i18n_storefront.STOREFRONT` then fallbacks; many EU languages still fall back to English for some keys.  
- `ur` / `ar` set `dir="rtl"` on `<html>`.  

---

## Database (PostgreSQL)

Created/migrated in `init_db()` on first request. Important tables:

| Table | Purpose |
|--------|---------|
| `products` | Catalog, prices, JSON stock, visibility, `listed_by`, shipping JSON |
| `product_images` | Up to 5 slots, BYTEA ≤ 2 MB |
| `orders` | Checkout results |
| `users` | Shopper accounts |
| `reviews`, `contacts` | Reviews and contact messages |
| `partner_applications` (+ images) | Seller / dropship queue |
| `listings` | Legacy seller listings |
| `main_categories`, `sub_categories` … `_4` | Nav tree |
| `faqs`, `shipping_rates`, settings/merchants | Content and config |
| `pl` / password request tables | PL staff |

Point `DATABASE_URL` at Docker locally or a managed instance (same region as the app for speed). Remote DB + BYTEA images is the main latency source.

---

## Run locally

```bash
docker compose up -d
python3 -m venv .venv
source .venv/bin/activate
pip install -r requirements.txt
cp .env.example .env
# set SECRET_KEY, ADMIN_PASSWORD_HASH, DATABASE_URL
gunicorn -c gunicorn.conf.py
```

App listens on **`http://127.0.0.1:5001`** (`PORT` overrides). Tables and indexes seed on first hit.

`python app.py` still works for a single-process debug run. Use Gunicorn for anything that should handle more than one visitor at a time.

---

## VPS (Hostinger or similar)

Keep this Flask + Jinja frontend. Put **Gunicorn and Postgres on the same VPS** (or the same region). Behind nginx:

```nginx
server {
    listen 80;
    server_name your-domain.com;

    location /static/ {
        alias /path/to/app/static/;
        expires 7d;
    }

    location / {
        proxy_pass http://127.0.0.1:5001;
        proxy_set_header Host $host;
        proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
        proxy_set_header X-Forwarded-Proto $scheme;
    }
}
```

On the VPS `.env`: `TRUST_PROXY=1`, `FORCE_HTTPS=1` and `SESSION_COOKIE_SECURE=1` after TLS works. Keep `workers × DB_POOL_MAX` below your Postgres connection limit (example: 3 workers × 4 pool = 12).

Then Let's Encrypt (certbot) for HTTPS. systemd can run: `gunicorn -c gunicorn.conf.py` from the app directory with the venv.

---

Generate an admin hash:

```bash
python -c "from werkzeug.security import generate_password_hash; print(generate_password_hash('YourStrongPassword'))"
```

Gmail: App Password in `MAIL_PASSWORD`, not the normal Gmail password.

---

## HTTP map (summary)

**Shop:** `/` · `/products` · `/product/<id>` · `/product-image/<id>/<slot>` · `/cart` · `/checkout/*` · `/login` · `/register` · `/profile` · `/sell` · `/sell/seller` · `/sell/dropship` · `/contact` · `/preferences` · `/api/products`

**Admin:** `/admin/login` · `/admin` · `/admin/settings` · `/admin/orders` · `/admin/partners` · `/admin/product/*` · `/admin/faqs` · category managers · `/admin/listings*`

**PL:** `/pl/login` · `/pl` · `/pl/new` · `/pl/<id>/edit` · `/pl/password-request` · category managers

---

## Limits and honesty

- **Concurrency:** Gunicorn workers + a Postgres pool + cached category nav. A VPS with app and DB together can handle hundreds of shoppers at once. Images still come from Postgres BYTEA until you move them to disk/CDN. One VPS will not serve 100,000 people at the same second.  
- **Payments:** method stored; money is not collected in-app.  
- **SQLite `store.db`:** unused.  

Do not commit `.env`. Change default admin credentials before any public host.
