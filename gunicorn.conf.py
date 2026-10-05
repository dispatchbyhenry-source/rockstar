import os

bind = f"127.0.0.1:{os.environ.get('PORT', '5001')}"
workers = int(os.environ.get("WEB_CONCURRENCY") or 3)
threads = int(os.environ.get("GUNICORN_THREADS") or 2)
worker_class = "gthread"
timeout = int(os.environ.get("GUNICORN_TIMEOUT") or 120)
keepalive = 5
max_requests = 1000
max_requests_jitter = 50
preload_app = False
accesslog = "-"
errorlog = "-"
wsgi_app = "app:app"
