# Client product images

The client can replace the demo images without changing any code.

1. Find the product SKU on its product page, for example `AR-SHO-01`.
2. Create a matching folder here: `static/images/AR-SHO-01/`.
3. Add the product images with these exact names:

```text
static/images/AR-SHO-01/main.jpg   # main product image
static/images/AR-SHO-01/2.jpg      # optional second gallery image
static/images/AR-SHO-01/3.jpg      # optional third gallery image
```

Use JPG images, ideally square and at least 1200 × 1200 pixels. The website automatically uses these local client images; if a product folder has no `main.jpg`, it continues to show the included demo image.

Existing product SKUs:

`AR-PNT-01`, `AR-PNT-02`, `AR-SHR-01`, `AR-SHR-02`, `AR-JKT-01`, `AR-JKT-02`, `AR-WLT-01`, `AR-PRS-01`, `AR-BLT-01`, `AR-SHO-01`, `AR-SHO-02`.
