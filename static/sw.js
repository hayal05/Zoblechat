// Zoble Chat — offline app-shell service worker
//
// The server intentionally sends `Cache-Control: no-store` on page routes
// (see _no_store() in app.py) so the phone's back button can't restore a
// stale logged-out/logged-in snapshot via bfcache. That's correct and
// should stay as-is.
//
// The side effect is that the WebView never has a disk-cached copy of the
// page to fall back to when the connection drops — so Median shows its
// native "no internet" error instead of the last screen the user saw.
//
// Cache Storage (used here) is a separate mechanism entirely controlled by
// this script, not by the Cache-Control header, so we can keep a copy of
// the last successful page load for offline fallback without touching the
// no-store behavior at all.

const CACHE_NAME = "zoble-shell-v1";

self.addEventListener("install", () => {
  self.skipWaiting();
});

self.addEventListener("activate", (event) => {
  event.waitUntil(
    caches
      .keys()
      .then((keys) =>
        Promise.all(keys.filter((k) => k !== CACHE_NAME).map((k) => caches.delete(k)))
      )
      .then(() => self.clients.claim())
  );
});

self.addEventListener("fetch", (event) => {
  const req = event.request;
  if (req.method !== "GET") return;

  const url = new URL(req.url);
  if (url.origin !== self.location.origin) return;

  // Full page loads (e.g. "/", "/login") — network first, cached-copy
  // fallback when offline.
  if (req.mode === "navigate") {
    event.respondWith(
      fetch(req)
        .then((res) => {
          const copy = res.clone();
          caches.open(CACHE_NAME).then((cache) => cache.put(req, copy));
          return res;
        })
        .catch(async () => {
          const cache = await caches.open(CACHE_NAME);
          // Try the exact page the user was requesting first...
          const exact = await cache.match(req);
          if (exact) return exact;
          // ...otherwise fall back to whatever page was last cached.
          const lastKnown = await cache.match("/");
          if (lastKnown) return lastKnown;
          // Brand-new user, offline, nothing cached yet — small inline
          // fallback instead of the raw WebView/browser error.
          return new Response(
            "<!DOCTYPE html><html><head><meta name='viewport' content='width=device-width, initial-scale=1.0'>" +
              "<style>body{font-family:sans-serif;text-align:center;padding:3rem 1.5rem;color:#333}</style></head>" +
              "<body><h2>You're offline</h2><p>Reconnect to load Zoble Chat.</p></body></html>",
            { headers: { "Content-Type": "text/html" } }
          );
        })
    );
    return;
  }

  // Static assets (CSS, images, sounds) — cache-first, refresh in background.
  if (url.pathname.startsWith("/static/")) {
    event.respondWith(
      caches.open(CACHE_NAME).then(async (cache) => {
        const cached = await cache.match(req);
        const networkFetch = fetch(req)
          .then((res) => {
            cache.put(req, res.clone());
            return res;
          })
          .catch(() => cached);
        return cached || networkFetch;
      })
    );
  }
});
