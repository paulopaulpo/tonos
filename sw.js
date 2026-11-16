// Tonos service worker for the standalone copy (GitHub Pages). build.py fills in the build stamp and the file list.
// Goal: the installed app opens at once and works with no internet; a new version arrives the next time it is online.
const BUILD = '20261116-023201';
const CACHE = 'tonos-app';
const SHELL = ["./", "index.html", "icons/icon-192.png", "icons/icon-512.png", "state.json", "manifest.webmanifest"];
const CDN = ['fonts.googleapis.com', 'fonts.gstatic.com', 'cdnjs.cloudflare.com'];
const STATE_EVERY = 10 * 60 * 1000;      // the page asks for state.json every 0.9 s; the network is asked this often
let stateChecked = 0;

self.addEventListener('install', e => {
  e.waitUntil(caches.open(CACHE)
    .then(c => Promise.all(SHELL.map(u => c.add(new Request(u, { cache: 'reload' })).catch(() => {}))))
    .then(() => self.skipWaiting()));
});
self.addEventListener('activate', e => {
  e.waitUntil(caches.keys().then(ks => Promise.all(ks.filter(k => k !== CACHE).map(k => caches.delete(k)))).then(() => self.clients.claim()));
});

const store = (key, res) => { if (res && (res.ok || res.type === 'opaque')) { const copy = res.clone(); caches.open(CACHE).then(c => c.put(key, copy)).catch(() => {}); } return res; };
const timeout = (p, ms) => new Promise((ok, no) => { const t = setTimeout(() => no(new Error('slow')), ms); p.then(v => { clearTimeout(t); ok(v); }, err => { clearTimeout(t); no(err); }); });

self.addEventListener('fetch', e => {
  if (e.request.method !== 'GET') return;
  const url = new URL(e.request.url);
  const own = url.origin === location.origin;
  if (!own && !CDN.includes(url.hostname)) return;

  // state.json: answer from the saved copy, refresh it now and then
  if (own && url.pathname.endsWith('/state.json')) {
    const key = url.origin + url.pathname;
    e.respondWith(caches.match(key).then(hit => {
      if (hit && Date.now() - stateChecked < STATE_EVERY) return hit;
      stateChecked = Date.now();
      const fresh = fetch(key, { cache: 'no-store' }).then(r => store(key, r));
      if (!hit) return fresh;
      e.waitUntil(fresh.catch(() => {}));
      return hit;
    }));
    return;
  }

  // fonts and abcjs: saved copy first, refreshed in the background
  if (!own) {
    e.respondWith(caches.match(e.request).then(hit => {
      const fresh = fetch(e.request).then(r => store(e.request, r));
      if (!hit) return fresh;
      e.waitUntil(fresh.catch(() => {}));
      return hit;
    }));
    return;
  }

  // the app itself: the network first (so updates arrive), the saved copy after 3 s or when offline
  e.respondWith(
    timeout(fetch(e.request), 3000).then(r => store(e.request, r))
      .catch(() => caches.match(e.request, { ignoreSearch: true }).then(hit => hit || fetch(e.request)))
  );
});
