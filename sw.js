// keeps the game files on the device after the first visit, so the next launches load from the device.
// The page itself always comes from the internet first (so updates show at once).
// When a model / gltf.js / music file changes, bump VERSION so devices download the new one.
const VERSION = 'game-v1';
self.addEventListener('install', e => self.skipWaiting());
self.addEventListener('activate', e => e.waitUntil(caches.keys().then(ks => Promise.all(ks.filter(k => k !== VERSION).map(k => caches.delete(k)))).then(() => self.clients.claim())));
self.addEventListener('fetch', e => {
  const r = e.request; if (r.method !== 'GET') return;
  const u = new URL(r.url); if (u.protocol !== 'https:') return;
  const same = u.origin === location.origin;
  if (same && (r.mode === 'navigate' || u.pathname.endsWith('/') || u.pathname.endsWith('.html') || u.pathname.endsWith('sw.js'))){
    e.respondWith(fetch(r).then(res => { if (res.status === 200){ const cp = res.clone(); caches.open(VERSION).then(c => c.put(r, cp)); } return res; })
      .catch(() => caches.match(r, {ignoreSearch: true})));
    return;
  }
  if (!same && !/(^|\.)cdn\.jsdelivr\.net$|^fonts\.(googleapis|gstatic)\.com$/.test(u.host)) return;   // multiplayer signalling etc. never cached
  e.respondWith(caches.open(VERSION).then(async c => {
    const hit = await c.match(r); if (hit) return hit;
    const res = await fetch(r); if (res.status === 200 || res.type === 'opaque') c.put(r, res.clone()); return res;
  }));
});
