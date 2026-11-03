// عالم دبا الحقيقي للعبة «مغامرات عيال وليد» — three.js r149 (النسخة العامة THREE)
// يبني من بيانات dibba_scene.json: الأرض الحقيقية، البحر، الشوارع، البيوت، مزارع النخيل، لوحات الأماكن، وخريطة صغيرة.
// كل الإحداثيات داخل اللعبة = إحداثيات البيانات ناقص (ox, oz) — يعني المخيّم في (0,0).
'use strict';
window.DibbaWorld = function(T, D, cfg){
  const PI = Math.PI, OX = cfg.ox, OZ = cfg.oz;
  const SW = D.size[0], SH = D.size[1], R = D.res, DX = SW/(R - 1), DZ = SH/(R - 1);
  const X0 = -SW/2 - OX, Z0 = -SH/2 - OZ, X1 = X0 + SW, Z1 = Z0 + SH;
  const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
  const sm = (e0, e1, x) => { const t = clamp((x - e0)/(e1 - e0), 0, 1); return t*t*(3 - 2*t); };
  let seed = 12345; const rnd = () => { seed = (seed*1664525 + 1013904223) >>> 0; return seed/4294967296; };
  const pick = a => a[Math.floor(rnd()*a.length)];
  const sh = p => [p[0] - OX, p[1] - OZ];
  function clean(p){ const q = p.slice(); if (q.length > 1 && q[0][0] === q[q.length - 1][0] && q[0][1] === q[q.length - 1][1]) q.pop(); return q; }
  // ---------- data in game coordinates ----------
  const roads = D.roads.map(r => ({h: r.h, n: r.n, bw: r.bw, p: r.p.map(sh)}));
  const blds = D.blds.map(b => ({p: clean(b.p.map(sh)), lv: b.lv, gen: b.gen, g: b.g || 0}));
  const greens = D.green.map(g => clean(g.p.map(sh))).filter(p => p.length >= 3);
  const wadis = (D.wadis || []).map(w => w.p.map(sh));
  const waters = (D.waters || []).map(w => ({k: w.k, sea: w.sea, p: clean(w.p.map(sh))}));
  const pois = (D.pois || []).map(p => ({n: p.n, k: p.k, c: sh(p.c)}));
  const CN = D.corn || null; var CTOP = () => -1e9;
  const CZX = CN ? CN.ex.map(p => { const q = p.map(c => [c[0] - OX, c[1] - OZ]); let x0 = 1e9, x1 = -1e9, z0 = 1e9, z1 = -1e9; q.forEach(c => { x0 = Math.min(x0, c[0]); x1 = Math.max(x1, c[0]); z0 = Math.min(z0, c[1]); z1 = Math.max(z1, c[1]); }); return {p: q, x0, x1, z0, z1}; }) : [];
  function inCZ(x, z){ for (const e of CZX) if (x >= e.x0 && x <= e.x1 && z >= e.z0 && z <= e.z1 && inPoly(x, z, e.p)) return true; return false; }
  const CSTRIP = CN ? CN.strip.map(c => [c[0] - OX, c[1] - OZ]) : null;
  const RBS = CN ? [CN.rb[0].c[0] - OX, CN.rb[0].c[1] - OZ, CN.rS + 30] : null; const nearRBS = (x, z) => RBS && Math.hypot(x - RBS[0], z - RBS[1]) < RBS[2];

  // ---------- heights (decimetres → metres) ----------
  const bin = atob(D.h16), u8 = new Uint8Array(bin.length); for (let i = 0; i < bin.length; i++) u8[i] = bin.charCodeAt(i);
  const q16 = new Int16Array(u8.buffer), G = new Float32Array(R*R); for (let i = 0; i < R*R; i++) G[i] = q16[i]/10;
  // scanline fill of a polygon on the height grid: fn(cellIndex)
  function rasterPoly(p, fn){
    let zmin = 1e9, zmax = -1e9; for (const c of p){ zmin = Math.min(zmin, c[1]); zmax = Math.max(zmax, c[1]); }
    const j0 = Math.max(0, Math.ceil((zmin - Z0)/DZ)), j1 = Math.min(R - 1, Math.floor((zmax - Z0)/DZ));
    for (let j = j0; j <= j1; j++){
      const z = Z0 + j*DZ, xs = [];
      for (let k = 0, m = p.length - 1; k < p.length; m = k++){ const a = p[k], b = p[m]; if ((a[1] > z) !== (b[1] > z)) xs.push(a[0] + (z - a[1])*(b[0] - a[0])/(b[1] - a[1])); }
      xs.sort((a, b) => a - b);
      for (let k = 0; k + 1 < xs.length; k += 2){ const i0 = Math.max(0, Math.ceil((xs[k] - X0)/DX)), i1 = Math.min(R - 1, Math.floor((xs[k + 1] - X0)/DX)); for (let i = i0; i <= i1; i++) fn(j*R + i); }
    }
  }
  // the harbour basin and the canal around the island are real water: carve them into the ground
  const carved = new Uint8Array(R*R);
  waters.forEach(w => { if (w.sea && w.p.length > 2) rasterPoly(w.p, k => carved[k] = 1); });
  // distance (in metres) from every cell to the shore, both ways (two-pass chamfer)
  function dist(mask){
    const d = new Float32Array(R*R), S2 = Math.SQRT2;
    for (let k = 0; k < R*R; k++) d[k] = mask[k] ? 0 : 1e9;
    for (let j = 0; j < R; j++) for (let i = 0; i < R; i++){ const k = j*R + i; let v = d[k]; if (!v) continue;
      if (i > 0) v = Math.min(v, d[k - 1] + 1); if (j > 0){ v = Math.min(v, d[k - R] + 1); if (i > 0) v = Math.min(v, d[k - R - 1] + S2); if (i < R - 1) v = Math.min(v, d[k - R + 1] + S2); } d[k] = v; }
    for (let j = R - 1; j >= 0; j--) for (let i = R - 1; i >= 0; i--){ const k = j*R + i; let v = d[k]; if (!v) continue;
      if (i < R - 1) v = Math.min(v, d[k + 1] + 1); if (j < R - 1){ v = Math.min(v, d[k + R] + 1); if (i < R - 1) v = Math.min(v, d[k + R + 1] + S2); if (i > 0) v = Math.min(v, d[k + R - 1] + S2); } d[k] = v; }
    for (let k = 0; k < R*R; k++) d[k] *= DX; return d;
  }
  const seaM = new Uint8Array(R*R), landM = new Uint8Array(R*R);
  for (let k = 0; k < R*R; k++){ const s = G[k] < 0 || carved[k]; seaM[k] = s ? 1 : 0; landM[k] = s ? 0 : 1; }
  const dSea = dist(seaM), dLand = dist(landM);   // land cells: metres to the sea; sea cells: metres to land
  const SHORE = new Float32Array(R*R);   // signed: + on land, - at sea
  for (let k = 0; k < R*R; k++){
    if (seaM[k]){ const s = Math.max(0, dLand[k] - DX/2); SHORE[k] = -s; G[k] = Math.max(-8.5, -1.6 - s*0.12); if (carved[k]) G[k] = Math.max(G[k], -3); }
    else { const s = Math.max(0, dSea[k] - DX/2); SHORE[k] = s; G[k] = G[k] + (Math.min(G[k], 0.25 + s*0.07) - G[k])*(1 - sm(40, 90, s)); }   // a sandy beach down to the water
  }
  // bilinear sample of the grid (for edits)
  function at(x, z){ let fx = clamp((x - X0)/DX, 0, R - 1.001), fz = clamp((z - Z0)/DZ, 0, R - 1.001); const i = fx | 0, j = fz | 0; fx -= i; fz -= j; const k = j*R + i;
    return G[k]*(1 - fx)*(1 - fz) + G[k + 1]*fx*(1 - fz) + G[k + R]*(1 - fx)*fz + G[k + R + 1]*fx*fz; }
  // let the game shape the ground where its places need it (flat pads, dunes, the pearl island, the wadi and the mountain village)
  function region(x0, z0, x1, z1, fn){
    const i0 = Math.max(0, Math.floor((x0 - X0)/DX)), i1 = Math.min(R - 1, Math.ceil((x1 - X0)/DX)), j0 = Math.max(0, Math.floor((z0 - Z0)/DZ)), j1 = Math.min(R - 1, Math.ceil((z1 - Z0)/DZ));
    for (let j = j0; j <= j1; j++) for (let i = i0; i <= i1; i++){ const k = j*R + i; G[k] = fn(X0 + i*DX, Z0 + j*DZ, G[k], k); }
  }
  if (cfg.edit) cfg.edit({region, at, X0, Z0, DX, DZ, R, G, SHORE});
  if (CN){ const ax = CN.axis.concat(CN.axB).map(c => [c[0] - OX, c[1] - OZ]); const axH = ax.map(c => { const i = clamp(Math.round((c[0] - X0)/DX), 0, R - 1), j = clamp(Math.round((c[1] - Z0)/DZ), 0, R - 1); return G[j*R + i]; });
    const hAx = (x, z) => { let bd = 1e18, bh = 0; for (let i = 0; i < ax.length; i++){ const d = (ax[i][0] - x)**2 + (ax[i][1] - z)**2; if (d < bd){ bd = d; bh = axH[i]; } } return bh; };
    const rb0 = CN.rb[0], rbx = rb0.c[0] - OX, rbz = rb0.c[1] - OZ, rbR = (rb0.ro || rb0.r + 4.6) + 45;
    const segD = (x, z, p) => { let bd = 1e18; for (let i = 0; i < p.length; i++){ const a = p[i], b = p[(i + 1) % p.length], vx = b[0] - a[0], vz = b[1] - a[1], l2 = vx*vx + vz*vz || 1, t = clamp(((x - a[0])*vx + (z - a[1])*vz)/l2, 0, 1), d = (x - a[0] - vx*t)**2 + (z - a[1] - vz*t)**2; if (d < bd) bd = d; } return Math.sqrt(bd); };
    const zoneD = (x, z) => { if (inPoly(x, z, CSTRIP) || inCZ(x, z)) return 0; let d = Math.max(0, Math.hypot(x - rbx, z - rbz) - rbR); d = Math.min(d, segD(x, z, CSTRIP)); for (const e of CZX) if (x > e.x0 - d && x < e.x1 + d && z > e.z0 - d && z < e.z1 + d) d = Math.min(d, segD(x, z, e.p)); return d; };
    let x0 = 1e9, x1 = -1e9, z0 = 1e9, z1 = -1e9; CSTRIP.forEach(c => { x0 = Math.min(x0, c[0]); x1 = Math.max(x1, c[0]); z0 = Math.min(z0, c[1]); z1 = Math.max(z1, c[1]); }); CZX.forEach(e => { x0 = Math.min(x0, e.x0); x1 = Math.max(x1, e.x1); z0 = Math.min(z0, e.z0); z1 = Math.max(z1, e.z1); }); x0 = Math.min(x0, rbx - rbR); x1 = Math.max(x1, rbx + rbR); z0 = Math.min(z0, rbz - rbR); z1 = Math.max(z1, rbz + rbR);
    const SINK = CN.sink.map(p => p.map(c => [c[0] - OX, c[1] - OZ])); const tgt = new Map(); region(x0 - 80, z0 - 80, x1 + 80, z1 + 80, (x, z, h, k) => { if (!carved[k] && SINK.some(p => inPoly(x, z, p))) return Math.min(h, -2.2); if (carved[k] || h < 0.6) return h; const d = zoneD(x, z); if (d > 70) return h; const w = 1 - sm(0, 70, d); const t = (Math.hypot(x - rbx, z - rbz) < rbR ? hAx(rbx, rbz) : hAx(x, z)) - 0.3; return h + (t - h)*w; }); }

  // height of the ground exactly as the terrain mesh draws it (same triangles)
  function Hc(x, z){
    let fx = (x - X0)/DX, fz = (z - Z0)/DZ; if (fx < 0) fx = 0; else if (fx > R - 1.001) fx = R - 1.001; if (fz < 0) fz = 0; else if (fz > R - 1.001) fz = R - 1.001;
    const ix = fx | 0, iz = fz | 0; fx -= ix; fz -= iz; const k = iz*R + ix, ha = G[k], hb = G[k + R], hd = G[k + 1];
    if (fx + fz <= 1) return ha + (hd - ha)*fx + (hb - ha)*fz;
    const hc = G[k + R + 1]; return hc + (hb - hc)*(1 - fx) + (hd - hc)*(1 - fz);
  }
  // the game can shape the ground finer in places (harbour quays, the camp pad): everything (houses, streets, palms) stands on that
  const H = cfg.ground ? (x, z) => cfg.ground(x, z, Hc(x, z)) : Hc;
  function shoreDistL(x, z){ let fx = clamp((x - X0)/DX, 0, R - 1.001), fz = clamp((z - Z0)/DZ, 0, R - 1.001); const i = fx | 0, j = fz | 0; fx -= i; fz -= j; const k = j*R + i;
    return SHORE[k]*(1 - fx)*(1 - fz) + SHORE[k + 1]*fx*(1 - fz) + SHORE[k + R]*(1 - fx)*fz + SHORE[k + R + 1]*fx*fz; }
  function shoreDist(x, z){ const i = clamp(Math.round((x - X0)/DX), 0, R - 1), j = clamp(Math.round((z - Z0)/DZ), 0, R - 1); return SHORE[j*R + i]; }
  function slopeAt(k){ const i = k % R, j = (k/R) | 0, a = G[j*R + Math.max(0, i - 1)], b = G[j*R + Math.min(R - 1, i + 1)], c = G[Math.max(0, j - 1)*R + i], d = G[Math.min(R - 1, j + 1)*R + i];
    return Math.hypot((b - a)/(2*DX), (d - c)/(2*DZ)); }

  // ---------- masks painted on the ground: palm farms and wadi gravel ----------
  const farmM = new Uint8Array(R*R), wadiM = new Uint8Array(R*R);
  greens.forEach(p => rasterPoly(p, k => farmM[k] = 1));
  wadis.forEach(p => { for (let s = 0; s < p.length - 1; s++){ const a = p[s], b = p[s + 1], L = Math.hypot(b[0] - a[0], b[1] - a[1]), n = Math.max(1, Math.ceil(L/4));
    for (let t = 0; t <= n; t++){ const x = a[0] + (b[0] - a[0])*t/n, z = a[1] + (b[1] - a[1])*t/n, i = Math.round((x - X0)/DX), j = Math.round((z - Z0)/DZ); if (i >= 0 && j >= 0 && i < R && j < R) wadiM[j*R + i] = 1; } } });

  // ---------- terrain colours (per grid point) ----------
  const COL = new Float32Array(R*R*3);
  {
    const sand = new T.Color(0xe3bf86), sand2 = new T.Color(0xd8b07a), beach = new T.Color(0xeedcb2), wet = new T.Color(0xcdb287), floor = new T.Color(0xb9a37a), deepF = new T.Color(0x9c8f72),
      rock = new T.Color(0x9c8672), rock2 = new T.Color(0x86725f), hajar = new T.Color(0x76645a), hajar2 = new T.Color(0x62564e), farm = new T.Color(0xa7ad72), farm2 = new T.Color(0x93a462), gravel = new T.Color(0xcbbfa8), c = new T.Color();
    for (let k = 0; k < R*R; k++){
      const x = X0 + (k % R)*DX, z = Z0 + ((k/R) | 0)*DZ, h = G[k], sl = slopeAt(k), n = Math.sin(x*0.013 + Math.sin(z*0.011)*2) * Math.cos(z*0.017 - x*0.004);
      c.copy(sand).lerp(sand2, 0.35 + 0.35*n);
      const rk = clamp(sl*2.6 - 0.2, 0, 1)*0.95 + clamp((h - 35)/110, 0, 1)*0.6;   // the Hajar mountains: bare brown-grey rock
      if (rk > 0) c.lerp(n > 0 ? rock : rock2, clamp(rk, 0, 0.95));
      if (h > 60 && sl > 0.12) c.lerp(n > 0 ? hajar : hajar2, clamp((h - 60)/160, 0, 0.85)*clamp(sl*3, 0, 1));
      if (wadiM[k] && sl < 0.35) c.lerp(gravel, 0.7);
      if (farmM[k] && h > 0.8) c.lerp(n > 0 ? farm : farm2, 0.75);
      const sd = SHORE[k];
      if (sd >= 0 && sd < 45 && h < 3.2) c.lerp(beach, (1 - sd/45)*0.9);
      if (h < 0.45 && h > -0.8) c.lerp(wet, 0.55); else if (h <= -0.8) c.copy(h < -4 ? deepF : floor);
      if (cfg.color) cfg.color(x, z, h, c);
      COL[k*3] = c.r; COL[k*3 + 1] = c.g; COL[k*3 + 2] = c.b;
    }
  }
  function colorAt(x, z, out){ let fx = clamp((x - X0)/DX, 0, R - 1.001), fz = clamp((z - Z0)/DZ, 0, R - 1.001); const i = fx | 0, j = fz | 0; fx -= i; fz -= j; const k = j*R + i, w = [(1 - fx)*(1 - fz), fx*(1 - fz), (1 - fx)*fz, fx*fz], ks = [k, k + 1, k + R, k + R + 1];
    let r = 0, g = 0, b = 0; for (let q = 0; q < 4; q++){ r += COL[ks[q]*3]*w[q]; g += COL[ks[q]*3 + 1]*w[q]; b += COL[ks[q]*3 + 2]*w[q]; } return out.setRGB(r, g, b); }
  // fine sand grain + wind ripples (tiled every 4 m, multiplied with the colours)
  const sandTex = (function(){
    const cv = document.createElement('canvas'); cv.width = cv.height = 256; const g = cv.getContext('2d'), img = g.createImageData(256, 256);
    for (let y = 0; y < 256; y++) for (let x = 0; x < 256; x++){ const v = 232 + (rnd() - 0.5)*20 + (rnd() < 0.06 ? -28 : 0), i = (y*256 + x)*4; img.data[i] = img.data[i + 1] = img.data[i + 2] = clamp(v, 0, 255); img.data[i + 3] = 255; }
    g.putImageData(img, 0, 0); const t = new T.CanvasTexture(cv); t.encoding = T.sRGBEncoding; t.wrapS = t.wrapT = T.RepeatWrapping; t.anisotropy = 4; return t;
  })();

  // ---------- terrain: 16×16 chunks, full detail near, light version far (with skirts so no cracks show) ----------
  const terrainMat = new T.MeshLambertMaterial({vertexColors: true, map: sandTex});
  const CS = 64, NC = Math.ceil((R - 1)/CS), root = new T.Group(); cfg.scene.add(root);
  const chunks = [], HOLES = cfg.holes || [];
  const inHole = (fi, fj) => HOLES.some(h => fi > h.i0 && fi < h.i1 && fj > h.j0 && fj < h.j1);
  function chunkGeo(ci, cj, step){
    const i0 = ci*CS, i1 = Math.min((ci + 1)*CS, R - 1), j0 = cj*CS, j1 = Math.min((cj + 1)*CS, R - 1);
    const is = [], js = []; for (let i = i0; i < i1; i += step) is.push(i); is.push(i1); for (let j = j0; j < j1; j += step) js.push(j); js.push(j1);
    const nx = is.length, nz = js.length, ux = 4*Math.floor((X0 + i0*DX)/4), uz = 4*Math.floor((Z0 + j0*DZ)/4);
    const nv = nx*nz + 2*(nx + nz)*1, pos = new Float32Array(nv*3), nor = new Float32Array(nv*3), col = new Float32Array(nv*3), uv = new Float32Array(nv*2), idx = [];
    let v = 0;
    const put = (i, j, drop) => { const k = j*R + i, x = X0 + i*DX, z = Z0 + j*DZ, h = G[k];
      const a = G[j*R + Math.max(0, i - 1)], b = G[j*R + Math.min(R - 1, i + 1)], c = G[Math.max(0, j - 1)*R + i], d = G[Math.min(R - 1, j + 1)*R + i];
      let gx = -(b - a)/(2*DX), gz = -(d - c)/(2*DZ), L = Math.hypot(gx, 1, gz);
      pos[v*3] = x; pos[v*3 + 1] = h - drop; pos[v*3 + 2] = z; nor[v*3] = gx/L; nor[v*3 + 1] = 1/L; nor[v*3 + 2] = gz/L;
      col[v*3] = COL[k*3]; col[v*3 + 1] = COL[k*3 + 1]; col[v*3 + 2] = COL[k*3 + 2]; uv[v*2] = (x - ux)/4; uv[v*2 + 1] = (z - uz)/4; return v++; };
    for (let b = 0; b < nz; b++) for (let a = 0; a < nx; a++) put(is[a], js[b], 0);
    for (let b = 0; b < nz - 1; b++) for (let a = 0; a < nx - 1; a++){ if (inHole((is[a] + is[a + 1])/2, (js[b] + js[b + 1])/2)) continue; const A = b*nx + a, B = A + nx, C = B + 1, Dd = A + 1; idx.push(A, B, Dd, B, C, Dd); }
    // skirts down the four edges
    const skirt = (list, rev) => { const base = v; list.forEach(([i, j]) => put(i, j, 14)); for (let s = 0; s < list.length - 1; s++){ if (inHole((list[s][0] + list[s + 1][0])/2, (list[s][1] + list[s + 1][1])/2)) continue; const top0 = list[s][2], top1 = list[s + 1][2], b0 = base + s, b1 = base + s + 1; if (rev) idx.push(top0, b0, top1, top1, b0, b1); else idx.push(top0, top1, b0, top1, b1, b0); } };
    skirt(is.map((i, a) => [i, js[0], a]), false); skirt(is.map((i, a) => [i, js[nz - 1], (nz - 1)*nx + a]), true);
    skirt(js.map((j, b) => [is[0], j, b*nx]), true); skirt(js.map((j, b) => [is[nx - 1], j, b*nx + nx - 1]), false);
    const g = new T.BufferGeometry();
    g.setAttribute('position', new T.BufferAttribute(pos.subarray(0, v*3), 3)); g.setAttribute('normal', new T.BufferAttribute(nor.subarray(0, v*3), 3));
    g.setAttribute('color', new T.BufferAttribute(col.subarray(0, v*3), 3)); g.setAttribute('uv', new T.BufferAttribute(uv.subarray(0, v*2), 2));
    g.setIndex(idx); g.computeBoundingSphere(); return g;
  }
  for (let cj = 0; cj < NC; cj++) for (let ci = 0; ci < NC; ci++){
    const i0 = ci*CS, i1 = Math.min((ci + 1)*CS, R - 1), j0 = cj*CS, j1 = Math.min((cj + 1)*CS, R - 1);
    let mx = -1e9; for (let j = j0; j <= j1; j += 2) for (let i = i0; i <= i1; i += 2) mx = Math.max(mx, G[j*R + i]);
    if (mx < -6.5) continue;   // open sea: the water covers it
    const ch = {ci, cj, x0: X0 + i0*DX, x1: X0 + i1*DX, z0: Z0 + j0*DZ, z1: Z0 + j1*DZ, hi: null, lo: new T.Mesh(chunkGeo(ci, cj, 4), terrainMat), used: 0};
    ch.lo.receiveShadow = true; root.add(ch.lo); chunks.push(ch);
  }
  const rectDist = (o, x, z) => Math.hypot(Math.max(o.x0 - x, 0, x - o.x1), Math.max(o.z0 - z, 0, z - o.z1));

  // ---------- the sea: one water surface at y = 0 that follows the camera; colour and foam come from the real depth ----------
  const depthTex = (function(){ const a = new Uint8Array(R*R*4); for (let k = 0; k < R*R; k++){ const d = clamp(-G[k], 0, 10)*25.5; a[k*4] = a[k*4 + 1] = a[k*4 + 2] = d; a[k*4 + 3] = 255; }
    const t = new T.DataTexture(a, R, R, T.RGBAFormat); t.magFilter = T.LinearFilter; t.minFilter = T.LinearFilter; t.wrapS = t.wrapT = T.ClampToEdgeWrapping; t.needsUpdate = true; return t; })();
  const WATER_Y = cfg.waterY || 0;
  const seaMat = new T.ShaderMaterial({transparent: true, fog: true, depthWrite: false,
    uniforms: T.UniformsUtils.merge([T.UniformsLib.fog, {time: {value: 0}, deep: {value: new T.Color(0x3f8fae)}, shallow: {value: new T.Color(0x8fd0d0)}, foam: {value: new T.Color(0xfbf6ea)},
      dmap: {value: null}, box: {value: new T.Vector4(X0, Z0, SW, SH)}, res: {value: R}, ctr: {value: new T.Vector3()}, nearR: {value: 760}}]),
    vertexShader: `uniform float time; uniform sampler2D dmap; uniform vec4 box; uniform float res; uniform vec3 ctr; uniform float nearR; varying float vD; varying float vW; varying vec3 vWP;
      #include <fog_pars_vertex>
      float depthAt(vec2 p){ vec2 uv = ((p - box.xy)/box.zw*(res - 1.0) + 0.5)/res; return texture2D(dmap, uv).r*10.0; }
      void main(){ vec4 wp = modelMatrix*vec4(position, 1.0); float d = depthAt(wp.xz);
        float w = sin(wp.x*0.18 + time*1.3)*0.16 + sin(wp.z*0.23 - time*1.1)*0.12 + sin((wp.x + wp.z)*0.5 + time*2.0)*0.05;
        w *= smoothstep(0.15, 2.5, d)*(1.0 - smoothstep(nearR*0.8, nearR, max(abs(wp.x - ctr.x), abs(wp.z - ctr.z))));
        wp.y += w; vD = d; vW = w; vWP = wp.xyz;
        vec4 mvPosition = viewMatrix*wp; gl_Position = projectionMatrix*mvPosition;
        #include <fog_vertex>
      }`,
    fragmentShader: `uniform vec3 deep; uniform vec3 shallow; uniform vec3 foam; uniform float time; uniform sampler2D dmap; uniform vec4 box; uniform float res; varying float vD; varying float vW; varying vec3 vWP;
      #include <fog_pars_fragment>
      void main(){ vec2 uv = ((vWP.xz - box.xy)/box.zw*(res - 1.0) + 0.5)/res; float d = texture2D(dmap, uv).r*10.0;
        float k = smoothstep(0.2, 6.0, d); vec3 c = mix(shallow, deep, k);
        c += vec3(0.08)*smoothstep(0.12, 0.3, vW);
        float f = 1.0 - smoothstep(0.0, 0.55 + 0.25*sin(vWP.x*0.15 + vWP.z*0.11 + time*0.9), d);
        c = mix(c, foam, f*0.7); gl_FragColor = linearToOutputTexel(vec4(c, mix(0.62, 0.95, smoothstep(0.0, 3.5, d))));
        #include <fog_fragment>
      }`});
  seaMat.uniforms.dmap.value = depthTex;
  const NEAR_S = 1520, seaNear = new T.Mesh(new T.PlaneGeometry(NEAR_S, NEAR_S, 128, 128).rotateX(-PI/2), seaMat);
  const seaFar = (function(){ const a = NEAR_S/2, b = 30000, p = [], ix = [];
    [[-b, -b], [b, -b], [b, b], [-b, b], [-a, -a], [a, -a], [a, a], [-a, a]].forEach(q => p.push(q[0], 0, q[1]));
    for (let s = 0; s < 4; s++){ const o0 = s, o1 = (s + 1) % 4, i0 = 4 + s, i1 = 4 + (s + 1) % 4; ix.push(o0, i0, o1, o1, i0, i1); }
    const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(p, 3)); g.setIndex(ix); return new T.Mesh(g, seaMat); })();
  seaMat.side = T.DoubleSide;
  [seaNear, seaFar].forEach(m => { m.renderOrder = 1; m.frustumCulled = false; m.position.y = WATER_Y; cfg.scene.add(m); });

  // ---------- the street network (worked out before houses and palms, so nothing is ever placed on a road) ----------
  // real widths in metres: one carriageway of a divided road ≈ 2 lanes (7 m), a town street 7–8 m, plus 2 m sidewalks in town
  const BASEW = {motorway: 14, trunk: 13, primary: 12, secondary: 10, tertiary: 8.5, residential: 7.5, unclassified: 7, living_street: 6, service: 5};
  const RANK = {motorway: 6, trunk: 5, primary: 4, secondary: 3, tertiary: 2, residential: 1, unclassified: 1, living_street: 0, service: 0};
  const RD = [];
  roads.forEach(r => { const p = []; r.p.forEach(c => { if (!p.length || Math.hypot(c[0] - p[p.length - 1][0], c[1] - p[p.length - 1][1]) > 0.4) p.push(c); });
    if (p.length < 2) return; const link = /_link$/.test(r.h), base = r.h.replace('_link', '');
    const closed = p.length > 3 && Math.hypot(p[0][0] - p[p.length - 1][0], p[0][1] - p[p.length - 1][1]) < 1; if (closed) p.pop();
    RD.push({h: r.h, n: r.n, bw: r.bw, base, link, p, closed, W: link ? 6.5 : (BASEW[base] || 6), rank: RANK[base] || 0, major: /^(motorway|trunk|primary|secondary|tertiary)$/.test(base) && !link, dual: null, sw: 0}); });
  const segCount = r => r.closed ? r.p.length : r.p.length - 1, segB = (r, i) => r.p[(i + 1) % r.p.length];
  const RSG = 32, rsh = new Map();
  RD.forEach((r, ri) => { for (let i = 0; i < segCount(r); i++){ const a = r.p[i], b = segB(r, i), m = 14;
    for (let u = Math.floor((Math.min(a[0], b[0]) - m)/RSG); u <= Math.floor((Math.max(a[0], b[0]) + m)/RSG); u++) for (let v = Math.floor((Math.min(a[1], b[1]) - m)/RSG); v <= Math.floor((Math.max(a[1], b[1]) + m)/RSG); v++){ const k = u + ',' + v; (rsh.get(k) || rsh.set(k, []).get(k)).push(ri, i); } } });
  function segNear(x, z, fn){ const L = rsh.get(Math.floor(x/RSG) + ',' + Math.floor(z/RSG)); if (!L) return; for (let k = 0; k < L.length; k += 2){ const r = RD[L[k]], i = L[k + 1], a = r.p[i], b = segB(r, i), vx = b[0] - a[0], vz = b[1] - a[1], l2 = vx*vx + vz*vz || 1, t = clamp(((x - a[0])*vx + (z - a[1])*vz)/l2, 0, 1), px = a[0] + vx*t, pz = a[1] + vz*t; fn(r, i, Math.hypot(x - px, z - pz), t, vx, vz, l2); } }
  // towns: where real buildings stand close together (100 m cells)
  const TC = 100, tcount = new Map(); blds.forEach(b => { if (b.p.length < 3) return; const k = Math.floor(b.p[0][0]/TC) + ',' + Math.floor(b.p[0][1]/TC); tcount.set(k, (tcount.get(k) || 0) + 1); });
  function inTown(x, z){ const a = Math.floor(x/TC), b = Math.floor(z/TC); let n = 0; for (let u = a - 1; u <= a + 1; u++) for (let v = b - 1; v <= b + 1; v++) n += tcount.get(u + ',' + v) || 0; return n >= 14; }
  // divided roads: OSM draws each direction as its own way; find the partner running alongside, the gap between them is the median
  RD.forEach(r => { if (!r.major || r.closed) return; const n = r.p.length, seps = new Array(n).fill(0), sides = new Array(n).fill(0); let found = 0;
    for (let i = 0; i < n; i++){ const a = r.p[Math.max(0, i - 1)], b = r.p[Math.min(n - 1, i + 1)], tx = b[0] - a[0], tz = b[1] - a[1], tl = Math.hypot(tx, tz) || 1, ux = tx/tl, uz = tz/tl, x = r.p[i][0], z = r.p[i][1];
      let best = 1e9, side = 0;
      segNear(x, z, (o, j, d, t, vx, vz, l2) => { if (o === r || !o.major || o.closed) return; const l = Math.sqrt(l2); if (Math.abs((vx*ux + vz*uz)/l) < 0.93) return;
        const px = o.p[j][0] + vx*t - x, pz = o.p[j][1] + vz*t - z, along = px*ux + pz*uz, perp = -px*uz + pz*ux; if (Math.abs(along) > 6 || d < 3.5 || d > 34) return; if (d < best){ best = d; side = Math.sign(perp); } });
      if (best < 1e9){ seps[i] = best; sides[i] = side; found++; } }
    if (found < n*0.6) return; const ok = seps.filter(v => v > 0).sort((a, b) => a - b), med = ok[ok.length >> 1], sd = Math.sign(sides.reduce((s, v) => s + v, 0)) || 1;
    for (let i = 0; i < n; i++) if (!seps[i] || sides[i] !== sd) seps[i] = med;
    r.W = clamp(med - 1.4, 5.5, 7.4); r.dual = {side: sd, mh: seps.map(s => clamp(s/2 - r.W/2, 0, 12))}; });
  RD.forEach(r => { const m = r.p[r.p.length >> 1]; r.sw = r.rank >= 1 && r.base !== 'unclassified' && inTown(m[0], m[1]) ? 2 : 0; if (r.link) r.sw = 0; });
  // the corniche: a paved seafront promenade (7 m) on the sea side of «شارع الكورنيش», only where the open sea (not the canal) is on that side
  const cellK = (x, z) => clamp(Math.round((z - Z0)/DZ), 0, R - 1)*R + clamp(Math.round((x - X0)/DX), 0, R - 1);
  const PROM_W = 7, promPalms = [];
  RD.forEach(r => { r.prom = 0; if (!/كورنيش/.test(r.n || '') || r.closed || r.link) return; const m = r.p.length >> 1, a = r.p[Math.max(0, m - 1)], b = r.p[Math.min(r.p.length - 1, m + (r.p.length > 2 ? 0 : 1))];
    const L = Math.hypot(b[0] - a[0], b[1] - a[1]) || 1, nx = -(b[1] - a[1])/L, nz = (b[0] - a[0])/L, c = r.p[m];
    for (const sg of [1, -1]){ if (r.dual && sg === r.dual.side) continue;
      for (let d = 6; d < 260; d += 4){ const k = cellK(c[0] + nx*sg*d, c[1] + nz*sg*d); if (seaM[k]){ if (!carved[k]) r.prom = sg; break; } } if (r.prom) break; } });
  RD.forEach(r => { if (r.prom && !r.sw) r.sw = 0; });
  RD.forEach(r => { if (r.bw){ r.W = r.bw; r.sw = 0; r.nosw = true; } });
  if (CSTRIP) RD.forEach(r => { if (!/كورنيش/.test(r.n || '')) return; if (r.p.some(c => inPoly(c[0], c[1], CSTRIP) || inCZ(c[0], c[1]) || nearRBS(c[0], c[1]))){ r.sw = 0; r.prom = 0; } });
  // junctions: a node two or more streets share, or a street end that meets another street
  const JS = new Map(), JL = [], jkey = c => Math.round(c[0]*2) + ',' + Math.round(c[1]*2);
  RD.forEach((r, ri) => r.p.forEach((c, i) => { const k = jkey(c); let J = JS.get(k); if (!J){ J = {x: c[0], z: c[1], rs: new Set(), r: 0}; JS.set(k, J); } J.rs.add(ri); }));
  JS.forEach(J => { if (J.rs.size > 1) JL.push(J); });
  RD.forEach((r, ri) => { if (r.closed) return; [r.p[0], r.p[r.p.length - 1]].forEach(c => { const J = JS.get(jkey(c)); if (J.rs.size > 1) return; let hit = null;
    segNear(c[0], c[1], (o, j, d) => { if (o !== r && d < o.W/2 + 1.5) hit = o; }); if (hit){ J.rs.add(RD.indexOf(hit)); JL.push(J); } else J.end = true; }); });
  JL.forEach(J => { J.rs.forEach(ri => { const r = RD[ri]; J.r = Math.max(J.r, r.W/2 + r.sw + (r.dual ? 2 : 0)); }); J.r += 1.2; });
  const JG = 24, jh = new Map(); JL.forEach(J => { for (let u = Math.floor((J.x - 30)/JG); u <= Math.floor((J.x + 30)/JG); u++) for (let v = Math.floor((J.z - 30)/JG); v <= Math.floor((J.z + 30)/JG); v++){ const k = u + ',' + v; (jh.get(k) || jh.set(k, []).get(k)).push(J); } });
  function nearJ(x, z, extra){ const L = jh.get(Math.floor(x/JG) + ',' + Math.floor(z/JG)); if (L) for (const J of L) if (Math.hypot(x - J.x, z - J.z) < J.r + (extra || 0)) return J; return null; }
  // how far a street (asphalt + sidewalk/median) reaches from its centre line
  const reach = (r, i) => r.W/2 + r.sw + (r.prom ? PROM_W : 0) + (r.dual ? Math.max(r.dual.mh[i], r.dual.mh[Math.min(r.p.length - 1, i + 1)]) : 0);
  function nearRoad(x, z, pad){ let on = false; segNear(x, z, (r, i, d) => { if (d < reach(r, i) + (pad || 0)) on = true; }); return on; }
  const liftOf = r => 0.08 + r.rank*0.012;
  // what the kids and the car stand on at (x, z): asphalt, a sidewalk or a median is a little above the bare ground
  function roadTop(x, z){ let best = 0;
    segNear(x, z, (r, i, d, t, vx, vz) => { const lift = liftOf(r); if (d < r.W/2) best = Math.max(best, lift);
      else if (r.sw && d < r.W/2 + r.sw && !nearJ(x, z, 0)) best = Math.max(best, lift + 0.16);
      else if (r.prom && d < r.W/2 + r.sw + PROM_W && !nearJ(x, z, 0)){ const a = r.p[i], side = Math.sign(-(x - a[0])*vz + (z - a[1])*vx); if (side === r.prom) best = Math.max(best, lift + 0.16); }
      else if (r.dual){ const mh = r.dual.mh[i]; if (mh > 0.3 && d < r.W/2 + mh){ const a = r.p[i], side = Math.sign(-(x - a[0])*vz + (z - a[1])*vx); if (side === r.dual.side) best = Math.max(best, lift + 0.18); } } });
    return best; }
  // what is already taken (real buildings and plots) on a 4 m grid
  const EOC = 4, EOX = Math.ceil(SW/EOC) + 1, EOZ = Math.ceil(SH/EOC) + 1, EO = new Uint8Array(EOX*EOZ);
  function eoMark(p, pad){ let x0 = 1e9, x1 = -1e9, z0 = 1e9, z1 = -1e9; p.forEach(c => { x0 = Math.min(x0, c[0]); x1 = Math.max(x1, c[0]); z0 = Math.min(z0, c[1]); z1 = Math.max(z1, c[1]); });
    for (let x = x0 - pad; x <= x1 + pad; x += EOC/2) for (let z = z0 - pad; z <= z1 + pad; z += EOC/2){ if (!pad && !inPolyP(x, z, p)) continue; const i = Math.floor((x - X0)/EOC), j = Math.floor((z - Z0)/EOC); if (i >= 0 && j >= 0 && i < EOX && j < EOZ) EO[j*EOX + i] = 1; } }
  function inPolyP(x, z, p){ let c = false; for (let i = 0, j = p.length - 1; i < p.length; j = i++){ const a = p[i], b = p[j]; if ((a[1] > z) !== (b[1] > z) && x < (b[0] - a[0])*(z - a[1])/(b[1] - a[1]) + a[0]) c = !c; } return c; }
  const eoAt = (x, z) => { const i = Math.floor((x - X0)/EOC), j = Math.floor((z - Z0)/EOC); return i < 0 || j < 0 || i >= EOX || j >= EOZ || EO[j*EOX + i] === 1; };
  blds.forEach(b => { if (b.p.length > 2) eoMark(b.p, 1.5); });
  // fill the empty frontage of town streets with villa plots facing the street (≈20 × 25 m, like the real ones), never in open desert,
  // farms, wadis or the sea, never on a street or over another house
  let plotsAdded = 0;
  if (cfg.fillPlots !== false) RD.forEach(r => {
    if (r.dual || r.closed || !/^(residential|living_street|tertiary|unclassified)$/.test(r.base) || r.link) return;
    for (let i = 0; i < r.p.length - 1; i++){
      const a = r.p[i], b = r.p[i + 1], L = Math.hypot(b[0] - a[0], b[1] - a[1]); if (L < 26) continue;
      const ux = (b[0] - a[0])/L, uz = (b[1] - a[1])/L;
      if (!inTown((a[0] + b[0])/2, (a[1] + b[1])/2)) continue;
      for (const side of [1, -1]){
        const nx = -uz*side, nz = ux*side, f = r.W/2 + Math.max(r.sw, 1) + 0.7;
        for (let s = 3; s < L - 3;){
          const w = 18 + Math.floor(rnd()*5), d = 22 + Math.floor(rnd()*5); if (s + w > L - 3) break;
          const P = (q, o) => [a[0] + ux*q + nx*o, a[1] + uz*q + nz*o], A = P(s, f), B = P(s + w, f), C = P(s + w, f + d), E = P(s, f + d);
          let ok = true, hmin = 1e9, hmax = -1e9;
          for (let qa = 0; qa <= 4 && ok; qa++) for (let qb = 0; qb <= 4 && ok; qb++){ const [x, z] = P(s + w*qa/4, f + d*qb/4);
            if (eoAt(x, z) || shoreDist(x, z) < 25 || nearRoad(x, z, 0.6) || nearJ(x, z, 2) || !inTown(x, z)) ok = false;
            else { const k = clamp(Math.round((z - Z0)/DZ), 0, R - 1)*R + clamp(Math.round((x - X0)/DX), 0, R - 1); if (farmM[k] || wadiM[k]) ok = false; const h = H(x, z); hmin = Math.min(hmin, h); hmax = Math.max(hmax, h); } }
          if (ok && [A, B, C, E].some(c => inCZ(c[0], c[1]))) ok = false;
          if (ok && hmin > 0.8 && hmax - hmin < 3){ const p = [A, B, C, E]; blds.push({p, lv: rnd() < 0.6 ? 2 : 1, gen: 1, g: 0, filled: 1}); eoMark(p, 1.5); plotsAdded++; s += w + 1.5; }
          else s += 2;
        }
      }
    }
  });

  // ---------- buildings: geometry in buckets (base = walls & roofs, seen from far; detail = parapets, gates, tanks… only near) ----------
  const BC = 800, DC = 200;   // chunk sizes (m)
  const key = (x, z, s) => Math.floor(x/s) + ',' + Math.floor(z/s);
  const baseB = new Map(), detB = new Map();
  function bucket(map, k, mat){ let o = map.get(k); if (!o){ o = {}; map.set(k, o); } return o[mat] || (o[mat] = {p: [], n: [], c: [], uv: []}); }
  const _a = new T.Vector3(), _b = new T.Vector3(), _x = new T.Vector3();
  function tri(bk, v0, v1, v2, n, c, t0, t1, t2){
    _a.set(v1[0] - v0[0], v1[1] - v0[1], v1[2] - v0[2]); _b.set(v2[0] - v0[0], v2[1] - v0[1], v2[2] - v0[2]); _x.crossVectors(_a, _b);
    if (_x.x*n[0] + _x.y*n[1] + _x.z*n[2] < 0){ [v1, v2] = [v2, v1]; [t1, t2] = [t2, t1]; }
    bk.p.push(v0[0], v0[1], v0[2], v1[0], v1[1], v1[2], v2[0], v2[1], v2[2]); bk.n.push(n[0], n[1], n[2], n[0], n[1], n[2], n[0], n[1], n[2]); bk.c.push(c.r, c.g, c.b, c.r, c.g, c.b, c.r, c.g, c.b);
    t0 = t0 || [0, 0]; t1 = t1 || [0, 0]; t2 = t2 || [0, 0]; bk.uv.push(t0[0], t0[1], t1[0], t1[1], t2[0], t2[1]);
  }
  function quad(bk, a, b, c4, d, n, col, uv){ tri(bk, a, b, c4, n, col, uv && uv[0], uv && uv[1], uv && uv[2]); tri(bk, a, c4, d, n, col, uv && uv[0], uv && uv[2], uv && uv[3]); }
  function area(p){ let s = 0; for (let i = 0; i < p.length; i++){ const a = p[i], b = p[(i + 1) % p.length]; s += a[0]*b[1] - b[0]*a[1]; } return s/2; }
  function outN(a, b, ccw){ const dx = b[0] - a[0], dz = b[1] - a[1], L = Math.hypot(dx, dz) || 1; return ccw ? [dz/L, 0, -dx/L] : [-dz/L, 0, dx/L]; }
  function walls(bk, p, y0, y1, col, tile, fh, vBase, both){
    const ccw = area(p) > 0; let u = 0;
    for (let i = 0; i < p.length; i++){ const a = p[i], b = p[(i + 1) % p.length], L = Math.hypot(b[0] - a[0], b[1] - a[1]); if (L < 0.05) continue;
      const n = outN(a, b, ccw), u0 = u/tile, u1 = (u + L)/tile; u += L; const v0 = (y0 - vBase)/fh, v1 = (y1 - vBase)/fh, uvs = [[u0, v0], [u1, v0], [u1, v1], [u0, v1]];
      quad(bk, [a[0], y0, a[1]], [b[0], y0, b[1]], [b[0], y1, b[1]], [a[0], y1, a[1]], n, col, uvs);
      if (both) quad(bk, [a[0], y0, a[1]], [b[0], y0, b[1]], [b[0], y1, b[1]], [a[0], y1, a[1]], [-n[0], 0, -n[2]], col, uvs); }
  }
  function flat(bk, p, y, col, up){
    const v = p.map(c => new T.Vector2(c[0], c[1])); let tris; try { tris = T.ShapeUtils.triangulateShape(v, []); } catch (e){ return; }
    const n = [0, up === false ? -1 : 1, 0];
    for (const t of tris) tri(bk, [p[t[0]][0], y, p[t[0]][1]], [p[t[1]][0], y, p[t[1]][1]], [p[t[2]][0], y, p[t[2]][1]], n, col, [p[t[0]][0]/3, p[t[0]][1]/3], [p[t[1]][0]/3, p[t[1]][1]/3], [p[t[2]][0]/3, p[t[2]][1]/3]);
  }
  function box(bk, cx, cz, w, d, y0, h, ang, col){
    const ca = Math.cos(ang), sa = Math.sin(ang), pts = [[-w/2, -d/2], [w/2, -d/2], [w/2, d/2], [-w/2, d/2]].map(([x, z]) => [cx + x*ca - z*sa, cz + x*sa + z*ca]);
    walls(bk, pts, y0, y0 + h, col, 4, 3.6, y0); flat(bk, pts, y0 + h, col);
  }
  function inset(p, d){
    const ccw = area(p) > 0, n = p.length, L = [];
    for (let i = 0; i < n; i++){ const a = p[i], b = p[(i + 1) % n], o = outN(a, b, ccw); L.push([[a[0] - o[0]*d, a[1] - o[2]*d], [b[0] - o[0]*d, b[1] - o[2]*d]]); }
    const out = [];
    for (let i = 0; i < n; i++){ const [p1, p2] = L[(i - 1 + n) % n], [p3, p4] = L[i];
      const den = (p1[0] - p2[0])*(p3[1] - p4[1]) - (p1[1] - p2[1])*(p3[0] - p4[0]); if (Math.abs(den) < 1e-9){ out.push(p3); continue; }
      const t = ((p1[0] - p3[0])*(p3[1] - p4[1]) - (p1[1] - p3[1])*(p3[0] - p4[0]))/den; out.push([p1[0] + t*(p2[0] - p1[0]), p1[1] + t*(p2[1] - p1[1])]); }
    return out;
  }
  const C = s => new T.Color(s);
  const plaster = [0xf4efe4, 0xefe5d2, 0xf7f3ea, 0xe9dcc2, 0xe4d3b4, 0xf1ead9, 0xdcd6cc, 0xeee2c8].map(C), accent = [0xc9b28a, 0xb89a72, 0xd8c7a6, 0xa58d6a, 0xcbbfa9].map(C);
  const fenceC = [0xe6d6b8, 0xdcc8a4, 0xefe3cc, 0xd2bf9c, 0xe9e1d2].map(C), roofC = [0xd9d3c8, 0xcfc9bd, 0xe0dbd0, 0xc8c2b6].map(C), yardC = [0xcbb89a, 0xbfae92, 0xd4c6ae, 0xb7a68c].map(C);
  const gateC = [0x5a4632, 0x3f4b45, 0x6b5a40, 0x2f3a44, 0x7a6448].map(C), doorC = [0x6e4b2e, 0x5a3c25, 0x7b5636, 0x4d3a2a].map(C), white = C(0xf2f2ee), grey = C(0xa8aaa8);
  const GA = 256/384;   // atlas: gate pattern on the left, door on the right
  // collision walls (segments) and the doors of the villas you can go into
  const SEG = [], DOORS = [], BLD_LIST = [], YARDS = [];   // YARDS: paved villa yards (flat), so the kids walk on the paving, not under it
  const palmsYard = [];
  for (const b of blds){
    const p = b.p; if (p.length < 3) continue;
    let cx = 0, cz = 0; p.forEach(c => { cx += c[0]; cz += c[1]; }); cx /= p.length; cz /= p.length;
    if (cx < X0 || cx > X1 || cz < Z0 || cz > Z1) continue;
    if (cfg.skipBuilding && cfg.skipBuilding(cx, cz, p)) continue;
    if (!b.filled && nearRoad(cx, cz, -1.5)) continue;
    if (inCZ(cx, cz) || p.some(c => inCZ(c[0], c[1]))) continue;
    const gs = p.map(c => H(c[0], c[1])), gMin = Math.min(...gs), gAvg = gs.reduce((s, v) => s + v, 0)/gs.length;
    const g = Math.max(gAvg, 0.6), gLow = Math.max(gMin, 0.3) - 1.2;
    const lv = parseFloat(b.lv) || (rnd() < 0.7 ? 1 : 2), fh = 3.7, wall = pick(plaster), trim = pick(accent);
    const kB = key(cx, cz, BC), kD = key(cx, cz, DC);
    const WIN = bucket(baseB, kB, 'win'), BPL = bucket(baseB, kB, 'plain'), DPL = bucket(detB, kD, 'plain'), YARD = bucket(detB, kD, 'yard'), ATL = bucket(detB, kD, 'atlas');
    BLD_LIST.push({p, cx, cz, gen: !!b.gen, kD});
    let house = p;
    if (b.gen){   // a plot with a wall and a gate, the villa inside
      const fence = pick(fenceC), fh2 = 2.5, th = 0.3, ccw = area(p) > 0, gi = b.g || 0;
      for (let i = 0; i < p.length; i++){
        const a = p[i], c2 = p[(i + 1) % p.length], L = Math.hypot(c2[0] - a[0], c2[1] - a[1]); if (L < 0.1) continue;
        const segs = i === gi && L > 8 ? [[0, L/2 - 2.2], [L/2 + 2.2, L]] : [[0, L]], dx = (c2[0] - a[0])/L, dz = (c2[1] - a[1])/L, o = outN(a, c2, ccw);
        for (const [s0, s1] of segs){
          const A = [a[0] + dx*s0, a[1] + dz*s0], Bp = [a[0] + dx*s1, a[1] + dz*s1]; SEG.push([A[0], A[1], Bp[0], Bp[1]]);
          const Ai = [A[0] - o[0]*th, A[1] - o[2]*th], Bi = [Bp[0] - o[0]*th, Bp[1] - o[2]*th];
          quad(BPL, [A[0], gLow, A[1]], [Bp[0], gLow, Bp[1]], [Bp[0], g + fh2, Bp[1]], [A[0], g + fh2, A[1]], o, fence, [[0, 0], [L/4, 0], [L/4, 1], [0, 1]]);
          quad(DPL, [Ai[0], g, Ai[1]], [Bi[0], g, Bi[1]], [Bi[0], g + fh2, Bi[1]], [Ai[0], g + fh2, Ai[1]], [-o[0], 0, -o[2]], fence);
          const cap = fence.clone().multiplyScalar(0.88);
          quad(DPL, [A[0] + o[0]*0.06, g + fh2 + 0.12, A[1] + o[2]*0.06], [Bp[0] + o[0]*0.06, g + fh2 + 0.12, Bp[1] + o[2]*0.06], [Bi[0], g + fh2 + 0.12, Bi[1]], [Ai[0], g + fh2 + 0.12, Ai[1]], [0, 1, 0], cap);
          quad(DPL, [A[0] + o[0]*0.06, g + fh2, A[1] + o[2]*0.06], [Bp[0] + o[0]*0.06, g + fh2, Bp[1] + o[2]*0.06], [Bp[0] + o[0]*0.06, g + fh2 + 0.12, Bp[1] + o[2]*0.06], [A[0] + o[0]*0.06, g + fh2 + 0.12, A[1] + o[2]*0.06], o, cap);
        }
        if (i === gi && L > 8){   // the gate and its pillars
          const m = L/2, ang = Math.atan2(dz, dx);
          for (const s of [-2.45, 2.45]) box(DPL, a[0] + dx*(m + s) - o[0]*0.15, a[1] + dz*(m + s) - o[2]*0.15, 0.6, 0.6, gLow, g - gLow + 3.1, ang, trim);
          // the two gate leaves stand open (swung into the yard), so the kids can walk in to the villa door
          const gc = pick(gateC), uvg = [[0, 0], [GA/2, 0], [GA/2, 1], [0, 1]];
          [[m - 2.15, -1], [m + 2.15, 1]].forEach(([s, sd]) => {
            const P0 = [a[0] + dx*s - o[0]*0.25, a[1] + dz*s - o[2]*0.25], ex = -o[0]*0.85 + dx*sd*0.5, ez = -o[2]*0.85 + dz*sd*0.5, el = Math.hypot(ex, ez), P1 = [P0[0] + ex/el*2.1, P0[1] + ez/el*2.1];
            const nn = [-(P1[1] - P0[1])/2.1, 0, (P1[0] - P0[0])/2.1];
            quad(ATL, [P0[0], g + 0.05, P0[1]], [P1[0], g + 0.05, P1[1]], [P1[0], g + 2.35, P1[1]], [P0[0], g + 2.35, P0[1]], nn, gc, uvg);
            quad(ATL, [P0[0], g + 0.05, P0[1]], [P1[0], g + 0.05, P1[1]], [P1[0], g + 2.35, P1[1]], [P0[0], g + 2.35, P0[1]], [-nn[0], 0, -nn[2]], gc, uvg);
          });
        }
      }
      flat(YARD, p, g + 0.12, pick(yardC)); { let x0 = 1e9, x1 = -1e9, z0 = 1e9, z1 = -1e9; p.forEach(c => { x0 = Math.min(x0, c[0]); x1 = Math.max(x1, c[0]); z0 = Math.min(z0, c[1]); z1 = Math.max(z1, c[1]); }); YARDS.push({p, y: g + 0.12, x0, x1, z0, z1}); }
      house = inset(p, 3.2); if (Math.abs(area(house)) < 30) house = inset(p, 2);
      const np = rnd() < 0.75 ? (rnd() < 0.4 ? 2 : 1) : 0;   // palms in the yard corners
      for (let k = 0; k < np; k++){ const c0 = p[Math.floor(rnd()*p.length)], t = 0.18 + rnd()*0.08; if (!nearRoad(c0[0] + (cx - c0[0])*t, c0[1] + (cz - c0[1])*t, 1.2) && !inCZ(c0[0] + (cx - c0[0])*t, c0[1] + (cz - c0[1])*t)) palmsYard.push([c0[0] + (cx - c0[0])*t, g, c0[1] + (cz - c0[1])*t, 0.8 + rnd()*0.5]); }
    }
    const top = g + lv*fh;
    for (let i = 0; i < house.length; i++){ const a = house[i], c2 = house[(i + 1) % house.length]; SEG.push([a[0], a[1], c2[0], c2[1]]); }
    walls(WIN, house, gLow, g + 0.45, trim, 4, fh, g);            // base
    walls(WIN, house, g + 0.45, top, wall, 4, fh, g);             // walls with arched windows
    flat(BPL, house, top + 0.02, pick(roofC));
    walls(DPL, house, top, top + 1.0, wall, 4, fh, g, true);      // parapet (both faces)
    walls(DPL, house, top - 0.05, top + 0.25, trim, 4, fh, g);    // band
    flat(DPL, house, top + 1.0, wall);
    if (b.gen){   // villa door on the street side (you can go in)
      const gi = Math.min(b.g || 0, house.length - 1), a = house[gi], c2 = house[(gi + 1) % house.length], ccw = area(house) > 0, o = outN(a, c2, ccw), L = Math.hypot(c2[0] - a[0], c2[1] - a[1]);
      if (L > 4){
        const dx = (c2[0] - a[0])/L, dz = (c2[1] - a[1])/L, m = L/2, P = s => [a[0] + dx*(m + s) + o[0]*0.04, a[1] + dz*(m + s) + o[2]*0.04];
        const d0 = P(-0.9), d1 = P(0.9); quad(ATL, [d0[0], g + 0.45, d0[1]], [d1[0], g + 0.45, d1[1]], [d1[0], g + 3.0, d1[1]], [d0[0], g + 3.0, d0[1]], o, pick(doorC), [[GA, 0], [1, 0], [1, 1], [GA, 1]]);
        const e0 = P(-1.6), e1 = P(1.6), oo = [o[0]*1.3, o[2]*1.3];
        box(DPL, (e0[0] + e1[0])/2 + oo[0]/2, (e0[1] + e1[1])/2 + oo[1]/2, 3.4, 1.3, g + 3.2, 0.3, Math.atan2(dz, dx), trim);
        DOORS.push({x: a[0] + dx*m + o[0]*0.3, z: a[1] + dz*m + o[2]*0.3, ry: Math.atan2(o[0], o[2]), y: g + 0.45});
      }
    }
    if (Math.abs(area(house)) > 60){   // on the roof: stair room, water tank, air conditioners
      let hx = 0, hz = 0; house.forEach(c => { hx += c[0]; hz += c[1]; }); hx /= house.length; hz /= house.length;
      const e = house[0], f = house[1], ang = Math.atan2(f[1] - e[1], f[0] - e[0]);
      if (rnd() < 0.7) box(DPL, hx + (e[0] - hx)*0.45, hz + (e[1] - hz)*0.45, 3.2, 3.6, top, 2.9, ang, wall);
      const tx = hx + (f[0] - hx)*0.4, tz = hz + (f[1] - hz)*0.4; box(DPL, tx, tz, 1.4, 1.4, top + 0.6, 1.3, ang, white); box(DPL, tx, tz, 1.6, 1.6, top, 0.6, ang, grey);
      const nAC = 1 + Math.floor(rnd()*3); for (let q = 0; q < nAC; q++){ const h2 = house[(2 + q) % house.length]; box(DPL, hx + (h2[0] - hx)*0.55, hz + (h2[1] - hz)*0.55, 1.0, 0.8, top, 0.8, ang, grey); }
    }
  }
  // textures drawn in code (free)
  function canvasTex(w, h, draw){ const c = document.createElement('canvas'); c.width = w; c.height = h; draw(c.getContext('2d'), w, h); const t = new T.CanvasTexture(c); t.wrapS = t.wrapT = T.RepeatWrapping; t.encoding = T.sRGBEncoding; t.anisotropy = 4; return t; }
  function noise(x, w, h, a){ const im = x.getImageData(0, 0, w, h); for (let i = 0; i < im.data.length; i += 4){ const n = (rnd() - 0.5)*a; im.data[i] += n; im.data[i + 1] += n; im.data[i + 2] += n; } x.putImageData(im, 0, 0); }
  const winTex = canvasTex(256, 256, (x, w, h) => {   // a 4 m wall tile with an Emirati arched window
    x.fillStyle = '#fff'; x.fillRect(0, 0, w, h); noise(x, w, h, 14);
    const wx = w*0.32, ww = w*0.36, wy = h*0.22, wh = h*0.5;
    x.fillStyle = '#e9e4da'; x.fillRect(wx - 8, wy - 8, ww + 16, wh + 22);
    x.beginPath(); x.moveTo(wx, wy + wh); x.lineTo(wx, wy + ww*0.35); x.quadraticCurveTo(wx + ww/2, wy - ww*0.25, wx + ww, wy + ww*0.35); x.lineTo(wx + ww, wy + wh); x.closePath();
    const gr = x.createLinearGradient(0, wy, 0, wy + wh); gr.addColorStop(0, '#5f7f8f'); gr.addColorStop(1, '#2d4552'); x.fillStyle = gr; x.fill();
    x.strokeStyle = '#f8f6f0'; x.lineWidth = 5; x.stroke();
    x.beginPath(); x.moveTo(wx + ww/2, wy + 4); x.lineTo(wx + ww/2, wy + wh); x.moveTo(wx, wy + wh*0.55); x.lineTo(wx + ww, wy + wh*0.55); x.lineWidth = 3; x.stroke();
    x.fillStyle = 'rgba(0,0,0,.12)'; x.fillRect(wx - 10, wy + wh + 14, ww + 20, 6); x.fillStyle = 'rgba(120,100,70,.18)'; x.fillRect(0, 0, w, 6);
  });
  const plainTex = canvasTex(128, 128, (x, w, h) => { x.fillStyle = '#fff'; x.fillRect(0, 0, w, h); noise(x, w, h, 10); });
  const paveTex = canvasTex(128, 128, (x, w, h) => { x.fillStyle = '#fff'; x.fillRect(0, 0, w, h); noise(x, w, h, 18); x.strokeStyle = 'rgba(0,0,0,.18)'; x.lineWidth = 2; for (let i = 0; i <= w; i += 32){ x.beginPath(); x.moveTo(i, 0); x.lineTo(i, h); x.stroke(); x.beginPath(); x.moveTo(0, i); x.lineTo(w, i); x.stroke(); } });
  const atlasTex = canvasTex(384, 128, (x, w, h) => {
    x.fillStyle = '#fff'; x.fillRect(0, 0, w, h);
    for (let c = 0; c < 2; c++){ const o = c*128; x.fillStyle = 'rgba(0,0,0,.35)'; for (let i = 4; i < 128; i += 9) x.fillRect(o + i, 12, 3, h - 24); x.fillRect(o, 0, 128, 12); x.fillRect(o, h - 12, 128, 12); x.fillStyle = 'rgba(255,215,140,.6)'; x.fillRect(o + 62, 0, 4, h); }
    const o = 256; x.strokeStyle = 'rgba(0,0,0,.35)'; x.lineWidth = 5; x.strokeRect(o + 10, 6, 50, h - 12); x.strokeRect(o + 68, 6, 50, h - 12); x.fillStyle = 'rgba(230,190,90,.9)'; x.fillRect(o + 54, h*0.5, 7, 14); x.fillRect(o + 67, h*0.5, 7, 14);
  });
  atlasTex.wrapS = atlasTex.wrapT = T.ClampToEdgeWrapping;
  const LM = o => new T.MeshLambertMaterial(Object.assign({vertexColors: true}, o));
  const MATS = {win: LM({map: winTex}), plain: LM({map: plainTex}), yard: LM({map: paveTex, polygonOffset: true, polygonOffsetFactor: -2, polygonOffsetUnits: -2}), atlas: LM({map: atlasTex})};
  function makeMesh(bk, mat, cast){
    if (!bk || !bk.p.length) return null; const g = new T.BufferGeometry();
    g.setAttribute('position', new T.Float32BufferAttribute(bk.p, 3)); g.setAttribute('normal', new T.Float32BufferAttribute(bk.n, 3));
    g.setAttribute('color', new T.Float32BufferAttribute(bk.c, 3)); g.setAttribute('uv', new T.Float32BufferAttribute(bk.uv, 2)); g.computeBoundingSphere();
    const m = new T.Mesh(g, mat); m.castShadow = cast !== false; m.receiveShadow = true; m.matrixAutoUpdate = false; return m;
  }
  const chunkRect = (k, s) => { const [a, b] = k.split(',').map(Number); return {x0: a*s, x1: (a + 1)*s, z0: b*s, z1: (b + 1)*s}; };
  const baseChunks = [], detChunks = new Map();
  baseB.forEach((o, k) => { const g = new T.Group(); ['win', 'plain'].forEach(mt => { const m = makeMesh(o[mt], MATS[mt]); if (m) g.add(m); }); root.add(g); baseChunks.push(Object.assign(chunkRect(k, BC), {g, k})); });
  detB.forEach((o, k) => { const g = new T.Group(); ['plain', 'yard', 'atlas'].forEach(mt => { const m = makeMesh(o[mt], MATS[mt], mt !== 'yard'); if (m) g.add(m); }); g.visible = false; root.add(g); detChunks.set(k, Object.assign(chunkRect(k, DC), {g, k, palms: []})); });
  baseB.clear(); detB.clear();

  // ---------- palms: yards and palm farms (instanced; detailed near, light far) ----------
  function inPoly(x, z, p){ let c = false; for (let i = 0, j = p.length - 1; i < p.length; j = i++){ const a = p[i], b = p[j]; if ((a[1] > z) !== (b[1] > z) && x < (b[0] - a[0])*(z - a[1])/(b[1] - a[1]) + a[0]) c = !c; } return c; }
  const palmsFarm = [];
  greens.forEach(p => { const A = Math.abs(area(p)), sp = A > 200000 ? 26 : 13; let x0 = 1e9, x1 = -1e9, z0 = 1e9, z1 = -1e9; p.forEach(c => { x0 = Math.min(x0, c[0]); x1 = Math.max(x1, c[0]); z0 = Math.min(z0, c[1]); z1 = Math.max(z1, c[1]); });
    for (let x = x0 + sp/2; x < x1; x += sp) for (let z = z0 + sp/2; z < z1; z += sp){ if (rnd() < 0.15) continue; const jx = x + (rnd() - 0.5)*4, jz = z + (rnd() - 0.5)*4; if (!inPoly(jx, jz, p)) continue; const h = H(jx, jz); if (h < 1) continue;
      if (cfg.skipPalm && cfg.skipPalm(jx, jz)) continue; if (nearRoad(jx, jz, 1.5) || inCZ(jx, jz)) continue; palmsFarm.push([jx, h, jz, 1.0 + rnd()*0.6]); } });
  function colorGeo(geo, col){ const n = geo.attributes.position.count, a = new Float32Array(n*3); for (let i = 0; i < n; i++){ a[i*3] = col.r; a[i*3 + 1] = col.g; a[i*3 + 2] = col.b; } geo.setAttribute('color', new T.BufferAttribute(a, 3)); return geo; }
  function mergeGeos(list){   // small stand-in for BufferGeometryUtils.mergeBufferGeometries (non-indexed position/normal/color)
    let n = 0; list.forEach(g => n += g.attributes.position.count);
    const pos = new Float32Array(n*3), nor = new Float32Array(n*3), col = new Float32Array(n*3); let o = 0;
    list.forEach(g => { pos.set(g.attributes.position.array, o*3); nor.set(g.attributes.normal.array, o*3); col.set(g.attributes.color.array, o*3); o += g.attributes.position.count; });
    const g = new T.BufferGeometry(); g.setAttribute('position', new T.BufferAttribute(pos, 3)); g.setAttribute('normal', new T.BufferAttribute(nor, 3)); g.setAttribute('color', new T.BufferAttribute(col, 3)); return g;
  }
  function palmGeo(NF, lo){
    const parts = [], trunk = new T.CylinderGeometry(0.22, 0.32, 8, lo ? 4 : 7, lo ? 1 : 4); trunk.translate(0, 4, 0);
    const tp = trunk.attributes.position; for (let i = 0; i < tp.count; i++){ const y = tp.getY(i); tp.setX(i, tp.getX(i) + Math.sin(y*0.25)*0.25); }
    trunk.computeVertexNormals(); parts.push(colorGeo(trunk.toNonIndexed(), C(0x7a5c3e)));
    for (let k = 0; k < NF; k++){
      const f = new T.PlaneGeometry(lo ? 1.5 : 0.9, 4.2, 1, lo ? 2 : 4); f.translate(0, 2.1, 0);
      const fp = f.attributes.position; for (let i = 0; i < fp.count; i++){ const y = fp.getY(i); fp.setZ(i, -y*y*0.09); fp.setX(i, fp.getX(i)*(1 - y/5)); }
      f.rotateX(-PI/2 + 0.55 + (k % 2)*0.25); f.rotateY(k/NF*PI*2); f.translate(0.25, 8, 0); f.computeVertexNormals();
      parts.push(colorGeo(f.toNonIndexed(), C(k % 3 ? 0x5f7d32 : 0x6f8a3a)));
    }
    return mergeGeos(parts);
  }
  // instances further than R from the camera (hi) or nearer than R (lo) fold away in the vertex shader, so the two sets never overlap
  const palmU = {cam: {value: new T.Vector3()}, rad: {value: 520}};
  function palmMat(far){ const m = new T.MeshLambertMaterial({vertexColors: true, side: T.DoubleSide});
    m.onBeforeCompile = sh => { sh.uniforms.pCam = palmU.cam; sh.uniforms.pRad = palmU.rad;
      sh.vertexShader = 'uniform vec3 pCam; uniform float pRad;\n' + sh.vertexShader.replace('#include <begin_vertex>', '#include <begin_vertex>\n#ifdef USE_INSTANCING\n{ vec4 ip = instanceMatrix*vec4(0.0,0.0,0.0,1.0); float dd = distance(ip.xz, pCam.xz); if (' + (far ? 'dd < pRad' : 'dd > pRad') + ') transformed *= 0.0; }\n#endif'); };
    m.customProgramCacheKey = () => far ? 'palmFar' : 'palmNear'; return m; }
  const palmHiGeo = palmGeo(9), palmLoGeo = palmGeo(6, true), palmHiMat = palmMat(false), palmLoMat = palmMat(true);
  const loPalmChunks = new Map();
  const _M = new T.Matrix4(), _Q = new T.Quaternion(), _E = new T.Euler(), _V = new T.Vector3(), _S = new T.Vector3();
  const allPalms = palmsYard.concat(palmsFarm), hiLists = new Map();
  allPalms.forEach(pp => { const kd = key(pp[0], pp[2], DC), kb = key(pp[0], pp[2], BC); (hiLists.get(kd) || hiLists.set(kd, []).get(kd)).push(pp); (loPalmChunks.get(kb) || loPalmChunks.set(kb, []).get(kb)).push(pp); });
  function instPalms(list, geo, mat, keep){ const im = new T.InstancedMesh(geo, mat, list.length);
    list.forEach((pp, i) => { const [x, y, z, s] = pp; _E.set((rnd() - 0.5)*0.12, rnd()*6.28, (rnd() - 0.5)*0.12); _Q.setFromEuler(_E); _M.compose(_V.set(x, y, z), _Q, _S.set(s, s, s)); im.setMatrixAt(i, _M);
      if (keep){ pp.im = im; pp.ix = i; pp.q = _Q.clone(); } });
    im.frustumCulled = false; return im; }
  // shake one palm (the near, detailed copy): a small tilt on top of its own turn
  const _Q2 = new T.Quaternion();
  function palmTilt(pp, rx, rz){ if (!pp.im) return; _E.set(rx, 0, rz); _Q2.setFromEuler(_E).multiply(pp.q); _M.compose(_V.set(pp[0], pp[1], pp[2]), _Q2, _S.set(pp[3], pp[3], pp[3])); pp.im.setMatrixAt(pp.ix, _M); pp.im.instanceMatrix.needsUpdate = true; }
  hiLists.forEach((list, k) => { let ch = detChunks.get(k); if (!ch){ const g = new T.Group(); g.visible = false; root.add(g); ch = Object.assign(chunkRect(k, DC), {g, k, palms: []}); detChunks.set(k, ch); }
    const im = instPalms(list, palmHiGeo, palmHiMat, true); im.castShadow = false; im.receiveShadow = true; ch.g.add(im); ch.pim = im; });
  const loPalms = []; loPalmChunks.forEach((list, k) => { const im = instPalms(list, palmLoGeo, palmLoMat); const r = chunkRect(k, BC); root.add(im); loPalms.push(Object.assign(r, {im})); });
  const detList = Array.from(detChunks.values());

  // ---------- streets: continuous asphalt ribbons (mitred bends, filled junctions, round ends), kerbs and sidewalks in town,
  //            white edge lines and dashed centre lines that follow the curve, a median with lamp posts on divided roads ----------
  const roadB = new Map(), roadSegs = new Map();   // roadSegs: per 200 m cell, for the minimap
  const asphaltTex = canvasTex(256, 256, (x, w, h) => { x.fillStyle = '#6f6b66'; x.fillRect(0, 0, w, h); noise(x, w, h, 26);
    for (let i = 0; i < 900; i++){ x.fillStyle = rnd() < 0.5 ? 'rgba(255,250,240,.10)' : 'rgba(20,18,16,.12)'; x.fillRect(rnd()*w, rnd()*h, 1 + rnd()*2, 1 + rnd()*2); }
    for (let i = 0; i < 5; i++){ x.strokeStyle = 'rgba(30,28,26,.10)'; x.lineWidth = 2 + rnd()*5; x.beginPath(); const y0 = rnd()*h; x.moveTo(0, y0); x.bezierCurveTo(w*0.3, y0 + rnd()*30 - 15, w*0.6, y0 + rnd()*30 - 15, w, y0 + rnd()*20 - 10); x.stroke(); } });
  const walkTex = canvasTex(256, 256, (x, w, h) => { x.fillStyle = '#9a968f'; x.fillRect(0, 0, w, h); const pw = 25.6, ph = 12.8; for (let j = 0; j < 20; j++) for (let i = -1; i < 11; i++){ const t = rnd(); x.fillStyle = t < 0.5 ? '#cfcbc4' : t < 0.8 ? '#bdb8b0' : '#dedad3'; x.fillRect(i*pw + (j % 2)*pw/2 + 1, j*ph + 1, pw - 2, ph - 2); } noise(x, w, h, 14); });   // grey interlock pavers, 2 m repeat
  const kerbTex = canvasTex(128, 32, (x, w, h) => { x.fillStyle = '#e5b52b'; x.fillRect(0, 0, w, h); x.fillStyle = '#262626'; x.fillRect(w/2, 0, w/2, h); noise(x, w, h, 10); });   // black-and-yellow kerb stones
  const medTex = canvasTex(256, 256, (x, w, h) => { x.fillStyle = '#9a968f'; x.fillRect(0, 0, w, h); const pw = 25.6, ph = 12.8; for (let j = 0; j < 20; j++) for (let i = -1; i < 11; i++){ const t = rnd(); x.fillStyle = t < 0.5 ? '#cfcbc4' : t < 0.8 ? '#bdb8b0' : '#dedad3'; x.fillRect(i*pw + (j % 2)*pw/2 + 1, j*ph + 1, pw - 2, ph - 2); } noise(x, w, h, 14); });
  const RM = (map, o) => new T.MeshLambertMaterial(Object.assign({map}, o || {}));
  const promTex = canvasTex(128, 128, (x, w, h) => { x.fillStyle = '#e2cfa6'; x.fillRect(0, 0, w, h); noise(x, w, h, 12); x.strokeStyle = 'rgba(150,110,70,.35)'; x.lineWidth = 3; for (let i = 0; i <= w; i += 64){ x.beginPath(); x.moveTo(i, 0); x.lineTo(i, h); x.stroke(); x.beginPath(); x.moveTo(0, i); x.lineTo(w, i); x.stroke(); } x.strokeStyle = 'rgba(120,90,60,.15)'; x.lineWidth = 1; for (let i = 0; i <= w; i += 16){ x.beginPath(); x.moveTo(i, 0); x.lineTo(i, h); x.stroke(); x.beginPath(); x.moveTo(0, i); x.lineTo(w, i); x.stroke(); } });
  const lawnTexR = canvasTex(256, 256, (x, w, h) => { x.fillStyle = '#58893a'; x.fillRect(0, 0, w, h); for (let i = 0; i < 9000; i++){ x.fillStyle = rnd() < 0.5 ? 'rgba(150,175,90,.35)' : 'rgba(40,70,25,.32)'; x.fillRect(rnd()*w, rnd()*h, 1, 2 + rnd()*2); } });
  const RMAT = {lawn: RM(lawnTexR), prom: RM(promTex), conc: new T.MeshLambertMaterial({color: 0xd9d3c7}), wood: new T.MeshLambertMaterial({color: 0x8a5f3a}), asph: RM(asphaltTex, {polygonOffset: true, polygonOffsetFactor: -1, polygonOffsetUnits: -2}), walk: RM(walkTex), kerb: RM(kerbTex, {side: T.DoubleSide}), med: RM(medTex),
    white: new T.MeshLambertMaterial({color: 0xf4f2ea, polygonOffset: true, polygonOffsetFactor: -4, polygonOffsetUnits: -6}), yellow: new T.MeshLambertMaterial({color: 0xe8b830, polygonOffset: true, polygonOffsetFactor: -4, polygonOffsetUnits: -6})};
  const rbk = (x, z, m) => { const k = key(x, z, BC); let o = roadB.get(k); if (!o){ o = {}; roadB.set(k, o); } return o[m] || (o[m] = {p: [], n: [], uv: [], i: []}); };
  // one quad strip piece between two cross-sections (each: [x, y, z] left/right) with a given normal
  function rquad(bk, A, B, C, Dd, n, uvs){ const v = bk.p.length/3; [A, B, C, Dd].forEach((q, k) => { bk.p.push(q[0], q[1], q[2]); bk.n.push(n[0], n[1], n[2]); bk.uv.push(uvs[k][0], uvs[k][1]); }); bk.i.push(v, v + 1, v + 2, v, v + 2, v + 3); }
  const UP = [0, 1, 0];
  const lampPts = [], lampSeen = new Set(), BRIDGES = [], benchPts = [], planterPts = [];
  const smooth01r = t => { t = clamp(t, 0, 1); return t*t*(3 - 2*t); };
  RD.forEach((r, ri) => {
    const p = r.p, n = p.length, closed = r.closed, lift = liftOf(r);
    // mitred offset direction at every node (unit normal × mitre length)
    const nrm = i => { const a = p[i], b = p[(i + 1) % n], l = Math.hypot(b[0] - a[0], b[1] - a[1]) || 1; return [-(b[1] - a[1])/l, (b[0] - a[0])/l]; };
    const off = []; for (let i = 0; i < n; i++){
      let n0, n1; if (closed){ n0 = nrm((i - 1 + n) % n); n1 = nrm(i); } else { n0 = nrm(Math.max(0, i - 1)); n1 = nrm(Math.min(n - 2, i)); }
      let mx = n0[0] + n1[0], mz = n0[1] + n1[1]; const ml = Math.hypot(mx, mz) || 1; mx /= ml; mz /= ml; const k = 1/Math.max(0.45, mx*n1[0] + mz*n1[1]); off.push([mx*k, mz*k, k > 2.1]); }
    // samples along the street every ≤ 7 m (s = distance along)
    const S = []; let s = 0; const segs = closed ? n : n - 1;
    for (let i = 0; i < segs; i++){ const a = p[i], b = p[(i + 1) % n], o0 = off[i], o1 = off[(i + 1) % n], L = Math.hypot(b[0] - a[0], b[1] - a[1]), m = Math.max(1, Math.ceil(L/7));
      const mk = key((a[0] + b[0])/2, (a[1] + b[1])/2, DC); (roadSegs.get(mk) || roadSegs.set(mk, []).get(mk)).push([a[0], a[1], b[0], b[1], r.W + (r.dual ? 0 : 2*r.sw*0.6)]);
      for (let t = (i ? 1 : 0); t <= m; t++){ const f = t/m; S.push({x: a[0] + (b[0] - a[0])*f, z: a[1] + (b[1] - a[1])*f, ox: o0[0] + (o1[0] - o0[0])*f, oz: o0[1] + (o1[1] - o0[1])*f, s: s + L*f, i, mh: r.dual ? r.dual.mh[i] + (r.dual.mh[Math.min(n - 1, i + 1)] - r.dual.mh[i])*f : 0}); }
      s += L; }
    if (S.length < 2) return;
    S.forEach(q => { q.j = !!nearJ(q.x, q.z, 0); q.deck = null; });
    // bridges: where the street runs over water (the canal, the harbour), a deck above the water with ramps at both ends
    { const wet = q => Hc(q.x, q.z) < 0.25 && shoreDist(q.x, q.z) < 4; let k = 0;
      while (k < S.length){ if (!wet(S[k])){ k++; continue; } let e = k; while (e + 1 < S.length && wet(S[e + 1])) e++;
        const s0 = S[k].s, s1 = S[e].s; if (s1 - s0 < 140){ const gA = H(S[Math.max(0, k - 1)].x, S[Math.max(0, k - 1)].z), gB = H(S[Math.min(S.length - 1, e + 1)].x, S[Math.min(S.length - 1, e + 1)].z);
          const deck = Math.max(gA, gB, WATER_Y + 2.4) + 0.25, RL = 16, A = s0 - 4, B = s1 + 4;
          S.forEach(q => { const dd = q.s < A ? A - q.s : q.s > B ? q.s - B : 0; if (dd < RL){ const y = deck - (deck - Math.min(deck, H(q.x, q.z)))*smooth01r(dd/RL); q.deck = q.deck === null ? y : Math.max(q.deck, y); } });
          BRIDGES.push({r, S, A, B, deck, hw: r.W/2 + Math.max(r.sw, 1.6)}); }
        k = e + 1; } }
    // more samples on a bridge so the deck and the ramps stay smooth
    const at = (q, o, dy) => { const x = q.x + q.ox*o, z = q.z + q.oz*o, g = H(x, z); return [x, (q.deck !== null ? Math.max(g, q.deck) : g) + dy, z]; };
    const hw = r.W/2, sd = r.dual ? r.dual.side : 0;   // sd: which side the median is on (+1 = the +offset side)
    for (let k = 0; k < S.length - 1; k++){
      const q0 = S[k], q1 = S[k + 1], bxz = rbk(q0.x, q0.z, 'asph'), cut = q0.j || q1.j;
      // asphalt (3 points across so it follows the ground)
      for (const [o0, o1] of [[-hw, 0], [0, hw]]) rquad(bxz, at(q0, o0, lift), at(q0, o1, lift), at(q1, o1, lift), at(q0 === q1 ? q0 : q1, o0, lift), UP, [[o0/5, q0.s/5], [o1/5, q0.s/5], [o1/5, q1.s/5], [o0/5, q1.s/5]]);
      if (cut) continue;
      // kerbs + sidewalks (outer side only on a divided road; the inner side gets the median)
      for (const sg of [1, -1]){
        if (r.dual && sg === sd){ const m0 = q0.mh, m1 = q1.mh; if (m0 < 0.3 || m1 < 0.3 || nearRBS(q0.x, q0.z)) continue; const bm = rbk(q0.x, q0.z, 'med'), bk2 = rbk(q0.x, q0.z, 'kerb'), e = 0.2;
          rquad(bk2, at(q0, sg*hw, lift - 0.05), at(q1, sg*hw, lift - 0.05), at(q1, sg*hw, lift + e), at(q0, sg*hw, lift + e), [-sg*q0.ox, 0, -sg*q0.oz], [[q0.s/2, 0], [q1.s/2, 0], [q1.s/2, 1], [q0.s/2, 1]]);
          { const bw = Math.min(0.9, m0/3, m1/3), bl = rbk(q0.x, q0.z, 'lawn'), strip = (mat, a0, b0, a1, b1) => { if (sg > 0) rquad(mat, at(q0, hw + a0, lift + e), at(q0, hw + b0, lift + e), at(q1, hw + b1, lift + e), at(q1, hw + a1, lift + e), UP, [[0, q0.s/4], [(b0 - a0)/4, q0.s/4], [(b1 - a1)/4, q1.s/4], [0, q1.s/4]]); else rquad(mat, at(q0, -hw - b0, lift + e), at(q0, -hw - a0, lift + e), at(q1, -hw - a1, lift + e), at(q1, -hw - b1, lift + e), UP, [[0, q0.s/4], [(b0 - a0)/4, q0.s/4], [(b1 - a1)/4, q1.s/4], [0, q1.s/4]]); };
            if (m0 < 2.4 || m1 < 2.4) strip(bm, 0, m0, 0, m1); else { strip(bm, 0, bw, 0, bw); strip(bl, bw, m0 - bw, bw, m1 - bw); strip(bm, m0 - bw, m0, m1 - bw, m1); } }
          continue; }
        const swW = r.sw || (!r.nosw && q0.deck !== null && q1.deck !== null && Math.max(q0.deck - H(q0.x, q0.z), q1.deck - H(q1.x, q1.z)) > 0.3 ? 1.6 : 0);
        if (r.prom === sg && !(q0.deck !== null) && !nearRBS(q0.x, q0.z)){ const bp = rbk(q0.x, q0.z, 'prom'), bk3 = rbk(q0.x, q0.z, 'kerb'), e = 0.16, a0 = hw + swW, a1 = hw + swW + PROM_W, oa = Math.min(sg*a0, sg*a1), ob = Math.max(sg*a0, sg*a1);
          rquad(bp, at(q0, oa, lift + e), at(q0, ob, lift + e), at(q1, ob, lift + e), at(q1, oa, lift + e), UP, [[oa/4, q0.s/4], [ob/4, q0.s/4], [ob/4, q1.s/4], [oa/4, q1.s/4]]);
          rquad(bk3, at(q0, sg*a1, lift + e), at(q1, sg*a1, lift + e), at(q1, sg*a1, lift - 0.35), at(q0, sg*a1, lift - 0.35), [sg*q0.ox, 0, sg*q0.oz], [[q0.s/2, 0], [q1.s/2, 0], [q1.s/2, 1], [q0.s/2, 1]]);
          if (!swW) rquad(bk3, at(q0, sg*hw, lift - 0.05), at(q1, sg*hw, lift - 0.05), at(q1, sg*hw, lift + e), at(q0, sg*hw, lift + e), [-sg*q0.ox, 0, -sg*q0.oz], [[q0.s/2, 0], [q1.s/2, 0], [q1.s/2, 1], [q0.s/2, 1]]);
          // planters with palms every 16 m, benches between them, lamp posts every 32 m (on the sea edge)
          const p0 = Math.floor(q0.s/16), p1 = Math.floor(q1.s/16); if (p1 > p0){ const f = (p1*16 - q0.s)/((q1.s - q0.s) || 1), q = {x: q0.x + (q1.x - q0.x)*f, z: q0.z + (q1.z - q0.z)*f, ox: q0.ox, oz: q0.oz, deck: null}, oc = sg*(a0 + 1.6), P = at(q, oc, 0);
            if (p1 % 2){ planterPts.push([P[0], P[1] + lift + e, P[2]]); promPalms.push([P[0], P[1] + lift + e + 0.5, P[2], 0.9 + (p1 % 3)*0.1]); }
            else { const Pb = at(q, sg*(a1 - 1.2), 0); benchPts.push([Pb[0], Pb[1] + lift + e, Pb[2], Math.atan2(q.ox*sg, q.oz*sg)]); const Pl = at(q, sg*(a1 - 0.4), 0); lampPts.push([Pl[0], Pl[1] + lift + e, Pl[2], Math.atan2(q.ox, q.oz), 1]); } }
        }
        if (!swW || nearRBS(q0.x, q0.z)) continue; const bw = rbk(q0.x, q0.z, 'walk'), bk2 = rbk(q0.x, q0.z, 'kerb'), e = 0.16, o0 = sg*hw, o1 = sg*(hw + swW);
        rquad(bk2, at(q0, o0, lift - 0.05), at(q1, o0, lift - 0.05), at(q1, o0, lift + e), at(q0, o0, lift + e), [-sg*q0.ox, 0, -sg*q0.oz], [[q0.s/2, 0], [q1.s/2, 0], [q1.s/2, 1], [q0.s/2, 1]]);
        { const oa = Math.min(o0, o1), ob = Math.max(o0, o1); rquad(bw, at(q0, oa, lift + e), at(q0, ob, lift + e), at(q1, ob, lift + e), at(q1, oa, lift + e), UP, [[oa/2, q0.s/2], [ob/2, q0.s/2], [ob/2, q1.s/2], [oa/2, q1.s/2]]); }
        rquad(bk2, at(q0, o1, lift + e), at(q1, o1, lift + e), at(q1, o1, lift - 0.3), at(q0, o1, lift - 0.3), [sg*q0.ox, 0, sg*q0.oz], [[q0.s/2, 0], [q1.s/2, 0], [q1.s/2, 1], [q0.s/2, 1]]);
        if (q0.deck !== null && q1.deck !== null && !(r.dual && sg === sd)){   // bridge: parapet wall on the outer edge and the deck's side face
          const bc = rbk(q0.x, q0.z, 'conc'), oo = sg*(hw + swW), o2 = sg*(hw + swW + 0.3), nO = [sg*q0.ox, 0, sg*q0.oz], uvs = [[0, 0], [1, 0], [1, 1], [0, 1]];
          rquad(bc, at(q0, oo, lift + e), at(q1, oo, lift + e), at(q1, oo, lift + e + 1.0), at(q0, oo, lift + e + 1.0), [-nO[0], 0, -nO[2]], uvs);
          rquad(bc, at(q0, oo, lift + e + 1.0), at(q1, oo, lift + e + 1.0), at(q1, o2, lift + e + 1.0), at(q0, o2, lift + e + 1.0), UP, uvs);
          rquad(bc, at(q0, o2, lift - 0.9), at(q1, o2, lift - 0.9), at(q1, o2, lift + e + 1.0), at(q0, o2, lift + e + 1.0), nO, uvs);
          rquad(bc, at(q0, -o2, lift - 0.9), at(q1, -o2, lift - 0.9), at(q1, o2, lift - 0.9), at(q0, o2, lift - 0.9), [0, -1, 0], uvs); }
      }
    }
    // painted lines: continuous or dashed, following the curve (pieces cut at the junctions)
    function paint(mat, o, wd, dash){
      for (let k = 0; k < S.length - 1; k++){ const q0 = S[k], q1 = S[k + 1]; if (q0.j || q1.j || (RBS && Math.hypot(q0.x - RBS[0], q0.z - RBS[1]) < RBS[2] - 16)) continue;
        const pieces = []; if (!dash) pieces.push([0, 1]); else { const L = q1.s - q0.s || 1; for (let d0 = Math.floor(q0.s/9)*9; d0 < q1.s; d0 += 9){ const a = Math.max(q0.s, d0), b = Math.min(q1.s, d0 + 3); if (b > a) pieces.push([(a - q0.s)/L, (b - q0.s)/L]); } }
        const bk = rbk(q0.x, q0.z, mat), P = f => ({x: q0.x + (q1.x - q0.x)*f, z: q0.z + (q1.z - q0.z)*f, ox: q0.ox + (q1.ox - q0.ox)*f, oz: q0.oz + (q1.oz - q0.oz)*f, deck: q0.deck === null || q1.deck === null ? null : q0.deck + (q1.deck - q0.deck)*f});
        for (const [fa, fb] of pieces){ const A = P(fa), B = P(fb); rquad(bk, at(A, o - wd/2, lift + 0.02), at(A, o + wd/2, lift + 0.02), at(B, o + wd/2, lift + 0.02), at(B, o - wd/2, lift + 0.02), UP, [[0, 0], [1, 0], [1, 1], [0, 1]]); } } }
    if (r.dual){ paint('white', -sd*(hw - 0.35), 0.15, false); paint('yellow', sd*(hw - 0.35), 0.15, false); paint('white', 0, 0.12, true); }
    else if (r.rank >= 2 && !r.link){ paint('white', 0, 0.13, true); if (r.rank >= 3){ paint('white', hw - 0.35, 0.15, false); paint('white', -hw + 0.35, 0.15, false); } }
    // round ends where a street just stops; filled wedges at sharp bends
    const disc = (x, z, rad, y) => { const bk = rbk(x, z, 'asph'), v0 = bk.p.length/3; bk.p.push(x, y, z); bk.n.push(0, 1, 0); bk.uv.push(x/5, z/5);
      for (let a = 0; a <= 16; a++){ const ang = a/16*2*PI, px = x + Math.cos(ang)*rad, pz = z + Math.sin(ang)*rad; bk.p.push(px, Math.max(y, H(px, pz) + lift), pz); bk.n.push(0, 1, 0); bk.uv.push(px/5, pz/5); if (a) bk.i.push(v0, v0 + a + 1, v0 + a); } };
    if (!closed){ [0, n - 1].forEach(i => { const J = JS.get(jkey(p[i])); if (J && J.end) disc(p[i][0], p[i][1], hw, H(p[i][0], p[i][1]) + lift); }); }
    off.forEach((o, i) => { if (o[2]) disc(p[i][0], p[i][1], hw, H(p[i][0], p[i][1]) + lift); });
    // lamp posts every 40 m on the bigger streets: in the median of a divided road, else on the sidewalk edge
    if (r.dual || (r.rank >= 3 && r.sw)){ for (let d = 20; d < s; d += 40){ let k = 0; while (k < S.length - 2 && S[k + 1].s < d) k++; const q = S[k]; if (q.j) continue;
      const o = r.dual ? (q.mh > 0.5 ? sd*(hw + q.mh) : -sd*(hw + 0.6)) : (hw + r.sw - 0.4)*((Math.floor(d/40) % 2) ? 1 : -1);
      const x = q.x + q.ox*o, z = q.z + q.oz*o, kk = Math.round(x/6) + ',' + Math.round(z/6); if (lampSeen.has(kk) || inCZ(x, z) || (CSTRIP && inPoly(x, z, CSTRIP))) continue; lampSeen.add(kk);
      lampPts.push([x, H(x, z) + lift + 0.18, z, Math.atan2(q.ox*Math.sign(o || 1), q.oz*Math.sign(o || 1)), r.dual && q.mh > 0.5 ? 2 : 1]); } }
  });
  // junction fills: a disc of asphalt where streets meet, so there are no gaps or overlaps in the corners
  JL.forEach(J => { let hw = 0, lift = 0; J.rs.forEach(ri => { const r = RD[ri]; hw = Math.max(hw, r.W/2 + (r.dual ? 0.5 : 0)); lift = Math.max(lift, liftOf(r)); });
    const bk = rbk(J.x, J.z, 'asph'), y = H(J.x, J.z) + lift + 0.004, v0 = bk.p.length/3; bk.p.push(J.x, y, J.z); bk.n.push(0, 1, 0); bk.uv.push(J.x/5, J.z/5);
    for (let a = 0; a <= 20; a++){ const ang = a/20*2*PI, px = J.x + Math.cos(ang)*hw*1.15, pz = J.z + Math.sin(ang)*hw*1.15; bk.p.push(px, Math.max(y - 0.05, H(px, pz) + lift + 0.004), pz); bk.n.push(0, 1, 0); bk.uv.push(px/5, pz/5); if (a) bk.i.push(v0, v0 + a + 1, v0 + a); } });
  // bridges: piers into the water, walls you can't drive through, and the deck height for the kids and the car
  const BRG = 24, bgrid = new Map();
  function boxAt(mat, cx, cy0, cz, ux, uz, w, d, h){   // w along (ux, uz), d across, from cy0 up h
    const vx = -uz, vz = ux, P = (a, b, y) => [cx + ux*a + vx*b, y, cz + uz*a + vz*b], bk = rbk(cx, cz, mat), uv = [[0, 0], [1, 0], [1, 1], [0, 1]], y1 = cy0 + h;
    rquad(bk, P(-w/2, -d/2, cy0), P(w/2, -d/2, cy0), P(w/2, -d/2, y1), P(-w/2, -d/2, y1), [-vx, 0, -vz], uv); rquad(bk, P(w/2, d/2, cy0), P(-w/2, d/2, cy0), P(-w/2, d/2, y1), P(w/2, d/2, y1), [vx, 0, vz], uv);
    rquad(bk, P(-w/2, d/2, cy0), P(-w/2, -d/2, cy0), P(-w/2, -d/2, y1), P(-w/2, d/2, y1), [-ux, 0, -uz], uv); rquad(bk, P(w/2, -d/2, cy0), P(w/2, d/2, cy0), P(w/2, d/2, y1), P(w/2, -d/2, y1), [ux, 0, uz], uv);
    rquad(bk, P(-w/2, -d/2, y1), P(w/2, -d/2, y1), P(w/2, d/2, y1), P(-w/2, d/2, y1), UP, uv); }
  BRIDGES.forEach(B => { const S = B.S, r = B.r, lift = liftOf(r), sd = r.dual ? r.dual.side : 0, ew = B.hw + 0.15;
    for (let k = 0; k < S.length - 1; k++){ const q0 = S[k], q1 = S[k + 1]; if (q0.deck === null || q1.deck === null) continue;
      for (const sg of [1, -1]){ if (r.dual && sg === sd) continue; SEG.push([q0.x + q0.ox*sg*ew, q0.z + q0.oz*sg*ew, q1.x + q1.ox*sg*ew, q1.z + q1.oz*sg*ew]); }
      const key2 = Math.floor(q0.x/BRG) + ',' + Math.floor(q0.z/BRG); (bgrid.get(key2) || bgrid.set(key2, []).get(key2)).push([q0, q1, B]);
      [[Math.floor(q1.x/BRG), Math.floor(q1.z/BRG)], [Math.floor(q0.x/BRG) + 1, Math.floor(q0.z/BRG)], [Math.floor(q0.x/BRG) - 1, Math.floor(q0.z/BRG)], [Math.floor(q0.x/BRG), Math.floor(q0.z/BRG) + 1], [Math.floor(q0.x/BRG), Math.floor(q0.z/BRG) - 1]].forEach(([a, b]) => { const k3 = a + ',' + b; const L = bgrid.get(k3) || bgrid.set(k3, []).get(k3); if (L[L.length - 1] === undefined || L[L.length - 1][0] !== q0) L.push([q0, q1, B]); }); }
    // piers every 11 m where the water is below
    let next = B.A + 5; S.forEach(q => { if (q.s < next || q.s > B.B || q.deck === null) return; next = q.s + 11; const g = H(q.x, q.z); if (g > WATER_Y) return;
      const L = Math.hypot(q.oz, q.ox) || 1; boxAt('conc', q.x, g - 0.5, q.z, q.oz/L, -q.ox/L, 1.2, B.hw*1.6, q.deck - 0.9 - (g - 0.5)); }); });
  function bridgeTop(x, z){ const L = bgrid.get(Math.floor(x/BRG) + ',' + Math.floor(z/BRG)); if (!L) return -1e9; let best = -1e9;
    for (const [q0, q1, B] of L){ const vx = q1.x - q0.x, vz = q1.z - q0.z, l2 = vx*vx + vz*vz || 1, t = clamp(((x - q0.x)*vx + (z - q0.z)*vz)/l2, 0, 1), d = Math.hypot(x - q0.x - vx*t, z - q0.z - vz*t); if (d > B.hw + 0.1) continue;
      const y = Math.max(H(x, z), q0.deck + (q1.deck - q0.deck)*t) + liftOf(B.r) + (d > B.r.W/2 ? 0.16 : 0); best = Math.max(best, y); }
    return best; }
  // the corniche furniture: planters (palms in them), benches
  planterPts.forEach(P => { boxAt('conc', P[0], P[1], P[2], 1, 0, 1.7, 1.7, 0.5); const s2 = 0.95; SEG.push([P[0] - s2, P[2] - s2, P[0] + s2, P[2] - s2], [P[0] + s2, P[2] - s2, P[0] + s2, P[2] + s2], [P[0] + s2, P[2] + s2, P[0] - s2, P[2] + s2], [P[0] - s2, P[2] + s2, P[0] - s2, P[2] - s2]); });
  benchPts.forEach(P => { const ux = Math.cos(P[3]), uz = -Math.sin(P[3]), vx = Math.sin(P[3]), vz = Math.cos(P[3]);
    boxAt('wood', P[0], P[1] + 0.42, P[2], ux, uz, 1.8, 0.45, 0.07); boxAt('wood', P[0] - vx*0.22, P[1] + 0.49, P[2] - vz*0.22, ux, uz, 1.8, 0.06, 0.42);
    [-0.75, 0.75].forEach(a => boxAt('conc', P[0] + ux*a, P[1], P[2] + uz*a, ux, uz, 0.12, 0.45, 0.42)); });
  const promPalmMat = new T.MeshLambertMaterial({vertexColors: true, side: T.DoubleSide}), promB = new Map();
  promPalms.forEach(pp => { const k = key(pp[0], pp[2], BC); (promB.get(k) || promB.set(k, []).get(k)).push(pp); });
  // lamp posts: one merged model, instanced per 800 m chunk; you bump into them
  const lampGeo = (function(){ const parts = [], grey = C(0xb9bec3), dark = C(0x6d7378), lampC = C(0xfff4d6);
    const pole = new T.CylinderGeometry(0.09, 0.14, 9, 7); pole.translate(0, 4.5, 0); parts.push(colorGeo(pole.toNonIndexed(), grey));
    [1, -1].forEach(sg => { const arm = new T.BoxGeometry(0.08, 0.08, 1.8); arm.translate(0, 8.8, sg*0.9); parts.push(colorGeo(arm.toNonIndexed(), grey));
      const hd = new T.BoxGeometry(0.34, 0.14, 0.7); hd.translate(0, 8.75, sg*1.75); parts.push(colorGeo(hd.toNonIndexed(), dark));
      const gl = new T.BoxGeometry(0.26, 0.04, 0.55); gl.translate(0, 8.66, sg*1.75); parts.push(colorGeo(gl.toNonIndexed(), lampC)); });
    const base = new T.CylinderGeometry(0.22, 0.26, 0.5, 8); base.translate(0, 0.25, 0); parts.push(colorGeo(base.toNonIndexed(), dark));
    return mergeGeos(parts); })();
  const lampMat = new T.MeshLambertMaterial({vertexColors: true}), lampB = new Map();
  lampPts.forEach(L => { const k = key(L[0], L[2], BC); (lampB.get(k) || lampB.set(k, []).get(k)).push(L);
    const s = 0.2; SEG.push([L[0] - s, L[2] - s, L[0] + s, L[2] - s], [L[0] + s, L[2] - s, L[0] + s, L[2] + s], [L[0] + s, L[2] + s, L[0] - s, L[2] + s], [L[0] - s, L[2] + s, L[0] - s, L[2] - s]); });
  const roadChunks = [];
  roadB.forEach((o, k) => { const g = new T.Group();
    for (const mt in o){ const bk = o[mt]; if (!bk.p.length) continue; const geo = new T.BufferGeometry(); geo.setAttribute('position', new T.Float32BufferAttribute(bk.p, 3)); geo.setAttribute('normal', new T.Float32BufferAttribute(bk.n, 3));
      geo.setAttribute('uv', new T.Float32BufferAttribute(bk.uv, 2)); geo.setIndex(bk.i); geo.computeBoundingSphere(); const m = new T.Mesh(geo, RMAT[mt]); m.receiveShadow = true; m.matrixAutoUpdate = false; g.add(m); }
    { const Lp = promB.get(k); if (Lp){ const im = new T.InstancedMesh(palmHiGeo, promPalmMat, Lp.length); Lp.forEach((q, i) => { _E.set(0, i*2.4, 0); _Q.setFromEuler(_E); _M.compose(_V.set(q[0], q[1], q[2]), _Q, _S.set(q[3], q[3], q[3])); im.setMatrixAt(i, _M); }); im.castShadow = true; g.add(im); } }
    const L = lampB.get(k); if (L){ const im = new T.InstancedMesh(lampGeo, lampMat, L.length); L.forEach((q, i) => { _E.set(0, q[3] + (q[4] === 2 ? 0 : PI/2), 0); _Q.setFromEuler(_E); _M.compose(_V.set(q[0], q[1], q[2]), _Q, _S.set(1, 1, 1)); im.setMatrixAt(i, _M); }); im.castShadow = true; g.add(im); }
    root.add(g); roadChunks.push(Object.assign(chunkRect(k, BC), {g})); });
  roadB.clear();

  // ---------- lakes behind the dams (in the mountains) ----------
  { const wm = new T.MeshLambertMaterial({color: 0x3f86a8});
    waters.forEach(w => { if (w.sea || w.k === 'dam' || w.p.length < 4) return; const shp = new T.Shape(); w.p.forEach((c, k) => k ? shp.lineTo(c[0], -c[1]) : shp.moveTo(c[0], -c[1]));
      const g = new T.ShapeGeometry(shp); g.rotateX(-PI/2); let cx = 0, cz = 0; w.p.forEach(c => { cx += c[0]; cz += c[1]; }); g.translate(0, Math.max(H(cx/w.p.length, cz/w.p.length), 0) + 0.5, 0); root.add(new T.Mesh(g, wm)); }); }

  // ---------- name signs of the real places (road-sign style) ----------
  const bigK = new Set(['city', 'town', 'village', 'suburb', 'neighbourhood', 'hamlet']), labels = [];
  function mkLabel(t, isBig){
    const c = document.createElement('canvas'), fs = isBig ? 72 : 44, ctx = c.getContext('2d'); ctx.font = '800 ' + fs + 'px Tajawal, sans-serif';
    const w = Math.ceil(ctx.measureText(t).width) + fs*1.6; c.width = w; c.height = fs*2;
    ctx.fillStyle = isBig ? '#1f4f9a' : '#1b5e3b'; ctx.fillRect(0, 0, c.width, c.height); ctx.strokeStyle = '#ffffff'; ctx.lineWidth = fs/9; ctx.strokeRect(fs/7, fs/7, c.width - fs*2/7, c.height - fs*2/7);
    ctx.font = '800 ' + fs + 'px Tajawal, sans-serif'; ctx.direction = 'rtl'; ctx.textAlign = 'center'; ctx.textBaseline = 'middle'; ctx.fillStyle = '#ffffff'; ctx.fillText(t, w/2, c.height/2 + fs*0.06);
    const tx = new T.CanvasTexture(c); tx.encoding = T.sRGBEncoding; tx.anisotropy = 4; const s = new T.Sprite(new T.SpriteMaterial({map: tx, fog: false}));
    const k = (isBig ? 6 : 3.2)/c.height; s.scale.set(c.width*k, c.height*k, 1); s.userData.big = isBig; s.userData.base = [c.width*k, c.height*k]; return s;
  }
  const poleM = new T.MeshLambertMaterial({color: 0x9aa3ab}), poleG = new T.CylinderGeometry(0.12, 0.12, 1, 6);
  pois.forEach(p => { let [x, z] = p.c; if (CN) return; { let done = false; for (let rr = 0; rr <= 80 && !done; rr += 3) for (let a = 0; a < 12 && !done; a++){ const px = x + Math.cos(a*PI/6)*rr, pz = z + Math.sin(a*PI/6)*rr; if (!nearRoad(px, pz, 1.2) && !eoAt(px, pz) && shoreDist(px, pz) > 3){ x = px; z = pz; done = true; } if (!rr) break; } } if (x < X0 || x > X1 || z < Z0 || z > Z1) return; if (cfg.skipLabel && cfg.skipLabel(p)) return; const b = bigK.has(p.k), s = mkLabel(p.n, b), g = Math.max(H(x, z), 0.6), ph = b ? 7 : 4.5;
    const pole = new T.Mesh(poleG, poleM); pole.scale.y = ph; pole.position.set(x, g + ph/2, z); root.add(pole); s.position.set(x, g + ph + s.userData.base[1]/2, z); s.renderOrder = 2; root.add(s); labels.push(s); s.userData.pole = pole; s.userData.name = p.n; });

  // ---------- ground the kids walk on: the terrain, or the paved yard of a villa where that is higher ----------
  const YS = 24, YG = new Map();
  YARDS.forEach(y => { for (let a = Math.floor(y.x0/YS); a <= Math.floor(y.x1/YS); a++) for (let b = Math.floor(y.z0/YS); b <= Math.floor(y.z1/YS); b++){ const k = a + ',' + b; (YG.get(k) || YG.set(k, []).get(k)).push(y); } });
  function Hy(x, z){ const h = Math.max(H(x, z) + roadTop(x, z), bridgeTop(x, z), CTOP(x, z)), L = YG.get(Math.floor(x/YS) + ',' + Math.floor(z/YS)); if (L) for (const y of L) if (x >= y.x0 && x <= y.x1 && z >= y.z0 && z <= y.z1 && y.y > h && inPoly(x, z, y.p)) return y.y; return h; }
  // ---------- collision: walls as line segments in a 16 m grid ----------
  const SG = 16, segGrid = new Map();
  SEG.forEach((s, i) => { const x0 = Math.floor(Math.min(s[0], s[2])/SG), x1 = Math.floor(Math.max(s[0], s[2])/SG), z0 = Math.floor(Math.min(s[1], s[3])/SG), z1 = Math.floor(Math.max(s[1], s[3])/SG);
    for (let a = x0; a <= x1; a++) for (let b = z0; b <= z1; b++){ const k = a + ',' + b; (segGrid.get(k) || segGrid.set(k, []).get(k)).push(i); } });
  // push a circle (x, z, r) out of the walls; returns [x, z, nx, nz] (n = direction away from the wall that was hit, or null)
  function pushWalls(x, z, r){
    let hit = null;
    for (let pass = 0; pass < 2; pass++){
      const a0 = Math.floor((x - r)/SG), a1 = Math.floor((x + r)/SG), b0 = Math.floor((z - r)/SG), b1 = Math.floor((z + r)/SG);
      for (let a = a0; a <= a1; a++) for (let b = b0; b <= b1; b++){ const L = segGrid.get(a + ',' + b); if (!L) continue;
        for (const i of L){ const s = SEG[i], vx = s[2] - s[0], vz = s[3] - s[1], l2 = vx*vx + vz*vz || 1, t = clamp(((x - s[0])*vx + (z - s[1])*vz)/l2, 0, 1), px = s[0] + vx*t, pz = s[1] + vz*t, dx = x - px, dz = z - pz, d = Math.hypot(dx, dz);
          if (d < r){ let ux, uz; if (d > 1e-5){ ux = dx/d; uz = dz/d; } else { const L2 = Math.sqrt(l2); ux = -vz/L2; uz = vx/L2; } x = px + ux*r; z = pz + uz*r; hit = [ux, uz]; } } }
    }
    return [x, z, hit];
  }
  // first wall hit on the way from (x0, z0) to (x1, z1): the fraction of the way (1 = nothing in between) — keeps the camera out of the houses
  function rayWalls(x0, z0, x1, z1){
    let best = 1; const seen = new Set(), dx = x1 - x0, dz = z1 - z0, L = Math.hypot(dx, dz), n = Math.max(1, Math.ceil(L/(SG*0.5)));
    for (let s = 0; s <= n; s++){ const x = x0 + dx*s/n, z = z0 + dz*s/n, a = Math.floor(x/SG), b = Math.floor(z/SG);
      for (let u = a - 1; u <= a + 1; u++) for (let v = b - 1; v <= b + 1; v++){ const Lc = segGrid.get(u + ',' + v); if (!Lc) continue;
        for (const i of Lc){ if (seen.has(i)) continue; seen.add(i); const q = SEG[i], ex = q[2] - q[0], ez = q[3] - q[1], den = dx*ez - dz*ex; if (Math.abs(den) < 1e-9) continue;
          const t = ((q[0] - x0)*ez - (q[1] - z0)*ex)/den, w = ((q[0] - x0)*dz - (q[1] - z0)*dx)/den; if (t >= 0 && t < best && w >= 0 && w <= 1) best = t; } } }
    return best;
  }
  function blockedWall(x, z, r){ return pushWalls(x, z, r)[2] !== null; }
  // ---------- what is taken (houses, roads, sea) — for scattering rocks, trees and bushes ----------
  const OC = 6, ONX = Math.ceil(SW/OC), ONZ = Math.ceil(SH/OC), OCC = new Uint8Array(ONX*ONZ);
  const OCCB = new Uint8Array(ONX*ONZ);
  const occSet = (x, z) => { const i = Math.floor((x - X0)/OC), j = Math.floor((z - Z0)/OC); if (i >= 0 && j >= 0 && i < ONX && j < ONZ) OCC[j*ONX + i] = 1; };
  BLD_LIST.forEach(b => { const p = b.p; let x0 = 1e9, x1 = -1e9, z0 = 1e9, z1 = -1e9; p.forEach(c => { x0 = Math.min(x0, c[0]); x1 = Math.max(x1, c[0]); z0 = Math.min(z0, c[1]); z1 = Math.max(z1, c[1]); });
    for (let x = x0 - 3; x <= x1 + 3; x += OC/2) for (let z = z0 - 3; z <= z1 + 3; z += OC/2){ occSet(x, z); const i = Math.floor((x - X0)/OC), j = Math.floor((z - Z0)/OC); if (i >= 0 && j >= 0 && i < ONX && j < ONZ) OCCB[j*ONX + i] = 1; } });
  function inBld(x, z){ const i = Math.floor((x - X0)/OC), j = Math.floor((z - Z0)/OC); return i >= 0 && j >= 0 && i < ONX && j < ONZ && OCCB[j*ONX + i] === 1; }
  roadSegs.forEach(list => list.forEach(s => { const L = Math.hypot(s[2] - s[0], s[3] - s[1]), n = Math.ceil(L/3), w = s[4]/2 + 2;
    for (let t = 0; t <= n; t++){ const x = s[0] + (s[2] - s[0])*t/n, z = s[1] + (s[3] - s[1])*t/n; for (let o = -w; o <= w; o += 3){ const nx = -(s[3] - s[1])/L, nz = (s[2] - s[0])/L; occSet(x + nx*o, z + nz*o); } } }));
  function blocked(x, z, r){ r = r || 0; if (x < X0 + 50 || x > X1 - 50 || z < Z0 + 50 || z > Z1 - 50) return true;
    for (let a = Math.floor((x - r - X0)/OC); a <= Math.floor((x + r - X0)/OC); a++) for (let b = Math.floor((z - r - Z0)/OC); b <= Math.floor((z + r - Z0)/OC); b++) if (OCC[b*ONX + a]) return true;
    return false; }

  // ---------- maps: the whole of Dibba painted once, then any window of it on demand ----------
  const MAPN = 2048, mapS = MAPN/SW, MAPH = Math.round(SH*mapS);
  const fullMap = (function(){
    const cv = document.createElement('canvas'); cv.width = MAPN; cv.height = MAPH; const g = cv.getContext('2d'), img = g.createImageData(MAPN, MAPH);
    const sand = [227, 196, 142], rockC = [150, 128, 110], water = [120, 182, 196], shallow = [160, 208, 206], beachC = [238, 220, 178], greenC = [184, 178, 122], hi = [178, 160, 140];
    for (let py = 0; py < MAPH; py++) for (let px = 0; px < MAPN; px++){
      const x = X0 + (px + 0.5)/mapS, z = Z0 + (py + 0.5)/mapS, h = at(x, z), i = (py*MAPN + px)*4, k = clamp(Math.round((z - Z0)/DZ), 0, R - 1)*R + clamp(Math.round((x - X0)/DX), 0, R - 1);
      let c;
      if (h < 0) c = h < -2 ? water : shallow;
      else { const sl = slopeAt(k), m = clamp(sl*2 - 0.2, 0, 1)*0.85 + clamp((h - 60)/200, 0, 0.6); c = sand.map((v, j) => v + (rockC[j] - v)*clamp(m, 0, 1)); if (h > 300) c = c.map((v, j) => v + (hi[j] - v)*0.5);
        if (farmM[k]) c = greenC; else if (h < 2 && SHORE[k] < 40) c = beachC; }
      img.data[i] = c[0]; img.data[i + 1] = c[1]; img.data[i + 2] = c[2]; img.data[i + 3] = 255;
    }
    g.putImageData(img, 0, 0);
    const X = x => (x - X0)*mapS, Y = z => (z - Z0)*mapS;
    g.lineCap = g.lineJoin = 'round'; g.strokeStyle = '#a89a80';
    RD.forEach(r => { g.lineWidth = Math.max(1, (r.W + r.sw*2)*mapS*1.4); g.beginPath(); r.p.forEach((c, k) => k ? g.lineTo(X(c[0]), Y(c[1])) : g.moveTo(X(c[0]), Y(c[1]))); g.stroke(); });
    g.fillStyle = '#c9b48e'; BLD_LIST.forEach(b => { g.beginPath(); b.p.forEach((c, k) => k ? g.lineTo(X(c[0]), Y(c[1])) : g.moveTo(X(c[0]), Y(c[1]))); g.closePath(); g.fill(); });
    return cv;
  })();
  const bldByCell = new Map(); BLD_LIST.forEach(b => (bldByCell.get(b.kD) || bldByCell.set(b.kD, []).get(b.kD)).push(b));
  // paint the square around (cx, cz) with half-size Rm metres into ctx (N×N px)
  function paintMap(g, cx, cz, Rm, N, extra){
    const s = N/(2*Rm), X = x => (x - cx + Rm)*s, Y = z => (z - cz + Rm)*s;
    g.fillStyle = '#78b6c4'; g.fillRect(0, 0, N, N); g.imageSmoothingEnabled = true;
    { let sx = (cx - Rm - X0)*mapS, sy = (cz - Rm - Z0)*mapS, sw = 2*Rm*mapS, dx0 = 0, dy0 = 0, dw = N, dh = N; const k = N/sw, sh = sw;   // clip the source to the image (Safari draws nothing otherwise)
      let sx1 = sx + sw, sy1 = sy + sh; if (sx < 0){ dx0 = -sx*k; sx = 0; } if (sy < 0){ dy0 = -sy*k; sy = 0; } if (sx1 > MAPN) sx1 = MAPN; if (sy1 > MAPH) sy1 = MAPH;
      if (sx1 > sx && sy1 > sy) g.drawImage(fullMap, sx, sy, sx1 - sx, sy1 - sy, dx0, dy0, (sx1 - sx)*k, (sy1 - sy)*k); }
    if (Rm < 1200){   // crisp streets and houses when zoomed in
      const a0 = Math.floor((cx - Rm)/DC), a1 = Math.floor((cx + Rm)/DC), b0 = Math.floor((cz - Rm)/DC), b1 = Math.floor((cz + Rm)/DC);
      g.lineCap = g.lineJoin = 'round'; g.strokeStyle = '#ad9f86';
      for (let a = a0; a <= a1; a++) for (let b = b0; b <= b1; b++){ const L = roadSegs.get(a + ',' + b); if (L) L.forEach(r => { g.lineWidth = Math.max(1.5, r[4]*s); g.beginPath(); g.moveTo(X(r[0]), Y(r[1])); g.lineTo(X(r[2]), Y(r[3])); g.stroke(); }); }
      for (let a = a0; a <= a1; a++) for (let b = b0; b <= b1; b++){ const L = bldByCell.get(a + ',' + b); if (L) L.forEach(o => { g.fillStyle = o.gen ? '#d8c6a2' : '#c4ab84'; g.beginPath(); o.p.forEach((c, k) => k ? g.lineTo(X(c[0]), Y(c[1])) : g.moveTo(X(c[0]), Y(c[1]))); g.closePath(); g.fill(); }); }
    }
    if (extra) extra(g, X, Y, s);
  }

  // ---------- every frame: what to draw where ----------
  let NEAR = 900, DET = 520, ROADV = 3200, BASEV = 3800, LOPALM = 2600;
  const fullBuilt = [];
  function update(cam){
    const x = cam.x, z = cam.z;
    for (const ch of chunks){ const d = rectDist(ch, x, z), wantHi = d < NEAR;
      if (wantHi && !ch.hi){ ch.hi = new T.Mesh(chunkGeo(ch.ci, ch.cj, 1), terrainMat); ch.hi.receiveShadow = true; root.add(ch.hi); fullBuilt.push(ch); }
      if (ch.hi) ch.hi.visible = wantHi; ch.lo.visible = !wantHi; if (wantHi) ch.used = performance.now(); }
    if (fullBuilt.length > 30){ fullBuilt.sort((a, b) => a.used - b.used); const old = fullBuilt.shift(); if (old.hi && !old.hi.visible){ root.remove(old.hi); old.hi.geometry.dispose(); old.hi = null; } else fullBuilt.push(old); }
    for (const c of baseChunks) c.g.visible = rectDist(c, x, z) < BASEV;
    for (const c of detList){ const d = rectDist(c, x, z); c.g.visible = d < DET; if (c.pim) c.pim.castShadow = d < 40; }   // palm shadows only right around you (cheaper shadow pass)
    for (const c of roadChunks) c.g.visible = rectDist(c, x, z) < ROADV;
    for (const c of loPalms) c.im.visible = rectDist(c, x, z) < LOPALM;
    palmU.cam.value.set(x, 0, z); palmU.rad.value = DET;
    for (const s of labels){ const d = s.position.distanceTo(cam), v = s.userData.big ? d < 6000 : d < 1600; s.visible = v; s.userData.pole.visible = v && d < 900; const f = d < 300 ? 1 : d/300; s.scale.set(s.userData.base[0]*f, s.userData.base[1]*f, 1); }
    const step = NEAR_S/128; seaNear.position.set(Math.round(x/step)*step, WATER_Y, Math.round(z/step)*step); seaFar.position.set(seaNear.position.x, WATER_Y - 0.02, seaNear.position.z);
    seaMat.uniforms.ctr.value.copy(seaNear.position); seaMat.uniforms.nearR.value = NEAR_S/2;
  }
  function setRange(k){ NEAR = 900*k; DET = 520*k; ROADV = 3200*k; BASEV = 3800*k; LOPALM = 2600*k; }

  // ---------- كورنيش دبا الحصن (مطابق للتجوّل الافتراضي): مواقف إنترلوك رمادي، عشب، ممشى أحمر على القناة بسور حديد أسود،
  //            بستان النخيل، المجمّع أبو الأقواس الأندلسية، المسجدين، القرية التراثية، المقاهي، الدوارات، سارية العلم، اللوحات ----------
  if (CN){
    const G = new T.Group(); root.add(G); const CC = s => new T.Color(s);
    const tex = (w, h, f, rx, ry) => { const t = canvasTex(w, h, f); if (rx) t.repeat.set(rx, ry || rx); return t; };
    const Lm = (o) => new T.MeshLambertMaterial(o);
    // ground textures (world-space UVs: 1 unit = 1 m)
    // interlock pavers (10 x 20 cm, herringbone-free running bond, each paver its own tone), 4 m per texture repeat
    const pavers = (base, dark, light, joint, w) => tex(512, 512, (x, cw, ch) => { x.fillStyle = joint; x.fillRect(0, 0, cw, ch); const pw = 25.6, ph = 12.8;
      for (let j = 0; j < 40; j++) for (let i = -1; i < 21; i++){ const t = rnd(); x.fillStyle = t < 0.5 ? base : t < 0.8 ? dark : light; const ox = (j % 2)*pw/2; x.fillRect(i*pw + ox + 1, j*ph + 1, pw - 2, ph - 2); } noise(x, cw, ch, 14); });
    const greyPave = pavers('#cfcbc4', '#bdb8b0', '#dedad3', '#9a968f');
    const redPave = pavers('#7c3029', '#672721', '#8e3a32', '#4a1e1a');
    const pinkPave = tex(256, 256, (x, w, h) => { x.fillStyle = '#d9a294'; x.fillRect(0, 0, w, h); noise(x, w, h, 14); x.strokeStyle = 'rgba(120,70,60,.32)'; x.lineWidth = 2;
      const r = 16; for (let j = -1; j < 12; j++) for (let i = -1; i < 10; i++){ const cx = i*r*1.75 + (j % 2)*r*0.87, cy = j*r*1.5; x.beginPath(); for (let k = 0; k < 7; k++){ const a = PI/6 + k*PI/3; x.lineTo(cx + Math.cos(a)*r, cy + Math.sin(a)*r); } x.stroke(); } });
    const grass = tex(256, 256, (x, w, h) => { x.fillStyle = '#58893a'; x.fillRect(0, 0, w, h); for (let i = 0; i < 9000; i++){ x.fillStyle = rnd() < 0.5 ? 'rgba(150,175,90,.35)' : 'rgba(40,70,25,.32)'; x.fillRect(rnd()*w, rnd()*h, 1, 2 + rnd()*2); } });
    const asph = tex(256, 256, (x, w, h) => { x.fillStyle = '#6d6a66'; x.fillRect(0, 0, w, h); noise(x, w, h, 24); });
    const sandTexC = tex(256, 256, (x, w, h) => { x.fillStyle = '#d9c9a8'; x.fillRect(0, 0, w, h); noise(x, w, h, 18); });
    const GM = {park: Lm({map: greyPave}), walk: Lm({map: pinkPave}), prom: Lm({map: redPave}), lawn: Lm({map: grass}), asph: Lm({map: asph})};
    const AX = CN.axis.map(c => [c[0] - OX, c[1] - OZ]), AXB = CN.axB.map(c => [c[0] - OX, c[1] - OZ]);
    const nearOn = (L, x, z) => { let bd = 1e9, bp = L[0]; for (let i = 0; i + 1 < L.length; i++){ const [ax, az] = L[i], [bx, bz] = L[i + 1], vx = bx - ax, vz = bz - az, l2 = vx*vx + vz*vz || 1, t = clamp(((x - ax)*vx + (z - az)*vz)/l2, 0, 1), px = ax + vx*t, pz = az + vz*t, d = (x - px)**2 + (z - pz)**2; if (d < bd){ bd = d; bp = [px, pz]; } } return [bp, Math.sqrt(bd)]; };
    const Hf = (x, z) => { const [pa, da] = nearOn(AX, x, z), [pb, db] = nearOn(AXB, x, z), p = da < db ? pa : pb; return Math.max(H(x, z), H(p[0], p[1])); };
    const UVS = {park: 1/4, walk: 1/4, prom: 1/4, lawn: 1/8, asph: 1/8};
    const TOP = {park: 0.22, walk: 0.24, prom: 0.22, lawn: 0.25, asph: 0.2};
    // walkable heights: a 2 m grid of what the paving adds on top of the ground
    const CG = 2, CT = new Map();
    for (const k in CN.tris){ const t = CN.tris[k], top = TOP[k], P = [], N = [], U = [];
      for (let i = 0; i < t.length; i += 6){
        const v = [[t[i] - OX, t[i + 1] - OZ], [t[i + 2] - OX, t[i + 3] - OZ], [t[i + 4] - OX, t[i + 5] - OZ]];
        const cr = (v[1][0] - v[0][0])*(v[2][1] - v[0][1]) - (v[1][1] - v[0][1])*(v[2][0] - v[0][0]); const o = cr > 0 ? [0, 2, 1] : [0, 1, 2];
        const tv = []; for (const j of o){ const [x, z] = v[j], yv = Hf(x, z) + top; P.push(x, yv, z); N.push(0, 1, 0); U.push(x*UVS[k], z*UVS[k]); tv.push(x, yv, z); }
        let x0 = 1e9, x1 = -1e9, z0 = 1e9, z1 = -1e9; v.forEach(c => { x0 = Math.min(x0, c[0]); x1 = Math.max(x1, c[0]); z0 = Math.min(z0, c[1]); z1 = Math.max(z1, c[1]); });
        for (let a = Math.floor(x0/CG); a <= Math.floor(x1/CG); a++) for (let b = Math.floor(z0/CG); b <= Math.floor(z1/CG); b++){ const kk = a + ',' + b; let L = CT.get(kk); if (!L) CT.set(kk, L = []); L.push(tv); } }
      const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(P, 3)); g.setAttribute('normal', new T.Float32BufferAttribute(N, 3)); g.setAttribute('uv', new T.Float32BufferAttribute(U, 2));
      const ms = new T.Mesh(g, GM[k]); ms.receiveShadow = true; G.add(ms); }
    // the walkable height is exactly the paving's own surface (the triangle under you), so feet never sink into it
    CTOP = (x, z) => { const L = CT.get(Math.floor(x/CG) + ',' + Math.floor(z/CG)); if (!L) return -1e9; let best = -1e9;
      for (const t of L){ const ax = t[0], az = t[2], bx = t[3], bz = t[5], cx = t[6], cz = t[8], d = (bz - cz)*(ax - cx) + (cx - bx)*(az - cz); if (Math.abs(d) < 1e-9) continue;
        const l1 = ((bz - cz)*(x - cx) + (cx - bx)*(z - cz))/d, l2 = ((cz - az)*(x - cx) + (ax - cx)*(z - cz))/d, l3 = 1 - l1 - l2;
        if (l1 < -1e-4 || l2 < -1e-4 || l3 < -1e-4) continue; const y = l1*t[1] + l2*t[4] + l3*t[7]; if (y > best) best = y; }
      return best; };
    const Ht = (x, z) => Math.max(H(x, z), CTOP(x, z));
    // kerbs: a stone band round each paved/planted piece (black-yellow by the traffic, black-white in the parking)
    const kerbBY = tex(128, 16, (x, w, h) => { x.fillStyle = '#e5b52b'; x.fillRect(0, 0, w, h); x.fillStyle = '#262626'; x.fillRect(w/2, 0, w/2, h); noise(x, w, h, 10); });
    const kerbBW = tex(128, 16, (x, w, h) => { x.fillStyle = '#efede6'; x.fillRect(0, 0, w, h); x.fillStyle = '#262626'; x.fillRect(w/2, 0, w/2, h); noise(x, w, h, 10); });
    const ribbon = (pts, y0f, y1f, mat, uScale) => { const P = [], N = [], U = []; let d = 0;
      for (let i = 0; i + 1 < pts.length; i++){ const [ax, az] = pts[i], [bx, bz] = pts[i + 1], L = Math.hypot(bx - ax, bz - az); if (L < 0.01) continue; const nx = (bz - az)/L, nz = -(bx - ax)/L;
        const n = Math.max(1, Math.ceil(L/2)); for (let s = 0; s < n; s++){ const t0 = s/n, t1 = (s + 1)/n, x0 = ax + (bx - ax)*t0, z0 = az + (bz - az)*t0, x1 = ax + (bx - ax)*t1, z1 = az + (bz - az)*t1;
          const a0 = y0f(x0, z0), a1 = y0f(x1, z1), b0 = y1f(x0, z0), b1 = y1f(x1, z1), u0 = (d + L*t0)*uScale, u1 = (d + L*t1)*uScale;
          P.push(x0, a0, z0, x1, a1, z1, x1, b1, z1, x0, a0, z0, x1, b1, z1, x0, b0, z0); for (let k = 0; k < 6; k++) N.push(nx, 0, nz); U.push(u0, 0, u1, 0, u1, 1, u0, 0, u1, 1, u0, 1); }
        d += L; }
      const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(P, 3)); g.setAttribute('normal', new T.Float32BufferAttribute(N, 3)); g.setAttribute('uv', new T.Float32BufferAttribute(U, 2)); const ms = new T.Mesh(g, mat); G.add(ms); return ms; };
    const kMatBY = Lm({map: kerbBY, side: T.DoubleSide}), kMatBW = Lm({map: kerbBW, side: T.DoubleSide});
    CN.kerbs.forEach(k => ribbon(k.p.map(c => [c[0] - OX, c[1] - OZ]), (x, z) => Hf(x, z) - 0.3, (x, z) => Hf(x, z) + 0.2, k.k === 'by' ? kMatBY : kMatBW, 1));
    // white parking-bay lines
    { const P = [], N = []; CN.bays.forEach(b => { const ax = b[0] - OX, az = b[1] - OZ, bx = b[2] - OX, bz = b[3] - OZ, L = Math.hypot(bx - ax, bz - az), px = -(bz - az)/L*0.06, pz = (bx - ax)/L*0.06;
        const y = (x, z) => Hf(x, z) + 0.235; const q = [[ax + px, az + pz], [bx + px, bz + pz], [bx - px, bz - pz], [ax - px, az - pz]].map(c => [c[0], y(c[0], c[1]), c[1]]);
        [q[0], q[2], q[1], q[0], q[3], q[2]].forEach(v => { P.push(v[0], v[1], v[2]); N.push(0, 1, 0); }); });
      const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(P, 3)); g.setAttribute('normal', new T.Float32BufferAttribute(N, 3)); G.add(new T.Mesh(g, new T.MeshBasicMaterial({color: 0xe4e4df, side: T.DoubleSide}))); }
    // instancing helper: geo + list of [x, z, yaw, s?] (+ y from the paving)
    const _m = new T.Matrix4(), _q = new T.Quaternion(), _e = new T.Euler(), _p = new T.Vector3(), _s = new T.Vector3();
    const inst = (geo, mat, list, cast, yOff) => { if (!list.length) return null; const im = new T.InstancedMesh(geo, mat, list.length);
      list.forEach((L, i) => { const x = L[0], z = L[1]; _e.set(0, L[2] || 0, 0); _q.setFromEuler(_e); const s = L[3] || 1; _m.compose(_p.set(x, (L[4] !== undefined ? L[4] : Ht(x, z)) + (yOff || 0), z), _q, _s.set(s, s, s)); im.setMatrixAt(i, _m); });
      im.castShadow = !!cast; im.receiveShadow = true; G.add(im); return im; };
    const vc = Lm({vertexColors: true});
    const cg = (geo, col, tx, ty, tz, rx, rz) => { if (rx) geo.rotateX(rx); if (rz) geo.rotateZ(rz); geo.translate(tx || 0, ty || 0, tz || 0); return colorGeo(geo.index ? geo.toNonIndexed() : geo, CC(col)); };
    const PT = (L) => L.map(p => [p[0] - OX, p[1] - OZ, p[2] || 0]);
    const BLK = 0x1e1e1e, GOLD = 0xb89b55, GLOBE = 0xf6f2e4;
    // double-arm lantern post (median / separator): black, about 8.5 m, two lanterns
    const lampDGeo = mergeGeos([cg(new T.CylinderGeometry(0.32, 0.4, 0.9, 8), BLK, 0, 0.45), cg(new T.CylinderGeometry(0.09, 0.14, 8.0, 8), BLK, 0, 4.4), cg(new T.SphereGeometry(0.16, 8, 6), GOLD, 0, 8.5)]
      .concat(...[-1, 1].map(s => [cg(new T.TorusGeometry(0.75, 0.05, 6, 12, PI*0.75), BLK, s*0.7, 7.6, 0, 0, s > 0 ? -PI*0.05 : PI*0.3), cg(new T.BoxGeometry(1.5, 0.07, 0.07), BLK, s*0.75, 7.95),
        cg(new T.CylinderGeometry(0.28, 0.14, 0.62, 6), GLOBE, s*1.5, 7.35), cg(new T.ConeGeometry(0.34, 0.3, 6), BLK, s*1.5, 7.82), cg(new T.SphereGeometry(0.06, 6, 4), GOLD, s*1.5, 8.0)])));
    inst(lampDGeo, vc, PT(CN.pts.lampD), true);
    // five-globe park lamp (lawn by the canal): black post on a stone base
    const lamp5Geo = mergeGeos([cg(new T.BoxGeometry(1.1, 0.25, 1.1), 0xd8d2c6, 0, 0.12), cg(new T.CylinderGeometry(0.22, 0.3, 0.9, 8), BLK, 0, 0.7), cg(new T.CylinderGeometry(0.08, 0.11, 3.6, 8), BLK, 0, 2.9),
      cg(new T.SphereGeometry(0.26, 10, 8), GLOBE, 0, 5.05)].concat(...[0, 1, 2, 3].map(k => { const a = k*PI/2, cx = Math.cos(a)*0.55, cz = Math.sin(a)*0.55;
        return [cg(new T.BoxGeometry(Math.abs(cx) + 0.05, 0.05, Math.abs(cz) + 0.05), BLK, cx/2, 4.45, cz/2), cg(new T.SphereGeometry(0.22, 10, 8), GLOBE, cx, 4.62, cz)]; })));
    inst(lamp5Geo, vc, PT(CN.pts.lamp5), true);
    // white urns with yellow flowers (median)
    const urnPts = []; for (let i = 0; i <= 12; i++){ const t = i/12; urnPts.push(new T.Vector2(0.18 + Math.sin(t*PI)*0.32 + (t > 0.85 ? 0.12 : 0), t*0.95)); }
    const urnGeo = mergeGeos([cg(new T.CylinderGeometry(0.32, 0.38, 0.18, 10), 0xf1efe9, 0, 0.09), cg(new T.LatheGeometry(urnPts, 12), 0xf6f4ee, 0, 0.18), cg(new T.SphereGeometry(0.5, 8, 6).scale(1, 0.55, 1), 0xe9c537, 0, 1.18)]);
    inst(urnGeo, vc, PT(CN.pts.urn), false);
    // date palms (separator, grove, lawn): the world's own palm model
    const pgeo = palmGeo(9, false), pmat = palmMat(false);
    inst(pgeo, pmat, PT(CN.pts.palm).map(p => [p[0], p[1], rnd()*6, 1.05]), true);
    inst(pgeo, pmat, PT(CN.pts.grove).map(p => [p[0], p[1], rnd()*6, 0.7 + rnd()*0.15]), true);
    // flame trees (poinciana): wide flat crown, red-orange blossom over green
    const flameGeo = mergeGeos([cg(new T.CylinderGeometry(0.16, 0.26, 3.0, 7), 0x6b5440, 0, 1.5), cg(new T.CylinderGeometry(0.08, 0.12, 2.2, 5).rotateZ(0.7), 0x6b5440, 0.6, 3.1), cg(new T.CylinderGeometry(0.08, 0.12, 2.2, 5).rotateZ(-0.7), 0x6b5440, -0.6, 3.1)]
      .concat(...[[0, 0, 3.0, 0x4f7d2f], [2.2, 0.8, 1.9, 0x44702a], [-2.0, -0.9, 2.0, 0x557f33], [0.5, -2.2, 1.8, 0x4a782c], [-0.6, 2.1, 1.9, 0x527c30]].map(([dx, dz, r, gc]) => [cg(new T.IcosahedronGeometry(r, 1).scale(1, 0.42, 1), gc, dx, 3.9, dz),
        cg(new T.IcosahedronGeometry(r*0.92, 1).scale(1, 0.3, 1), (dx + dz) > 0 ? 0xd8432a : 0xe4592f, dx*0.95, 4.25, dz*0.95)])));
    inst(flameGeo, vc, PT(CN.pts.flame), true);
    const ficusGeo = mergeGeos([cg(new T.CylinderGeometry(0.2, 0.3, 2.2, 7), 0x6b5440, 0, 1.1), cg(new T.SphereGeometry(2.6, 12, 9).scale(1, 0.85, 1), 0x3f7a2a, 0, 3.8)]);
    // black iron railings by the water: posts every 2 m and two rails
    { const posts = [], bars = []; CN.rails.forEach(r => { const p = r.map(c => [c[0] - OX, c[1] - OZ]); let acc = 0;
        for (let i = 0; i + 1 < p.length; i++){ const [ax, az] = p[i], [bx, bz] = p[i + 1], L = Math.hypot(bx - ax, bz - az); if (L < 0.05) continue; const yaw = Math.atan2(bx - ax, bz - az);
          for (let d = (2 - acc % 2) % 2; d < L; d += 2){ const x = ax + (bx - ax)*d/L, z = az + (bz - az)*d/L; posts.push([x, z, yaw]); }
          acc += L; const mx = (ax + bx)/2, mz = (az + bz)/2; bars.push([mx, mz, yaw, L]); } });
      inst(cg(new T.BoxGeometry(0.07, 1.1, 0.07), BLK, 0, 0.55), vc, posts, false);
      const bg = new T.BoxGeometry(0.05, 0.05, 1); const im = new T.InstancedMesh(bg, Lm({color: BLK}), bars.length*2);
      bars.forEach((b, i) => [1.05, 0.5].forEach((hh, j) => { _e.set(0, b[2], 0); _q.setFromEuler(_e); _m.compose(_p.set(b[0], Ht(b[0], b[1]) + hh, b[1]), _q, _s.set(1, 1, b[3] + 0.04)); im.setMatrixAt(i*2 + j, _m); })); G.add(im); }
    { const st = canvasTex(256, 64, (x, w, h) => { x.fillStyle = '#9d988f'; x.fillRect(0, 0, w, h); noise(x, w, h, 26); x.strokeStyle = 'rgba(60,55,50,.45)'; x.lineWidth = 2; for (let j = 0; j < 4; j++){ x.beginPath(); x.moveTo(0, j*16); x.lineTo(w, j*16); x.stroke(); for (let i = 0; i < 8; i++){ const o = (j % 2)*16; x.beginPath(); x.moveTo(i*32 + o, j*16); x.lineTo(i*32 + o, j*16 + 16); x.stroke(); } } x.fillStyle = '#d9d4ca'; x.fillRect(0, 0, w, 6); });
      const sm = Lm({map: st, side: T.DoubleSide}); CN.cwall.forEach(w => ribbon(w.map(c => [c[0] - OX, c[1] - OZ]), () => cfg.waterY - 1.5, (x, z) => Hf(x, z) + 0.32, sm, 1/3)); }
    // «الجسر الجديد»: concrete parapets on both outer edges, the yellow-hatched median between the two carriageways, yellow crossings at both ends
    if (CN.bridge){ const Bz = CN.bridge, topY = (x, z) => Math.max(H(x, z) + roadTop(x, z), bridgeTop(x, z)), hw = 4.05, medW = Bz.gap/2 - 3.65;
      const pts = L => L.map(c => [c[0] - OX, c[1] - OZ]); const a = pts(Bz.a), b = pts(Bz.b), mid = pts(Bz.mid);
      const off = (L, o) => L.map(([x, z], i) => { const j = Math.min(i, L.length - 2), [ax, az] = L[j], [bx, bz] = L[j + 1], l = Math.hypot(bx - ax, bz - az); return [x + (bz - az)/l*o, z - (bx - ax)/l*o]; });
      const dense = L => { const o = []; for (let i = 0; i + 1 < L.length; i++){ const [ax, az] = L[i], [bx, bz] = L[i + 1], n = Math.ceil(Math.hypot(bx - ax, bz - az)/2); for (let k = 0; k < n; k++) o.push([ax + (bx - ax)*k/n, az + (bz - az)*k/n]); } o.push(L[L.length - 1]); return o; };
      const sideOf = (L, P) => { const [ax, az] = L[0], [bx, bz] = L[L.length - 1]; return Math.sign((bx - ax)*(P[1] - az) - (bz - az)*(P[0] - ax)) || 1; };
      const conc = Lm({color: 0xd7d2c8, side: T.DoubleSide});
      // parapets on the two outer edges (away from the other carriageway), 1 m high, with a cap
      [[a, b], [b, a]].forEach(([L, M]) => { const sg = -sideOf(L, M[1] || M[0]); const e = dense(off(L, sg*hw)); const w = ribbon(e, (x, z) => topY(x, z) - 0.35, (x, z) => topY(x, z) + 0.95, conc, 1/4); w.castShadow = true; ribbon(dense(off(L, sg*(hw + 0.3))), (x, z) => topY(x, z) + 0.95, (x, z) => topY(x, z) + 1.05, conc, 1/4); ribbon(dense(off(L, sg*(hw - 0.3))), (x, z) => topY(x, z) + 0.95, (x, z) => topY(x, z) + 1.05, conc, 1/4); });
      // the median: yellow hatching between the carriageways (3 m)
      const hatchY = canvasTex(128, 128, (c, w, h) => { c.fillStyle = '#6d6a66'; c.fillRect(0, 0, w, h); c.strokeStyle = '#e6c21a'; c.lineWidth = 7; for (let i = -128; i < 256; i += 40){ c.beginPath(); c.moveTo(i, 128); c.lineTo(i + 128, 0); c.stroke(); } c.fillStyle = '#e6c21a'; c.fillRect(0, 0, 8, h); c.fillRect(w - 8, 0, 8, h); });
      { const L1 = dense(off(mid, -medW)), L2 = dense(off(mid, medW)), n = Math.min(L1.length, L2.length), P = [], N = [], U = [];
        const yAt = i => Math.max(topY(L1[i][0], L1[i][1]), topY(L2[i][0], L2[i][1])) + 0.04; for (let i = 0; i + 1 < n; i++){ const q = [L1[i], L2[i], L2[i + 1], L1[i + 1]], ys = [yAt(i), yAt(i), yAt(i + 1), yAt(i + 1)]; [0, 1, 2, 0, 2, 3].forEach(k => { const [x, z] = q[k]; P.push(x, ys[k], z); N.push(0, 1, 0); U.push(k === 0 || k === 3 ? 0 : 1, (k < 2 ? i : i + 1)*2/3); }); }
        const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(P, 3)); g.setAttribute('normal', new T.Float32BufferAttribute(N, 3)); g.setAttribute('uv', new T.Float32BufferAttribute(U, 2)); G.add(new T.Mesh(g, Lm({map: hatchY, side: T.DoubleSide, polygonOffset: true, polygonOffsetFactor: -6, polygonOffsetUnits: -8}))); }
      { const lp = []; const md = dense(mid); for (let i = 6; i < md.length - 6; i += 12) lp.push([md[i][0], md[i][1], Math.atan2(md[i + 1][0] - md[i][0], md[i + 1][1] - md[i][1]), 1, Math.max(topY(md[i][0] - 2, md[i][1]), topY(md[i][0] + 2, md[i][1])) + 0.05]); inst(lampDGeo, vc, lp, true); }
      // yellow zebra crossings at both ends, over both carriageways and the median
      const ym = new T.MeshBasicMaterial({color: 0xe6c21a, side: T.DoubleSide, polygonOffset: true, polygonOffsetFactor: -6, polygonOffsetUnits: -8});
      [[mid[0], mid[1]], [mid[mid.length - 1], mid[mid.length - 2]]].forEach(([m0, m1]) => { const l = Math.hypot(m1[0] - m0[0], m1[1] - m0[1]), ux = (m1[0] - m0[0])/l, uz = (m1[1] - m0[1])/l, nx = -uz, nz = ux, cx = m0[0] + ux*3, cz = m0[1] + uz*3, span = Bz.gap/2 + hw - 0.3;
        const yC = Math.max(topY(cx + nx*(Bz.gap/2), cz + nz*(Bz.gap/2)), topY(cx - nx*(Bz.gap/2), cz - nz*(Bz.gap/2))) + 0.05; for (let o = -span; o < span; o += 1.2){ const P = [], N = []; [[o, 0], [o + 0.6, 0], [o + 0.6, 3.5], [o, 0], [o + 0.6, 3.5], [o, 3.5]].forEach(([w, d]) => { const x = cx + nx*w + ux*d, z = cz + nz*w + uz*d; P.push(x, yC, z); N.push(0, 1, 0); });
          const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(P, 3)); g.setAttribute('normal', new T.Float32BufferAttribute(N, 3)); G.add(new T.Mesh(g, ym)); } }); }
    (CN.uturns || []).forEach(u => { const x = u.c[0] - OX, z = u.c[1] - OZ, g = new T.Group(); g.position.set(x, H(x, z) + 0.3, z); g.rotation.y = u.yaw; G.add(g);
      const ht = canvasTex(64, 128, (c, w, h) => { c.fillStyle = '#b5413a'; c.fillRect(0, 0, w, h); c.fillStyle = '#f4f2ec'; for (let i = 0; i < h; i += 24) c.fillRect(0, i + 4, w, 10); });
      const sh = new T.Shape([new T.Vector2(-u.w/2, 0), new T.Vector2(u.w/2, 0), new T.Vector2(0, -9)]); const gg = new T.ShapeGeometry(sh); gg.rotateX(-PI/2); const tri = new T.Mesh(gg, Lm({map: ht, polygonOffset: true, polygonOffsetFactor: -6, polygonOffsetUnits: -8, side: T.DoubleSide})); g.add(tri);
      const kb = new T.Mesh(new T.BoxGeometry(u.w, 0.16, 0.3), kMatBY); kb.position.set(0, 0.08, 0.1); g.add(kb); });
    if (CN.wallE){ const wl = CN.wallE.map(c => [c[0] - OX, c[1] - OZ]); const wm2 = Lm({color: 0xf4f2ec, side: T.DoubleSide}); ribbon(wl, (x, z) => H(x, z) - 0.2, (x, z) => H(x, z) + 2.3, wm2, 1/4); ribbon(wl.map(([x, z], i) => { const j = Math.min(i, wl.length - 2), [ax, az] = wl[j], [bx, bz] = wl[j + 1], l = Math.hypot(bx - ax, bz - az); return [x + (bz - az)/l*0.3, z - (bx - ax)/l*0.3]; }), (x, z) => H(x, z) - 0.2, (x, z) => H(x, z) + 2.3, wm2, 1/4);
      let acc = 0; for (let i = 0; i + 1 < wl.length; i++){ const [ax, az] = wl[i], [bx, bz] = wl[i + 1], l = Math.hypot(bx - ax, bz - az); for (let d = (6 - acc % 6) % 6; d < l; d += 6){ const px = ax + (bx - ax)*d/l, pz = az + (bz - az)*d/l; const pil = new T.Mesh(new T.BoxGeometry(0.6, 2.7, 0.7), wm2); pil.position.set(px, H(px, pz) + 1.15, pz); pil.rotation.y = Math.atan2(bx - ax, bz - az); G.add(pil); } acc += l; } }
    if (CN.touristSign){ const d = CN.touristSign, x = d.c[0] - OX, z = d.c[1] - OZ, y = Ht(x, z), g = new T.Group(); g.position.set(x, y, z); g.rotation.y = d.yaw + PI/2; G.add(g);
      const tx = canvasTex(512, 384, (c, w, h) => { c.fillStyle = '#6b3b1e'; c.fillRect(0, 0, w, h); c.strokeStyle = '#fff'; c.lineWidth = 6; c.strokeRect(8, 8, w - 16, h - 16); c.fillStyle = '#fff';
        [['القرية التراثية', 'Heritage Village'], ['حديقة شاطئ دبا الحصن', 'Dibba Al Hisn Beach Park'], ['قلعة دبا الحصن', 'Dibba Al Hisn Fort']].forEach(([ar, en], i) => { const yy = 70 + i*118; c.direction = 'rtl'; c.textAlign = 'right'; c.font = 'bold 40px Tajawal, Arial'; c.fillText(ar, w - 90, yy); c.direction = 'ltr'; c.font = 'bold 26px Arial'; c.fillText(en, w - 90, yy + 40); c.beginPath(); c.moveTo(40, yy); c.lineTo(70, yy - 18); c.lineTo(70, yy - 6); c.lineTo(100, yy - 6); c.lineTo(100, yy + 6); c.lineTo(70, yy + 6); c.lineTo(70, yy + 18); c.closePath(); c.fill(); }); });
      const bd = new T.Mesh(new T.PlaneGeometry(3.6, 2.7), Lm({map: tx})); bd.position.y = 2.8; g.add(bd); const bk = new T.Mesh(new T.PlaneGeometry(3.6, 2.7), Lm({color: 0x8e959a})); bk.position.set(0, 2.8, -0.03); bk.rotation.y = PI; g.add(bk);
      [-1.0, 1.0].forEach(o => { const lg = new T.Mesh(new T.BoxGeometry(0.12, 4.2, 0.12), Lm({color: 0x9aa0a4})); lg.position.set(o, 2.1, -0.08); g.add(lg); }); }
    // text on canvas (signs, shop names, road paint)
    const textTex = (t, o) => { o = o || {}; const W = o.w || 512, Hh = o.h || 128; return canvasTex(W, Hh, (x, w, h) => { x.fillStyle = o.bg || '#ffffff'; x.fillRect(0, 0, w, h);
      if (o.border){ x.strokeStyle = o.border; x.lineWidth = 8; x.strokeRect(6, 6, w - 12, h - 12); }
      x.fillStyle = o.fg || '#222'; x.font = (o.bold === false ? '' : 'bold ') + (o.size || 64) + 'px Tajawal, "Noto Naskh Arabic", Arial'; x.textAlign = 'center'; x.textBaseline = 'middle'; x.direction = 'rtl'; x.fillText(t, w/2, h/2 + 4); }); };
    // the mall: long three-storey cream arcade, Andalusian striped arches, blue windows, black balconies, small white domes on the roof
    const bayTex = canvasTex(256, 512, (x, w, h) => { x.fillStyle = '#efe4cc'; x.fillRect(0, 0, w, h); noise(x, w, h, 8);
      // ground floor: an open horseshoe arch (see-through to the shops behind the arcade), red/white voussoirs, pilasters with red inlay
      const ax = w/2, ay = 372, r = 94; x.globalCompositeOperation = 'destination-out'; x.beginPath(); x.moveTo(ax - r + 22, 512); x.lineTo(ax - r + 22, ay); x.arc(ax, ay, r - 22, PI, 0); x.lineTo(ax + r - 22, 512); x.closePath(); x.fill(); x.globalCompositeOperation = 'source-over';
      for (let k = 0; k < 14; k++){ const a0 = PI + k*PI/14 - 0.18, a1 = a0 + PI/14; x.fillStyle = k % 2 ? '#b8442f' : '#f4efe4'; x.beginPath(); x.arc(ax, ay, r, a0, a1 + 0.01); x.arc(ax, ay, r - 22, a1 + 0.01, a0, true); x.fill(); }
      x.fillStyle = '#c98a7e'; x.fillRect(8, 330, 8, 170); x.fillRect(w - 16, 330, 8, 170);
      // cornice bands
      x.fillStyle = '#e2d3b2'; x.fillRect(0, 262, w, 12); x.fillRect(0, 128, w, 10); x.fillRect(0, 16, w, 10);
      // two upper floors: arched blue windows with a white frame and a black iron balcony
      [[158, 84], [36, 74]].forEach(([y, hh]) => { x.fillStyle = '#3c6f9e'; x.fillRect(ax - 40, y + 14, 80, hh); x.beginPath(); x.arc(ax, y + 14, 40, PI, 0); x.fill(); x.strokeStyle = '#f7f3ea'; x.lineWidth = 6; x.strokeRect(ax - 40, y + 14, 80, hh); x.beginPath(); x.arc(ax, y + 14, 40, PI, 0); x.stroke();
        x.fillStyle = 'rgba(255,255,255,.25)'; x.fillRect(ax - 34, y + 20, 10, hh - 12);
        x.fillStyle = '#222'; for (let i = -48; i <= 48; i += 8) x.fillRect(ax + i, y + hh - 8, 3, 26); x.fillRect(ax - 52, y + hh - 10, 104, 5); x.fillRect(ax - 52, y + hh + 16, 104, 4); });
      x.fillStyle = '#d9c9a6'; x.fillRect(0, 0, w, 16); });
    // shopfronts at the back of the arcade: dark glass, frames, a red sign band
    const shopTex = canvasTex(256, 128, (x, w, h) => { x.fillStyle = '#efe4cc'; x.fillRect(0, 0, w, h); x.fillStyle = '#a3362c'; x.fillRect(20, 6, w - 40, 22); x.fillStyle = '#2f3a3f'; x.fillRect(24, 34, w - 48, h - 36);
      x.fillStyle = 'rgba(150,190,205,.45)'; x.fillRect(30, 40, (w - 66)/2, h - 44); x.fillRect(36 + (w - 66)/2, 40, (w - 66)/2, h - 44); x.fillStyle = '#e8dcc2'; x.fillRect(0, 0, 18, h); x.fillRect(w - 18, 0, 18, h); });
    const bayTex2 = canvasTex(256, 384, (x, w, h) => { x.fillStyle = '#efe4cc'; x.fillRect(0, 0, w, h); noise(x, w, h, 8);
      const ax = w/2, ay = 250, r = 94; x.globalCompositeOperation = 'destination-out'; x.beginPath(); x.moveTo(ax - r + 22, 384); x.lineTo(ax - r + 22, ay); x.arc(ax, ay, r - 22, PI, 0); x.lineTo(ax + r - 22, 384); x.closePath(); x.fill(); x.globalCompositeOperation = 'source-over';
      for (let k = 0; k < 14; k++){ const a0 = PI + k*PI/14 - 0.18, a1 = a0 + PI/14; x.fillStyle = k % 2 ? '#b8442f' : '#f4efe4'; x.beginPath(); x.arc(ax, ay, r, a0, a1 + 0.01); x.arc(ax, ay, r - 22, a1 + 0.01, a0, true); x.fill(); }
      x.fillStyle = '#c98a7e'; x.fillRect(8, 210, 8, 170); x.fillRect(w - 16, 210, 8, 170); x.fillStyle = '#e2d3b2'; x.fillRect(0, 140, w, 12); x.fillRect(0, 16, w, 10);
      x.fillStyle = '#3c6f9e'; x.fillRect(ax - 40, 50, 80, 76); x.beginPath(); x.arc(ax, 50, 40, PI, 0); x.fill(); x.strokeStyle = '#f7f3ea'; x.lineWidth = 6; x.strokeRect(ax - 40, 50, 80, 76); x.beginPath(); x.arc(ax, 50, 40, PI, 0); x.stroke();
      x.fillStyle = '#222'; for (let i = -48; i <= 48; i += 8) x.fillRect(ax + i, 118, 3, 26); x.fillRect(ax - 52, 116, 104, 5); x.fillRect(ax - 52, 142, 104, 4); x.fillStyle = '#d9c9a6'; x.fillRect(0, 0, w, 16); });
    const creamM = Lm({color: 0xeee3ca}), domeM = Lm({color: 0xf7f5ef}), mosqueM = Lm({color: 0xf2ece0});
    CN.blds.forEach(b => {
      if (b.k === 'mall'){
        const ext = (pp, y0, hh) => { const fp = pp.map(c => new T.Vector2(c[0] - OX, -(c[1] - OZ))); const eg = new T.ExtrudeGeometry(new T.Shape(fp), {depth: hh, bevelEnabled: false}); eg.rotateX(-PI/2); eg.translate(0, y0, 0); const ms = new T.Mesh(eg, creamM); ms.castShadow = ms.receiveShadow = true; G.add(ms); };
        const base = Math.min(...b.p.map(c => H(c[0] - OX, c[1] - OZ))), two = b.floors === 2, HT = two ? 9.4 : 12.5;
        ext(b.p, base + 5.7, HT - 5.6); ext(b.p2, base, 5.8);   // the upper floors overhang the 3 m arcade
        const line = b.line.map(c => [c[0] - OX, c[1] - OZ]), line2 = b.line2.map(c => [c[0] - OX, c[1] - OZ]); const bt = (two ? bayTex2 : bayTex).clone(); bt.needsUpdate = true;
        const fac = ribbon(line.slice().reverse(), (x, z) => base, (x, z) => base + HT + 0.1, Lm({map: bt, side: T.DoubleSide, alphaTest: 0.5}), 1/7.2); fac.castShadow = true;
        const stt = shopTex.clone(); stt.needsUpdate = true; ribbon(line2.slice().reverse(), () => base + 0.3, () => base + 5.7, Lm({map: stt, side: T.DoubleSide}), 1/7.2);
        // arcade paving under the arches, a lantern in every bay, merlons on the parapet
        { const P = [], N = [], U = []; for (let i = 0; i + 1 < line.length; i++){ const j = Math.min(i, line2.length - 2), q = [line[i], line[i + 1], line2[Math.min(j + 1, line2.length - 1)], line2[j]];
            [0, 1, 2, 0, 2, 3].forEach(k => { P.push(q[k][0], base + 0.32, q[k][1]); N.push(0, 1, 0); U.push(q[k][0]/4, q[k][1]/4); }); }
          const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(P, 3)); g.setAttribute('normal', new T.Float32BufferAttribute(N, 3)); g.setAttribute('uv', new T.Float32BufferAttribute(U, 2)); G.add(new T.Mesh(g, Lm({map: pinkPave, side: T.DoubleSide}))); }
        { const lan = [], mer = []; let acc2 = 0; for (let i = 0; i + 1 < line.length; i++){ const [ax, az] = line[i], [bx, bz] = line[i + 1], L = Math.hypot(bx - ax, bz - az), yaw = Math.atan2(bx - ax, bz - az), nx = (bz - az)/L, nz = -(bx - ax)/L;
            for (let d = (3.6 - acc2 % 7.2 + 7.2) % 7.2; d < L; d += 7.2) lan.push([ax + (bx - ax)*d/L + nx*1.5, az + (bz - az)*d/L + nz*1.5, yaw, 1, base + 3.9]);
            for (let d = (1.6 - acc2 % 1.6) % 1.6; d < L; d += 1.6) mer.push([ax + (bx - ax)*d/L + nx*0.2, az + (bz - az)*d/L + nz*0.2, yaw, 1, base + HT + 0.1]); acc2 += L; }
          inst(mergeGeos([cg(new T.CylinderGeometry(0.02, 0.02, 1.0, 4), BLK, 0, 0.9), cg(new T.CylinderGeometry(0.22, 0.16, 0.55, 6), 0xf3dca0, 0, 0.2), cg(new T.ConeGeometry(0.3, 0.25, 6), BLK, 0, 0.58)]), vc, lan, false);
          inst(cg(new T.BoxGeometry(0.7, 0.8, 0.35), 0xe6d8b8, 0, 0.4), vc, mer, false); }
        // roof domes every ~40 m and the taller block at the north end
        let acc = 0; for (let i = 0; i + 1 < line.length; i++){ const [ax, az] = line[i], [bx, bz] = line[i + 1], L = Math.hypot(bx - ax, bz - az); const nx = (bz - az)/L, nz = -(bx - ax)/L;
          for (let d = (40 - acc % 40) % 40; d < L; d += 40){ const x = ax + (bx - ax)*d/L + nx*6, z = az + (bz - az)*d/L + nz*6; const dm = new T.Mesh(new T.SphereGeometry(2.6, 14, 8, 0, PI*2, 0, PI/2), domeM); dm.position.set(x, base + HT + 1.1, z); G.add(dm);
            const dr = new T.Mesh(new T.CylinderGeometry(2.7, 2.7, 1.2, 14), creamM); dr.position.set(x, base + HT + 0.5, z); G.add(dr); }
          acc += L; }
        if (two){ let cx = 0, cz = 0; const pp = b.p.map(c => [c[0] - OX, c[1] - OZ]); pp.forEach(c => { cx += c[0]; cz += c[1]; }); cx /= pp.length; cz /= pp.length; const dm = (x, z, r2) => { const d = new T.Mesh(new T.SphereGeometry(r2, 14, 8, 0, PI*2, 0, PI/2), domeM); d.position.set(x, base + HT + 0.9, z); G.add(d); const dr = new T.Mesh(new T.CylinderGeometry(r2 + 0.1, r2 + 0.1, 1.0, 14), creamM); dr.position.set(x, base + HT + 0.4, z); G.add(dr); }; dm(cx, cz, 3.2); [[-15, -10], [15, -10], [-15, 10], [15, 10]].forEach(([dx, dz]) => dm(cx + dx, cz + dz, 1.8)); }
        const [ex, ez] = line[line.length - 1], [fx, fz] = line[line.length - 2], yaw = Math.atan2(ex - fx, ez - fz), tw = new T.Mesh(new T.BoxGeometry(16, two ? 0.01 : 5, 22), creamM), Ln = Math.hypot(ex - fx, ez - fz), tnx = (ez - fz)/Ln, tnz = -(ex - fx)/Ln;
        tw.position.set(ex - Math.sin(yaw)*11 + tnx*8, base + 15, ez - Math.cos(yaw)*11 + tnz*8); tw.rotation.y = yaw; tw.castShadow = true; G.add(tw);
      } else if (b.k === 'mosqueBig' || b.k === 'mosqueOld'){
        const big = b.k === 'mosqueBig', x = b.c[0] - OX, z = b.c[1] - OZ, y = H(x, z), g = new T.Group(); g.position.set(x, y, z); g.rotation.y = b.yaw; G.add(g);
        const hall = new T.Mesh(new T.BoxGeometry(b.w, big ? 11 : 6, b.d), mosqueM); hall.position.y = big ? 5.5 : 3; hall.castShadow = hall.receiveShadow = true; g.add(hall);
        const wt = canvasTex(256, 256, (cx, w, h) => { cx.fillStyle = '#f2ece0'; cx.fillRect(0, 0, w, h); cx.fillStyle = '#7a8f99'; cx.fillRect(88, 90, 80, 120); cx.beginPath(); cx.arc(128, 90, 40, PI, 0); cx.fill(); cx.strokeStyle = '#c9b48a'; cx.lineWidth = 10; cx.beginPath(); cx.arc(128, 90, 50, PI, 0); cx.stroke(); cx.strokeRect(78, 90, 100, 128); }); wt.repeat.set(b.w/6, 1);
        [[0, b.d/2 + 0.02, 0], [0, -b.d/2 - 0.02, PI], [b.w/2 + 0.02, 0, PI/2], [-b.w/2 - 0.02, 0, -PI/2]].forEach(([px, pz, ry]) => { const len = Math.abs(ry) === PI/2 ? b.d : b.w; const t = wt.clone(); t.needsUpdate = true; t.repeat.set(len/6, 1);
          const pl = new T.Mesh(new T.PlaneGeometry(len, big ? 8 : 4.5), Lm({map: t})); pl.position.set(px, big ? 5 : 2.8, pz); pl.rotation.y = ry; g.add(pl); });
        const dr = new T.Mesh(new T.CylinderGeometry(big ? 8 : 4, big ? 8 : 4, big ? 3 : 1.2, 24), mosqueM); dr.position.set(big ? -12 : 0, big ? 12.5 : 6.6, big ? 2 : 0); g.add(dr);
        const dome = new T.Mesh(new T.SphereGeometry(big ? 8.4 : 4.2, 24, 12, 0, PI*2, 0, PI/2), Lm({color: big ? 0xe8cfa0 : 0xfbfaf6})); dome.scale.y = big ? 1.25 : 1.1; dome.position.set(big ? -12 : 0, big ? 14 : 7.2, big ? 2 : 0); dome.castShadow = true; g.add(dome);
        const fin = new T.Mesh(new T.ConeGeometry(0.35, 2.2, 8), Lm({color: 0xc9a54a})); fin.position.set(big ? -12 : 0, big ? 25.6 : 12.4, big ? 2 : 0); g.add(fin);
        if (big) [[-20, -20], [4, -20], [-20, 20], [4, 20], [16, -8], [16, 8]].forEach(([dx, dz]) => { const sd = new T.Mesh(new T.SphereGeometry(2.6, 14, 8, 0, PI*2, 0, PI/2), Lm({color: 0xe8cfa0})); sd.position.set(dx, 11.2, dz); g.add(sd); });
        // minaret: big = octagonal cream with two balconies; old = slim white with beige bands
        const mg = new T.Group(); mg.position.set(b.w/2 - (big ? 3 : 2), 0, big ? b.d/2 - 3 : -b.d/2 + 2); g.add(mg);
        const H1 = big ? 36 : 15, sh = new T.Mesh(new T.CylinderGeometry(big ? 2.0 : 1.1, big ? 2.4 : 1.3, H1, 8), mosqueM); sh.position.y = H1/2; sh.castShadow = true; mg.add(sh);
        (big ? [20, 30] : [14]).forEach(hh => { const bal = new T.Mesh(new T.CylinderGeometry(big ? 3.0 : 1.8, big ? 2.4 : 1.3, 1.0, 8), Lm({color: big ? 0xe0cba0 : 0xd8c39a})); bal.position.y = hh; mg.add(bal); });
        if (!big) [5, 9, 18].forEach(hh => { const bd = new T.Mesh(new T.CylinderGeometry(1.16, 1.16, 0.6, 8), Lm({color: 0xc9a46a})); bd.position.y = hh; mg.add(bd); });
        const top = new T.Mesh(new T.SphereGeometry(big ? 1.9 : 1.1, 12, 8), Lm({color: big ? 0xe8cfa0 : 0xfbfaf6})); top.scale.y = 1.4; top.position.y = H1 + 1.6; mg.add(top);
        const cone = new T.Mesh(new T.ConeGeometry(0.25, 2, 6), Lm({color: 0xc9a54a})); cone.position.y = H1 + 4; mg.add(cone);
      } else if (b.k === 'heritage'){
        const line = b.line.map(c => [c[0] - OX, c[1] - OZ]); const base = Math.min(...line.map(c => H(c[0], c[1])));
        const ht = canvasTex(256, 256, (x, w, h) => { x.fillStyle = '#c9a676'; x.fillRect(0, 0, w, h); noise(x, w, h, 20); x.fillStyle = '#5b4632'; x.fillRect(80, 110, 96, 146); x.beginPath(); x.arc(128, 110, 48, PI, 0); x.fill(); x.fillStyle = '#b8955f'; x.fillRect(0, 0, w, 18); for (let i = 0; i < w; i += 32){ x.fillRect(i + 6, 0, 18, 30); } });
        const f = ribbon(line, () => base, () => base + 5.5, Lm({map: ht, side: T.DoubleSide}), 1/4.5); f.castShadow = true;
        const back = line.map(([x, z], i) => { const j = Math.min(i, line.length - 2), [ax, az] = line[j], [bx, bz] = line[j + 1], L = Math.hypot(bx - ax, bz - az); return [x - (bz - az)/L*b.d, z + (bx - ax)/L*b.d]; });
        const fp = line.concat(back.slice().reverse()).map(c => new T.Vector2(c[0], -c[1])); const eg = new T.ExtrudeGeometry(new T.Shape(fp), {depth: 5.4, bevelEnabled: false}); eg.rotateX(-PI/2); eg.translate(0, base, 0);
        const ms = new T.Mesh(eg, Lm({color: 0xc6a271})); ms.castShadow = true; G.add(ms);
      } else if (b.k === 'mosqueT'){
        const x = b.c[0] - OX, z = b.c[1] - OZ, y = H(x, z), g = new T.Group(); g.position.set(x, y, z); g.rotation.y = b.yaw; G.add(g); const wm = Lm({color: 0xf6f3ec});
        const hall = new T.Mesh(new T.BoxGeometry(b.w, 8, b.d), wm); hall.position.y = 4; hall.castShadow = hall.receiveShadow = true; g.add(hall);
        const ft = canvasTex(256, 256, (c, w, h) => { c.fillStyle = '#f6f3ec'; c.fillRect(0, 0, w, h); c.fillStyle = '#e9e2d2'; c.fillRect(40, 30, 176, 210); c.fillStyle = '#7a4a2a'; c.beginPath(); c.moveTo(128, 60); c.lineTo(190, 110); c.lineTo(190, 230); c.lineTo(66, 230); c.lineTo(66, 110); c.closePath(); c.fill(); c.strokeStyle = '#f6f3ec'; c.lineWidth = 3; for (let i = 70; i < 190; i += 14){ c.beginPath(); c.moveTo(i, 110); c.lineTo(i, 230); c.stroke(); } for (let j = 115; j < 230; j += 14){ c.beginPath(); c.moveTo(66, j); c.lineTo(190, j); c.stroke(); } });
        [[0, b.d/2 + 0.02, 0, b.w], [0, -b.d/2 - 0.02, PI, b.w], [b.w/2 + 0.02, 0, PI/2, b.d], [-b.w/2 - 0.02, 0, -PI/2, b.d]].forEach(([px, pz, ry, len]) => { const t = ft.clone(); t.needsUpdate = true; t.repeat.set(len/6, 1); const pl = new T.Mesh(new T.PlaneGeometry(len, 7), Lm({map: t})); pl.position.set(px, 3.6, pz); pl.rotation.y = ry; g.add(pl); });
        const dome = new T.Mesh(new T.SphereGeometry(4.2, 20, 10, 0, PI*2, 0, PI/2), Lm({color: 0xe8d9b8})); dome.position.y = 9.2; g.add(dome); const dr = new T.Mesh(new T.CylinderGeometry(4.3, 4.3, 1.4, 20), wm); dr.position.y = 8.6; g.add(dr);
        [[-b.w/2 + 2, b.d/2 - 2], [b.w/2 - 2, b.d/2 - 2]].forEach(([mx, mz]) => { const mn = new T.Mesh(new T.CylinderGeometry(0.9, 1.1, 20, 8), wm); mn.position.set(mx, 10, mz); mn.castShadow = true; g.add(mn); const cap = new T.Mesh(new T.SphereGeometry(1.0, 10, 8), Lm({color: 0xe8d9b8})); cap.scale.y = 1.4; cap.position.set(mx, 20.6, mz); g.add(cap); const bal = new T.Mesh(new T.CylinderGeometry(1.5, 1.2, 0.8, 8), wm); bal.position.set(mx, 15, mz); g.add(bal); });
        // forecourt: cream/red paving to the road and a black iron fence along it
        const fc = new T.Mesh(new T.PlaneGeometry(b.w + 14, 14), Lm({map: pinkPave})); fc.rotation.x = -PI/2; fc.position.set(0, 0.26, b.d/2 + 7); g.add(fc);
        for (let o = -(b.w + 14)/2; o <= (b.w + 14)/2; o += 2.2){ const pst = new T.Mesh(new T.BoxGeometry(0.1, 1.5, 0.1), Lm({color: 0x1e1e1e})); pst.position.set(o, 0.75, b.d/2 + 14); g.add(pst); }
        [0.5, 1.3].forEach(hh => { const rl = new T.Mesh(new T.BoxGeometry(b.w + 14, 0.05, 0.05), Lm({color: 0x1e1e1e})); rl.position.set(0, hh, b.d/2 + 14); g.add(rl); });
      } else if (b.k === 'block'){
        const x = b.c[0] - OX, z = b.c[1] - OZ, y = H(x, z), wallC = {cream: '#efe6d3', beige: '#e3d2b0', pink: '#e8b9a3'}[b.col || 'beige'], winC = {cream: '#3c6f9e', beige: '#5b6d74', pink: '#4a5a62'}[b.col || 'beige']; const bl = canvasTex(256, 256, (cx, w, h) => { cx.fillStyle = wallC; cx.fillRect(0, 0, w, h); noise(cx, w, h, 10); const rows = Math.max(2, Math.round(b.h/3.4)); for (let j = 0; j < rows; j++) for (let i = 0; i < 4; i++){ cx.fillStyle = winC; cx.fillRect(i*64 + 14, j*(256/rows) + 12, 36, 256/rows*0.55); cx.fillStyle = 'rgba(0,0,0,.12)'; cx.fillRect(i*64 + 8, j*(256/rows) + 256/rows*0.55 + 14, 48, 5); } }); bl.repeat.set(b.w/14, 1);
        const m = new T.Mesh(new T.BoxGeometry(b.w, b.h, b.d), Lm({map: bl})); m.position.set(x, y + b.h/2, z); m.rotation.y = b.yaw; m.castShadow = m.receiveShadow = true; G.add(m);
      } else if (b.k === 'ruins'){
        const x = b.c[0] - OX, z = b.c[1] - OZ, y = H(x, z), sm = Lm({color: 0xb39a76}), L = [];
        for (let k = 0; k < 9; k++){ const a = rnd()*PI, wl = 4 + rnd()*9; L.push([x + (rnd() - 0.5)*b.w, z + (rnd() - 0.5)*b.d, a, wl]); }
        L.forEach(([px, pz, a, wl]) => { const m = new T.Mesh(new T.BoxGeometry(wl, 0.6 + rnd()*0.9, 0.7), sm); m.position.set(px, H(px, pz) + 0.4, pz); m.rotation.y = a; m.castShadow = true; G.add(m); });
        const tw = new T.Mesh(new T.CylinderGeometry(2.6, 3.0, 2.2, 14), sm); tw.position.set(x + b.w*0.35, y + 1.1, z - b.d*0.35); G.add(tw);
      } else if (b.k === 'shop1'){
        const x = b.c[0] - OX, z = b.c[1] - OZ, y = H(x, z), g = new T.Group(); g.position.set(x, y, z); g.rotation.y = b.yaw; G.add(g);
        const bx = new T.Mesh(new T.BoxGeometry(b.w, 4.2, b.d), Lm({color: 0xe8dcc4})); bx.position.y = 2.1; bx.castShadow = true; g.add(bx);
        const gl = new T.Mesh(new T.PlaneGeometry(b.w - 2, 2.6), Lm({color: 0x3a4a52})); gl.position.set(0, 1.4, b.d/2 + 0.02); g.add(gl);
        const sg = new T.Mesh(new T.PlaneGeometry(b.w - 1, 1.1), Lm({map: textTex(b.n, {bg: '#ffffff', fg: '#1d4f8a', size: 52, w: 640})})); sg.position.set(0, 3.45, b.d/2 + 0.03); g.add(sg);
      } else if (b.k === 'cafe'){
        const x = b.c[0] - OX, z = b.c[1] - OZ, y = Ht(x, z), g = new T.Group(); g.position.set(x, y, z); g.rotation.y = b.yaw; G.add(g);
        const wood = canvasTex(128, 128, (cx, w, h) => { cx.fillStyle = '#4a3324'; cx.fillRect(0, 0, w, h); for (let i = 0; i < w; i += 8){ cx.fillStyle = i % 16 ? '#3d2a1d' : '#57402e'; cx.fillRect(i, 0, 6, h); } noise(cx, w, h, 12); }); wood.repeat.set(3, 1);
        const bx = new T.Mesh(new T.BoxGeometry(b.d, 4.2, b.w), Lm({map: wood})); bx.position.y = 2.1; bx.castShadow = true; g.add(bx);
        const rf = new T.Mesh(new T.BoxGeometry(b.d + 2.4, 0.3, b.w + 2.4), Lm({color: 0x2e2620})); rf.position.y = 4.35; g.add(rf);
        const sgn = new T.Mesh(new T.PlaneGeometry(6, 1.1), Lm({map: textTex(b.n, {bg: '#2a1d14', fg: '#f0a640', size: 70})})); sgn.position.set(-b.d/2 - 0.05, 3.6, 0); sgn.rotation.y = -PI/2; g.add(sgn);
        const sg2 = sgn.clone(); sg2.position.x = b.d/2 + 0.05; sg2.rotation.y = PI/2; g.add(sg2);
      } });
    // shop signs on the arcade (names as they show on the map)
    CN.shops.forEach(s => { const x = s.c[0] - OX, z = s.c[1] - OZ; const pl = new T.Mesh(new T.PlaneGeometry(5.2, 0.9), Lm({map: textTex(s.t, {bg: '#ffffff', fg: '#7a1f1f', size: 66})}));
      pl.position.set(x + Math.sin(s.yaw)*0.25, H(x, z) + 4.55, z + Math.cos(s.yaw)*0.25); pl.rotation.y = s.yaw; G.add(pl); });
    // the giant flag (UAE): white pole and the flag
    { const x = CN.flag[0] - OX, z = CN.flag[1] - OZ, y = H(x, z), hP = 52;
      const pole = new T.Mesh(new T.CylinderGeometry(0.35, 0.75, hP, 12), Lm({color: 0xdfe2e4})); pole.position.set(x, y + hP/2, z); pole.castShadow = true; G.add(pole);
      const fl = canvasTex(256, 128, (c, w, h) => { c.fillStyle = '#00843d'; c.fillRect(0, 0, w, h/3); c.fillStyle = '#ffffff'; c.fillRect(0, h/3, w, h/3); c.fillStyle = '#000000'; c.fillRect(0, 2*h/3, w, h/3); c.fillStyle = '#ef3340'; c.fillRect(0, 0, w/4, h); });
      const fg = new T.PlaneGeometry(16, 8, 16, 1); const pa = fg.attributes.position; for (let i = 0; i < pa.count; i++){ const u = pa.getX(i) + 8; pa.setZ(i, Math.sin(u*0.45)*0.6*(u/16)); } fg.computeVertexNormals();
      const flg = new T.Mesh(fg, Lm({map: fl, side: T.DoubleSide})); flg.position.set(x + 8, y + hP - 4.5, z); flg.castShadow = true; G.add(flg);
      const base = new T.Mesh(new T.CylinderGeometry(3.2, 3.6, 0.5, 20), Lm({color: 0xece9e2})); base.position.set(x, y + 0.25, z); G.add(base); }
    { const x = CN.fountain[0] - OX, z = CN.fountain[1] - OZ, y = Ht(x, z); const rim = new T.Mesh(new T.CylinderGeometry(4.2, 4.4, 0.6, 28), Lm({color: 0xece8de})); rim.position.set(x, y + 0.3, z); G.add(rim);
      const wtr = new T.Mesh(new T.CircleGeometry(3.9, 28), Lm({color: 0x3f8fc4})); wtr.rotation.x = -PI/2; wtr.position.set(x, y + 0.55, z); G.add(wtr); const jet = new T.Mesh(new T.CylinderGeometry(0.1, 0.45, 2.2, 10), Lm({color: 0xdff0ff, transparent: true, opacity: 0.7})); jet.position.set(x, y + 1.6, z); G.add(jet); }
    // دوار مسجد الشيخ راشد (from above): white flowers, 16 dark-red triangles round the rim, a green 8-point star, a light centre circle
    const starTex = canvasTex(512, 512, (c, w, h) => { const cx = w/2, cy = h/2, R0 = 254; c.fillStyle = '#58893a'; c.fillRect(0, 0, w, h);
      c.fillStyle = '#d97a8e'; c.beginPath(); c.arc(cx, cy, R0, 0, PI*2); c.fill(); for (let i = 0; i < 6000; i++){ const a = rnd()*PI*2, rr = rnd()*R0, q = rnd(); c.fillStyle = q < 0.35 ? '#e9a0b4' : q < 0.6 ? '#c8324a' : q < 0.8 ? '#8d6bb3' : '#f3e6ea'; c.fillRect(cx + Math.cos(a)*rr, cy + Math.sin(a)*rr, 4, 4); }
      for (let k = 0; k < 16; k++){ const a0 = k*PI/8, a1 = a0 + PI/8, am = (a0 + a1)/2; c.fillStyle = k % 2 ? '#5a2a4a' : '#7a2f3f'; c.beginPath(); c.moveTo(cx + Math.cos(a0)*R0, cy + Math.sin(a0)*R0); c.lineTo(cx + Math.cos(a1)*R0, cy + Math.sin(a1)*R0); c.lineTo(cx + Math.cos(am)*R0*0.74, cy + Math.sin(am)*R0*0.74); c.closePath(); c.fill(); }
      c.fillStyle = '#4f7f33'; c.beginPath(); for (let k = 0; k <= 16; k++){ const a = PI/16 + k*PI/8, rr = k % 2 ? R0*0.5 : R0*0.8; c.lineTo(cx + Math.cos(a)*rr, cy + Math.sin(a)*rr); } c.fill();
      c.fillStyle = '#e3d6c2'; c.beginPath(); c.arc(cx, cy, R0*0.42, 0, PI*2); c.fill(); c.strokeStyle = '#c9b89c'; c.lineWidth = 3; for (let rr = 20; rr < R0*0.42; rr += 18){ c.beginPath(); c.arc(cx, cy, rr, 0, PI*2); c.stroke(); } });
    // ring markings: dashed lane line in the circulating road, dashed give-way edge, hatching round the splitter islands
    { const dash = (rr, y0) => { const P = [], N = []; for (let k = 0; k < 64; k += 2){ const a0 = k/64*PI*2, a1 = (k + 1)/64*PI*2; [[a0, rr - 0.08], [a1, rr - 0.08], [a1, rr + 0.08], [a0, rr - 0.08], [a1, rr + 0.08], [a0, rr + 0.08]].forEach(([a, r2]) => { P.push(Math.cos(a)*r2, 0, Math.sin(a)*r2); N.push(0, 1, 0); }); }
        const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(P, 3)); g.setAttribute('normal', new T.Float32BufferAttribute(N, 3)); return g; };
      const rb0 = CN.rb[0], x = rb0.c[0] - OX, z = rb0.c[1] - OZ, y = H(x, z) + 0.27, rbo = rb0.ro || (rb0.r + 4.6), wm = new T.MeshBasicMaterial({color: 0xe8e8e2, side: T.DoubleSide, polygonOffset: true, polygonOffsetFactor: -6, polygonOffsetUnits: -8});
      [rb0.r + 6.0, rbo + 5.3].forEach(rr => { const m = new T.Mesh(dash(rr), wm); m.position.set(x, y, z); G.add(m); });
      const ht = canvasTex(64, 64, (c, w, h) => { c.clearRect(0, 0, w, h); c.strokeStyle = '#f2f2ec'; c.lineWidth = 9; for (let i = -64; i < 128; i += 40){ c.beginPath(); c.moveTo(i, 64); c.lineTo(i + 64, 0); c.stroke(); } });
      const hm = new T.MeshBasicMaterial({map: ht, color: 0xdedede, transparent: true, alphaTest: 0.4, polygonOffset: true, polygonOffsetFactor: -6, polygonOffsetUnits: -8, side: T.DoubleSide});
      CN.hatch.forEach(p => { const v = p.map(c => new T.Vector2(c[0] - OX, c[1] - OZ)); let tris; try { tris = T.ShapeUtils.triangulateShape(v, []); } catch (e){ return; } const P = [], N = [], U = [];
        tris.forEach(t => t.forEach(i => { const q = v[i]; P.push(q.x, H(q.x, q.y) + 0.27, q.y); N.push(0, 1, 0); U.push(q.x/3, q.y/3); }));
        const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(P, 3)); g.setAttribute('normal', new T.Float32BufferAttribute(N, 3)); g.setAttribute('uv', new T.Float32BufferAttribute(U, 2)); G.add(new T.Mesh(g, hm)); }); }
    inst(lamp5Geo, vc, PT(CN.ringLamps).map(p => [p[0], p[1], 0, 1.35]), true);
    // yellow lines round the hatching (south arm), and the white planter on its island
    { const ymat = new T.MeshBasicMaterial({color: 0xe3b81c, side: T.DoubleSide, polygonOffset: true, polygonOffsetFactor: -7, polygonOffsetUnits: -9}); const P = [], N = [];
      (CN.ylines || []).forEach(L => { const p = L.map(c => [c[0] - OX, c[1] - OZ]); for (let i = 0; i + 1 < p.length; i++){ const [ax, az] = p[i], [bx, bz] = p[i + 1], l = Math.hypot(bx - ax, bz - az), nx = -(bz - az)/l*0.08, nz = (bx - ax)/l*0.08;
        [[ax - nx, az - nz], [bx - nx, bz - nz], [bx + nx, bz + nz], [ax - nx, az - nz], [bx + nx, bz + nz], [ax + nx, az + nz]].forEach(([x, z]) => { P.push(x, H(x, z) + 0.28, z); N.push(0, 1, 0); }); } });
      const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(P, 3)); g.setAttribute('normal', new T.Float32BufferAttribute(N, 3)); G.add(new T.Mesh(g, ymat)); }
    { const yh = canvasTex(128, 128, (c, w, h) => { c.fillStyle = '#6d6a66'; c.fillRect(0, 0, w, h); c.strokeStyle = '#e6c21a'; c.lineWidth = 7; for (let i = -128; i < 256; i += 36){ c.beginPath(); c.moveTo(i, 128); c.lineTo(i + 128, 0); c.stroke(); } });
      const ym2 = Lm({map: yh, side: T.DoubleSide, polygonOffset: true, polygonOffsetFactor: -6, polygonOffsetUnits: -8}); const tri2 = (polys, mat, y0, uvs) => polys.forEach(p => { const v = p.map(c => new T.Vector2(c[0] - OX, c[1] - OZ)); let tris; try { tris = T.ShapeUtils.triangulateShape(v, []); } catch (e){ return; } const P = [], N = [], U = [];
        tris.forEach(t => t.forEach(i => { const q = v[i]; P.push(q.x, H(q.x, q.y) + y0, q.y); N.push(0, 1, 0); U.push(q.x*uvs, q.y*uvs); })); const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(P, 3)); g.setAttribute('normal', new T.Float32BufferAttribute(N, 3)); g.setAttribute('uv', new T.Float32BufferAttribute(U, 2)); G.add(new T.Mesh(g, mat)); });
      tri2(CN.yhatch || [], ym2, 0.28, 1/3);
      // the hedge / flower strip inside the kerb of the mosque lawn: a low dark-green hedge with pink flowers
      const hdg = canvasTex(64, 64, (c, w, h) => { c.fillStyle = '#2f5e26'; c.fillRect(0, 0, w, h); for (let i = 0; i < 300; i++){ c.fillStyle = rnd() < 0.6 ? '#3f7a30' : (rnd() < 0.5 ? '#e37fa0' : '#f2f0e4'); c.fillRect(rnd()*w, rnd()*h, 2, 2); } });
      const hm2 = Lm({map: hdg}); (CN.hedges || []).forEach(p => { const v = p.map(c => [c[0] - OX, c[1] - OZ]); let tris; try { tris = T.ShapeUtils.triangulateShape(v.map(c => new T.Vector2(c[0], c[1])), []); } catch (e){ return; } const P = [], N = [], U = [];
        tris.forEach(t => t.forEach(i => { const q = v[i]; P.push(q[0], Ht(q[0], q[1]) + 0.42, q[1]); N.push(0, 1, 0); U.push(q[0]/2, q[1]/2); })); const g = new T.BufferGeometry(); g.setAttribute('position', new T.Float32BufferAttribute(P, 3)); g.setAttribute('normal', new T.Float32BufferAttribute(N, 3)); g.setAttribute('uv', new T.Float32BufferAttribute(U, 2)); G.add(new T.Mesh(g, hm2));
        ribbon(v, (x, z) => Ht(x, z), (x, z) => Ht(x, z) + 0.42, hm2, 1/2); }); }
    inst(urnGeo, vc, PT(CN.urnsRB || []).map(p => [p[0], p[1], 0, 1.2]), false);
    inst(pgeo, pmat, PT(CN.medPalms || []).map(p => [p[0], p[1], rnd()*6, 0.9]), true);
    const shrubGeo = mergeGeos([[0, 0, 1.1, 0x3f6f2c], [0.9, 0.3, 0.8, 0x4c7d34], [-0.8, 0.4, 0.85, 0x386428], [0.2, -0.9, 0.8, 0x47783a]].map(([dx, dz, rr, c]) => cg(new T.IcosahedronGeometry(rr, 1).scale(1, 0.7, 1), c, dx, rr*0.6, dz)));
    inst(shrubGeo, vc, PT(CN.medPalms || []).map(p => [p[0], p[1], rnd()*6, 1.3]), false);
    // white balustrade (corniche 105, by the mosque and the fish market): posts every 2.4 m, balusters between, a rail on top
    { const posts = [], bals = [], rails2 = []; (CN.balus || []).forEach(L => { const p = L.map(c => [c[0] - OX, c[1] - OZ]); for (let i = 0; i + 1 < p.length; i++){ const [ax, az] = p[i], [bx, bz] = p[i + 1], l = Math.hypot(bx - ax, bz - az), yaw = Math.atan2(bx - ax, bz - az); if (l < 0.2) continue;
          for (let d = 0; d < l; d += 2.4) posts.push([ax + (bx - ax)*d/l, az + (bz - az)*d/l, yaw]); for (let d = 0.3; d < l; d += 0.3) bals.push([ax + (bx - ax)*d/l, az + (bz - az)*d/l, yaw]); rails2.push([(ax + bx)/2, (az + bz)/2, yaw, l]); } });
      const wh = 0xf3f1ea; inst(mergeGeos([cg(new T.BoxGeometry(0.36, 0.92, 0.36), wh, 0, 0.46), cg(new T.BoxGeometry(0.44, 0.07, 0.44), wh, 0, 0.95)]), vc, posts, false);
      const blt = []; for (let i = 0; i <= 10; i++){ const t = i/10; blt.push(new T.Vector2(0.05 + Math.sin(t*PI)*0.06 + (t < 0.1 || t > 0.9 ? 0.03 : 0), t*0.66)); } inst(cg(new T.LatheGeometry(blt, 8), wh, 0, 0.12), vc, bals, false);
      const rg = new T.BoxGeometry(0.3, 0.1, 1), im = new T.InstancedMesh(rg, Lm({color: wh}), rails2.length*2); rails2.forEach((b, i) => [0.83, 0.08].forEach((hh, j) => { _e.set(0, b[2], 0); _q.setFromEuler(_e); _m.compose(_p.set(b[0], Ht(b[0], b[1]) + hh, b[1]), _q, _s.set(1, 1, b[3] + 0.05)); im.setMatrixAt(i*2 + j, _m); })); G.add(im); }
    // the second arcade building (SW corner of the roundabout): same style as the corniche mall
    (CN.swBlock || []).forEach(fp0 => { const fp = fp0.map(c => [c[0] - OX, c[1] - OZ]), base = Math.min(...fp.map(c => H(c[0], c[1])));
      const extr = (pp, y0, hh) => { const eg = new T.ExtrudeGeometry(new T.Shape(pp.map(c => new T.Vector2(c[0], -c[1]))), {depth: hh, bevelEnabled: false}); eg.rotateX(-PI/2); eg.translate(0, y0, 0); const ms = new T.Mesh(eg, creamM); ms.castShadow = ms.receiveShadow = true; G.add(ms); };
      extr(fp, base + 5.7, 6.9);
      const inner = fp.map(([x, z], i) => { let cx = 0, cz = 0; fp.forEach(c => { cx += c[0]; cz += c[1]; }); cx /= fp.length; cz /= fp.length; const dx = x - cx, dz = z - cz, l = Math.hypot(dx, dz) || 1; return [x - dx/l*3, z - dz/l*3]; });
      extr(inner, base, 5.8); const bt = bayTex.clone(); bt.needsUpdate = true; ribbon(fp, () => base, () => base + 12.6, Lm({map: bt, side: T.DoubleSide, alphaTest: 0.5}), 1/7.2);
      const st2 = shopTex.clone(); st2.needsUpdate = true; ribbon(inner, () => base + 0.3, () => base + 5.7, Lm({map: st2, side: T.DoubleSide}), 1/7.2);
      const mer = []; for (let i = 0; i + 1 < fp.length; i++){ const [ax, az] = fp[i], [bx, bz] = fp[i + 1], l = Math.hypot(bx - ax, bz - az), yaw = Math.atan2(bx - ax, bz - az); for (let d = 0; d < l; d += 1.6) mer.push([ax + (bx - ax)*d/l, az + (bz - az)*d/l, yaw, 1, base + 12.6]); }
      inst(cg(new T.BoxGeometry(0.7, 0.8, 0.35), 0xe6d8b8, 0, 0.4), vc, mer, false); });
    // green direction sign before the roundabout (as seen): Al Hisn Island / Al Eqd Al Fareed Rd / Daba Water Canal
    if (CN.dirSign){ const d = CN.dirSign, x = d.c[0] - OX, z = d.c[1] - OZ, y = Ht(x, z), g = new T.Group(); g.position.set(x, y, z); g.rotation.y = d.yaw; G.add(g);
      const tx = canvasTex(640, 320, (c, w, h) => { c.fillStyle = '#0d7a43'; c.fillRect(0, 0, w, h); c.strokeStyle = '#fff'; c.lineWidth = 8; c.strokeRect(8, 8, w - 16, h - 16);
        c.fillStyle = '#fff'; c.lineWidth = 16; c.beginPath(); c.arc(320, 92, 34, 0, PI*2); c.stroke(); c.beginPath(); c.moveTo(320, 300); c.lineTo(320, 126); c.stroke(); c.beginPath(); c.moveTo(286, 92); c.lineTo(230, 92); c.stroke(); c.beginPath(); c.moveTo(354, 92); c.lineTo(410, 92); c.stroke(); c.beginPath(); c.moveTo(320, 58); c.lineTo(320, 28); c.stroke();
        c.textAlign = 'center'; c.direction = 'rtl'; c.font = 'bold 34px Tajawal, Arial'; c.fillText('جزيرة الحصن', 130, 72); c.fillText('شارع العقد الفريد', 520, 72); c.fillText('قناة دبا المائية', 470, 236);
        c.direction = 'ltr'; c.font = 'bold 26px Arial'; c.fillText('Al Hisn Island', 130, 112); c.fillText('Al Eqd Al Fareed Rd', 520, 112); c.fillText('Daba Water Canal', 470, 274); });
      const bd = new T.Mesh(new T.PlaneGeometry(4.6, 2.3), Lm({map: tx})); bd.position.y = 2.9; g.add(bd); const bk = new T.Mesh(new T.PlaneGeometry(4.6, 2.3), Lm({color: 0x8e959a})); bk.position.set(0, 2.9, -0.03); bk.rotation.y = PI; g.add(bk);
      [-1.4, 0, 1.4].forEach(o => { const lg = new T.Mesh(new T.BoxGeometry(0.12, 4.0, 0.12), Lm({color: 0x9aa0a4})); lg.position.set(o, 2.0, -0.08); g.add(lg); }); }
    // roundabouts: S = flower beds; N = white urn monument, red beds and a green hedge; NE = lawn with round shade trees
    CN.rb.forEach(rb => { const x = rb.c[0] - OX, z = rb.c[1] - OZ, r = rb.r; const y = H(x, z) + 0.3;
      const dg = new T.RingGeometry(0.01, r, 72, 14); dg.rotateX(-PI/2); { const pa = dg.attributes.position; for (let i = 0; i < pa.count; i++){ const px = pa.getX(i) + x, pz = pa.getZ(i) + z; pa.setY(i, H(px, pz) + 0.3); } dg.computeVertexNormals(); }
      const disc = new T.Mesh(dg, Lm({map: grass})); disc.position.set(x, 0, z); disc.receiveShadow = true; G.add(disc);
      const ring = []; for (let k = 0; k <= 72; k++){ const a = k/72*PI*2; ring.push([x + Math.cos(a)*r, z + Math.sin(a)*r]); } ribbon(ring, (a, b) => H(a, b) - 0.05, (a, b) => H(a, b) + 0.31, kMatBY, 1);
      const bed = (rr, w, col) => { const g = new T.Mesh(new T.RingGeometry(rr - w/2, rr + w/2, 48), Lm({color: col})); g.rotation.x = -PI/2; g.position.set(x, y + 0.04, z); G.add(g); };
      if (rb.k === 'flowers'){ disc.material = Lm({map: starTex}); const um = Lm({color: 0xd8c6a2}), pad = new T.Mesh(new T.CylinderGeometry(7.5, 7.5, 0.25, 32), Lm({color: 0xe8e2d6})); pad.position.set(x, y + 0.12, z); G.add(pad);
        [[5.0, 0.45, 0.47], [4.0, 0.55, 0.97], [3.0, 1.1, 1.8]].forEach(([ww, hh, yy]) => { const t = new T.Mesh(new T.BoxGeometry(ww, hh, ww), um); t.position.set(x, y + yy, z); t.castShadow = true; G.add(t); });
        const prof = [[0.9, 0], [1.1, 0.25], [0.75, 0.5], [0.6, 1.2], [1.0, 1.9], [1.55, 2.6], [1.65, 3.2], [1.45, 3.8], [1.35, 4.3], [1.75, 4.55], [1.85, 4.85], [1.6, 4.95], [0.3, 5.0], [0.3, 5.1], [0.6, 5.3], [0.25, 5.6], [0.0, 6.0]].map(([r2, h2]) => new T.Vector2(r2, h2));
        const urn = new T.Mesh(new T.LatheGeometry(prof, 28), um); urn.position.set(x, y + 2.35, z); urn.castShadow = true; G.add(urn);
        const ch = canvasTex(256, 64, (c, w, h) => { c.fillStyle = '#fff'; c.fillRect(0, 0, w, h); c.fillStyle = '#d0202a'; for (let i = -1; i < 6; i++){ c.beginPath(); c.moveTo(i*48 + 6, 6); c.lineTo(i*48 + 30, 32); c.lineTo(i*48 + 6, 58); c.lineTo(i*48 + 24, 58); c.lineTo(i*48 + 48, 32); c.lineTo(i*48 + 24, 6); c.fill(); } c.strokeStyle = '#d0202a'; c.lineWidth = 4; c.strokeRect(2, 2, w - 4, h - 4); });
        (CN.splitSigns || []).filter(sg => sg.k === 'give').forEach(sg => { const ax = sg.c[0] - OX - x, az = sg.c[1] - OZ - z, L = Math.hypot(ax, az), px = x + ax/L*(r - 0.8), pz = z + az/L*(r - 0.8); const g = new T.Group(); g.position.set(px, y, pz); g.rotation.y = Math.atan2(ax, az); G.add(g);
          const bd = new T.Mesh(new T.PlaneGeometry(2.4, 0.6), Lm({map: ch, side: T.DoubleSide})); bd.position.y = 1.0; g.add(bd); [-0.9, 0.9].forEach(o => { const lg = new T.Mesh(new T.CylinderGeometry(0.04, 0.04, 1.3, 6), Lm({color: 0x9aa0a4})); lg.position.set(o, 0.65, -0.03); g.add(lg); }); }); }
      if (rb.k === 'urn'){   // as on the current map: a sand island being re-planted, six dark soil beds in rows, a round pad with the stone urn in the centre
        disc.material = Lm({map: sandTexC}); const soil = Lm({color: 0x6b5340});
        [[-7, -9, 10, 2.6], [-7, -4.5, 10, 2.6], [-7, 0, 10, 2.6], [4, 5, 8, 2.4], [4, 9, 8, 2.4], [-9, 6, 6, 2.4]].forEach(([dx, dz, w, d]) => { const bd2 = new T.Mesh(new T.BoxGeometry(w, 0.3, d), soil); bd2.position.set(x + dx, y + 0.1, z + dz); G.add(bd2); });
        const pad = new T.Mesh(new T.CylinderGeometry(4.5, 4.5, 0.3, 28), Lm({color: 0xe9e4da})); pad.position.set(x, y + 0.15, z); G.add(pad);
        const up = []; for (let i = 0; i <= 16; i++){ const t = i/16; up.push(new T.Vector2(0.6 + Math.sin(t*PI*0.9)*1.2 + (t > 0.85 ? 0.5 : 0), t*3.4)); }
        const urn = new T.Mesh(new T.LatheGeometry(up, 20), Lm({color: 0xf7f6f1})); urn.position.set(x, y + 1.2, z); urn.castShadow = true; G.add(urn); const ped = new T.Mesh(new T.CylinderGeometry(1.4, 1.7, 1.2, 16), Lm({color: 0xefece4})); ped.position.set(x, y + 0.6, z); G.add(ped); }
      if (rb.k === 'trees'){ bed(r*0.5, 2.0, 0xc8323a); const tl = []; for (let k = 0; k < 5; k++){ const a = k/5*PI*2 + 0.3; tl.push([x + Math.cos(a)*r*0.62, z + Math.sin(a)*r*0.62, 0, 1, y]); } tl.push([x, z, 0, 1.1, y]); inst(ficusGeo, vc, tl, true); } });
    // road signs (as seen in the drive-through)
    const signFace = {
      s60: () => canvasTex(128, 128, (c, w, h) => { c.fillStyle = '#fff'; c.beginPath(); c.arc(64, 64, 62, 0, PI*2); c.fill(); c.strokeStyle = '#d0202a'; c.lineWidth = 14; c.beginPath(); c.arc(64, 64, 55, 0, PI*2); c.stroke(); c.fillStyle = '#111'; c.font = 'bold 52px Arial'; c.textAlign = 'center'; c.textBaseline = 'middle'; c.fillText('60', 64, 68); }),
      s40: () => canvasTex(128, 128, (c, w, h) => { c.fillStyle = '#fff'; c.beginPath(); c.arc(64, 64, 62, 0, PI*2); c.fill(); c.strokeStyle = '#d0202a'; c.lineWidth = 14; c.beginPath(); c.arc(64, 64, 55, 0, PI*2); c.stroke(); c.fillStyle = '#111'; c.font = 'bold 34px Arial'; c.textAlign = 'center'; c.textBaseline = 'middle'; c.fillText('٤٠', 64, 46); c.fillText('40', 64, 84); }),
      tri: (draw) => () => canvasTex(128, 128, (c, w, h) => { c.fillStyle = '#fff'; c.beginPath(); c.moveTo(64, 6); c.lineTo(122, 116); c.lineTo(6, 116); c.closePath(); c.fill(); c.strokeStyle = '#d0202a'; c.lineWidth = 12; c.stroke(); c.fillStyle = '#111'; draw(c); }),
      give: () => canvasTex(128, 128, (c, w, h) => { c.fillStyle = '#fff'; c.beginPath(); c.moveTo(6, 10); c.lineTo(122, 10); c.lineTo(64, 120); c.closePath(); c.fill(); c.strokeStyle = '#d0202a'; c.lineWidth = 13; c.stroke(); }) };
    signFace.keep = () => canvasTex(128, 128, (c, w, h) => { c.fillStyle = '#1f5fb5'; c.beginPath(); c.arc(64, 64, 60, 0, PI*2); c.fill(); c.strokeStyle = '#fff'; c.lineWidth = 6; c.stroke(); c.fillStyle = '#fff'; c.beginPath(); c.moveTo(40, 40); c.lineTo(84, 84); c.lineTo(92, 64); c.lineTo(96, 100); c.lineTo(60, 96); c.lineTo(78, 88); c.lineTo(34, 46); c.closePath(); c.fill(); });
    signFace.two = signFace.tri(c => { c.fillRect(46, 50, 8, 50); c.fillRect(74, 50, 8, 50); c.beginPath(); c.moveTo(50, 40); c.lineTo(40, 58); c.lineTo(60, 58); c.fill(); c.beginPath(); c.moveTo(78, 108); c.lineTo(68, 90); c.lineTo(88, 90); c.fill(); });
    signFace.bump = signFace.tri(c => { c.beginPath(); c.moveTo(30, 100); c.quadraticCurveTo(64, 50, 98, 100); c.fill(); });
    signFace.ped = signFace.tri(c => { c.beginPath(); c.arc(64, 50, 8, 0, PI*2); c.fill(); c.fillRect(59, 58, 10, 26); c.fillRect(52, 82, 7, 22); c.fillRect(70, 82, 7, 22); c.fillRect(46, 64, 36, 6); });
    signFace.kids = signFace.tri(c => { c.beginPath(); c.arc(50, 52, 7, 0, PI*2); c.arc(80, 58, 6, 0, PI*2); c.fill(); c.fillRect(46, 60, 9, 24); c.fillRect(76, 65, 8, 20); c.fillRect(44, 84, 5, 18); c.fillRect(52, 84, 5, 18); c.fillRect(76, 85, 4, 16); c.fillRect(81, 85, 4, 16); });
    const sCache = {}; const poleM = Lm({color: 0x9aa0a4}), backM = Lm({color: 0xb5bbbf});
    CN.signs.concat(CN.splitSigns || []).forEach(s => { const f = signFace[s.k]; if (!f) return; const x = s.c[0] - OX, z = s.c[1] - OZ, y = Ht(x, z), g = new T.Group(); g.position.set(x, y, z); g.rotation.y = s.yaw; G.add(g);
      const p = new T.Mesh(new T.CylinderGeometry(0.045, 0.05, 2.9, 6), poleM); p.position.y = 1.45; g.add(p);
      const m = sCache[s.k] || (sCache[s.k] = Lm({map: f(), transparent: true, alphaTest: 0.5})); const pl = new T.Mesh(new T.PlaneGeometry(0.9, 0.9), m); pl.position.set(0, 2.6, 0.06); g.add(pl);
      const bk = new T.Mesh(new T.CircleGeometry(0.42, 16), backM); bk.position.set(0, 2.6, 0.04); bk.rotation.y = PI; g.add(bk); });
    // zebra crossings: red base with white bars across both carriageways; pedestrian signals where they are
    CN.cross.forEach(c => { const x = c.c[0] - OX, z = c.c[1] - OZ, g = new T.Group(); g.position.set(x, H(x, z) + 0.2, z); g.rotation.y = c.yaw; G.add(g);
      const zt = canvasTex(64, 256, (cx, w, h) => { cx.fillStyle = '#b5413a'; cx.fillRect(0, 0, w, h); cx.fillStyle = '#f4f2ec'; for (let i = 0; i < h; i += 32) cx.fillRect(0, i + 4, w, 16); }); zt.repeat.set(1, c.w/8);
      const zb = new T.Mesh(new T.PlaneGeometry(4, c.w), Lm({map: zt, polygonOffset: true, polygonOffsetFactor: -6, polygonOffsetUnits: -8})); zb.rotation.x = -PI/2; zb.rotation.z = PI/2; g.add(zb);
      if (c.sig) [-1, 1].forEach(sd => { const pg = new T.Group(); pg.position.set(sd*(c.w/2 + 0.6), 0, 0); g.add(pg); const p = new T.Mesh(new T.CylinderGeometry(0.08, 0.09, 3.6, 8), Lm({color: 0x8e9498})); p.position.y = 1.8; pg.add(p);
        const hd = new T.Mesh(new T.BoxGeometry(0.5, 1.4, 0.36), Lm({color: 0x1f2326})); hd.position.y = 3.2; pg.add(hd); const bb = new T.Mesh(new T.BoxGeometry(0.9, 1.8, 0.04), Lm({color: 0xe8c21a})); bb.position.set(0, 3.2, -sd*0.2); pg.add(bb); const sol = new T.Mesh(new T.BoxGeometry(0.9, 0.05, 0.6), Lm({color: 0x1a2a4a})); sol.position.set(0, 4.25, 0); sol.rotation.x = 0.4; pg.add(sol); [[0x7a1210, 3.6], [0x6a5010, 3.2], [0x1fbf4a, 2.8]].forEach(([col, hh]) => { const l = new T.Mesh(new T.CircleGeometry(0.13, 12), Lm({color: col, emissive: hh < 3 ? 0x0a5020 : 0})); l.position.set(0, hh, sd*0.17); l.rotation.y = sd > 0 ? 0 : PI; pg.add(l); }); }); });
  }

  return {H, Hy, Hc, palms: allPalms, palmTilt, at, shoreDist, shoreDistL, colorAt, inBld, rayWalls, blockedWall, terrainMat, DX, DZ, R, labels, X0, Z0, X1, Z1, SW, SH, roads, blds: BLD_LIST, greens, wadis, pois, SEG, DOORS, pushWalls, blocked, paintMap, update, setRange,
    sea: {m: seaNear, far: seaFar, mat: seaMat}, root, inPoly, nearRoad, roadTop, roads2: RD, plotsAdded: () => plotsAdded, bridges: () => BRIDGES.map(b => ({n: b.r.n, h: b.r.h, A: b.A, B: b.B, deck: b.deck, x: b.S[0].x, z: b.S[0].z})), stats: () => ({plots: plotsAdded, bridges: BRIDGES.length, lamps: lampPts.length, chunks: chunks.length, base: baseChunks.length, det: detList.length, roads: roadChunks.length, palms: allPalms.length, segs: SEG.length, doors: DOORS.length})};
};
