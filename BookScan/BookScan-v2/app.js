'use strict';
/* BookScan v2: point at an open book, turn pages, get a searchable PDF. Everything runs on the device. */
const VERSION = '2.0';
const $ = (s) => document.querySelector(s);
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const BASE = new URL('./', location.href).href;

/* ---------- settings ---------- */
const DEF = { mode: 'spread', clean: 'strong', sens: 1, hold: 800, hires: false, sound: true, diag: true };
let S = { ...DEF };
try { S = { ...DEF, ...JSON.parse(localStorage.getItem('bs.settings2') || '{}') }; } catch (e) {}
const saveS = () => { try { localStorage.setItem('bs.settings2', JSON.stringify(S)); } catch (e) {} };

/* ---------- storage ---------- */
let db;
function openDB() {
  return new Promise((res, rej) => {
    const r = indexedDB.open('bookscan', 1);
    r.onupgradeneeded = () => {
      const d = r.result;
      d.createObjectStore('books', { keyPath: 'id' });
      d.createObjectStore('pages', { keyPath: 'id' }).createIndex('bookId', 'bookId');
    };
    r.onsuccess = () => res(r.result);
    r.onerror = () => rej(r.error);
  });
}
const tx = (store, mode, fn) => new Promise((res, rej) => {
  const t = db.transaction(store, mode);
  const out = fn(t.objectStore(store));
  t.oncomplete = () => res(out && out.result !== undefined ? out.result : undefined);
  t.onerror = () => rej(t.error);
});
const dbPut = (s, v) => tx(s, 'readwrite', (o) => o.put(v));
const dbDel = (s, k) => tx(s, 'readwrite', (o) => o.delete(k));
const dbAll = (s) => tx(s, 'readonly', (o) => o.getAll());
const dbPagesOf = (id) => tx('pages', 'readonly', (o) => o.index('bookId').getAll(id));
const dbCount = (id) => tx('pages', 'readonly', (o) => o.index('bookId').count(id));
const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 6);

/* ---------- state ---------- */
let book = null, pages = [];
const urls = new Map();
let running = false, busy = false, inScan = false, stream = null, track = null, wakeLock = null;
let pagesVer = 0;

/* ---------- canvas / image helpers ---------- */
function mkCanvas(w, h) { const c = document.createElement('canvas'); c.width = w; c.height = h; return c; }
const srcW = (s) => s.videoWidth || s.width;
const srcH = (s) => s.videoHeight || s.height;
/* area-style downscale: halve repeatedly so thin text and sensor noise average out instead of aliasing */
function downTo(src, w) {
  let cw = srcW(src), ch = srcH(src), cur = src;
  while (cw > w) {
    const nw = Math.max(w, Math.round(cw / 2)), nh = Math.max(1, Math.round(ch * nw / cw));
    const c = mkCanvas(nw, nh), x = c.getContext('2d', { willReadFrequently: true });
    x.imageSmoothingEnabled = true; x.imageSmoothingQuality = 'high'; x.drawImage(cur, 0, 0, nw, nh);
    cur = c; cw = nw; ch = nh;
  }
  return cur;
}
function grayOf(src, w) {
  const c = downTo(src, w), x = c.getContext('2d', { willReadFrequently: true }), cw = c.width, h = c.height;
  const d = x.getImageData(0, 0, cw, h).data, g = new Float32Array(cw * h);
  for (let i = 0, j = 0; i < d.length; i += 4, j++) g[j] = d[i] * 0.299 + d[i + 1] * 0.587 + d[i + 2] * 0.114;
  return { g, w: cw, h };
}
function boxBlur(g, w, h, r) {
  const t = new Float32Array(g.length), o = new Float32Array(g.length), k = 2 * r + 1;
  for (let y = 0; y < h; y++) {
    let s = 0; const row = y * w;
    for (let x = -r; x <= r; x++) s += g[row + Math.min(w - 1, Math.max(0, x))];
    for (let x = 0; x < w; x++) {
      t[row + x] = s / k;
      s += g[row + Math.min(w - 1, x + r + 1)] - g[row + Math.max(0, x - r)];
    }
  }
  for (let x = 0; x < w; x++) {
    let s = 0;
    for (let y = -r; y <= r; y++) s += t[Math.min(h - 1, Math.max(0, y)) * w + x];
    for (let y = 0; y < h; y++) {
      o[y * w + x] = s / k;
      s += t[Math.min(h - 1, y + r + 1) * w + x] - t[Math.max(0, y - r) * w + x];
    }
  }
  return o;
}
/* sharpness (variance of Laplacian) over the central 70% of the frame */
function sharpness(src, W = 480) {
  const full = grayOf(src, W), { g, w, h } = full;
  const x0 = Math.floor(w * 0.15), x1 = Math.floor(w * 0.85), y0 = Math.floor(h * 0.15), y1 = Math.floor(h * 0.85);
  let s = 0, s2 = 0, n = 0;
  for (let y = y0 + 1; y < y1 - 1; y++) for (let x = x0 + 1; x < x1 - 1; x++) {
    const i = y * w + x, l = 4 * g[i] - g[i - 1] - g[i + 1] - g[i - w] - g[i + w];
    s += l; s2 += l * l; n++;
  }
  const m = s / n; return s2 / n - m * m;
}

/* ---------- book / page detection ---------- */
function otsu(vals) {
  const hist = new Float64Array(256); for (let i = 0; i < vals.length; i++) hist[Math.max(0, Math.min(255, vals[i] | 0))]++;
  const total = vals.length; let sum = 0; for (let i = 0; i < 256; i++) sum += i * hist[i];
  let sB = 0, wB = 0, best = 0, T = 128;
  for (let t = 0; t < 256; t++) {
    wB += hist[t]; if (!wB) continue; const wF = total - wB; if (!wF) break;
    sB += t * hist[t]; const mB = sB / wB, mF = (sum - sB) / wF, v = wB * wF * (mB - mF) * (mB - mF);
    if (v > best) { best = v; T = t; }
  }
  return T;
}
/* Returns normalized {tl,tr,br,bl,gt,gb} (0..1) for the bright paper area of an open book, or null. */
function detectPaper(src, W) {
  const { g, w, h } = grayOf(src, W);
  const b = boxBlur(g, w, h, Math.max(2, Math.round(w / 40)));
  const T = otsu(b), N = w * h;
  const mask = new Uint8Array(N); for (let i = 0; i < N; i++) mask[i] = b[i] > T ? 1 : 0;
  const lab = new Int32Array(N), stack = new Int32Array(N);
  let best = 0, bestSize = 0, nl = 0;
  for (let i = 0; i < N; i++) {
    if (!mask[i] || lab[i]) continue;
    nl++; let sp = 0, size = 0; stack[sp++] = i; lab[i] = nl;
    while (sp) {
      const p = stack[--sp]; size++; const x = p % w, y = (p / w) | 0;
      if (x > 0 && mask[p - 1] && !lab[p - 1]) { lab[p - 1] = nl; stack[sp++] = p - 1; }
      if (x < w - 1 && mask[p + 1] && !lab[p + 1]) { lab[p + 1] = nl; stack[sp++] = p + 1; }
      if (y > 0 && mask[p - w] && !lab[p - w]) { lab[p - w] = nl; stack[sp++] = p - w; }
      if (y < h - 1 && mask[p + w] && !lab[p + w]) { lab[p + w] = nl; stack[sp++] = p + w; }
    }
    if (size > bestSize) { bestSize = size; best = nl; }
  }
  if (bestSize < 0.12 * N || bestSize > 0.97 * N) return null;
  const comp = new Uint8Array(N); for (let i = 0; i < N; i++) comp[i] = lab[i] === best ? 1 : 0;
  // fill holes (ink, shadows) by flooding the outside
  const out = new Uint8Array(N); let sp = 0;
  const seed = (p) => { if (!comp[p] && !out[p]) { out[p] = 1; stack[sp++] = p; } };
  for (let x = 0; x < w; x++) { seed(x); seed((h - 1) * w + x); }
  for (let y = 0; y < h; y++) { seed(y * w); seed(y * w + w - 1); }
  while (sp) {
    const p = stack[--sp], x = p % w, y = (p / w) | 0;
    if (x > 0) seed(p - 1); if (x < w - 1) seed(p + 1); if (y > 0) seed(p - w); if (y < h - 1) seed(p + w);
  }
  for (let i = 0; i < N; i++) if (!out[i]) comp[i] = 1;
  let minx = w, maxx = 0, miny = h, maxy = 0;
  const top = new Int32Array(w).fill(-1), bot = new Int32Array(w).fill(-1);
  const lft = new Int32Array(h).fill(-1), rgt = new Int32Array(h).fill(-1);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    if (!comp[y * w + x]) continue;
    if (x < minx) minx = x; if (x > maxx) maxx = x; if (y < miny) miny = y; if (y > maxy) maxy = y;
    if (top[x] < 0) top[x] = y; bot[x] = y;
    if (lft[y] < 0) lft[y] = x; rgt[y] = x;
  }
  const bw = maxx - minx, bh = maxy - miny;
  if (bw < w * 0.25 || bh < h * 0.25) return null;
  const band = (yA, yB) => {
    yA = Math.round(yA); yB = Math.round(yB);
    const xa = Math.round(minx + 0.33 * bw), xb = Math.round(minx + 0.67 * bw);
    const col = new Float32Array(w);
    for (let x = 0; x < w; x++) { let s = 0, n = 0; for (let y = yA; y < yB; y++) { s += g[y * w + x]; n++; } col[x] = n ? s / n : 0; }
    const sm = boxBlur(col, w, 1, 1);
    const k0 = Math.max(3, Math.round(bw * 0.04)), k1 = Math.max(k0 + 3, Math.round(bw * 0.10));
    let bx = -1, bs = -1e9;
    for (let x = xa; x <= xb; x++) {
      let l = 0, r = 0, n = 0;
      for (let k = k0; k <= k1; k++) if (x - k >= 0 && x + k < w) { l += sm[x - k]; r += sm[x + k]; n++; }
      if (!n) continue; const sc = (l + r) / (2 * n) - sm[x];
      if (sc > bs) { bs = sc; bx = x; }
    }
    return bs > 3 ? bx : null;
  };
  const yTm = miny + 0.285 * bh, yBm = miny + 0.715 * bh;
  let xt = band(miny + 0.12 * bh, miny + 0.45 * bh), xb = band(miny + 0.55 * bh, miny + 0.88 * bh);
  const xmid = minx + bw / 2;
  if (xt === null && xb === null) { xt = xb = xmid; } else if (xt === null) xt = xb; else if (xb === null) xb = xt;
  if (Math.abs(xt - xb) > 0.12 * bw) { xt = xb = (xt + xb) / 2; }
  // straight edge lines, fitted robustly to the mask boundary (corners of a blurred mask are rounded, lines are not)
  const fit = (pts) => {
    let use = pts, a = 0, b = 0;
    for (let it = 0; it < 3; it++) {
      const n = use.length; if (n < 6) return null;
      let su = 0, sv = 0, suu = 0, suv = 0; for (const p of use) { su += p[0]; sv += p[1]; suu += p[0] * p[0]; suv += p[0] * p[1]; }
      const den = n * suu - su * su; if (Math.abs(den) < 1e-9) return null;
      b = (n * suv - su * sv) / den; a = (sv - b * su) / n;
      const res = use.map((p) => Math.abs(p[1] - (a + b * p[0]))).sort((x, y) => x - y), lim = Math.max(1.2, 3 * res[Math.floor(n / 2)]);
      use = use.filter((p) => Math.abs(p[1] - (a + b * p[0])) <= lim);
    }
    return { a, b };
  };
  const colsPts = (arr, x0, x1) => { const o = []; for (let x = Math.max(0, Math.ceil(x0)); x <= Math.min(w - 1, Math.floor(x1)); x++) if (arr[x] >= 0) o.push([x, arr[x]]); return o; };
  const rowsPts = (arr, y0, y1) => { const o = []; for (let y = Math.max(0, Math.ceil(y0)); y <= Math.min(h - 1, Math.floor(y1)); y++) if (arr[y] >= 0) o.push([y, arr[y]]); return o; };
  const gm = 0.10 * bw, em = 0.04 * bw;
  const Ltop = fit(colsPts(top, minx + em, xt - gm)), Rtop = fit(colsPts(top, xt + gm, maxx - em));
  const Lbot = fit(colsPts(bot, minx + em, xb - gm)), Rbot = fit(colsPts(bot, xb + gm, maxx - em));
  const Wtop = fit(colsPts(top, minx + em, maxx - em)), Wbot = fit(colsPts(bot, minx + em, maxx - em));
  const Ledge = fit(rowsPts(lft, miny + 0.1 * bh, maxy - 0.1 * bh)), Redge = fit(rowsPts(rgt, miny + 0.1 * bh, maxy - 0.1 * bh));
  if (!Wtop || !Wbot || !Ledge || !Redge) return null;
  const bg2 = (xb - xt) / (yBm - yTm), ag = xt - bg2 * yTm; // gutter line x = ag + bg2*y
  const HV = (H, V) => { const x = (V.a + V.b * H.a) / (1 - V.b * H.b); return [x, H.a + H.b * x]; };
  const G = { a: ag, b: bg2 };
  const nz = (p) => [p[0] / w, p[1] / h];
  const whole = [HV(Wtop, Ledge), HV(Wtop, Redge), HV(Wbot, Redge), HV(Wbot, Ledge)].map(nz);
  let L = null, R = null;
  if (Ltop && Rtop && Lbot && Rbot) {
    L = [HV(Ltop, Ledge), HV(Ltop, G), HV(Lbot, G), HV(Lbot, Ledge)].map(nz);
    R = [HV(Rtop, G), HV(Rtop, Redge), HV(Rbot, Redge), HV(Rbot, G)].map(nz);
  } else {
    const gt = [ag + bg2 * miny, miny], gb2 = [ag + bg2 * maxy, maxy];
    L = [whole[0].map((v, i) => v * (i ? h : w)), gt, gb2, whole[3].map((v, i) => v * (i ? h : w))].map(nz);
    R = [gt, whole[1].map((v, i) => v * (i ? h : w)), whole[2].map((v, i) => v * (i ? h : w)), gb2].map(nz);
  }
  const ok = (q) => q.every((p) => isFinite(p[0]) && isFinite(p[1]));
  if (!ok(whole) || !ok(L) || !ok(R)) return null;
  return { whole, L, R };
}

/* ---------- warp (perspective flatten) ---------- */
function warpQuad(src, q, maxLong) {
  const [p0, p1, p2, p3] = q;
  const dist = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1]);
  let ow = Math.max(dist(p0, p1), dist(p3, p2)), oh = Math.max(dist(p0, p3), dist(p1, p2));
  const k = Math.min(1, maxLong / Math.max(ow, oh)); ow = Math.max(8, Math.round(ow * k)); oh = Math.max(8, Math.round(oh * k));
  const sw = src.width, sh = src.height;
  const sd = src.getContext('2d', { willReadFrequently: true }).getImageData(0, 0, sw, sh).data;
  const [x0, y0] = p0, [x1, y1] = p1, [x2, y2] = p2, [x3, y3] = p3;
  const dx1 = x1 - x2, dx2 = x3 - x2, dx3 = x0 - x1 + x2 - x3, dy1 = y1 - y2, dy2 = y3 - y2, dy3 = y0 - y1 + y2 - y3;
  let A, B, C, D, E, F, G = 0, H = 0;
  if (Math.abs(dx3) < 1e-9 && Math.abs(dy3) < 1e-9) { A = x1 - x0; B = x3 - x0; C = x0; D = y1 - y0; E = y3 - y0; F = y0; }
  else {
    const den = dx1 * dy2 - dx2 * dy1;
    G = (dx3 * dy2 - dx2 * dy3) / den; H = (dx1 * dy3 - dx3 * dy1) / den;
    A = x1 - x0 + G * x1; B = x3 - x0 + H * x3; C = x0; D = y1 - y0 + G * y1; E = y3 - y0 + H * y3; F = y0;
  }
  const out = mkCanvas(ow, oh), ox = out.getContext('2d'), id = ox.createImageData(ow, oh), od = id.data;
  for (let y = 0; y < oh; y++) {
    const v = y / (oh - 1);
    for (let x = 0; x < ow; x++) {
      const u = x / (ow - 1), den = G * u + H * v + 1;
      let sx = (A * u + B * v + C) / den, sy = (D * u + E * v + F) / den;
      sx = sx < 0 ? 0 : sx > sw - 1.001 ? sw - 1.001 : sx; sy = sy < 0 ? 0 : sy > sh - 1.001 ? sh - 1.001 : sy;
      const ix = sx | 0, iy = sy | 0, fx = sx - ix, fy = sy - iy, i = (iy * sw + ix) * 4, j = i + sw * 4, o = (y * ow + x) * 4;
      const w00 = (1 - fx) * (1 - fy), w10 = fx * (1 - fy), w01 = (1 - fx) * fy, w11 = fx * fy;
      od[o] = sd[i] * w00 + sd[i + 4] * w10 + sd[j] * w01 + sd[j + 4] * w11;
      od[o + 1] = sd[i + 1] * w00 + sd[i + 5] * w10 + sd[j + 1] * w01 + sd[j + 5] * w11;
      od[o + 2] = sd[i + 2] * w00 + sd[i + 6] * w10 + sd[j + 2] * w01 + sd[j + 6] * w11;
      od[o + 3] = 255;
    }
  }
  ox.putImageData(id, 0, 0);
  return out;
}
function inset(q, f) {
  const cx = q.reduce((s, p) => s + p[0], 0) / 4, cy = q.reduce((s, p) => s + p[1], 0) / 4;
  return q.map((p) => [p[0] + (cx - p[0]) * f, p[1] + (cy - p[1]) * f]);
}

/* ---------- clean-up: flatten shadows, sharpen, push to black on white ---------- */
function enhance(src, level) {
  if (level === 'off') return src;
  const w = src.width, h = src.height, ctx = src.getContext('2d', { willReadFrequently: true });
  const img = ctx.getImageData(0, 0, w, h), d = img.data;
  const B = Math.max(8, Math.round(w / 60)), sw = Math.max(2, Math.ceil(w / B)), sh = Math.max(2, Math.ceil(h / B));
  let small = new Float32Array(sw * sh); const cnt = new Float32Array(sw * sh);
  let gray = new Float32Array(w * h);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const i = (y * w + x) * 4, v = d[i] * 0.299 + d[i + 1] * 0.587 + d[i + 2] * 0.114;
    gray[y * w + x] = v;
    const k = Math.min(sh - 1, (y / B) | 0) * sw + Math.min(sw - 1, (x / B) | 0);
    small[k] += v; cnt[k]++;
  }
  for (let k = 0; k < small.length; k++) small[k] /= cnt[k] || 1;
  const passes = 3;
  for (let p = 0; p < passes; p++) {
    const o = new Float32Array(small.length);
    for (let y = 0; y < sh; y++) for (let x = 0; x < sw; x++) {
      let m = 0;
      for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
        const yy = y + dy, xx = x + dx;
        if (yy >= 0 && yy < sh && xx >= 0 && xx < sw) m = Math.max(m, small[yy * sw + xx]);
      }
      o[y * sw + x] = m;
    }
    small = o;
  }
  small = boxBlur(small, sw, sh, 1);
  const sc = mkCanvas(sw, sh), sx = sc.getContext('2d'), sd = sx.createImageData(sw, sh);
  for (let k = 0; k < small.length; k++) { const v = small[k]; sd.data[k * 4] = sd.data[k * 4 + 1] = sd.data[k * 4 + 2] = v; sd.data[k * 4 + 3] = 255; }
  sx.putImageData(sd, 0, 0);
  const bc = mkCanvas(w, h), bx = bc.getContext('2d', { willReadFrequently: true });
  bx.imageSmoothingEnabled = true; bx.imageSmoothingQuality = 'high'; bx.drawImage(sc, 0, 0, w, h);
  const bd = bx.getImageData(0, 0, w, h).data;
  for (let p = 0; p < w * h; p++) gray[p] = Math.min(255, (gray[p] / Math.max(60, bd[p * 4])) * 255);
  const bl = boxBlur(gray, w, h, 2);
  const lo = level === 'strong' ? 95 : 60, hi = level === 'strong' ? 190 : 225, amt = level === 'strong' ? 1.6 : 1.0;
  for (let p = 0; p < w * h; p++) {
    let v = gray[p] + amt * (gray[p] - bl[p]);
    v = (v - lo) * 255 / (hi - lo); v = v < 0 ? 0 : v > 255 ? 255 : v;
    d[p * 4] = d[p * 4 + 1] = d[p * 4 + 2] = v; d[p * 4 + 3] = 255;
  }
  ctx.putImageData(img, 0, 0);
  return src;
}
/* Crop to the printed area with a margin; leave alone if the page is mostly blank. */
function inkCrop(c) {
  const W = Math.min(c.width, 500), { g, w, h } = grayOf(c, W);
  const bm = Math.round(Math.min(w, h) * 0.02);
  const rows = new Int32Array(h), cols = new Int32Array(w);
  for (let y = bm; y < h - bm; y++) for (let x = bm; x < w - bm; x++) if (g[y * w + x] < 110) { rows[y]++; cols[x]++; }
  const rt = Math.max(2, w * 0.006), ct = Math.max(2, h * 0.006);
  let y0 = 0, y1 = h - 1, x0 = 0, x1 = w - 1;
  while (y0 < h && rows[y0] < rt) y0++; while (y1 > y0 && rows[y1] < rt) y1--;
  while (x0 < w && cols[x0] < ct) x0++; while (x1 > x0 && cols[x1] < ct) x1--;
  if (x1 - x0 < w * 0.35 || y1 - y0 < h * 0.25) return c;
  const m = Math.round(Math.min(w, h) * 0.035);
  x0 = Math.max(0, x0 - m); y0 = Math.max(0, y0 - m); x1 = Math.min(w - 1, x1 + m); y1 = Math.min(h - 1, y1 + m);
  const k = c.width / w, o = mkCanvas(Math.round((x1 - x0) * k), Math.round((y1 - y0) * k));
  o.getContext('2d').drawImage(c, x0 * k, y0 * k, o.width, o.height, 0, 0, o.width, o.height);
  return o;
}
function toJpeg(c) {
  return new Promise((r) => c.toBlob((b) => r({ blob: b, w: c.width, h: c.height }), 'image/jpeg', 0.85));
}

/* ---------- camera ---------- */
const video = $('#cam');
async function openCamera() {
  if (stream) return;
  const tries = [
    { facingMode: { ideal: 'environment' }, width: { ideal: 4032 }, height: { ideal: 3024 } },
    { facingMode: { ideal: 'environment' }, width: { ideal: 1920 }, height: { ideal: 1080 } },
    { facingMode: { ideal: 'environment' } },
  ];
  let err;
  for (const v of tries) {
    try { stream = await navigator.mediaDevices.getUserMedia({ video: v, audio: false }); break; } catch (e) { err = e; if (e && e.name === 'NotAllowedError') break; }
  }
  if (!stream) throw err || new Error('No camera');
  video.srcObject = stream; track = stream.getVideoTracks()[0];
  try {
    const caps = track.getCapabilities ? track.getCapabilities() : {};
    const adv = {};
    for (const k of ['focusMode', 'exposureMode', 'whiteBalanceMode']) if (caps[k] && caps[k].includes('continuous')) adv[k] = 'continuous';
    if (Object.keys(adv).length) await track.applyConstraints({ advanced: [adv] });
  } catch (e) {}
  await video.play().catch(() => {});
  await new Promise((r) => { if (video.videoWidth) r(); else video.onloadedmetadata = () => r(); });
}
function closeCamera() {
  if (stream) stream.getTracks().forEach((t) => t.stop());
  stream = null; track = null; video.srcObject = null;
}
async function refocus(x, y) {
  if (!track || !track.getCapabilities) return;
  try {
    const caps = track.getCapabilities();
    if (caps.focusMode && caps.focusMode.includes('single-shot')) {
      const adv = { focusMode: 'single-shot' };
      if (x !== undefined && caps.pointsOfInterest !== undefined) adv.pointsOfInterest = [{ x, y }];
      await track.applyConstraints({ advanced: [adv] });
      await sleep(500);
      if (caps.focusMode.includes('continuous')) await track.applyConstraints({ advanced: [{ focusMode: 'continuous' }] });
    }
  } catch (e) {}
}
$('#scan').addEventListener('click', (e) => {
  if (e.target.closest('button,.sheet')) return;
  const r = video.getBoundingClientRect(); refocus((e.clientX - r.left) / r.width, (e.clientY - r.top) / r.height);
});

async function grabBest() {
  if (S.hires && window.ImageCapture && track) {
    try {
      const bmp = await createImageBitmap(await new ImageCapture(track).takePhoto());
      const c = mkCanvas(bmp.width, bmp.height); c.getContext('2d').drawImage(bmp, 0, 0); return c;
    } catch (e) {}
  }
  let best = null, bs = -1;
  for (let i = 0; i < 5; i++) {
    const c = mkCanvas(video.videoWidth, video.videoHeight); c.getContext('2d').drawImage(video, 0, 0);
    const s = sharpness(c, 480);
    if (s > bs) { best = c; bs = s; }
    if (i < 4) await sleep(110);
  }
  return best;
}

/* ---------- OCR ---------- */
let worker = null, ocrReady = null, ocrBusy = false;
const ocrQueue = [];
function initOCR() {
  if (ocrReady) return ocrReady;
  ocrReady = (async () => {
    worker = await Tesseract.createWorker('eng', 1, {
      workerPath: BASE + 'lib/worker.min.js', corePath: BASE + 'lib/', langPath: BASE + 'lib/lang',
      workerBlobURL: false, cacheMethod: 'none', gzip: true,
    });
  })();
  return ocrReady;
}
function enqueueOCR(p) { if (!ocrQueue.includes(p.id)) ocrQueue.push(p.id); pump(); }
async function pump() {
  if (ocrBusy) return; ocrBusy = true;
  try {
    await initOCR();
    while (ocrQueue.length) {
      const id = ocrQueue.shift(), p = pages.find((x) => x.id === id);
      if (!p || p.ocr === 'done') continue;
      renderOcrState();
      try {
        const { data } = await worker.recognize(p.blob);
        p.lines = (data.lines || []).map((l) => ({ t: l.text.replace(/\s+/g, ' ').trim(), x0: l.bbox.x0, y0: l.bbox.y0, x1: l.bbox.x1, y1: l.bbox.y1 })).filter((l) => l.t);
        p.text = data.text || ''; p.ocr = 'done';
      } catch (e) { console.error(e); p.ocr = 'error'; }
      await dbPut('pages', p); pagesVer++; renderThumbs(); renderOcrState();
    }
  } catch (e) { console.error(e); $('#ocrState').textContent = 'Text recognition failed to start'; }
  ocrBusy = false; renderOcrState();
}
const ocrLeft = () => pages.filter((p) => p.ocr !== 'done' && p.ocr !== 'error').length;
function renderOcrState() { const n = ocrLeft(); $('#ocrState').textContent = n ? `Reading text: ${n} page${n > 1 ? 's' : ''} left` : ''; }

/* ---------- projects ---------- */
async function touchBook() {
  book.count = pages.length; book.updated = Date.now();
  if (pages.length && book.coverFor !== pages[0].id) {
    try {
      const bmp = await createImageBitmap(pages[0].blob), k = 140 / bmp.height, c = mkCanvas(Math.round(bmp.width * k), 140);
      c.getContext('2d').drawImage(bmp, 0, 0, c.width, c.height);
      book.cover = (await toJpeg(c)).blob; book.coverFor = pages[0].id;
    } catch (e) {}
  }
  if (!pages.length) { book.cover = null; book.coverFor = null; }
  await dbPut('books', book);
}
async function loadBook(b) {
  book = b;
  pages = (await dbPagesOf(b.id)).sort((x, y) => x.n - y.n);
  urls.forEach((u) => URL.revokeObjectURL(u)); urls.clear(); ocrQueue.length = 0; pagesVer++;
  $('#bookTitle').textContent = b.title;
  pages.filter((p) => p.ocr !== 'done').forEach((p) => { p.ocr = 'pending'; enqueueOCR(p); });
  renderThumbs(); renderOcrState();
}
const urlOf = (p) => { if (!urls.has(p.id)) urls.set(p.id, URL.createObjectURL(p.blob)); return urls.get(p.id); };
function renderThumbs() {
  const box = $('#thumbs'); box.innerHTML = '';
  pages.forEach((p, i) => {
    const d = document.createElement('div'); d.className = 'th ' + (p.ocr || '');
    d.innerHTML = '<img alt=""><b></b><i></i>'; d.firstChild.src = urlOf(p); d.children[1].textContent = i + 1;
    d.onclick = () => openPage(p); box.appendChild(d);
  });
  box.scrollLeft = box.scrollWidth;
  $('#btnUndo').disabled = !pages.length; $('#btnExport').disabled = !pages.length;
}
async function addPage(canvas) {
  const { blob, w, h } = await toJpeg(canvas);
  const n = pages.length ? pages[pages.length - 1].n + 1 : 1;
  const p = { id: uid(), bookId: book.id, n, blob, w, h, ocr: 'pending', lines: [], text: '' };
  pages.push(p); pagesVer++; await dbPut('pages', p); await touchBook(); enqueueOCR(p); renderThumbs();
}
async function removePage(p) {
  pages = pages.filter((x) => x !== p); pagesVer++;
  const i = ocrQueue.indexOf(p.id); if (i >= 0) ocrQueue.splice(i, 1);
  await dbDel('pages', p.id);
  if (urls.has(p.id)) { URL.revokeObjectURL(urls.get(p.id)); urls.delete(p.id); }
  await touchBook(); renderThumbs(); renderOcrState();
}

/* ---------- capture ---------- */
let lastSig = null;
function sigDiff(a, b) {
  if (!a || !b || a.w !== b.w || a.h !== b.h) return 999;
  let s = 0; for (let i = 0; i < a.g.length; i++) s += Math.abs(a.g[i] - b.g[i]); return s / a.g.length;
}
async function processFrame(frame) {
  const det = detectPaper(frame, 400);
  const W = frame.width, H = frame.height, P = (q) => q.map((n) => [n[0] * W, n[1] * H]);
  const MAXL = 2600; const quads = [];
  const toward = (p, t, f) => [p[0] + (t[0] - p[0]) * f, p[1] + (t[1] - p[1]) * f];
  if (det && S.mode === 'spread') {
    const L = P(det.L), R = P(det.R); // L = [tl, gt, gb, bl], R = [gt, tr, br, gb]
    L[1] = toward(L[1], L[0], 0.035); L[2] = toward(L[2], L[3], 0.035); // trim crease shadow
    R[0] = toward(R[0], R[1], 0.035); R[3] = toward(R[3], R[2], 0.035);
    quads.push(inset(L, 0.008), inset(R, 0.008));
  } else if (det) {
    quads.push(inset(P(det.whole), 0.01));
  } else if (S.mode === 'spread') {
    quads.push([[0, 0], [W / 2, 0], [W / 2, H], [0, H]], [[W / 2, 0], [W, 0], [W, H], [W / 2, H]]);
  } else quads.push([[0, 0], [W, 0], [W, H], [0, H]]);
  for (const q of quads) {
    let c = warpQuad(frame, q, MAXL);
    c = enhance(c, S.clean);
    if (det && S.clean !== 'off') c = inkCrop(c);
    await addPage(c);
  }
  return !!det;
}
async function capture(manual) {
  if (busy) return false; busy = true;
  try {
    setStatus('Capturing', 'go');
    const frame = await grabBest();
    const sig = grayOf(frame, 160);
    if (!manual && sigDiff(sig, lastSig) < 2.0) return false;
    lastSig = sig;
    setStatus('Processing', 'go');
    const found = await processFrame(frame);
    cue();
    if (!found) setStatus('Book edges not found, used full frame', 'warn');
    return true;
  } catch (e) { console.error(e); setStatus('Capture failed', 'warn'); return false; }
  finally { busy = false; }
}
let actx = null;
function cue() {
  const f = $('#flash'); f.classList.remove('on'); void f.offsetWidth; f.classList.add('on');
  if (!S.sound) return;
  try { navigator.vibrate && navigator.vibrate(35); } catch (e) {}
  try {
    actx = actx || new (window.AudioContext || window.webkitAudioContext)();
    const o = actx.createOscillator(), g = actx.createGain();
    o.frequency.value = 880; g.gain.value = 0.06; o.connect(g); g.connect(actx.destination); o.start(); o.stop(actx.currentTime + 0.07);
  } catch (e) {}
}
function setStatus(t, cls) { const s = $('#status'); s.textContent = t; s.className = cls || ''; }

/* ---------- overlay: show what will be captured ---------- */
const ov = $('#ov');
let live = null;
function sizeOv() { const r = ov.getBoundingClientRect(), d = window.devicePixelRatio || 1; ov.width = r.width * d; ov.height = r.height * d; }
window.addEventListener('resize', sizeOv);
function drawOverlay() {
  const x = ov.getContext('2d'), d = window.devicePixelRatio || 1; x.clearRect(0, 0, ov.width, ov.height);
  if (!live || !video.videoWidth) return;
  const cw = ov.width / d, ch = ov.height / d, vw = video.videoWidth, vh = video.videoHeight, s = Math.min(cw / vw, ch / vh);
  const ox = (cw - vw * s) / 2, oy = (ch - vh * s) / 2, M = (p) => [(ox + p[0] * vw * s) * d, (oy + p[1] * vh * s) * d];
    const quads = S.mode === 'spread' ? [live.L, live.R] : [live.whole];
  x.lineWidth = 3 * d; x.strokeStyle = running ? 'rgba(80,225,150,.95)' : 'rgba(255,255,255,.8)'; x.fillStyle = 'rgba(80,225,150,.08)';
  for (const q of quads) { x.beginPath(); q.forEach((p, i) => { const m = M(p); i ? x.lineTo(m[0], m[1]) : x.moveTo(m[0], m[1]); }); x.closePath(); x.fill(); x.stroke(); }
}
function updateLive(src) {
  const det = detectPaper(src, 160);
  if (!det) { live = null; return; }
  if (live) {
    let far = false;
    for (const k of ['whole', 'L', 'R']) det[k].forEach((p, i) => { if (Math.hypot(p[0] - live[k][0][0] * 0 - live[k][i][0], p[1] - live[k][i][1]) > 0.12) far = true; });
    if (!far) for (const k of ['whole', 'L', 'R']) det[k] = det[k].map((p, i) => [live[k][i][0] * 0.55 + p[0] * 0.45, live[k][i][1] * 0.55 + p[1] * 0.45]);
  }
  live = det;
}

/* ---------- auto-capture loop ---------- */
let prevS = null, stillSince = 0, accum = 0, needMotion = false, cooldown = 0, loop = 0, tickN = 0, focusSince = 0, focused = false;
const sharpWin = [], peakWin = [];
function motionFrame(base) {
  const c = downTo(base, 48), d = c.getContext('2d', { willReadFrequently: true }).getImageData(0, 0, c.width, c.height).data;
  let g = new Float32Array(c.width * c.height); let mean = 0;
  for (let i = 0, j = 0; i < d.length; i += 4, j++) g[j] = d[i] * 0.299 + d[i + 1] * 0.587 + d[i + 2] * 0.114;
  g = boxBlur(g, c.width, c.height, 2); // soften edges so a little hand shake does not read as motion
  for (let j = 0; j < g.length; j++) mean += g[j];
  mean /= g.length; let v = 0; for (let j = 0; j < g.length; j++) { g[j] -= mean; v += g[j] * g[j]; }
  const sd = Math.sqrt(v / g.length) || 1; for (let j = 0; j < g.length; j++) g[j] = g[j] / sd * 40; // cancel exposure/brightness changes
  return g;
}
const mHist = [];
function tick() {
  loop = setTimeout(tick, 110);
  if (!inScan || !video.videoWidth) return;
  tickN++;
  const base = downTo(video, 640); // one shared downscale per tick keeps phones cool
  if (tickN % 3 === 0) { updateLive(base); drawOverlay(); }
  if (!running || busy) return;
  const now = performance.now();
  const cur = motionFrame(base); let m = 0;
  if (prevS) { for (let i = 0; i < cur.length; i++) m += Math.abs(cur[i] - prevS[i]); m /= cur.length; }
  prevS = cur;
  mHist.push(m); if (mHist.length > 3) mHist.shift();
  const mm = [...mHist].sort((x, y) => x - y)[Math.floor(mHist.length / 2)]; // median of last 3 ignores single spikes
  const sh = sharpness(base, 480); sharpWin.push(sh); if (sharpWin.length > 4) sharpWin.shift();
  const STILL = 1.3 * S.sens, TURN0 = 1.2 * S.sens, ACC = 3.5;
  if (S.diag) $('#diag').textContent = `motion ${mm.toFixed(2)} / ${STILL.toFixed(2)}   sharp ${sh.toFixed(0)}   ${video.videoWidth}x${video.videoHeight}${live ? '' : '   no book'}`;
  if (now < cooldown) { stillSince = 0; return; }
  const still = mm < STILL;
  accum = accum * 0.9 + Math.max(0, m - TURN0); // sustained movement (a hand or page crossing the frame)
  if (!still) { stillSince = 0; focused = false; focusSince = 0; } else if (!stillSince) stillSince = now;
  if (needMotion && accum > ACC) needMotion = false;
  if (needMotion) { setStatus('Turn the page'); return; }
  if (!still) { setStatus('Settling...', 'warn'); return; }
  if (!live) { setStatus('Book not found. Move closer, add light', 'warn'); return; }
  if (now - stillSince < S.hold) { setStatus('Hold still...', 'go'); return; }
  // wait for focus to settle: recent sharpness values agree and are close to the best seen for this page
  peakWin.push(sh); if (peakWin.length > 40) peakWin.shift();
  const mx = Math.max(...sharpWin), mn = Math.min(...sharpWin), peak = Math.max(...peakWin);
  const stable = sharpWin.length >= 4 && mx / Math.max(1, mn) < 1.35 && sh >= 0.8 * peak;
  if (!stable) {
    if (!focusSince) { focusSince = now; refocus(); }
    if (now - focusSince < 3000) { setStatus('Focusing...', 'warn'); return; }
  }
  capture(false).then((ok) => {
    cooldown = performance.now() + 800; stillSince = 0; accum = 0; prevS = null; mHist.length = 0; focusSince = 0; peakWin.length = 0; sharpWin.length = 0;
    needMotion = true;
    setStatus(ok ? (S.mode === 'spread' ? `Got pages ${pages.length - 1} and ${pages.length}. Turn the page` : `Got page ${pages.length}. Turn the page`) : 'Turn the page');
  });
}
function setRunning(on) {
  running = on;
  $('#btnMain').textContent = on ? 'Pause' : 'Resume';
  $('#btnMain').classList.toggle('live', on);
  if (on) {
    needMotion = false; prevS = null; mHist.length = 0; stillSince = 0; accum = 0; cooldown = performance.now() + 500; focusSince = 0; peakWin.length = 0; sharpWin.length = 0;
    navigator.wakeLock && navigator.wakeLock.request('screen').then((w) => { wakeLock = w; }).catch(() => {});
    setStatus('Hold still...', 'go');
  } else {
    try { wakeLock && wakeLock.release(); } catch (e) {} wakeLock = null; setStatus('Paused');
  }
}

/* ---------- screens ---------- */
const open = (id) => $(id).classList.add('open');
const closeAll = () => document.querySelectorAll('.sheet').forEach((s) => s.classList.remove('open'));
document.querySelectorAll('.sheet .close').forEach((b) => (b.onclick = closeAll));

async function showHome() {
  inScan = false; setRunning(false); closeCamera(); live = null;
  $('#scan').classList.add('hidden'); $('#home').classList.remove('hidden');
  await renderHome();
}
async function renderHome() {
  const all = (await dbAll('books')).sort((a, b) => (b.updated || b.created) - (a.updated || a.created));
  const box = $('#projList'); box.innerHTML = '';
  if (!all.length) { box.innerHTML = '<p>No projects yet.</p>'; }
  for (const b of all) {
    if (b.count === undefined) b.count = await dbCount(b.id);
    const d = document.createElement('div'); d.className = 'proj';
    const when = new Date(b.updated || b.created).toLocaleDateString(undefined, { month: 'short', day: 'numeric' });
    d.innerHTML = '<div class="cv"></div><div class="in"><b></b><small></small><div class="bt"><button class="go">Scan</button><button class="ex">Export</button><button class="mo">More</button></div></div>';
    d.querySelector('b').textContent = b.title; d.querySelector('small').textContent = `${b.count} page${b.count === 1 ? '' : 's'} · ${when}`;
    if (b.cover) d.querySelector('.cv').style.backgroundImage = `url(${URL.createObjectURL(b.cover)})`;
    d.querySelector('.go').onclick = () => openProject(b);
    d.querySelector('.ex').onclick = async () => { await loadBook(b); if (!pages.length) { alert('No pages in this project yet.'); return; } openExport(); };
    d.querySelector('.mo').onclick = () => openMore(b);
    box.appendChild(d);
  }
  $('#ver').textContent = 'BookScan v' + VERSION;
}
async function openProject(b) {
  await loadBook(b);
  $('#home').classList.add('hidden'); $('#scan').classList.remove('hidden'); inScan = true; sizeOv();
  $('#camMsg').classList.add('hidden'); setStatus('Starting camera');
  try {
    await openCamera(); sizeOv(); setRunning(true);
  } catch (e) {
    $('#camErr').textContent = 'Camera unavailable: ' + (e && e.message ? e.message : e) + '. Allow camera access for this site in browser settings.';
    $('#camMsg').classList.remove('hidden');
  }
}
$('#btnRetry').onclick = () => openProject(book);
$('#btnBack').onclick = showHome;

/* name sheet */
let nameCb = null;
function askName(title, val, cb) { $('#nameTitle').textContent = title; $('#nameInput').value = val; nameCb = cb; open('#sheetName'); setTimeout(() => $('#nameInput').select(), 50); }
$('#btnNameOk').onclick = () => { const v = $('#nameInput').value.trim(); if (!v) return; closeAll(); nameCb && nameCb(v); };
$('#nameInput').addEventListener('keydown', (e) => { if (e.key === 'Enter') $('#btnNameOk').click(); });
$('#btnNew').onclick = () => {
  const d = new Date(), def = 'Scan ' + d.toLocaleDateString(undefined, { month: 'short', day: 'numeric' }) + ' ' + d.toLocaleTimeString(undefined, { hour: 'numeric', minute: '2-digit' });
  askName('New project name', def, async (t) => {
    const b = { id: uid(), title: t, created: Date.now(), updated: Date.now(), count: 0 };
    await dbPut('books', b); openProject(b);
  });
};
let moreBook = null;
function openMore(b) { moreBook = b; $('#moreTitle').textContent = b.title; open('#sheetMore'); }
$('#btnRename').onclick = () => { const b = moreBook; closeAll(); askName('Rename project', b.title, async (t) => { b.title = t; await dbPut('books', b); renderHome(); }); };
$('#btnClear').onclick = async () => {
  const b = moreBook; if (!confirm(`Remove all ${b.count || 0} pages from "${b.title}"? The project stays.`)) return;
  for (const p of await dbPagesOf(b.id)) await dbDel('pages', p.id);
  b.count = 0; b.cover = null; b.coverFor = null; b.updated = Date.now(); await dbPut('books', b); closeAll(); renderHome();
};
$('#btnDelProj').onclick = async () => {
  const b = moreBook; if (!confirm(`Delete "${b.title}" and its pages from this phone? This cannot be undone.`)) return;
  for (const p of await dbPagesOf(b.id)) await dbDel('pages', p.id);
  await dbDel('books', b.id); closeAll(); renderHome();
};

/* settings */
function syncSettingsUI() {
  $('#setMode').value = S.mode; $('#setClean').value = S.clean; $('#setSens').value = String(S.sens); $('#setHold').value = String(S.hold);
  $('#setHires').checked = S.hires; $('#setSound').checked = S.sound; $('#setDiag').checked = S.diag;
  $('#setHires').closest('.row').style.display = window.ImageCapture ? '' : 'none';
}
const bind = (id, key, conv) => { $(id).onchange = (e) => { S[key] = conv(e.target); saveS(); if (key === 'diag' && !S.diag) $('#diag').textContent = ''; }; };
bind('#setMode', 'mode', (t) => t.value); bind('#setClean', 'clean', (t) => t.value); bind('#setSens', 'sens', (t) => +t.value);
bind('#setHold', 'hold', (t) => +t.value); bind('#setHires', 'hires', (t) => t.checked); bind('#setSound', 'sound', (t) => t.checked); bind('#setDiag', 'diag', (t) => t.checked);
$('#btnSet').onclick = () => { syncSettingsUI(); open('#sheetSet'); };

/* scan controls */
$('#btnMain').onclick = () => setRunning(!running);
$('#btnShutter').onclick = async () => { const ok = await capture(true); if (ok) { cooldown = performance.now() + 800; needMotion = running; setStatus('Captured'); } };
$('#btnUndo').onclick = async () => {
  if (!pages.length) return;
  const k = S.mode === 'spread' ? Math.min(2, pages.length) : 1;
  for (let i = 0; i < k; i++) await removePage(pages[pages.length - 1]);
  lastSig = null; needMotion = false; setStatus('Removed last scan');
};
function openPage(p) {
  $('#pgTitle').textContent = 'Page ' + (pages.indexOf(p) + 1); $('#pgImg').src = urlOf(p);
  $('#btnDelPage').onclick = async () => { if (confirm('Delete this page?')) { await removePage(p); closeAll(); } };
  open('#sheetPage');
}

/* ---------- export ---------- */
function toWinAnsi(font, s) { let o = ''; for (const ch of s) { try { font.encodeText(ch); o += ch; } catch (e) {} } return o; }
async function buildPdf() {
  const { PDFDocument, StandardFonts } = PDFLib;
  const doc = await PDFDocument.create();
  doc.setTitle(book.title); doc.setProducer('BookScan'); doc.setCreator('BookScan');
  const font = await doc.embedFont(StandardFonts.Helvetica), K = 72 / 200;
  for (const p of pages) {
    const img = await doc.embedJpg(await p.blob.arrayBuffer()), W = img.width * K, H = img.height * K;
    const page = doc.addPage([W, H]); page.drawImage(img, { x: 0, y: 0, width: W, height: H });
    for (const l of p.lines || []) {
      const t = toWinAnsi(font, l.t); if (!t) continue;
      const bw = (l.x1 - l.x0) * K, bh = (l.y1 - l.y0) * K, w1 = font.widthOfTextAtSize(t, 1) || 1;
      page.drawText(t, { x: l.x0 * K, y: H - l.y1 * K + bh * 0.2, size: Math.max(2, Math.min(bw / w1, bh * 2.5)), font, opacity: 0 });
    }
  }
  return doc.save();
}
const buildText = () => pages.map((p, i) => `--- Page ${i + 1} ---\n${(p.text || '').trim()}\n`).join('\n');
const safeName = () => (book.title.replace(/[^\w\-]+/g, '_').replace(/^_+|_+$/g, '') || 'book');
let exp = { ver: -1, file: null, text: '', url: null };
const expBtns = ['#btnShare', '#btnOpen', '#btnShareTxt', '#btnCopy', '#btnDownload'];
async function openExport() {
  $('#expInfo').textContent = `${book.title}: ${pages.length} pages`; $('#expMsg').textContent = '';
  expBtns.forEach((b) => ($(b).disabled = true)); open('#sheetExp');
  const myBook = book.id;
  try {
    while (ocrLeft() > 0) { $('#expMsg').textContent = `Reading text: ${ocrLeft()} page${ocrLeft() > 1 ? 's' : ''} left...`; await sleep(400); if (book.id !== myBook) return; }
    if (exp.ver !== pagesVer || exp.book !== book.id) {
      $('#expMsg').textContent = 'Building PDF...';
      const bytes = await buildPdf();
      if (exp.url) URL.revokeObjectURL(exp.url);
      const blob = new Blob([bytes], { type: 'application/pdf' });
      exp = { ver: pagesVer, book: book.id, file: new File([blob], safeName() + '.pdf', { type: 'application/pdf' }), text: buildText(), url: URL.createObjectURL(blob) };
    }
    $('#expMsg').textContent = `PDF ready (${(exp.file.size / 1048576).toFixed(1)} MB). Tap Share, then choose Mail, Save to Files, or another app.`;
    expBtns.forEach((b) => ($(b).disabled = false));
  } catch (e) { console.error(e); $('#expMsg').textContent = 'Could not build PDF: ' + e.message; }
}
$('#btnExport').onclick = openExport;
/* share must be called straight from the tap, so the file is built beforehand */
$('#btnShare').onclick = async () => {
  try {
    if (navigator.canShare && navigator.canShare({ files: [exp.file] })) { await navigator.share({ files: [exp.file], title: book.title }); return; }
    $('#expMsg').textContent = 'Sharing files is not supported here. Use Open PDF or Download.';
  } catch (e) { if (e && e.name !== 'AbortError') $('#expMsg').textContent = 'Share failed (' + e.name + '). Try Open PDF.'; }
};
$('#btnShareTxt').onclick = async () => {
  const f = new File([exp.text], safeName() + '.txt', { type: 'text/plain' });
  try { if (navigator.canShare && navigator.canShare({ files: [f] })) { await navigator.share({ files: [f], title: book.title }); return; } } catch (e) { if (e && e.name === 'AbortError') return; }
  try { await navigator.share({ text: exp.text, title: book.title }); } catch (e) { if (e && e.name !== 'AbortError') $('#expMsg').textContent = 'Use Copy text.'; }
};
$('#btnCopy').onclick = async () => { try { await navigator.clipboard.writeText(exp.text); $('#expMsg').textContent = 'Text copied.'; } catch (e) { $('#expMsg').textContent = 'Copy failed.'; } };
$('#btnOpen').onclick = () => { const w = window.open(exp.url, '_blank'); if (!w) location.href = exp.url; };
$('#btnDownload').onclick = () => { const a = document.createElement('a'); a.href = exp.url; a.download = exp.file.name; document.body.appendChild(a); a.click(); a.remove(); };

/* ---------- boot ---------- */
async function boot() {
  db = await openDB();
  if ('serviceWorker' in navigator) navigator.serviceWorker.register('sw.js').catch(() => {});
  initOCR().catch(() => {});
  tick();
  await showHome();
  window.__bs = { get pages() { return pages; }, get running() { return running; }, get live() { return live; }, S, setRunning, openProject, dbAll };
}
boot();
