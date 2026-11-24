'use strict';
/* BookScan: point at an open book, turn pages, get a searchable PDF. Everything runs on the device. */

const $ = (s) => document.querySelector(s);
const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
const BASE = new URL('./', location.href).href;

/* ---------- settings ---------- */
const DEF = { mode: 'spread', enhance: true, hires: false, hold: 800, sound: true };
let S = { ...DEF };
try { S = { ...DEF, ...JSON.parse(localStorage.getItem('bs.settings') || '{}') }; } catch (e) {}
const saveS = () => { try { localStorage.setItem('bs.settings', JSON.stringify(S)); } catch (e) {} };

/* ---------- storage (IndexedDB) ---------- */
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
const dbPagesOf = (bookId) => tx('pages', 'readonly', (o) => o.index('bookId').getAll(bookId));
const uid = () => Date.now().toString(36) + Math.random().toString(36).slice(2, 6);

/* ---------- state ---------- */
let book = null;          // current book record
let pages = [];           // pages of current book, sorted
const urls = new Map();   // page id -> object URL
let running = false, busy = false;
let stream = null, track = null, wakeLock = null;
const gutterHist = [];

/* ---------- camera ---------- */
const video = $('#cam');
async function openCamera() {
  stream = await navigator.mediaDevices.getUserMedia({
    video: { facingMode: { ideal: 'environment' }, width: { ideal: 3840 }, height: { ideal: 2160 } },
    audio: false,
  });
  video.srcObject = stream;
  track = stream.getVideoTracks()[0];
  try {
    const caps = track.getCapabilities ? track.getCapabilities() : {};
    const adv = {};
    if (caps.focusMode && caps.focusMode.includes('continuous')) adv.focusMode = 'continuous';
    if (caps.exposureMode && caps.exposureMode.includes('continuous')) adv.exposureMode = 'continuous';
    if (caps.whiteBalanceMode && caps.whiteBalanceMode.includes('continuous')) adv.whiteBalanceMode = 'continuous';
    if (Object.keys(adv).length) await track.applyConstraints({ advanced: [adv] });
  } catch (e) { /* not supported, fine */ }
  await video.play().catch(() => {});
  await new Promise((r) => { if (video.videoWidth) r(); else video.onloadedmetadata = () => r(); });
}

/* ---------- image helpers ---------- */
function mkCanvas(w, h) { const c = document.createElement('canvas'); c.width = w; c.height = h; return c; }
function grayOf(canvas, w) {
  const h = Math.max(1, Math.round(canvas.height * w / canvas.width));
  const c = mkCanvas(w, h), x = c.getContext('2d', { willReadFrequently: true });
  x.drawImage(canvas, 0, 0, w, h);
  const d = x.getImageData(0, 0, w, h).data, g = new Float32Array(w * h);
  for (let i = 0, j = 0; i < d.length; i += 4, j++) g[j] = d[i] * 0.299 + d[i + 1] * 0.587 + d[i + 2] * 0.114;
  return { g, w, h };
}
function sharpness(canvas) {
  const { g, w, h } = grayOf(canvas, 480);
  let s = 0, s2 = 0, n = 0;
  for (let y = 1; y < h - 1; y++) for (let x = 1; x < w - 1; x++) {
    const i = y * w + x, l = 4 * g[i] - g[i - 1] - g[i + 1] - g[i - w] - g[i + w];
    s += l; s2 += l * l; n++;
  }
  const m = s / n; return s2 / n - m * m;
}
function frameCanvas() {
  const c = mkCanvas(video.videoWidth, video.videoHeight);
  c.getContext('2d').drawImage(video, 0, 0);
  return c;
}
async function grabBest() {
  if (S.hires && window.ImageCapture && track) {
    try {
      const blob = await new ImageCapture(track).takePhoto();
      const bmp = await createImageBitmap(blob);
      const c = mkCanvas(bmp.width, bmp.height); c.getContext('2d').drawImage(bmp, 0, 0);
      return c;
    } catch (e) { /* fall through to video frame */ }
  }
  let best = null, bs = -1;
  for (let i = 0; i < 3; i++) {
    const c = frameCanvas(), s = sharpness(c);
    if (s > bs) { best = c; bs = s; }
    if (i < 2) await sleep(90);
  }
  return best;
}

/* Find the crease: the darkest vertical dip near the middle, as a fraction of width. */
function detectGutter(canvas) {
  const { g, w, h } = grayOf(canvas, 400);
  const y0 = Math.floor(h * 0.12), y1 = Math.floor(h * 0.88);
  const col = new Float32Array(w);
  for (let x = 0; x < w; x++) { let s = 0; for (let y = y0; y < y1; y++) s += g[y * w + x]; col[x] = s / (y1 - y0); }
  const sm = new Float32Array(w);
  for (let x = 0; x < w; x++) { let s = 0, n = 0; for (let k = -2; k <= 2; k++) { const xx = x + k; if (xx >= 0 && xx < w) { s += col[xx]; n++; } } sm[x] = s / n; }
  let bestX = -1, bestScore = -1e9;
  for (let x = Math.floor(w * 0.3); x <= Math.floor(w * 0.7); x++) {
    let l = 0, r = 0, n = 0;
    for (let k = 14; k <= 34; k++) { if (x - k >= 0 && x + k < w) { l += sm[x - k]; r += sm[x + k]; n++; } }
    if (!n) continue;
    const score = (l + r) / (2 * n) - sm[x];
    if (score > bestScore) { bestScore = score; bestX = x; }
  }
  if (bestX < 0 || bestScore < 3) return null;
  return bestX / w;
}
function medianGutter() {
  if (!gutterHist.length) return 0.5;
  const a = [...gutterHist].sort((x, y) => x - y); return a[Math.floor(a.length / 2)];
}

/* Flatten shadows and lift contrast so pages read like a scan. */
function enhance(src) {
  const w = src.width, h = src.height;
  const ctx = src.getContext('2d', { willReadFrequently: true });
  const img = ctx.getImageData(0, 0, w, h), d = img.data;
  const B = 16, sw = Math.max(2, Math.ceil(w / B)), sh = Math.max(2, Math.ceil(h / B));
  let small = new Float32Array(sw * sh); const cnt = new Float32Array(sw * sh);
  const gray = new Uint8ClampedArray(w * h);
  for (let y = 0; y < h; y++) for (let x = 0; x < w; x++) {
    const i = (y * w + x) * 4, v = d[i] * 0.299 + d[i + 1] * 0.587 + d[i + 2] * 0.114;
    gray[y * w + x] = v;
    const k = Math.min(sh - 1, (y / B) | 0) * sw + Math.min(sw - 1, (x / B) | 0);
    small[k] += v; cnt[k]++;
  }
  for (let k = 0; k < small.length; k++) small[k] /= cnt[k] || 1;
  for (let pass = 0; pass < 3; pass++) { // grey dilation: paper level, ignore ink
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
  const sc = mkCanvas(sw, sh), sx = sc.getContext('2d'), sd = sx.createImageData(sw, sh);
  for (let k = 0; k < small.length; k++) { const v = small[k]; sd.data[k * 4] = sd.data[k * 4 + 1] = sd.data[k * 4 + 2] = v; sd.data[k * 4 + 3] = 255; }
  sx.putImageData(sd, 0, 0);
  const bc = mkCanvas(w, h), bx = bc.getContext('2d', { willReadFrequently: true });
  bx.imageSmoothingEnabled = true; bx.imageSmoothingQuality = 'high';
  bx.drawImage(sc, 0, 0, w, h);
  const bd = bx.getImageData(0, 0, w, h).data;
  for (let p = 0; p < w * h; p++) {
    const bg = Math.max(60, bd[p * 4]);
    let v = (gray[p] / bg) * 255;
    v = (v - 70) * 255 / (225 - 70);
    v = v < 0 ? 0 : v > 255 ? 255 : v;
    d[p * 4] = d[p * 4 + 1] = d[p * 4 + 2] = v; d[p * 4 + 3] = 255;
  }
  ctx.putImageData(img, 0, 0);
  return src;
}

function cropCanvas(src, x0, x1) {
  const c = mkCanvas(x1 - x0, src.height);
  c.getContext('2d').drawImage(src, x0, 0, x1 - x0, src.height, 0, 0, x1 - x0, src.height);
  return c;
}
function toJpeg(canvas) {
  const MAX = 2600;
  let c = canvas;
  const long = Math.max(c.width, c.height);
  if (long > MAX) { const k = MAX / long; const n = mkCanvas(Math.round(c.width * k), Math.round(c.height * k)); n.getContext('2d').drawImage(c, 0, 0, n.width, n.height); c = n; }
  return new Promise((r) => c.toBlob((b) => r({ blob: b, w: c.width, h: c.height }), 'image/jpeg', 0.82));
}

/* ---------- OCR ---------- */
let worker = null, ocrReady = null;
const ocrQueue = [];
let ocrBusy = false;
function initOCR() {
  if (ocrReady) return ocrReady;
  ocrReady = (async () => {
    worker = await Tesseract.createWorker('eng', 1, {
      workerPath: BASE + 'lib/worker.min.js',
      corePath: BASE + 'lib/',
      langPath: BASE + 'lib/lang',
      workerBlobURL: false,
      cacheMethod: 'none',
      gzip: true,
    });
  })();
  return ocrReady;
}
function enqueueOCR(p) { if (!ocrQueue.includes(p.id)) ocrQueue.push(p.id); pump(); }
async function pump() {
  if (ocrBusy) return;
  ocrBusy = true;
  try {
    await initOCR();
    while (ocrQueue.length) {
      const id = ocrQueue.shift();
      const p = pages.find((x) => x.id === id);
      if (!p || p.ocr === 'done') continue;
      renderOcrState();
      try {
        const { data } = await worker.recognize(p.blob);
        p.lines = (data.lines || []).map((l) => ({ t: l.text.replace(/\s+/g, ' ').trim(), x0: l.bbox.x0, y0: l.bbox.y0, x1: l.bbox.x1, y1: l.bbox.y1 })).filter((l) => l.t);
        p.text = data.text || '';
        p.ocr = 'done';
      } catch (e) { console.error(e); p.ocr = 'error'; }
      await dbPut('pages', p);
      renderThumbs(); renderOcrState();
    }
  } catch (e) {
    console.error(e); $('#ocrState').textContent = 'OCR failed to start';
  }
  ocrBusy = false; renderOcrState();
}
function renderOcrState() {
  const n = pages.filter((p) => p.ocr !== 'done' && p.ocr !== 'error').length;
  $('#ocrState').textContent = n ? `Reading text: ${n} page${n > 1 ? 's' : ''} left` : '';
  $('#btnExport').disabled = !pages.length;
}

/* ---------- book / pages ---------- */
async function loadBook(b) {
  book = b;
  localStorage.setItem('bs.current', b.id);
  pages = (await dbPagesOf(b.id)).sort((a, c) => a.n - c.n);
  urls.forEach((u) => URL.revokeObjectURL(u)); urls.clear();
  gutterHist.length = 0;
  $('#bookTitle').textContent = b.title;
  renderThumbs();
  pages.filter((p) => p.ocr !== 'done').forEach((p) => { p.ocr = 'pending'; enqueueOCR(p); });
  renderOcrState();
}
async function newBook() {
  const all = await dbAll('books');
  const b = { id: uid(), title: 'Book ' + (all.length + 1), created: Date.now() };
  await dbPut('books', b); await loadBook(b);
}
const urlOf = (p) => { if (!urls.has(p.id)) urls.set(p.id, URL.createObjectURL(p.blob)); return urls.get(p.id); };
function renderThumbs() {
  const box = $('#thumbs'); box.innerHTML = '';
  pages.forEach((p, i) => {
    const d = document.createElement('div'); d.className = 'th ' + (p.ocr || '');
    d.innerHTML = `<img alt=""><b>${i + 1}</b><i></i>`; d.firstChild.src = urlOf(p);
    d.onclick = () => openPage(p);
    box.appendChild(d);
  });
  box.scrollLeft = box.scrollWidth;
  $('#btnUndo').disabled = !pages.length;
  $('#btnExport').disabled = !pages.length;
}
async function addPage(canvas) {
  if (S.enhance) enhance(canvas);
  const { blob, w, h } = await toJpeg(canvas);
  const n = pages.length ? pages[pages.length - 1].n + 1 : 1;
  const p = { id: uid(), bookId: book.id, n, blob, w, h, ocr: 'pending', lines: [], text: '' };
  pages.push(p); await dbPut('pages', p); enqueueOCR(p); renderThumbs();
}
async function removePage(p) {
  pages = pages.filter((x) => x !== p);
  const i = ocrQueue.indexOf(p.id); if (i >= 0) ocrQueue.splice(i, 1);
  await dbDel('pages', p.id);
  if (urls.has(p.id)) { URL.revokeObjectURL(urls.get(p.id)); urls.delete(p.id); }
  renderThumbs(); renderOcrState();
}

/* ---------- capture ---------- */
let lastSig = null;
function sigOf(canvas) { return grayOf(canvas, 160); }
function sigDiff(a, b) {
  if (!a || !b || a.w !== b.w || a.h !== b.h) return 999;
  let s = 0; for (let i = 0; i < a.g.length; i++) s += Math.abs(a.g[i] - b.g[i]);
  return s / a.g.length;
}
const DUP_T = 2.0;

async function capture(manual) {
  if (busy) return false;
  busy = true;
  try {
    setStatus('Capturing', 'go');
    const frame = await grabBest();
    const sig = sigOf(frame);
    if (!manual && sigDiff(sig, lastSig) < DUP_T) { busy = false; return false; }
    lastSig = sig;
    if (S.mode === 'spread') {
      const gx = detectGutter(frame);
      if (gx !== null) { gutterHist.push(gx); if (gutterHist.length > 7) gutterHist.shift(); }
      const x = Math.round(medianGutter() * frame.width);
      await addPage(cropCanvas(frame, 0, x));
      await addPage(cropCanvas(frame, x, frame.width));
    } else {
      await addPage(frame);
    }
    cue();
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
    o.frequency.value = 880; g.gain.value = 0.06; o.connect(g); g.connect(actx.destination);
    o.start(); o.stop(actx.currentTime + 0.07);
  } catch (e) {}
}
function setStatus(t, cls) { const s = $('#status'); s.textContent = t; s.className = cls || ''; }

/* Auto-capture loop: wait for motion (page turn), then stillness, then capture. */
const STILL_T = 1.3, MOTION_ACCUM = 14;
let prev = null, stillSince = 0, accum = 0, needMotion = false, cooldown = 0, loop = 0;
function tick() {
  loop = setTimeout(tick, 110);
  if (!running || busy || !video.videoWidth) return;
  const now = performance.now();
  const cur = grayOf(frameSmall(), 80);
  const m = prev ? sigDiff(cur, prev) : 0; prev = cur;
  if (now < cooldown) { stillSince = 0; return; }
  const still = m < STILL_T;
  if (!still) { stillSince = 0; if (m > 2.5) accum += m; } else if (!stillSince) stillSince = now;
  if (needMotion && accum > MOTION_ACCUM) needMotion = false;
  if (needMotion) { setStatus('Turn the page'); return; }
  if (!still) { setStatus('Settling...', 'warn'); return; }
  setStatus('Hold still...', 'go');
  if (now - stillSince >= S.hold) {
    capture(false).then((ok) => {
      cooldown = performance.now() + 700; stillSince = 0; accum = 0; prev = null;
      if (ok) { needMotion = true; setStatus(S.mode === 'spread' ? `Got pages ${pages.length - 1}-${pages.length}. Turn the page` : `Got page ${pages.length}. Turn the page`); }
      else { needMotion = true; setStatus('Turn the page'); }
    });
  }
}
let smallC = null;
function frameSmall() {
  if (!smallC) smallC = mkCanvas(160, 120);
  const x = smallC.getContext('2d', { willReadFrequently: true });
  x.drawImage(video, 0, 0, 160, 120);
  return smallC;
}

async function setRunning(on) {
  running = on;
  $('#btnMain').textContent = on ? 'Pause' : 'Start';
  $('#btnMain').classList.toggle('live', on);
  $('#app').classList.toggle('live', on);
  if (on) {
    needMotion = false; prev = null; stillSince = 0; accum = 0; cooldown = performance.now() + 600; lastSig = pages.length ? lastSig : null;
    try { wakeLock = await navigator.wakeLock.request('screen'); } catch (e) {}
    setStatus('Hold still...', 'go');
  } else {
    try { wakeLock && wakeLock.release(); } catch (e) {}
    setStatus('Paused');
  }
}

/* ---------- export ---------- */
function toWinAnsi(font, s) {
  let out = '';
  for (const ch of s) { try { font.encodeText(ch); out += ch; } catch (e) { out += ''; } }
  return out;
}
async function buildPdf() {
  const { PDFDocument, StandardFonts } = PDFLib;
  const doc = await PDFDocument.create();
  doc.setTitle(book.title); doc.setProducer('BookScan'); doc.setCreator('BookScan');
  const font = await doc.embedFont(StandardFonts.Helvetica);
  const K = 72 / 200; // assume 200 dpi
  for (const p of pages) {
    const img = await doc.embedJpg(await p.blob.arrayBuffer());
    const W = img.width * K, H = img.height * K;
    const page = doc.addPage([W, H]);
    page.drawImage(img, { x: 0, y: 0, width: W, height: H });
    for (const l of p.lines || []) {
      const t = toWinAnsi(font, l.t); if (!t) continue;
      const bw = (l.x1 - l.x0) * K, bh = (l.y1 - l.y0) * K;
      const w1 = font.widthOfTextAtSize(t, 1) || 1;
      const size = Math.max(2, Math.min(bw / w1, bh * 2.5));
      page.drawText(t, { x: l.x0 * K, y: H - l.y1 * K + bh * 0.2, size, font, opacity: 0 });
    }
  }
  return doc.save();
}
function buildText() {
  return pages.map((p, i) => `--- Page ${i + 1} ---\n${(p.text || '').trim()}\n`).join('\n');
}
async function shareOrSave(blob, name, type) {
  const file = new File([blob], name, { type });
  try {
    if (navigator.canShare && navigator.canShare({ files: [file] })) { await navigator.share({ files: [file], title: book.title }); return 'Shared.'; }
  } catch (e) { if (e && e.name === 'AbortError') return ''; }
  const a = document.createElement('a'); a.href = URL.createObjectURL(blob); a.download = name;
  document.body.appendChild(a); a.click(); a.remove();
  setTimeout(() => URL.revokeObjectURL(a.href), 20000);
  return 'Saved to downloads.';
}
const safeName = () => book.title.replace(/[^\w\-]+/g, '_') || 'book';
async function waitOCR() {
  while (pages.some((p) => p.ocr !== 'done' && p.ocr !== 'error')) { $('#expMsg').textContent = 'Finishing text recognition...'; await sleep(400); }
}

/* ---------- UI ---------- */
const open = (id) => $(id).classList.add('open');
const closeAll = () => document.querySelectorAll('.sheet').forEach((s) => s.classList.remove('open'));
document.querySelectorAll('.sheet .close').forEach((b) => (b.onclick = closeAll));

function applyMode() { $('#app').classList.toggle('single', S.mode === 'single'); }
function syncSettingsUI() {
  $('#setMode').value = S.mode; $('#setEnhance').checked = S.enhance; $('#setHires').checked = S.hires;
  $('#setHold').value = String(S.hold); $('#setSound').checked = S.sound;
  $('#setHires').closest('.row').style.display = window.ImageCapture ? '' : 'none';
}
$('#setMode').onchange = (e) => { S.mode = e.target.value; saveS(); applyMode(); };
$('#setEnhance').onchange = (e) => { S.enhance = e.target.checked; saveS(); };
$('#setHires').onchange = (e) => { S.hires = e.target.checked; saveS(); };
$('#setHold').onchange = (e) => { S.hold = +e.target.value; saveS(); };
$('#setSound').onchange = (e) => { S.sound = e.target.checked; saveS(); };
$('#btnSet').onclick = () => { syncSettingsUI(); open('#sheetSet'); };

$('#btnMain').onclick = () => setRunning(!running);
$('#btnShutter').onclick = async () => { const ok = await capture(true); if (ok) { cooldown = performance.now() + 700; needMotion = running; setStatus('Captured'); } };
$('#btnUndo').onclick = async () => {
  if (!pages.length) return;
  const k = S.mode === 'spread' ? Math.min(2, pages.length) : 1;
  for (let i = 0; i < k; i++) await removePage(pages[pages.length - 1]);
  lastSig = null; needMotion = false; setStatus('Removed last scan');
};

async function openPage(p) {
  $('#pgTitle').textContent = 'Page ' + (pages.indexOf(p) + 1);
  $('#pgImg').src = urlOf(p);
  $('#btnDelPage').onclick = async () => { if (confirm('Delete this page?')) { await removePage(p); closeAll(); } };
  open('#sheetPage');
}

$('#btnExport').onclick = () => {
  $('#expInfo').textContent = `${book.title}: ${pages.length} pages`; $('#expMsg').textContent = ''; open('#sheetExp');
};
$('#btnPdf').onclick = async () => {
  try {
    await waitOCR(); $('#expMsg').textContent = 'Building PDF...';
    const bytes = await buildPdf();
    $('#expMsg').textContent = await shareOrSave(new Blob([bytes], { type: 'application/pdf' }), safeName() + '.pdf', 'application/pdf');
  } catch (e) { console.error(e); $('#expMsg').textContent = 'Export failed: ' + e.message; }
};
$('#btnTxt').onclick = async () => {
  try {
    await waitOCR();
    $('#expMsg').textContent = await shareOrSave(new Blob([buildText()], { type: 'text/plain' }), safeName() + '.txt', 'text/plain');
  } catch (e) { $('#expMsg').textContent = 'Export failed: ' + e.message; }
};

async function openLibrary() {
  const all = (await dbAll('books')).sort((a, b) => b.created - a.created);
  const list = $('#bookList'); list.innerHTML = '';
  for (const b of all) {
    const n = (await dbPagesOf(b.id)).length;
    const d = document.createElement('div'); d.className = 'bk';
    d.innerHTML = `<div><b></b><small>${n} pages</small></div><button>Open</button><button class="x">Delete</button>`;
    d.querySelector('b').textContent = b.title;
    d.querySelector('b').onclick = () => { const t = prompt('Rename book', b.title); if (t) { b.title = t; dbPut('books', b).then(() => { if (book.id === b.id) { book.title = t; $('#bookTitle').textContent = t; } openLibrary(); }); } };
    d.children[1].onclick = async () => { await loadBook(b); closeAll(); };
    d.children[2].onclick = async () => {
      if (!confirm(`Delete "${b.title}" and its ${n} pages from this phone?`)) return;
      for (const p of await dbPagesOf(b.id)) await dbDel('pages', p.id);
      await dbDel('books', b.id);
      if (book.id === b.id) { const rest = (await dbAll('books')); if (rest.length) await loadBook(rest[0]); else await newBook(); }
      openLibrary();
    };
    list.appendChild(d);
  }
  open('#sheetLib');
}
$('#btnLib').onclick = openLibrary;
$('#btnNewBook').onclick = async () => { await newBook(); closeAll(); };

/* ---------- boot ---------- */
async function boot() {
  db = await openDB();
  applyMode();
  const all = await dbAll('books');
  const cur = localStorage.getItem('bs.current');
  const b = all.find((x) => x.id === cur) || all.sort((a, c) => c.created - a.created)[0];
  if (b) await loadBook(b); else await newBook();
  if ('serviceWorker' in navigator) navigator.serviceWorker.register('sw.js').catch(() => {});
  initOCR().catch(() => {});
  $('#btnBegin').onclick = async () => {
    try {
      $('#camErr').textContent = '';
      await openCamera();
      $('#splash').classList.add('hide');
      tick(); setStatus('Tap Start');
    } catch (e) {
      $('#camErr').textContent = 'Camera unavailable: ' + (e && e.message ? e.message : e) + '. Allow camera access in browser settings and reload.';
    }
  };
  window.__bs = { get pages() { return pages; }, get running() { return running; }, setRunning, S };
}
boot();
