'use strict';
(() => {
const COLS = 10, ROWS = 20;
const STORE = 'shogi-puzzle-v1';
// ---------- piece definitions ----------
const P = {
  I: {k:'飛', name:'飛車', ab:'列消し', color:'#00f0ff', m:['....','####','....','....'],
      desc:'横置き→その横1列を消す／縦置き→その縦1列を丸ごと消す'},
  T: {k:'角', name:'角行', ab:'斜め消し', color:'#ff2bd6', m:['.#.','###','...'],
      desc:'中心から斜め4方向へ最大3マスのブロックを消し、上のブロックが落ちて詰まる'},
  O: {k:'金', name:'金将', ab:'穴埋め', color:'#ffd23a', m:['##','##'],
      desc:'置いた2列と左右1列ずつ（計4列）の「上がふさがった穴」を金で埋める'},
  L: {k:'桂', name:'桂馬', ab:'跳び崩し', color:'#9dff3a', m:['..#','###','...'],
      desc:'着地点の真下から桂馬跳び（2つ下×1つ横、1つ下×2つ横）の4マスを壊し、列を詰める'},
  J: {k:'桂', name:'桂馬', ab:'跳び崩し', color:'#3affb0', m:['#..','###','...'],
      desc:''},
  S: {k:'歩', name:'歩兵', ab:'成りカウント', color:'#ff8a2b', m:['.##','##.','...'],
      desc:'能力なし。ただし5個置くと、次の駒が「と金」に成る'},
  Z: {k:'歩', name:'歩兵', ab:'成りカウント', color:'#ff5a3a', m:['##.','.##','...'],
      desc:''},
  P: {k:'と', name:'と金', ab:'穴もぐり', color:'#ff4f8b', m:['#'],
      desc:'1マスの万能駒。着地した列の下にある穴へもぐり込んで埋める（そろいそうな行を優先）'},
  K: {k:'王', name:'王将', ab:'大爆破', color:'#ffffff', m:['#'],
      desc:'まれに出現。着地点の下を中心に3×3を吹き飛ばし、列を詰める'},
  G: {k:'金', name:'金', ab:'', color:'#b89a2e', m:['#'], desc:''},
};
const BAG = ['I','T','O','L','J','S','Z'];
function toMat(rows){ return rows.map(r => [...r].map(ch => ch === '#')); }
function rotCW(m){ const n = m.length; return m.map((_, r) => m.map((__, c) => m[n-1-c][r])); }
const SHAPES = {};
for (const t of Object.keys(P)) {
  let m = toMat(P[t].m); SHAPES[t] = [m];
  for (let i = 1; i < 4; i++) { m = rotCW(m); SHAPES[t].push(m); }
}

// ---------- state ----------
let board, cur, queue, holdT, holdUsed, score, lines, level, combo, fuCount, bagLeft;
let running = false, paused = false, over = false;
let dropAcc = 0, lockTimer = 0, lockMoves = 0, softHeld = false, lastT = 0;
let particles = [], flashes = [], clearAnims = [];
let rng = Math.random;
let frozen = false;

function emptyBoard(){ return Array.from({length: ROWS}, () => Array(COLS).fill(null)); }
function nextFromBag(){
  if (!bagLeft || !bagLeft.length) {
    bagLeft = BAG.slice();
    for (let i = bagLeft.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i+1)); [bagLeft[i], bagLeft[j]] = [bagLeft[j], bagLeft[i]]; }
  }
  const t = bagLeft.pop();
  if (level >= 2 && rng() < 0.035) { bagLeft.push(t); return 'K'; }
  return t;
}
function fillQueue(){ while (queue.length < 3) queue.push(nextFromBag()); }
function makePiece(t){
  const m = SHAPES[t][0], n = m.length;
  return {t, rot: 0, x: Math.floor((COLS - n) / 2), y: t === 'I' ? -1 : 0};
}
function cellsOf(p, rot = p.rot, x = p.x, y = p.y){
  const m = SHAPES[p.t][rot], out = [];
  for (let r = 0; r < m.length; r++) for (let c = 0; c < m.length; c++) if (m[r][c]) out.push([x + c, y + r]);
  return out;
}
function collides(p, rot = p.rot, x = p.x, y = p.y){
  for (const [cx, cy] of cellsOf(p, rot, x, y)) {
    if (cx < 0 || cx >= COLS || cy >= ROWS) return true;
    if (cy >= 0 && board[cy][cx]) return true;
  }
  return false;
}
function spawn(t){
  cur = makePiece(t);
  holdUsed = holdUsed && false;
  dropAcc = 0; lockTimer = 0; lockMoves = 0;
  if (collides(cur)) { gameOver(); return false; }
  return true;
}
function spawnNext(){
  fillQueue();
  const t = queue.shift(); fillQueue();
  holdUsed = false;
  spawn(t); updateSide();
}
function gravityMs(){ return Math.max(70, 800 - (level - 1) * 75); }

// ---------- movement ----------
function move(dx){
  if (!canPlay()) return;
  if (!collides(cur, cur.rot, cur.x + dx, cur.y)) { cur.x += dx; touchLock(); }
}
function rotate(dir = 1){
  if (!canPlay() || cur.t === 'O' || SHAPES[cur.t][0].length === 1) return;
  const nr = (cur.rot + (dir > 0 ? 1 : 3)) % 4;
  const kicks = [[0,0],[-1,0],[1,0],[-2,0],[2,0],[0,-1],[-1,-1],[1,-1]];
  for (const [kx, ky] of kicks) {
    if (!collides(cur, nr, cur.x + kx, cur.y + ky)) { cur.rot = nr; cur.x += kx; cur.y += ky; touchLock(); return; }
  }
}
function touchLock(){ if (onGround() && lockMoves < 15) { lockTimer = 0; lockMoves++; } }
function onGround(){ return collides(cur, cur.rot, cur.x, cur.y + 1); }
function softDrop(){
  if (!canPlay()) return;
  if (!onGround()) { cur.y++; score += 1; dropAcc = 0; updateHud(); }
}
function ghostY(){ let y = cur.y; while (!collides(cur, cur.rot, cur.x, y + 1)) y++; return y; }
function hardDrop(){
  if (!canPlay()) return;
  const gy = ghostY(); score += 2 * (gy - cur.y); cur.y = gy; lockPiece();
}
function hold(){
  if (!canPlay() || holdUsed) return;
  const t = cur.t;
  if (holdT) { const h = holdT; holdT = t; spawn(h); }
  else { holdT = t; fillQueue(); const n = queue.shift(); fillQueue(); spawn(n); }
  holdUsed = true; updateSide();
}
function canPlay(){ return running && !paused && !over && cur; }

// ---------- abilities ----------
function compactCols(xs){
  for (const x of xs) {
    if (x < 0 || x >= COLS) continue;
    const col = [];
    for (let y = ROWS - 1; y >= 0; y--) if (board[y][x]) col.push(board[y][x]);
    for (let y = ROWS - 1, i = 0; y >= 0; y--, i++) board[y][x] = i < col.length ? col[i] : null;
  }
}
function removeRow(y){ board.splice(y, 1); board.unshift(Array(COLS).fill(null)); }
const inB = (x, y) => x >= 0 && x < COLS && y >= 0 && y < ROWS;

// returns {text, cells:[[x,y]], count, color} or null. `pc` = placed cells.
function applyAbility(t, pc, piece){
  const own = new Set(pc.map(([x, y]) => x + ',' + y));
  const res = {cells: [], count: 0, color: P[t].color, text: ''};
  if (t === 'I') {
    const ys = new Set(pc.map(c => c[1]));
    if (ys.size === 1) {               // horizontal -> clear row
      const y = pc[0][1];
      for (let x = 0; x < COLS; x++) if (board[y][x]) { res.cells.push([x, y]); res.count++; }
      removeRow(y); res.text = '飛車！横一列消し';
    } else {                           // vertical -> clear column
      const x = pc[0][0];
      for (let y = 0; y < ROWS; y++) if (board[y][x]) { res.cells.push([x, y]); res.count++; board[y][x] = null; }
      res.text = '飛車！縦一列消し';
    }
  } else if (t === 'T') {
    const cx = piece.x + 1, cy = piece.y + 1, xs = new Set();
    for (const [dx, dy] of [[1,1],[-1,1],[1,-1],[-1,-1]]) for (let d = 1; d <= 3; d++) {
      const x = cx + dx * d, y = cy + dy * d;
      if (inB(x, y) && board[y][x] && !own.has(x + ',' + y)) { res.cells.push([x, y]); board[y][x] = null; xs.add(x); res.count++; }
    }
    res.diag = [cx, cy];
    compactCols(xs); res.text = '角行！斜め消し';
  } else if (t === 'O') {
    const xs = pc.map(c => c[0]); const x0 = Math.min(...xs) - 1, x1 = Math.max(...xs) + 1;
    for (let x = x0; x <= x1; x++) {
      if (x < 0 || x >= COLS) continue;
      let top = -1; for (let y = 0; y < ROWS; y++) if (board[y][x]) { top = y; break; }
      if (top < 0) continue;
      for (let y = top + 1; y < ROWS; y++) if (!board[y][x]) { board[y][x] = 'G'; res.cells.push([x, y]); res.count++; }
    }
    res.text = '金将！穴埋め';
  } else if (t === 'L' || t === 'J') {
    const ymax = Math.max(...pc.map(c => c[1]));
    const bx = pc.filter(c => c[1] === ymax).map(c => c[0]);
    const ox = Math.round((Math.min(...bx) + Math.max(...bx)) / 2);
    const xs = new Set();
    for (const [dx, dy] of [[-1,2],[1,2],[-2,1],[2,1]]) {
      const x = ox + dx, y = ymax + dy;
      if (inB(x, y) && board[y][x] && !own.has(x + ',' + y)) { res.cells.push([x, y]); board[y][x] = null; xs.add(x); res.count++; }
    }
    res.origin = [ox, ymax];
    compactCols(xs); res.text = '桂馬！跳び崩し';
  } else if (t === 'S' || t === 'Z') {
    fuCount++;
    if (fuCount >= 5) {
      fuCount = 0; fillQueue(); queue[0] = 'P';
      res.text = '歩兵5枚！と金に成る'; res.promo = true;
    } else return {cells: [], count: 0, color: P[t].color, text: '', fu: true};
  } else if (t === 'P') {
    const [x, y] = pc[0]; let best = -1, bestFill = -1;
    for (let yy = y + 1; yy < ROWS; yy++) if (!board[yy][x]) {
      const f = board[yy].filter(Boolean).length;
      if (f >= bestFill) { bestFill = f; best = yy; }
    }
    if (best >= 0) { board[y][x] = null; board[best][x] = 'P'; res.cells.push([x, best]); res.count = 1; res.text = 'と金！穴もぐり'; }
    else res.text = 'と金！';
  } else if (t === 'K') {
    const [x, y] = pc[0]; const cy = y + 1, xs = new Set();
    for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
      const xx = x + dx, yy = cy + dy;
      if (inB(xx, yy) && board[yy][xx]) { res.cells.push([xx, yy]); board[yy][xx] = null; xs.add(xx); res.count++; }
    }
    compactCols(xs); res.text = '王将！大爆破';
  }
  return res;
}

function clearLines(){
  const full = [];
  for (let y = 0; y < ROWS; y++) if (board[y].every(Boolean)) full.push(y);
  for (const y of full) { removeRow(y); }
  return full;
}

function lockPiece(){
  const pc = cellsOf(cur);
  if (pc.some(([, y]) => y < 0)) { gameOver(); return; }
  for (const [x, y] of pc) board[y][x] = cur.t;
  const t = cur.t, piece = {...cur};
  const ab = applyAbility(t, pc, piece);
  const full = clearLines();
  // scoring
  let gained = 0, active = false;
  if (ab && ab.count > 0) { gained += (50 + 15 * ab.count) * level; active = true; }
  if (full.length) { gained += [0, 100, 300, 500, 800][Math.min(4, full.length)] * level; active = true; }
  if (active) { combo++; if (combo > 0) gained += 50 * combo * level; } else combo = -1;
  score += gained; lines += full.length;
  const nl = Math.floor(lines / 10) + 1; if (nl > level) { level = nl; toast('LEVEL ' + level, '#9dff3a'); }
  // effects
  if (ab && ab.text) {
    effect(ab, t);
    const extra = ab.count > 0 ? ' +' + ab.count : '';
    toast(ab.text + extra, ab.color);
  }
  if (full.length) {
    for (const y of full) flashes.push({y, life: 1, color: '#ffffff'});
    for (const y of full) for (let x = 0; x < COLS; x++) burst(x, y, '#00f0ff', 4);
    if (!ab || !ab.text || ab.fu) toast(full.length >= 4 ? 'TETRA!! ' + full.length + 'ライン' : full.length + 'ライン', '#00f0ff');
  }
  if (combo > 0) toastCombo(combo);
  lastLock = {type: t, ability: ab, lines: full.length, gained};
  cur = null;
  updateHud();
  if (!over) spawnNext();
}
let lastLock = null;

// ---------- effects ----------
let CS = 26, DPR = 1;
function burst(x, y, color, n = 8){
  for (let i = 0; i < n; i++) {
    const a = rng() * Math.PI * 2, s = 0.06 + rng() * 0.22;
    particles.push({x: x + 0.5, y: y + 0.5, vx: Math.cos(a) * s, vy: Math.sin(a) * s - 0.05, life: 1, color, r: 1 + rng() * 2.2});
  }
}
function effect(ab, t){
  const c = ab.color;
  for (const [x, y] of ab.cells) { burst(x, y, c, 10); clearAnims.push({x, y, life: 1, color: c}); }
  screenFlash = {color: c, life: 1};
  if (ab.promo) screenFlash.color = '#ff4f8b';
}
let screenFlash = null;
let toastTimer = 0;
function toast(text, color){
  const el = document.getElementById('toast'); if (!el) return;
  el.textContent = text; el.style.color = color;
  el.style.textShadow = `0 0 8px ${color}, 0 0 22px ${color}`;
  el.classList.remove('show'); void el.offsetWidth; el.classList.add('show');
}
function toastCombo(n){ const el = document.getElementById('combo'); if (el) el.textContent = n + ' COMBO'; }

// ---------- rendering ----------
const cv = document.getElementById('board'), ctx = cv.getContext('2d');
const sprites = {};
function makeSprite(t, cs, ghost = false){
  const g = Math.ceil(cs * 0.35), size = cs + g * 2;
  const c = document.createElement('canvas'); c.width = size * DPR; c.height = size * DPR;
  const x = c.getContext('2d'); x.scale(DPR, DPR);
  const col = P[t].color, r = Math.max(3, cs * 0.18), pad = 1.5;
  const rr = (X, Y, W, H) => { x.beginPath(); x.moveTo(X + r, Y); x.arcTo(X + W, Y, X + W, Y + H, r); x.arcTo(X + W, Y + H, X, Y + H, r); x.arcTo(X, Y + H, X, Y, r); x.arcTo(X, Y, X + W, Y, r); x.closePath(); };
  if (ghost) {
    rr(g + pad, g + pad, cs - pad * 2, cs - pad * 2); x.strokeStyle = col; x.globalAlpha = 0.45; x.lineWidth = 1.5; x.stroke();
    return c;
  }
  x.shadowColor = col; x.shadowBlur = g * 0.9;
  rr(g + pad, g + pad, cs - pad * 2, cs - pad * 2);
  const grad = x.createLinearGradient(0, g, 0, g + cs);
  grad.addColorStop(0, hexA(col, t === 'G' ? 0.35 : 0.55)); grad.addColorStop(1, hexA(col, t === 'G' ? 0.12 : 0.18));
  x.fillStyle = grad; x.fill();
  x.lineWidth = Math.max(1.5, cs * 0.07); x.strokeStyle = col; x.stroke();
  x.shadowBlur = g * 0.6; x.fillStyle = '#ffffff';
  x.font = `900 ${Math.floor(cs * 0.6)}px "Hiragino Mincho ProN","Noto Serif JP","Noto Serif CJK JP",serif`;
  x.textAlign = 'center'; x.textBaseline = 'middle';
  if (t !== 'G') x.fillText(P[t].k, g + cs / 2, g + cs / 2 + cs * 0.03);
  return c;
}
function hexA(hex, a){ const n = parseInt(hex.slice(1), 16); return `rgba(${n >> 16 & 255},${n >> 8 & 255},${n & 255},${a})`; }
function buildSprites(){
  for (const t of Object.keys(P)) { sprites[t] = makeSprite(t, CS); sprites[t + '_g'] = makeSprite(t, CS, true); }
}
function drawSprite(c2, key, px, py, cs, alpha = 1){
  const s = sprites[key]; const g = Math.ceil(CS * 0.35);
  const scale = cs / CS;
  c2.globalAlpha = alpha;
  c2.drawImage(s, px - g * scale, py - g * scale, (CS + 2 * g) * scale, (CS + 2 * g) * scale);
  c2.globalAlpha = 1;
}
function render(){
  const W = COLS * CS, H = ROWS * CS;
  ctx.setTransform(DPR, 0, 0, DPR, 0, 0);
  ctx.fillStyle = '#05050d'; ctx.fillRect(0, 0, W, H);
  ctx.strokeStyle = 'rgba(0,240,255,0.07)'; ctx.lineWidth = 1;
  ctx.beginPath();
  for (let x = 1; x < COLS; x++) { ctx.moveTo(x * CS + .5, 0); ctx.lineTo(x * CS + .5, H); }
  for (let y = 1; y < ROWS; y++) { ctx.moveTo(0, y * CS + .5); ctx.lineTo(W, y * CS + .5); }
  ctx.stroke();
  for (let y = 0; y < ROWS; y++) for (let x = 0; x < COLS; x++) { const t = board[y][x]; if (t) drawSprite(ctx, t, x * CS, y * CS, CS, 0.88); }
  if (cur && !over) {
    const gy = ghostY();
    for (const [x, y] of cellsOf(cur, cur.rot, cur.x, gy)) if (y >= 0) drawSprite(ctx, cur.t + '_g', x * CS, y * CS, CS);
    for (const [x, y] of cellsOf(cur)) if (y >= 0) drawSprite(ctx, cur.t, x * CS, y * CS, CS);
  }
  ctx.globalCompositeOperation = 'lighter';
  for (const a of clearAnims) {
    ctx.globalAlpha = a.life; ctx.fillStyle = a.color;
    const s = CS * (1 + (1 - a.life) * 0.8), o = (s - CS) / 2;
    ctx.fillRect(a.x * CS - o, a.y * CS - o, s, s);
  }
  for (const f of flashes) { ctx.globalAlpha = f.life * 0.8; ctx.fillStyle = f.color; ctx.fillRect(0, f.y * CS, W, CS); }
  for (const p of particles) {
    ctx.globalAlpha = Math.max(0, p.life); ctx.fillStyle = p.color;
    ctx.beginPath(); ctx.arc(p.x * CS, p.y * CS, p.r * (CS / 26), 0, Math.PI * 2); ctx.fill();
  }
  if (screenFlash) { ctx.globalAlpha = screenFlash.life * 0.22; ctx.fillStyle = screenFlash.color; ctx.fillRect(0, 0, W, H); }
  ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
}
function stepFx(dt){
  const k = dt / 16.7;
  for (const p of particles) { p.x += p.vx * k; p.y += p.vy * k; p.vy += 0.012 * k; p.life -= 0.022 * k; }
  particles = particles.filter(p => p.life > 0);
  for (const a of clearAnims) a.life -= 0.05 * k; clearAnims = clearAnims.filter(a => a.life > 0);
  for (const f of flashes) f.life -= 0.06 * k; flashes = flashes.filter(f => f.life > 0);
  if (screenFlash) { screenFlash.life -= 0.05 * k; if (screenFlash.life <= 0) screenFlash = null; }
}
function drawMini(canvas, t, size){
  const c2 = canvas.getContext('2d');
  canvas.width = size * DPR; canvas.height = size * DPR; canvas.style.width = size + 'px'; canvas.style.height = size + 'px';
  c2.setTransform(DPR, 0, 0, DPR, 0, 0); c2.clearRect(0, 0, size, size);
  if (!t) return;
  const m = SHAPES[t][0];
  let minR = 9, maxR = -1, minC = 9, maxC = -1;
  m.forEach((row, r) => row.forEach((v, c) => { if (v) { minR = Math.min(minR, r); maxR = Math.max(maxR, r); minC = Math.min(minC, c); maxC = Math.max(maxC, c); } }));
  const w = maxC - minC + 1, h = maxR - minR + 1;
  const cs = Math.min(size * 0.8 / Math.max(w, 2), size * 0.8 / 2.2, CS);
  const ox = (size - w * cs) / 2, oy = (size - h * cs) / 2;
  m.forEach((row, r) => row.forEach((v, c) => { if (v) drawSprite(c2, t, ox + (c - minC) * cs, oy + (r - minR) * cs, cs); }));
}

// ---------- HUD ----------
const $ = id => document.getElementById(id);
function updateHud(){
  $('score').textContent = score; $('level').textContent = level; $('lines').textContent = lines;
  if (combo <= 0) $('combo').textContent = '-';
  const fm = $('fuMeter'); fm.innerHTML = '';
  for (let i = 0; i < 5; i++) { const e = document.createElement('i'); if (i < fuCount) e.className = 'on'; fm.appendChild(e); }
}
function sideSize(){ return Math.floor(parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--side')) - 8); }
function updateSide(){
  const s = sideSize();
  drawMini($('holdCv'), holdT, s); $('holdName').textContent = holdT ? P[holdT].k + ' ' + P[holdT].name : '-';
  fillQueue();
  const n = queue[0];
  drawMini($('nextCv'), n, s); $('nextName').textContent = P[n].k + ' ' + P[n].name; $('nextAb').textContent = P[n].ab;
  drawMini($('next2Cv'), queue[1], Math.floor(s * 0.7)); drawMini($('next3Cv'), queue[2], Math.floor(s * 0.7));
  updateHud();
}

// ---------- layout ----------
function layout(){
  DPR = Math.min(window.devicePixelRatio || 1, 3);
  const W = window.innerWidth;
  const side = W < 360 ? 56 : 64;
  document.documentElement.style.setProperty('--side', side + 'px');
  const hud = $('hud').offsetHeight, ctr = $('controls').offsetHeight;
  const app = $('app'), cs = getComputedStyle(app);
  const padV = parseFloat(cs.paddingTop) + parseFloat(cs.paddingBottom);
  const padH = parseFloat(cs.paddingLeft) + parseFloat(cs.paddingRight);
  const availH = window.innerHeight - hud - ctr - padV - 12;
  const availW = W - padH - side * 2 - 24;
  CS = Math.max(12, Math.floor(Math.min(availH / ROWS, availW / COLS)));
  cv.width = COLS * CS * DPR; cv.height = ROWS * CS * DPR;
  cv.style.width = COLS * CS + 'px'; cv.style.height = ROWS * CS + 'px';
  buildSprites();
  if (queue) updateSide();
  if (board) render();
}
window.addEventListener('resize', layout);

// ---------- loop ----------
function loop(ts){
  const dt = Math.min(50, ts - (lastT || ts)); lastT = ts;
  if (running && !paused && !over && cur && !frozen) {
    dropAcc += dt;
    const g = softHeld ? Math.min(40, gravityMs()) : gravityMs();
    while (dropAcc >= g && cur) {
      dropAcc -= g;
      if (!onGround()) { cur.y++; if (softHeld) score++; } else break;
    }
    if (cur && onGround()) { lockTimer += dt; if (lockTimer >= 500) lockPiece(); }
    else lockTimer = 0;
    if (softHeld) updateHud();
  }
  stepFx(dt);
  if (board) render();
  requestAnimationFrame(loop);
}

// ---------- game flow ----------
function newGame(seed){
  board = emptyBoard(); queue = []; bagLeft = []; holdT = null; holdUsed = false;
  score = 0; lines = 0; level = 1; combo = -1; fuCount = 0; over = false; paused = false; running = true;
  particles = []; flashes = []; clearAnims = []; screenFlash = null; lastLock = null;
  showOverlay(null); spawnNext(); updateHud();
}
function gameOver(){
  over = true; running = false; cur = null;
  const data = loadBest(); const entry = {score, lines, level, date: new Date().toISOString().slice(0, 10)};
  data.push(entry); data.sort((a, b) => b.score - a.score); const top = data.slice(0, 5);
  try { localStorage.setItem(STORE, JSON.stringify({best: top})); } catch (e) {}
  $('finalScore').textContent = score;
  $('newBest').textContent = top[0] === entry && score > 0 ? '★ ハイスコア更新！' : '';
  renderBest('bestList2'); showOverlay('over');
}
function loadBest(){ try { return (JSON.parse(localStorage.getItem(STORE)) || {}).best || []; } catch (e) { return []; } }
function renderBest(id){
  const b = loadBest(); const el = $(id);
  el.innerHTML = b.length ? '<b>ハイスコア</b><br>' + b.map((e, i) => `${i + 1}. ${e.score}点（Lv${e.level}・${e.lines}ライン）`).join('<br>') : 'ハイスコアはまだありません';
}
let howFrom = 'title';
function showOverlay(id){
  for (const o of document.querySelectorAll('.overlay')) o.classList.toggle('show', o.id === id);
}
function pause(){ if (running && !over && !paused) { paused = true; softHeld = false; showOverlay('pause'); } }
function resume(){ if (paused) { paused = false; lastT = 0; showOverlay(null); } }
document.addEventListener('visibilitychange', () => { if (document.hidden) pause(); });
window.addEventListener('pagehide', pause);
window.addEventListener('blur', pause);

function buildLegend(){
  const L = $('legend'); L.innerHTML = '';
  for (const t of ['I', 'T', 'O', 'L', 'S', 'P', 'K']) {
    const row = document.createElement('div'); row.className = 'lg';
    const c = document.createElement('canvas'); row.appendChild(c);
    const shapeLbl = {I: 'I型', T: 'T型', O: 'O型', L: 'L/J型', S: 'S/Z型', P: '1マス', K: '1マス'}[t];
    const d = document.createElement('div');
    d.innerHTML = `<div class="t" style="color:${P[t].color};text-shadow:0 0 8px ${P[t].color}">${P[t].k} ${P[t].name}（${shapeLbl}）— ${P[t].ab}</div><div class="d">${P[t].desc}</div>`;
    row.appendChild(d); L.appendChild(row);
    drawMini(c, t, 56);
  }
}

// ---------- input ----------
const ACT = {left: () => move(-1), right: () => move(1), rotate: () => rotate(1), soft: () => softDrop(), hard: hardDrop, hold};
for (const b of document.querySelectorAll('.cbtn')) {
  const act = b.dataset.act; let rep = null, del = null;
  const stop = () => { clearTimeout(del); clearInterval(rep); b.classList.remove('press'); if (act === 'soft') softHeld = false; };
  b.addEventListener('pointerdown', e => {
    e.preventDefault(); b.classList.add('press');
    try { b.setPointerCapture(e.pointerId); } catch (_) {}
    ACT[act]();
    if (act === 'left' || act === 'right') { del = setTimeout(() => { rep = setInterval(ACT[act], 55); }, 170); }
    if (act === 'soft') softHeld = true;
  });
  b.addEventListener('pointerup', stop); b.addEventListener('pointercancel', stop); b.addEventListener('lostpointercapture', stop);
  b.addEventListener('contextmenu', e => e.preventDefault());
}
// gestures on board
let gs = null;
cv.addEventListener('pointerdown', e => { e.preventDefault(); gs = {x: e.clientX, y: e.clientY, t: performance.now(), mx: 0, moved: false, id: e.pointerId}; try { cv.setPointerCapture(e.pointerId); } catch (_) {} });
cv.addEventListener('pointermove', e => {
  if (!gs || e.pointerId !== gs.id) return;
  const dx = e.clientX - gs.x, step = Math.max(18, CS * 0.9);
  const cells = Math.trunc(dx / step);
  while (gs.mx < cells) { move(1); gs.mx++; gs.moved = true; }
  while (gs.mx > cells) { move(-1); gs.mx--; gs.moved = true; }
});
cv.addEventListener('pointerup', e => {
  if (!gs || e.pointerId !== gs.id) return;
  const dx = e.clientX - gs.x, dy = e.clientY - gs.y, dtm = performance.now() - gs.t;
  if (!gs.moved && dy > 50 && dy > Math.abs(dx) * 1.5 && dtm < 400) hardDrop();
  else if (!gs.moved && Math.abs(dx) < 10 && Math.abs(dy) < 10 && dtm < 300) rotate(1);
  gs = null;
});
cv.addEventListener('pointercancel', () => { gs = null; });
document.addEventListener('keydown', e => {
  const k = e.key;
  if (k === 'p' || k === 'P' || k === 'Escape') { paused ? resume() : pause(); e.preventDefault(); return; }
  if (!canPlay()) { if ((k === 'Enter' || k === ' ') && !running) { newGame(); e.preventDefault(); } return; }
  const map = {ArrowLeft: () => move(-1), ArrowRight: () => move(1), ArrowDown: softDrop, ArrowUp: () => rotate(1), x: () => rotate(1), X: () => rotate(1), z: () => rotate(-1), Z: () => rotate(-1), ' ': hardDrop, c: hold, C: hold, Shift: hold};
  if (map[k]) { map[k](); e.preventDefault(); }
});
document.addEventListener('gesturestart', e => e.preventDefault());
document.addEventListener('dblclick', e => e.preventDefault());
document.addEventListener('touchmove', e => { if (!e.target.closest('.overlay')) e.preventDefault(); }, {passive: false});

$('btnStart').onclick = () => newGame();
$('btnHow').onclick = () => { howFrom = 'title'; showOverlay('howto'); };
$('btnHow2').onclick = () => { howFrom = 'pause'; showOverlay('howto'); };
$('btnHowClose').onclick = () => showOverlay(howFrom);
$('btnPause').onclick = () => (paused ? resume() : pause());
$('btnResume').onclick = resume;
$('btnQuit').onclick = () => { running = false; paused = false; cur = null; renderBest('bestList'); showOverlay('title'); };
$('btnRetry').onclick = () => newGame();
$('btnTitle').onclick = () => { renderBest('bestList'); showOverlay('title'); };

// ---------- test hooks ----------
window.__test = {
  P, SHAPES,
  start(){ newGame(); },
  setBoard(rows){ // rows: array of strings top->bottom (any length <=20, aligned to bottom). '.' empty, other char = block type ('#' -> 'G')
    board = emptyBoard(); const off = ROWS - rows.length;
    rows.forEach((r, i) => [...r].forEach((ch, x) => { if (ch !== '.') board[off + i][x] = ch === '#' ? 'G' : ch; }));
  },
  getBoard(){ return board.map(r => r.map(c => c ? (c === 'G' ? '#' : c) : '.').join('')); },
  spawn(t, rot = 0, x){ cur = makePiece(t); cur.rot = rot; if (x !== undefined) cur.x = x; return !collides(cur); },
  cells(){ return cur ? cellsOf(cur) : null; },
  drop(){ hardDrop(); return lastLock; },
  lock(){ lockPiece(); return lastLock; },
  state(){ return {score, lines, level, combo, fuCount, over, running, paused, queue: queue.slice(), hold: holdT, cur: cur && {...cur}}; },
  setFu(n){ fuCount = n; },
  setQueue(q){ queue = q.slice(); },
  pause, resume, hold, move, rotate, softDrop,
  seed(s){ let a = s >>> 0; rng = () => { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; },
  freeze(v = true){ frozen = v; softHeld = false; },
};

// ---------- boot ----------
board = emptyBoard(); queue = []; bagLeft = []; score = 0; lines = 0; level = 1; combo = -1; fuCount = 0;
layout(); buildLegend(); renderBest('bestList'); fillQueue(); updateSide();
requestAnimationFrame(loop);
})();
