'use strict';
(() => {
const COLS = 10, ROWS = 20;
const STORE = 'shogi-puzzle-v1';
// ---------- piece definitions ----------
const P = {
  I: {k:'飛', name:'飛車', ab:'縦埋め', color:'#00f0ff', m:['....','####','....','....'],
      desc:'飛車で列をそろえると、次の駒に「飛車の力」。次の駒が着地した列の穴を、上から下まで全部埋める（最強）'},
  T: {k:'角', name:'角行', ab:'斜め埋め', color:'#ff2bd6', m:['.#.','###','...'],
      desc:'角で列をそろえると「角の力」。次の駒の中心から斜め4方向（各3マス）にある穴を埋める'},
  O: {k:'金', name:'金将', ab:'小埋め', color:'#ffd23a', m:['##','##'],
      desc:'金で列をそろえると「金の力」。次の駒の列の穴を、近い順に最大2マスだけ埋める'},
  L: {k:'桂', name:'桂馬', ab:'桂馬埋め', color:'#9dff3a', m:['..#','###','...'],
      desc:'桂馬（L/J）で列をそろえると「桂馬の力」。次の駒の中心から桂馬跳び8か所にある穴を埋める'},
  J: {k:'桂', name:'桂馬', ab:'桂馬埋め', color:'#3affb0', m:['#..','###','...'], desc:''},
  S: {k:'歩', name:'歩兵', ab:'なし（成り）', color:'#ff8a2b', m:['.##','##.','...'],
      desc:'能力なし（そろえても力は宿らない）。5個置くと次の駒が「と金」に成る'},
  Z: {k:'歩', name:'歩兵', ab:'なし（成り）', color:'#ff5a3a', m:['##.','.##','...'], desc:''},
  P: {k:'と', name:'と金', ab:'すり抜け埋め', color:'#ff4f8b', m:['#'],
      desc:'いつでも自動発動。ブロックをすり抜けて、その列の一番そろいそうな穴に入って埋める'},
  K: {k:'王', name:'王将', ab:'キングスフィールド', color:'#ffffff', m:['#'],
      desc:'飛・角・金・桂・歩（成り）・と の6つが全部1回ずつ発動すると登場。すり抜けで穴に入り、自分を中心に5×5の24マスを全部埋める'},
  G: {k:'', name:'ブロック', ab:'', color:'#8a90a8', m:['#'], desc:''},
  F: {k:'◇', name:'埋め', ab:'', color:'#c9a0ff', m:['#'], desc:''},
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

// ---------- abilities: all hole-filling ----------
const TRACK = ['I', 'T', 'O', 'L', 'S', 'P'];            // 飛 角 金 桂 歩(成り) と
let charge = null, fired = new Set(), kingPending = false;
function chargeOf(t){ return t === 'J' ? 'L' : ('ITOL'.includes(t) ? t : null); }
function removeRow(y){ board.splice(y, 1); board.unshift(Array(COLS).fill(null)); }
const inB = (x, y) => x >= 0 && x < COLS && y >= 0 && y < ROWS;
function isHole(x, y){
  if (!inB(x, y) || board[y][x]) return false;
  for (let yy = y - 1; yy >= 0; yy--) if (board[yy][x]) return true;
  return false;
}
function centerCell(pc){
  const mx = pc.reduce((a, c) => a + c[0], 0) / pc.length, my = pc.reduce((a, c) => a + c[1], 0) / pc.length;
  let best = pc[0], bd = 1e9;
  for (const c of pc) { const d = (c[0] - mx) ** 2 + (c[1] - my) ** 2; if (d < bd - 1e-9 || (Math.abs(d - bd) < 1e-9 && c[1] > best[1])) { bd = d; best = c; } }
  return best;
}
function fireCharge(c, pc){
  const res = {cells: [], count: 0, color: P[c].color, key: c, charge: true};
  const fill = (x, y) => { if (isHole(x, y)) { board[y][x] = 'F'; res.cells.push([x, y]); res.count++; } };
  const xs = [...new Set(pc.map(p => p[0]))];
  if (c === 'I') {
    for (const x of xs) for (let y = 0; y < ROWS; y++) fill(x, y);
    res.text = '飛車の力！縦埋め';
  } else if (c === 'T') {
    const [cx, cy] = centerCell(pc);
    for (let d = 1; d <= 3; d++) for (const [dx, dy] of [[1,1],[-1,1],[1,-1],[-1,-1]]) fill(cx + dx * d, cy + dy * d);
    res.text = '角の力！斜め埋め';
  } else if (c === 'L') {
    const [cx, cy] = centerCell(pc);
    for (const [dx, dy] of [[-1,2],[1,2],[-2,1],[2,1],[-2,-1],[2,-1],[-1,-2],[1,-2]]) fill(cx + dx, cy + dy);
    res.text = '桂馬の力！桂馬埋め';
  } else if (c === 'O') {
    const cand = [];
    for (const x of xs) {
      const bottom = Math.max(...pc.filter(p => p[0] === x).map(p => p[1]));
      for (let y = bottom + 1; y < ROWS; y++) if (isHole(x, y)) cand.push([x, y, y - bottom]);
    }
    cand.sort((a, b) => a[2] - b[2] || a[0] - b[0]);
    for (const [x, y] of cand.slice(0, 2)) fill(x, y);
    res.text = '金の力！小埋め';
  }
  return res;
}
// と金/王: slip down through blocks into the most useful hole of its column
function slip(x, y){
  let best = -1, bestFill = -1;
  for (let yy = y + 1; yy < ROWS; yy++) if (!board[yy][x]) {
    const f = board[yy].filter(Boolean).length;
    if (f >= bestFill) { bestFill = f; best = yy; }
  }
  if (best < 0) return y;
  board[best][x] = board[y][x]; board[y][x] = null; return best;
}
function clearLines(){
  const full = [];
  for (let y = 0; y < ROWS; y++) if (board[y].every(Boolean)) full.push(y);
  for (const y of full) removeRow(y);
  return full;
}
function lockPiece(){
  const pc = cellsOf(cur);
  if (pc.some(([, y]) => y < 0)) { gameOver(); return; }
  for (const [x, y] of pc) board[y][x] = cur.t;
  const t = cur.t, used = charge; charge = null;
  const evs = []; let fillCount = 0, kfCount = 0, pos = pc;
  if (t === 'P' || t === 'K') {
    const [x, y] = pc[0], ny = slip(x, y); pos = [[x, ny]];
    const e = {cells: ny !== y ? [[x, ny]] : [], count: ny !== y ? 1 : 0, color: P[t].color, key: t};
    if (t === 'P') { e.text = ny !== y ? 'と金！すり抜け埋め' : 'と金！'; fired.add('P'); fillCount += e.count; }
    else {
      for (let dy = -2; dy <= 2; dy++) for (let dx = -2; dx <= 2; dx++) {
        const xx = x + dx, yy = ny + dy;
        if ((dx || dy) && inB(xx, yy) && !board[yy][xx]) { board[yy][xx] = 'F'; e.cells.push([xx, yy]); e.count++; }
      }
      e.text = 'キングスフィールド！'; e.king = true; e.center = [x, ny]; kfCount = e.count;
    }
    evs.push(e);
  }
  if (used) { const e = fireCharge(used, pos); fired.add(used); fillCount += e.count; evs.push(e); }
  if (t === 'S' || t === 'Z') {
    fuCount++;
    if (fuCount >= 5) { fuCount = 0; fillQueue(); queue[0] = 'P'; fired.add('S'); evs.push({cells: [], count: 0, color: P.P.color, text: '歩兵5枚！と金に成る', promo: true}); }
  }
  const full = clearLines();
  const newCharge = full.length ? chargeOf(t) : null;
  charge = newCharge;
  if (t === 'K') { fired.clear(); kingPending = false; }
  else if (!kingPending && TRACK.every(k => fired.has(k))) {
    kingPending = true; fillQueue();
    if (queue[0] === 'P') queue.splice(1, 0, 'K'); else queue.unshift('K');
    evs.push({cells: [], count: 0, color: '#ffffff', text: '王将、出陣！', kingCall: true});
  }
  // scoring
  let gained = 0;
  if (fillCount > 0) gained += (40 + 30 * fillCount) * level;
  if (kfCount > 0) gained += (500 + 60 * kfCount) * level;
  if (full.length) gained += [0, 100, 300, 500, 800][Math.min(4, full.length)] * level;
  const active = full.length > 0 || fillCount > 0 || kfCount > 0;
  if (active) { combo++; if (combo > 0) gained += 50 * combo * level; } else combo = -1;
  score += gained; lines += full.length;
  const nl = Math.floor(lines / 10) + 1; const lvUp = nl > level; if (lvUp) level = nl;
  // effects + text
  for (const e of evs) effect(e);
  if (full.length) {
    for (const y of full) flashes.push({y, life: 1, color: '#ffffff'});
    for (const y of full) for (let x = 0; x < COLS; x++) burst(x, y, '#00f0ff', 4);
  }
  const msg = [];
  const main = evs.find(e => e.king) || evs.find(e => e.charge) || evs.find(e => e.key === 'P') || evs.find(e => e.promo);
  if (main) msg.push(main.text + (main.count > 0 ? ' +' + main.count : ''));
  if (full.length) msg.push(full.length >= 4 ? 'TETRA!! ' + full.length + 'ライン' : full.length + 'ライン');
  if (newCharge) msg.push('⚡ ' + P[newCharge].name + 'の力 チャージ');
  if (evs.some(e => e.kingCall)) msg.push('王将、出陣！');
  if (lvUp) msg.push('LEVEL ' + level);
  if (msg.length) toast(msg.join('\n'), main ? main.color : (newCharge ? P[newCharge].color : '#00f0ff'));
  if (combo > 0) toastCombo(combo);
  lastLock = {type: t, used, events: evs.map(e => ({text: e.text, count: e.count})), fills: fillCount, kf: kfCount, lines: full.length, gained, charge};
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
let rings = [];
function effect(ab){
  const c = ab.color;
  for (const [x, y] of ab.cells) { burst(x, y, c, ab.king ? 14 : 10); clearAnims.push({x, y, life: 1, color: c}); }
  if (ab.cells.length || ab.promo || ab.kingCall) screenFlash = {color: c, life: 1};
  if (ab.king) {
    const [x, y] = ab.center;
    rings.push({x, y, r: 0, life: 1, color: '#ffffff'}, {x, y, r: -0.8, life: 1.2, color: '#ffd23a'}, {x, y, r: -1.6, life: 1.4, color: '#ff2bd6'});
    for (let i = 0; i < 60; i++) burst(x, y, ['#ffffff', '#ffd23a', '#00f0ff', '#ff2bd6'][i % 4], 1);
    screenFlash = {color: '#ffffff', life: 1.6};
  }
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
  grad.addColorStop(0, hexA(col, t === 'G' ? 0.35 : t === 'F' ? 0.7 : 0.55)); grad.addColorStop(1, hexA(col, t === 'G' ? 0.12 : t === 'F' ? 0.3 : 0.18));
  x.fillStyle = grad; x.fill();
  x.lineWidth = Math.max(1.5, cs * 0.07); x.strokeStyle = col; x.stroke();
  x.shadowBlur = g * 0.6; x.fillStyle = '#ffffff';
  x.font = `900 ${Math.floor(cs * 0.6)}px "Hiragino Mincho ProN","Noto Serif JP","Noto Serif CJK JP",serif`;
  x.textAlign = 'center'; x.textBaseline = 'middle';
  if (P[t].k) x.fillText(P[t].k, g + cs / 2, g + cs / 2 + cs * 0.03);
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
    if (charge) drawAura(cellsOf(cur));
    for (const [x, y] of cellsOf(cur)) if (y >= 0) drawSprite(ctx, cur.t, x * CS, y * CS, CS);
    if (charge) drawAuraLabel(cellsOf(cur));
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
  for (const g of rings) if (g.r > 0) {
    ctx.globalAlpha = Math.max(0, Math.min(1, g.life)); ctx.strokeStyle = g.color; ctx.lineWidth = CS * 0.25;
    ctx.beginPath(); ctx.arc((g.x + .5) * CS, (g.y + .5) * CS, g.r * CS, 0, Math.PI * 2); ctx.stroke();
  }
  if (screenFlash) { ctx.globalAlpha = Math.min(1, screenFlash.life) * 0.22; ctx.fillStyle = screenFlash.color; ctx.fillRect(0, 0, W, H); }
  ctx.globalAlpha = 1; ctx.globalCompositeOperation = 'source-over';
}
function drawAura(cells){
  const col = P[charge].color, pulse = 0.55 + 0.45 * Math.sin(performance.now() / 160);
  ctx.save(); ctx.globalCompositeOperation = 'lighter';
  ctx.shadowColor = col; ctx.shadowBlur = CS * (0.6 + 0.6 * pulse);
  ctx.strokeStyle = col; ctx.lineWidth = Math.max(2, CS * 0.12); ctx.globalAlpha = 0.5 + 0.5 * pulse;
  for (const [x, y] of cells) if (y >= 0) ctx.strokeRect(x * CS - 2, y * CS - 2, CS + 4, CS + 4);
  ctx.globalAlpha = 0.18 * pulse; ctx.fillStyle = col;
  for (const [x, y] of cells) if (y >= 0) ctx.fillRect(x * CS - 3, y * CS - 3, CS + 6, CS + 6);
  ctx.restore();
}
function drawAuraLabel(cells){
  const col = P[charge].color;
  const minY = Math.min(...cells.map(c => c[1])), maxY = Math.max(...cells.map(c => c[1]));
  const cx = (Math.min(...cells.map(c => c[0])) + Math.max(...cells.map(c => c[0])) + 1) / 2 * CS;
  let ty = minY * CS - CS * 0.35; if (ty < CS * 0.5) ty = (maxY + 1) * CS + CS * 0.55;
  const txt = '⚡' + P[charge].name + 'の力';
  ctx.save(); ctx.font = `900 ${Math.max(11, Math.floor(CS * 0.55))}px -apple-system,"Hiragino Sans","Noto Sans JP",sans-serif`;
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  const w = ctx.measureText(txt).width; const x = Math.max(w / 2 + 2, Math.min(COLS * CS - w / 2 - 2, cx));
  ctx.shadowColor = col; ctx.shadowBlur = 10; ctx.fillStyle = col; ctx.fillText(txt, x, ty);
  ctx.shadowBlur = 0; ctx.fillStyle = '#ffffff'; ctx.globalAlpha = 0.85; ctx.fillText(txt, x, ty);
  ctx.restore();
}
function stepFx(dt){
  const k = dt / 16.7;
  for (const g of rings) { g.r += 0.18 * k; g.life -= 0.02 * k; } rings = rings.filter(g => g.life > 0);
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
  const ch = $('chargeLbl');
  if (charge) { ch.innerHTML = `<b style="color:${P[charge].color};text-shadow:0 0 8px ${P[charge].color}">${P[charge].k}</b>${P[charge].ab}`; ch.parentNode.classList.add('lit'); }
  else { ch.textContent = 'なし'; ch.parentNode.classList.remove('lit'); }
  $('track').innerHTML = TRACK.map(k => `<span class="${fired.has(k) ? 'on' : ''}" style="--c:${P[k].color}">${P[k].k}</span>`).join('');
  $('track').parentNode.classList.toggle('lit', kingPending);
}
function nextAbText(t){
  const c = chargeOf(t);
  if (c) return 'そろえる→' + P[c].ab;
  return P[t].ab;
}
function sideSize(){ return Math.floor(parseFloat(getComputedStyle(document.documentElement).getPropertyValue('--side')) - 8); }
function updateSide(){
  const s = sideSize();
  drawMini($('holdCv'), holdT, s); $('holdName').textContent = holdT ? P[holdT].k + ' ' + P[holdT].name : '-';
  fillQueue();
  const n = queue[0];
  drawMini($('nextCv'), n, s); $('nextName').textContent = P[n].k + ' ' + P[n].name; $('nextAb').textContent = nextAbText(n);
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
  particles = []; flashes = []; clearAnims = []; rings = []; screenFlash = null; lastLock = null;
  charge = null; fired = new Set(); kingPending = false;
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
  state(){ return {score, lines, level, combo, fuCount, over, running, paused, queue: queue.slice(), hold: holdT, cur: cur && {...cur}, charge, fired: [...fired], kingPending}; },
  setCharge(c){ charge = c; updateHud(); },
  setFired(a){ fired = new Set(a); kingPending = false; updateHud(); },
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
