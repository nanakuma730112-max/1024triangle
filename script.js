'use strict';
/* ===== ユーティリティ ===== */
const $ = id => document.getElementById(id);
const rad = d => d * Math.PI / 180;
const gcd = (a, b) => b ? gcd(b, a % b) : a;
const FN = { sin: '\\sin\\theta', cos: '\\cos\\theta', tan: '\\tan\\theta' };
const OP = { '=': '=', '>=': '\\geqq', '>': '>', '<=': '\\leqq', '<': '<' };
const rnd = a => a[Math.floor(Math.random() * a.length)];

/* 数式表示（KaTeX。読み込めない場合は簡易表示） */
function plain(s) {
  return s.replace(/\\frac\{([^{}]*)\}\{([^{}]*)\}/g, '($1)/($2)').replace(/\\sqrt\{([^{}]*)\}/g, '√$1')
    .replace(/\\circ/g, '°').replace(/\\theta/g, 'θ').replace(/\\pi/g, 'π').replace(/\\geqq/g, '≧').replace(/\\leqq/g, '≦')
    .replace(/\\approx/g, '≒').replace(/\\(sin|cos|tan)/g, '$1').replace(/\\(quad|,|\\ )/g, ' ').replace(/[{}]/g, '');
}
function tex(s) {
  if (window.katex) { try { return katex.renderToString(s, { throwOnError: false }); } catch (e) { /* 簡易表示へ */ } }
  return '<span>' + plain(s) + '</span>';
}

/* ===== 数学計算（角度は整数度で厳密に判定） ===== */
const BASE = {
  '0': ['0', 0], '1/2': ['\\frac{1}{2}', .5], '√2/2': ['\\frac{\\sqrt{2}}{2}', Math.SQRT1_2],
  '√3/2': ['\\frac{\\sqrt{3}}{2}', Math.sqrt(3) / 2], '1': ['1', 1],
  '√3/3': ['\\frac{\\sqrt{3}}{3}', Math.sqrt(3) / 3], '√3': ['\\sqrt{3}', Math.sqrt(3)]
};
function val(k) { const n = k[0] === '-', b = BASE[n ? k.slice(1) : k]; return { tex: (n ? '-' : '') + b[0], num: n ? -b[1] : b[1] }; }
function fval(f, d) {
  const r = rad(d);
  if (f === 'sin') return Math.sin(r);
  if (f === 'cos') return Math.cos(r);
  return Math.abs(Math.cos(r)) < 1e-9 ? NaN : Math.tan(r);
}
function sat(p, d) {
  const y = fval(p.f, d), v = p.v.num, e = 1e-9;
  if (isNaN(y)) return false;
  switch (p.op) {
    case '=': return Math.abs(y - v) < e;
    case '>=': return y >= v - e;
    case '>': return y > v + e;
    case '<=': return y <= v + e;
    default: return y < v - e;
  }
}
function eqSol(p) { const s = []; for (let d = p.lo; d < p.hi; d++) if (sat(p, d)) s.push(d); return s; }
function ineqSol(p) {
  const q = { ...p, op: '=' }, pts = [p.lo], out = [];
  for (let d = p.lo + 1; d < p.hi; d++) if (isNaN(fval(p.f, d)) || sat(q, d)) pts.push(d);
  const all = [...pts, p.hi];
  for (let i = 0; i < all.length - 1; i++) {
    const a = all[i], b = all[i + 1];
    if (!sat(p, (a + b) / 2)) continue;
    const last = out[out.length - 1];
    if (last && last.hi === a && sat(p, a)) last.hi = b; else out.push({ lo: a, hi: b });
  }
  out.forEach(u => { u.li = sat(p, u.lo); u.hiI = u.hi === p.hi ? false : sat(p, u.hi); });
  pts.forEach(b => { /* sin≧1 のような「1点だけ」の解 */
    if (!sat(p, b)) return;
    if (out.some(u => (b > u.lo || (b === u.lo && u.li)) && (b < u.hi || (b === u.hi && u.hiI)))) return;
    out.push({ lo: b, hi: b, li: true, hiI: true });
  });
  return out.sort((a, b) => a.lo - b.lo || a.hi - b.hi);
}
/* 方程式の解も「幅0の区間」として同じ形で扱う */
const solve = p => p.op === '=' ? eqSol(p).map(d => ({ lo: d, hi: d, li: true, hiI: true })) : ineqSol(p);
const isBoundary = (p, e) => isNaN(fval(p.f, e)) || sat({ ...p, op: '=' }, e);

const SM = { 0: '0', 30: '\\frac{1}{2}', 45: '\\frac{\\sqrt{2}}{2}', 60: '\\frac{\\sqrt{3}}{2}', 90: '1' };
const TM = { 0: '0', 30: '\\frac{\\sqrt{3}}{3}', 45: '1', 60: '\\sqrt{3}' };
function exact(f, deg) {
  const d = ((deg % 360) + 360) % 360;
  if (d % 30 && d % 45) return null;
  const r = d <= 90 ? d : d <= 180 ? 180 - d : d <= 270 ? d - 180 : 360 - d;
  let mag, neg;
  if (f === 'sin') { mag = SM[r]; neg = d > 180; }
  else if (f === 'cos') { mag = SM[90 - r]; neg = d > 90 && d < 270; }
  else { if (d === 90 || d === 270) return 'undef'; mag = TM[r]; neg = (d > 90 && d < 180) || d > 270; }
  return neg && mag !== '0' ? '-' + mag : mag;
}

/* ===== 状態 ===== */
const DOMS = [[0, 360], [-180, 180], [0, 720], [-360, 360]];
const RHS = { sin: ['-1', '-√3/2', '-√2/2', '-1/2', '0', '1/2', '√2/2', '√3/2', '1'], tan: ['-√3', '-1', '-√3/3', '0', '√3/3', '1', '√3'] };
RHS.cos = RHS.sin;
const S = { kind: 'eq', f: 'sin', op: '>=', vk: '1/2', dom: 0, rad: false, angle: 0, q: null };
const prob = () => ({ f: S.f, op: S.kind === 'eq' ? '=' : S.op, k: S.vk, v: val(S.vk), lo: DOMS[S.dom][0], hi: DOMS[S.dom][1] });

/* 角度の表記（度数法／弧度法） */
function angTex(d) {
  if (!S.rad) return d + '^\\circ';
  if (d === 0) return '0';
  const g = gcd(Math.abs(d), 180), n = d / g, m = 180 / g, an = Math.abs(n), top = an === 1 ? '\\pi' : an + '\\pi';
  return (n < 0 ? '-' : '') + (m === 1 ? top : `\\frac{${top}}{${m}}`);
}
function angPlain(d) {
  if (!S.rad) return d + '°';
  if (d === 0) return '0';
  const g = gcd(Math.abs(d), 180), n = d / g, m = 180 / g, an = Math.abs(n);
  return (n < 0 ? '−' : '') + (an === 1 ? 'π' : an + 'π') + (m === 1 ? '' : '/' + m);
}
const ivTex = u => u.lo === u.hi ? `\\theta=${angTex(u.lo)}` : `${angTex(u.lo)}${u.li ? '\\leqq' : '<'}\\theta${u.hiI ? '\\leqq' : '<'}${angTex(u.hi)}`;
const ivKey = sol => JSON.stringify(sol.map(u => [u.lo, u.hi, u.li, u.hiI]));

/* ===== 描画 ===== */
const cv = $('cv'), ctx = cv.getContext('2d');
const W = 600, C = 300, R = 165;
const dpr = window.devicePixelRatio || 1;
cv.width = cv.height = W * dpr;
ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
const BLUE = '#1565c0', ORANGE = '#e65100', TEAL = '#00897b', RED = '#d32f2f';
const PX = d => C + R * Math.cos(rad(d)), PY = d => C - R * Math.sin(rad(d));

function dot(d, filled, col) {
  ctx.beginPath(); ctx.arc(PX(d), PY(d), 8, 0, 7);
  ctx.fillStyle = filled ? col : '#fff'; ctx.fill(); ctx.lineWidth = 3; ctx.strokeStyle = col; ctx.stroke();
}
function pdot(x, y, filled, col) {
  ctx.beginPath(); ctx.arc(x, y, 7, 0, 7);
  ctx.fillStyle = filled ? col : '#fff'; ctx.fill(); ctx.lineWidth = 3; ctx.strokeStyle = col; ctx.stroke();
}
function line(x1, y1, x2, y2, col, w, dash) {
  ctx.setLineDash(dash || []); ctx.lineWidth = w; ctx.strokeStyle = col;
  ctx.beginPath(); ctx.moveTo(x1, y1); ctx.lineTo(x2, y2); ctx.stroke(); ctx.setLineDash([]);
}
function text(s, x, y, col, size, align) {
  ctx.font = `bold ${size || 15}px sans-serif`; ctx.textAlign = align || 'center'; ctx.textBaseline = 'middle';
  ctx.lineWidth = 4; ctx.strokeStyle = '#fff'; ctx.strokeText(s, x, y); ctx.fillStyle = col; ctx.fillText(s, x, y);
}

function draw(p, sol, hide) {
  const x = ctx, v = p.v.num, ineq = p.op !== '=', inc = p.op === '>=' || p.op === '<=', up = p.op === '>=' || p.op === '>';
  const showSol = !hide, vlab = p.k.replace('-', '−');
  x.clearRect(0, 0, W, W);
  /* 不等式を満たす範囲（円周の弧と扇形） */
  if (ineq && showSol) sol.forEach(u => {
    if (u.lo === u.hi) return;
    x.beginPath(); x.moveTo(C, C); x.arc(C, C, R, -rad(u.lo), -rad(u.hi), true); x.closePath();
    x.fillStyle = 'rgba(21,101,192,.14)'; x.fill();
    x.beginPath(); x.arc(C, C, R, -rad(u.lo), -rad(u.hi), true); x.lineWidth = 9; x.strokeStyle = BLUE; x.stroke();
  });
  /* 軸と単位円 */
  line(20, C, W - 20, C, '#7a8591', 1.5); line(C, 20, C, W - 20, '#7a8591', 1.5);
  x.beginPath(); x.arc(C, C, R, 0, 7); x.lineWidth = 2; x.strokeStyle = '#37474f'; x.stroke();
  text('x', W - 14, C - 12, '#555', 14); text('y', C + 14, 16, '#555', 14); text('O', C - 12, C + 14, '#555', 14);
  text('1', C + R + 8, C + 14, '#555', 13); text('−1', C - R - 10, C + 14, '#555', 13);
  /* 選択した関数の基準線と不等式の範囲 */
  if (p.f === 'sin') {
    const yl = C - R * v;
    line(C - R - 40, yl, C + R + 40, yl, ORANGE, 2, [7, 5]); text('y＝' + vlab, 40, yl - 12, ORANGE, 14);
    text('1', C - 12, C - R - 8, '#555', 13); text('−1', C - 14, C + R + 10, '#555', 13);
    if (ineq && showSol) { line(C, yl, C, up ? C - R : C + R, BLUE, 7); pdot(C, yl, inc, BLUE); }
  } else if (p.f === 'cos') {
    const xl = C + R * v;
    line(xl, C - R - 40, xl, C + R + 40, ORANGE, 2, [7, 5]); text('x＝' + vlab, xl + 4, 30, ORANGE, 14, 'left');
    if (ineq && showSol) { line(xl, C, up ? C + R : C - R, C, BLUE, 7); pdot(xl, C, inc, BLUE); }
  } else {
    const yk = C - R * v, ext = 1.8 * R;
    line(C + R, 20, C + R, W - 20, '#8e6bbf', 2, [5, 5]); text('x＝1', C + R + 6, 30, '#6a4aa0', 14, 'left');
    line(C - ext, C + ext * v, C + ext, C - ext * v, ORANGE, 2, [7, 5]);
    if (Math.abs(yk - C) < 280) pdot(C + R, yk, ineq && showSol ? inc : true, ORANGE);
    if (ineq && showSol) { line(C + R, Math.max(20, Math.min(W - 20, yk)), C + R, up ? 20 : W - 20, BLUE, 7); if (Math.abs(yk - C) < 280) pdot(C + R, yk, inc, BLUE); }
  }
  /* 方程式の解／不等式の境界の点と角度ラベル */
  const cnt = {};
  const lab = d => { const m = ((d % 360) + 360) % 360, n = cnt[m] = (cnt[m] || 0) + 1, r = R + 28 + (n - 1) * 18; text(angPlain(d), C + r * Math.cos(rad(d)), C - r * Math.sin(rad(d)), '#222', 14); };
  if (showSol) {
    if (!ineq) sol.forEach(u => {
      line(C, C, PX(u.lo), PY(u.lo), ORANGE, 2);
      x.beginPath(); x.arc(PX(u.lo), PY(u.lo), 11, 0, 7); x.fillStyle = 'rgba(230,81,0,.3)'; x.fill(); x.lineWidth = 4; x.strokeStyle = ORANGE; x.stroke();
      lab(u.lo);
    });
    else {
      const seen = new Set();
      sol.forEach(u => [[u.lo, u.li], [u.hi, u.hiI]].forEach(([e, f]) => {
        if (seen.has(e)) return;
        if (u.lo === u.hi || isBoundary(p, e)) { seen.add(e); dot(e, f, BLUE); lab(e); }
      }));
    }
  }
  /* 現在の角度 */
  const a = S.angle, px = PX(a), py = PY(a), t = fval(p.f, a);
  if (p.f === 'sin') { line(px, py, px, C, TEAL, 5); x.fillStyle = TEAL; x.fillRect(px - 4, C - 4, 8, 8); }
  else if (p.f === 'cos') { line(px, py, C, py, TEAL, 5); x.fillStyle = TEAL; x.fillRect(C - 4, py - 4, 8, 8); }
  else if (!isNaN(t)) {
    const tv = R * Math.tan(rad(a)), k = Math.abs(tv) > 280 ? 280 / Math.abs(tv) : 1;
    line(px, py, C + R * k, C - tv * k, TEAL, 2, [4, 4]);
    line(C + R, C, C + R, C - tv * k, TEAL, 6);
    if (k === 1) { x.beginPath(); x.moveTo(C + R, C - tv - 8); x.lineTo(C + R + 8, C - tv); x.lineTo(C + R, C - tv + 8); x.lineTo(C + R - 8, C - tv); x.closePath(); x.fillStyle = TEAL; x.fill(); }
  }
  x.beginPath(); x.arc(C, C, 30, 0, -rad(a), a > 0); x.lineWidth = 3; x.strokeStyle = RED; x.stroke();
  const am = rad(((a % 360) + 360) % 360 / 2);
  text('θ', C + 50 * Math.cos(am), C - 50 * Math.sin(am), RED, 16);
  line(C, C, px, py, '#222', 5);
  x.beginPath(); x.arc(C, C, 4, 0, 7); x.fillStyle = '#222'; x.fill();
  x.beginPath(); x.arc(px, py, 10, 0, 7); x.fillStyle = RED; x.fill(); x.lineWidth = 3; x.strokeStyle = '#fff'; x.stroke();
  text('P', px + 16 * Math.cos(rad(a)), py - 16 * Math.sin(rad(a)), '#222', 15);
}

/* ===== 画面更新 ===== */
function valHtml(p, a) {
  const e = exact(p.f, a);
  if (e === 'undef') return `${tex(FN.tan)} は<b>定義されない</b>（cosθ＝0）`;
  if (e !== null) return tex(`${FN[p.f]}=${e}`);
  return tex(`${FN[p.f]}\\approx ${fval(p.f, a).toFixed(3)}`) + ' <small>（近似値）</small>';
}
function solHtml(p, sol, hide) {
  const title = p.op === '=' ? '方程式の解' : '不等式の解の範囲';
  if (hide) return `<b>${title}</b>クイズに答えると表示されます。`;
  if (!sol.length) return `<b>${title}</b>解なし`;
  if (p.op === '=') return `<b>${title}</b>${tex('\\theta=' + sol.map(u => angTex(u.lo)).join(',\\ '))}`;
  return `<b>${title}</b>` + sol.map(u => `<div class="line">${tex(ivTex(u))}</div>`).join('');
}
function render() {
  const p = prob(), sol = solve(p), hide = !!(S.q && S.q.hidden);
  const [lo, hi] = [p.lo, p.hi];
  S.angle = Math.max(lo, Math.min(hi - 1, S.angle));
  document.querySelectorAll('[data-kind]').forEach(b => b.setAttribute('aria-pressed', b.dataset.kind === S.kind));
  document.querySelectorAll('[data-f]').forEach(b => b.setAttribute('aria-pressed', b.dataset.f === S.f));
  document.querySelectorAll('[data-rad]').forEach(b => b.setAttribute('aria-pressed', (b.dataset.rad === '1') === S.rad));
  $('opWrap').hidden = S.kind === 'eq';
  $('eqShow').innerHTML = `${tex(FN[p.f] + OP[p.op] + p.v.tex)}<small>ただし、${tex(angTex(lo) + '\\leqq\\theta<' + angTex(hi))} とする。</small>`;
  $('angleOut').innerHTML = tex('\\theta=' + angTex(S.angle));
  $('valOut').innerHTML = valHtml(p, S.angle);
  const ok = sat(p, S.angle), und = isNaN(fval(p.f, S.angle));
  $('status').textContent = und ? `✖ tanθ が定義されないので、${p.op === '=' ? '解ではありません' : '条件を満たしません'}`
    : ok ? (p.op === '=' ? '✔ 今の角度は方程式の解です' : '✔ 今の角度は不等式を満たします')
      : (p.op === '=' ? '✖ 今の角度は解ではありません' : '✖ 今の角度は不等式を満たしません');
  $('status').style.color = ok ? '#1b7f3b' : '#b3261e';
  const sl = $('slider'); sl.min = lo; sl.max = hi - 1; sl.value = S.angle;
  if (document.activeElement !== $('angIn')) {
    const g = gcd(Math.abs(S.angle), 180);
    $('angIn').value = !S.rad ? S.angle : S.angle === 0 ? '0' : (S.angle / g) + (180 / g === 1 ? '' : '/' + (180 / g));
  }
  $('angUnit').textContent = S.rad ? 'π' : '°';
  $('solBox').innerHTML = solHtml(p, sol, hide);
  draw(p, sol, hide);
}
function fillRhs() {
  $('rhs').innerHTML = RHS[S.f].map(k => `<option value="${k}">${k.replace('-', '−')}</option>`).join('');
  if (!RHS[S.f].includes(S.vk)) S.vk = S.f === 'tan' ? '1' : '1/2';
  $('rhs').value = S.vk;
}
function fillUnitDependent() {
  $('dom').innerHTML = DOMS.map((d, i) => `<option value="${i}">${angPlain(d[0])}≦θ＜${angPlain(d[1])}</option>`).join('');
  $('dom').value = S.dom;
  document.querySelectorAll('[data-step]').forEach(b => { const s = +b.dataset.step; b.textContent = (s < 0 ? '−' : '＋') + angPlain(Math.abs(s)); });
  const [lo, hi] = DOMS[S.dom], sp = [];
  for (let d = lo; d < hi; d++) if (d % 30 === 0 || d % 45 === 0) sp.push(d);
  $('specials').innerHTML = sp.map(d => `<button type="button" data-sp="${d}">${angPlain(d)}</button>`).join('');
}
function syncAll() { fillRhs(); $('op').value = S.op; fillUnitDependent(); render(); }

/* ===== 角度の操作 ===== */
function setAngle(a) { if (isNaN(a)) return; S.angle = Math.round(a); render(); }
let drag = false;
function move(e) {
  const r = cv.getBoundingClientRect(), k = W / r.width;
  const x = (e.clientX - r.left) * k - C, y = C - (e.clientY - r.top) * k;
  if (Math.hypot(x, y) < 8) return;
  const a = Math.atan2(y, x) * 180 / Math.PI, [lo, hi] = DOMS[S.dom];
  let best = null;
  for (let k2 = -3; k2 <= 3; k2++) {
    const c = Math.round(a) + 360 * k2;
    if (c >= lo && c <= hi - 1 && (best === null || Math.abs(c - S.angle) < Math.abs(best - S.angle))) best = c;
  }
  if (best === null) return;
  const s = [Math.round(best / 30) * 30, Math.round(best / 45) * 45].sort((m, n) => Math.abs(m - best) - Math.abs(n - best))[0];
  if (Math.abs(s - best) <= 3 && s >= lo && s <= hi - 1) best = s;
  setAngle(best);
}
cv.addEventListener('pointerdown', e => { drag = true; cv.setPointerCapture(e.pointerId); move(e); e.preventDefault(); });
cv.addEventListener('pointermove', e => { if (drag) { move(e); e.preventDefault(); } });
['pointerup', 'pointercancel'].forEach(t => cv.addEventListener(t, () => { drag = false; }));
cv.addEventListener('keydown', e => {
  const k = { ArrowRight: 1, ArrowUp: 1, ArrowLeft: -1, ArrowDown: -1 }[e.key];
  if (!k) return; e.preventDefault(); setAngle(S.angle + k * (e.shiftKey ? 15 : 1));
});
$('slider').addEventListener('input', e => setAngle(+e.target.value));
document.querySelectorAll('[data-step]').forEach(b => b.addEventListener('click', () => setAngle(S.angle + +b.dataset.step)));
$('specials').addEventListener('click', e => { const d = e.target.dataset.sp; if (d !== undefined) setAngle(+d); });
function applyInput() {
  let s = $('angIn').value.replace(/[π°度\s]/g, '').replace(/[−ー]/g, '-');
  const [n, m] = s.split('/');
  let v = n === '' || n === undefined ? NaN : n === '-' ? -1 : parseFloat(n);
  if (s.startsWith('/')) v = 1;
  if (m !== undefined) v = v / parseFloat(m);
  if (S.rad) v *= 180;
  if (isNaN(v)) { render(); return; }
  setAngle(v);
}
$('angSet').addEventListener('click', applyInput);
$('angIn').addEventListener('keydown', e => { if (e.key === 'Enter') applyInput(); });
$('angIn').addEventListener('blur', render);

/* ===== 問題の設定 ===== */
function changed() { S.q = null; renderQuiz(); render(); }
document.querySelectorAll('[data-kind]').forEach(b => b.addEventListener('click', () => { S.kind = b.dataset.kind; changed(); }));
document.querySelectorAll('[data-f]').forEach(b => b.addEventListener('click', () => { S.f = b.dataset.f; fillRhs(); changed(); }));
$('op').addEventListener('change', e => { S.op = e.target.value; changed(); });
$('rhs').addEventListener('change', e => { S.vk = e.target.value; changed(); });
$('dom').addEventListener('change', e => { S.dom = +e.target.value; fillUnitDependent(); changed(); });
document.querySelectorAll('[data-rad]').forEach(b => b.addEventListener('click', () => { S.rad = b.dataset.rad === '1'; fillUnitDependent(); render(); renderQuiz(); }));

/* ===== クイズ（最後に配置・初期画面には出さない） ===== */
function makeQuiz() {
  let p, sol, n = 0;
  do {
    S.kind = rnd(['eq', 'in']); S.f = rnd(['sin', 'cos', 'tan']); S.op = rnd(['>=', '>', '<=', '<']);
    S.vk = rnd(RHS[S.f]); S.dom = 0; p = prob(); sol = solve(p); n++;
  } while (!sol.length && n < 200);
  S.angle = 0;
  const q = { hidden: true, answered: false, sel: new Set(), choice: null, opts: [], res: '', cls: '' };
  if (p.op !== '=') {
    const flip = { '>=': '>', '>': '>=', '<=': '<', '<': '<=' }, opp = { '>=': '<=', '>': '<', '<=': '>=', '<': '>' };
    const cands = [ineqSol({ ...p, op: flip[p.op] }), ineqSol({ ...p, op: opp[p.op] }), ineqSol({ ...p, op: flip[opp[p.op]] }), ineqSol({ ...p, v: { num: -p.v.num } })];
    const seen = new Set([ivKey(sol)]), opts = [{ sol, ok: true }];
    cands.forEach(c => { const k = ivKey(c); if (!seen.has(k) && opts.length < 4) { seen.add(k); opts.push({ sol: c, ok: false }); } });
    q.opts = opts.sort(() => Math.random() - .5);
  }
  S.q = q; syncAll(); renderQuiz();
}
function renderQuiz() {
  const box = $('quizBox'), q = S.q;
  if (!q) { box.innerHTML = '<p>単位円を動かして考え、答えを選びます。</p><button type="button" id="qNew" class="primary">問題を出す</button>'; return; }
  const p = prob();
  let body;
  if (p.op === '=') {
    const sp = []; for (let d = p.lo; d < p.hi; d++) if (d % 30 === 0 || d % 45 === 0) sp.push(d);
    body = `<p>上の方程式の解を、すべて選びましょう。</p><div class="grid">${sp.map(d => `<button type="button" data-qa="${d}" aria-pressed="${q.sel.has(d)}">${angPlain(d)}</button>`).join('')}</div>`;
  } else {
    body = '<p>上の不等式の解の範囲を選びましょう。</p>' + q.opts.map((o, i) =>
      `<label class="opt"><input type="radio" name="qc" value="${i}" ${q.choice === i ? 'checked' : ''}> ${o.sol.length ? o.sol.map(u => tex(ivTex(u))).join('　') : '解なし'}</label>`).join('');
  }
  box.innerHTML = body + `<div class="row"><button type="button" id="qCheck" class="primary" ${q.answered ? 'disabled' : ''}>答え合わせ</button><button type="button" id="qNew">新しい問題</button></div><div class="res ${q.cls}" aria-live="polite">${q.res}</div>`;
}
$('quizBtn').addEventListener('click', () => {
  const b = $('quizBox'); b.hidden = !b.hidden;
  $('quizBtn').textContent = b.hidden ? 'クイズに挑戦する' : 'クイズを閉じる';
  if (!b.hidden) renderQuiz();
});
$('quizBox').addEventListener('click', e => {
  const t = e.target, q = S.q;
  if (t.id === 'qNew') return makeQuiz();
  if (!q || q.answered) return;
  if (t.dataset.qa !== undefined) { const d = +t.dataset.qa; q.sel.has(d) ? q.sel.delete(d) : q.sel.add(d); renderQuiz(); }
  if (t.id === 'qCheck') {
    const p = prob(), sol = solve(p);
    let ok;
    if (p.op === '=') { const a = sol.map(u => u.lo); ok = a.length === q.sel.size && a.every(d => q.sel.has(d)); }
    else if (q.choice === null) { q.res = 'まず、答えを選ぼう。'; q.cls = ''; return renderQuiz(); }
    else ok = q.opts[q.choice].ok;
    q.answered = true; q.hidden = false;
    q.res = ok ? '✔ 正解です。単位円で確かめよう。' : '✖ 不正解です。単位円に表示された解を見て確かめよう。'; q.cls = ok ? 'ok' : 'bad';
    renderQuiz(); render();
  }
});
$('quizBox').addEventListener('change', e => { if (e.target.name === 'qc' && S.q) S.q.choice = +e.target.value; });

/* ===== 操作ガイド ===== */
function showGuide(on) { $('modal').hidden = !on; (on ? $('closeGuide') : $('guideBtn')).focus(); }
$('guideBtn').addEventListener('click', () => showGuide(true));
$('closeGuide').addEventListener('click', () => showGuide(false));
$('modal').addEventListener('click', e => { if (e.target === $('modal')) showGuide(false); });
document.addEventListener('keydown', e => { if (e.key === 'Escape' && !$('modal').hidden) showGuide(false); });

/* ===== 起動 ===== */
syncAll(); renderQuiz();
