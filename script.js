'use strict';
/* ===== 基本ユーティリティ ===== */
const $ = id => document.getElementById(id);
const rad = d => d * Math.PI / 180;
const FN = { sin: '\\sin\\theta', cos: '\\cos\\theta', tan: '\\tan\\theta' };
const OP = { '=': '=', '>=': '\\geqq', '>': '>', '<=': '\\leqq', '<': '<' };
const SIDE = { '>=': '以上', '>': 'より大きい', '<=': '以下', '<': 'より小さい' };
const COORD = { sin: '点のy座標', cos: '点のx座標', tan: '動径の傾き（直線 x=1 との交点のy座標）' };

/* 数式表示（KaTeX。読み込めない場合は簡易表示） */
function plain(s) {
  return s.replace(/\\frac\{([^{}]*)\}\{([^{}]*)\}/g, '($1)/($2)').replace(/\\sqrt\{([^{}]*)\}/g, '√$1')
    .replace(/\\circ/g, '°').replace(/\\theta/g, 'θ').replace(/\\geqq/g, '≧').replace(/\\leqq/g, '≦')
    .replace(/\\approx/g, '≒').replace(/\\(sin|cos|tan)/g, '$1').replace(/\\(quad|,|\\ )/g, ' ').replace(/[{}]/g, '');
}
function tex(s) {
  if (window.katex) { try { return katex.renderToString(s, { throwOnError: false }); } catch (e) { /* fallthrough */ } }
  return '<span>' + plain(s) + '</span>';
}

/* ===== 値と問題 ===== */
const BASE = {
  '0': ['0', 0], '1/2': ['\\frac{1}{2}', .5], '√2/2': ['\\frac{\\sqrt{2}}{2}', Math.SQRT1_2],
  '√3/2': ['\\frac{\\sqrt{3}}{2}', Math.sqrt(3) / 2], '1': ['1', 1],
  '√3/3': ['\\frac{\\sqrt{3}}{3}', Math.sqrt(3) / 3], '√3': ['\\sqrt{3}', Math.sqrt(3)]
};
function val(k) { const n = k[0] === '-', b = BASE[n ? k.slice(1) : k]; return { tex: (n ? '-' : '') + b[0], num: n ? -b[1] : b[1] }; }
/* 関数 記号 値 下限 上限 難易度（0基本 1標準 2発展）。θの範囲は 下限≦θ＜上限 */
const BANK = {
  eq: ['sin = 1/2 0 360 0', 'cos = 1/2 0 360 0', 'sin = √3/2 0 360 0', 'cos = √2/2 0 360 0', 'tan = 1 0 360 0', 'tan = √3 0 360 0',
    'sin = √2/2 0 360 0', 'cos = √3/2 0 360 0', 'tan = √3/3 0 360 0',
    'sin = -1/2 0 360 1', 'cos = -1/2 0 360 1', 'sin = -√2/2 0 360 1', 'cos = -√3/2 0 360 1', 'tan = -1 0 360 1',
    'tan = -√3 0 360 1', 'tan = -√3/3 0 360 1', 'sin = 0 0 360 1', 'cos = -1 0 360 1',
    'sin = √2/2 -360 360 2', 'cos = 1/2 0 720 2', 'tan = 1 -180 360 2', 'sin = -√3/2 -360 360 2', 'cos = -√2/2 -360 360 2'],
  in: ['sin >= 1/2 0 360 0', 'sin > 1/2 0 360 0', 'cos < 1/2 0 360 0', 'sin <= √3/2 0 360 0', 'cos > √2/2 0 360 0',
    'tan > 1 0 360 0', 'tan <= √3 0 360 0', 'cos >= √3/2 0 360 0', 'sin < √2/2 0 360 0',
    'sin >= -1/2 0 360 1', 'cos < -1/2 0 360 1', 'sin <= -√2/2 0 360 1', 'cos > -√3/2 0 360 1', 'tan > -1 0 360 1',
    'tan <= -√3/3 0 360 1', 'cos <= 0 0 360 1',
    'sin >= √2/2 -360 360 2', 'cos < 1/2 0 720 2', 'tan > -√3 -180 360 2', 'sin < -1/2 -360 360 2']
};
function parse(s) { const [f, op, k, lo, hi, lv] = s.split(' '); return { f, op, k, v: val(k), lo: +lo, hi: +hi, lv: +lv }; }
function pick(tab, lv, except) {
  const list = BANK[tab].map(parse).filter(p => p.lv === lv && !(except && p.f === except.f && p.op === except.op && p.k === except.k && p.lo === except.lo && p.hi === except.hi));
  return list[Math.floor(Math.random() * list.length)];
}

/* ===== 数学計算（角度は整数度で厳密に判定） ===== */
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
function eqSol(p) { const q = { ...p, op: '=' }, s = []; for (let d = p.lo; d < p.hi; d++) if (sat(q, d)) s.push(d); return s; }
function ineqSol(p) {
  const pts = [p.lo], q = { ...p, op: '=' };
  for (let d = p.lo + 1; d < p.hi; d++) if (isNaN(fval(p.f, d)) || sat(q, d)) pts.push(d);
  pts.push(p.hi);
  const out = [];
  for (let i = 0; i < pts.length - 1; i++) {
    const a = pts[i], b = pts[i + 1];
    if (!sat(p, (a + b) / 2)) continue;
    const last = out[out.length - 1];
    if (last && last.hi === a && sat(p, a)) last.hi = b; else out.push({ lo: a, hi: b });
  }
  out.forEach(u => { u.li = sat(p, u.lo); u.hiI = u.hi === p.hi ? false : sat(p, u.hi); });
  return out;
}
/* 有名角の正確な値（TeX）。有名角でなければ null、tanの定義なしは 'undef' */
const SM = { 0: '0', 30: '\\frac{1}{2}', 45: '\\frac{\\sqrt{2}}{2}', 60: '\\frac{\\sqrt{3}}{2}', 90: '1' };
const TM = { 0: '0', 30: '\\frac{\\sqrt{3}}{3}', 45: '1', 60: '\\sqrt{3}' };
function exact(f, deg) {
  if (Math.abs(deg - Math.round(deg)) > 1e-6) return null;
  const d = ((Math.round(deg) % 360) + 360) % 360;
  if (d % 30 && d % 45) return null;
  const r = d <= 90 ? d : d <= 180 ? 180 - d : d <= 270 ? d - 180 : 360 - d;
  let mag, neg;
  if (f === 'sin') { mag = SM[r]; neg = d > 180; }
  else if (f === 'cos') { mag = SM[90 - r]; neg = d > 90 && d < 270; }
  else { if (d === 90 || d === 270) return 'undef'; mag = TM[r]; neg = (d > 90 && d < 180) || d > 270; }
  return neg && mag !== '0' ? '-' + mag : mag;
}
const fmt = a => Math.abs(a - Math.round(a)) < 0.05 ? String(Math.round(a)) : a.toFixed(1);
function rowHtml(f, a) {
  const lhs = `\\${f}\\,${fmt(a)}^\\circ`, e = exact(f, a);
  if (e === 'undef') return `<div class="vrow">${tex(lhs)} <span class="undef">は定義されない</span></div>`;
  if (e !== null) return `<div class="vrow">${tex(lhs + '=' + e)}</div>`;
  const y = fval(f, a);
  return `<div class="vrow">${tex(lhs + '\\approx ' + y.toFixed(3))} <small>（近似値）</small></div>`;
}
const rangeTex = p => `${p.lo}^\\circ\\leqq\\theta<${p.hi}^\\circ`;
const ivTex = u => `${u.lo}^\\circ${u.li ? '\\leqq' : '<'}\\theta${u.hiI ? '\\leqq' : '<'}${u.hi}^\\circ`;
const probTex = p => `${FN[p.f]}${OP[p.op]}${p.v.tex}`;

/* ===== 状態 ===== */
const S = { tab: 'eq', lv: 0, snap: true, st: {} };
function newState(tab, except) { return { p: pick(tab, S.lv, except), angle: 0, reg: [], ranges: [], checks: 0, mode: 'explore', locked: true, pred: '', done: false, hint: 0 }; }
const c = () => S.st[S.tab];
function msg(html, type) {
  const m = $('msg'), icon = { ok: '✔ ', bad: '✖ ', info: 'ℹ ' }[type] || '';
  m.className = 'msg ' + (type || ''); m.innerHTML = html ? icon + html : '';
}

/* ===== ヒントと解説 ===== */
function hints(st) {
  const p = st.p, v = tex(p.v.tex), fn = tex(FN[p.f]);
  if (S.tab === 'eq') {
    const sym = { sin: 'y軸について対称な位置にも同じ y 座標の点があります。', cos: 'x軸について対称な位置にも同じ x 座標の点があります。', tan: '動径を反対側へのばした直線上の点でも、tan の値は同じです（180°ずつ離れた角）。' }[p.f];
    return [
      `注目するのは ${fn} の値です。単位円では ${COORD[p.f]}に対応します。`,
      `30°・45°・60°・90° などの特殊角で、sin・cos・tan の値がいくつだったか思い出そう。まず ${tex(probTex(p))} になる角度を1つ見つけよう。`,
      `${sym}範囲 ${tex(rangeTex(p))} の中で、動径を一周させて探そう。`
    ];
  }
  const inc = p.op === '>=' || p.op === '<=';
  return [
    `注目するのは ${fn} の値です。単位円では ${COORD[p.f]}に対応します。`,
    `まず等号のとき（${tex(FN[p.f] + '=' + p.v.tex)}）になる角度、つまり範囲の境界を探そう。`,
    `単位円上で、${COORD[p.f]}が ${v} ${SIDE[p.op]}となる動径の範囲を探そう。`,
    `${tex('\\geqq')}・${tex('\\leqq')} は境界を含む（●）、${tex('>')}・${tex('<')} は含まない（○）。この問題は ${tex(OP[p.op])} なので、境界は${inc ? '含みます' : '含みません'}。`
  ];
}
function explainHtml(st) {
  const p = st.p, sol = eqSol(p), pred = st.pred ? `<p>あなたの予想：${esc(st.pred)}</p>` : '';
  if (S.tab === 'eq') {
    return `<div class="explain"><h3>解説</h3><ol>
      <li>${tex(FN[p.f])} に注目します。単位円では ${COORD[p.f]}が ${tex(p.v.tex)} になる動径を探します。</li>
      <li>特殊角の値と対称性から、${tex(rangeTex(p))} で条件を満たす角度を求めます。</li></ol>
      <div class="ans">${tex('\\theta=' + sol.map(d => d + '^\\circ').join(',\\ '))}</div>${pred}</div>`;
  }
  const ivs = ineqSol(p), inc = p.op === '>=' || p.op === '<=';
  const undef = p.f === 'tan' ? '<li>tan θ が定義されない角度は、範囲に含まれません。</li>' : '';
  return `<div class="explain"><h3>解説</h3><ol>
    <li>まず境界を求めます。${tex(FN[p.f] + '=' + p.v.tex)} となる角度は ${tex(sol.map(d => d + '^\\circ').join(',\\ '))} です。</li>
    <li>単位円で、${COORD[p.f]}が ${tex(p.v.tex)} ${SIDE[p.op]}となる動径の範囲を調べます。</li>
    <li>${tex(OP[p.op])} なので境界は${inc ? '含みます（●）' : '含みません（○）'}。</li>${undef}</ol>
    <div class="ans">${ivs.map(u => tex(ivTex(u))).join('<br>')}</div>
    <p><b>方程式との比較：</b>方程式 ${tex(FN[p.f] + '=' + p.v.tex)} は「点（角度）」を求め、不等式は「範囲」を求めます。同じ単位円で、境界の点が方程式の解にあたります。</p>${pred}</div>`;
}
const esc = s => s.replace(/[&<>]/g, ch => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[ch]));

/* ===== 描画 ===== */
const cv = $('cv'), ctx = cv.getContext('2d');
const W = 600, CX = 300, CY = 300, R = 210;
const dpr = window.devicePixelRatio || 1;
cv.width = cv.height = W * dpr;
ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
const BLUE = '#1565c0', GREEN = '#1b7f3b', ORANGE = '#e65100', RED = '#d32f2f';
const P = (d, r) => [CX + r * Math.cos(rad(d)), CY - r * Math.sin(rad(d))];

function dot(d, r, filled, col) {
  const [x, y] = P(d, r);
  ctx.beginPath(); ctx.arc(x, y, 8, 0, 7);
  ctx.fillStyle = filled ? col : '#fff'; ctx.fill();
  ctx.lineWidth = 3; ctx.strokeStyle = col; ctx.stroke();
}
function arcPath(a, b, r) { ctx.beginPath(); ctx.arc(CX, CY, r, -rad(a), -rad(b), true); }

function draw() {
  const st = c(), p = st.p, x = ctx;
  x.clearRect(0, 0, W, W);
  const shade = S.tab === 'in' && st.mode !== 'explore';
  /* 不等式の解（確認・解答モード） */
  if (shade) {
    ineqSol(p).forEach(u => {
      x.beginPath(); x.moveTo(CX, CY); x.arc(CX, CY, R, -rad(u.lo), -rad(u.hi), true); x.closePath();
      x.fillStyle = 'rgba(21,101,192,.18)'; x.fill();
      arcPath(u.lo, u.hi, R); x.lineWidth = 8; x.strokeStyle = BLUE; x.stroke();
      dot(u.lo, R, u.li, BLUE); dot(u.hi, R, u.hiI, BLUE);
    });
  }
  /* 軸・単位円 */
  x.lineWidth = 1.5; x.strokeStyle = '#7a8591';
  x.beginPath(); x.moveTo(20, CY); x.lineTo(W - 20, CY); x.moveTo(CX, 20); x.lineTo(CX, W - 20); x.stroke();
  x.beginPath(); x.arc(CX, CY, R, 0, 7); x.lineWidth = 2; x.strokeStyle = '#37474f'; x.stroke();
  if (p.f === 'tan') { x.setLineDash([4, 4]); x.strokeStyle = '#8e6bbf'; x.beginPath(); x.moveTo(CX + R, 20); x.lineTo(CX + R, W - 20); x.stroke(); x.setLineDash([]); }
  /* 目盛りと角度ラベル */
  x.font = 'bold 13px sans-serif'; x.fillStyle = '#5a6672'; x.textAlign = 'center'; x.textBaseline = 'middle';
  [0, 30, 45, 60, 90, 120, 135, 150, 180, 210, 225, 240, 270, 300, 315, 330].forEach(d => {
    const [a, b] = P(d, R - 6), [e, f] = P(d, R + 6), [tx, ty] = P(d, R + 38);
    x.lineWidth = 1.5; x.strokeStyle = '#37474f'; x.beginPath(); x.moveTo(a, b); x.lineTo(e, f); x.stroke();
    x.fillText(d + '°', tx, ty);
  });
  /* 解答ガイド線 */
  if (st.done && p.f !== 'tan') {
    x.setLineDash([6, 5]); x.strokeStyle = GREEN; x.lineWidth = 2; x.beginPath();
    if (p.f === 'sin') { const y = CY - R * p.v.num; x.moveTo(CX - R - 20, y); x.lineTo(CX + R + 20, y); }
    else { const xx = CX + R * p.v.num; x.moveTo(xx, CY - R - 20); x.lineTo(xx, CY + R + 20); }
    x.stroke(); x.setLineDash([]);
  }
  /* 登録済みの解（方程式） */
  if (S.tab === 'eq') st.reg.forEach(d => {
    const [ex, ey] = P(d, R), [lx, ly] = P(d, R * .6);
    x.lineWidth = 3; x.strokeStyle = GREEN; x.beginPath(); x.moveTo(CX, CY); x.lineTo(ex, ey); x.stroke();
    dot(d, R, true, GREEN);
    x.font = 'bold 15px sans-serif'; x.lineWidth = 4; x.strokeStyle = '#fff'; x.strokeText(d + '°', lx, ly); x.fillStyle = GREEN; x.fillText(d + '°', lx, ly);
  });
  /* 入力済みの範囲（不等式） */
  if (S.tab === 'in') st.ranges.forEach(u => {
    x.setLineDash([8, 5]); arcPath(u.lo, u.hi, R + 16); x.lineWidth = 5; x.strokeStyle = ORANGE; x.stroke(); x.setLineDash([]);
    dot(u.lo, R + 16, u.li, ORANGE); dot(u.hi, R + 16, u.hiI, ORANGE);
  });
  /* 現在の動径 */
  const a = st.angle, [px, py] = P(a, R), sn = Math.sin(rad(a)), cs = Math.cos(rad(a));
  x.setLineDash([3, 4]); x.lineWidth = 1.5; x.strokeStyle = '#9aa5b1';
  x.beginPath(); x.moveTo(px, py); x.lineTo(px, CY); x.moveTo(px, py); x.lineTo(CX, py); x.stroke(); x.setLineDash([]);
  if (p.f === 'tan' && Math.abs(cs) > 1e-9 && Math.abs(R * sn / cs) < 280) {
    const ty = CY - R * sn / cs;
    x.setLineDash([3, 4]); x.strokeStyle = '#8e6bbf'; x.beginPath(); x.moveTo(CX, CY); x.lineTo(CX + R, ty); x.stroke(); x.setLineDash([]);
    x.beginPath(); x.arc(CX + R, ty, 6, 0, 7); x.fillStyle = '#8e6bbf'; x.fill();
  }
  x.beginPath(); x.arc(CX, CY, 34, 0, -rad(a), a > 0); x.lineWidth = 3; x.strokeStyle = RED; x.stroke();
  x.lineWidth = 5; x.strokeStyle = '#222'; x.beginPath(); x.moveTo(CX, CY); x.lineTo(px, py); x.stroke();
  x.beginPath(); x.arc(CX, CY, 4, 0, 7); x.fillStyle = '#222'; x.fill();
  x.beginPath(); x.arc(px, py, 10, 0, 7); x.fillStyle = RED; x.fill(); x.lineWidth = 3; x.strokeStyle = '#fff'; x.stroke();
}

/* ===== 画面更新 ===== */
function render() {
  const st = c(), p = st.p, eq = S.tab === 'eq';
  $('tabEq').setAttribute('aria-selected', eq); $('tabIn').setAttribute('aria-selected', !eq);
  $('eqPanel').hidden = !eq; $('inPanel').hidden = eq;
  $('problem').innerHTML = `<span class="tag">${eq ? '方程式' : '不等式'}（${['基本', '標準', '発展'][p.lv]}）</span><div>${tex(probTex(p))}</div><div>ただし、${tex(rangeTex(p))} とする。</div>`;
  $('predBox').hidden = !st.locked; $('lock').hidden = !st.locked;
  $('angleOut').innerHTML = tex(`\\theta=${fmt(st.angle)}^\\circ`);
  $('vals').innerHTML = ['sin', 'cos', 'tan'].map(f => rowHtml(f, st.angle)).join('');
  $('status').textContent = '';
  if (!eq && st.mode !== 'explore') {
    const d = Math.round(st.angle), ok = sat(p, st.angle);
    $('status').textContent = ok ? '✔ 今の動径は条件を満たしています' : '✖ 今の動径は条件を満たしていません';
  }
  $('regList').innerHTML = st.reg.map(d => `<li><span>${tex(`\\theta=${d}^\\circ`)}　${tex(`${FN[p.f].replace('\\theta', '')}${d}^\\circ=${exact(p.f, d)}`)}</span><button type="button" data-del="${d}" aria-label="${d}°を取り消す">×</button></li>`).join('');
  $('rangeList').innerHTML = st.ranges.map((u, i) => `<li><span>${tex(ivTex(u))}</span><button type="button" data-delr="${i}" aria-label="範囲を取り消す">×</button></li>`).join('');
  document.querySelectorAll('input[name=mode]').forEach(r => r.checked = r.value === st.mode);
  const hs = hints(st);
  $('hintBtn').textContent = `ヒント（${st.hint}/${hs.length}）`;
  $('hintBox').innerHTML = hs.slice(0, st.hint).map((h, i) => `<div class="hint"><b>ヒント${i + 1}：</b>${h}</div>`).join('');
  $('giveBtn').hidden = !(st.checks >= 2 && !st.done);
  $('explain').innerHTML = st.done ? explainHtml(st) : '';
  draw();
}

/* ===== 動径の操作 ===== */
function setAngle(a) {
  const st = c();
  if (S.snap) {
    const cand = [Math.round(a / 30) * 30, Math.round(a / 45) * 45].sort((m, n) => Math.abs(m - a) - Math.abs(n - a))[0];
    if (Math.abs(cand - a) < 4) a = cand;
  }
  st.angle = a; render();
}
let drag = false;
function move(e) {
  const r = cv.getBoundingClientRect(), k = W / r.width;
  const x = (e.clientX - r.left) * k - CX, y = CY - (e.clientY - r.top) * k;
  if (Math.hypot(x, y) < 5) return;
  const a = Math.atan2(y, x) * 180 / Math.PI, st = c();
  const now = ((st.angle % 360) + 360) % 360;
  const d = ((a - now + 540) % 360) - 180;
  setAngle(st.angle + d);
}
cv.addEventListener('pointerdown', e => { if (c().locked) return; drag = true; cv.setPointerCapture(e.pointerId); move(e); e.preventDefault(); });
cv.addEventListener('pointermove', e => { if (drag) { move(e); e.preventDefault(); } });
['pointerup', 'pointercancel'].forEach(t => cv.addEventListener(t, () => { drag = false; }));
cv.addEventListener('keydown', e => {
  if (c().locked) return;
  const k = { ArrowRight: 1, ArrowUp: 1, ArrowLeft: -1, ArrowDown: -1 }[e.key];
  if (!k) return;
  e.preventDefault(); c().angle = Math.round(c().angle) + k * (e.shiftKey ? 15 : 1); render();
});
document.querySelectorAll('[data-step]').forEach(b => b.addEventListener('click', () => {
  if (c().locked) return; c().angle = Math.round(c().angle) + +b.dataset.step; render();
}));
$('snap').addEventListener('change', e => { S.snap = e.target.checked; });

/* ===== 方程式：登録・答え合わせ ===== */
$('regBtn').addEventListener('click', () => {
  const st = c(), p = st.p, d = Math.round(st.angle);
  if (st.locked) return msg('先に予想を確定しよう。', 'info');
  if (d < p.lo || d >= p.hi) return msg(`範囲外です。${tex(rangeTex(p))} の中で探そう。`, 'bad');
  if (st.reg.includes(d)) return msg(`${d}° はすでに登録しています。`, 'info');
  if (!sat({ ...p, op: '=' }, d)) {
    const e = exact(p.f, d), lhs = `${FN[p.f].replace('\\theta', '')}${d}^\\circ`;
    const rhs = e === 'undef' ? '定義されない' : e !== null ? tex(lhs + '=' + e) : tex(lhs + '\\approx ' + fval(p.f, d).toFixed(3));
    return msg(`${d}° のとき ${e === 'undef' ? tex(lhs) + ' は定義されません。' : rhs + ' で、' + tex(p.v.tex) + ' になりません。'}`, 'bad');
  }
  st.reg.push(d); st.reg.sort((m, n) => m - n); msg(`${d}° を登録しました。`, 'ok'); render();
});
$('regList').addEventListener('click', e => {
  const d = e.target.dataset.del; if (d === undefined) return;
  const st = c(); st.reg = st.reg.filter(v => v !== +d); msg(''); render();
});

/* ===== 不等式：範囲の入力 ===== */
$('setLo').addEventListener('click', () => { $('lo').value = Math.round(c().angle); });
$('setHi').addEventListener('click', () => { $('hi').value = Math.round(c().angle); });
$('addRange').addEventListener('click', () => {
  const st = c(), p = st.p, lo = parseFloat($('lo').value), hi = parseFloat($('hi').value);
  const li = $('loOp').value === 'le', hiI = $('hiOp').value === 'le';
  if (st.locked) return msg('先に予想を確定しよう。', 'info');
  if (!isFinite(lo) || !isFinite(hi)) return msg('下限と上限の角度を入力しよう。', 'info');
  if (lo >= hi) return msg('下限は上限より小さくなるようにしよう。', 'bad');
  if (lo < p.lo || hi > p.hi || (hiI && hi >= p.hi)) return msg(`範囲外です。${tex(rangeTex(p))} の中で答えよう。`, 'bad');
  if (st.ranges.some(u => u.lo === lo && u.hi === hi && u.li === li && u.hiI === hiI)) return msg('同じ範囲がすでにあります。', 'info');
  st.ranges.push({ lo, hi, li, hiI }); st.ranges.sort((m, n) => m.lo - n.lo); msg('範囲を登録しました。', 'ok'); render();
});
$('rangeList').addEventListener('click', e => {
  const i = e.target.dataset.delr; if (i === undefined) return;
  c().ranges.splice(+i, 1); msg(''); render();
});
document.querySelectorAll('input[name=mode]').forEach(r => r.addEventListener('change', () => {
  const st = c();
  if (r.value === 'answer' && !st.done) {
    if (!confirm('答えを表示します。自分で考えてからにしましょう。表示してよいですか？')) { render(); return; }
    st.done = true;
  }
  st.mode = r.value; msg(''); render();
}));

/* ===== 共通ボタン ===== */
$('checkBtn').addEventListener('click', () => {
  const st = c(), p = st.p;
  if (st.locked) return msg('先に予想を確定しよう。', 'info');
  st.checks++;
  if (S.tab === 'eq') {
    if (!st.reg.length) { msg('まず、条件を満たす角度を登録しよう。', 'info'); }
    else if (eqSol(p).every(d => st.reg.includes(d))) { st.done = true; msg('正解です。解説を確認しよう。', 'ok'); }
    else msg('ほかにも条件を満たす角度がないか確認しよう。', 'info');
  } else {
    const sol = ineqSol(p), u = st.ranges;
    const same = (a, b) => a.lo === b.lo && a.hi === b.hi && a.li === b.li && a.hiI === b.hiI;
    if (!u.length) msg('まず、答えの範囲を登録しよう。', 'info');
    else if (u.length === sol.length && sol.every(s => u.some(t => same(s, t)))) { st.done = true; st.mode = 'answer'; msg('正解です。解説を確認しよう。', 'ok'); }
    else if (sol.some(s => u.some(t => t.lo === s.lo && t.hi === s.hi))) msg('境界の角度を含むか含まないか（≦と＜の違い）を確認しよう。', 'bad');
    else if (u.length < sol.length) msg('ほかにも条件を満たす範囲がないか確認しよう。', 'info');
    else msg('範囲の端の角度をもう一度確認しよう。', 'bad');
  }
  render();
});
$('giveBtn').addEventListener('click', () => {
  const st = c(); st.done = true;
  if (S.tab === 'eq') st.reg = eqSol(st.p); else { st.mode = 'answer'; st.ranges = []; }
  msg('解説を表示しました。次の問題にも挑戦しよう。', 'info'); render();
});
$('hintBtn').addEventListener('click', () => {
  const st = c(); if (st.locked) return msg('先に予想を確定しよう。', 'info');
  const n = hints(st).length; if (st.hint < n) st.hint++; else msg('ヒントはここまでです。', 'info'); render();
});
$('resetBtn').addEventListener('click', () => { S.st[S.tab] = { ...newState(S.tab), p: c().p }; msg(''); render(); });
$('newBtn').addEventListener('click', () => { S.st[S.tab] = newState(S.tab, c().p); msg(''); render(); });
$('predOk').addEventListener('click', () => {
  const st = c(), v = $('predIn').value.trim();
  if (!v) return msg('予想を入力するか、「予想せずに始める」を押そう。', 'info');
  st.pred = v; st.locked = false; $('predIn').value = ''; msg('予想を確定しました。動径を動かして確かめよう。', 'ok'); render();
});
$('predSkip').addEventListener('click', () => { c().locked = false; $('predIn').value = ''; msg(''); render(); });
function switchTab(t) { S.tab = t; msg(''); render(); }
$('tabEq').addEventListener('click', () => switchTab('eq'));
$('tabIn').addEventListener('click', () => switchTab('in'));
$('lv').addEventListener('change', e => {
  S.lv = +e.target.value; S.st.eq = newState('eq'); S.st.in = newState('in'); msg(''); render();
});

/* ===== 操作ガイド ===== */
function showGuide(on) {
  $('modal').hidden = !on;
  if (!on) { try { localStorage.setItem('trigEqGuideSeen', '1'); } catch (e) { /* 保存できなくても動作する */ } $('guideBtn').focus(); }
  else $('closeGuide').focus();
}
$('guideBtn').addEventListener('click', () => showGuide(true));
$('closeGuide').addEventListener('click', () => showGuide(false));
$('modal').addEventListener('click', e => { if (e.target === $('modal')) showGuide(false); });
document.addEventListener('keydown', e => { if (e.key === 'Escape' && !$('modal').hidden) showGuide(false); });

/* ===== 起動 ===== */
S.st.eq = newState('eq'); S.st.in = newState('in');
render();
try { if (!localStorage.getItem('trigEqGuideSeen')) showGuide(true); } catch (e) { /* 初回表示のみ省略 */ }
