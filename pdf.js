/* Vector PDF of the current view: the export button, top right beside the live status (14 Nov 2026).

   The map is drawn on canvases, which a browser can only save as pixels. So the export draws the view once more into
   a stand-in canvas context (PdfCtx) that writes PDF drawing commands instead of pixels:
     1. paint() from map.html (coast, streets, lots, subway lines, end dots, labels), with map.html's `ctx` and
        `roadCtx` swapped for PdfCtx objects for that one call;
     2. one frame of live.js (trains, station dots), through window.liveRenderTo;
     3. the substation icons and lots, which are SVG: read from the page (shapes, computed styles, clip paths and the
        banded lot gradients).
   The panels, legend and buttons are not included. The page is the window's size, 1 pt per CSS pixel, white.
   Path2D objects are opaque, so map.html records their steps while PDF_REC.on (see the top of its script).
   Runs after map.html's script and live.js; uses their top-level names (paint, ctx, roadCtx, roadLayer, roadAlpha,
   view, size, svg, PDF_REC, draw). */
(function pdfExport() {
  const num = v => { const r = Math.round(v * 100) / 100; return Object.is(r, -0) ? '0' : String(r); };
  const scratch = document.createElement('canvas').getContext('2d');
  const colours = new Map();
  function rgba(c) {                                       /* any CSS colour -> [r, g, b, a], 0..1 */
    if (typeof c !== 'string') return [0, 0, 0, 1];
    if (colours.has(c)) return colours.get(c);
    scratch.fillStyle = '#000'; scratch.fillStyle = c; const s = scratch.fillStyle; let out;
    if (s[0] === '#') { const n = parseInt(s.slice(1), 16); out = [(n >> 16 & 255) / 255, (n >> 8 & 255) / 255, (n & 255) / 255, 1]; }
    else { const m = s.match(/[\d.]+/g).map(Number); out = [m[0] / 255, m[1] / 255, m[2] / 255, m.length > 3 ? m[3] : 1]; }
    colours.set(c, out); return out;
  }
  const CAP = { butt: 0, round: 1, square: 2 }, JOIN = { miter: 0, round: 1, bevel: 2 };

  /* ---------- geometry: drawing steps -> PDF path operators, in page coordinates ---------- */
  function arcCurves(x, y, r, a0, a1, ccw) {                /* canvas arc() as cubic curves: [[c1x, c1y, c2x, c2y, x, y], ...] and its start */
    const TAU = Math.PI * 2; let sweep = a1 - a0;
    if (!ccw) sweep = sweep >= TAU ? TAU : ((sweep % TAU) + TAU) % TAU;
    else sweep = -(a0 - a1 >= TAU ? TAU : (((a0 - a1) % TAU) + TAU) % TAU);
    const n = Math.max(1, Math.ceil(Math.abs(sweep) / (Math.PI / 2) - 1e-9)), da = sweep / n, kk = 4 / 3 * Math.tan(da / 4), out = [];
    let t = a0;
    for (let i = 0; i < n; i++) {
      const t1 = t + da, c0 = Math.cos(t), s0 = Math.sin(t), c1 = Math.cos(t1), s1 = Math.sin(t1);
      out.push([x + r * (c0 - kk * s0), y + r * (s0 + kk * c0), x + r * (c1 + kk * s1), y + r * (s1 - kk * c1), x + r * c1, y + r * s1]);
      t = t1;
    }
    return { start: [x + r * Math.cos(a0), y + r * Math.sin(a0)], curves: out };
  }
  function parseSvgPath(d) {                               /* M L H V Q C Z (absolute and relative) -> steps */
    const tok = d.match(/[a-zA-Z]|[-+]?(?:\d*\.\d+|\d+\.?)(?:e[-+]?\d+)?/g) || [], ops = [];
    let i = 0, cmd = '', x = 0, y = 0, sx = 0, sy = 0;
    const n = () => parseFloat(tok[i++]);
    while (i < tok.length) {
      if (/[a-zA-Z]/.test(tok[i])) cmd = tok[i++];
      const rel = cmd === cmd.toLowerCase(), C = cmd.toUpperCase(), ox = rel ? x : 0, oy = rel ? y : 0;
      if (C === 'M') { x = ox + n(); y = oy + n(); sx = x; sy = y; ops.push(['M', x, y]); cmd = rel ? 'l' : 'L'; }
      else if (C === 'L') { x = ox + n(); y = oy + n(); ops.push(['L', x, y]); }
      else if (C === 'H') { x = ox + n(); ops.push(['L', x, y]); }
      else if (C === 'V') { y = oy + n(); ops.push(['L', x, y]); }
      else if (C === 'Q') { const a = ox + n(), b = oy + n(); x = ox + n(); y = oy + n(); ops.push(['Q', a, b, x, y]); }
      else if (C === 'C') { const a = ox + n(), b = oy + n(), c = ox + n(), e = oy + n(); x = ox + n(); y = oy + n(); ops.push(['C', a, b, c, e, x, y]); }
      else if (C === 'Z') { ops.push(['Z']); x = sx; y = sy; }
      else i++;                                             /* not used by the map */
    }
    return ops;
  }
  /* steps (in their own coordinates) -> PDF path text, through T(x, y) -> [X, Y] */
  function pathText(ops, T, out) {
    let cx = 0, cy = 0, sx = 0, sy = 0, has = false;
    const P = (x, y) => { const p = T(x, y); return num(p[0]) + ' ' + num(p[1]); };
    for (const o of ops) {
      switch (o[0]) {
        case 'M': out.push(P(o[1], o[2]) + ' m'); cx = sx = o[1]; cy = sy = o[2]; has = true; break;
        case 'L': out.push(P(o[1], o[2]) + (has ? ' l' : ' m')); if (!has) { sx = o[1]; sy = o[2]; } cx = o[1]; cy = o[2]; has = true; break;
        case 'Q': { const [, a, b, x, y] = o;           /* quadratic -> cubic */
          if (!has) { out.push(P(cx, cy) + ' m'); has = true; }
          out.push(P(cx + 2 / 3 * (a - cx), cy + 2 / 3 * (b - cy)) + ' ' + P(x + 2 / 3 * (a - x), y + 2 / 3 * (b - y)) + ' ' + P(x, y) + ' c'); cx = x; cy = y; break; }
        case 'C': out.push(P(o[1], o[2]) + ' ' + P(o[3], o[4]) + ' ' + P(o[5], o[6]) + ' c'); cx = o[5]; cy = o[6]; break;
        case 'Z': out.push('h'); cx = sx; cy = sy; break;
        case 'A': { const a = arcCurves(o[1], o[2], o[3], o[4], o[5], o[6]);
          out.push(P(a.start[0], a.start[1]) + (has ? ' l' : ' m')); if (!has) { sx = a.start[0]; sy = a.start[1]; }
          for (const c of a.curves) out.push(P(c[0], c[1]) + ' ' + P(c[2], c[3]) + ' ' + P(c[4], c[5]) + ' c');
          const last = a.curves[a.curves.length - 1]; cx = last[4]; cy = last[5]; has = true; break; }
        case 'R': { const [, x, y, w, h] = o; out.push(P(x, y) + ' m', P(x + w, y) + ' l', P(x + w, y + h) + ' l', P(x, y + h) + ' l', 'h'); cx = sx = x; cy = sy = y; has = true; break; }
      }
    }
    return out;
  }
  function stepsOf(p) {                                    /* a Path2D's steps: recorded, or kept as lot rings / an SVG string */
    if (p.ops) return p.ops;
    if (p.rings) { const ops = []; for (const f of p.rings) { ops.push(['M', f[0], f[1]]); for (let i = 2; i < f.length; i += 2) ops.push(['L', f[i], f[i + 1]]); ops.push(['Z']); } return ops; }
    if (p.svgD) return (p._svgOps || (p._svgOps = parseSvgPath(p.svgD)));
    return [];
  }

  /* ---------- the document ---------- */
  class Doc {
    constructor() { this.gs = new Map(); }
    alpha(a) { a = Math.round(Math.max(0, Math.min(1, a)) * 1000) / 1000; if (!this.gs.has(a)) this.gs.set(a, 'G' + this.gs.size); return '/' + this.gs.get(a) + ' gs'; }
    colour(c, op, a, mix) {                                /* 'rg' (fill) or 'RG' (stroke); mix: blend toward white instead of transparency */
      let [r, g, b, ca] = rgba(c); a *= ca;
      if (mix) { r = 1 - (1 - r) * mix; g = 1 - (1 - g) * mix; b = 1 - (1 - b) * mix; }
      return { text: num(r) + ' ' + num(g) + ' ' + num(b) + ' ' + op, alpha: a };
    }
  }
  const STATE = ['strokeStyle', 'fillStyle', 'lineWidth', 'lineCap', 'lineJoin', 'globalAlpha', 'font', 'letterSpacing', 'textAlign', 'textBaseline', 'miterLimit', '_m', '_dash'];
  /* A stand-in for CanvasRenderingContext2D: the calls the map and live.js make, written out as PDF. Coordinates:
     the context's own transform (device pixels), then times `k` (1 / devicePixelRatio) into page points. */
  class PdfCtx {
    constructor(doc, k) {
      this.doc = doc; this.k = k; this.buf = []; this.stack = []; this.path = []; this._cur = this._start = null; this.road = null; this.mix = 0;
      Object.assign(this, { strokeStyle: '#000', fillStyle: '#000', lineWidth: 1, lineCap: 'butt', lineJoin: 'miter', globalAlpha: 1,
        font: '10px Helvetica', letterSpacing: '0px', textAlign: 'start', textBaseline: 'alphabetic', miterLimit: 10, _m: [1, 0, 0, 1, 0, 0], _dash: [] });
    }
    /* transform */
    setTransform(a, b, c, d, e, f) { this._m = typeof a === 'object' ? [a.a, a.b, a.c, a.d, a.e, a.f] : [a, b, c, d, e, f]; }
    getTransform() { const [a, b, c, d, e, f] = this._m; return { a, b, c, d, e, f }; }
    transform(a, b, c, d, e, f) { const [A, B, C, D, E, F] = this._m; this._m = [A * a + C * b, B * a + D * b, A * c + C * d, B * c + D * d, A * e + C * f + E, B * e + D * f + F]; }
    translate(x, y) { this.transform(1, 0, 0, 1, x, y); }
    scale(x, y) { this.transform(x, 0, 0, y, 0, 0); }
    rotate(t) { const c = Math.cos(t), s = Math.sin(t); this.transform(c, s, -s, c, 0, 0); }
    T() { const [a, b, c, d, e, f] = this._m, k = this.k; return (x, y) => [(a * x + c * y + e) * k, (b * x + d * y + f) * k]; }
    get _scale() { const [a, b, c, d] = this._m; return Math.sqrt(Math.abs(a * d - b * c)) * this.k; }
    /* state */
    save() { const s = {}; for (const n of STATE) s[n] = this[n]; s._dash = this._dash.slice(); this.stack.push(s); this.buf.push('q'); }
    restore() { const s = this.stack.pop(); if (!s) return; Object.assign(this, s); this.buf.push('Q'); }
    setLineDash(d) { this._dash = (d || []).slice(); }
    getLineDash() { return this._dash.slice(); }
    /* the current path: canvas puts each point through the transform as it is added, so it is kept in page
       coordinates, as PDF path text, with the current point and the start of the subpath */
    beginPath() { this.path = []; this._cur = null; this._start = null; }
    _p(x, y) { return this.T()(x, y); }
    _put(p, op) { this.path.push(num(p[0]) + ' ' + num(p[1]) + ' ' + op); }
    moveTo(x, y) { const p = this._p(x, y); this._put(p, 'm'); this._cur = this._start = p; }
    lineTo(x, y) { const p = this._p(x, y); if (!this._cur) { this._put(p, 'm'); this._start = p; } else this._put(p, 'l'); this._cur = p; }
    _curve(c1, c2, p) { this.path.push([c1, c2, p].map(q => num(q[0]) + ' ' + num(q[1])).join(' ') + ' c'); this._cur = p; }
    quadraticCurveTo(a, b, x, y) {
      const q = this._p(a, b), p = this._p(x, y); if (!this._cur) { this._put(q, 'm'); this._cur = this._start = q; }
      const c = this._cur; this._curve([c[0] + 2 / 3 * (q[0] - c[0]), c[1] + 2 / 3 * (q[1] - c[1])], [p[0] + 2 / 3 * (q[0] - p[0]), p[1] + 2 / 3 * (q[1] - p[1])], p);
    }
    bezierCurveTo(a, b, c, d, x, y) { const p1 = this._p(a, b); if (!this._cur) { this._put(p1, 'm'); this._cur = this._start = p1; } this._curve(p1, this._p(c, d), this._p(x, y)); }
    arc(x, y, r, a0, a1, ccw) {
      const T = this.T(), a = arcCurves(x, y, r, a0, a1, !!ccw), s = T(a.start[0], a.start[1]);
      if (this._cur) this._put(s, 'l'); else { this._put(s, 'm'); this._start = s; } this._cur = s;
      for (const c of a.curves) this._curve(T(c[0], c[1]), T(c[2], c[3]), T(c[4], c[5]));
    }
    rect(x, y, w, h) { const T = this.T(), p = T(x, y); this._put(p, 'm'); this._put(T(x + w, y), 'l'); this._put(T(x + w, y + h), 'l'); this._put(T(x, y + h), 'l'); this.path.push('h'); this._cur = this._start = p; }
    closePath() { if (this._cur) { this.path.push('h'); this._cur = this._start; } }
    _pathText(p) { return p ? pathText(stepsOf(p), this.T(), []).join('\n') : this.path.join('\n'); }
    _style(stroke) {
      const d = this.doc, c = d.colour(stroke ? this.strokeStyle : this.fillStyle, stroke ? 'RG' : 'rg', this.mix ? 1 : this.globalAlpha, this.mix);
      let s = d.alpha(c.alpha) + ' ' + c.text;
      if (stroke) {
        const sc = this._scale;
        s += ` ${num(this.lineWidth * sc)} w ${CAP[this.lineCap] || 0} J ${JOIN[this.lineJoin] || 0} j`;
        s += ' [' + this._dash.map(v => num(v * sc)).join(' ') + '] 0 d';
      }
      return { s, a: c.alpha };
    }
    stroke(p) { const st = this._style(true); if (st.a <= 0) return; const t = this._pathText(p); if (t) this.buf.push('q ' + st.s + '\n' + t + '\nS Q'); }
    fill(p, rule) { if (typeof p === 'string') { rule = p; p = null; } const st = this._style(false); if (st.a <= 0) return; const t = this._pathText(p); if (t) this.buf.push('q ' + st.s + '\n' + t + (rule === 'evenodd' ? '\nf* Q' : '\nf Q')); }
    clip(p) { const t = this._pathText(p && typeof p === 'object' ? p : null); this.buf.push((t || '0 0 m') + '\nW n'); }
    fillRect(x, y, w, h) { const keep = this.path; this.path = []; this.rect(x, y, w, h); this.fill(); this.path = keep; }
    strokeRect(x, y, w, h) { const keep = this.path; this.path = []; this.rect(x, y, w, h); this.stroke(); this.path = keep; }
    clearRect() {}
    drawImage(img) { if (img === roadLayer && this.road) this.buf.push(...this.road.buf); }   /* the street layer: its own vector strokes */
    /* text: Helvetica (bold when the font says so), placed and turned as the canvas would */
    measureText(t) { scratch.font = this.font; if ('letterSpacing' in scratch) scratch.letterSpacing = this.letterSpacing || '0px'; return scratch.measureText(t); }
    fillText(t, x, y) { this._text(t, x, y, false); }
    strokeText(t, x, y) { this._text(t, x, y, true); }
    _text(t, x, y, stroke) {
      const size = parseFloat((this.font.match(/([\d.]+)px/) || [0, 10])[1]), bold = /bold|[6-9]00/.test(this.font);
      const sp = parseFloat(this.letterSpacing) || 0, w = this.measureText(t).width;
      const dx = this.textAlign === 'center' ? -w / 2 : this.textAlign === 'right' || this.textAlign === 'end' ? -w : 0;
      const dy = this.textBaseline === 'middle' ? size * 0.35 : this.textBaseline === 'top' || this.textBaseline === 'hanging' ? size * 0.75 : this.textBaseline === 'bottom' ? -size * 0.22 : 0;
      const [a, b, c, d] = this._m, k = this.k, [X, Y] = this.T()(x + dx, y + dy);
      const tm = [a * k * size, b * k * size, -c * k * size, -d * k * size, X, Y].map(num).join(' ');
      const st = this._style(stroke); if (st.a <= 0) return;
      this.buf.push(`q ${st.s} ${stroke ? '1 j ' : ''}BT /${bold ? 'F2' : 'F1'} 1 Tf ${num(sp / size)} Tc ${stroke ? 1 : 0} Tr ${tm} Tm (${pdfString(t)}) Tj ET Q`);
    }
  }
  const WIN = { 0x2013: 0x96, 0x2014: 0x97, 0x2018: 0x91, 0x2019: 0x92, 0x201c: 0x93, 0x201d: 0x94, 0x2022: 0x95, 0x2026: 0x85, 0x20ac: 0x80 };
  function pdfString(t) {                                  /* WinAnsi, escaped */
    let s = '';
    for (const ch of t) {
      let c = ch.codePointAt(0); if (WIN[c]) c = WIN[c]; else if (c > 255) c = 63;
      if (c === 40 || c === 41 || c === 92) s += '\\' + ch; else if (c < 32 || c > 126) s += '\\' + c.toString(8).padStart(3, '0'); else s += ch;
    }
    return s;
  }

  /* ---------- the SVG layer: substation icons and lots ---------- */
  function svgLayer(doc) {
    const out = [];
    const shown = n => { for (let e = n; e && e !== svg; e = e.parentNode) { const cs = getComputedStyle(e); if (cs.display === 'none' || cs.visibility === 'hidden') return false; } return true; };
    const opacity = n => { let o = 1; for (let e = n; e && e !== svg; e = e.parentNode) o *= parseFloat(getComputedStyle(e).opacity); return o; };
    const Tof = M => (x, y) => [M.a * x + M.c * y + M.e, M.b * x + M.d * y + M.f];
    const urlId = v => { const m = /url\(["']?#([^"')]+)/.exec(v || ''); return m && m[1]; };
    const stepsOfEl = e => {
      const tag = e.tagName.toLowerCase(), A = n => parseFloat(e.getAttribute(n)) || 0;
      if (tag === 'rect') {
        const x = A('x'), y = A('y'), w = A('width'), h = A('height'), cs = getComputedStyle(e);
        let r = parseFloat(cs.rx); if (!(r > 0)) r = parseFloat(cs.ry); if (!(r > 0)) r = A('rx') || A('ry');   /* rounded corners (also set from CSS) */
        if (!(r > 0)) return [['R', x, y, w, h]];
        if (/%/.test(cs.rx)) r = parseFloat(cs.rx) / 100 * w;
        r = Math.min(r, w / 2, h / 2); const H = Math.PI / 2;
        return [['M', x + r, y], ['L', x + w - r, y], ['A', x + w - r, y + r, r, -H, 0, false], ['L', x + w, y + h - r], ['A', x + w - r, y + h - r, r, 0, H, false],
          ['L', x + r, y + h], ['A', x + r, y + h - r, r, H, 2 * H, false], ['L', x, y + r], ['A', x + r, y + r, r, 2 * H, 3 * H, false], ['Z']];
      }
      if (tag === 'circle') return [['A', A('cx'), A('cy'), A('r'), 0, Math.PI * 2, false], ['Z']];
      if (tag === 'line') return [['M', A('x1'), A('y1')], ['L', A('x2'), A('y2')]];
      if (tag === 'path') return parseSvgPath(e.getAttribute('d') || '');
      if (tag === 'polygon' || tag === 'polyline') { const p = (e.getAttribute('points') || '').trim().split(/[\s,]+/).map(Number), ops = []; for (let i = 0; i + 1 < p.length; i += 2) ops.push([i ? 'L' : 'M', p[i], p[i + 1]]); if (tag === 'polygon') ops.push(['Z']); return ops; }
      return [];
    };
    for (const g of svg.querySelectorAll('#g-subs > g')) {
      if (!shown(g)) continue;
      for (const e of g.querySelectorAll('rect, circle, path, line, polygon, polyline')) {
        if (!shown(e)) continue;
        const cs = getComputedStyle(e), op = opacity(e); if (op <= 0.001) continue;
        const M = e.getCTM(); if (!M) continue;
        const T = Tof(M), body = pathText(stepsOfEl(e), T, []).join('\n'); if (!body) continue;
        const parts = ['q'];
        /* clip paths on the shape or its groups (the slices of a multi-line icon) */
        for (let a = e; a && a !== svg; a = a.parentNode) {
          const id = urlId(getComputedStyle(a).clipPath); if (!id) continue;
          const cp = document.getElementById(id), Ma = a.getCTM(); if (!cp || !Ma) continue;
          const cl = []; for (const c of cp.children) pathText(stepsOfEl(c), Tof(Ma), cl);
          if (cl.length) parts.push(cl.join('\n') + '\nW n');
        }
        const rule = cs.fillRule === 'evenodd' ? 'f*' : 'f', fillOp = parseFloat(cs.fillOpacity) * op;
        const gid = urlId(cs.fill), grad = gid && document.getElementById(gid);
        if (grad && grad.tagName.toLowerCase() === 'lineargradient') {
          /* the lot of a multi-line substation: equal bands, one per line colour (hard-stop gradient along x) */
          const x1 = parseFloat(grad.getAttribute('x1')) || 0, x2 = parseFloat(grad.getAttribute('x2')) || 0, stops = [...grad.querySelectorAll('stop')];
          for (let i = 0; i + 1 < stops.length; i += 2) {
            const f0 = parseFloat(stops[i].getAttribute('offset')), f1 = parseFloat(stops[i + 1].getAttribute('offset'));
            const xa = i === 0 ? -1e4 : x1 + (x2 - x1) * f0, xb = i + 2 >= stops.length ? 1e4 : x1 + (x2 - x1) * f1;
            const c = doc.colour(stops[i].getAttribute('stop-color'), 'rg', fillOp, 0);
            parts.push(`q ${body}\nW n ${doc.alpha(c.alpha)} ${c.text}\n` + pathText([['R', xa, -1e4, xb - xa, 2e4]], T, []).join('\n') + '\nf Q');
          }
        } else if (cs.fill !== 'none') {
          const c = doc.colour(cs.fill, 'rg', fillOp, 0);
          if (c.alpha > 0) parts.push(`${doc.alpha(c.alpha)} ${c.text}\n${body}\n${rule}`);
        }
        if (cs.stroke !== 'none') {
          const c = doc.colour(cs.stroke, 'RG', parseFloat(cs.strokeOpacity) * op, 0), sw = parseFloat(cs.strokeWidth) || 0;
          const w = cs.vectorEffect === 'non-scaling-stroke' ? sw : sw * Math.sqrt(Math.abs(M.a * M.d - M.b * M.c));
          if (c.alpha > 0 && w > 0) parts.push(`${doc.alpha(c.alpha)} ${c.text} ${num(w)} w ${CAP[cs.strokeLinecap] || 0} J ${JOIN[cs.strokeLinejoin] || 0} j [] 0 d\n${body}\nS`);
        }
        parts.push('Q');
        if (parts.length > 2) out.push(parts.join('\n'));
      }
    }
    return out;
  }

  /* ---------- the file ---------- */
  async function build() {
    const dpr = window.devicePixelRatio || 1, W = Math.round(size.w), H = Math.round(size.h), doc = new Doc();
    const main = new PdfCtx(doc, 1 / dpr), road = new PdfCtx(doc, 1 / dpr), trains = new PdfCtx(doc, 1 / dpr);
    road.mix = roadAlpha(view.k); main.road = road;        /* streets: their grey blended to white, so crossings do not darken */
    const keepCtx = ctx, keepRoad = roadCtx;
    PDF_REC.on = true;
    try {
      ctx = main; roadCtx = road; paint();
      ctx = keepCtx; roadCtx = keepRoad;
      if (window.liveRenderTo) liveRenderTo(trains);
    } finally { ctx = keepCtx; roadCtx = keepRoad; PDF_REC.on = false; draw(); }
    const icons = svgLayer(doc);
    const content = [`q 1 0 0 -1 0 ${H} cm 1 1 1 rg 0 0 ${W} ${H} re f`, ...main.buf, ...trains.buf, ...icons, 'Q'].join('\n');
    let data = new TextEncoder().encode(content), filter = '';
    if (window.CompressionStream) {                        /* zlib, which is what PDF's FlateDecode reads */
      data = new Uint8Array(await new Response(new Blob([data]).stream().pipeThrough(new CompressionStream('deflate'))).arrayBuffer()); filter = ' /Filter /FlateDecode';
    }
    const gsNames = [...doc.gs], first = 7;
    const objs = [
      '<< /Type /Catalog /Pages 2 0 R >>',
      '<< /Type /Pages /Kids [3 0 R] /Count 1 >>',
      `<< /Type /Page /Parent 2 0 R /MediaBox [0 0 ${W} ${H}] /Contents 4 0 R /Resources << /Font << /F1 5 0 R /F2 6 0 R >> /ExtGState << ` +
        gsNames.map(([, n], i) => `/${n} ${first + i} 0 R`).join(' ') + ' >> >> >>',
      null,                                                /* 4: the content stream */
      '<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica /Encoding /WinAnsiEncoding >>',
      '<< /Type /Font /Subtype /Type1 /BaseFont /Helvetica-Bold /Encoding /WinAnsiEncoding >>',
      ...gsNames.map(([a]) => `<< /Type /ExtGState /CA ${a} /ca ${a} >>`),
      `<< /Title (${pdfString('NYC Substations map')}) /Producer (NYC Substations map) /CreationDate (D:${new Date().toISOString().replace(/[-:T]/g, '').slice(0, 14)}) >>`
    ];
    const enc = new TextEncoder(), parts = [], offsets = []; let pos = 0;
    const put = b => { const u = typeof b === 'string' ? enc.encode(b) : b; parts.push(u); pos += u.length; };
    put('%PDF-1.4\n%\xe2\xe3\xcf\xd3\n');
    objs.forEach((o, i) => {
      offsets.push(pos); put(`${i + 1} 0 obj\n`);
      if (o === null) { put(`<< /Length ${data.length}${filter} >>\nstream\n`); put(data); put('\nendstream\n'); }
      else put(o + '\n');
      put('endobj\n');
    });
    const xref = pos;
    put(`xref\n0 ${objs.length + 1}\n0000000000 65535 f \n` + offsets.map(o => String(o).padStart(10, '0') + ' 00000 n \n').join(''));
    put(`trailer\n<< /Size ${objs.length + 1} /Root 1 0 R /Info ${objs.length} 0 R >>\nstartxref\n${xref}\n%%EOF\n`);
    return new Blob(parts, { type: 'application/pdf' });
  }
  async function save() {
    const b = document.getElementById('pdfbtn'); if (b.disabled) return;
    b.disabled = true;                                    /* greyed while it works (the icon stays) */
    try {
      const blob = await build(), d = new Date(), p = n => String(n).padStart(2, '0');
      const a = Object.assign(document.createElement('a'), { href: URL.createObjectURL(blob),
        download: `NYC substations ${d.getFullYear()}-${p(d.getMonth() + 1)}-${p(d.getDate())} ${p(d.getHours())}.${p(d.getMinutes())}.pdf` });
      document.body.appendChild(a); a.click(); a.remove(); setTimeout(() => URL.revokeObjectURL(a.href), 4000);
    } catch (e) { console.error('PDF export failed', e); alert('Sorry, the PDF could not be made: ' + e.message); }
    finally { b.disabled = false; }
  }
  const btn = document.getElementById('pdfbtn'); if (btn) btn.onclick = save;
  window.pdfDebug = { build };
})();
