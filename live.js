/* NYC Subway Live (13 Nov 2026): live trains on the substation map's linework.

   Data: the MTA's public GTFS-realtime feeds (api-endpoint.mta.info, no key; they allow browser requests), read
   every POLL seconds and decoded here (a small protobuf reader, below). Each train's trip lists its coming stops
   with predicted times; the train is placed between the stop it last left and the next one, on the lane of its
   colour that the map draws, and moved smoothly along that lane from frame to frame.
   Stations: stations.js (MTA Subway Stations, data.ny.gov), drawn as black dots with a white outline (once the streets show) on each coloured lane that
   stops there, as on the 1972 Vignelli diagram.
   This file runs after map.html's own script and uses its top-level names (variants, routes, view, fitK, size,
   keyOf, GROUP_COLOR, draw, apply). */
(function live() {
  const FEEDS = ['', '-ace', '-bdfm', '-g', '-jz', '-nqrw', '-l', '-si'].map(s => 'https://api-endpoint.mta.info/Dataservice/mtagtfsfeeds/nyct%2Fgtfs' + s);
  const POLL = 30, SPEED = 9.5 / 55.66;                   /* s between reads; assumed running speed in map units per s */
  const FETCH_TIMEOUT = 15000;                             /* ms: a feed request taking longer is given up (it used to stall polling) */
  const TRAINS_FROM = 4, TRAINS_FULL = 6;                 /* px per map unit: trains gone below FROM, fully shown from FULL */
  const MU = 55.66, NEAR = 250 / MU;                       /* a station further than 250 m from its lane is not placed */

  /* ---------- protobuf (GTFS-realtime) ---------- */
  function reader(buf) { return { b: buf, i: 0 }; }
  function varint(r) { let x = 0, m = 1, c; do { c = r.b[r.i++]; x += (c & 127) * m; m *= 128; } while (c & 128); return x; }
  function fields(buf, fn) {                               /* calls fn(field number, wire type, value) for each field */
    const r = reader(buf);
    while (r.i < r.b.length) {
      const tag = varint(r), f = Math.floor(tag / 8), w = tag & 7;
      if (w === 0) fn(f, 0, varint(r));
      else if (w === 2) { const n = varint(r); fn(f, 2, r.b.subarray(r.i, r.i + n)); r.i += n; }
      else if (w === 1) r.i += 8; else if (w === 5) r.i += 4; else return;
    }
  }
  const text = b => new TextDecoder().decode(b);
  function decodeFeed(buf) {
    const trips = new Map(), veh = new Map(); let stamp = 0;
    fields(buf, (f, w, v) => {
      if (f === 1 && w === 2) fields(v, (g, w2, u) => { if (g === 3) stamp = u; });
      if (f !== 2 || w !== 2) return;
      fields(v, (g, w2, u) => {
        if (w2 !== 2) return;
        if (g === 3) {                                   /* TripUpdate */
          const t = { id: '', route: '', stops: [] };
          fields(u, (h, w3, x) => {
            if (h === 1 && w3 === 2) fields(x, (k, w4, y) => { if (k === 1) t.id = text(y); else if (k === 5) t.route = text(y); });
            else if (h === 2 && w3 === 2) {
              const s = { id: '', arr: 0, dep: 0 };
              fields(x, (k, w4, y) => {
                if (k === 4 && w4 === 2) s.id = text(y);
                else if ((k === 2 || k === 3) && w4 === 2) fields(y, (m, w5, z) => { if (m === 2) s[k === 2 ? 'arr' : 'dep'] = z; });
              });
              s.arr = s.arr || s.dep; s.dep = s.dep || s.arr; if (s.id) t.stops.push(s);
            }
          });
          if (t.id) trips.set(t.id, t);
        } else if (g === 4) {                            /* VehiclePosition */
          const p = { trip: '', status: 2, stop: '', seq: 0 };
          fields(u, (h, w3, x) => {
            if (h === 1 && w3 === 2) fields(x, (k, w4, y) => { if (k === 1) p.trip = text(y); });
            else if (h === 4) p.status = x; else if (h === 7 && w3 === 2) p.stop = text(x); else if (h === 3) p.seq = x;
          });
          if (p.trip) veh.set(p.trip, p);
        }
      });
    });
    return { trips, veh, stamp };
  }

  /* ---------- the drawn lanes ---------- */
  const svcOf = route => { let r = route.replace(/X$/, ''); if (r === 'SI' || r === 'SS') r = 'SIR'; return r; };   /* 6X -> 6, FX -> F */
  const strandsFor = svc => {                              /* the strands of the service's colour group */
    const key = keyOf(svc), ri = routes.findIndex(r => !r.dashed && r.key === key);
    return ri < 0 ? [] : variants.near.strands[ri] || [];
  };
  const stationAt = new Map(), stationRoutes = new Map();   /* gtfs stop id -> [x, y]; -> daytime services */
  for (const [id, name, rts, lat, lon] of window.STATIONS || []) { stationAt.set(id, px(lon, lat)); stationRoutes.set(id, rts.split(' ').map(svcOf)); }
  const projCache = new Map();
  function project(stopId, svc) {                          /* nearest point of a lane running svc: { st, pos } (pos = segment + fraction) */
    const key = stopId + '|' + svc + (arguments[2] ? '|own' : '');   /* 'own': the service's own lane only, no fallback */
    if (projCache.has(key)) return projCache.get(key);
    const p = stationAt.get(stopId); let best = null;
    if (p) for (const st of strandsFor(svc)) for (let i = 0; i < st.length - 1; i++) {
      const a = st[i], b = st[i + 1];
      if (!(a.svcs && a.svcs.has(svc)) && !(b.svcs && b.svcs.has(svc))) continue;
      const dx = b[0] - a[0], dy = b[1] - a[1], L = dx * dx + dy * dy;
      const t = L ? Math.max(0, Math.min(1, ((p[0] - a[0]) * dx + (p[1] - a[1]) * dy) / L)) : 0;
      const d = Math.hypot(p[0] - a[0] - t * dx, p[1] - a[1] - t * dy);
      if (d < NEAR && (!best || d < best.d)) best = { st, pos: i + t, d };
    }
    /* the map does not draw this service here (a night or rush-hour extension, e.g. the 4 to New Lots): use the
       lane of a line that does stop at this station, which is the track the train is on */
    if (!best && !arguments[2]) for (const r of stationRoutes.get(stopId) || []) if (r !== svc) { const b = project(stopId, r, true); if (b) { best = { ...b, svc: r }; break; } }
    if (best && !best.svc) best.svc = svc;
    projCache.set(key, best); return best;
  }
  const pointAt = (st, pos) => {                           /* a lane point (with its lane offset) at a fractional index */
    const i = Math.max(0, Math.min(st.length - 2, Math.floor(pos))), t = pos - i, a = st[i], b = st[i + 1];
    const q = [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, (a.ax || 0) + ((b.ax || 0) - (a.ax || 0)) * t, (a.ay || 0) + ((b.ay || 0) - (a.ay || 0)) * t];
    q.st = st; q.pos = pos; return q;                      /* which lane and where on it, so a train never has to guess */
  };
  const pathCache = new Map();
  function pathBetween(svc, s0, s1) {                     /* polyline [[x, y, ax, ay], ...] with cumulative lengths */
    const key = svc + '|' + s0 + '|' + s1;
    if (pathCache.has(key)) return pathCache.get(key);
    let A = project(s0, svc), B = project(s1, svc), pts = null;
    /* one stop on the service's own lane and the next on another line's (the train has gone onto that line's track):
       put both on the same colour, where that line stops at both */
    if (A && B && A.svc !== B.svc) { const A2 = project(s0, B.svc, true), B2 = project(s1, A.svc, true); if (A2) A = { ...A2, svc: B.svc }; else if (B2) B = { ...B2, svc: A.svc }; }
    const via = A && B && A.st !== B.st ? route(A, B) : null;
    if (via) pts = via;
    else if (A && B && A.st === B.st) {
      pts = [pointAt(A.st, A.pos)];
      if (B.pos > A.pos) for (let i = Math.floor(A.pos) + 1; i <= Math.ceil(B.pos) - 1; i++) pts.push(pointAt(A.st, i));
      else for (let i = Math.ceil(A.pos) - 1; i >= Math.floor(B.pos) + 1; i--) pts.push(pointAt(A.st, i));
      pts.push(pointAt(B.st, B.pos));
    } else if (A && B) pts = [pointAt(A.st, A.pos), pointAt(B.st, B.pos)];   /* across a junction the map draws as two strands */
    else if (A || B) { const C = A || B; pts = [pointAt(C.st, C.pos)]; }
    if (pts) { let s = 0; pts[0].s = 0; for (let i = 1; i < pts.length; i++) { s += Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]); pts[i].s = s; } pts.len = s; }
    pathCache.set(key, pts); return pts;
  }
  /* Strands of one colour meet at junctions, where one strand's end touches another strand. A graph of all the
     points of a colour, joined along each strand and across those junctions, gives the way between two stops on
     different strands (shortest, with stretches that do not carry the train's service counted three times over). */
  const graphs = new Map();
  function graphFor(strands, svc) {
    const key = strands.length + ':' + svc + ':' + (strands[0] && strands[0][0][0]);
    if (graphs.has(key)) return graphs.get(key);
    const off = [], nodes = []; let n = 0;
    strands.forEach((st, s) => { off[s] = n; st.forEach((q, i) => nodes.push({ s, i, q })); n += st.length; });
    const adj = nodes.map(() => []), add = (a, b, w) => { adj[a].push([b, w]); adj[b].push([a, w]); };
    const cost = (a, b) => Math.hypot(a[0] - b[0], a[1] - b[1]) * (a.svcs && a.svcs.has(svc) ? 1 : 3);
    strands.forEach((st, s) => { for (let i = 0; i + 1 < st.length; i++) add(off[s] + i, off[s] + i + 1, cost(st[i], st[i + 1])); });
    strands.forEach((st, s) => [0, st.length - 1].forEach(e => {      /* an end touching another strand: a junction */
      const q = st[e]; let best = null;
      strands.forEach((o, t) => { if (t === s) return; o.forEach((r, j) => { const d = Math.hypot(r[0] - q[0], r[1] - q[1]); if (d < 3 && (!best || d < best.d)) best = { d, node: off[t] + j }; }); });
      if (best) add(off[s] + e, best.node, best.d + 0.05);
    }));
    const g = { off, nodes, adj }; graphs.set(key, g); return g;
  }
  function route(A, B) {
    const strands = strandsFor(A.svc); if (!strands.includes(A.st) || !strands.includes(B.st)) return null;
    const g = graphFor(strands, A.svc), sa = strands.indexOf(A.st), sb = strands.indexOf(B.st);
    const ia = Math.floor(A.pos), ib = Math.floor(B.pos), N = g.nodes.length;
    const dist = new Float64Array(N).fill(Infinity), from = new Int32Array(N).fill(-1), done = new Uint8Array(N);
    const seg = (st, i, pos) => Math.hypot(st[i][0] - pointAt(st, pos)[0], st[i][1] - pointAt(st, pos)[1]);
    const starts = [[g.off[sa] + ia, seg(A.st, ia, A.pos)], [g.off[sa] + Math.min(ia + 1, A.st.length - 1), seg(A.st, Math.min(ia + 1, A.st.length - 1), A.pos)]];
    const ends = new Map([[g.off[sb] + ib, seg(B.st, ib, B.pos)], [g.off[sb] + Math.min(ib + 1, B.st.length - 1), seg(B.st, Math.min(ib + 1, B.st.length - 1), B.pos)]]);
    const heap = [];                                       /* small binary heap of [distance, node] */
    const push = (d, v) => { heap.push([d, v]); let i = heap.length - 1; while (i) { const p = (i - 1) >> 1; if (heap[p][0] <= heap[i][0]) break; [heap[p], heap[i]] = [heap[i], heap[p]]; i = p; } };
    const pop = () => { const top = heap[0], last = heap.pop(); if (heap.length) { heap[0] = last; let i = 0; for (;;) { const l = 2 * i + 1, r = l + 1; let m = i; if (l < heap.length && heap[l][0] < heap[m][0]) m = l; if (r < heap.length && heap[r][0] < heap[m][0]) m = r; if (m === i) break; [heap[m], heap[i]] = [heap[i], heap[m]]; i = m; } } return top; };
    for (const [v, d] of starts) if (d < dist[v]) { dist[v] = d; push(d, v); }
    let bestEnd = -1, bestD = Infinity;
    while (heap.length) {
      const [d, v] = pop(); if (done[v]) continue; done[v] = 1;
      if (ends.has(v) && d + ends.get(v) < bestD) { bestD = d + ends.get(v); bestEnd = v; }
      if (d > bestD || d > 400) break;
      for (const [u, w] of g.adj[v]) if (!done[u] && d + w < dist[u]) { dist[u] = d + w; from[u] = v; push(d + w, u); }
    }
    if (bestEnd < 0) return null;
    const chain = []; for (let v = bestEnd; v >= 0; v = from[v]) chain.push(v); chain.reverse();
    const pts = [pointAt(A.st, A.pos)];
    for (const v of chain) { const nd = g.nodes[v]; pts.push(pointAt(strands[nd.s], nd.i)); }
    pts.push(pointAt(B.st, B.pos));
    return pts;
  }
  function along(pts, f) {                                 /* point and heading at fraction f of the path */
    if (pts.length === 1) return [...pts[0], 1, 0];
    const s = f * pts.len; let i = 1; while (i < pts.length - 1 && pts[i].s < s) i++;
    const a = pts[i - 1], b = pts[i], seg = (b.s - a.s) || 1, t = Math.max(0, Math.min(1, (s - a.s) / seg));
    const hx = b[0] - a[0], hy = b[1] - a[1], hl = Math.hypot(hx, hy) || 1;
    const q = [a[0] + hx * t, a[1] + hy * t, a[2] + (b[2] - a[2]) * t, a[3] + (b[3] - a[3]) * t, hx / hl, hy / hl];
    if (a.st && a.st === b.st) { q.st = a.st; q.pos = a.pos + (b.pos - a.pos) * t; }   /* (not across a junction link) */
    return q;
  }
  /* the station before `stop` on its lane, on the side away from `next` (for a train first seen between stations) */
  function stationBefore(svc, stop, next) {
    const A = project(stop, svc), B = next && project(next, svc); if (!A || !B || A.st !== B.st) return null;
    const dir = Math.sign(B.pos - A.pos); let best = null;
    for (const id of stationAt.keys()) {
      const P = project(id, svc); if (!P || P.st !== A.st || id === stop) continue;
      const d = (A.pos - P.pos) * dir; if (d > 0.01 && (!best || d < best.d)) best = { id, d };
    }
    return best && best.id;
  }

  /* ---------- trains ---------- */
  const trains = new Map();                                /* trip id -> state */
  const base = id => id.replace(/[NS]$/, '');
  function update(feeds) {                                 /* feeds: [{ idx, trips, veh }], only those that answered */
    const now = Date.now() / 1000, seen = new Set(), answered = new Set(feeds.map(f => f.idx));
    for (const { idx, trips, veh } of feeds) for (const [id, t] of trips) {
      const v = veh.get(id); if (!v) continue;              /* only trains that are out on the line */
      const svc = svcOf(t.route); if (!strandsFor(svc).length) continue;   /* shuttles are not drawn on this map */
      const stops = t.stops.map(s => ({ id: base(s.id), arr: s.arr, dep: s.dep })).filter(s => stationAt.has(s.id));
      if (!stops.length) continue;
      seen.add(id);
      let tr = trains.get(id);
      if (!tr) { tr = { id, svc, prev: null }; trains.set(id, tr); }
      tr.feed = idx;
      /* a stop that has dropped off the front of the list has been passed */
      if (tr.stops && tr.stops.length && tr.stops[0].id !== stops[0].id && !stops.some(s => s.id === tr.stops[0].id)) {
        const gone = tr.stops.filter(s => !stops.some(n => n.id === s.id)); const last = gone[gone.length - 1];
        tr.prev = { id: last.id, t: Math.min(now, last.dep || now) };
      }
      if (v.status === 1 && base(v.stop) === stops[0].id) tr.stopped = true; else tr.stopped = false;
      if (!tr.prev && !tr.stopped) {                       /* first seen between stations: start from the one before */
        const p = stationBefore(svc, stops[0].id, stops[1] && stops[1].id);
        if (p) { const path = pathBetween(svc, p, stops[0].id); tr.prev = { id: p, t: Math.min(now, stops[0].arr - (path ? path.len / SPEED : 60)) }; }
      }
      tr.svc = svc; tr.stops = stops;
    }
    /* a train no longer listed has finished its trip; but a feed that did not answer this time keeps its trains
       (they used to vanish and come back somewhere else on the next read) */
    for (const [id, tr] of trains) if (!seen.has(id) && answered.has(tr.feed)) trains.delete(id);
  }
  /* pull away, run at an even speed, brake: a quarter of the time each to speed up and slow down (top speed is then
     a third above the average, not half again as with a cosine) */
  const ACC = 0.25, ease = f => f < ACC ? f * f / (2 * ACC * (1 - ACC)) : f > 1 - ACC ? 1 - (1 - f) * (1 - f) / (2 * ACC * (1 - ACC)) : (f - ACC / 2) / (1 - ACC);
  function place(tr, T) {                                  /* [x, y, ax, ay, hx, hy] at time T, or null */
    const W = tr.prev ? [{ id: tr.prev.id, arr: tr.prev.t, dep: tr.prev.t }, ...tr.stops] : tr.stops;
    for (let i = 0; i < W.length; i++) {
      const w = W[i];
      if (T < w.arr) {
        if (i === 0) { const p = pathBetween(tr.svc, w.id, (W[1] || w).id); return p ? along(p, 0) : null; }
        const a = W[i - 1], p = pathBetween(tr.svc, a.id, w.id); if (!p) return null;
        return along(p, ease(Math.max(0, Math.min(1, (T - a.dep) / Math.max(1, w.arr - a.dep)))));
      }
      if (T <= w.dep || i === W.length - 1) {              /* at the station (or the predicted time has passed and no news yet) */
        const nx = W[i + 1] || W[i - 1], p = nx && pathBetween(tr.svc, w.id, nx.id);
        if (p) { const q = along(p, 0); if (!W[i + 1]) { q[4] = -q[4]; q[5] = -q[5]; } return q; }
        const P = project(w.id, tr.svc); return P ? [...pointAt(P.st, P.pos), 1, 0] : null;
      }
    }
    return null;
  }

  /* ---------- motion ----------
     Each train keeps its own place and speed and only ever moves forward. New predictions do not move it: they
     change the time it should reach its next stop, and it speeds up or slows down to make that time (a revised,
     later arrival used to pull the train backwards). It brakes into each station, waits until its predicted
     departure, and sets off for its next stop. A stop the feed no longer lists has been passed, so a train still
     short of it hurries on. */
  const VMAX = 24 / MU, HURRY = 14 / MU, BRAKE = 1.1 / MU, ACCEL = 1.0 / MU;   /* map units per s, per s^2 */
  function locate(tr, T) {                                 /* where a newly seen train is: on a stretch or at a stop */
    const W = tr.prev ? [{ id: tr.prev.id, arr: tr.prev.t, dep: tr.prev.t }, ...tr.stops] : tr.stops;
    for (let i = 0; i < W.length; i++) {
      const w = W[i];
      if (T < w.arr && i > 0) {
        const a = W[i - 1], pts = pathBetween(tr.svc, a.id, w.id); if (!pts) return { at: w.id };
        const lin = Math.max(0, Math.min(1, (T - a.dep) / Math.max(1, w.arr - a.dep)));
        return { a: a.id, b: w.id, pts, f: ease(lin), v: Math.min(VMAX, pts.len / Math.max(1, w.arr - a.dep)) };
      }
      if (T < w.arr || T <= w.dep || i === W.length - 1) return { at: w.id };
    }
    return { at: W[W.length - 1].id };
  }
  function step(tr, T, dt) {
    if (!tr.m) tr.m = locate(tr, T);
    const m = tr.m;
    if (m.at) {                                            /* at a stop: leave at the predicted departure */
      const k = tr.stops.findIndex(s => s.id === m.at), here = k >= 0 ? tr.stops[k] : null;
      const next = k >= 0 ? tr.stops[k + 1] : tr.stops[0];
      if (next && next.id !== m.at && (!here || T >= here.dep)) {
        const pts = pathBetween(tr.svc, m.at, next.id);
        if (pts && pts.len > 0.01) tr.m = { a: m.at, b: next.id, pts, f: 0, v: 0 };
        else tr.m = { at: next.id };
      }
    } else {
      const target = tr.stops.find(s => s.id === m.b), left = (1 - m.f) * m.pts.len;
      const remain = target ? target.arr - T : 0;
      let want = remain > 2 ? left / remain : HURRY;      /* the speed that arrives on time (or hurry if overdue) */
      want = Math.min(want, VMAX, Math.sqrt(2 * BRAKE * left) + 0.05 / MU);   /* and brake into the stop */
      m.v = want > m.v ? Math.min(want, m.v + ACCEL * dt * 3) : Math.max(want, m.v - BRAKE * dt * 3);
      m.f = Math.min(1, m.f + m.v * dt / m.pts.len);
      if (m.f >= 0.999) tr.m = { at: m.b };
    }
    const n = tr.m;
    if (n.at) {                                            /* standing at a stop: lined up with the track there */
      const P = project(n.at, tr.svc); if (!P) return null;
      const s = P.st[Math.max(0, Math.min(P.st.length - 1, Math.round(P.pos)))];
      const q = [...pointAt(P.st, P.pos), s.dx || tr.hx || 1, s.dy || tr.hy || 0]; q.st = P.st; q.pos = P.pos; return q;
    }
    const q = along(n.pts, n.f); tr.hx = q[4]; tr.hy = q[5]; return q;
  }

  /* ---------- drawing (a canvas of its own over the map's, under the icons) ---------- */
  const cv = document.createElement('canvas'); cv.id = 'trains';
  document.getElementById('canvas').after(cv);
  const screenCx = cv.getContext('2d'); let cx = screenCx;   /* pdf.js draws one frame into its PDF context */
  const dark = c => { const n = parseInt(c.slice(1), 16), f = 0.55; return `rgb(${Math.round((n >> 16) * f)},${Math.round((n >> 8 & 255) * f)},${Math.round((n & 255) * f)})`; };
  const darkOf = new Map();
  const colorOf = svc => { const key = keyOf(svc); if (!darkOf.has(key)) darkOf.set(key, dark(GROUP_COLOR[key] || '#808080')); return darkOf.get(key); };
  /* station dots: one per lane stopping there */
  const dots = [];
  { const seen = new Set();
    for (const [id, name, rts] of window.STATIONS || []) for (const r of rts.split(' ')) {
      const svc = svcOf(r), P = project(id, svc); if (!P) continue;
      const k = P.st.length + ':' + Math.round(P.pos * 4) + ':' + keyOf(svc) + ':' + Math.round(P.st[0][0]); if (seen.has(k)) continue; seen.add(k);
      dots.push({ st: P.st, pos: P.pos, name, svc, rts });
    } }
  /* ---------- power view ----------
     How the substations feed the trains (see General/HOW_SUBSTATIONS_POWER_THE_SUBWAY.md). NYC Transit's third rail is
     cut into sections, track by track, running between substations and the circuit-breaker houses that tie them;
     each section is fed from both ends (a 2005 fire at the 144th St substation tripped the breakers at the
     substations on both sides of it). So a train draws from the substation behind it and the one ahead of it on
     its line. Here those two are found along the drawn lane (up to REACH, beyond which the index is taken to be
     missing a substation), the section between them lights up in the line's colour, and the rest of the lines and
     the idle substations fade. Zoomed out (trains hidden) the map is as usual. Clicking the status box (top right)
     turns the power view off and on. */
  const REACH = 2500 / MU, BASE = 1;   /* REACH in map units; BASE: opacity of lines with no train (0.14 faded them; 1 since 14 Nov 2026) */
  let powerOn = false;   /* the power view is switched off (14 Nov 2026): lines and substations always shown in full */
  const trainAlpha = k => Math.max(0, Math.min(1, (k - TRAINS_FROM) / (TRAINS_FULL - TRAINS_FROM)));
  window.liveLineAlpha = k => powerOn ? 1 - (1 - BASE) * trainAlpha(k) : 1;
  const cumOf = st => {                                    /* running length along a strand */
    if (!st.cum) { st.cum = [0]; for (let i = 1; i < st.length; i++) st.cum.push(st.cum[i - 1] + Math.hypot(st[i][0] - st[i - 1][0], st[i][1] - st[i - 1][1])); }
    return st.cum;
  };
  const posAt = (st, s) => {                               /* fractional index at running length s */
    const c = cumOf(st); let lo = 0, hi = c.length - 1;
    while (hi - lo > 1) { const m = (lo + hi) >> 1; if (c[m] <= s) lo = m; else hi = m; }
    return lo + Math.max(0, Math.min(1, (s - c[lo]) / ((c[hi] - c[lo]) || 1)));
  };
  /* Trains and station dots sit exactly on the line as the map draws it. The map does not draw straight segments
     between a lane's points: it simplifies each strand for the zoom level (runsOf), cuts it into runs, and draws each
     run as a curve through the midpoints of its points. Close in, that is several pixels off the straight segments.
     So the drawn curves are sampled here (per zoom level, once), each sample keeping the strand index it stands for
     and its lane-offset direction (the curve is linear in the offset, so any lane spacing can be applied later). */
  const drawnCache = new Map();
  function drawnFor(level) {
    if (drawnCache.has(level)) return drawnCache.get(level);
    const byStrand = new Map(), SUB = 8;
    routes.forEach((route, ri) => {
      if (route.dashed || !(variants.near.strands[ri] || []).length) return;
      for (const run of runsOf(route, level, 'near')) {
        const p = run.pts; if (p.length < 2) continue;
        const st = p[0][5] && p[0][5].st; if (!st) continue;
        const V = j => ({ x: p[j][0], y: p[j][1], ox: p[j][2] || 0, oy: p[j][3] || 0, i: p[j][5].i });
        const mid = (a, b) => ({ x: (a.x + b.x) / 2, y: (a.y + b.y) / 2, ox: (a.ox + b.ox) / 2, oy: (a.oy + b.oy) / 2, i: (a.i + b.i) / 2 });
        const out = byStrand.get(st) || []; byStrand.set(st, out);
        const quad = (A, C, B) => {                      /* about one sample per 10 m of curve (long simplified runs are long curves) */
          const len = Math.hypot(C.x - A.x, C.y - A.y) + Math.hypot(B.x - C.x, B.y - C.y), n = Math.max(SUB, Math.min(1500, Math.ceil(len / 0.18)));
          for (let k = 0; k <= n; k++) { const u = k / n, w = 1 - u, f = (a, c, b) => w * w * a + 2 * w * u * c + u * u * b;
          out.push({ x: f(A.x, C.x, B.x), y: f(A.y, C.y, B.y), ox: f(A.ox, C.ox, B.ox), oy: f(A.oy, C.oy, B.oy), i: A.i + (B.i - A.i) * u }); } };
        let start = V(0);
        for (let j = 2; j < p.length; j++) { const C = V(j - 1), B = mid(C, V(j)); quad(start, C, B); start = B; }
        const last = V(p.length - 1); out.push(start, last);       /* the closing straight piece */
      }
    });
    for (const list of byStrand.values()) list.sort((a, b) => a.i - b.i);
    drawnCache.set(level, byStrand); return byStrand;
  }
  function curveAt(st, pos, gap) {                       /* [x, y]: the lane point at fractional index pos, moved onto the drawn curve */
    const OF = (ax, ay) => window.laneOff ? laneOff(ax, ay, view.k) : [ax, ay];   /* the map's lane offsets, squeezed close in */
    const q = pointAt(st, pos), qo = OF(q[2], q[3]), tx = q[0] + qo[0] * gap, ty = q[1] + qo[1] * gap;
    const list = drawnFor(levelFor(view.k)).get(st);
    if (!list || list.length < 2) return [tx, ty];
    /* samples of this strand whose index is near pos (simplified runs can be long, so a wide window), then the
       nearest point on the sampled curve to the true lane point (the curve is at most a metre or two off it) */
    const W = 120; let lo = 0, hi = list.length - 1;
    { let a = 0, b = hi; while (a < b) { const m = (a + b) >> 1; if (list[m].i < pos - W) a = m + 1; else b = m; } lo = Math.max(0, a - 1); }
    { let a = lo, b = hi; while (a < b) { const m = (a + b + 1) >> 1; if (list[m].i > pos + W) b = m - 1; else a = m; } hi = Math.min(list.length - 1, a + 1); }
    /* coarse pass over every 12th sample, then the exact nearest segment around the best one */
    let cj = lo, cd = Infinity;
    for (let j = lo; j <= hi; j += 12) { const A = list[j], ao = OF(A.ox, A.oy), dx = A.x + ao[0] * gap - tx, dy = A.y + ao[1] * gap - ty, d = dx * dx + dy * dy; if (d < cd) { cd = d; cj = j; } }
    let best = null;
    for (let j = Math.max(lo, cj - 14); j < Math.min(hi, cj + 14); j++) {
      const A = list[j], B = list[j + 1];
      const ao = OF(A.ox, A.oy), bo = OF(B.ox, B.oy), ax = A.x + ao[0] * gap, ay = A.y + ao[1] * gap, bx = B.x + bo[0] * gap, by = B.y + bo[1] * gap;
      const ex = bx - ax, ey = by - ay, L = ex * ex + ey * ey, u = L ? Math.max(0, Math.min(1, ((tx - ax) * ex + (ty - ay) * ey) / L)) : 0;
      const x = ax + ex * u, y = ay + ey * u, d = (x - tx) * (x - tx) + (y - ty) * (y - ty);
      if (!best || d < best[2]) best = [x, y, d];
    }
    return best && best[2] < 0.25 ? [best[0], best[1]] : [tx, ty];   /* more than ~28 m away: not this curve, keep the lane point */
  }
  function stretch(st, a, b) {                             /* lane points from running length a to b */
    const pa = posAt(st, a), pb = posAt(st, b), out = [pointAt(st, pa)];
    for (let i = Math.floor(pa) + 1; i <= Math.ceil(pb) - 1; i++) out.push(pointAt(st, i));
    out.push(pointAt(st, pb)); return out;
  }
  /* each group's lanes in a coarse grid, for finding where a train is on them */
  const grids = new Map(), CELL = 1.5;
  function gridFor(key) {
    if (grids.has(key)) return grids.get(key);
    const g = new Map(), ri = routes.findIndex(r => !r.dashed && r.key === key), strands = ri < 0 ? [] : variants.near.strands[ri] || [];
    for (const st of strands) for (let i = 0; i + 1 < st.length; i++) {
      const c = Math.floor(st[i][0] / CELL) + ',' + Math.floor(st[i][1] / CELL);
      if (!g.has(c)) g.set(c, []); g.get(c).push([st, i]);
    }
    grids.set(key, g); return g;
  }
  function laneAt(key, x, y) {                             /* { st, s }: the nearest point of a lane of this group */
    const g = gridFor(key), cx0 = Math.floor(x / CELL), cy0 = Math.floor(y / CELL); let best = null;
    for (let dx = -1; dx <= 1; dx++) for (let dy = -1; dy <= 1; dy++) for (const [st, i] of g.get((cx0 + dx) + ',' + (cy0 + dy)) || []) {
      const a = st[i], b = st[i + 1], ex = b[0] - a[0], ey = b[1] - a[1], L = ex * ex + ey * ey;
      const u = L ? Math.max(0, Math.min(1, ((x - a[0]) * ex + (y - a[1]) * ey) / L)) : 0, d = Math.hypot(x - a[0] - u * ex, y - a[1] - u * ey);
      if (!best || d < best.d) best = { d, st, s: cumOf(st)[i] + u * Math.sqrt(L) };
    }
    return best && best.d < 0.5 ? best : null;
  }
  /* each substation's place on every lane of the lines it feeds that passes close by (parallel lanes of one colour
     each get it: a substation feeds all the tracks of its line); a line not recorded: any lane within 250 m */
  const feeders = new Map();                               /* strand -> [{ sub, key, s }] sorted by s */
  if (powerOn) for (const sub of subs) {
    const d = sub.data; if (d.status === 'off') continue;  /* decommissioned or converted: feeds nothing */
    let keys = d.lines.filter(k => GROUP_COLOR[k] && k !== 'EL');
    const near = !keys.length; if (near) keys = GROUP_KEYS.concat(['SIR']);
    const lim = (near ? 250 : 600) / MU, R = Math.ceil(lim / CELL);
    for (const key of keys) {
      const g = gridFor(key), best = new Map();             /* strand -> nearest point on it */
      const cx0 = Math.floor(sub.x / CELL), cy0 = Math.floor(sub.y / CELL);
      for (let dx = -R; dx <= R; dx++) for (let dy = -R; dy <= R; dy++) for (const [st, i] of g.get((cx0 + dx) + ',' + (cy0 + dy)) || []) {
        const a = st[i], b = st[i + 1], ex = b[0] - a[0], ey = b[1] - a[1], L = ex * ex + ey * ey;
        const u = L ? Math.max(0, Math.min(1, ((sub.x - a[0]) * ex + (sub.y - a[1]) * ey) / L)) : 0, dd = Math.hypot(sub.x - a[0] - u * ex, sub.y - a[1] - u * ey);
        if (dd <= lim && (!best.has(st) || dd < best.get(st).d)) best.set(st, { d: dd, s: cumOf(st)[i] + u * Math.sqrt(L) });
      }
      for (const [st, b] of best) { if (!feeders.has(st)) feeders.set(st, []); feeders.get(st).push({ sub, key, s: b.s }); }
    }
  }
  for (const list of feeders.values()) list.sort((a, b) => a.s - b.s);
  function feedersOf(key, at) {                            /* the nearest feeding substation behind and ahead */
    const list = feeders.get(at.st); if (!list) return [];
    let behind = null, ahead = null;
    for (const f of list) {
      if (f.key !== key) continue;
      if (f.s <= at.s) { if (at.s - f.s < REACH) behind = f; }
      else { if (f.s - at.s < REACH && !ahead) ahead = f; }
    }
    return [behind, ahead];
  }
  /* substation icons: shown only while they feed a train (fading over about half a second) */
  function fadeIcons(feeding, pa, dt) {
    const rate = Math.min(1, dt / 0.5);
    for (const sub of subs) {
      const want = 1 - pa * (feeding.has(sub) ? 0 : 1);
      const now = sub.liveA === undefined ? want : sub.liveA + (want - sub.liveA) * rate;
      if (now !== sub.liveA) { sub.liveA = now; sub.g.style.opacity = now.toFixed(3); sub.g.style.pointerEvents = now < 0.15 ? 'none' : ''; }
    }
  }
  let last = performance.now(), shownDots = [], dotR = 4, unfed = 0;
  /* a line clicked (or picked in the legend) leaves only its own trains and stations */
  const keptBy = svc => {
    const iso = isolate; if (!iso) return true;
    if (iso.els) return false;                             /* only the demolished els are shown */
    const key = keyOf(svc);
    return iso.co ? KEY_CO[key] === iso.co : iso.key === key;
  };
  /* hovering a station dot shows the station's name (and the services stopping there by day) */
  document.getElementById('svg').addEventListener('mousemove', ev => {
    if (!shownDots.length) return;
    const r = ev.currentTarget.getBoundingClientRect(), mx = ev.clientX - r.left, my = ev.clientY - r.top;
    let best = null;
    for (const [sx, sy, d] of shownDots) { const e = Math.hypot(sx - mx, sy - my); if (e <= dotR + 3 && (!best || e < best.e)) best = { e, d }; }
    if (best) { showTip(ev, [[best.d.name, '#000'], ['Stops: ' + best.d.rts.replace(/ /g, ', '), '#555']]); ev.currentTarget.classList.add('online'); }
  });
  function frame(nowMs, once) {
    const gapS = (nowMs - last) / 1000, dt = Math.min(0.2, gapS); last = nowMs;
    if (gapS > 3) for (const tr of trains.values()) tr.m = null;   /* back from a hidden tab: place everyone afresh */
    const { w, h } = size, dpr = window.devicePixelRatio || 1, k = view.k;
    if (cv.width !== Math.round(w * dpr) || cv.height !== Math.round(h * dpr)) { cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr); }
    cx.setTransform(1, 0, 0, 1, 0, 0); cx.clearRect(0, 0, cv.width, cv.height);
    if (!hidden.subway) {
      cx.setTransform(dpr * k, 0, 0, dpr * k, dpr * view.tx, dpr * view.ty);
      const weight = Math.min(4, Math.max(1.5, 1.5 + Math.log2(k / fitK) * 0.5)), casing = Math.max(1, weight * 0.45), gap = (weight + casing + (window.laneExtra ? laneExtra(k) : 0)) / k;   /* same lane spacing as the map */
      const x0 = -view.tx / k - 2, y0 = -view.ty / k - 2, x1 = (w - view.tx) / k + 2, y1 = (h - view.ty) / k + 2;
      /* trains first (their places feed the power view), drawn last */
      const sz = Math.max(0.55, Math.min(1, k / fitK / 6));   /* smaller trains when the whole city is in view */
      const T = Date.now() / 1000, len = weight * 3.0 * sz / k, wd = weight * 1.45 * sz / k;
      const ta = hidden.trains ? 0 : trainAlpha(k);         /* trains fade out zoomed out; none when switched off in the legend */
      const byColor = new Map(), live = [];
      for (const tr of trains.values()) {
        const q = step(tr, T, dt); if (!q || !keptBy(tr.svc)) continue;
        const qo = window.laneOff ? laneOff(q[2], q[3], k) : [q[2], q[3]], X = q[0] + qo[0] * gap, Y = q[1] + qo[1] * gap;
        live.push([tr, q]);
        if (X < x0 || X > x1 || Y < y0 || Y > y1) continue;
        /* the train's body: a short stretch of its own lane centred on it, so it bends with the line on curves */
        let body = null;
        if (ta > 0) {
          /* the lane the train is actually on (carried along its path); searching for the nearest lane is only the
             fallback, as it can pick a neighbouring lane on the same centreline */
          let at = null;
          if (q.st) { const c = cumOf(q.st), i = Math.max(0, Math.min(q.st.length - 2, Math.floor(q.pos))); at = { st: q.st, s: c[i] + (c[i + 1] - c[i]) * (q.pos - i) }; }
          if (!at) at = laneAt(keyOf(tr.svc), q[0], q[1]);
          if (!at) for (const k2 of GROUP_KEYS.concat(['SIR'])) { const a2 = laneAt(k2, q[0], q[1]); if (a2 && (!at || a2.d < at.d)) at = a2; }
          if (at) {
            /* length: a fixed size on screen (real length, tried on 14 Nov 2026, was far too long close in) */
            const c = cumOf(at.st), endS = c[c.length - 1], L = len;
            const s0 = Math.max(0, at.s - L), s1 = Math.min(endS, at.s + L), N = Math.max(10, Math.min(80, Math.ceil((s1 - s0) * k / 6)));
            body = []; for (let j = 0; j <= N; j++) body.push(curveAt(at.st, posAt(at.st, s0 + (s1 - s0) * j / N), gap));   /* on the drawn curve */
          }
        }
        if (!body) body = [[X - q[4] * len, Y - q[5] * len], [X + q[4] * len, Y + q[5] * len]];
        const c = colorOf(tr.svc); if (!byColor.has(c)) byColor.set(c, []); byColor.get(c).push(body);
      }
      /* power view. A train draws from the two substations at the ends of the section it is in, one behind it and
         one ahead: that whole section lights up in the line's colour, and hands over to the next pair as the train
         passes a substation. With only one of them recorded within reach, the stretch from it to the train lights. */
      const pa = powerOn ? ta : 0;
      const feeding = new Set(); unfed = 0;
      if (pa > 0) {
        cx.globalAlpha = pa; cx.lineCap = 'round'; cx.lineJoin = 'round';
        const byKey = new Map(), done = new Set();
        for (const [tr, q] of live) {
          let key = keyOf(tr.svc), at = laneAt(key, q[0], q[1]);
          if (!at) for (const k2 of GROUP_KEYS.concat(['SIR'])) { const a2 = laneAt(k2, q[0], q[1]); if (a2 && (!at || a2.d < at.d)) { at = a2; key = k2; } }   /* on another line's track (e.g. a night 4 on the 3's): that line's sections */
          if (!at) { unfed++; continue; }
          const [behind, ahead] = feedersOf(key, at);
          if (!behind && !ahead) { unfed++; continue; }
          for (const f of [behind, ahead]) if (f) feeding.add(f.sub);
          const a = behind ? behind.s : at.s, b = ahead ? ahead.s : at.s;
          const id = at.st.length + ':' + Math.round(at.st[0][0] * 10) + ':' + key + ':' + Math.round(a * 20) + ':' + Math.round(b * 20);
          if (done.has(id)) continue; done.add(id);
          if (!byKey.has(key)) byKey.set(key, new Path2D());
          const path = byKey.get(key); let first = true;
          for (const pt of stretch(at.st, a, b)) { const X = pt[0] + pt[2] * gap, Y = pt[1] + pt[3] * gap; if (first) { path.moveTo(X, Y); first = false; } else path.lineTo(X, Y); }
        }
        /* the white border only while the rest of the line is faded: over a full-strength line its ends would cut
           white nicks across the line where a section stops */
        cx.lineCap = 'butt';
        for (const [key, path] of byKey) {
          if (BASE < 1) { cx.strokeStyle = '#fff'; cx.lineWidth = (weight + 2 * casing) / k; cx.stroke(path); }
          cx.strokeStyle = GROUP_COLOR[key] || '#888'; cx.lineWidth = weight / k; cx.stroke(path);
        }
        cx.globalAlpha = 1;
      }
      if (powerOn) fadeIcons(feeding, pa, dt);
      /* stations: black dots with a white outline, shown (fading in) only once the streets appear. Dots that touch
         (the lanes of several lines side by side at one station) merge into one rounded bar across them. */
      const sa = roadAlpha(k); shownDots = []; dotR = weight * 1.35;
      if (sa > 0) {
        const rd = dotR / k, pts = [];
        for (const d of dots) {
          if (!keptBy(d.svc)) continue;
          const r0 = pointAt(d.st, d.pos); if (r0[0] < x0 - 1 || r0[0] > x1 + 1 || r0[1] < y0 - 1 || r0[1] > y1 + 1) continue;   /* off screen: skip the projection */
          const [X, Y] = curveAt(d.st, d.pos, gap);         /* on the line as drawn */
          if (X < x0 || X > x1 || Y < y0 || Y > y1) continue;
          pts.push([X, Y]);
          shownDots.push([X * k + view.tx, Y * k + view.ty, d]);   /* window position, for the hover label */
        }
        /* group dots closer than a dot's width plus a hair (union-find over a coarse grid) */
        const par = pts.map((_, i) => i), find = i => { while (par[i] !== i) i = par[i] = par[par[i]]; return i; };
        const lim = 2 * rd + 1 / k, grid = new Map(), cell = lim;
        pts.forEach(([X, Y], i) => {
          const gx = Math.floor(X / cell), gy = Math.floor(Y / cell);
          for (let dx = -1; dx <= 1; dx++) for (let dy = -1; dy <= 1; dy++) for (const j of grid.get((gx + dx) + ',' + (gy + dy)) || [])
            if (Math.hypot(pts[j][0] - X, pts[j][1] - Y) < lim) par[find(i)] = find(j);
          const key = gx + ',' + gy; if (!grid.has(key)) grid.set(key, []); grid.get(key).push(i);
        });
        const groups = new Map(); pts.forEach((p, i) => { const r = find(i); if (!groups.has(r)) groups.set(r, []); groups.get(r).push(p); });
        /* each group: a bar between its two farthest dots (one dot: a bar of no length, i.e. a dot) */
        const bars = new Path2D();
        for (const g of groups.values()) {
          let a = g[0], b = g[0], far = 0;
          for (let i = 0; i < g.length; i++) for (let j = i + 1; j < g.length; j++) { const d = Math.hypot(g[i][0] - g[j][0], g[i][1] - g[j][1]); if (d > far) { far = d; a = g[i]; b = g[j]; } }
          bars.moveTo(a[0], a[1]); bars.lineTo(far < 1e-6 ? a[0] + 1e-4 : b[0], b[1]);   /* a lone dot: a bar too short to see */
        }
        cx.globalAlpha = sa; cx.lineCap = 'round';
        /* the white border first under every bar and dot, then the black on top, so borders never cut a neighbour */
        cx.strokeStyle = '#fff'; cx.lineWidth = 2 * rd + 2.4 / k; cx.stroke(bars);
        cx.strokeStyle = '#000'; cx.lineWidth = 2 * rd; cx.stroke(bars);
        cx.globalAlpha = 1;
      }
      /* trains: a short capsule in the darker line colour, pointing the way it is going */
      cx.lineCap = 'round'; cx.lineJoin = 'round'; cx.globalAlpha = ta;
      if (ta > 0) for (const [c, list] of byColor) {
        const p = new Path2D();
        for (const body of list) { p.moveTo(body[0][0], body[0][1]); for (let i = 1; i < body.length; i++) p.lineTo(body[i][0], body[i][1]); }
        cx.strokeStyle = '#fff'; cx.lineWidth = wd + 2 / k; cx.stroke(p);
        cx.strokeStyle = c; cx.lineWidth = wd; cx.stroke(p);
      }
      cx.globalAlpha = 1;
    }
    if (!once) requestAnimationFrame(frame);
  }
  requestAnimationFrame(frame);
  /* the PDF export: this frame's trains and station dots, drawn into another context */
  window.liveRenderTo = target => { cx = target; try { frame(performance.now(), true); } finally { cx = screenCx; } };

  /* ---------- reading the feeds ---------- */
  const status = document.createElement('div'); status.id = 'livestatus'; document.getElementById('map').appendChild(status);

  let lastOk = 0, failed = 0;
  async function poll() {
    const got = await Promise.all(FEEDS.map(u => {
      const ac = new AbortController(), timer = setTimeout(() => ac.abort(), FETCH_TIMEOUT);
      return fetch(u, { cache: 'no-store', signal: ac.signal }).then(r => r.ok ? r.arrayBuffer() : null).catch(() => null).finally(() => clearTimeout(timer));
    }));
    const feeds = [];
    got.forEach((b, idx) => { if (b) try { feeds.push({ idx, ...decodeFeed(new Uint8Array(b)) }); } catch (e) { /* a garbled answer counts as no answer */ } });
    failed = got.length - feeds.length;
    if (feeds.length) { update(feeds); lastOk = Date.now(); }
    setTimeout(poll, POLL * 1000);
  }
  setInterval(() => {
    const age = lastOk ? Math.round((Date.now() - lastOk) / 1000) : null;
    status.textContent = (lastOk ? `Live · ${trains.size} trains · updated ${age} s ago` + (failed ? ` · ${failed} feed${failed > 1 ? 's' : ''} not answering` : '') : 'Live · connecting to the MTA feeds…');
  }, 1000);
  poll();
  window.liveDebug = { trains, dots, project, pathBetween, place, step, laneAt, feedersOf, feeders, stretch, cumOf, curveAt, posAt };
})();
