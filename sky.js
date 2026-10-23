// PRIGH sky: the whole map as stars in three dimensions on one canvas (no libraries), and a constellation for any
// star you pick. Positions come fixed from /api/sky (domains as balls on a globe; hubs at each core). Only drawing
// happens here, so fifty thousand stars cost nothing; a constellation runs a small force layout on a few hundred.
// Drag to orbit in any direction, wheel to zoom, right-drag (or Shift+drag) to move.
const css = k => getComputedStyle(document.documentElement).getPropertyValue(k).trim();
const DOMS = ['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J', 'X'];
const color = {};
for (const d of DOMS) color[d] = css('--' + d);
const PROOF = { 0: css('--ink-soft'), 1: css('--accent'), 2: css('--verified'), 3: css('--bad') };
const SERVICE = new Set(['RETURN_PREPARED_BY', 'FILINGS_SUBMITTED_BY', 'SAME_FILED_ADDRESS', 'RESIDENT_AGENT_IS']);   // shared service providers (signals, drawn faint)
const PAPER = css('--paper'), INK = css('--ink');

const canvas = document.getElementById('sky'), ctx = canvas.getContext('2d');
const tip = document.getElementById('tip'), panel = document.getElementById('panel'), status = document.getElementById('status');
let stars = [], names = [], dimmed = new Set();
const cam = { yaw: 0.5, pitch: -0.3, dist: 4000, tx: 0, ty: 0, tz: 0, panX: 0, panY: 0 };
let mode = 'sky';                    // 'sky' | 'constellation'
let con = null;                      // {center, nodes:[{id,label,dom,person,deg,x,y,z,...}], edges:[...], byId}
let hover = null, dirty = true, alpha = 0, spin = false;
let projected = [];                  // last frame's screen positions, for picking
let domainMarks = [];                // {d, name, count, x, y, z, radius}: one label per domain ball
let labelBoxes = [];                 // where each galaxy's name was last drawn on screen: a click on it flies to that galaxy
let sectorMarks = [], subNames = {}; // sub-domain wedges inside each ball, and code -> label
// Gravity: what sinks to the core of each domain ball. 'connections' is a count (how many filed records touch an
// entity); 'influence' is a model (weighted reach through the verified graph). Each star keeps both positions and
// glides between them when the toggle flips, so the eye can follow who moves.
const PUBLIC_PAGE = document.body.dataset.public === '1';      // the read-only public copy: no drafting, no workbench
const STATIC = document.body.dataset.static === '1';           // the GitHub Pages copy: the server's answers written out as files under data/
const shard = id => { let h = 0; for (const ch of id) h = (h * 31 + ch.charCodeAt(0)) >>> 0; return (h % 256).toString(16).padStart(2, '0'); };
const _shards = new Map();
async function loadShard(kind, id) {
  const k = `${kind}/${shard(id)}`;
  if (!_shards.has(k)) _shards.set(k, fetch(`data/${k}.json`).then(r => r.ok ? r.json() : {}).catch(() => ({})));
  return _shards.get(k);
}
// the constellation, built here from edge and node shards: the same rule as the server (direct connections, and through a person their organizations; capped to 400)
async function staticConstellation(nid, hops) {
  const edgesOf = async id => (await loadShard('edges', id))[id] || [];
  const nodeOf = async id => (await loadShard('nodes', id))[id];
  if (!(await nodeOf(nid))) return null;
  const keep = new Set([nid]); let frontier = [nid];
  for (let h = 0; h < hops; h++) {
    const nxt = [];
    for (const u of frontier) for (const e of await edgesOf(u)) {
      const v = e.s === u ? e.t : e.s;
      if (keep.has(v)) continue;
      keep.add(v); nxt.push(v);
      const nv = await nodeOf(v);
      if (nv && nv.person) for (const e2 of await edgesOf(v)) { const w = e2.s === v ? e2.t : e2.s; if (!keep.has(w)) { keep.add(w); nxt.push(w); } }
    }
    frontier = nxt;
  }
  const nodes = {}; for (const x of keep) nodes[x] = await nodeOf(x);
  let ids = [...keep].filter(x => nodes[x]);
  if (ids.length > 400) ids = [nid, ...ids.filter(x => x !== nid).sort((a, b) => nodes[b].deg - nodes[a].deg).slice(0, 399)];
  const set = new Set(ids), seen = new Set(), edges = [];
  for (const x of ids) for (const e of await edgesOf(x)) if (set.has(e.s) && set.has(e.t) && !seen.has(e.id)) { seen.add(e.id); edges.push(e); }
  return { center: nid, nodes: ids.map(x => ({ ...nodes[x], id: x })), edges };
}
let gravity = 'connections', glide = 1, glideStart = 0, influenceNote = '';
const PICTURES = new Set(['flows', 'loops']);                 // modes with no stars: a drawn picture instead
const picture = () => PICTURES.has(gravity);
// 'connections' and 'influence' sink to each domain ball's core. 'flows' is not a gravity but a different picture: no
// stars at all, the ten groups around a circle and the bands of money and people between them (see drawFlows).

// ------------------------------------------------------------ data
async function load() {
  const res = await fetch(STATIC ? 'data/sky.json' : '/api/sky').then(r => r.json());
  stars = res.nodes.map(([id, label, dom, person, deg, proof, x, y, z, x2, y2, z2, infl, sub, x3, y3, z3, dmn, others]) => ({ id, label, dom, person: !!person, deg, proof,
    x, y, z, fx: x, fy: y, fz: z, infl, sub: sub || '', dmn: dmn ?? 0, others: others || '', r: person ? 1.1 : 1.5 + Math.log2(deg + 1) * 1.1,
    pos: { connections: [x, y, z], influence: [x2, y2, z2], sky: [x3 ?? x, y3 ?? y, z3 ?? z] } }));
  influenceNote = res.influence_note || '';
  names = stars.map(s => ({ s, t: s.label.toLowerCase() }));
  const counts = {};
  for (const s of stars) counts[s.dom] = (counts[s.dom] || 0) + 1;
  domainMarks = Object.entries(res.anchors || {}).map(([d, [x, y, z]]) =>
    ({ d, name: res.domains[d] || d, count: (res.counts || {})[d] ?? counts[d] ?? 0, x, y, z, radius: (res.radius || {})[d] || 60 + 44 * Math.cbrt(Math.max(counts[d] || 1, 1)),
       core: (res.core || {})[d] || null, anchors: res.anchors }));
  // sub-domains: wedges of each ball (from /api/sky); a label at each wedge's mid-longitude on the ball's equator, a faint meridian at each boundary
  // sub-domains are the galaxies' spiral arms: the server gives each arm's spine (points from the core outward) and a label spot
  sectorMarks = [];
  for (const m of domainMarks) {
    for (const w of (res.subsectors || {})[m.d] || []) {
      const at = w.label_at || [m.x, m.y, m.z];
      sectorMarks.push({ d: m.d, code: w.code, name: w.label, count: w.count, other: w.code.endsWith('.other'),
        x: at[0], y: at[1], z: at[2], cx: m.x, cy: m.y, cz: m.z, R: m.radius, spine: w.spine || [] });
    }
  }
  subNames = {};
  for (const w of sectorMarks) subNames[w.code] = w.name;
  const chips = document.getElementById('domchips');
  chips.innerHTML = Object.entries(res.domains).map(([d, name]) =>
    `<button class="chip" data-dom="${d}" title="${name}"><span class="d" style="background:${color[d]}"></span>${d}</button>`).join('');
  chips.addEventListener('click', ev => {
    const b = ev.target.closest('[data-dom]'); if (!b) return;
    const d = b.dataset.dom;
    if (dimmed.has(d)) dimmed.delete(d); else dimmed.add(d);
    chips.querySelectorAll('.chip').forEach(c => c.classList.toggle('off', dimmed.has(c.dataset.dom)));
    dirty = true; if (gravity === 'flows') flowsStatus();
  });
  document.getElementById('loading').remove();
  skyGenerated = res.generated.slice(0, 10);
  skyStatus = `${stars.length.toLocaleString()} entities · generated ${res.generated.slice(0, 10)}`
    + (res.building ? ' · the map changed: a new sky is being built, entities added since are not placed yet (reload in a few minutes)' : '')
    + ' · drag to orbit · wheel to zoom where you point · click a galaxy\'s name to fly to it · right-drag to move';
  status.textContent = skyStatus;
  fitAll();
}
let skyStatus = '', skyGenerated = '';

// ------------------------------------------------------------ camera
function size() {
  const dpr = window.devicePixelRatio || 1, W = window.innerWidth, H = window.innerHeight;
  if (canvas.width !== W * dpr || canvas.height !== H * dpr) { canvas.width = W * dpr; canvas.height = H * dpr; }
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  return { W, H };
}
function project(p, W, H) {
  const x0 = p.x - cam.tx, y0 = p.y - cam.ty, z0 = p.z - cam.tz;
  const cy = Math.cos(cam.yaw), sy = Math.sin(cam.yaw), cp = Math.cos(cam.pitch), sp = Math.sin(cam.pitch);
  const x1 = x0 * cy - z0 * sy, z1 = x0 * sy + z0 * cy;
  const y2 = y0 * cp - z1 * sp, z2 = y0 * sp + z1 * cp;
  const zc = z2 + cam.dist;
  if (zc < 30) return null;
  const f = Math.min(W, H) * 0.95 / zc;
  return { sx: W / 2 + cam.panX + x1 * f, sy: (H + 58) / 2 + cam.panY + y2 * f, f, z: zc };
}
function fitAll() {
  const pts = mode === 'sky' ? stars : con.nodes;
  if (!pts.length) return;
  let cx = 0, cy = 0, cz = 0;
  for (const p of pts) { cx += p.x; cy += p.y; cz += p.z; }
  cam.tx = cx / pts.length; cam.ty = cy / pts.length; cam.tz = cz / pts.length;
  let r = 100;
  for (const p of pts) r = Math.max(r, Math.hypot(p.x - cam.tx, p.y - cam.ty, p.z - cam.tz));
  cam.dist = r * 2.3; cam.panX = cam.panY = 0; dirty = true;
}
// Zoom toward the pointer: the point under the cursor stays where it is, so the wheel can dive into any galaxy, not only the center.
const zoom = (f, mx, my) => {
  const before = cam.dist, after = Math.min(60000, Math.max(60, cam.dist / f)), k = before / after;
  if (mx != null) {
    const W = window.innerWidth, H = window.innerHeight;
    cam.panX = (mx - W / 2) - ((mx - W / 2) - cam.panX) * k;
    cam.panY = (my - (H + 58) / 2) - ((my - (H + 58) / 2) - cam.panY) * k;
  }
  cam.dist = after; dirty = true;
};
// Fly to a galaxy: its center becomes the orbit's center and the view fits its disc.
function flyTo(m) {
  cam.tx = m.x; cam.ty = m.y; cam.tz = m.z; cam.panX = cam.panY = 0;
  cam.dist = Math.max(200, m.radius * 2.6); dirty = true;
}

// ------------------------------------------------------------ draw
const depthAlpha = z => Math.max(0.15, Math.min(1, 1.7 - z / (cam.dist * 1.5)));

// Each galaxy's singularity: a dark point at the center that nothing sits on, with a thin bright horizon ring at the radius
// where the strongest entities orbit. Drawn under the stars, only in the per-galaxy gravities.
function singularities(W, H) {
  for (const m of domainMarks) {
    if (!m.core || (dimmed.size && dimmed.has(m.d))) continue;
    const c = project(m, W, H); if (!c) continue;
    const horizon = m.core[0] * c.f, ring = m.core[1] * c.f;
    if (ring < 6) continue;
    const a = Math.max(0.2, Math.min(1, 1.9 - c.z / (cam.dist * 1.4)));
    ctx.globalAlpha = 0.9 * a; ctx.fillStyle = '#000';
    ctx.beginPath(); ctx.arc(c.sx, c.sy, Math.max(2, horizon * 0.6), 0, Math.PI * 2); ctx.fill();
    ctx.globalAlpha = 0.55 * a; ctx.strokeStyle = color[m.d] || INK; ctx.lineWidth = Math.max(0.8, Math.min(2, ring / 40));
    ctx.beginPath(); ctx.arc(c.sx, c.sy, horizon, 0, Math.PI * 2); ctx.stroke();
    ctx.globalAlpha = 0.18 * a; ctx.setLineDash([3, 5]);
    ctx.beginPath(); ctx.arc(c.sx, c.sy, ring, 0, Math.PI * 2); ctx.stroke();
    ctx.setLineDash([]);
  }
  ctx.globalAlpha = 1;
}

function drawSky(W, H) {
  ctx.fillStyle = PAPER; ctx.fillRect(0, 0, W, H);
  singularities(W, H);
  const big = []; projected = [];
  for (const s of stars) {
    const q = project(s, W, H); if (!q || q.sx < -20 || q.sx > W + 20 || q.sy < -20 || q.sy > H + 20) continue;
    const r = Math.min(14, Math.max(0.5, s.r * q.f * 5));
    const dim = dimmed.size && dimmed.has(s.dom) ? 0.1 : 1;
    const da = depthAlpha(q.z);
    const a = (s.person ? 0.3 : s.proof === 0 ? 0.5 : s.proof === -1 ? 0.3 : 0.9) * dim * da;
    if (!s.person && s.proof >= 1 && r > 2) {                       // the glow of proof
      ctx.globalCompositeOperation = 'lighter';
      ctx.globalAlpha = (s.proof === 2 ? 0.16 : s.proof === 3 ? 0.4 : 0.1) * dim * da;
      ctx.fillStyle = PROOF[s.proof];
      ctx.beginPath(); ctx.arc(q.sx, q.sy, r * 2.2, 0, Math.PI * 2); ctx.fill();
      ctx.globalCompositeOperation = 'source-over';
    }
    ctx.globalAlpha = a;
    if (s.others && r > 2.5) {                                      // in several domains: a wheel of every domain's color, its first domain on top
      const all = s.dom + s.others, step = Math.PI * 2 / all.length;
      ctx.globalAlpha = s.person ? Math.min(1, a + 0.35) : a;        // people are faint discs; their wheels get a little more light
      for (let i = 0; i < all.length; i++) {
        ctx.fillStyle = color[all[i]] || color.X;
        ctx.beginPath(); ctx.moveTo(q.sx, q.sy); ctx.arc(q.sx, q.sy, r, -Math.PI / 2 + i * step, -Math.PI / 2 + (i + 1) * step); ctx.closePath(); ctx.fill();
      }
    } else {
      ctx.fillStyle = s.person ? '#9fb6ff' : color[s.dom] || color.X;
      ctx.beginPath(); ctx.arc(q.sx, q.sy, r, 0, Math.PI * 2); ctx.fill();
    }
    if ((!s.person || s.others) && r > 2.2) {                       // a dark rim on every institution and every wheel, so touching discs stay two discs
      ctx.globalAlpha = Math.min(1, a + 0.2); ctx.strokeStyle = '#05070c'; ctx.lineWidth = r > 6 ? 1.4 : 0.9;
      ctx.beginPath(); ctx.arc(q.sx, q.sy, r, 0, Math.PI * 2); ctx.stroke();
    }
    projected.push({ s, sx: q.sx, sy: q.sy, r });
    if (!s.person && r > 5 && dim === 1) big.push({ s, sx: q.sx, sy: q.sy, r, z: q.z });
  }
  ctx.globalAlpha = 1;
  sectorLines(W, H); domainLabels(W, H); sectorLabels(W, H);
  labels(big.sort((p, q) => q.r - p.r).slice(0, 40));
  if (hover) ring(hover);
}

// Each ball's sub-domains are wedges of longitude. A faint meridian marks each boundary and the wedge's name sits on
// the equator at its middle, both only once the ball is big enough on screen to read, fading with depth.
function ballScale(m, W, H) {
  const c = project(m.cx !== undefined ? { x: m.cx, y: m.cy, z: m.cz } : m, W, H);
  return c ? { c, px: c.f * m.R } : null;
}
function sectorLines(W, H) {
  ctx.lineWidth = 1;
  for (const w of sectorMarks) {
    if (dimmed.size && dimmed.has(w.d)) continue;
    const b = ballScale(w, W, H); if (!b || b.px < 70) continue;
    const a = Math.min(0.35, (b.px - 70) / 400) * Math.max(0.2, Math.min(1, 1.9 - b.c.z / (cam.dist * 1.4)));
    ctx.globalAlpha = a; ctx.strokeStyle = color[w.d] || INK;
    ctx.beginPath();
    let first = true;
    for (const [x, y, z] of w.spine) {                                // the arm's spine, from the core outward
      const q = project({ x, y, z }, W, H);
      if (!q) { first = true; continue; }
      if (first) { ctx.moveTo(q.sx, q.sy); first = false; } else ctx.lineTo(q.sx, q.sy);
    }
    ctx.stroke();
  }
  ctx.globalAlpha = 1;
}
function sectorLabels(W, H) {
  ctx.textAlign = 'center';
  for (const w of sectorMarks) {
    if (dimmed.size && dimmed.has(w.d)) continue;
    const b = ballScale(w, W, H); if (!b || b.px < 90) continue;
    const q = project(w, W, H); if (!q) continue;
    const front = q.z <= b.c.z + w.R * 0.15;                            // the far side of the ball stays quiet
    const a = (front ? 0.95 : 0.25) * Math.min(1, (b.px - 90) / 300 + 0.4) * Math.max(0.2, Math.min(1, 1.9 - q.z / (cam.dist * 1.4)));
    const px = Math.max(9, Math.min(13, 8 + b.px / 120));
    ctx.globalAlpha = a;
    ctx.font = `${w.other ? '' : '600 '}${px}px "IBM Plex Mono", ui-monospace, monospace`;
    const t = `${w.name} · ${w.count.toLocaleString()}`;
    ctx.lineWidth = 3; ctx.strokeStyle = PAPER; ctx.strokeText(t, q.sx, q.sy);
    ctx.fillStyle = w.other ? css('--ink-soft') : color[w.d]; ctx.fillText(t, q.sx, q.sy);
  }
  ctx.globalAlpha = 1;
}

// Each domain's name floats just above its ball, fading with depth so the far side of the globe stays quiet.
function domainLabels(W, H) {
  ctx.textAlign = 'center';
  labelBoxes = [];
  for (const m of domainMarks) {
    if (dimmed.size && dimmed.has(m.d)) continue;
    const top = project({ x: m.x, y: m.y - m.radius, z: m.z }, W, H), c = project(m, W, H);
    if (!top || !c) continue;
    const a = Math.max(0.25, Math.min(1, 1.9 - c.z / (cam.dist * 1.4)));
    const big = Math.max(10, Math.min(22, 11 + c.f * 60));
    const y = Math.min(top.sy, c.sy) - 14;
    ctx.globalAlpha = a;
    ctx.font = `600 ${big}px "Fraunces", Georgia, serif`;
    ctx.lineWidth = 4; ctx.strokeStyle = PAPER; ctx.strokeText(m.name, c.sx, y);
    ctx.fillStyle = color[m.d]; ctx.fillText(m.name, c.sx, y);
    labelBoxes.push({ m, x: c.sx - ctx.measureText(m.name).width / 2 - 6, y: y - big, w: ctx.measureText(m.name).width + 12, h: big * 1.9 });
    ctx.font = `${Math.max(9, big * 0.55)}px "IBM Plex Mono", ui-monospace, monospace`;
    ctx.strokeText(`${m.d} · ${m.count.toLocaleString()} entities`, c.sx, y + big * 0.8);
    ctx.fillStyle = css('--ink-soft'); ctx.fillText(`${m.d} · ${m.count.toLocaleString()} entities`, c.sx, y + big * 0.8);
  }
  ctx.globalAlpha = 1;
}

function labels(list) {
  ctx.font = '11px "IBM Plex Sans", system-ui, sans-serif'; ctx.textAlign = 'center';
  const placed = [];
  for (const o of list) {
    const t = o.s.label.length > 34 ? o.s.label.slice(0, 32) + '…' : o.s.label;
    const w = ctx.measureText(t).width, box = [o.sx - w / 2 - 3, o.sy + o.r + 3, o.sx + w / 2 + 3, o.sy + o.r + 16];
    if (placed.some(b => box[0] < b[2] && box[2] > b[0] && box[1] < b[3] && box[3] > b[1])) continue;
    placed.push(box);
    ctx.lineWidth = 3; ctx.strokeStyle = PAPER; ctx.strokeText(t, o.sx, o.sy + o.r + 13);
    ctx.fillStyle = INK; ctx.fillText(t, o.sx, o.sy + o.r + 13);
  }
}
function ring(o) {
  ctx.strokeStyle = INK; ctx.lineWidth = 1.5; ctx.beginPath(); ctx.arc(o.sx, o.sy, o.r + 4, 0, Math.PI * 2); ctx.stroke();
}

function drawConstellation(W, H) {
  ctx.fillStyle = PAPER; ctx.fillRect(0, 0, W, H);
  const sel = con.center, pr = new Map();
  for (const n of con.nodes) { const q = project(n, W, H); if (q) pr.set(n.id, q); }
  for (const e of con.edges) {
    const a = pr.get(e.s), b = pr.get(e.t); if (!a || !b) continue;
    const p = e.proof;
    const service = SERVICE.has(e.type);                           // shared service providers: a faint dotted thread, a signal not a role
    ctx.strokeStyle = p === 'confirmed' ? PROOF[2] : p === 'alert' ? PROOF[3] : p === 'one source' ? PROOF[1] : PROOF[0];
    ctx.globalAlpha = (p === 'not checked yet' ? 0.45 : 0.9) * depthAlpha((a.z + b.z) / 2) * (service ? 0.45 : 1);
    ctx.lineWidth = e.s === sel || e.t === sel ? 1.8 : 1;
    ctx.setLineDash(service ? [1, 4] : !e.active ? [5, 5] : p === 'one source' ? [2, 4] : []);
    ctx.beginPath(); ctx.moveTo(a.sx, a.sy); ctx.lineTo(b.sx, b.sy); ctx.stroke();
  }
  ctx.setLineDash([]); ctx.globalAlpha = 1;
  const big = []; projected = [];
  const order = con.nodes.map(n => [n, pr.get(n.id)]).filter(x => x[1]).sort((p, q) => q[1].z - p[1].z);
  for (const [n, q] of order) {
    const r = Math.min(11, Math.max(2.5, n.r * q.f * 1.4));
    ctx.globalAlpha = depthAlpha(q.z);
    if (n.id === sel) { ctx.fillStyle = INK; ctx.globalAlpha = 0.22; ctx.beginPath(); ctx.arc(q.sx, q.sy, r * 2, 0, Math.PI * 2); ctx.fill(); ctx.globalAlpha = 1; }
    ctx.fillStyle = n.person ? '#dfe8ff' : color[n.dom] || color.X;
    ctx.beginPath(); ctx.arc(q.sx, q.sy, r, 0, Math.PI * 2); ctx.fill();
    if (n.person) { ctx.strokeStyle = '#9fb6ff'; ctx.lineWidth = 1; ctx.stroke(); }
    else { ctx.strokeStyle = '#05070c'; ctx.lineWidth = 1.2; ctx.stroke(); }
    projected.push({ s: n, sx: q.sx, sy: q.sy, r });
    big.push({ s: n, sx: q.sx, sy: q.sy, r: n.id === sel ? r + 10 : r });
  }
  ctx.globalAlpha = 1;
  labels(big.sort((p, q) => q.r - p.r).slice(0, con.nodes.length < 80 ? 80 : 45));
  if (hover) ring(hover);
}

function setGravity(g) {
  if (g === gravity || !stars.length || (!PICTURES.has(g) && !stars[0].pos[g])) return;
  const wasFlows = picture();
  document.querySelectorAll('[data-gravity]').forEach(b => b.classList.toggle('off', b.dataset.gravity !== g));
  document.body.classList.toggle('flows', g === 'flows');
  document.body.classList.toggle('loops', g === 'loops');
  if (g === 'flows') { gravity = g; flowHover = null; loopHover = null; hover = null; tip.hidden = true; dirty = true; const lb = document.getElementById('flows-note'); if (lb) lb.hidden = true; loadFlows(); return; }
  if (g === 'loops') { gravity = g; flowHover = null; loopHover = null; hover = null; tip.hidden = true; dirty = true; loadLoops(); return; }
  for (const s of stars) { s.fx = s.x; s.fy = s.y; s.fz = s.z; }     // glide from wherever each star is now
  gravity = g; glide = wasFlows ? 1 : 0; glideStart = performance.now(); dirty = true;
  if (wasFlows) for (const s of stars) { const p = s.pos[g]; s.x = p[0]; s.y = p[1]; s.z = p[2]; }
  const note = document.getElementById('gravity-note');
  if (note) note.textContent = g === 'influence' ? 'Influence is a model: ' + influenceNote + '.' : 'Connections is a count: how many filed records touch an entity.';
  const box = document.getElementById('flows-note'); if (box) box.hidden = true;
  canvas.style.cursor = '';
  if (mode === 'sky') { if (wasFlows) { fitAll(); status.textContent = skyStatus; } else fitAllSoon(); }
}
let fitTimer = 0;
function fitAllSoon() { clearTimeout(fitTimer); fitTimer = setTimeout(() => { if (mode === 'sky') fitAll(); }, 1450); }
function slide() {                                             // 0 = where the stars were, 1 = the chosen gravity's positions
  if (glide >= 1 || picture()) return false;
  const t = Math.min(1, (performance.now() - glideStart) / 1400), e = t < 0.5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2;
  glide = t >= 1 ? 1 : e;
  for (const s of stars) { const p = s.pos[gravity]; s.x = s.fx + (p[0] - s.fx) * glide; s.y = s.fy + (p[1] - s.fy) * glide; s.z = s.fz + (p[2] - s.fz) * glide; }
  return true;
}

function frame() {
  if (mode === 'sky' && slide()) dirty = true;
  if (mode === 'constellation' && alpha > 0.01) { for (let i = 0; i < 3; i++) step(); alpha *= 0.97; dirty = true; }
  if (spin) { cam.yaw += 0.002; dirty = true; }
  if (dirty) { const { W, H } = size(); (mode === 'sky' ? (gravity === 'flows' ? drawFlows : gravity === 'loops' ? drawLoops : drawSky) : drawConstellation)(W, H); dirty = false; }
  requestAnimationFrame(frame);
}

// ------------------------------------------------------------ constellation layout (small, local, 3D)
function step() {
  const ns = con.nodes;
  for (const n of ns) { n.vx = n.vy = n.vz = 0; }
  for (let i = 0; i < ns.length; i++) for (let j = i + 1; j < ns.length; j++) {
    const a = ns[i], b = ns[j]; let dx = b.x - a.x, dy = b.y - a.y, dz = b.z - a.z; const d2 = dx * dx + dy * dy + dz * dz + 0.5;
    if (d2 > 160000) continue;
    const d = Math.sqrt(d2), f = 900 / d2; dx /= d; dy /= d; dz /= d;
    a.vx -= dx * f; a.vy -= dy * f; a.vz -= dz * f; b.vx += dx * f; b.vy += dy * f; b.vz += dz * f;
  }
  for (const e of con.edges) {
    const a = con.byId.get(e.s), b = con.byId.get(e.t); if (!a || !b) continue;
    const dx = b.x - a.x, dy = b.y - a.y, dz = b.z - a.z, d = Math.hypot(dx, dy, dz) + 0.01, f = (d - (a.person || b.person ? 55 : 90)) * 0.03;
    a.vx += dx / d * f; a.vy += dy / d * f; a.vz += dz / d * f; b.vx -= dx / d * f; b.vy -= dy / d * f; b.vz -= dz / d * f;
  }
  for (const n of ns) {
    if (n.id === con.center) { n.x = n.y = n.z = 0; continue; }     // the chosen star holds the center
    n.vx -= n.x * 0.004; n.vy -= n.y * 0.004; n.vz -= n.z * 0.004;
    const v = Math.hypot(n.vx, n.vy, n.vz); if (v > 30) { n.vx *= 30 / v; n.vy *= 30 / v; n.vz *= 30 / v; }
    n.x += n.vx * alpha; n.y += n.vy * alpha; n.z += n.vz * alpha;
  }
}

async function openConstellation(id, hops = 1) {
  const c = STATIC ? await staticConstellation(id, hops) : await fetch(`/api/constellation/${encodeURIComponent(id)}?hops=${hops}`).then(r => r.ok ? r.json() : null);
  if (!c) return;
  con = c; con.byId = new Map();
  c.nodes.forEach((n, i) => {
    n.r = n.person ? 2 : 2.4 + Math.log2(n.deg + 1) * 1.2;
    const yy = 1 - (i + 0.5) / c.nodes.length * 2, rr = Math.sqrt(1 - yy * yy), t = i * 2.39996, rad = n.id === c.center ? 0 : 60 + Math.cbrt(i) * 40;
    n.x = Math.cos(t) * rr * rad; n.y = yy * rad; n.z = Math.sin(t) * rr * rad; n.vx = n.vy = n.vz = 0;
    con.byId.set(n.id, n);
  });
  mode = 'constellation'; alpha = 1; hover = null;
  document.getElementById('nav-sky').textContent = '← Back to the sky';
  renderPanel(c, hops);
  cam.tx = cam.ty = cam.tz = 0; cam.dist = 420 + Math.sqrt(c.nodes.length) * 40; cam.panX = -(panel.classList.contains('open') ? 190 : 0); cam.panY = 0;
  dirty = true;
  location.hash = id;
}
function backToSky() {
  mode = 'sky'; con = null; hover = null;
  document.getElementById('nav-sky').textContent = 'Sky';
  panel.classList.remove('open');
  history.replaceState(null, '', location.pathname);
  if (gravity === 'flows') { dirty = true; flowsStatus(); flowsNote(); } else if (gravity === 'loops') { dirty = true; loopsStatus(); loopsNote(); } else fitAll();
}

// ------------------------------------------------------------ panel
const esc = s => String(s ?? '').replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' })[c]);
function renderPanel(c, hops) {
  const me = c.byId.get(c.center);
  const mine = c.edges.filter(e => e.s === c.center || e.t === c.center).sort((a, b) => (b.active - a.active) || (b.date || '').localeCompare(a.date || ''));
  const counts = { confirmed: 0, 'one source': 0, 'not checked yet': 0, alert: 0 };
  for (const e of mine) counts[e.proof] = (counts[e.proof] || 0) + 1;
  const ids = Object.entries(me.identity).filter(([k]) => k !== 'jurisdiction').map(([k, v]) => `${k}: ${esc(v)}`).join(' · ');
  document.getElementById('panel-body').innerHTML = `
    <p class="kicker">${esc((me.type || 'entity').replace(/_/g, ' ').toLowerCase())} · domain ${me.doms.join(', ') || '—'}</p>
    <h2>${esc(me.label)}</h2>
    <div class="meta"><span>${ids || 'no identifier'}</span>${me.place ? `<span>${esc(me.place.state ? me.place.state + ', ' : '')}${esc(me.place.country || '')}</span>` : ''}</div>
    <div class="meta">
      <span class="pill v">${counts.confirmed} confirmed</span><span class="pill o">${counts['one source']} checked once</span>
      <span class="pill">${counts['not checked yet']} not checked yet</span>${counts.alert ? `<span class="pill a">${counts.alert} source changed</span>` : ''}
    </div>
    <div class="btns">
      <button class="btn primary" id="hops" type="button">${hops === 1 ? 'Widen to 2 hops' : 'Narrow to 1 hop'}</button>
      ${PUBLIC_PAGE ? `<button class="btn" id="report" type="button" title="A read-only report built here, in your browser, from the filed records on this page: every connection with its filing, what is checked and what is not, the right of reply, a fingerprint. Printable.">Report on this entity</button>`
        : `<button class="btn" id="draft" type="button" title="Draft a report from the filings on the map: findings, limits, right of reply, fingerprint. A draft; nothing is published.">Draft a report</button>
      <a class="btn" href="/#${encodeURIComponent(c.center)}" title="Open in the working viewer">Workbench</a>`}
    </div>
    <p class="kicker" style="color:var(--ink-soft)">${mine.length} filed connection${mine.length === 1 ? '' : 's'}</p>
    ${mine.slice(0, 200).map(e => {
      const other = e.s === c.center ? c.byId.get(e.t) : c.byId.get(e.s);
      const dir = e.s === c.center ? '→' : '←';
      return `<div class="conn${e.active ? '' : ' ended'}">
        <div class="who"><span class="mono" style="color:var(--ink-soft);font-size:.7rem">${dir} ${esc(e.type.replace(/_/g, ' ').toLowerCase())}</span>
          <button type="button" data-go="${esc(other?.id || '')}">${esc(other?.label || '?')}</button>${e.active ? '' : ' <span class="pill">ended</span>'}</div>
        ${e.role ? `<div class="how">${esc(e.role.length > 160 ? e.role.slice(0, 158) + '…' : e.role)}</div>` : ''}
        <div class="src"><span class="pill ${e.proof === 'confirmed' ? 'v' : e.proof === 'one source' ? 'o' : e.proof === 'alert' ? 'a' : ''}">${esc(e.proof)}</span>
          ${esc(e.source)}${e.date ? ' · ' + esc(e.date) : ''}${e.url ? ` · <a href="${esc(e.url)}" target="_blank" rel="noopener">filing</a>` : ''}</div>
      </div>`; }).join('')}
    ${mine.length > 200 ? `<p class="note">${mine.length - 200} more connections not listed here.</p>` : ''}
    <p class="note">Each line is a filed record; "confirmed" means a second, independent official source agrees. Connected is not the same as culpable.</p>`;
  panel.classList.add('open');
  panel.querySelectorAll('[data-go]').forEach(b => b.addEventListener('click', () => openConstellation(b.dataset.go)));
  document.getElementById('hops').addEventListener('click', () => openConstellation(c.center, hops === 1 ? 2 : 1));
  const draftBtn = document.getElementById('draft'); if (draftBtn) draftBtn.addEventListener('click', ev => draftReport(c.center, ev.currentTarget));
  const reportBtn = document.getElementById('report'); if (reportBtn) reportBtn.addEventListener('click', () => entityReport(c));
}

// ------------------------------------------------------------ interaction
function pick(sx, sy) {
  let best = null, bd = 10;
  for (let i = projected.length - 1; i >= 0; i--) {
    const o = projected[i];
    if (dimmed.size && mode === 'sky' && dimmed.has(o.s.dom)) continue;
    const d = Math.hypot(o.sx - sx, o.sy - sy) - o.r;
    if (d < bd) { best = o; bd = d; }
  }
  return best;
}
let drag = null;
canvas.addEventListener('contextmenu', e => e.preventDefault());
canvas.addEventListener('pointerdown', e => { drag = { x: e.clientX, y: e.clientY, moved: false, pan: e.button === 2 || e.shiftKey }; canvas.setPointerCapture(e.pointerId); canvas.classList.add('grabbing'); });
canvas.addEventListener('pointermove', e => {
  if (mode === 'sky' && gravity === 'flows') { drag = null; flowsHover(e); return; }
  if (mode === 'sky' && gravity === 'loops') { drag = null; loopsHover(e); return; }
  if (drag) {
    const dx = e.clientX - drag.x, dy = e.clientY - drag.y;
    if (Math.abs(dx) + Math.abs(dy) > 3) drag.moved = true;
    if (drag.pan) { cam.panX += dx; cam.panY += dy; }
    else { cam.yaw += dx * 0.006; cam.pitch = Math.max(-1.55, Math.min(1.55, cam.pitch + dy * 0.006)); }
    drag.x = e.clientX; drag.y = e.clientY; dirty = true; return;
  }
  const h = pick(e.clientX, e.clientY);
  if (h?.s !== hover?.s) { hover = h; dirty = true; }
  if (h) {
    const s = h.s;
    tip.innerHTML = `<b>${esc(s.label)}</b><div class="sub">${s.person ? 'person' : 'domain ' + s.dom}${s.sub && subNames[s.dom + '.' + s.sub] ? ' · ' + esc(subNames[s.dom + '.' + s.sub]) : ''}${s.others ? ' · also in ' + s.others.split('').join(', ') : ''} · ${s.deg} connection${s.deg === 1 ? '' : 's'}${mode === 'sky' ? ' · ' + (['not checked yet', 'checked once', 'confirmed by a second source', 'source changed'][s.proof] || 'no connections') + (s.infl != null ? ` · influence ${Math.round(s.infl * 100)}` : '') + (s.dmn != null ? ` · dominion ${Math.round(s.dmn * 100)}` : '') : ''}</div>`;
    tip.style.left = `${e.clientX + 14}px`; tip.style.top = `${e.clientY + 12}px`; tip.hidden = false;
  } else tip.hidden = true;
});
canvas.addEventListener('pointerup', e => {
  if (mode === 'sky' && gravity === 'flows') { const b = flowAt(e.clientX, e.clientY); if (b) { tip.hidden = true; openBand(b); } }
  else if (mode === 'sky' && gravity === 'loops') { const l = loopAt(e.clientX, e.clientY); if (l) { tip.hidden = true; openLoop(l); } }
  else if (drag && !drag.moved && !drag.pan) {
    const box = mode === 'sky' && labelBoxes.find(b => e.clientX >= b.x && e.clientX <= b.x + b.w && e.clientY >= b.y && e.clientY <= b.y + b.h);
    if (box) flyTo(box.m);                                           // a click on a galaxy's name flies to it
    else { const h = pick(e.clientX, e.clientY); if (h) openConstellation(h.s.id); }
  }
  drag = null; canvas.classList.remove('grabbing');
  if (canvas.hasPointerCapture(e.pointerId)) canvas.releasePointerCapture(e.pointerId);
});
canvas.addEventListener('wheel', e => { e.preventDefault(); if (mode === 'sky' && picture()) return; zoom(Math.exp(-e.deltaY * 0.0012), e.clientX, e.clientY); }, { passive: false });
window.addEventListener('resize', () => { dirty = true; });
window.addEventListener('keydown', e => { if (e.key === ' ' && e.target === document.body) { spin = !spin; e.preventDefault(); } if (e.key === 'Escape' && mode === 'constellation') backToSky(); });

// search
const q = document.getElementById('q'), hits = document.getElementById('hits');
q.addEventListener('input', () => {
  const t = q.value.trim().toLowerCase();
  if (t.length < 2) { hits.hidden = true; return; }
  const words = t.split(/\s+/);
  const list = [];
  for (const { s, t: name } of names) { if (words.every(w => name.includes(w))) { list.push(s); if (list.length >= 60) break; } }
  list.sort((a, b) => b.deg - a.deg);
  hits.innerHTML = list.slice(0, 25).map(s => `<button class="hit" type="button" data-id="${esc(s.id)}"><span class="d" style="background:${s.person ? '#dfe8ff' : color[s.dom]}"></span>${esc(s.label)}<span class="sub">${s.person ? 'person' : s.dom} · ${s.deg}</span></button>`).join('')
    || '<div class="hit">no match</div>';
  hits.hidden = false;
});
hits.addEventListener('click', ev => { const b = ev.target.closest('[data-id]'); if (!b) return; hits.hidden = true; q.value = ''; openConstellation(b.dataset.id); });
document.addEventListener('click', ev => { if (!ev.target.closest('.search')) hits.hidden = true; });

// the reading pages (how to read it, method, corrections) sit over the sky; one at a time
const PAGES = { 'nav-about': 'about', 'nav-method': 'method', 'nav-balance': 'balance-page', 'nav-corrections': 'corrections', 'nav-reports': 'reports' };
function showPage(id) {
  for (const [nav, sec] of Object.entries(PAGES)) {
    const on = sec === id;
    document.getElementById(sec).hidden = !on;
    document.getElementById(nav).classList.toggle('on', on);
  }
  document.getElementById('nav-sky').classList.toggle('on', !id);
  if (id === 'reports') loadReports();
  if (id === 'balance-page') loadBalance();
}

// Reports: the drafts on file, with their review state; a new draft can be asked for from an entity's card.
async function loadReports() {
  const box = document.getElementById('report-list');
  const { reports } = await fetch('/api/reports').then(r => r.json()).catch(() => ({ reports: [] }));
  if (!reports.length) { box.innerHTML = '<p class="mono" style="font-size:.78rem">No reports drafted yet. Open an entity and choose "Draft a report".</p>'; return; }
  box.innerHTML = reports.map(r => `
    <div class="rcard">
      <h3>${esc(r.label || r.subject)}</h3>
      <div class="m"><span>${esc(r.id)}</span><span>drafted ${esc((r.drafted_at || '').slice(0, 10))}</span><span>${r.sources} sources</span><span>${r.named} organization${r.named === 1 ? '' : 's'} to contact</span>
        ${r.folder === 'auto' ? '<span class="pill">auto-draft</span>' : ''}
        <span class="pill ${/verified|ready/i.test(r.verdict || '') ? 'v' : /hold|fail|block|not/i.test(r.verdict || '') ? 'c' : ''}">${esc(r.verdict ? String(r.verdict).split(':')[0] : r.review === 'done' ? 'reviewed' : r.review || 'unreviewed')}</span></div>
      ${r.verdict ? `<div style="font-size:.84rem;color:var(--ink-soft)">${esc(String(r.verdict).slice(0, 220))}</div>` : ''}
      <div class="links"><a href="${esc(r.html)}" target="_blank" rel="noopener">Read the draft</a>${r.reviewed_html ? `<a href="${esc(r.reviewed_html)}" target="_blank" rel="noopener">Reviewed copy</a>` : ''}
        <button type="button" data-go="${esc(r.subject || '')}">Constellation</button></div>
    </div>`).join('');
  box.querySelectorAll('[data-go]').forEach(b => b.addEventListener('click', () => { showPage(null); if (b.dataset.go) openConstellation(b.dataset.go); }));
}
async function draftReport(subject, btn) {
  btn.disabled = true; btn.textContent = 'Drafting…';
  try {
    const res = await fetch('/api/report', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ subject }) });
    const d = await res.json();
    if (!res.ok) throw new Error(d.error || 'could not draft');
    btn.textContent = 'Drafted: open';
    btn.disabled = false;
    btn.onclick = () => window.open(d.html_url, '_blank', 'noopener');
  } catch (e) { btn.textContent = 'Draft failed: ' + e.message; }
}
for (const [nav, sec] of Object.entries(PAGES)) {
  document.getElementById(nav).addEventListener('click', () => showPage(document.getElementById(sec).hidden ? sec : null));
}
document.getElementById('nav-sky').addEventListener('click', () => { showPage(null); if (mode === 'constellation') backToSky(); });
document.getElementById('close').addEventListener('click', () => panel.classList.remove('open'));
document.querySelectorAll('[data-gravity]').forEach(b => b.addEventListener('click', () => setGravity(b.dataset.gravity)));

document.querySelectorAll('[data-kind]').forEach(b => b.addEventListener('click', () => {
  flowKind = b.dataset.kind; flowHover = null; tip.hidden = true;
  document.querySelectorAll('[data-kind]').forEach(c => c.classList.toggle('off', c.dataset.kind !== flowKind));
  dirty = true; flowsStatus(); flowsNote();
}));

document.querySelectorAll('[data-loops]').forEach(b => b.addEventListener('click', () => {
  loopShow = b.dataset.loops; loopHover = null; tip.hidden = true;
  document.querySelectorAll('[data-loops]').forEach(c => c.classList.toggle('off', c.dataset.loops !== loopShow));
  dirty = true; loopsStatus(); loopsNote();
}));

load().then(() => { requestAnimationFrame(frame); if (location.hash.length > 1) openConstellation(decodeURIComponent(location.hash.slice(1))); });


// ------------------------------------------------------------ flows: the groups around a circle, the bands between them
// Josie, 2026-10-22: individuals and companies never mattered, the money and the connections do. So this picture has no
// stars. The ten groups (domains) sit around a circle; a band is money or a person moving from one group to another,
// drawn from the filed records already on the map (/api/flows aggregates them once per map version). Its thickness is
// how much: dollars where the filings state them (one money kind chosen), the number of records otherwise. Click a band
// and it unrolls into its records, newest first, each with its citation.
const SHORT = { A: 'Defense', B: 'Retail & Food', C: 'Finance', D: 'Tech', E: 'Life Sciences', F: 'Energy', G: 'Media', H: 'Education', I: 'Government', J: 'Legal' };
const NOUN = { contributions: 'contributions', lobbying: 'lobbying records', contracts: 'contracts', grants: 'grants', seats: 'seats and roles', moves: 'revolving-door moves' };
const MONEY = new Set(['contributions', 'contracts', 'grants']);
let flows = null, flowKind = 'all', flowHover = null, flowShapes = [], flowsLoading = false;
const money = v => v == null ? 'amount not filed' : v >= 1e9 ? `$${(v / 1e9).toFixed(1)}B` : v >= 1e6 ? `$${(v / 1e6).toFixed(1)}M` : v >= 1e3 ? `$${Math.round(v / 1e3)}K` : `$${Math.round(v)}`;
const years = b => b.first ? (b.first.slice(0, 4) === b.last.slice(0, 4) ? b.first.slice(0, 4) : `${b.first.slice(0, 4)}-${b.last.slice(0, 4)}`) : 'undated';
const pct = b => b.count ? Math.round(100 * b.confirmed / b.count) : 0;

async function loadFlows() {
  if (flows || flowsLoading) { flowsStatus(); flowsNote(); return; }
  flowsLoading = true; status.textContent = 'reading the flows…';
  try { flows = await fetch(STATIC ? 'data/flows.json' : '/api/flows').then(r => r.json()); } catch (e) { status.textContent = 'the flows could not be read: ' + e.message; flowsLoading = false; return; }
  flowsLoading = false; dirty = true; flowsStatus(); flowsNote();
}
function bandsShown() {
  if (!flows) return [];
  return flows.bands.filter(b => b.from !== b.to && SHORT[b.from] && SHORT[b.to] && (flowKind === 'all' || b.kind === flowKind)
    && !(dimmed.size && (dimmed.has(b.from) || dimmed.has(b.to))));
}
const byAmount = () => flowKind !== 'all' && MONEY.has(flowKind);
function flowsStatus() {
  if (!flows || mode !== 'sky' || gravity !== 'flows') return;
  const bs = bandsShown(), n = bs.reduce((a, b) => a + b.count, 0), amt = bs.reduce((a, b) => a + (b.amount || 0), 0);
  const w = document.getElementById('flows-width');
  if (w) w.textContent = byAmount() ? `width: dollars the filings state (${NOUN[flowKind]})` : 'width: number of filed records';
  status.textContent = `${bs.length} bands · ${n.toLocaleString()} filed records` + (byAmount() ? ` · ${money(amt)} stated` : '')
    + ` · generated ${(flows.generated || '').slice(0, 10)} · hover a band to read it, click to unroll it`;
}
// Short facts: which groups no band reaches, where bands run, what stays inside one group.
function flowsNote() {
  const box = document.getElementById('flows-note'); if (!box || !flows) return;
  const doms = Object.keys(SHORT), has = new Set();
  for (const b of flows.bands) if (b.from !== b.to && (flowKind === 'all' || b.kind === flowKind)) { has.add(b.from + b.to); has.add(b.to + b.from); }
  const what = flowKind === 'all' ? 'band' : NOUN[flowKind];
  const lonely = doms.filter(d => doms.every(o => o === d || !has.has(d + o)));
  const pairs = [], run = [];
  for (const d of doms) for (const o of doms) {
    if (d >= o || lonely.includes(d) || lonely.includes(o)) continue;
    (has.has(d + o) ? run : pairs).push(`${SHORT[d]}–${SHORT[o]}`);
  }
  let text = '';
  if (lonely.length) text += `No ${what === 'band' ? 'band' : 'band of ' + what} reaches ${lonely.map(d => SHORT[d]).join(', ')}. `;
  if (pairs.length > 8) text += `Runs only: ${run.join('; ')}. `;
  else if (pairs.length) text += `Missing between: ${pairs.join('; ')}. `;
  else text += `Every group has a ${what} to every other. `;
  const inside = Object.entries(flows.within || {}).map(([d, ks]) => {
    const n = Object.entries(ks).filter(([k]) => flowKind === 'all' || k === flowKind).reduce((a, [, v]) => a + v, 0);
    return n ? `${n.toLocaleString()} ${SHORT[d] || d}` : '';
  }).filter(Boolean);
  if (inside.length) text += `Inside one group, not drawn: ${inside.join(', ')}.`;
  box.textContent = text.trim();
  box.hidden = !(mode === 'sky' && gravity === 'flows');
  const legendEl = document.getElementById('legend');
  if (!box.hidden && legendEl) box.style.top = `${Math.max(70, legendEl.getBoundingClientRect().top - box.offsetHeight - 14)}px`;   // bottom-left corner, clear of the bar
}

function drawFlows(W, H) {
  ctx.fillStyle = PAPER; ctx.fillRect(0, 0, W, H);
  flowShapes = []; projected = [];
  if (!flows) { ctx.fillStyle = css('--ink-soft'); ctx.font = '13px "IBM Plex Mono", ui-monospace, monospace'; ctx.textAlign = 'center'; ctx.fillText('reading the flows…', W / 2, (H + 58) / 2); return; }
  const doms = Object.keys(SHORT).filter(d => !(dimmed.size && dimmed.has(d)));
  const bs = bandsShown(), amount = byAmount();
  const weight = b => amount ? (b.amount || 0) : b.count;
  const open = panel.classList.contains('open');
  const legendEl = document.getElementById('legend'), noteEl = document.getElementById('flows-note');
  const floor = legendEl ? Math.min(H, legendEl.getBoundingClientRect().top) : H;      // the legend bar must not cover a group's name
  const cx = (W - (open ? Math.min(416, W * 0.92) : 0)) / 2;
  const size = fl => Math.max(80, Math.min(W - (open ? Math.min(416, W * 0.92) : 0), fl - 58 - 100) / 2 - 92);
  let fl = floor, R = size(fl), cy = (fl + 58) / 2 + 6;
  if (noteEl && !noteEl.hidden) {                                                       // the note sits bottom-left; if it would touch the circle, the circle sits above it
    const nb = noteEl.getBoundingClientRect();
    const dx = Math.max(0, (cx - R - 110) - nb.right), dy = Math.max(0, nb.top - (cy + R + 40));
    if (dx === 0 && dy === 0) { fl = Math.min(floor, nb.top); R = size(fl); cy = (fl + 58) / 2 + 6; }
  }
  const total = {}; for (const d of doms) total[d] = 0;
  for (const b of bs) { total[b.from] += weight(b); total[b.to] += weight(b); }
  const sum = Object.values(total).reduce((a, v) => a + v, 0) || 1;
  const gap = 0.035, room = Math.PI * 2 - gap * doms.length, minArc = 0.17;   // a group with little keeps room for its name
  const arcs = {}, raw = doms.map(d => Math.max(minArc, room * total[d] / sum)), rs = raw.reduce((a, v) => a + v, 0) || 1;
  let a0 = -Math.PI / 2;                                               // clockwise from the top, A..J
  doms.forEach((d, i) => { const span = raw[i] * room / rs; arcs[d] = { a0, a1: a0 + span }; a0 += span + gap; });
  // each band takes a slice of both of its ends, ordered by where the partner sits on the circle (fewer crossings)
  const ends = {}; for (const d of doms) ends[d] = [];
  for (const b of bs) { ends[b.from].push({ b, side: 'from', partner: b.to }); ends[b.to].push({ b, side: 'to', partner: b.from }); }
  const mid = d => (arcs[d].a0 + arcs[d].a1) / 2, turn = (d, o) => (mid(o) - mid(d) + Math.PI * 3) % (Math.PI * 2);
  const slice = {};
  for (const d of doms) {
    const list = ends[d].sort((p, q) => turn(d, q.partner) - turn(d, p.partner));
    const span = arcs[d].a1 - arcs[d].a0, t = total[d] || 1, minW = Math.min(0.012, span / Math.max(1, list.length) * 0.5);
    const ws = list.map(x => Math.max(minW, span * weight(x.b) / t)), k = span / (ws.reduce((a, v) => a + v, 0) || 1);
    let a = arcs[d].a0;
    list.forEach((x, i) => { const w = ws[i] * k; slice[x.b.from + x.b.to + x.b.kind + x.side] = [a, a + w]; a += w; });
  }
  const P = (ang, r = R) => [cx + Math.cos(ang) * r, cy + Math.sin(ang) * r];
  const hov = flowHover, r = R - 9;
  for (const b of bs.slice().sort((p, q) => weight(q) - weight(p))) {      // big bands under small ones
    const [s0, s1] = slice[b.from + b.to + b.kind + 'from'], [t0, t1] = slice[b.from + b.to + b.kind + 'to'];
    const path = new Path2D();
    path.arc(cx, cy, r, s0, s1);
    const [tx0, ty0] = P(t0, r); path.quadraticCurveTo(cx, cy, tx0, ty0);
    path.arc(cx, cy, r, t0, t1);
    const [sx0, sy0] = P(s0, r); path.quadraticCurveTo(cx, cy, sx0, sy0);
    path.closePath();
    const on = hov === b, other = hov && !on;
    ctx.globalAlpha = on ? 0.85 : other ? 0.08 : 0.42;
    ctx.fillStyle = color[b.from]; ctx.fill(path);
    ctx.globalAlpha = on ? 1 : other ? 0.1 : 0.55; ctx.lineWidth = on ? 1.4 : 0.6; ctx.strokeStyle = color[b.from]; ctx.stroke(path);
    // the arrival end carries the receiving group's color as a thin cap, so the eye can tell which way the band runs
    ctx.globalAlpha = on ? 1 : other ? 0.15 : 0.9; ctx.lineWidth = 5; ctx.strokeStyle = color[b.to];
    ctx.beginPath(); ctx.arc(cx, cy, r - 3, t0, t1); ctx.stroke();
    flowShapes.push({ b, path });
  }
  ctx.globalAlpha = 1;
  let lastM = -9, level = 0;
  for (const d of doms) {                                               // the groups: an arc each, its name outside
    const { a0, a1 } = arcs[d];
    ctx.lineWidth = 14; ctx.strokeStyle = color[d]; ctx.globalAlpha = hov && hov.from !== d && hov.to !== d ? 0.35 : 1;
    ctx.beginPath(); ctx.arc(cx, cy, R, a0, a1); ctx.stroke();
    const m = (a0 + a1) / 2;
    level = m - lastM < 0.26 ? (level + 1) % 3 : 0; lastM = m;            // names of small neighbouring groups step outward so they stay apart
    const [lx, ly] = P(m, R + 22 + level * 30), right = Math.cos(m) > 0.05, left = Math.cos(m) < -0.05;
    if (level) { ctx.globalAlpha = 0.5; ctx.lineWidth = 1; ctx.strokeStyle = color[d]; ctx.beginPath(); ctx.moveTo(...P(m, R + 9)); ctx.lineTo(...P(m, R + 12 + level * 30)); ctx.stroke(); ctx.globalAlpha = 1; }
    ctx.textAlign = right ? 'left' : left ? 'right' : 'center'; ctx.textBaseline = 'middle';
    ctx.font = `600 ${Math.max(12, Math.min(18, R / 22))}px "Fraunces", Georgia, serif`;
    ctx.lineWidth = 4; ctx.strokeStyle = PAPER; ctx.strokeText(SHORT[d], lx, ly - 8); ctx.fillStyle = color[d]; ctx.fillText(SHORT[d], lx, ly - 8);
    const nIn = bs.filter(b => b.to === d).reduce((a, b) => a + b.count, 0), nOut = bs.filter(b => b.from === d).reduce((a, b) => a + b.count, 0);
    ctx.font = '10px "IBM Plex Mono", ui-monospace, monospace';
    const sub = `${d} · ${nOut.toLocaleString()} out · ${nIn.toLocaleString()} in`;
    ctx.strokeText(sub, lx, ly + 8); ctx.fillStyle = css('--ink-soft'); ctx.fillText(sub, lx, ly + 8);
  }
  ctx.globalAlpha = 1; ctx.textBaseline = 'alphabetic';
  if (!bs.length) { ctx.fillStyle = css('--ink-soft'); ctx.font = '13px "IBM Plex Mono", ui-monospace, monospace'; ctx.textAlign = 'center'; ctx.fillText('no band of this kind between the groups shown', cx, cy); }
}
function flowAt(x, y) {
  const dpr = window.devicePixelRatio || 1;
  for (let i = flowShapes.length - 1; i >= 0; i--) if (ctx.isPointInPath(flowShapes[i].path, x * dpr, y * dpr)) return flowShapes[i].b;
  return null;
}
function bandText(b) {
  const amt = b.amount == null ? 'amount not filed' : money(b.amount) + (b.amount_n < b.count ? ` stated in ${b.amount_n.toLocaleString()} of them` : '');
  return `${SHORT[b.from]} → ${SHORT[b.to]}: ${b.count.toLocaleString()} ${NOUN[b.kind]}, ${amt}, ${years(b)}, ${pct(b)}% with a second source`;
}
function flowsHover(e) {
  const b = flowAt(e.clientX, e.clientY);
  if (b !== flowHover) { flowHover = b; dirty = true; }
  canvas.style.cursor = b ? 'pointer' : 'default';
  if (b) {
    tip.innerHTML = `<b>${esc(bandText(b))}</b><div class="sub">${esc(flows.kinds[b.kind] || b.kind)} · click to unroll the records</div>`;
    tip.style.left = `${e.clientX + 14}px`; tip.style.top = `${e.clientY + 12}px`; tip.hidden = false;
  } else tip.hidden = true;
}
async function openBand(b, offset = 0, into = null) {
  const d = STATIC
    ? await fetch(`data/flows/${b.from}-${b.to}-${b.kind}.json`).then(r => r.ok ? r.json() : null).then(all => all && ({ records: all.slice(offset, offset + 200), total: all.length, offset }))
    : await fetch(`/api/flows/records?from=${b.from}&to=${b.to}&kind=${b.kind}&offset=${offset}`).then(r => r.ok ? r.json() : null);
  if (!d) return;
  const rows = d.records.map(r => `<div class="conn${r.active ? '' : ' ended'}">
      <div class="who"><button type="button" data-go="${esc(r.s)}">${esc(r.sl)}</button><span class="mono" style="color:var(--ink-soft);font-size:.7rem">→</span>
        <button type="button" data-go="${esc(r.t)}">${esc(r.tl)}</button>${r.amount != null ? ` <span class="pill">${esc(money(r.amount))}</span>` : ''}${r.active ? '' : ' <span class="pill">ended</span>'}</div>
      ${r.role ? `<div class="how">${esc(r.role.length > 160 ? r.role.slice(0, 158) + '…' : r.role)}</div>` : ''}
      <div class="src"><span class="pill ${r.proof === 'confirmed' ? 'v' : r.proof === 'one source' ? 'o' : r.proof === 'alert' ? 'a' : ''}">${esc(r.proof)}</span>
        ${esc(r.type.replace(/_/g, ' ').toLowerCase())} · ${esc(r.source)}${r.date ? ' · ' + esc(r.date) : ''}${r.url ? ` · <a href="${esc(r.url)}" target="_blank" rel="noopener">filing</a>` : ''}${STATIC ? '' : ` · <a href="/api/edge/${encodeURIComponent(r.id)}" target="_blank" rel="noopener" title="the full record on the map, as filed">record</a>`}</div>
    </div>`).join('');
  const left = d.total - d.offset - d.records.length;
  const more = left > 0 ? `<button class="btn" id="more" type="button">Show ${Math.min(200, left)} more of ${d.total.toLocaleString()}</button>` : '';
  if (into) into.outerHTML = rows + more;
  else {
    document.getElementById('panel-body').innerHTML = `
      <p class="kicker">a band · ${esc(flows.kinds[b.kind] || b.kind)}</p>
      <h2>${esc(SHORT[b.from])} → ${esc(SHORT[b.to])}</h2>
      <div class="meta"><span>${b.count.toLocaleString()} ${esc(NOUN[b.kind])}</span><span>${esc(b.amount == null ? 'amount not filed' : money(b.amount) + (b.amount_n < b.count ? ` stated in ${b.amount_n.toLocaleString()}` : ''))}</span><span>${esc(years(b))}</span></div>
      <div class="meta"><span class="pill v">${b.confirmed.toLocaleString()} confirmed by a second source</span><span class="pill">${(b.count - b.confirmed).toLocaleString()} one source or not checked yet</span></div>
      <p class="kicker" style="color:var(--ink-soft)">the filed records, newest first</p>
      ${rows}${more}
      <p class="note">Each line is a filed record already on the map, with its citation. The band's direction is where the money or the person goes. A lawful, disclosed fact each; connected is not the same as culpable.</p>`;
    panel.classList.add('open'); dirty = true;
  }
  panel.querySelectorAll('[data-go]').forEach(el => { if (!el.dataset.bound) { el.dataset.bound = '1'; el.addEventListener('click', () => openConstellation(el.dataset.go)); } });
  const m = document.getElementById('more'); if (m) m.addEventListener('click', () => { m.textContent = 'reading…'; openBand(b, d.offset + d.records.length, m); });
}


// ------------------------------------------------------------ loops: a company lobbied a bill, a member introduced it, the company's PAC gave
// Josie, 2026-10-23: the circle, by the records. Three filed records that never share a page: the company's lobbying
// filing (LDA) names a bill; the bill's own record (GovInfo) names its sponsor; the company's PAC (FEC Schedule B) gave
// to that member. /api/loops serves the dry-run join (src/maintenance/pac_sponsor_join.py). Companies left, bills in the
// middle, members right; the arc over the top is the gift, as wide as it was. Omnibus vehicles are kept apart.
let loops = null, loopShow = '40', loopHover = null, loopShapes = [], loopsLoading = false;
async function loadLoops() {
  if (loops || loopsLoading) { loopsStatus(); loopsNote(); return; }
  loopsLoading = true; status.textContent = 'reading the loops…';
  try { loops = await fetch(STATIC ? 'data/loops.json' : '/api/loops').then(r => { if (!r.ok) throw new Error(r.status === 404 ? 'the loops have not been built yet' : 'HTTP ' + r.status); return r.json(); }); }
  catch (e) { status.textContent = 'the loops could not be read: ' + e.message; loopsLoading = false; return; }
  loopsLoading = false; dirty = true; loopsStatus(); loopsNote();
}
function loopsShown() {
  if (!loops) return [];
  if (loopShow === 'omnibus') return loops.omnibus;
  const n = loopShow === 'all' ? Infinity : +loopShow;
  return loops.loops.slice(0, n);
}
function loopsStatus() {
  if (!loops || mode !== 'sky' || gravity !== 'loops') return;
  const ls = loopsShown(), amt = ls.reduce((a, l) => a + (l.gave_this_cycle || 0), 0);
  const cs = new Set(ls.map(l => l.company_id)).size, ms = new Set(ls.map(l => l.member_id)).size;
  status.textContent = `${ls.length} loops · ${cs} companies · ${ms} members · ${money(amt)} in PAC gifts, ${loops.cycle} cycle` + (loopShow === 'omnibus' ? ' · through omnibus bills, kept apart' : '')
    + ` · generated ${(loops.generated || '')} · hover a loop to read it, click for its three records`;
}
function loopsNote() {
  const box = document.getElementById('flows-note'); if (!box || !loops) return;
  const s = loops.summary || {}, c = loops.cycles || {};
  const n = v => (v || 0).toLocaleString();
  box.textContent = `One loop: a company lobbied a bill; a member introduced it; the company's PAC paid that member. `
    + `${n(s.pairs_lobbied)} company–member pairs. ${n(s.pairs_with_gift_this_cycle)} with a PAC gift this cycle (${s.pairs_lobbied ? Math.round(100 * s.pairs_with_gift_this_cycle / s.pairs_lobbied) : 0}%). `
    + `${n(s.loops)} loops outside omnibus bills: ${money(s.loop_money || 0)}. ${n(s.loops_omnibus)} through omnibus bills, kept apart. `
    + (c.comparable ? `${n(c.new_relationship)} of ${n(c.comparable)} pairs: first gift this cycle. ` : '')
    + (s.lobbying_spend_all ? `What the same companies paid to lobby Congress, two years, by their own filings: ${money(s.lobbying_spend_all)}. The ${n(s.loop_companies)} companies drawn here alone: ${money(s.lobbying_spend_loop_companies)}. Their PAC gifts in these loops: ${money(s.loop_money || 0)}. ` : '')
    + 'All filed. All lawful.';
  box.hidden = !(mode === 'sky' && gravity === 'loops');
  box.style.top = '';                                                                   // loops keep the note at the top; the drawing starts under it
}
function drawLoops(W, H) {
  ctx.fillStyle = PAPER; ctx.fillRect(0, 0, W, H);
  loopShapes = []; projected = [];
  if (!loops) { ctx.fillStyle = css('--ink-soft'); ctx.font = '13px "IBM Plex Mono", ui-monospace, monospace'; ctx.textAlign = 'center'; ctx.fillText('reading the loops…', W / 2, (H + 58) / 2); return; }
  const ls = loopsShown();
  const open = panel.classList.contains('open'), PW = open ? Math.min(416, W * 0.92) : 0;
  const noteEl = document.getElementById('flows-note'), legendEl = document.getElementById('legend');
  const noteB = noteEl && !noteEl.hidden ? noteEl.getBoundingClientRect().bottom : 0;
  const legendT = legendEl ? legendEl.getBoundingClientRect().top : H - 70;
  const left = 24, right = W - PW - 24, top = Math.max(150, noteB + 44), bottom = Math.min(H - 70, legendT - 18);
  if (!ls.length) { ctx.fillStyle = css('--ink-soft'); ctx.font = '13px "IBM Plex Mono", ui-monospace, monospace'; ctx.textAlign = 'center'; ctx.fillText('no loops to draw', (left + right) / 2, (top + bottom) / 2); return; }
  // order: members by gift total (largest at top), bills under their member, companies by their first bill
  const mTot = {}; for (const l of ls) mTot[l.member_id] = (mTot[l.member_id] || 0) + (l.gave_this_cycle || 0);
  const members = [...new Set(ls.map(l => l.member_id))].sort((a, b) => mTot[b] - mTot[a]);
  const mPos = Object.fromEntries(members.map((m, i) => [m, i]));
  const bills = [...new Set(ls.map(l => l.bill))].sort((a, b) => { const la = ls.find(l => l.bill === a), lb = ls.find(l => l.bill === b); return mPos[la.member_id] - mPos[lb.member_id]; });
  const bPos = Object.fromEntries(bills.map((b, i) => [b, i]));
  const cFirst = {}; for (const l of ls) cFirst[l.company_id] = Math.min(cFirst[l.company_id] ?? 1e9, bPos[l.bill]);
  const companies = [...new Set(ls.map(l => l.company_id))].sort((a, b) => cFirst[a] - cFirst[b]);
  const cPos = Object.fromEntries(companies.map((c, i) => [c, i]));
  const span = right - left, xC = left + span * 0.2, xB = left + span * 0.5, xM = left + span * 0.8;
  const Y = (i, n) => n <= 1 ? (top + bottom) / 2 : top + (bottom - top) * i / (n - 1);
  const yC = Object.fromEntries(companies.map((c, i) => [c, Y(i, companies.length)]));
  const yB = Object.fromEntries(bills.map((b, i) => [b, Y(i, bills.length)]));
  const yM = Object.fromEntries(members.map((m, i) => [m, Y(i, members.length)]));
  const label = { }; for (const l of ls) { label[l.company_id] = l.company; label[l.member_id] = l.member; label[l.bill] = l; }
  const maxGift = Math.max(1, ...ls.map(l => l.gave_this_cycle || 0));
  const hov = loopHover, gold = '#d9a441', ink = css('--ink'), soft = css('--ink-soft');
  const lineW = l => 1.2 + 5 * (l.gave_this_cycle || 0) / maxGift;
  for (const l of ls.slice().sort((p, q) => (q.gave_this_cycle || 0) - (p.gave_this_cycle || 0))) {   // big under small
    const on = hov === l, other = hov && !on;
    const y0 = yC[l.company_id], y1 = yB[l.bill], y2 = yM[l.member_id];
    // the lobbying: company -> bill -> member, thin and dark
    const walk = new Path2D();
    walk.moveTo(xC + 4, y0); walk.bezierCurveTo((xC + xB) / 2, y0, (xC + xB) / 2, y1, xB - 4, y1);
    walk.moveTo(xB + 4, y1); walk.bezierCurveTo((xB + xM) / 2, y1, (xB + xM) / 2, y2, xM - 4, y2);
    ctx.globalAlpha = on ? 0.95 : other ? 0.05 : 0.28; ctx.lineWidth = on ? 1.8 : 1; ctx.strokeStyle = ink; ctx.stroke(walk);
    // the gift: company -> member, an arc over the top, colored, as wide as the money
    const lift = Math.min(top - 70, 40 + Math.abs(xM - xC) * 0.12 + Math.abs(y2 - y0) * 0.15);
    const gift = new Path2D();
    gift.moveTo(xC + 4, y0); gift.bezierCurveTo(xC + (xM - xC) * 0.3, Math.min(y0, y2) - lift, xM - (xM - xC) * 0.3, Math.min(y0, y2) - lift, xM - 4, y2);
    ctx.globalAlpha = on ? 0.95 : other ? 0.06 : 0.5; ctx.lineWidth = lineW(l) * (on ? 1.3 : 1); ctx.strokeStyle = gold; ctx.stroke(gift);
    loopShapes.push({ l, gift, walk, w: Math.max(8, lineW(l) + 4) });
  }
  ctx.globalAlpha = 1;
  const dot = (x, y, dim) => { ctx.beginPath(); ctx.arc(x, y, 3, 0, Math.PI * 2); ctx.fillStyle = dim ? soft : ink; ctx.fill(); };
  const dimOf = id => hov && hov.company_id !== id && hov.member_id !== id && hov.bill !== id;
  const fontPx = Math.max(9, Math.min(12, (bottom - top) / Math.max(companies.length, bills.length, members.length) * 0.8));
  ctx.font = `${fontPx}px "IBM Plex Mono", ui-monospace, monospace`; ctx.textBaseline = 'middle';
  ctx.lineWidth = 3; ctx.strokeStyle = PAPER;
  const put = (text, x, y, align, dim) => { ctx.textAlign = align; ctx.strokeText(text, x, y); ctx.fillStyle = dim ? soft : ink; ctx.fillText(text, x, y); };
  const clip = (t, n) => t.length > n ? t.slice(0, n - 1) + '…' : t;
  const nC = Math.max(10, Math.floor(span * 0.2 / (fontPx * 0.62)) - 2), nB = Math.max(10, Math.floor(span * 0.26 / (fontPx * 0.62)) - 2);
  for (const c of companies) { const d = dimOf(c); dot(xC, yC[c], d); put(clip(label[c], nC), xC - 8, yC[c], 'right', d); }
  for (const b of bills) { const d = dimOf(b), l = label[b]; dot(xB, yB[b], d); put(clip(`${b.split(':')[1]} ${l.title || ''}`, nB), xB, yB[b] - fontPx * 0.75, 'center', d); }
  for (const m of members) { const d = dimOf(m); dot(xM, yM[m], d); put(clip(`${label[m]}  ${money(mTot[m])}`, nC + 8), xM + 8, yM[m], 'left', d); }
  ctx.font = `600 13px "Fraunces", Georgia, serif`; ctx.textBaseline = 'alphabetic';
  put('companies that lobbied', xC, top - 28, 'center', false); put('the bills they named', xB, top - 28, 'center', false); put('the members who introduced them', xM, top - 28, 'center', false);
  ctx.font = '10px "IBM Plex Mono", ui-monospace, monospace';
  put('lobbying filing → bill → sponsor, in ink; the PAC gift, in color over the top', (left + right) / 2, top - 12, 'center', true);
}
function loopAt(x, y) {
  const dpr = window.devicePixelRatio || 1;
  for (let i = loopShapes.length - 1; i >= 0; i--) {
    const s = loopShapes[i]; ctx.lineWidth = s.w;
    if (ctx.isPointInStroke(s.gift, x * dpr, y * dpr) || ctx.isPointInStroke(s.walk, x * dpr, y * dpr)) return s.l;
  }
  return null;
}
function loopText(l) {
  const all = Object.entries(l.gave || {}).filter(([c]) => c).sort().map(([c, a]) => `${c}: ${money(a)}`).join(', ');
  return `${l.company} lobbied ${l.bill.split(':')[1]} (${l.title}); ${l.member} introduced it; ${l.company}'s PAC gave ${l.member} ${money(l.gave_this_cycle)} this cycle${all ? ` (on the map: ${all})` : ''}${l.omnibus ? ' · an omnibus vehicle, kept apart' : ''}`;
}
function loopsHover(e) {
  const l = loopAt(e.clientX, e.clientY);
  if (l !== loopHover) { loopHover = l; dirty = true; }
  canvas.style.cursor = l ? 'pointer' : 'default';
  if (l) {
    tip.innerHTML = `<b>${esc(loopText(l))}</b><div class="sub">three filed records · click to read them</div>`;
    tip.style.left = `${Math.min(e.clientX + 14, window.innerWidth - 380)}px`; tip.style.top = `${e.clientY + 12}px`; tip.hidden = false;
  } else tip.hidden = true;
}
function openLoop(l) {
  const bill = l.bill.split(':'), cg = bill[0], num = bill[1];
  const type = num.split(' ')[0], n = num.split(' ')[1];
  const chamber = type.startsWith('H') ? 'house' : 'senate', kind = (type === 'HR' || type === 'S') ? 'bill' : type.endsWith('JRES') ? 'joint-resolution' : type.endsWith('CONRES') ? 'concurrent-resolution' : 'resolution';
  const billUrl = `https://www.congress.gov/bill/${cg}th-congress/${chamber}-${kind}/${n}`;
  const filings = (l.filings || []).map(f => `<div class="conn"><div class="who"><span class="mono">${esc(f.posted || '')}</span> ${esc(l.company)} ← ${esc(f.registrant || 'in-house')}</div><div class="src">Lobbying Disclosure Act filing · <a href="${esc(f.url)}" target="_blank" rel="noopener">filing</a></div></div>`).join('');
  const cycles = Object.entries(l.gave || {}).filter(([c]) => c).sort().map(([c, a]) => `<span class="pill">${esc(c)}: ${esc(money(a))}</span>`).join(' ');
  document.getElementById('panel-body').innerHTML = `
    <p class="kicker">a loop · three filed records</p>
    <h2>${esc(l.company)} → ${esc(num)} → ${esc(l.member)}</h2>
    <div class="meta"><span>${esc(money(l.gave_this_cycle))} PAC gift this cycle</span>${l.omnibus ? '<span class="pill">omnibus vehicle, kept apart</span>' : ''}${l.public_law ? `<span class="pill">became Pub. L. ${esc(l.public_law)}</span>` : ''}</div>
    <p class="kicker" style="color:var(--ink-soft)">1 · the company lobbied the bill</p>
    ${filings || '<div class="conn"><div class="how">filing links not carried</div></div>'}
    <p class="kicker" style="color:var(--ink-soft)">2 · the member introduced the bill</p>
    <div class="conn"><div class="who"><button type="button" data-go="${esc(l.member_id)}">${esc(l.member)}</button> · ${esc(num)} ${esc(l.title || '')}</div><div class="src">the bill's own record (GovInfo bill status) · <a href="${esc(billUrl)}" target="_blank" rel="noopener">bill</a></div></div>
    <p class="kicker" style="color:var(--ink-soft)">3 · the company's PAC gave to the member</p>
    <div class="conn"><div class="who"><button type="button" data-go="${esc(l.company_id)}">${esc(l.company)}</button> → <button type="button" data-go="${esc(l.member_id)}">${esc(l.member)}</button></div><div class="how">${cycles}</div><div class="src">FEC Schedule B, the PAC's own filing · <a href="${esc(l.fec_url)}" target="_blank" rel="noopener">filing image</a></div></div>
    <p class="note">Three lawful, disclosed facts that the filings keep on three different pages. The sponsor introduced the bill; that is not the same as writing the provision the company cared about. Connected is not the same as culpable.</p>`;
  panel.classList.add('open'); dirty = true;
  panel.querySelectorAll('[data-go]').forEach(el => { if (!el.dataset.bound) { el.dataset.bound = '1'; el.addEventListener('click', () => openConstellation(el.dataset.go)); } });
}


// ------------------------------------------------------------ the read-only report (public copy): built here from the filed records, nothing sent anywhere
// Josie 2026-10-23: the same shape as the drafted reports (Summary, Scope, Method, Findings, Limits, reply, Sources, Integrity),
// held to the three cores without saying so; every kind of connection, the money trail beside the roles; no waiting period.
const GATES = [
  ['Identity', 'Official ID', 'every organization and person is tied to a registry identifier (SEC CIK, GLEIF LEI, IRS EIN, Bioguide, agency code)'],
  ['Identity', 'Two facts', 'a name alone never links a person; a second independent fact must agree'],
  ['Identity', 'One ID, one entity', 'duplicates are folded into one record with the reason logged; two different official IDs are never merged automatically'],
  ['Transparency', 'Primary source', 'connections come from filings themselves (SEC forms, IRS Form 990, FEC and LDA filings, rosters, statutes), not from news or aggregators'],
  ['Transparency', 'Receipt', 'each connection carries the filing reference and link'],
  ['Transparency', 'Recency', 'a role counts as current only while a filing reports it; ended roles are kept with their dates'],
  ['Integrity', 'No silent change', 'corrections are added as new records that point to the old one; nothing is overwritten'],
  ['Integrity', 'Fingerprint', 'every record and every save is fingerprinted (SHA-256) in a hash-chained log'],
  ['Integrity', 'Boundary crossing', 'links between sectors are measured and logged, not assumed to mean wrongdoing'],
];
const MONEY_TYPES = {
  CORPORATE_PAC_CONTRIBUTED_TO: 'company PAC contributions', LOBBYIST_CONTRIBUTED_TO: "lobbyists' contributions", REGISTRANT_PAC_CONTRIBUTED_TO: "lobbying firms' PAC contributions",
  FEDERAL_CONTRACTOR_FOR: 'federal contracts', FEDERAL_GRANT_FROM: 'federal grants', GRANT_FROM: 'grants', LOBBIES_FOR: 'lobbying (reported income)',
  TRADED_SECURITIES_OF: 'reported trades in its securities', FOUNDATION_GRANT_TO: 'foundation grants',
};
const amountIn = t => { const m = /\$([\d,]+(?:\.\d+)?)/.exec(t || ''); return m ? parseFloat(m[1].replace(/,/g, '')) : null; };
const ROLE_TYPES = new Set(['DIRECTOR_OF', 'OFFICER_OF', 'POSITION_AT', 'OFFICIAL_OF', 'REPRESENTATIVE_IN', 'SENATOR_IN', 'COMMITTEE_MEMBER_OF', 'TEN_PERCENT_OWNER_OF', 'BENEFICIAL_OWNER_OF', 'TRUSTEE_OF', 'MEMBER_OF']);
const TO_SOURCE = new Set(['LOBBIES_FOR', 'FEDERAL_CONTRACTOR_FOR', 'FEDERAL_GRANT_FROM', 'GRANT_FROM']);   // the money runs toward the edge's source (the firm, the contractor, the grantee)
const NOT_MONEY_TO = new Set(['TRADED_SECURITIES_OF']);                                                     // the value of trades: neither paid nor received by the company
async function entityReport(c) {
  const me = c.byId.get(c.center), isPerson = me.person;
  const other = e => c.byId.get(e.s === c.center ? e.t : e.s);
  const direct = c.edges.filter(e => e.s === c.center || e.t === c.center).sort((a, b) => (b.active - a.active) || (b.date || '').localeCompare(a.date || ''));
  const cur = direct.filter(e => e.active).length;
  const counts = { confirmed: 0, 'one source': 0, 'not checked yet': 0, alert: 0 };
  for (const e of direct) counts[e.proof] = (counts[e.proof] || 0) + 1;
  const noUrl = direct.filter(e => !e.url).length;
  // organizations linked through a shared person (the same rule as the drafted reports)
  const byNode = new Map();
  for (const e of c.edges) { for (const x of [e.s, e.t]) { if (!byNode.has(x)) byNode.set(x, []); byNode.get(x).push(e); } }
  const links = [], seen = new Set();
  const push = (a, b, p, e1, e2) => { const k = [a < b ? a : b, a < b ? b : a, p].join('|'); if (!seen.has(k)) { seen.add(k); links.push({ a, b, p, e1, e2 }); } };
  if (isPerson) {
    const orgs = direct.filter(e => ROLE_TYPES.has(e.type)).map(e => [e.s === c.center ? e.t : e.s, e]).filter(([o]) => c.byId.get(o) && !c.byId.get(o).person);
    for (let i = 0; i < orgs.length; i++) for (let j = i + 1; j < orgs.length; j++) if (orgs[i][0] !== orgs[j][0]) push(orgs[i][0], orgs[j][0], c.center, orgs[i][1], orgs[j][1]);
  } else {
    for (const e of direct) {
      if (!ROLE_TYPES.has(e.type)) continue;                                   // a role shared, not a gift or a trade
      const pid = e.s === c.center ? e.t : e.s, pn = c.byId.get(pid);
      if (!pn || !pn.person) continue;
      for (const f of byNode.get(pid) || []) { if (!ROLE_TYPES.has(f.type)) continue; const o = f.s === pid ? f.t : f.s; const on = c.byId.get(o); if (o !== c.center && on && !on.person) push(c.center, o, pid, e, f); }
    }
  }
  const doms = id => new Set((c.byId.get(id) || {}).doms || []);
  const crosses = l => ![...doms(l.a)].some(d => doms(l.b).has(d));
  const cross = links.filter(crosses), same = links.filter(l => !crosses(l));
  const people = new Set(links.map(l => l.p)), orgsLinked = new Set(links.flatMap(l => [l.a, l.b]).filter(x => x !== c.center));
  // the money trail: filed amounts by kind, in and out
  const money = new Map();
  for (const e of direct) {
    const kind = MONEY_TYPES[e.type]; if (!kind) continue;
    const amt = amountIn(e.role);
    const toSource = TO_SOURCE.has(e.type);
    const dir = NOT_MONEY_TO.has(e.type) ? 'value' : ((e.s === c.center) !== toSource ? 'out' : 'in');
    const m = money.get(kind) || { n: 0, stated: 0, out: 0, in: 0, value: 0, top: [] };
    m.n++; if (amt != null) { m.stated++; m[dir] += amt; m.top.push([amt, (other(e) || {}).label || '', dir, e.url]); }
    money.set(kind, m);
  }
  const sources = [...new Set(direct.map(e => e.source).filter(Boolean))].sort();
  const dates = direct.map(e => e.date).filter(Boolean).sort();
  const ids = Object.entries(me.identity || {}).map(([k, v]) => `${esc(k)} ${esc(v)}`).join(', ') || 'no identifier';
  const today = new Date().toISOString().slice(0, 10);
  const roleWord = e => (e.role || e.type.replace(/_/g, ' ').toLowerCase());
  const row = e => { const o = other(e) || {}; const holder = e.s === c.center ? me : o, org = e.s === c.center ? o : me;
    return `<tr class="${e.active ? '' : 'ended'}"><td>Filings report <b>${esc(holder.label || '')}</b> as ${esc(roleWord(e))} of <b>${esc(org.label || '')}</b></td><td>${e.active ? 'current' : 'ended'}</td><td>${esc(e.date || '')}</td><td>${esc(e.source || '')}</td><td class="p-${esc(e.proof).replace(/ /g, '-')}">${esc(e.proof)}</td><td>${e.url ? `<a href="${esc(e.url)}">filing</a>` : 'no link on file'}</td></tr>`; };
  const linkRow = l => { const A = c.byId.get(l.a) || {}, B = c.byId.get(l.b) || {}, P = c.byId.get(l.p) || {};
    return `<tr><td><b>${esc(A.label)}</b> and <b>${esc(B.label)}</b></td><td>${esc(P.label)}: ${esc(roleWord(l.e1))} at the first, ${esc(roleWord(l.e2))} at the second</td><td>${crosses(l) ? 'crosses sectors (' + esc([...doms(l.a)].join('')) + ' / ' + esc([...doms(l.b)].join('')) + ')' : 'within a sector'}</td><td>${l.e1.url ? `<a href="${esc(l.e1.url)}">filing</a>` : ''} ${l.e2.url ? `<a href="${esc(l.e2.url)}">filing</a>` : ''}</td></tr>`; };
  const moneyRows = [...money.entries()].sort((a, b) => (b[1].in + b[1].out) - (a[1].in + a[1].out)).map(([kind, m]) => {
    const top = m.top.sort((a, b) => b[0] - a[0]).slice(0, 5).map(([a, l, d, u]) => `${d === 'out' ? 'to' : d === 'in' ? 'from' : 'by'} ${esc(l)} ${esc(moneyFmt(a))}${u ? ` (<a href="${esc(u)}">filing</a>)` : ''}`).join('; ');
    return `<tr><td>${esc(kind)}${m.value ? ' (value of trades, not money to or from it)' : ''}</td><td>${m.n}</td><td>${m.stated} of ${m.n}</td><td>${m.in ? esc(moneyFmt(m.in)) : '—'}</td><td>${m.out ? esc(moneyFmt(m.out)) : '—'}</td><td>${top}</td></tr>`; });
  const moneyTotal = [...money.values()].reduce((a, m) => a + m.in + m.out, 0);
  const summary = [`Public filings on record connect <b>${esc(me.label)}</b> to ${direct.length} ${isPerson ? 'organizations' : 'organizations and people'} directly (${cur} current, ${direct.length - cur} ended).`];
  if (links.length) summary.push(isPerson
    ? `Because filings report this person at each of them, those organizations are linked to one another: ${links.length} pair${links.length === 1 ? '' : 's'}, ${cross.length} crossing between sectors and ${same.length} within a sector.`
    : `Through ${people.size} ${people.size === 1 ? 'person' : 'people'}, it is linked to ${orgsLinked.size} other organization${orgsLinked.size === 1 ? '' : 's'}; ${cross.length} of those links cross between sectors and ${same.length} stay within a sector.`);
  if (money.size) summary.push(`Money on the record: ${[...money.keys()].join(', ')}; ${moneyFmt(moneyTotal)} paid or received where the filings state an amount (section 4.3).`);
  summary.push(`${counts.confirmed} of the direct connections are confirmed by a second source; ${counts['not checked yet']} are not checked yet${counts.alert ? `; ${counts.alert} cite a source that has changed` : ''}.`);
  const body = `<h1>${esc(me.label)}: connections on the public record</h1>
<p class="meta">Published by Priority Nexus LLC · Systems Assurance Forensic Investigation &amp; Design · built ${today} in your browser from the public sky (prioritynexusllc.github.io/PRIGH-Sky) · read-only</p>
<p><b>Signals for review, not findings of wrongdoing.</b> Everything below is what public filings report. Each item links to its filing so any reader can check it.</p>
<h2>1. Summary</h2><p>${summary.join(' ')}</p>
<h2>2. Scope</h2><ul>
<li>Subject: ${esc(me.label)} (${ids})${me.place ? ', ' + esc([me.place.city, me.place.state, me.place.country].filter(Boolean).join(', ')) : ''}</li>
<li>Sources: ${esc(sources.join(', ') || 'none')}</li>
<li>Filing dates covered: ${dates.length ? esc(dates[0]) + ' to ' + esc(dates[dates.length - 1]) : 'n/a'}</li>
<li>Not examined: private contracts, foreign registries not yet connected, news reporting, and any relationship that is not in a filing. The sky is a work in progress: not every register has been read.</li></ul>
<h2>3. Method</h2><p>Nine checks, three for each core principle, applied to every record before it enters the map:</p>
<ul>${GATES.map(([core, name, text]) => `<li><b>${core}: ${name}</b>: ${text}</li>`).join('')}</ul>
<h3>How this report was made</h3>
<p>Built by the page itself from official public records only; every item links to its filing. Each connection carries the result of automated checks: re-read from its own source, confirmed by a second official source where one exists. No person wrote or edited this page. Nothing here is an accusation or a finding of wrongdoing: it describes what the filings say.</p>
<p><b>Disclosure.</b> Priority Nexus LLC takes funding two ways only: anonymously, never named; or openly, with a report on the giver next to every mention. Today it has no funders, no financial or business relationship with any organization or person in this report, and knows of no conflict of interest.</p>
<h2>4. Findings</h2>
<h3>4.1 Direct connections (${direct.length})</h3>
${direct.length ? `<table><thead><tr><th>What the filings report</th><th>Status</th><th>Latest filing</th><th>Source</th><th>Checked</th><th>Filing</th></tr></thead><tbody>${direct.map(row).join('')}</tbody></table>` : '<p>No verified connections on record.</p>'}
<h3>4.2 Organizations linked through a shared person (${links.length})</h3>
${links.length ? `<table><thead><tr><th>Pair</th><th>Through</th><th>Sectors</th><th>Filings</th></tr></thead><tbody>${links.slice(0, 300).map(linkRow).join('')}</tbody></table>${links.length > 300 ? `<p class="meta">${links.length - 300} more pairs not listed.</p>` : ''}` : '<p>None on record.</p>'}
<h3>4.3 Money on the record</h3>
${money.size ? `<p>Amounts are the figures the filings state, summed; a record without a stated amount is counted but adds nothing to the sum. "In" is money this entity received; "out" is money it paid or gave.</p><table><thead><tr><th>Kind</th><th>Records</th><th>With an amount</th><th>In</th><th>Out</th><th>Largest</th></tr></thead><tbody>${moneyRows.join('')}</tbody></table>` : '<p>No money records on file for this entity: no contributions, contracts, grants, lobbying income or reported trades in the filings read.</p>'}
<h3>4.4 Balance measures</h3><p>Independence, tenure, single-point and overboarding measures run on the whole map and are not computed on this page. The published standards and limits are on the Method page.</p>
<h2>5. Limits</h2><ul>
<li>${noUrl} of ${direct.length} direct connections carry no filing link on this copy; they are shown but should be read as unverified here.</li>
<li>A connection is a filed fact: a board seat, a contract, a contribution, a lobbying filing. It says nothing about intent. Connected is not guilty.</li>
<li>Only people in public roles appear, from the filings that name them in those roles. Nothing about private life is collected.</li>
<li>The map is a work in progress. Missing is not the same as clean.</li></ul>
<h2>6. If you are named here</h2>
<p>Want to answer? Send it to <a href="mailto:theaistherapist@gmail.com?subject=Reply%3A%20${encodeURIComponent(me.label)}">theaistherapist@gmail.com</a>. We post it, in full, under your name, the day it arrives. A record wrong? Say which; it is corrected with a dated note.</p>
<h2>7. All sources</h2>
<ol>${direct.filter(e => e.url).map(e => `<li><a href="${esc(e.url)}">${esc(e.url)}</a> · ${esc(e.source || '')}${e.date ? ' · ' + esc(e.date) : ''}</li>`).join('')}</ol>
<h2>8. Integrity</h2>
<p class="meta" id="fp">fingerprint: computing…</p>`;
  const html = `<!doctype html><html lang="en"><head><meta charset="utf-8"><title>Report: ${esc(me.label)} · PRIGH</title></head><body>${body}</body></html>`;
  let fp = '';
  try { const buf = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(html)); fp = [...new Uint8Array(buf)].map(b => b.toString(16).padStart(2, '0')).join('').slice(0, 16); } catch (e) { fp = 'not available'; }
  const final = html.replace('fingerprint: computing…', `Fingerprint ${fp}: SHA-256 of this page as built, first 16 characters; the same records give the same fingerprint. Map data generated ${esc(skyGenerated || '')}. Every record on the map is fingerprinted in a hash-chained log kept with the project.`);
  let sec = document.getElementById('report-page');
  if (!sec) { sec = document.createElement('section'); sec.className = 'about page report-page'; sec.id = 'report-page'; document.body.appendChild(sec); }
  sec.innerHTML = `<div class="wrap report"><div class="btns no-print"><button class="btn primary" type="button" id="report-print">Print or save as PDF</button><button class="btn" type="button" id="report-close">Close</button></div>${final.replace(/^[\s\S]*<body>/, '').replace(/<\/body>[\s\S]*$/, '')}</div>`;
  sec.hidden = false;
  document.getElementById('report-print').addEventListener('click', () => window.print());
  document.getElementById('report-close').addEventListener('click', () => { sec.hidden = true; });
  sec.scrollTop = 0;
}
const moneyFmt = v => v >= 1e9 ? `$${(v / 1e9).toFixed(2)}B` : v >= 1e6 ? `$${(v / 1e6).toFixed(2)}M` : v >= 1e3 ? `$${Math.round(v / 1e3).toLocaleString()}K` : `$${Math.round(v).toLocaleString()}`;


// ------------------------------------------------------------ Balance: each published standard beside what the records show
// Josie 2026-10-23: like the workbench's Balance tab, "no alarm or tags of alarm, just showing the same laws vs entities".
let balance = null, balanceLoading = false;
async function loadBalance() {
  const box = document.getElementById('balance-body'); if (!box) return;
  if (balance) { renderBalancePage(); return; }
  if (balanceLoading) return;
  balanceLoading = true;
  try { balance = await fetch(STATIC ? 'data/balance.json' : '/api/balance').then(r => { if (!r.ok) throw new Error('HTTP ' + r.status); return r.json(); }); }
  catch (e) { box.innerHTML = `<p class="mono" style="font-size:.78rem">the measures could not be read: ${esc(e.message)}</p>`; balanceLoading = false; return; }
  balanceLoading = false; renderBalancePage();
}
function renderBalancePage() {
  const box = document.getElementById('balance-body'); if (!box || !balance) return;
  const r = balance, go = (id, text) => `<button type="button" class="lnk" data-go="${esc(id)}">${esc(text)}</button>`;
  const pct = v => v == null ? '—' : `${Math.round(v * 100)}%`;
  const ind = r.independence || {}, con = r.concentration || {}, sp = r.single_points || {}, ten = r.tenure || {}, ob = r.overboarding || {};
  const indRows = (ind.flags || []).map(f => `<tr><td>${go(f.org, f.label)}</td><td>${f.directors}</td><td>${f.tied}</td><td>${f.directors ? Math.round(100 * (f.directors - f.tied) / f.directors) : 0}%</td><td>${(f.ties || []).map(t => `${esc(t.label)}: ${esc((t.why || []).join('; '))}`).join('<br>')}</td></tr>`).join('');
  const conRows = (con.domains || []).map(d => !d.organizations && !d.ownership_blocks
    ? `<tr><td><b>${esc(SHORT[d.domain.slice(-1)] || d.domain)}</b></td><td colspan="6">no shareholders to measure (government bodies and courts)</td></tr>`
    : `<tr><td><b>${esc(SHORT[d.domain.slice(-1)] || d.domain)}</b></td><td>${d.organizations}</td><td>${d.ownership_blocks}${d.blocks_above_5 != null ? ` (${d.blocks_above_5} above 5%)` : ''}</td><td>${d.hhi ?? '—'}</td><td>${pct(d.top4_reach_share)}</td><td>${pct(d.top4_family_reach_share ?? d.top4_reach_share)}</td><td>${(d.top_holders || []).slice(0, 3).map(h => `${go(h.id, h.label)} (${h.blocks})`).join(', ')}</td></tr>`).join('');
  const spRows = (sp.flags || []).slice(0, 40).map(f => `<tr><td>${go(f.id, f.label)}</td><td>${(f.cut_off || 0).toLocaleString()}</td></tr>`).join('');
  const tenRows = (ten.flags || []).slice(0, 80).map(f => `<tr><td>${go(f.person, f.label)}</td><td>${go(f.org, f.org_label)}</td><td>${f.years_at_least}</td><td>${esc(f.first_filing || '')} → ${esc(f.latest_filing || '')}</td></tr>`).join('');
  const obRows = (ob.flags || []).map(f => `<tr><td>${go(f.person, f.label)}</td><td>${esc(f.why || '')}</td></tr>`).join('');
  box.innerHTML = `<div class="bal">
<h2>1. Board independence</h2>
<p class="std">Standard: ${esc(ind.standard || '')}. The number: more than ${Math.round((ind.threshold || 0.5) * 100)}% of directors independent. Records: ${ind.boards_scored ?? '—'} boards with enough recorded directors to measure; the rows are boards where half or more of the recorded directors have a filed tie to the company (an officer role, a large stake, or a role at a large holder). A director with no filed tie here may have ties these filings do not show.</p>
${indRows ? `<table><thead><tr><th>Board</th><th>Recorded directors</th><th>With a filed tie</th><th>Independent by the records</th><th>The ties, as filed</th></tr></thead><tbody>${indRows}</tbody></table>` : '<p class="std">Every scored board has a majority of recorded directors with no filed tie.</p>'}
<h2>2. Concentration of ownership, by field</h2>
<p class="std">Standard: ${esc(con.standard || '')}. The number: ${(con.threshold || 1800).toLocaleString()}. Records: every open ownership stake on the map counts as a block (each holder–company pair once); HHI measures how concentrated those blocks are among holders, 0 to 10,000; top-4 reach is the share of the field's organizations that the four most-connected holders own a block of or hold a seat at, counted as filed and again with a parent's units added back to the parent.</p>
<table><thead><tr><th>Field</th><th>Organizations</th><th>Blocks</th><th>HHI</th><th>Top-4 reach, as filed</th><th>Top-4 reach, by family</th><th>Largest holders (blocks)</th></tr></thead><tbody>${conRows}</tbody></table>
<h2>3. Single points</h2>
<p class="std">Not a published standard: a measure of the network itself. In ${(sp.network_size || 0).toLocaleString()} connected entities, ${esc(sp.meaning || 'these are the entities whose removal would cut others off from the rest')}. Records: the count of entities that depend on each.</p>
${spRows ? `<table><thead><tr><th>Entity</th><th>Entities that depend on it</th></tr></thead><tbody>${spRows}</tbody></table>` : '<p class="std">None at the display floor.</p>'}
<h2>4. Length of board service</h2>
<p class="std">Standard: ${esc(ten.standard || '')}. The number: ${ten.threshold || 9} years. Records: ${esc(ten.method || 'the first and latest filing that report the seat')}. The years shown are the least the filings prove.</p>
${tenRows ? `<table><thead><tr><th>Person</th><th>Board</th><th>Years, at least</th><th>Filings</th></tr></thead><tbody>${tenRows}</tbody></table>${(ten.flags || []).length > 80 ? `<p class="std">${(ten.flags || []).length - 80} more not listed.</p>` : ''}` : '<p class="std">None on record.</p>'}
<h2>5. Number of boards</h2>
<p class="std">Standard: ${esc(ob.standard || '')}. The number: ${ob.threshold || 5} public-company boards. Also: ${esc(ob.ceo_standard || '')}. Records: current public-company board seats on the map per person.</p>
${obRows ? `<table><thead><tr><th>Person</th><th>Seats, by the records</th></tr></thead><tbody>${obRows}</tbody></table>` : '<p class="std">None on record.</p>'}
<p class="std">Measured ${esc((r.generated || r.computed_at || '').slice(0, 10))} from the filed records on the map. Every number here can change when a filing is added; nothing is a verdict. Click a name to open its connections.</p>
</div>`;
  box.querySelectorAll('[data-go]').forEach(el => el.addEventListener('click', () => { showPage(null); openConstellation(el.dataset.go); }));
}
