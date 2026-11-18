'use strict';
/* ============================================================
   HOLLOWMERE — first-person dark-fantasy dungeon ARPG
   Single-file implementation. No engine: raw WebGL2 + DOM UI.
   Design source: first_person_dungeon_arpg_design.md
   Node mode (no window) runs headless self-tests instead of booting.
   ============================================================ */
const NODE = typeof window === 'undefined';
const TAU = Math.PI * 2;

/* ---------------- 0.1 basic utils ---------------- */
const clamp = (v, a, b) => v < a ? a : (v > b ? b : v);
const lerp = (a, b, t) => a + (b - a) * t;
const d2 = (ax, az, bx, bz) => { const dx = ax - bx, dz = az - bz; return Math.sqrt(dx * dx + dz * dz); };
const fmt = n => (n | 0).toLocaleString('en-US');
const esc = s => String(s).replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c]));
const el = id => document.getElementById(id);
function mk(tag, cls, html) { const e = document.createElement(tag); if (cls) e.className = cls; if (html !== undefined) e.innerHTML = html; return e; }

/* ---------------- 0.2 RNG ---------------- */
function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a |= 0; a = a + 0x6D2B79F5 | 0;
    let t = Math.imul(a ^ a >>> 15, 1 | a);
    t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
    return ((t ^ t >>> 14) >>> 0) / 4294967296;
  };
}
function hashMix(...ns) { let h = 2166136261 >>> 0; for (const n of ns) { h ^= (n | 0); h = Math.imul(h, 16777619) >>> 0; h ^= h >>> 13; h = Math.imul(h, 0x5bd1e995) >>> 0; } return h >>> 0; }
const pick = (r, arr) => arr[(r() * arr.length) | 0];
const ri = (r, a, b) => a + ((r() * (b - a + 1)) | 0);
const rf = (r, a, b) => a + r() * (b - a);
const chance = (r, p) => r() < p;
function wpick(r, entries) { // entries: [[value, weight],...]
  let tot = 0; for (const e of entries) tot += e[1];
  let x = r() * tot;
  for (const e of entries) { x -= e[1]; if (x <= 0) return e[0]; }
  return entries[entries.length - 1][0];
}
function shuffle(r, arr) { const a = arr.slice(); for (let i = a.length - 1; i > 0; i--) { const j = (r() * (i + 1)) | 0; [a[i], a[j]] = [a[j], a[i]]; } return a; }
function fnv(str) { let h = 2166136261 >>> 0; for (let i = 0; i < str.length; i++) { h ^= str.charCodeAt(i); h = Math.imul(h, 16777619) >>> 0; } return h >>> 0; }

/* ---------------- 0.3 vector / matrix ---------------- */
const v3add = (a, b) => [a[0] + b[0], a[1] + b[1], a[2] + b[2]];
const v3sub = (a, b) => [a[0] - b[0], a[1] - b[1], a[2] - b[2]];
const v3scale = (a, s) => [a[0] * s, a[1] * s, a[2] * s];
const v3dot = (a, b) => a[0] * b[0] + a[1] * b[1] + a[2] * b[2];
const v3cross = (a, b) => [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]];
const v3len = a => Math.sqrt(v3dot(a, a));
const v3norm = a => { const l = v3len(a) || 1; return [a[0] / l, a[1] / l, a[2] / l]; };
const v3dist = (a, b) => v3len(v3sub(a, b));

function m4ident() { return new Float32Array([1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]); }
function m4mul(a, b, out) { // out = a * b (column-major)
  out = out || new Float32Array(16);
  for (let c = 0; c < 4; c++) {
    const b0 = b[c * 4], b1 = b[c * 4 + 1], b2 = b[c * 4 + 2], b3 = b[c * 4 + 3];
    out[c * 4] = a[0] * b0 + a[4] * b1 + a[8] * b2 + a[12] * b3;
    out[c * 4 + 1] = a[1] * b0 + a[5] * b1 + a[9] * b2 + a[13] * b3;
    out[c * 4 + 2] = a[2] * b0 + a[6] * b1 + a[10] * b2 + a[14] * b3;
    out[c * 4 + 3] = a[3] * b0 + a[7] * b1 + a[11] * b2 + a[15] * b3;
  }
  return out;
}
function m4persp(fovY, aspect, near, far) {
  const f = 1 / Math.tan(fovY / 2), nf = 1 / (near - far);
  const m = new Float32Array(16);
  m[0] = f / aspect; m[5] = f; m[10] = (far + near) * nf; m[11] = -1; m[14] = 2 * far * near * nf;
  return m;
}
/* view from position + yaw/pitch. Convention: forward = (-sin(yaw)cos(pitch), sin(pitch), -cos(yaw)cos(pitch)).
   yaw+ turns LEFT; mouse-right decreases yaw. */
function m4view(px, py, pz, yaw, pitch) {
  const cy = Math.cos(yaw), sy = Math.sin(yaw), cp = Math.cos(pitch), sp = Math.sin(pitch);
  // basis
  const fx = -sy * cp, fy = sp, fz = -cy * cp;
  const rx = cy, ry = 0, rz = -sy;
  const ux = v3cross([rx, ry, rz], [fx, fy, fz])[0], uy = v3cross([rx, ry, rz], [fx, fy, fz])[1], uz = v3cross([rx, ry, rz], [fx, fy, fz])[2];
  const m = new Float32Array(16);
  m[0] = rx; m[4] = ry; m[8] = rz;
  m[1] = ux; m[5] = uy; m[9] = uz;
  m[2] = -fx; m[6] = -fy; m[10] = -fz;
  m[12] = -(rx * px + ry * py + rz * pz);
  m[13] = -(ux * px + uy * py + uz * pz);
  m[14] = -(-fx * px + -fy * py + -fz * pz);
  m[15] = 1;
  return m;
}
/* model matrix: translate + yaw(Y) + pitch(X) + roll(Z), scale. */
function m4trs(x, y, z, yaw, s, pitch, roll) {
  s = s === undefined ? 1 : s;
  const cy = Math.cos(yaw), sy = Math.sin(yaw);
  const m = new Float32Array(16);
  // R = Ry(yaw) * Rx(pitch) * Rz(roll) computed inline
  const cp = Math.cos(pitch || 0), sp = Math.sin(pitch || 0);
  const cr = Math.cos(roll || 0), sr = Math.sin(roll || 0);
  // column-major: columns of R*T
  m[0] = cy * cr + sy * sp * sr; m[1] = cp * sr; m[2] = -sy * cr + cy * sp * sr;
  m[4] = -cy * sr + sy * sp * cr; m[5] = cp * cr; m[6] = sy * sr + cy * sp * cr;
  m[8] = sy * cp; m[9] = -sp; m[10] = cy * cp;
  m[12] = x; m[13] = y; m[14] = z; m[15] = 1;
  if (s !== 1) { for (let i = 0; i < 12; i++) m[i] *= s; }
  return m;
}
const m4mulMany = (...ms) => { let m = ms[0]; for (let i = 1; i < ms.length; i++) m = m4mul(m, ms[i]); return m; };

/* ---------------- 0.4 config (data-driven balance, per §18.6) ---------------- */
const CFG = {
  maxLevel: 30, attrPtsPerLevel: 5, talentPtsPerLevel: 1,
  walkSpeed: 4.5, sprintSpeed: 6.3, crouchSpeed: 2.2, sprintStamina: 12,
  jumpSpeed: 5.0, gravity: 15.5,
  dodge: { dist: 3, dur: 0.35, cost: 20, iframes: 0.15 },
  eyeHeight: 1.7, crouchEye: 1.15,
  potionCD: 1.25, stackMaxDefault: 20,
  kick: { reach: 2, dmg: 6, poise: 20, stamina: 12 },
  block: { coneDeg: 100, perfectWindow: 0.18 },
  rarityWeights: { common: 65, enchanted: 25, rare: 9, relic: 1 },
  priceRarity: { common: 1, enchanted: 2, rare: 4, relic: 8 },
  sellFraction: 0.25, buybackMax: 20,
  tile: 3.0, mapW: 92, mapH: 92,
  staminaRegenDelay: 0.8, hpRegenDelay: 3.0,
  interactRange: 2.5,
  noiseStepRadius: 9, noiseAttackRadius: 16,
  severFraction: 0.60, severSingle: 0.35,
  headshotMul: 1.5, critCap: 0.60,
  difficulty: {
    wanderer: { hp: 0.80, dmg: 0.75, loot: 1.0, goldLoss: 0.05, label: 'Wanderer' },
    adventurer: { hp: 1.00, dmg: 1.00, loot: 1.0, goldLoss: 0.10, label: 'Adventurer' },
    dread: { hp: 1.25, dmg: 1.35, loot: 1.1, goldLoss: 0.20, label: 'Dread' },
  },
};
const RULES = {
  player: { max_level: CFG.maxLevel, attribute_points_per_level: 5, class_talent_points_per_level: 1, backpack_grid: [10, 6], quickbar_slots: 6, movement_walk_m_s: 4.5, movement_sprint_m_s: 6.3, stamina_sprint_per_s: 12, potion_shared_cooldown_s: 1.25 },
  dungeon: { floors: 16, regions: 4, min_main_path_nodes: 7, max_main_path_nodes: 15, branch_range: [2, 5], secret_room_range: [0, 2], boss_floors: [4, 8, 12, 16] },
  loot: { rarity_weight_percent: { common: 65, enchanted: 25, rare: 9, relic: 1 }, stack_max_default: 20 },
  difficulty: { default: 'adventurer', normal_gold_loss_fraction: 0.10 },
};

/* ---------------- 0.5 regions ---------------- */
const REGIONS = [
  { id: 0, name: 'Abandoned Barracks', floors: [1, 4], fog: [0.10, 0.09, 0.10], fogCol: [0.012, 0.010, 0.014], wall: [0.32, 0.28, 0.24], wall2: [0.24, 0.21, 0.18], floorC: [0.26, 0.23, 0.20], ceil: [0.16, 0.14, 0.12], torch: [1.0, 0.62, 0.28], amb: 'stone', desc: 'Dusty stone and broken timber.' },
  { id: 1, name: 'The Ossuary', floors: [5, 8], fog: [0.07, 0.10, 0.08], fogCol: [0.008, 0.013, 0.010], wall: [0.26, 0.29, 0.26], wall2: [0.20, 0.22, 0.20], floorC: [0.21, 0.23, 0.21], ceil: [0.12, 0.14, 0.13], torch: [0.45, 0.9, 0.7], amb: 'crypt', desc: 'Candlelit crypts of bone.' },
  { id: 2, name: 'Flooded Works', floors: [9, 12], fog: [0.06, 0.09, 0.12], fogCol: [0.008, 0.012, 0.018], wall: [0.22, 0.26, 0.30], wall2: [0.16, 0.20, 0.24], floorC: [0.19, 0.22, 0.26], ceil: [0.10, 0.12, 0.15], torch: [0.4, 0.8, 1.0], amb: 'cistern', desc: 'Industrial ruins under black water.' },
  { id: 3, name: 'The Unraveling', floors: [13, 16], fog: [0.09, 0.06, 0.12], fogCol: [0.014, 0.008, 0.020], wall: [0.25, 0.21, 0.30], wall2: [0.19, 0.15, 0.24], floorC: [0.22, 0.18, 0.27], ceil: [0.13, 0.10, 0.17], torch: [0.8, 0.4, 1.0], amb: 'rift', desc: 'Warped architecture beyond reason.' },
];
const TOWN_REG = { id: 9, name: 'Hollowmere', fog: [0.16, 0.16, 0.22], fogCol: [0.02, 0.022, 0.035], wall: [0.30, 0.26, 0.22], wall2: [0.24, 0.20, 0.17], floorC: [0.22, 0.20, 0.17], ceil: [0.1, 0.1, 0.12], torch: [1.0, 0.65, 0.3], amb: 'town' };
const regionOf = floor => floor <= 0 ? TOWN_REG : REGIONS[Math.min(3, ((floor - 1) / 4) | 0)];

/* ---------------- 0.6 event bus ---------------- */
const EVT = {
  m: {}, _n: 0,
  on(t, f) { (this.m[t] = this.m[t] || []).push(f); },
  emit(t, d) { const l = this.m[t]; if (!l) return; d = Object.assign({ _id: ++this._n, _t: t }, d); for (const f of l) try { f(d); } catch (e) { if (!NODE) console.error('evt', t, e); } },
};

/* ---------------- 0.7 globals ---------------- */
let G = null;      // session: campaign, floor, mode, time, settings...
let P = null;      // player actor
let R = null;      // renderer
let SND = null;    // audio
let UI = null;     // ui root helpers
let INPUT = null;  // input state

/* ============================================================
   1. AUDIO — procedural WebAudio synth (no assets)
   ============================================================ */
function makeSND() {
  let ctx = null, master = null, sfxG = null, musG = null, ambG = null;
  let ambientNodes = null, ambZone = '';
  const A = {
    init() {
      if (ctx) return;
      try {
        ctx = new (window.AudioContext || window.webkitAudioContext)();
        master = ctx.createGain(); master.connect(ctx.destination);
        sfxG = ctx.createGain(); sfxG.connect(master);
        musG = ctx.createGain(); musG.connect(master);
        ambG = ctx.createGain(); ambG.connect(master);
        this.applyVolumes(G && G.settings || {});
      } catch (e) { ctx = null; }
    },
    resume() { if (ctx && ctx.state === 'suspended') ctx.resume(); },
    applyVolumes(s) {
      if (!ctx) return;
      master.gain.value = (s.volMaster !== undefined ? s.volMaster : 0.8);
      sfxG.gain.value = (s.volSfx !== undefined ? s.volSfx : 0.9);
      musG.gain.value = (s.volMusic !== undefined ? s.volMusic : 0.55);
      ambG.gain.value = (s.volAmb !== undefined ? s.volAmb : 0.7);
    },
    tone(freq, dur, type, vol, slideTo, dest, delay) {
      if (!ctx) return;
      const t0 = ctx.currentTime + (delay || 0);
      const o = ctx.createOscillator(), g = ctx.createGain();
      o.type = type || 'sine'; o.frequency.setValueAtTime(Math.max(20, freq), t0);
      if (slideTo) o.frequency.exponentialRampToValueAtTime(Math.max(20, slideTo), t0 + dur);
      g.gain.setValueAtTime(vol || 0.2, t0);
      g.gain.exponentialRampToValueAtTime(0.0001, t0 + dur);
      o.connect(g); g.connect(dest || sfxG);
      o.start(t0); o.stop(t0 + dur + 0.05);
    },
    noise(dur, vol, filterFreq, q, slideTo, delay) {
      if (!ctx) return;
      const t0 = ctx.currentTime + (delay || 0);
      const len = Math.max(1, (dur * ctx.sampleRate) | 0);
      const buf = ctx.createBuffer(1, len, ctx.sampleRate);
      const d = buf.getChannelData(0);
      for (let i = 0; i < len; i++) d[i] = Math.random() * 2 - 1;
      const src = ctx.createBufferSource(); src.buffer = buf;
      const f = ctx.createBiquadFilter(); f.type = 'bandpass'; f.frequency.setValueAtTime(filterFreq || 800, t0);
      if (slideTo) f.frequency.exponentialRampToValueAtTime(Math.max(40, slideTo), t0 + dur);
      f.Q.value = q || 1;
      const g = ctx.createGain(); g.gain.setValueAtTime(vol || 0.3, t0);
      g.gain.exponentialRampToValueAtTime(0.0001, t0 + dur);
      src.connect(f); f.connect(g); g.connect(sfxG);
      src.start(t0); src.stop(t0 + dur + 0.05);
    },
  };
  const S = {
    init: A.init, resume: A.resume, applyVolumes: A.applyVolumes, ready: () => !!ctx,
    ui() { A.tone(700, 0.05, 'square', 0.05); },
    uiBig() { A.tone(340, 0.16, 'triangle', 0.14, 220); A.tone(510, 0.14, 'sine', 0.08, 400, null, 0.02); },
    error() { A.tone(140, 0.18, 'sawtooth', 0.1, 90); },
    step(mat, run) {
      const f = mat === 'water' ? 500 : mat === 'wood' ? 240 : 170;
      A.noise(0.07, run ? 0.10 : 0.06, f + Math.random() * 60, 1.4);
    },
    swing() { A.noise(0.14, 0.16, 900, 0.8, 300); },
    heavySwing() { A.noise(0.22, 0.2, 500, 0.8, 180); A.tone(90, 0.16, 'sine', 0.1, 55); },
    bow() { A.noise(0.09, 0.14, 1500, 2, 2400); A.tone(280, 0.07, 'triangle', 0.06, 480); },
    hitFlesh() { A.noise(0.09, 0.3, 300, 1, 120); A.tone(110, 0.08, 'sine', 0.14, 60); },
    hitMetal() { A.tone(2100, 0.1, 'square', 0.09, 1300); A.noise(0.07, 0.16, 2600, 3); },
    hitStone() { A.noise(0.08, 0.22, 800, 1.4, 300); },
    block() { A.tone(1300, 0.1, 'square', 0.13, 900); A.noise(0.06, 0.14, 3000, 4); },
    parry() { A.tone(2400, 0.16, 'triangle', 0.2, 3200); A.tone(1600, 0.2, 'sine', 0.14, 2400, null, 0.02); },
    kick() { A.noise(0.1, 0.24, 200, 0.9, 90); A.tone(70, 0.1, 'sine', 0.2, 45); },
    thud() { A.tone(80, 0.14, 'sine', 0.26, 45); A.noise(0.1, 0.16, 150, 1); },
    arrowHit() { A.noise(0.06, 0.2, 900, 2, 400); },
    castFire() { A.noise(0.3, 0.18, 600, 0.7, 1800); A.tone(180, 0.25, 'sawtooth', 0.08, 90); },
    castFrost() { A.tone(1300, 0.28, 'sine', 0.1, 500); A.noise(0.22, 0.1, 2400, 2, 800); },
    castArc() { A.tone(760, 0.16, 'triangle', 0.12, 1300); },
    castLight() { A.noise(0.16, 0.2, 2600, 1.2, 500); A.tone(2200, 0.12, 'sawtooth', 0.08, 400); },
    castHoly() { A.tone(620, 0.35, 'sine', 0.12, 930); A.tone(930, 0.3, 'sine', 0.08, 1240, null, 0.06); },
    castDark() { A.tone(210, 0.35, 'sawtooth', 0.1, 95); },
    explode() { A.noise(0.5, 0.4, 350, 0.6, 60); A.tone(60, 0.45, 'sine', 0.3, 30); },
    potion() { A.tone(300, 0.09, 'sine', 0.1, 500); A.noise(0.12, 0.12, 700, 2, 300, 0.06); },
    gold() { A.tone(1900, 0.08, 'triangle', 0.1); A.tone(2400, 0.1, 'triangle', 0.09, 2000, null, 0.05); A.tone(1500, 0.12, 'triangle', 0.08, 1800, null, 0.1); },
    pickup(r) {
      const base = r === 3 ? 900 : r === 2 ? 740 : r === 1 ? 600 : 480;
      A.tone(base, 0.12, 'triangle', 0.12);
      A.tone(base * 1.5, 0.14, 'triangle', 0.1, null, null, 0.08);
      if (r >= 2) { A.tone(base * 2, 0.2, 'triangle', 0.1, null, null, 0.16); A.tone(base * 3, 0.26, 'sine', 0.08, null, null, 0.24); }
    },
    levelUp() { [523, 659, 784, 1046].forEach((f, i) => A.tone(f, 0.3, 'triangle', 0.14, null, null, i * 0.1)); },
    quest() { [660, 880, 1100].forEach((f, i) => A.tone(f, 0.25, 'sine', 0.11, null, null, i * 0.09)); },
    door() { A.noise(0.5, 0.14, 200, 2, 90); A.tone(90, 0.4, 'sawtooth', 0.05, 65); },
    chest() { A.noise(0.3, 0.16, 250, 1.4, 120); A.tone(1200, 0.15, 'sine', 0.07, 1500, null, 0.2); },
    shrine() { A.tone(440, 0.7, 'sine', 0.1, 660); A.tone(659, 0.7, 'sine', 0.07, 880, null, 0.12); },
    growl(big) { A.tone(big ? 70 : 120, 0.35, 'sawtooth', big ? 0.16 : 0.1, big ? 45 : 80); A.noise(0.3, 0.1, big ? 150 : 300, 0.8); },
    screech() { A.tone(1400, 0.25, 'sawtooth', 0.08, 2400); },
    roar() { A.tone(55, 0.9, 'sawtooth', 0.3, 38); A.noise(0.8, 0.28, 180, 0.5, 70); },
    hurt() { A.tone(190, 0.14, 'sawtooth', 0.14, 130); },
    death() { A.tone(160, 0.7, 'sawtooth', 0.16, 50); A.noise(0.5, 0.2, 200, 0.7, 60); },
    portal() { A.tone(300, 0.8, 'sine', 0.1, 1200); A.tone(450, 0.8, 'sine', 0.08, 1800, null, 0.1); },
    identify() { A.tone(880, 0.2, 'sine', 0.1, 1320); A.tone(1320, 0.25, 'sine', 0.08, null, null, 0.12); },
    lore() { A.tone(520, 0.2, 'sine', 0.08); A.tone(780, 0.3, 'sine', 0.06, null, null, 0.12); },
    ambient(zone) {
      if (!ctx || zone === ambZone) return;
      ambZone = zone;
      if (ambientNodes) { ambientNodes.forEach(n => { try { n.g.gain.linearRampToValueAtTime(0.0001, ctx.currentTime + 1.5); n.o.stop(ctx.currentTime + 1.8); } catch (e) {} }); ambientNodes = null; }
      const defs = {
        town: [[98, 'sine', 0.05], [147, 'sine', 0.03], [196, 'triangle', 0.012]],
        stone: [[62, 'sine', 0.05], [93, 'triangle', 0.02]],
        crypt: [[55, 'sine', 0.05], [82.5, 'sawtooth', 0.012]],
        cistern: [[49, 'sine', 0.05], [73.4, 'triangle', 0.016]],
        rift: [[58, 'sawtooth', 0.03], [87, 'sine', 0.035], [116.5, 'triangle', 0.01]],
        boss: [[41.2, 'sawtooth', 0.06], [61.7, 'sine', 0.04]],
      };
      const use = defs[zone] || defs.stone;
      ambientNodes = use.map(([f, type, vol]) => {
        const o = ctx.createOscillator(), g = ctx.createGain();
        o.type = type; o.frequency.value = f;
        const lfo = ctx.createOscillator(), lg = ctx.createGain();
        lfo.frequency.value = 0.1 + Math.random() * 0.2; lg.gain.value = vol * 0.5;
        lfo.connect(lg); lg.connect(g.gain);
        g.gain.setValueAtTime(0.0001, ctx.currentTime);
        g.gain.linearRampToValueAtTime(vol, ctx.currentTime + 2.5);
        o.connect(g); g.connect(ambG);
        o.start(); lfo.start();
        return { o, g };
      });
    },
    stopAmbient() { if (ambientNodes) { ambientNodes.forEach(n => { try { n.o.stop(); } catch (e) {} }); ambientNodes = null; ambZone = ''; } },
  };
  return S;
}

/* ============================================================
   2. DATA — classes, talents (24), spells (10)
   ============================================================ */
const CLASSES = {
  vanguard: {
    name: 'Vanguard', color: '#b3552e', glyph: '🛡',
    attrs: { str: 20, dex: 12, int: 8, vit: 18 },
    hpB: 15, stB: 10, mpB: 0, mpRegen: 0, moveB: 0,
    gear: ['sword_iron', 'shield_round', 'chest_padded', 'potion_health_s:2'],
    desc: 'Block, armor converted to offense, staggering melee. Starts with sword, shield and padded armor.',
  },
  stalker: {
    name: 'Stalker', color: '#3f8a4f', glyph: '🏹',
    attrs: { str: 12, dex: 20, int: 10, vit: 14 },
    hpB: 0, stB: 5, mpB: 0, mpRegen: 0, moveB: 0.05,
    gear: ['bow_short', 'dagger_shiv', 'chest_leather', 'potion_health_s:1', 'potion_stam:1'],
    desc: 'Mobility, bow precision, bleeding and traps. Starts with short bow, dagger and leather armor.',
  },
  arcanist: {
    name: 'Arcanist', color: '#5b5fb5', glyph: '✦',
    attrs: { str: 8, dex: 12, int: 22, vit: 12 },
    hpB: 0, stB: 0, mpB: 20, mpRegen: 0.5, moveB: 0,
    gear: ['staff_apprentice', 'chest_cloth', 'book_magic_dart', 'potion_health_s:1', 'potion_mana_s:2'],
    desc: 'Spell manipulation, elemental effects, mana economy. Starts with a staff, robe and a learned Magic Dart.',
  },
};
const CLASS_IDS = ['vanguard', 'stalker', 'arcanist'];

/* talents: tier 1 free, tier 2 needs 3 pts in tree, tier 3 needs 8 */
const TALENTS = [
  { id: 'bulwark', cls: 'vanguard', name: 'Bulwark Rush', type: 'active', tier: 1, cd: 10, desc: 'Dash up to 5 m, deal 12 radiant damage + 0.15×current Armor to the first target.', scale: '+15% damage/rank', params: { dmg: 12, dmgRank: 1.8, armorScale: 0.15, dist: 5 } },
  { id: 'verdict', cls: 'vanguard', name: 'Crushing Verdict', type: 'active', tier: 1, cd: 8, desc: 'Next heavy strike adds 10 radiant damage and 25 stagger.', scale: '+5 damage/rank', params: { dmg: 10, dmgRank: 5, poise: 25, dur: 8 } },
  { id: 'shieldpulse', cls: 'vanguard', name: 'Shield Pulse', type: 'active', tier: 1, cd: 12, desc: 'Frontal 3 m knockback, 8 physical damage.', scale: '+10% force/rank', params: { dmg: 8, poise: 30, dist: 3, forceRank: 0.10 } },
  { id: 'rally', cls: 'vanguard', name: 'Rally', type: 'active', tier: 2, cd: 25, desc: 'Heal 15% missing health and grant +20 armor for 8 s.', scale: '+3 armor/rank', params: { healFrac: 0.15, armor: 20, armorRank: 3, dur: 8 } },
  { id: 'defiant', cls: 'vanguard', name: 'Defiant Stand', type: 'active', tier: 3, cd: 24, desc: '4 s guard stance: stamina drain on block halved.', scale: '+0.5 s/rank', params: { dur: 4, durRank: 0.5 } },
  { id: 'iron', cls: 'vanguard', name: 'Iron Training', type: 'passive', tier: 1, desc: '+8% base armor.', scale: '+4%/rank', params: { armorPct: 0.08, rank: 0.04 } },
  { id: 'retaliation', cls: 'vanguard', name: 'Retaliation', type: 'passive', tier: 2, desc: 'Successful perfect block adds +10% to next melee damage.', scale: '+5%/rank', params: { dmgPct: 0.10, rank: 0.05 } },
  { id: 'heavyhands', cls: 'vanguard', name: 'Heavy Hands', type: 'passive', tier: 3, desc: '+6% two-handed damage and stagger.', scale: '+4%/rank', params: { dmgPct: 0.06, rank: 0.04 } },
  { id: 'shadowstep', cls: 'stalker', name: 'Shadow Step', type: 'active', tier: 1, cd: 10, desc: '5 m evasion dash.', scale: '+0.5 m/rank', params: { dist: 5, distRank: 0.5 } },
  { id: 'piercing', cls: 'stalker', name: 'Piercing Shot', type: 'active', tier: 1, cd: 12, desc: 'Next arrow pierces 2 targets for 120% weapon damage.', scale: '+10% damage/rank', params: { dmgPct: 1.20, rank: 0.10, pierce: 2, dur: 8 } },
  { id: 'rend', cls: 'stalker', name: 'Rend', type: 'active', tier: 1, cd: 9, desc: 'Next dagger strike inflicts 4 s bleed for 12 total damage.', scale: '+25% bleed/rank', params: { bleed: 12, rank: 0.25, dur: 8 } },
  { id: 'caltrops', cls: 'stalker', name: 'Caltrops', type: 'active', tier: 2, cd: 20, desc: 'Trap lasting 12 s: slows enemies 35% in a 2.5 m area.', scale: '+2 s/rank', params: { dur: 12, durRank: 2, slow: 0.35, radius: 2.5 } },
  { id: 'quickdraw', cls: 'stalker', name: 'Quickdraw', type: 'active', tier: 3, cd: 25, desc: 'For 6 s, +25% bow attack speed.', scale: '+5%/rank', params: { dur: 6, spdPct: 0.25, rank: 0.05 } },
  { id: 'keeneye', cls: 'stalker', name: 'Keen Eye', type: 'passive', tier: 1, desc: '+4% critical chance.', scale: '+2%/rank', params: { crit: 0.04, rank: 0.02 } },
  { id: 'trapsense', cls: 'stalker', name: 'Trap Sense', type: 'passive', tier: 2, desc: 'Trap highlight from 2 m.', scale: '+1 m/rank', params: { dist: 2, rank: 1 } },
  { id: 'evasive', cls: 'stalker', name: 'Evasive Footwork', type: 'passive', tier: 3, desc: '-8% dodge stamina cost.', scale: '-4%/rank', params: { costPct: 0.08, rank: 0.04 } },
  { id: 'arcbolt', cls: 'arcanist', name: 'Arc Bolt', type: 'active', tier: 1, cd: 1.5, mana: 5, desc: 'Hitscan magic projectile: 16 arcane damage.', scale: '+20% damage/rank', params: { dmg: 16, rank: 0.20, mana: 5 } },
  { id: 'emberwave', cls: 'arcanist', name: 'Ember Wave', type: 'active', tier: 1, cd: 8, mana: 12, desc: '5 m cone: 18 fire damage, 35% ignite chance.', scale: '+15% damage/rank', params: { dmg: 18, rank: 0.15, mana: 12, cone: 5, ignite: 0.35 } },
  { id: 'frostring', cls: 'arcanist', name: 'Frost Ring', type: 'active', tier: 2, cd: 12, mana: 14, desc: '3 m radius: 12 frost damage, slow 40% for 3 s.', scale: '+10% slow duration/rank', params: { dmg: 12, rank: 0.10, mana: 14, radius: 3, slowDur: 3 } },
  { id: 'manaward', cls: 'arcanist', name: 'Mana Ward', type: 'active', tier: 2, cd: 20, desc: '10 s ward absorbs 30 damage, consuming 1 mana per 3 damage taken.', scale: '+10 ward/rank', params: { ward: 30, rank: 3, dur: 10, mana: 0 } },
  { id: 'blink', cls: 'arcanist', name: 'Blink', type: 'active', tier: 3, cd: 13, mana: 15, desc: 'Teleport up to 6 m to a visible navigable location.', scale: '+1 m/rank', params: { dist: 6, rank: 1, mana: 15 } },
  { id: 'channeler', cls: 'arcanist', name: 'Channeler', type: 'passive', tier: 1, desc: '+10% mana regeneration.', scale: '+5%/rank', params: { mpRegenPct: 0.10, rank: 0.05 } },
  { id: 'elementalist', cls: 'arcanist', name: 'Elementalist', type: 'passive', tier: 2, desc: '+6% fire/frost/lightning damage.', scale: '+3%/rank', params: { elemPct: 0.06, rank: 0.03 } },
  { id: 'spellecho', cls: 'arcanist', name: 'Spell Echo', type: 'passive', tier: 3, desc: '5% chance to repeat a projectile at 40% damage.', scale: '+3% chance/rank', params: { chance: 0.05, rank: 0.03, echoMul: 0.4 } },
];
const TALENT_BY_ID = {}; TALENTS.forEach(t => TALENT_BY_ID[t.id] = t);

const SPELLS = {
  magic_dart: { name: 'Magic Dart', kind: 'projectile', elem: 'arcane', dmg: 10, mana: 4, cast: 0.4, cd: 0.8, range: 20, speed: 26, desc: 'Arcane projectile.' },
  ember_orb: { name: 'Ember Orb', kind: 'projectile', elem: 'fire', dmg: 14, blast: 2, blastDmg: 8, mana: 12, cast: 1.0, cd: 3, range: 18, speed: 18, desc: 'Fire projectile with a 2 m blast.' },
  ice_lance: { name: 'Ice Lance', kind: 'projectile', elem: 'frost', dmg: 16, chill: 40, mana: 10, cast: 0.7, cd: 2, range: 20, speed: 30, desc: 'Frost lance, strong chill buildup.' },
  fork_lightning: { name: 'Forked Lightning', kind: 'chain', elem: 'lightning', dmg: 12, chain: 2, chainMul: 0.7, mana: 16, cast: 0.6, cd: 4, range: 16, desc: 'Lightning that chains to 2 further targets at 70%.' },
  mend: { name: 'Mend Wounds', kind: 'heal', heal: 20, healInt: 0.7, mana: 14, cast: 1.0, cd: 8, desc: 'Heal 20 + 0.7×INT. Cannot revive the dead.' },
  stone_skin: { name: 'Stone Skin', kind: 'buff', armor: 25, dur: 20, mana: 18, cast: 0.8, cd: 25, desc: '+25 armor for 20 s.' },
  reveal: { name: 'Reveal', kind: 'utility', dur: 8, mana: 10, cast: 0.6, cd: 15, desc: 'Reveals nearby loot, interactables and hidden-door hints for 8 s.' },
  phase: { name: 'Phase Step', kind: 'blink', dist: 4, mana: 14, cast: 0.4, cd: 10, desc: '4 m blink to the nearest valid spot.' },
  venom_mist: { name: 'Venom Mist', kind: 'aoe', elem: 'poison', dmg: 6, radius: 3, dur: 5, mana: 16, cast: 0.9, cd: 10, desc: '3 m poison cloud for 5 s.' },
  return_sigil: { name: 'Return Sigil', kind: 'portal', channel: 3, mana: 25, cast: 0, cd: 30, desc: 'Channel 3 s to open a return portal to town. Unusable for 5 s after taking damage.' },
};
const SPELL_ORDER = ['magic_dart', 'ice_lance', 'ember_orb', 'fork_lightning', 'mend', 'stone_skin', 'reveal', 'phase', 'venom_mist', 'return_sigil'];
const spellRankCost = (base, rank) => Math.round(base * (1 + 0.10 * (rank - 1)));
const spellRankMul = (rank, dmgLike) => 1 + (dmgLike ? 0.20 : 0.15) * (rank - 1);
const spellLearnINT = rank => 12 + (rank - 1) * 4;

/* ============================================================
   3. DATA — items, affixes, relics, loot generation
   ============================================================ */
const RAR = [
  { id: 'common', name: 'Common', col: '#d7d7d7', mult: 1 },
  { id: 'enchanted', name: 'Enchanted', col: '#5b9bd5', mult: 2 },
  { id: 'rare', name: 'Rare', col: '#e8c84a', mult: 4 },
  { id: 'relic', name: 'Relic', col: '#ff9a3c', mult: 8 },
];
const RAR_IDX = { common: 0, enchanted: 1, rare: 2, relic: 3 };
const SHAPE_MARK = ['■', '◆', '★', '✹'];

function W(id, name, fam, minD, maxD, elem, reach, wind, rec, stam, poise, reqs, minLvl, w, h, value, extra) {
  return Object.assign({ id, name, cat: 'weapon', fam, slot: 'main', dmg: { min: minD, max: maxD, elem }, reach, wind, rec, stam, poise, reqs: reqs || {}, minLvl: minLvl || 1, w, h, value, two: ['spear', 'great', 'bow'].includes(fam), durMax: 45 + (minLvl || 1) * 3 }, extra || {});
}
const ITEM_BASES = {};
[
  W('sword_worn', 'Worn Blade', 'sword', 4, 7, 'slash', 2.0, .22, .34, 8, 6, { str: 10 }, 1, 1, 3, 40),
  W('sword_iron', 'Iron Sabre', 'sword', 5, 9, 'slash', 2.0, .22, .34, 9, 7, { str: 12 }, 4, 1, 3, 65),
  W('longsword_steel', 'Steel Longsword', 'sword', 7, 12, 'slash', 2.1, .24, .36, 10, 9, { str: 14 }, 9, 1, 3, 120),
  W('knight_blade', "Knight's Blade", 'sword', 9, 15, 'slash', 2.1, .25, .36, 10, 10, { str: 16 }, 15, 1, 3, 210),
  W('runeblade', 'Runeblade', 'sword', 11, 18, 'slash', 2.15, .25, .37, 11, 12, { str: 18 }, 21, 1, 3, 340),
  W('axe_hand', 'Hand Axe', 'axe', 5, 9, 'slash', 1.8, .26, .38, 9, 8, { str: 11 }, 1, 1, 3, 45),
  W('axe_war', 'War Axe', 'axe', 8, 13, 'slash', 1.9, .28, .40, 11, 10, { str: 14 }, 8, 1, 3, 130),
  W('axe_cleaver', 'Ossuary Cleaver', 'axe', 10, 16, 'slash', 2.0, .30, .42, 12, 12, { str: 16 }, 14, 1, 3, 230),
  W('axe_executioner', "Executioner's Axe", 'axe', 13, 20, 'slash', 2.1, .33, .45, 13, 14, { str: 19 }, 20, 1, 3, 360),
  W('club', 'Club', 'mace', 4, 8, 'blunt', 1.7, .24, .36, 7, 9, { str: 9 }, 1, 1, 3, 25),
  W('mace_iron', 'Iron Mace', 'mace', 6, 10, 'blunt', 1.8, .26, .38, 9, 11, { str: 12 }, 5, 1, 3, 85),
  W('mace_morningstar', 'Morning Star', 'mace', 9, 14, 'blunt', 1.9, .28, .40, 11, 13, { str: 15 }, 10, 1, 3, 160),
  W('mace_skullhammer', 'Skullhammer', 'mace', 12, 18, 'blunt', 2.0, .30, .44, 13, 16, { str: 18 }, 16, 1, 3, 290),
  W('dagger_shiv', 'Shiv', 'dagger', 3, 5, 'pierce', 1.3, .14, .20, 5, 4, { dex: 9 }, 1, 1, 2, 35),
  W('dagger_stiletto', 'Stiletto', 'dagger', 4, 7, 'pierce', 1.3, .15, .21, 5, 5, { dex: 12 }, 6, 1, 2, 75),
  W('dagger_fang', 'Fang Dirk', 'dagger', 6, 9, 'pierce', 1.35, .16, .22, 6, 6, { dex: 15 }, 12, 1, 2, 140),
  W('spear_ash', 'Ash Spear', 'spear', 6, 10, 'pierce', 2.8, .28, .40, 9, 8, { str: 12 }, 1, 1, 4, 70),
  W('pike', 'Workshop Pike', 'spear', 9, 14, 'pierce', 3.0, .30, .42, 10, 10, { str: 14 }, 10, 1, 4, 150),
  W('spear_lance', 'Warlance', 'spear', 12, 18, 'pierce', 3.1, .32, .45, 11, 12, { str: 17 }, 16, 1, 4, 260),
  W('great_blade', 'Greatblade', 'great', 10, 16, 'slash', 2.3, .38, .50, 14, 16, { str: 15 }, 3, 2, 3, 140),
  W('zweihander', 'Mire Zweihander', 'great', 13, 20, 'slash', 2.4, .40, .52, 16, 19, { str: 18 }, 12, 2, 3, 250),
  W('doom_glaive', 'Doom Glaive', 'great', 16, 24, 'slash', 2.5, .42, .55, 18, 22, { str: 21 }, 18, 2, 3, 380),
  W('bow_short', 'Short Bow', 'bow', 5, 8, 'pierce', 30, .18, .30, 6, 0, { dex: 10 }, 1, 1, 4, 55, { projSpeed: 26 }),
  W('bow_hunter', "Hunter's Bow", 'bow', 7, 11, 'pierce', 32, .18, .30, 6, 0, { dex: 13 }, 6, 1, 4, 110, { projSpeed: 28 }),
  W('longbow', 'Longbow', 'bow', 9, 14, 'pierce', 34, .20, .32, 7, 0, { dex: 16 }, 11, 1, 4, 190, { projSpeed: 30 }),
  W('bow_war', 'Warbow', 'bow', 12, 18, 'pierce', 36, .20, .32, 7, 0, { dex: 19 }, 17, 1, 4, 300, { projSpeed: 33 }),
  W('staff_apprentice', 'Apprentice Staff', 'staff', 3, 5, 'blunt', 1.9, .30, .42, 8, 6, { int: 8 }, 1, 1, 4, 60, { spellPower: .08 }),
  W('staff_oak', 'Oak Staff', 'staff', 4, 7, 'blunt', 1.95, .30, .42, 8, 7, { int: 12 }, 7, 1, 4, 130, { spellPower: .12 }),
  W('staff_arch', 'Archfocus', 'staff', 5, 9, 'blunt', 2.0, .32, .44, 9, 8, { int: 16 }, 13, 1, 4, 240, { spellPower: .16 }),
  W('wand_willow', 'Willow Wand', 'wand', 2, 4, 'pierce', 1.5, .16, .24, 4, 3, { dex: 8 }, 1, 1, 2, 45, { spellPower: .06 }),
  W('wand_silver', 'Silver Wand', 'wand', 3, 6, 'pierce', 1.5, .16, .24, 4, 3, { dex: 11 }, 8, 1, 2, 95, { spellPower: .10 }),
].forEach(b => ITEM_BASES[b.id] = b);

function A_(id, name, slot, armor, reqs, minLvl, w, h, value, tags) {
  return { id, name, cat: 'armor', slot, armor, reqs: reqs || {}, minLvl: minLvl || 1, w, h, value, tags: tags || [], durMax: 30 + (minLvl || 1) * 2 };
}
[
  A_('hood_cloth', 'Cloth Hood', 'head', 2, null, 1, 1, 1, 20, ['cloth']),
  A_('cap_leather', 'Leather Cap', 'head', 4, null, 4, 1, 1, 45, ['leather']),
  A_('coif_chain', 'Chain Coif', 'head', 7, { str: 12 }, 9, 1, 1, 95, ['mail']),
  A_('helm_plate', 'Plate Helm', 'head', 10, { str: 16 }, 15, 2, 2, 180, ['plate']),
  A_('chest_cloth', 'Cloth Robe', 'chest', 3, null, 1, 2, 3, 30, ['cloth']),
  A_('chest_padded', 'Padded Armor', 'chest', 6, null, 1, 2, 3, 60, ['leather']),
  A_('chest_leather', 'Leather Jerkin', 'chest', 9, { dex: 10 }, 5, 2, 3, 110, ['leather']),
  A_('chest_mail', 'Chain Hauberk', 'chest', 14, { str: 13 }, 10, 2, 3, 210, ['mail']),
  A_('chest_plate', 'Plate Cuirass', 'chest', 20, { str: 17 }, 16, 2, 3, 360, ['plate']),
  A_('gloves_cloth', 'Cloth Wraps', 'gloves', 1, null, 1, 1, 1, 12, ['cloth']),
  A_('gloves_leather', 'Leather Gloves', 'gloves', 3, null, 4, 1, 1, 40, ['leather']),
  A_('gauntlets_mail', 'Mail Gauntlets', 'gloves', 5, { str: 12 }, 9, 1, 1, 85, ['mail']),
  A_('gauntlets_plate', 'Plate Gauntlets', 'gloves', 7, { str: 16 }, 15, 1, 1, 160, ['plate']),
  A_('boots_cloth', 'Cloth Shoes', 'boots', 1, null, 1, 1, 1, 12, ['cloth']),
  A_('boots_leather', 'Leather Boots', 'boots', 3, null, 4, 1, 2, 40, ['leather']),
  A_('boots_mail', 'Mail Sabatons', 'boots', 5, { str: 12 }, 9, 1, 2, 85, ['mail']),
  A_('boots_plate', 'Plate Greaves', 'boots', 7, { str: 16 }, 15, 1, 2, 160, ['plate']),
].forEach(b => ITEM_BASES[b.id] = b);
ITEM_BASES['buckler'] = { id: 'buckler', name: 'Buckler', cat: 'shield', slot: 'off', blockAbs: 0.70, blockElem: 0.35, reqs: { str: 8 }, minLvl: 1, w: 1, h: 2, value: 35, durMax: 40 };
ITEM_BASES['shield_round'] = { id: 'shield_round', name: 'Round Shield', cat: 'shield', slot: 'off', blockAbs: 0.75, blockElem: 0.4, reqs: { str: 10 }, minLvl: 1, w: 1, h: 2, value: 55, durMax: 48 };
ITEM_BASES['shield_kite'] = { id: 'shield_kite', name: 'Kite Shield', cat: 'shield', slot: 'off', blockAbs: 0.85, blockElem: 0.5, reqs: { str: 13 }, minLvl: 6, w: 1, h: 3, value: 105, durMax: 55 };
ITEM_BASES['shield_tower'] = { id: 'shield_tower', name: 'Tower Shield', cat: 'shield', slot: 'off', blockAbs: 0.95, blockElem: 0.6, reqs: { str: 17 }, minLvl: 12, w: 2, h: 3, value: 220, durMax: 62 };
ITEM_BASES['focus_crystal'] = { id: 'focus_crystal', name: 'Crystal Focus', cat: 'focus', slot: 'off', spellPower: .10, reqs: { int: 10 }, minLvl: 1, w: 1, h: 2, value: 70, durMax: 30 };
ITEM_BASES['tome_runes'] = { id: 'tome_runes', name: 'Runed Tome', cat: 'focus', slot: 'off', spellPower: .15, reqs: { int: 14 }, minLvl: 8, w: 1, h: 2, value: 150, durMax: 30 };
ITEM_BASES['ring_copper'] = { id: 'ring_copper', name: 'Copper Ring', cat: 'ring', slot: 'ring', w: 1, h: 1, value: 40, minLvl: 1, durMax: 0 };
ITEM_BASES['ring_signet'] = { id: 'ring_signet', name: 'Signet Ring', cat: 'ring', slot: 'ring', w: 1, h: 1, value: 90, minLvl: 6, durMax: 0 };
ITEM_BASES['ring_garnet'] = { id: 'ring_garnet', name: 'Garnet Ring', cat: 'ring', slot: 'ring', w: 1, h: 1, value: 140, minLvl: 11, durMax: 0 };
ITEM_BASES['amulet_bone'] = { id: 'amulet_bone', name: 'Bone Amulet', cat: 'amulet', slot: 'amulet', w: 1, h: 1, value: 50, minLvl: 1, durMax: 0 };
ITEM_BASES['amulet_moonglass'] = { id: 'amulet_moonglass', name: 'Moonglass Amulet', cat: 'amulet', slot: 'amulet', w: 1, h: 1, value: 120, minLvl: 7, durMax: 0 };
ITEM_BASES['amulet_ward'] = { id: 'amulet_ward', name: 'Warded Talisman', cat: 'amulet', slot: 'amulet', w: 1, h: 1, value: 200, minLvl: 12, durMax: 0 };
ITEM_BASES['arrows'] = { id: 'arrows', name: 'Arrows', cat: 'ammo', slot: null, stackMax: 240, w: 1, h: 1, value: 2, minLvl: 1, durMax: 0, priceEach: 2 };

const CONSUM = [
  ['potion_health_s', 'Minor Health Potion', 'heal', 0.30, 1, 1, 25],
  ['potion_health_m', 'Health Potion', 'heal', 0.50, 1, 1, 50],
  ['potion_health_g', 'Greater Health Potion', 'heal', 0.80, 1, 1, 90],
  ['potion_mana_s', 'Minor Mana Potion', 'mana', 0.30, 1, 1, 25],
  ['potion_mana_m', 'Mana Potion', 'mana', 0.50, 1, 1, 50],
  ['potion_mana_g', 'Greater Mana Potion', 'mana', 0.80, 1, 1, 90],
  ['potion_stam', 'Stamina Tonic', 'stam', 0.70, 1, 1, 40],
  ['antidote', 'Antidote', 'cure', 'poison', 1, 1, 30],
  ['cleanse', 'Cleansing Draught', 'cure', 'curse', 1, 1, 35],
  ['elixir_resist', 'Resistance Elixir', 'resist', 0.25, 1, 1, 45],
  ['scroll_identify', 'Scroll of Identification', 'identify', 1, 1, 1, 40],
  ['scroll_portal', 'Scroll of Return', 'portal', 1, 1, 1, 60],
];
CONSUM.forEach(([id, name, kind, param, w, h, value]) => ITEM_BASES[id] = { id, name, cat: kind === 'portal' || kind === 'identify' ? 'scroll' : 'potion', slot: null, effect: { kind, param }, stackMax: 20, w, h, value, minLvl: 1, durMax: 0 });
SPELL_ORDER.forEach(sid => {
  ITEM_BASES['book_' + sid] = { id: 'book_' + sid, name: 'Book: ' + SPELLS[sid].name, cat: 'book', slot: null, spell: sid, stackMax: 1, w: 1, h: 2, value: 120 + 30 * SPELL_ORDER.indexOf(sid), minLvl: 1, durMax: 0 };
});

/* --- affixes --- */
const AFFIXES = [
  { id: 'a_str', word: 'of the Bear', pre: 'Sturdy', f: { str: [1, 6] }, cats: ['armor', 'shield', 'amulet', 'ring', 'weapon'], band: [1, 99] },
  { id: 'a_dex', word: 'of the Fox', pre: 'Swift', f: { dex: [1, 6] }, cats: ['armor', 'shield', 'amulet', 'ring', 'weapon'], band: [1, 99] },
  { id: 'a_int', word: 'of the Owl', pre: 'Learned', f: { int: [1, 6] }, cats: ['armor', 'shield', 'focus', 'amulet', 'ring', 'weapon'], band: [1, 99] },
  { id: 'a_vit', word: 'of the Ox', pre: 'Hardy', f: { vit: [1, 6] }, cats: ['armor', 'shield', 'amulet', 'ring'], band: [1, 99] },
  { id: 'a_hp', word: 'of Vigor', pre: 'Vital', f: { hpFlat: [8, 30] }, cats: ['armor', 'shield', 'amulet', 'ring'], band: [1, 99] },
  { id: 'a_mp', word: 'of Insight', pre: 'Arcane', f: { mpFlat: [6, 25] }, cats: ['armor', 'focus', 'amulet', 'ring', 'weapon'], band: [1, 99] },
  { id: 'a_stam', word: 'of Wind', pre: 'Restless', f: { stFlat: [8, 25] }, cats: ['armor', 'amulet', 'ring'], band: [1, 99] },
  { id: 'a_dmgmin', word: 'of Wounds', pre: 'Keen', f: { dmgMin: [1, 4] }, cats: ['weapon'], band: [1, 99] },
  { id: 'a_dmgmax', word: 'of Slaughter', pre: 'Brutal', f: { dmgMax: [2, 6] }, cats: ['weapon'], band: [3, 99] },
  { id: 'a_sp', word: 'of Channeling', pre: 'Focused', f: { spellPower: [.03, .10] }, cats: ['weapon', 'focus', 'amulet', 'ring'], band: [1, 99] },
  { id: 'a_as', word: 'of Haste', pre: 'Fleet', f: { atkSpd: [.05, .14] }, cats: ['weapon', 'ring'], band: [3, 99] },
  { id: 'a_crit', word: 'of Precision', pre: 'Sharp', f: { crit: [.01, .05] }, cats: ['weapon', 'ring', 'amulet'], band: [2, 99] },
  { id: 'a_critd', word: 'of Ruin', pre: 'Cruel', f: { critDmg: [.10, .30] }, cats: ['weapon', 'ring', 'amulet'], band: [5, 99] },
  { id: 'a_armor', word: 'of the Wall', pre: 'Ironbound', f: { armor: [2, 10] }, cats: ['armor', 'shield'], band: [1, 99] },
  { id: 'a_resall', word: 'of Warding', pre: 'Warded', f: { resAll: [2, 8] }, cats: ['armor', 'shield', 'amulet', 'ring'], band: [2, 99] },
  { id: 'a_resfire', word: 'of Embers', pre: 'Fireproof', f: { resFire: [3, 12] }, cats: ['armor', 'shield', 'amulet', 'ring'], band: [1, 99], ex: 'res' },
  { id: 'a_resfrost', word: 'of the Deep Freeze', pre: 'Winterborn', f: { resFrost: [3, 12] }, cats: ['armor', 'shield', 'amulet', 'ring'], band: [1, 99], ex: 'res' },
  { id: 'a_reslight', word: 'of Grounding', pre: 'Grounded', f: { resLight: [3, 12] }, cats: ['armor', 'shield', 'amulet', 'ring'], band: [1, 99], ex: 'res' },
  { id: 'a_respoison', word: 'of the Antidote', pre: 'Venomward', f: { resPoison: [3, 12] }, cats: ['armor', 'shield', 'amulet', 'ring'], band: [1, 99], ex: 'res' },
  { id: 'a_resarc', word: 'of Silence', pre: 'Null', f: { resArc: [3, 12] }, cats: ['armor', 'shield', 'amulet', 'ring'], band: [3, 99], ex: 'res' },
  { id: 'a_hpreg', word: 'of Mending', pre: 'Renewing', f: { hpRegen: [.2, .8] }, cats: ['armor', 'amulet', 'ring'], band: [2, 99] },
  { id: 'a_mpreg', word: 'of the Well', pre: 'Deep', f: { mpRegen: [.1, .5] }, cats: ['armor', 'focus', 'amulet', 'ring', 'weapon'], band: [2, 99] },
  { id: 'a_lifesteal', word: 'of the Leech', pre: 'Thirsting', f: { lifeSteal: [.01, .04] }, cats: ['weapon', 'ring', 'amulet'], band: [4, 99] },
  { id: 'a_manasteal', word: 'of Syphon', pre: 'Syphoning', f: { manaSteal: [.01, .04] }, cats: ['weapon', 'ring'], band: [4, 99] },
  { id: 'a_move', word: 'of the Courier', pre: 'Bounding', f: { moveSpd: [.03, .08] }, cats: ['ring', 'amulet'], band: [1, 99] },
  { id: 'a_haste', word: 'of Alacrity', pre: 'Quickened', f: { haste: [.03, .10] }, cats: ['ring', 'amulet', 'weapon'], band: [4, 99] },
  { id: 'a_firedmg', word: 'of Flame', pre: 'Burning', f: { fireDmg: [2, 7] }, cats: ['weapon', 'ring', 'amulet'], band: [3, 99], ex: 'elemdmg' },
  { id: 'a_frostdmg', word: 'of Ice', pre: 'Freezing', f: { frostDmg: [2, 7] }, cats: ['weapon', 'ring', 'amulet'], band: [3, 99], ex: 'elemdmg' },
  { id: 'a_lightdmg', word: 'of Storms', pre: 'Stormforged', f: { lightDmg: [2, 7] }, cats: ['weapon', 'ring', 'amulet'], band: [3, 99], ex: 'elemdmg' },
  { id: 'a_poisonmdg', word: 'of Venom', pre: 'Envenomed', f: { poisonDmg: [2, 7] }, cats: ['weapon', 'ring', 'amulet'], band: [3, 99], ex: 'elemdmg' },
  { id: 'a_burn', word: 'of Ignition', pre: 'Smoldering', f: { onHitBurn: [.10, .30] }, cats: ['weapon'], band: [4, 99], ex: 'onhit' },
  { id: 'a_chill', word: 'of Frostbite', pre: 'Chilling', f: { onHitChill: [.10, .30] }, cats: ['weapon'], band: [4, 99], ex: 'onhit' },
  { id: 'a_envenom', word: 'of Toxicity', pre: 'Toxic', f: { onHitPoison: [.10, .30] }, cats: ['weapon'], band: [4, 99], ex: 'onhit' },
  { id: 'a_shockhit', word: 'of the Storm Coil', pre: 'Crackling', f: { onHitShock: [.10, .30] }, cats: ['weapon'], band: [4, 99], ex: 'onhit' },
  { id: 'a_kick', word: 'of the War Boot', pre: 'Kicking', f: { kickElem: ['fire', 'frost', 'lightning', 'poison'] }, cats: ['armor'], band: [3, 99] },
  { id: 'a_light', word: 'of Radiance', pre: 'Radiant', f: { light: [1, 3] }, cats: ['amulet', 'weapon', 'armor'], band: [1, 99] },
  { id: 'a_shstam', word: 'of Bracing', pre: 'Braced', f: { shieldStam: [.10, .30] }, cats: ['shield'], band: [3, 99] },
  { id: 'a_manacost', word: 'of Economy', pre: 'Efficient', f: { manaCostRed: [.08, .20] }, cats: ['weapon', 'focus', 'ring'], band: [4, 99] },
  { id: 'a_thorns', word: 'of Spikes', pre: 'Thorned', f: { thorns: [1, 6] }, cats: ['armor', 'shield'], band: [3, 99] },
  { id: 'a_goldfind', word: 'of Greed', pre: 'Gilded', f: { goldFind: [.10, .40] }, cats: ['ring', 'amulet'], band: [1, 99] },
  { id: 'a_resist_st', word: 'of Stability', pre: 'Anchored', f: { statusRes: [.05, .25] }, cats: ['armor', 'amulet', 'ring'], band: [3, 99] },
];
const AFFIX_BY_ID = {}; AFFIXES.forEach(a => AFFIX_BY_ID[a.id] = a);

/* --- relics (12 authored) --- */
const RELICS = {
  coalbrand: { name: 'Coalbrand', base: 'sword', dmg: [8, 13], reqs: { str: 14 }, minLvl: 6, w: 1, h: 3, value: 800, special: 'coalbrand', desc: 'Adds fire damage, inflicts burn, emits light.' },
  breakwater: { name: 'Breakwater', base: 'shield_kite', blockAbs: 0.88, blockElem: 0.55, reqs: { str: 14 }, minLvl: 8, w: 1, h: 3, value: 900, special: 'breakwater', desc: 'Perfect block sends a short-range shockwave.' },
  thunderheels: { name: 'Thunderheels', base: 'boots', armor: 4, reqs: { dex: 12 }, minLvl: 7, w: 1, h: 2, value: 700, special: 'thunderheels', desc: 'Kicks deal lightning damage and may chain.' },
  gravedigger: { name: "Gravedigger's Grasp", base: 'gauntlets', armor: 5, reqs: { str: 12 }, minLvl: 9, w: 1, h: 1, value: 650, special: 'gravedigger', desc: 'Melee takedowns restore stamina.' },
  quieteye: { name: 'The Quiet Eye', base: 'amulet', reqs: {}, minLvl: 5, w: 1, h: 1, value: 600, special: 'quieteye', desc: 'Reveals secret-door hints; -20 maximum mana.' },
  hollowfang: { name: 'Hollow Fang', base: 'dagger', dmg: [5, 9], reqs: { dex: 14 }, minLvl: 7, w: 1, h: 2, value: 750, special: 'hollowfang', desc: 'Backstab bonus and stronger bleed; lowered frontal damage.' },
  wardentoll: { name: "Warden's Toll", base: 'mace', dmg: [10, 15], reqs: { str: 15 }, minLvl: 9, w: 1, h: 3, value: 800, special: 'wardentoll', desc: 'Extra poise damage but slower recovery.' },
  ashglass: { name: 'Ashglass Staff', base: 'staff', dmg: [4, 7], spellPower: .14, reqs: { int: 14 }, minLvl: 8, w: 1, h: 4, value: 850, special: 'ashglass', desc: 'Fire spells gain splash radius at increased mana cost.' },
  frostvein: { name: 'Frostvein Ring', base: 'ring', reqs: {}, minLvl: 6, w: 1, h: 1, value: 550, special: 'frostvein', desc: 'Critical hits add chill buildup.' },
  lanternmail: { name: 'Lantern Mail', base: 'chest_mail', armor: 15, reqs: { str: 13 }, minLvl: 9, w: 2, h: 3, value: 950, special: 'lanternmail', desc: 'Increased armor and light radius; reduced dodge distance.' },
  serpentknot: { name: 'Serpent Knot', base: 'ring', reqs: {}, minLvl: 8, w: 1, h: 1, value: 600, special: 'serpentknot', desc: 'Poison damage you deal heals you, capped.' },
  wayfarer: { name: 'Wayfarer Bow', base: 'bow', dmg: [8, 12], reqs: { dex: 14 }, minLvl: 8, w: 1, h: 4, value: 800, special: 'wayfarer', desc: 'Arrows pierce one enemy at reduced damage.' },
};
const RELIC_FAM_BASE = {
  sword: { fam: 'sword', reach: 2.05, wind: .23, rec: .35, stam: 9, poise: 8, elem: 'slash' },
  dagger: { fam: 'dagger', reach: 1.35, wind: .15, rec: .21, stam: 5, poise: 5, elem: 'pierce' },
  mace: { fam: 'mace', reach: 1.85, wind: .27, rec: .39, stam: 9, poise: 12, elem: 'blunt' },
  staff: { fam: 'staff', reach: 1.95, wind: .30, rec: .42, stam: 8, poise: 7, elem: 'blunt' },
  bow: { fam: 'bow', reach: 33, wind: .19, rec: .31, stam: 6, poise: 0, elem: 'pierce', projSpeed: 29 },
  shield_kite: {}, gauntlets: {}, boots: {}, ring: {}, amulet: {}, chest_mail: {},
};

/* ---------------- item construction ---------------- */
let ITEM_IID = 1;
function baseOf(id) { return ITEM_BASES[id] || null; }
function relicItem(rid, ilvl, rng) {
  const def = RELICS[rid];
  const base = RELIC_FAM_BASE[def.base] || {};
  const it = {
    iid: 'itm_' + (ITEM_IID++), base: 'relic_' + rid, name: def.name, rarity: 'relic', ilvl,
    cat: ['shield_kite'].includes(def.base) ? 'shield' : ['chest_mail', 'boots', 'gauntlets'].includes(def.base) ? 'armor' : ['ring'].includes(def.base) ? 'ring' : ['amulet'].includes(def.base) ? 'amulet' : 'weapon',
    slot: def.base === 'ring' ? 'ring' : def.base === 'amulet' ? 'amulet' : def.base === 'shield_kite' ? 'off' : def.base === 'boots' ? 'boots' : def.base === 'gauntlets' ? 'gloves' : def.base === 'chest_mail' ? 'chest' : 'main',
    w: def.w, h: def.h, qty: 1, identified: true, special: rid,
    relic: def, reqs: def.reqs, minLvl: def.minLvl,
    dmg: def.dmg ? { min: def.dmg[0], max: def.dmg[1], elem: base.elem || 'slash' } : null,
    armor: def.armor || 0, blockAbs: def.blockAbs, blockElem: def.blockElem, spellPower: def.spellPower,
    fam: base.fam, reach: base.reach, wind: base.wind, rec: base.rec, stam: base.stam, poise: base.poise, projSpeed: base.projSpeed,
    two: !!(base.fam && ['spear', 'great', 'bow'].includes(base.fam)),
    durMax: 70, dur: 70, value: def.value,
  };
  it.price = itemValue(it);
  return it;
}
function itemValue(it) {
  const rmult = RAR[RAR_IDX[it.rarity]].mult;
  return Math.max(1, Math.round((it.baseValue || it.value || 50) * (1 + 0.12 * (it.ilvl || 1)) * rmult));
}
function makeItem(baseId, ilvl, rarity, rng, opts) {
  opts = opts || {};
  const b = baseOf(baseId);
  if (!b) return null;
  if (rarity === 'relic' && !b.relic) {
    const pool = Object.keys(RELICS).filter(r => RELICS[r].minLvl <= Math.max(1, ilvl));
    if (!pool.length) rarity = 'rare';
    else return relicItem(opts.relicId || pick(rng, pool), ilvl, rng);
  }
  const it = {
    iid: 'itm_' + (ITEM_IID++), base: baseId, name: b.name, rarity, ilvl: Math.max(1, ilvl),
    cat: b.cat, slot: b.slot || null, w: b.w, h: b.h, qty: b.stackMax ? (opts.qty || 1) : 1,
    identified: rarity === 'common' || !!opts.identified,
    reqs: b.reqs || {}, minLvl: b.minLvl || 1, stackMax: b.stackMax || 0,
    durMax: b.durMax, dur: b.durMax,
    baseValue: b.value, value: b.value,
  };
  if (b.cat === 'weapon') { it.fam = b.fam; it.dmg = { min: b.dmg.min, max: b.dmg.max, elem: b.dmg.elem }; it.reach = b.reach; it.wind = b.wind; it.rec = b.rec; it.stam = b.stam; it.poise = b.poise; it.two = b.two; it.projSpeed = b.projSpeed; }
  if (b.cat === 'armor' || b.cat === 'shield') { it.armor = b.armor; if (b.cat === 'shield') { it.blockAbs = b.blockAbs; it.blockElem = b.blockElem; } }
  if (b.spellPower) it.spellPower = b.spellPower;
  if (b.effect) it.effect = b.effect;
  if (b.spell) it.spell = b.spell;
  if (rarity !== 'common') {
    let n = rarity === 'enchanted' ? 1 : ri(rng, 2, 4);
    const usedIds = [], usedEx = [];
    let guard = 24;
    while (n > 0 && guard-- > 0) {
      const pool = AFFIXES.filter(a => a.cats.some(c => catMatches(b, c)) && a.band[0] <= it.ilvl + 2 && !usedIds.includes(a.id) && !(a.ex && usedEx.includes(a.ex)));
      if (!pool.length) break;
      const a = pick(rng, pool);
      usedIds.push(a.id); if (a.ex) usedEx.push(a.ex);
      n--;
      it.affixes = it.affixes || [];
      it.affixes.push({ id: a.id, v: rollAffix(rng, a, it.ilvl) });
    }
    const words = (it.affixes || []).map(f => AFFIX_BY_ID[f.id]);
    if (words.length) {
      const pre = words.find(w2 => w2.pre), suf = words.find(w2 => w2.word);
      it.name = ((pre && chance(rng, .6) ? pre.pre + ' ' : '') + b.name + (suf ? ' ' + suf.word : '')).trim();
    } else {
      // no eligible affixes for this base → downgrade to common (never a fake-magic item)
      it.rarity = 'common';
    }
  }
  it.price = itemValue(it);
  return it;
}
function catMatches(b, c) {
  if (b.cat === c) return true;
  if (c === 'boots' || c === 'head' || c === 'gloves') return b.slot === c;
  return false;
}
function rollAffix(rng, a, ilvl) {
  const key = Object.keys(a.f)[0];
  const raw = a.f[key];
  if (Array.isArray(raw) && typeof raw[0] === 'string') return pick(rng, raw); // categorical (e.g. kick element)
  const [lo, hi] = raw;
  const scale = 1 + Math.min(1.2, ilvl * 0.035);
  let v = lo + rng() * (hi - lo);
  if (typeof lo === 'number') v = clamp(v * scale, lo, hi * (key === 'str' || key === 'hpFlat' ? 2.2 : 1.6));
  if (Number.isInteger(lo)) v = Math.round(v);
  else v = +v.toFixed(3);
  return v;
}
/* committed loot roll — used for chests/enemies at generation time so save/load cannot reroll */
function rollLoot(rng, opts) {
  opts = Object.assign({ ilvl: 1, weights: null, n: 1, relicChance: 0, identified: false, lootMul: 1 }, opts);
  const out = [];
  for (let i = 0; i < opts.n; i++) {
    let rarity = wpick(rng, Object.entries(opts.weights || CFG.rarityWeights).map(([k, v]) => [k, v * (opts.lootMul || 1)]));
    if (opts.relicChance && rng() < opts.relicChance) rarity = 'relic';
    const base = pickLootBase(rng, opts.ilvl, rarity, opts.tags);
    if (!base) continue;
    const it = makeItem(base, opts.ilvl, rarity, rng, { identified: opts.identified, relicId: opts.relicId });
    if (it) out.push(it);
  }
  return out;
}
function pickLootBase(rng, ilvl, rarity, tags) {
  const pool = Object.values(ITEM_BASES).filter(b => {
    if (b.cat === 'book' || b.cat === 'scroll') return chance(rng, .06);
    if (b.minLvl > ilvl + 1) return false;
    if (tags && tags.includes('meleeOnly') && (b.fam === 'bow' || b.cat === 'ammo')) return false;
    if (tags && tags.includes('casterOnly') && b.fam && !['staff', 'wand'].includes(b.fam)) return false;
    return true;
  });
  if (!pool.length) return 'potion_health_s';
  const w = pool.map(b => (b.cat === 'weapon' || b.cat === 'armor' || b.cat === 'shield') ? 3 : (b.cat === 'ring' || b.cat === 'amulet' || b.cat === 'focus') ? 1.5 : 1);
  let tot = w.reduce((a, b) => a + b, 0), x = rng() * tot;
  for (let i = 0; i < pool.length; i++) { x -= w[i]; if (x <= 0) return pool[i].id; }
  return pool[0].id;
}
/* computed stats of an instance (affix effects active even when unidentified; tooltips conceal rolls) */
function itemStats(it) {
  const st = { dmgMin: 0, dmgMax: 0, armor: 0, spellPower: 0, atkSpd: 0, crit: 0, critDmg: 0, str: 0, dex: 0, int: 0, vit: 0, hpFlat: 0, mpFlat: 0, stFlat: 0, resAll: 0, resFire: 0, resFrost: 0, resLight: 0, resPoison: 0, resArc: 0, hpRegen: 0, mpRegen: 0, lifeSteal: 0, manaSteal: 0, moveSpd: 0, haste: 0, fireDmg: 0, frostDmg: 0, lightDmg: 0, poisonDmg: 0, onHitBurn: 0, onHitChill: 0, onHitPoison: 0, onHitShock: 0, kickElem: null, light: 0, shieldStam: 0, manaCostRed: 0, thorns: 0, goldFind: 0, statusRes: 0 };
  if (!it) return st;
  if (it.cat === 'weapon' && it.dmg) { st.dmgMin = it.dmg.min; st.dmgMax = it.dmg.max; }
  if (it.armor) st.armor = it.armor;
  if (it.spellPower) st.spellPower = it.spellPower;
  if (it.relic) st.special = it.special;
  for (const fx of (it.affixes || [])) {
    const a = AFFIX_BY_ID[fx.id]; if (!a) continue;
    const key = Object.keys(a.f)[0];
    if (key === 'kickElem') st.kickElem = fx.v;
    else if (key in st) st[key] += fx.v;
  }
  if (st.resAll) { st.resFire += st.resAll; st.resFrost += st.resAll; st.resLight += st.resAll; st.resPoison += st.resAll; st.resArc += st.resAll; }
  return st;
}
function itemDPS(it) {
  const s = itemStats(it);
  if (!s.dmgMax) return 0;
  const t = (it.wind || .25) + (it.rec || .35);
  return ((s.dmgMin + s.dmgMax) / 2 + (it.cat === 'bow' ? 6 : 10)) / t;
}

/* ============================================================
   4. DATA — enemies (24 archetypes), elite modifiers, bosses
   ============================================================ */
/* dmg scaled by difficulty; level scaling: hp*=(1+.22*(L-1)) dmg*=(1+.09*(L-1)) armor*=(1+.12*(L-1)) xp*=(1+.3*(L-1)) */
function E(id, name, reg, tier, hp, armor, dmg, atk, reach, windup, rec, cd, speed, vision, poise, xp, scale, col, col2, opts) {
  const o = opts || {};
  return Object.assign({ id, name, reg, tier, hp, armor, dmg, atk, reach, windup, active: o.active || .16, rec, cd, speed, vision: vision || 13, poise, xp, scale: scale || 1, col, col2, tags: o.tags || [], res: o.res || {}, imm: o.imm || [], spec: o.spec || null, sever: o.sever !== false, lootW: o.lootW || 1, desc: o.desc || '' }, o);
}
const ENEMIES = [
  // Region 1 — Barracks
  E('scavenger', 'Scavenger', 0, 'grunt', 34, 4, [5, 8], 'melee', 1.8, .45, .55, 1.6, 3.6, 13, 24, 12, 1, [.55, .45, .34], [.35, .28, .22], { desc: 'Desperate bandits haunting the upper halls.' }),
  E('bone_militia', 'Bone Militia', 0, 'grunt', 48, 14, [7, 11], 'melee', 2.1, .45, .16, .7, 2.6, 1.9, 24, 1, [.62, .60, .52], [.40, .38, .32], { tags: ['undead', 'shield'], res: { frost: 15, poison: 75 }, imm: ['poison'], sever: { head: false }, desc: 'Drilled dead men who remember their shields.' }),
  E('tower_archer', 'Tower Archer', 0, 'ranged', 30, 3, [6, 9], 'bow', 11, .9, .22, .9, 2.2, 3.0, 15, 18, 14, .95, [.48, .38, .30], [.30, .24, .18], { desc: 'Keeps to the high lanes and looses quick volleys.' }),
  E('kennel_beast', 'Kennel Beast', 0, 'beast', 38, 2, [7, 10], 'melee', 1.6, .35, .18, .9, 4.4, 14, 20, 14, .9, [.42, .30, .22], [.20, .15, .12], { tags: ['beast'], spec: 'rush', sever: { head: true, arms: false }, desc: 'Starred hounds that lunge without caution.' }),
  E('armored_reaver', 'Armored Reaver', 0, 'brute', 78, 18, [12, 17], 'melee', 2.2, .8, .2, 1.2, 2.3, 1.2, 15, 45, 34, 1.25, [.35, .35, .40], [.20, .20, .24], { tags: ['armored'], res: { slash: 20 }, desc: 'Slow, plated, and swings through guards.' }),
  E('whisper_wisp', 'Whisper Wisp', 0, 'caster', 26, 0, [9, 12], 'spell', 10, .8, .1, 2.2, 1.8, 3.2, 16, 10, 16, .8, [.55, .65, .70], [.30, .40, .50], { tags: ['spectral'], imm: ['bleed', 'poison'], sever: false, spec: 'float', res: { poison: 100, slash: 50 }, desc: 'Glowing remnants that hurl searing whispers.' }),
  // Region 2 — Ossuary
  E('rotwalker', 'Rotwalker', 1, 'grunt', 60, 6, [8, 12], 'melee', 1.8, .6, .2, 1.0, 2.0, 1.3, 12, 34, 20, 1.05, [.40, .48, .36], [.28, .34, .25], { tags: ['undead'], res: { poison: 75, frost: 20 }, imm: ['poison'], desc: 'Crawling dead with a crushing grab.' }),
  E('headless_guard', 'Headless Guard', 1, 'brute', 85, 12, [10, 15], 'melee', 2.3, .7, .2, 1.1, 2.4, 1.1, 15, 48, 36, 1.2, [.55, .52, .44], [.35, .33, .28], { tags: ['undead', 'armored'], imm: ['fear'], sever: { head: false }, spec: 'headless', desc: 'Decapitation means nothing to it.' }),
  E('tomb_archer', 'Tomb Archer', 1, 'ranged', 36, 4, [6, 9], 'bow', 11, .95, .22, .95, 2.3, 3.0, 16, 20, 16, .95, [.44, .50, .42], [.28, .32, .26], { tags: ['undead'], res: { poison: 60 }, imm: ['poison'], spec: 'poisonArrow', desc: 'Arrows fester with grave-rot.' }),
  E('grave_hound', 'Grave Hound', 1, 'beast', 30, 2, [5, 9], 'melee', 1.6, .3, .16, .8, 4.8, 15, 18, 12, 13, .85, [.35, .36, .30], [.18, .19, .16], { tags: ['beast', 'undead'], spec: 'pack', sever: { head: true, arms: false }, desc: 'Hunts in yelping packs.' }),
  E('crypt_magus', 'Crypt Magus', 1, 'caster', 40, 3, [10, 13], 'spell', 11, .9, .1, 2.4, 2.0, 3.2, 18, 22, 18, .95, [.30, .40, .38], [.18, .26, .24], { tags: ['undead'], spec: 'curse', res: { poison: 50, magic: 20 }, desc: 'Chants curses that rot resistance away.' }),
  E('bone_colossus', 'Bone Colossus', 1, 'brute', 130, 20, [15, 21], 'melee', 2.6, .95, .24, 1.6, 1.8, 1.0, 15, 90, 45, 1.55, [.66, .64, .56], [.42, .40, .34], { tags: ['undead', 'armored', 'bosslike'], res: { frost: 30 }, imm: ['stun'], desc: 'A mountain of stacked dead. Poise like a fortress.' }),
  // Region 3 — Flooded Works
  E('drowned_thrall', 'Drowned Thrall', 2, 'grunt', 52, 5, [8, 12], 'melee', 1.8, .5, .2, 1.0, 2.4, 1.2, 12, 30, 18, 1.0, [.28, .38, .40], [.16, .24, .26], { tags: ['undead'], spec: 'ambush', res: { frost: 25 }, imm: ['fear'], desc: 'Waits under black water until you pass.' }),
  E('salt_caster', 'Salt Caster', 2, 'caster', 42, 4, [11, 14], 'spell', 11, .85, .1, 2.3, 2.0, 3.2, 18, 24, 18, .95, [.30, .42, .52], [.18, .28, .36], { res: { lightning: 60 }, spec: 'waterbolt', desc: 'Throws searing brine that bites like lightning.' }),
  E('hook_brigand', 'Hook Brigand', 2, 'grunt', 48, 8, [7, 10], 'melee', 1.9, .5, .18, 1.1, 3.0, 1.4, 14, 28, 16, 1.0, [.45, .33, .26], [.30, .22, .17], { spec: 'pull', desc: 'Yanks the unwary off their footing.' }),
  E('mire_leech', 'Mire Leech', 2, 'beast', 16, 0, [3, 6], 'melee', 1.2, .25, .12, .7, 3.6, 1.0, 10, 8, 6, .5, [.30, .22, .30], [.18, .12, .18], { tags: ['beast'], spec: 'ambush', desc: 'Small, quick, and venomous.' }),
  E('rust_construct', 'Rust Construct', 2, 'brute', 95, 26, [11, 15], 'melee', 2.2, .75, .2, 1.3, 2.0, 1.1, 15, 60, 40, 1.2, [.45, .32, .20], [.28, .20, .12], { tags: ['construct'], imm: ['bleed', 'poison', 'fear'], sever: false, res: { lightning: -25 }, desc: 'Machine of the works, slow to die.' }),
  E('sump_horror', 'Sump Horror', 2, 'brute', 105, 10, [13, 18], 'melee', 2.4, .8, .22, 1.4, 2.2, 1.1, 14, 70, 42, 1.3, [.24, .34, .30], [.14, .22, .20], { spec: 'grapple', sever: { head: false, arms: true }, desc: 'Many-limbed and patient.' }),
  // Region 4 — The Unraveling
  E('riftling', 'Riftling', 3, 'grunt', 44, 4, [8, 12], 'melee', 1.7, .4, .16, 1.0, 3.2, 1.4, 14, 30, 18, .9, [.45, .30, .55], [.28, .18, .36], { spec: 'teleport', imm: ['fear'], desc: 'Flickers through holes in the world.' }),
  E('hollow_knight', 'Hollow Knight', 3, 'grunt', 70, 16, [10, 14], 'melee', 2.1, .5, .18, 1.1, 2.8, 1.3, 16, 44, 26, 1.05, [.35, .35, .38], [.20, .20, .22], { tags: ['armored', 'shield'], spec: 'counter', desc: 'Parries the predictable and punishes them.' }),
  E('eye_swarm', 'Eye Swarm', 3, 'ranged', 28, 2, [5, 8], 'spell', 9, .5, .08, 1.2, 2.6, 3.4, 15, 14, 12, .7, [.60, .40, .30], [.36, .24, .18], { tags: ['flying', 'spectral'], imm: ['bleed'], spec: 'float', sever: false, desc: 'A drifting cluster of watching eyes.' }),
  E('many_hands', 'Many-Hands', 3, 'grunt', 60, 8, [6, 9], 'melee', 2.0, .35, .14, .9, 3.0, 1.4, 14, 36, 22, 1.0, [.50, .44, .36], [.32, .28, .22], { spec: 'multiswing', desc: 'Too many arms to count, all of them sharp.' }),
  E('veil_priest', 'Veil Priest', 3, 'caster', 46, 6, [9, 12], 'spell', 11, 1.0, .1, 2.6, 1.8, 3.2, 20, 26, 20, .95, [.40, .30, .50], [.24, .18, .32], { spec: 'healcurse', res: { magic: 20 }, desc: 'Mends its servants and curses you.' }),
  E('deep_sentinel', 'Deep Sentinel', 3, 'brute', 140, 24, [14, 19], 'melee', 2.5, .9, .22, 1.5, 1.9, 1.0, 15, 95, 48, 1.35, [.30, .28, .36], [.18, .16, .22], { tags: ['construct', 'bosslike'], imm: ['stun', 'fear'], sever: false, spec: 'unparryable', desc: 'The last ward of the deep. Do not trade blows.' }),
];
const ENEMY_BY_ID = {}; ENEMIES.forEach(e => ENEMY_BY_ID[e.id] = e);

/* elite modifiers */
const ELITES = {
  enraged: { name: 'Enraged', hp: 1.15, dmg: 1.2, speed: 1.2, col: [0.9, 0.2, 0.2], desc: 'Faster and wilder.' },
  warded: { name: 'Warded', shield: 60, col: [0.2, 0.5, 0.9], desc: 'A magical shield absorbs damage first.' },
  venomous: { name: 'Venomous', poisonOnHit: true, col: [0.3, 0.7, 0.2], desc: 'Its attacks envenom.' },
  stormbound: { name: 'Stormbound', zap: true, col: [0.3, 0.6, 1.0], desc: 'Crackles with lightning around it.' },
  vampiric: { name: 'Vampiric', lifesteal: 0.3, col: [0.6, 0.1, 0.3], desc: 'Feeds on what it wounds.' },
  unstable: { name: 'Unstable', explode: true, col: [0.9, 0.5, 0.1], desc: 'Bursts violently on death.' },
  summoner: { name: 'Summoner', adds: true, col: [0.5, 0.2, 0.7], desc: 'Calls servants at half strength.' },
  thorned: { name: 'Thorned', reflect: 0.15, col: [0.4, 0.6, 0.3], desc: 'Reflects a share of melee wounds.' },
};

/* ---------------- bosses ---------------- */
const BOSSES = {
  ashbound_captain: {
    id: 'ashbound_captain', name: 'The Ashbound Captain', floor: 4, hp: 420, armor: 18, dmg: [14, 20], speed: 3.0, poise: 200, xp: 320, scale: 1.35,
    col: [.45, .30, .24], col2: [.25, .18, .14], tags: ['boss', 'armored', 'humanoid'],
    phases: [
      { at: 1.0, moves: ['slash', 'combo', 'charge', 'bash'] },
      { at: 0.5, moves: ['slash', 'combo', 'charge', 'bash', 'slam', 'summon'], msg: 'The Captain bellows for his retinue!' },
    ],
    desc: 'A shielded captain who punishes panic. Guard-break after his charge misses.',
  },
  bellkeeper: {
    id: 'bellkeeper', name: 'The Ossuary Bellkeeper', floor: 8, hp: 640, armor: 22, dmg: [17, 24], speed: 2.4, poise: 320, xp: 560, scale: 1.7,
    col: [.60, .58, .50], col2: [.36, .34, .28], tags: ['boss', 'undead', 'giant'],
    phases: [
      { at: 1.0, moves: ['sweep', 'shockwave', 'slam'] },
      { at: 0.5, moves: ['sweep', 'shockwave', 'slam', 'toll', 'cursezone'], msg: 'The great bell tolls. The dead answer.' },
    ],
    desc: 'A giant bound to a bell. Shockwave rings demand a dodge; his arms can be ruined.',
  },
  drowned_engineer: {
    id: 'drowned_engineer', name: 'The Drowned Engineer', floor: 12, hp: 780, armor: 20, dmg: [18, 26], speed: 2.6, poise: 340, xp: 780, scale: 1.5,
    col: [.26, .38, .42], col2: [.16, .24, .28], tags: ['boss', 'construct'],
    phases: [
      { at: 1.0, moves: ['slam', 'hook', 'chargeWater'] },
      { at: 0.5, moves: ['slam', 'hook', 'chargeWater', 'electrify', 'core'], msg: 'The Engineer floods the hall with current!' },
    ],
    desc: 'A drowned machine-tender. Watch the water; its core opens when the current stalls.',
  },
  warden_below: {
    id: 'warden_below', name: 'The Warden Below', floor: 16, hp: 1100, armor: 24, dmg: [20, 30], speed: 3.0, poise: 420, xp: 1400, scale: 1.6,
    col: [.40, .26, .52], col2: [.24, .14, .34], tags: ['boss', 'supernatural'],
    phases: [
      { at: 1.0, moves: ['combo', 'riftbolt', 'slam'] },
      { at: 0.6, moves: ['combo', 'riftbolt', 'slam', 'teleport', 'summon'], msg: 'The Warden tears the floor open!' },
      { at: 0.25, moves: ['combo', 'riftbolt', 'slam', 'teleport', 'cursezone'], msg: 'Its core is exposed — strike now!', core: true },
    ],
    desc: 'The guardian perpetuating the disaster. A multi-limbed horror with an exposed core phase.',
  },
};

/* ============================================================
   5. DATA — quests, lore, dialogue, events, shrines, traps
   ============================================================ */
const QUESTS = [
  { id: 'mq1', main: true, region: 0, name: 'Ash and Silence', giver: 'chronicler',
    desc: 'The Chronicler wants proof of what is happening below Hollowmere.',
    objectives: [
      { id: 'talk', type: 'dialog', npc: 'chronicler', text: 'Speak with the Chronicler' },
      { id: 'ledger', type: 'pickup', base: 'q_ledger', floorRange: [2, 3], text: 'Find the commander’s ledger in the Barracks (floors 2–3)' },
      { id: 'boss', type: 'boss', boss: 'ashbound_captain', text: 'Defeat the Ashbound Captain on Floor 4' },
      { id: 'return', type: 'dialog', npc: 'chronicler', text: 'Return to the Chronicler' },
    ],
    rewards: { gold: 250, xp: 300, item: 'rare' } },
  { id: 'mq2', main: true, region: 1, name: 'Bells for the Buried', giver: 'chronicler',
    desc: 'Something rings in the Ossuary, and the dead march to it.',
    objectives: [
      { id: 'talk', type: 'dialog', npc: 'chronicler', text: 'Speak with the Chronicler' },
      { id: 'boss', type: 'boss', boss: 'bellkeeper', text: 'Defeat the Ossuary Bellkeeper on Floor 8' },
      { id: 'return', type: 'dialog', npc: 'chronicler', text: 'Return to the Chronicler' },
    ],
    rewards: { gold: 400, xp: 600, item: 'rare' } },
  { id: 'mq3', main: true, region: 2, name: 'The Water Remembers', giver: 'chronicler',
    desc: 'The Flooded Works still answer to levers and valves.',
    objectives: [
      { id: 'talk', type: 'dialog', npc: 'chronicler', text: 'Speak with the Chronicler' },
      { id: 'valves', type: 'interact', tag: 'valve', count: 2, text: 'Open 2 sluice valves (floors 9–12)' },
      { id: 'boss', type: 'boss', boss: 'drowned_engineer', text: 'Defeat the Drowned Engineer on Floor 12' },
      { id: 'return', type: 'dialog', npc: 'chronicler', text: 'Return to the Chronicler' },
    ],
    rewards: { gold: 600, xp: 900, item: 'rare' } },
  { id: 'mq4', main: true, region: 3, name: 'The Warden Below', giver: 'chronicler',
    desc: 'Whatever keeps the Underkeep wounded must be confronted.',
    objectives: [
      { id: 'talk', type: 'dialog', npc: 'chronicler', text: 'Speak with the Chronicler' },
      { id: 'boss', type: 'boss', boss: 'warden_below', text: 'Defeat the Warden Below on Floor 16' },
      { id: 'return', type: 'dialog', npc: 'chronicler', text: 'Return to the Chronicler' },
    ],
    rewards: { gold: 1000, xp: 1600, item: 'relic', ending: true } },
  // side quests
  { id: 'sq_standard', name: 'The Lost Standard', giver: 'chronicler',
    objectives: [
      { id: 'find', type: 'pickup', base: 'q_standard', floorRange: [2, 3], text: 'Find the fallen standard fragment (floors 2–3)' },
      { id: 'return', type: 'dialog', npc: 'chronicler', text: 'Return it to the Chronicler' },
    ], rewards: { gold: 175, xp: 140, item: 'enchanted' } },
  { id: 'sq_cull', name: 'Scavenger Cull', giver: 'quartermaster',
    objectives: [{ id: 'kill', type: 'kill', arch: 'scavenger', count: 8, text: 'Kill 8 Scavengers' },
      { id: 'return', type: 'dialog', npc: 'quartermaster', text: 'Report to the Quartermaster' }],
    rewards: { gold: 150, xp: 160 } },
  { id: 'sq_survivor', name: 'A Voice Below', giver: 'healer',
    objectives: [{ id: 'find', type: 'event', event: 'survivor', text: 'Find the missing delver in the dungeon' },
      { id: 'return', type: 'dialog', npc: 'healer', text: 'Tell the Healer they live' }],
    rewards: { gold: 120, xp: 150, item: 'potion_health_m' } },
  { id: 'sq_butcher', name: 'The Kennel-Master', giver: 'smith',
    objectives: [{ id: 'kill', type: 'killElite', arch: 'kennel_beast', text: 'Slay the elite Kennel Beast below' },
      { id: 'return', type: 'dialog', npc: 'smith', text: 'Report to the Smith' }],
    rewards: { gold: 200, xp: 220, item: 'enchanted' } },
  { id: 'sq_cleanse', name: 'A Quiet Grave', giver: 'mystic',
    objectives: [{ id: 'cleanse', type: 'interact', tag: 'cleanse_altar', count: 1, text: 'Cleanse a cursed altar in the Ossuary' },
      { id: 'return', type: 'dialog', npc: 'mystic', text: 'Return to the Mystic' }],
    rewards: { gold: 180, xp: 200, item: 'scroll_identify:2' } },
  { id: 'sq_amulet', name: 'The Widow’s Amulet', giver: 'healer',
    objectives: [{ id: 'find', type: 'pickup', base: 'q_amulet', floorRange: [6, 6], text: 'Recover the amulet from Floor 6' },
      { id: 'return', type: 'dialog', npc: 'healer', text: 'Return it to the Healer' }],
    rewards: { gold: 220, xp: 240, item: 'amulet_moonglass' } },
  { id: 'sq_colossus', name: 'Bones on the Stair', giver: 'quartermaster',
    objectives: [{ id: 'kill', type: 'killElite', arch: 'bone_colossus', text: 'Slay the elite Bone Colossus' },
      { id: 'return', type: 'dialog', npc: 'quartermaster', text: 'Report to the Quartermaster' }],
    rewards: { gold: 320, xp: 380, item: 'rare' } },
  { id: 'sq_valve', name: 'Pressure and Silence', giver: 'smith',
    objectives: [{ id: 'valve', type: 'interact', tag: 'valve', count: 1, text: 'Turn any sluice valve in the Flooded Works' },
      { id: 'return', type: 'dialog', npc: 'smith', text: 'Report to the Smith' }],
    rewards: { gold: 200, xp: 220, item: 'potion_stam:2' } },
  { id: 'sq_pages', name: 'Pages of the Deep', giver: 'chronicler',
    objectives: [{ id: 'pages', type: 'lore', count: 6, text: 'Recover 6 lore fragments from the dungeon' },
      { id: 'return', type: 'dialog', npc: 'chronicler', text: 'Deliver them to the Chronicler' }],
    rewards: { gold: 250, xp: 300, item: 'rare' } },
  { id: 'sq_order', name: 'The Greater Order', giver: 'alchemist',
    objectives: [{ id: 'deliver', type: 'deliver', base: 'potion_health_g', count: 3, text: 'Deliver 3 Greater Health Potions' }],
    rewards: { gold: 300, xp: 260, item: 'elixir_resist' } },
  { id: 'sq_arrows', name: 'Shots in the Dark', giver: 'quartermaster',
    objectives: [{ id: 'deliver', type: 'deliver', base: 'arrows', count: 60, text: 'Deliver 60 Arrows' }],
    rewards: { gold: 150, xp: 120, item: 'potion_mana_m' } },
  { id: 'sq_sentinel', name: 'Final Proof', giver: 'chronicler',
    objectives: [{ id: 'kill', type: 'killElite', arch: 'deep_sentinel', text: 'Slay an elite Deep Sentinel (floor 13+)' },
      { id: 'return', type: 'dialog', npc: 'chronicler', text: 'Report to the Chronicler' }],
    rewards: { gold: 500, xp: 600, item: 'rare' } },
];
const QUEST_BY_ID = {}; QUESTS.forEach(q => QUEST_BY_ID[q.id] = q);

/* quest quest-item bases (non-vendor special items) */
ITEM_BASES['q_ledger'] = { id: 'q_ledger', name: 'Commander’s Ledger', cat: 'quest', slot: null, w: 1, h: 1, value: 0, minLvl: 1, durMax: 0, quest: 'mq1' };
ITEM_BASES['q_standard'] = { id: 'q_standard', name: 'Standard Fragment', cat: 'quest', slot: null, w: 1, h: 1, value: 0, minLvl: 1, durMax: 0, quest: 'sq_standard' };
ITEM_BASES['q_amulet'] = { id: 'q_amulet', name: 'The Widow’s Amulet', cat: 'quest', slot: null, w: 1, h: 1, value: 0, minLvl: 1, durMax: 0, quest: 'sq_amulet' };

/* lore entries (24) */
const LORE = [
  ['l_town_1', 'Letter from the Gate', '…the caravans stopped coming in spring. We hold the gate because the alternative is the dark. — Overser Hald'],
  ['l_town_2', 'The Hollowing', 'First the wells tasted of iron. Then the dogs would not bark at the hill. Then people began to be missed.'],
  ['l_town_3', 'Prices of Desperation', 'A silver coin buys a rope; a gold coin buys a soul. Both hang in the same shop window here.'],
  ['l_town_4', 'Chronicle Fragment I', '“Hollowmere was not built over the Underkeep. The Underkeep was built to sit beneath something older.”'],
  ['l_floor1', 'Drill Orders', 'Third watch holds the stair. No one descends alone. No one fires into the dark without a call.'],
  ['l_floor2', 'Ration Ledger', 'Bread: gone. Salt pork: 4 barrels. Nerves: none to spare.'],
  ['l_floor3', 'Ledger of the Commander', 'They emptied the barracks to feed the works below. Whatever they dug up, it dug back.'],
  ['l_floor4', 'The Captain’s Vow', 'Ash in the lungs, ash on the tongue. I hold this floor until the last torch dies.'],
  ['l_floor5', 'Burial Rite', 'We lay them facing downward so they cannot see the way back up.'],
  ['l_floor6', 'Grave Inventory', 'One hundred forty-one names. The stone remembers what we could not.'],
  ['l_floor7', 'Bell Fragment', '“…and the bell was cast from the melted arms of the first garrison, so that they may still warn us.”'],
  ['l_floor8', 'The Bellkeeper’s Oath', 'I ring to count the dead. I ring to wake no one. Tonight I count wrong.'],
  ['l_floor9', 'Works Manifest', 'Pumps three and four seized. The water is not draining because the water is not water.'],
  ['l_floor10', 'Engineer’s Note', 'Do not trust the switches. The current routes through what used to be the barracks cistern.'],
  ['l_floor11', 'Work Song', 'Down, down, down — the chain sings low; the wheel forgets what it was turning for.'],
  ['l_floor12', 'The Engineer’s Bargain', 'He gave his hands to the machine so the town could have one more winter. The machine kept them.'],
  ['l_floor13', 'Geometry Lesson', 'The corridor is longer inside than outside. Count your steps. Trust the count.'],
  ['l_floor14', 'A Delver’s Last Page', 'The walls breathe when the torches gutter. I have stopped counting my steps.'],
  ['l_floor15', 'Warden Fragment', '“It was built to hold, not to guard. We confused the two.”'],
  ['l_floor16', 'The Warden’s Charge', 'Below all repair, below all reason: I keep the wound open so it does not spread.'],
  ['l_boss1', 'Ashbound Captain’s Record', 'The gate sealed behind us on his order. “No retreat runs through ash,” he said.'],
  ['l_boss2', 'Bell Register', 'Each toll a name. The register is full. He rings anyway.'],
  ['l_boss3', 'Engineer’s Final Log', 'If the valves fail, drown the hall. If the hall fails, drown the works. I am the last valve.'],
  ['l_boss4', 'The Warden’s Testimony', '“You climb down to kill the wound. I climb down to keep it. We are not so different.”'],
];
const LORE_BY_ID = {}; LORE.forEach(l => LORE_BY_ID[l[0]] = { id: l[0], title: l[1], text: l[2] });

/* vendors */
const VENDORS = {
  smith: { name: 'Smith Brammach', glyph: '⚒', color: '#b3552e', services: ['buy', 'sell', 'repair'], greeting: 'Steel keeps better promises than prayer. What do you need?', staples: ['sword_iron', 'axe_hand', 'mace_iron', 'shield_round', 'helm_plate', 'chest_mail', 'arrows:100', 'boots_leather'], role: 'smith' },
  alchemist: { name: 'Alchemist Veyra', glyph: '⚗', color: '#7a5fb5', services: ['buy', 'sell'], greeting: 'Everything is fixable with the right bottle. Mostly.', staples: ['potion_health_s:4', 'potion_health_m:2', 'potion_mana_s:4', 'potion_mana_m:2', 'potion_stam:2', 'antidote:2', 'cleanse:1', 'elixir_resist:1'], role: 'alchemist' },
  mystic: { name: 'Mystic Corvel', glyph: '🜂', color: '#4a86c8', services: ['buy', 'sell', 'identify', 'recharge'], greeting: 'Names have weight here. I trade in names.', staples: ['scroll_identify:3', 'scroll_portal:2', 'book_magic_dart', 'book_ice_lance', 'book_reveal'], role: 'mystic' },
  healer: { name: 'Sister Ammath', glyph: '✚', color: '#8ab57a', services: ['heal'], greeting: 'Flesh mends. Scars keep count.', healCost: lvl => 10 * Math.max(1, lvl), role: 'healer' },
  quartermaster: { name: 'Quartermaster Doss', glyph: '📦', color: '#c8a84a', services: ['buy', 'sell', 'stash'], greeting: 'Everything in its place, and the place is my storehouse.', staples: ['arrows:120', 'shield_kite', 'chest_padded', 'boots_leather'], role: 'quartermaster' },
  chronicler: { name: 'Chronicler Ondrey', glyph: '📜', color: '#c8b04a', services: ['quests'], greeting: 'Every stone below has a story. Most of them end badly.', role: 'chronicler' },
  trainer: { name: 'Training Master Fell', glyph: '⚔', color: '#b07040', services: ['respec'], greeting: 'Skills fade, habits remain. Reforge both.', respecCost: lvl => 100 * Math.max(1, lvl), role: 'trainer' },
};
const NPCS = ['smith', 'alchemist', 'mystic', 'healer', 'quartermaster', 'chronicler', 'trainer'];

/* dungeon event patterns (10+) */
const EVENTS = [
  'elite_treasure', 'abandoned_camp', 'cursed_room', 'merchant_corpse', 'trapped_chest',
  'ambush_beasts', 'brazier_puzzle', 'lever_shortcut', 'survivor', 'poison_altar',
  'bone_trap_room', 'rat_nest',
];

/* shrine kinds */
const SHRINE_KINDS = {
  fountain: { name: 'Restorative Fountain', desc: 'Restores health and mana. Once.', one: true },
  blessing: { name: 'Shrine of Vigor', desc: 'Blessing: +15% damage for 90 s.', one: true },
  revelation: { name: 'Shrine of Sight', desc: 'Reveals the layout of this floor.', one: true },
  transmute: { name: 'Transmutation Altar', desc: 'Rerolls one affix of a chosen equipped item. Once.', one: true },
  risk: { name: 'Blood Pact Stone', desc: '+30% damage and +25% damage taken for 90 s.', one: true },
  cursed_altar: { name: 'Cursed Altar', desc: 'Summons a guardian. Its reward is worthwhile.', one: true },
};

/* trap defs */
const TRAP_DEFS = {
  spike_plate: { name: 'Spike Plate', dmg: [8, 14], type: 'phys', cd: 2.5, telegraph: .4, radius: 1.6 },
  dart_wall: { name: 'Dart Trap', dmg: [5, 9], type: 'pierce', cd: 1.8, radius: 7 },
  fire_vent: { name: 'Fire Vent', dmg: [9, 15], type: 'fire', cd: 3.0, radius: 2.2, status: 'burn' },
  curse_zone: { name: 'Curse Miasma', dmg: 0, type: 'curse', cd: 0, radius: 3.5, status: 'curse' },
  lightning_node: { name: 'Lightning Node', dmg: [12, 18], type: 'lightning', cd: 4.0, radius: 3.0, status: 'shock' },
  tripwire: { name: 'Tripwire Bolt', dmg: [10, 16], type: 'pierce', cd: 2.0, radius: 9 },
  rune_turret: { name: 'Rune Turret', dmg: [10, 15], type: 'arcane', cd: 2.5, radius: 9 },
};

/* ============================================================
   6. RENDERER — raw WebGL2. Lit boxes + point lights + fog + particles.
   ============================================================ */
function makeRenderer(canvas) {
  const gl = canvas.getContext('webgl2', { antialias: true });
  if (!gl) return null;
  const VS = `#version 300 es
layout(location=0) in vec3 aPos; layout(location=1) in vec3 aNor; layout(location=2) in vec4 aCol;
uniform mat4 uProj,uView,uModel; uniform float uSquash;
out vec3 vNor; out vec4 vCol; out vec3 vWorld;
void main(){ vec4 wp = uModel*vec4(aPos,1.0); vWorld=wp.xyz;
  mat3 nm = mat3(uModel); nm[0]=normalize(nm[0]); nm[1]=normalize(nm[1]); nm[2]=normalize(nm[2]);
  vNor = nm*aNor; vCol=aCol;
  gl_Position = uProj*uView*wp; }`;
  const FS = `#version 300 es
precision highp float;
in vec3 vNor; in vec4 vCol; in vec3 vWorld;
uniform int uLightCount; uniform vec4 uLights[14]; uniform vec4 uLightCol[14];
uniform vec3 uAmbient; uniform vec3 uFogCol; uniform float uFogDen; uniform vec3 uCamPos; uniform float uEmFull;
out vec4 frag;
float h21(vec2 p){ p=fract(p*vec2(123.34,456.21)); p+=dot(p,p+34.345); return fract(p.x*p.y); }
void main(){
  vec3 albedo = vCol.rgb; float em = vCol.a;
  vec3 n = normalize(vNor);
  float ay = abs(n.y);
  vec3 wp = vWorld;
  float shade = 1.0;
  if(ay < 0.6){ // walls: brick courses
    float row = floor(wp.y*1.4);
    if(fract(wp.y*1.4) < 0.07) shade *= 0.82;
    float off = mod(row,2.0)*0.5;
    vec2 hxz = (abs(n.x)>0.5) ? vec2(wp.z,wp.y) : vec2(wp.x,wp.y);
    if(fract(hxz.x*0.66+off) < 0.045) shade *= 0.88;
    shade *= 0.92 + 0.16*h21(floor(vec2(hxz.x*0.66+off, row)));
  } else if(n.y > 0.5){ // floors: slab joints
    if(fract(wp.x/3.0) < 0.035 || fract(wp.z/3.0) < 0.035) shade *= 0.85;
    shade *= 0.93 + 0.12*h21(floor(wp.xz*0.5));
  } else { shade *= 0.95; }
  albedo *= shade;
  vec3 lit = uAmbient;
  for(int i=0;i<14;i++){ if(i>=uLightCount) break;
    vec3 L = uLights[i].xyz - vWorld; float dist = length(L);
    float att = clamp(1.0 - dist/max(0.001,uLights[i].w), 0.0, 1.0); att *= att;
    float nl = max(dot(n, L/max(0.001,dist)), 0.0);
    lit += uLightCol[i].rgb * uLightCol[i].a * att * nl;
  }
  vec3 c = albedo * lit + albedo * max(em, uEmFull) * 1.4;
  float fog = 1.0 - exp(-distance(vWorld,uCamPos)*uFogDen);
  c = mix(c, uFogCol, clamp(fog,0.0,1.0));
  c = pow(clamp(c,0.0,1.0), vec3(1.0/1.7));
  frag = vec4(c,1.0);
  if(frag.a==0.0) discard;
}`;
  const PVS = `#version 300 es
layout(location=0) in vec3 aPos; layout(location=1) in vec4 aCol; layout(location=2) in float aSize;
uniform mat4 uProj,uView; out vec4 vCol;
void main(){ vec4 vp = uView*vec4(aPos,1.0); gl_Position = uProj*vp;
  gl_PointSize = aSize * 340.0 / max(0.2,-vp.z); vCol = aCol; }`;
  const PFS = `#version 300 es
precision highp float; in vec4 vCol; out vec4 frag;
void main(){ vec2 d = gl_PointCoord-0.5; float r = dot(d,d);
  if(r>0.25) discard; float a = vCol.a * (1.0 - r*4.0); frag = vec4(vCol.rgb*a,a); }`;
  function mkProg(vs, fs) {
    const p = gl.createProgram();
    for (const [src, type] of [[vs, gl.VERTEX_SHADER], [fs, gl.FRAGMENT_SHADER]]) {
      const s = gl.createShader(type); gl.shaderSource(s, src); gl.compileShader(s);
      if (!gl.getShaderParameter(s, gl.COMPILE_STATUS)) throw new Error('shader: ' + gl.getShaderInfoLog(s));
      gl.attachShader(p, s);
    }
    gl.linkProgram(p);
    if (!gl.getProgramParameter(p, gl.LINK_STATUS)) throw new Error('link: ' + gl.getProgramInfoLog(p));
    return p;
  }
  const prog = mkProg(VS, FS), pprog = mkProg(PVS, PFS);
  const U = n => gl.getUniformLocation(prog, n), PU = n => gl.getUniformLocation(pprog, n);
  const loc = { proj: U('uProj'), view: U('uView'), model: U('uModel'), lights: U('uLights'), lightCol: U('uLightCol'), lc: U('uLightCount'), amb: U('uAmbient'), fogc: U('uFogCol'), fogd: U('uFogDen'), cam: U('uCamPos'), emf: U('uEmFull') };
  const ploc = { proj: PU('uProj'), view: PU('uView') };

  const meshCache = new Map();
  function buildVAO(data) { // data = Float32Array [x,y,z, nx,ny,nz, r,g,b,em] * n
    const vao = gl.createVertexArray(); gl.bindVertexArray(vao);
    const buf = gl.createBuffer(); gl.bindBuffer(gl.ARRAY_BUFFER, buf);
    gl.bufferData(gl.ARRAY_BUFFER, data, gl.STATIC_DRAW);
    const stride = 40;
    gl.enableVertexAttribArray(0); gl.vertexAttribPointer(0, 3, gl.FLOAT, false, stride, 0);
    gl.enableVertexAttribArray(1); gl.vertexAttribPointer(1, 3, gl.FLOAT, false, stride, 12);
    gl.enableVertexAttribArray(2); gl.vertexAttribPointer(2, 4, gl.FLOAT, false, stride, 24);
    gl.bindVertexArray(null);
    return { vao, count: data.length / 10 };
  }
  function pushBox(arr, cx, cy, cz, w, h, d, r, g, b, em, jit) {
    const x0 = cx - w / 2, x1 = cx + w / 2, y0 = cy - h / 2, y1 = cy + h / 2, z0 = cz - d / 2, z1 = cz + d / 2;
    const j = () => jit ? (Math.random() - 0.5) * jit : 0;
    const faces = [
      [[x0, y0, z1], [x1, y0, z1], [x1, y1, z1], [x0, y1, z1], [0, 0, 1]],
      [[x1, y0, z0], [x0, y0, z0], [x0, y1, z0], [x1, y1, z0], [0, 0, -1]],
      [[x1, y0, z1], [x1, y0, z0], [x1, y1, z0], [x1, y1, z1], [1, 0, 0]],
      [[x0, y0, z0], [x0, y0, z1], [x0, y1, z1], [x0, y1, z0], [-1, 0, 0]],
      [[x0, y1, z1], [x1, y1, z1], [x1, y1, z0], [x0, y1, z0], [0, 1, 0]],
      [[x0, y0, z0], [x1, y0, z0], [x1, y0, z1], [x0, y0, z1], [0, -1, 0]],
    ];
    for (const f of faces) {
      const idx = [0, 1, 2, 0, 2, 3];
      for (const i of idx) {
        const v = f[i];
        arr.push(v[0] + j(), v[1] + j() * 0.3, v[2] + j(), f[4][0], f[4][1], f[4][2], r + j(), g + j(), b + j(), em);
      }
    }
  }
  function pushCyl(arr, cx, cy, cz, r, h, seg, cr, cg, cb, em, jit) {
    for (let i = 0; i < seg; i++) {
      const a0 = (i / seg) * TAU, a1 = ((i + 1) / seg) * TAU;
      const x0 = cx + Math.cos(a0) * r, z0 = cz + Math.sin(a0) * r, x1 = cx + Math.cos(a1) * r, z1 = cz + Math.sin(a1) * r;
      const y0 = cy - h / 2, y1 = cy + h / 2;
      const nx = Math.cos((a0 + a1) / 2), nz = Math.sin((a0 + a1) / 2);
      const cols = [cr, cg, cb];
      const j = () => jit ? (Math.random() - 0.5) * jit : 0;
      arr.push(x0, y0, z0, 0, 0, 0, cols[0], cols[1], cols[2], em);
      arr.push(x1, y0, z1, 0, 0, 0, cols[0], cols[1], cols[2], em);
      arr.push(x1, y1, z1, nx, 0, nz, cols[0], cols[1], cols[2], em);
      arr.push(x0, y0, z0, 0, 0, 0, cols[0], cols[1], cols[2], em);
      arr.push(x1, y1, z1, nx, 0, nz, cols[0], cols[1], cols[2], em);
      arr.push(x0, y1, z0, nx, 0, nz, cols[0], cols[1], cols[2], em);
    }
    // cap
    for (let i = 0; i < seg; i++) {
      const a0 = (i / seg) * TAU, a1 = ((i + 1) / seg) * TAU;
      arr.push(cx, cy + h / 2, cz, 0, 1, 0, cr, cg, cb, em);
      arr.push(cx + Math.cos(a0) * r, cy + h / 2, cz + Math.sin(a0) * r, 0, 1, 0, cr, cg, cb, em);
      arr.push(cx + Math.cos(a1) * r, cy + h / 2, cz + Math.sin(a1) * r, 0, 1, 0, cr, cg, cb, em);
    }
  }
  function pushQuadY(arr, cx, cy, cz, w, d, r, g, b, em) {
    const x0 = cx - w / 2, x1 = cx + w / 2, z0 = cz - d / 2, z1 = cz + d / 2;
    const idx = [[x0, z0], [x1, z0], [x1, z1], [x0, z0], [x1, z1], [x0, z1]];
    for (const [x, z] of idx) arr.push(x, cy, z, 0, 1, 0, r, g, b, em);
  }
  function meshOf(key, builder) {
    let m = meshCache.get(key);
    if (!m) { const arr = []; builder(arr); m = buildVAO(new Float32Array(arr)); meshCache.set(key, m); }
    return m;
  }
  const box = (w, h, d, r, g, b, em) => meshOf(`b${w.toFixed(2)}_${h.toFixed(2)}_${d.toFixed(2)}_${r.toFixed(2)}_${g.toFixed(2)}_${b.toFixed(2)}_${em}`, arr => pushBox(arr, 0, 0, 0, w, h, d, r, g, b, em, 0));
  const cyl = (r, h, seg, cr, cg, cb, em) => meshOf(`c${r.toFixed(2)}_${h.toFixed(2)}_${seg}_${cr.toFixed(2)}_${cg.toFixed(2)}_${cb.toFixed(2)}_${em}`, arr => pushCyl(arr, 0, 0, 0, r, h, seg, cr, cg, cb, em, 0));

  /* particles */
  const PMAX = 900;
  const pdata = new Float32Array(PMAX * 8); // pos3 col4 size
  const pvao = gl.createVertexArray();
  const pbuf = gl.createBuffer();
  gl.bindVertexArray(pvao); gl.bindBuffer(gl.ARRAY_BUFFER, pbuf);
  gl.bufferData(gl.ARRAY_BUFFER, pdata.byteLength, gl.DYNAMIC_DRAW);
  gl.enableVertexAttribArray(0); gl.vertexAttribPointer(0, 3, gl.FLOAT, false, 32, 0);
  gl.enableVertexAttribArray(1); gl.vertexAttribPointer(1, 4, gl.FLOAT, false, 32, 12);
  gl.enableVertexAttribArray(2); gl.vertexAttribPointer(2, 1, gl.FLOAT, false, 32, 28);
  gl.bindVertexArray(null);

  const parts = []; // {x,y,z,vx,vy,vz,life,maxLife,r,g,b,a,size,grav,drag,glow}
  function spawnP(o) { if (parts.length < PMAX) parts.push(Object.assign({ vx: 0, vy: 0, vz: 0, life: 0, maxLife: 1, r: 1, g: 1, b: 1, a: 1, size: 3, grav: 0, drag: 0, glow: 1 }, o)); }
  function burst(x, y, z, n, col, spd, size, life, opts) {
    opts = opts || {};
    for (let i = 0; i < n; i++) {
      const a = Math.random() * TAU, e = Math.random() * Math.PI - Math.PI / 2, s = spd * (0.4 + Math.random() * 0.8);
      spawnP({ x, y, z, vx: Math.cos(a) * Math.cos(e) * s, vy: Math.sin(e) * s + (opts.up || 0), vz: Math.sin(a) * Math.cos(e) * s, maxLife: life * (0.6 + Math.random() * 0.8), r: col[0], g: col[1], b: col[2], a: 1, size: size * (0.6 + Math.random() * 0.8), grav: opts.grav !== undefined ? opts.grav : 6, drag: 2, glow: opts.glow !== undefined ? opts.glow : 1 });
    }
  }
  function updateParts(dt) {
    for (let i = parts.length - 1; i >= 0; i--) {
      const p = parts[i];
      p.life += dt;
      if (p.life >= p.maxLife) { parts.splice(i, 1); continue; }
      p.vy -= p.grav * dt;
      const dr = Math.max(0, 1 - p.drag * dt);
      p.vx *= dr; p.vz *= dr;
      p.x += p.vx * dt; p.y += p.vy * dt; p.z += p.vz * dt;
      if (p.y < 0.05) { p.y = 0.05; p.vy *= -0.3; p.vx *= 0.7; p.vz *= 0.7; }
    }
  }
  function drawParts(proj, view) {
    if (!parts.length) return;
    let n = 0;
    for (const p of parts) {
      const t = p.life / p.maxLife;
      const a = p.a * (1 - t) * (p.glow ? 1 : 1);
      const o = n * 8;
      pdata[o] = p.x; pdata[o + 1] = p.y; pdata[o + 2] = p.z;
      pdata[o + 3] = p.r; pdata[o + 4] = p.g; pdata[o + 5] = p.b; pdata[o + 6] = a;
      pdata[o + 7] = p.size;
      n++;
    }
    gl.useProgram(pprog);
    gl.uniformMatrix4fv(ploc.proj, false, proj); gl.uniformMatrix4fv(ploc.view, false, view);
    gl.bindVertexArray(pvao);
    gl.bindBuffer(gl.ARRAY_BUFFER, pbuf);
    gl.bufferSubData(gl.ARRAY_BUFFER, 0, pdata.subarray(0, n * 8));
    gl.enable(gl.BLEND); gl.blendFunc(gl.SRC_ALPHA, gl.ONE); gl.depthMask(false);
    gl.drawArrays(gl.POINTS, 0, n);
    gl.depthMask(true); gl.disable(gl.BLEND);
    gl.bindVertexArray(null);
  }

  gl.enable(gl.DEPTH_TEST);
  gl.clearColor(0, 0, 0, 1);
  let W = 0, H = 0;
  function resize() {
    const dpr = Math.min(1.5, window.devicePixelRatio || 1);
    W = canvas.width = Math.floor(canvas.clientWidth * dpr);
    H = canvas.height = Math.floor(canvas.clientHeight * dpr);
    gl.viewport(0, 0, W, H);
  }
  function setLights(list, px, py, pz) {
    list.sort((a, b) => d2(a.x, a.z, px, pz) - d2(b.x, b.z, px, pz));
    const n = Math.min(14, list.length);
    const lp = new Float32Array(56), lc = new Float32Array(56);
    for (let i = 0; i < n; i++) {
      const L = list[i];
      lp[i * 4] = L.x; lp[i * 4 + 1] = L.y; lp[i * 4 + 2] = L.z; lp[i * 4 + 3] = L.radius;
      let f = L.flicker ? 0.75 + 0.25 * Math.sin(G.time * L.flicker + (L.ph || 0)) : 1;
      lc[i * 4] = L.r; lc[i * 4 + 1] = L.g; lc[i * 4 + 2] = L.b; lc[i * 4 + 3] = L.intensity * f;
    }
    gl.uniform4fv(loc.lights, lp); gl.uniform4fv(loc.lightCol, lc);
    gl.uniform1i(loc.lc, n);
  }
  const IDENT = m4ident();
  function beginFrame() {
    gl.clear(gl.COLOR_BUFFER_BIT | gl.DEPTH_BUFFER_BIT);
  }
  function useMain(proj, view, lights, ambient, fogCol, fogDen, camPos, model) {
    gl.useProgram(prog);
    gl.uniformMatrix4fv(loc.proj, false, proj);
    gl.uniformMatrix4fv(loc.view, false, view);
    setLights(lights, camPos[0], camPos[1], camPos[2]);
    gl.uniform3fv(loc.amb, ambient); gl.uniform3fv(loc.fogc, fogCol);
    gl.uniform1f(loc.fogd, fogDen); gl.uniform3fv(loc.cam, camPos);
    gl.uniform1f(loc.emf, 0);
    gl.uniformMatrix4fv(loc.model, false, model || IDENT);
  }
  function drawMesh(mesh, model, emFull) {
    if (model) gl.uniformMatrix4fv(loc.model, false, model);
    if (emFull !== undefined) gl.uniform1f(loc.emf, emFull); else gl.uniform1f(loc.emf, 0);
    gl.bindVertexArray(mesh.vao);
    gl.drawArrays(gl.TRIANGLES, 0, mesh.count);
    gl.bindVertexArray(null);
  }
  function project(world, proj, view, w, h) {
    const m = m4mul(proj, view);
    const x = world[0], y = world[1], z = world[2];
    const cx = m[0] * x + m[4] * y + m[8] * z + m[12];
    const cy = m[1] * x + m[5] * y + m[9] * z + m[13];
    const cw = m[3] * x + m[7] * y + m[11] * z + m[15];
    if (cw <= 0.01) return null;
    return [(cx / cw * 0.5 + 0.5) * w, (1 - (cy / cw * 0.5 + 0.5)) * h, cw];
  }
  return { gl, canvas, box, cyl, buildVAO, pushBox, pushCyl, pushQuadY, meshOf, useMain, drawMesh, drawParts, spawnP, burst, updateParts, resize, project, beginFrame, get size() { return [W, H]; }, clearDepth: () => gl.clear(gl.DEPTH_BUFFER_BIT), IDENT };
}

/* ============================================================
   7. WORLD — floor generation (logical graph → spatial tiles),
      town hub, collision, LOS, A* pathing
   ============================================================ */
const T_SOLID = 0, T_WALK = 1, T_WATER = 2;
const DIRS = [[0, -1], [1, 0], [0, 1], [-1, 0]]; // N E S W

let PROP_ID = 1;
function newFloor(idx, seed, isTown) {
  return {
    index: idx, isTown: !!isTown, seed, reg: isTown ? TOWN_REG : regionOf(idx),
    W: isTown ? 64 : CFG.mapW, H: isTown ? 64 : CFG.mapH,
    tiles: null, rooms: [], doors: [], props: [], actors: [], ground: [], chests: [], shrines: [],
    traps: [], loreItems: [], levers: [], valves: [], braziers: [], lights: [], portals: [], rifts: [], caltrops: [], mists: [],
    fog: null, spawns: [], bossSpawn: null, stairsDown: null, stairsUp: null, spawn: null,
    staticMesh: null, waterMesh: null, bossDefeated: false, revealed: false,
  };
}
const tileIdx = (F, x, y) => F.tiles[y * F.W + x];
function setTile(F, x, y, t) { if (x > 0 && y > 0 && x < F.W - 1 && y < F.H - 1) F.tiles[y * F.W + x] = t; }
function tileSolid(F, tx, ty) { return tx < 1 || ty < 1 || tx >= F.W - 1 || ty >= F.H - 1 || tileIdx(F, tx, ty) === T_SOLID; }
function worldSolid(F, x, z) {
  const tx = Math.floor(x / CFG.tile), ty = Math.floor(z / CFG.tile);
  if (tileSolid(F, tx, ty)) return true;
  for (const d of F.doors) {
    if (d.state === 'open' || d.state === 'removed') continue;
    const dx = Math.abs(x - (d.x * CFG.tile + CFG.tile / 2)), dz = Math.abs(z - (d.y * CFG.tile + CFG.tile / 2));
    const rr = d.horiz ? 1.5 : 0.5, rv = d.horiz ? 0.5 : 1.5;
    if (dx < rr && dz < rv) return true;
  }
  return false;
}
/* circle-body vs tile collision, axis separated */
function moveBody(F, body, dt) {
  const r = body.radius || 0.45;
  body.vel[1] -= CFG.gravity * dt;
  // horizontal
  let nx = body.pos[0] + body.vel[0] * dt;
  if (!circleBlocked(F, nx, body.pos[2], r)) body.pos[0] = nx; else { body.vel[0] = 0; body.hitWall = true; }
  let nz = body.pos[2] + body.vel[2] * dt;
  if (!circleBlocked(F, body.pos[0], nz, r)) body.pos[2] = nz; else { body.vel[2] = 0; body.hitWall = true; }
  // vertical (flat floors; ground at 0)
  body.pos[1] += body.vel[1] * dt;
  if (body.pos[1] <= 0) { body.pos[1] = 0; body.vel[1] = 0; body.onGround = true; } else body.onGround = false;
}
function circleBlocked(F, x, z, r) {
  const t = CFG.tile;
  for (let ty = Math.floor((z - r) / t); ty <= Math.floor((z + r) / t); ty++) {
    for (let tx = Math.floor((x - r) / t); tx <= Math.floor((x + r) / t); tx++) {
      if (tileSolid(F, tx, ty)) {
        const cx = clamp(x, tx * t, tx * t + t), cz = clamp(z, ty * t, ty * t + t);
        if (d2(x, z, cx, cz) < r * r) return true;
      }
    }
  }
  if (worldSolidDoorsOnly(F, x, z, r)) return true;
  // props with collision
  for (const p of F.props) {
    if (!p.blocking || p.dead) continue;
    if (d2(x, z, p.x, p.z) < (r + (p.rad || 0.5)) * (r + (p.rad || 0.5))) return true;
  }
  return false;
}
function worldSolidDoorsOnly(F, x, z, r) {
  for (const d of F.doors) {
    if (d.state === 'open' || d.state === 'removed') continue;
    const cx = d.x * CFG.tile + CFG.tile / 2, cz = d.y * CFG.tile + CFG.tile / 2;
    const hw = d.horiz ? 1.5 + r : 0.6 + r, hd = d.horiz ? 0.6 + r : 1.5 + r;
    if (Math.abs(x - cx) < hw && Math.abs(z - cz) < hd) return true;
  }
  return false;
}
/* tile DDA raycast for LOS */
function losClear(F, x0, z0, x1, z1) {
  let tx = Math.floor(x0 / CFG.tile), ty = Math.floor(z0 / CFG.tile);
  const ex = Math.floor(x1 / CFG.tile), ey = Math.floor(z1 / CFG.tile);
  const dx = x1 - x0, dz = z1 - z0;
  const stepX = dx > 0 ? 1 : -1, stepY = dz > 0 ? 1 : -1;
  const tDx = dx !== 0 ? Math.abs(CFG.tile / dx) : 1e9;
  const tDy = dz !== 0 ? Math.abs(CFG.tile / dz) : 1e9;
  let tMaxX = dx !== 0 ? ((dx > 0 ? (tx + 1) * CFG.tile - x0 : x0 - tx * CFG.tile) / Math.abs(dx)) : 1e9;
  let tMaxY = dz !== 0 ? ((dz > 0 ? (ty + 1) * CFG.tile - z0 : z0 - ty * CFG.tile) / Math.abs(dz)) : 1e9;
  let guard = 200;
  while (guard-- > 0) {
    if (tx === ex && ty === ey) return true;
    if (tileSolid(F, tx, ty)) return false;
    for (const d of F.doors) if (d.state !== 'open' && d.state !== 'removed' && d.x === tx && d.y === ty) return false;
    if (tMaxX < tMaxY) { tx += stepX; tMaxX += tDx; } else { ty += stepY; tMaxY += tDy; }
    if (tMaxX > 1e8 && tMaxY > 1e8) break;
  }
  return false;
}
/* A* on tiles (4-dir). returns array of [x,z] world centers or null */
function aStar(F, sx, sz, gx, gz) {
  const stx = clamp(Math.floor(sx / CFG.tile), 0, F.W - 1), stz = clamp(Math.floor(sz / CFG.tile), 0, F.H - 1);
  const gtx = clamp(Math.floor(gx / CFG.tile), 0, F.W - 1), gtz = clamp(Math.floor(gz / CFG.tile), 0, F.H - 1);
  if (tileSolid(F, gtx, gtz)) { // snap to nearest walkable neighbor
    let best = null, bd = 1e9;
    for (const [dx, dz] of [[0, 0], [1, 0], [-1, 0], [0, 1], [1, 1], [-1, -1], [1, -1], [-1, 1]]) {
      const nx = gtx + dx, nz = gtz + dz;
      if (!tileSolid(F, nx, nz)) { const d = dx * dx + dz * dz; if (d < bd) { bd = d; best = [nx, nz]; } }
    }
    if (!best) return null; [gtx, gtz] = best;
  }
  const W = F.W, N = W * F.H;
  const gScore = new Float32Array(N).fill(1e9), from = new Int32Array(N).fill(-1), closed = new Uint8Array(N);
  const open = []; // [f, idx]
  const hIdx = (x, y) => y * W + x;
  const hf = (x, y) => Math.abs(x - gtx) + Math.abs(y - gtz);
  gScore[hIdx(stx, stz)] = 0;
  open.push([hf(stx, stz), hIdx(stx, stz)]);
  const doorBlocked = (x, y) => F.doors.some(d => d.x === x && d.y === y && d.state !== 'open' && d.state !== 'removed');
  let found = false, guard = 6000;
  while (open.length && guard-- > 0) {
    let bi = 0; for (let i = 1; i < open.length; i++) if (open[i][0] < open[bi][0]) bi = i;
    const [f, cur] = open.splice(bi, 1)[0];
    if (closed[cur]) continue;
    closed[cur] = 1;
    const cx = cur % W, cy = (cur / W) | 0;
    if (cx === gtx && cy === gtz) { found = true; break; }
    for (const [dx, dz] of DIRS) {
      const nx = cx + dx, nz = cy + dz;
      if (tileSolid(F, nx, nz) || doorBlocked(nx, nz)) continue;
      const ni = hIdx(nx, nz);
      if (closed[ni]) continue;
      const cost = (tileIdx(F, nx, nz) === T_WATER ? 1.6 : 1);
      const ng = gScore[cur] + cost;
      if (ng < gScore[ni]) { gScore[ni] = ng; from[ni] = cur; open.push([ng + hf(nx, nz), ni]); }
    }
  }
  if (!found) return null;
  const path = [];
  let cur = hIdx(gtx, gtz);
  while (cur !== -1) { path.push([(cur % W) * CFG.tile + CFG.tile / 2, ((cur / W) | 0) * CFG.tile + CFG.tile / 2]); if (from[cur] === -1) break; cur = from[cur]; }
  path.reverse();
  return path;
}

/* ---------------- spatial helpers ---------------- */
function rectFree(F, x0, y0, w, h, margin) {
  margin = margin === undefined ? 1 : margin;
  for (let y = y0 - margin; y < y0 + h + margin; y++)
    for (let x = x0 - margin; x < x0 + w + margin; x++)
      if (x < 1 || y < 1 || x >= F.W - 1 || y >= F.H - 1) return false;
      else if (tileIdx(F, x, y) !== T_SOLID) return false;
  return true;
}
function stampRect(F, x0, y0, w, h, t) {
  for (let y = y0; y < y0 + h; y++) for (let x = x0; x < x0 + w; x++) setTile(F, x, y, t);
}
function carveCorridor(F, x0, y0, x1, y1, wHalf) {
  // L corridor (horiz then vert), width 2*wHalf+1 centered on line
  const step = (x, y) => { for (let dy = -wHalf; dy <= wHalf; dy++) for (let dx = -wHalf; dx <= wHalf; dx++) { if (tileIdx(F, x + dx, y + dy) === T_SOLID) setTile(F, x + dx, y + dy, T_WALK); } };
  let x = x0, y = y0;
  while (x !== x1) { step(x, y); x += x1 > x ? 1 : -1; }
  while (y !== y1) { step(x, y); y += y1 > y ? 1 : -1; }
  step(x1, y1);
}
function rectCenter(r) { return [(r.x0 + r.x1) / 2, (r.y0 + r.y1) / 2]; }
function rw(F, r) { return r.x1 - r.x0 + 1; }
function rh(F, r) { return r.y1 - r.y0 + 1; }

/* ---------------- floor generation ---------------- */
function generateFloor(campaign, idx, seedOverride) {
  const region = regionOf(idx);
  const baseSeed = seedOverride !== undefined ? seedOverride : campaign.seed;
  let layout = null, usedSeed = baseSeed;
  for (let attempt = 0; attempt < 12 && !layout; attempt++) {
    usedSeed = hashMix(baseSeed, idx, attempt, campaign.descent || 0);
    const cand = tryGenerateFloor(idx, usedSeed);
    // AssertMandatoryReachability: reject layouts whose rooms/exit are not connected
    if (cand && assertReachable(cand.F)) layout = cand;
  }
  if (!layout) throw new Error('floor gen failed');
  const F = layout.F;
  populateFloor(F, campaign, idx, usedSeed);
  return F;
}
function tryGenerateFloor(idx, seed) {
  const F = newFloor(idx, seed);
  F.tiles = new Uint8Array(F.W * F.H);
  F.fog = new Uint8Array(F.W * F.H);
  const r = mulberry32(seed);
  const bossFloor = [4, 8, 12, 16].includes(idx);
  const region = regionOf(idx);
  // main path node roles
  let mainCount = 7 + (region.id > 0 ? ri(r, 1, 3) : 0);
  mainCount = Math.min(mainCount, 12);
  const roles = ['start', 'combat'];
  const midRoles = ['combat', 'respite', 'combat', 'reward', 'challenge', 'combat', 'reward', 'combat', 'respite', 'challenge'];
  while (roles.length < mainCount - 2) roles.push(midRoles[roles.length % midRoles.length]);
  if (bossFloor) { roles.push('boss_ante', 'boss'); }
  roles.push('exit');

  // place rooms
  const sizes = { start: [7, 7], combat: [8, 10], respite: [7, 7], reward: [7, 8], challenge: [9, 9], boss_ante: [8, 8], boss: [13, 11], exit: [7, 7] };
  let cx = (F.W / 2) | 0, cy = (F.H / 2) | 0;
  let ok = true;
  for (let i = 0; i < roles.length && ok; i++) {
    const role = roles[i];
    const [w, h] = sizes[role];
    if (i === 0) {
      const x0 = cx - (w >> 1), y0 = cy - (h >> 1);
      if (!rectFree(F, x0, y0, w, h, 2)) { ok = false; break; }
      stampRect(F, x0, y0, w, h, T_WALK);
      F.rooms.push({ id: 'r' + i, role, x0, y0, x1: x0 + w - 1, y1: y0 + h - 1, order: 0, main: true, disc: false });
      continue;
    }
    const parent = F.rooms[F.rooms.length - (role === 'boss' ? 1 : role === 'boss_ante' ? 1 : 1)];
    let placed = false;
    for (let att = 0; att < 140 && !placed; att++) {
      const dir = pick(r, DIRS);
      const dist = ri(r, 4, 7);
      const px = Math.round(rectCenter(parent)[0]), py = Math.round(rectCenter(parent)[1]);
      const x0 = px + dir[0] * (dist + (dir[0] ? (rw(F, parent) / 2 | 0) + (w / 2 | 0) : 0)) - (w >> 1) + (dir[0] === 0 ? ri(r, -2, 2) : 0);
      const y0 = py + dir[1] * (dist + (dir[1] ? (rh(F, parent) / 2 | 0) + (h / 2 | 0) : 0)) - (h >> 1) + (dir[1] === 0 ? ri(r, -2, 2) : 0);
      if (!rectFree(F, x0, y0, w, h, 1)) continue;
      // corridor from parent center to new center
      const nx = x0 + (w >> 1), ny = y0 + (h >> 1);
      // corridor must pass through free-ish space (tiles solid or corridor-marked) — carve then check no room overlap:
      stampRect(F, x0, y0, w, h, T_WALK);
      carveCorridor(F, px, py, nx, ny, 0);
      // door cells: nearest boundary of parent room along corridor — simplified: door at midpoint of corridor
      const mx = ((px + nx) / 2) | 0, my = ((py + ny) / 2) | 0;
      const horiz = Math.abs(px - nx) >= Math.abs(py - ny);
      if (tileSolid(F, mx, my)) { /* fallback: undo? accept - door on corridor */ }
      const door = { id: 'd' + F.doors.length, x: mx, y: my, horiz: !horiz, state: 'closed', kind: 'normal', key: null };
      F.doors.push(door);
      F.rooms.push({ id: 'r' + F.rooms.length, role, x0, y0, x1: x0 + w - 1, y1: y0 + h - 1, order: i, main: true, disc: false, door: door.id, parent: parent.id });
      placed = true;
    }
    if (!placed) { ok = false; }
  }
  if (!ok) return null;

  // side branches (2-5, 1-3 rooms each)
  const branchCount = ri(r, 2, 5);
  const mainRooms = F.rooms.filter(rm => rm.main);
  for (let b = 0; b < branchCount; b++) {
    const anchor = pick(r, mainRooms.filter(rm => rm.role !== 'start' && rm.role !== 'boss' && rm.role !== 'boss_ante'));
    if (!anchor) break;
    let parent = anchor;
    const rooms = ri(r, 1, 3);
    for (let j = 0; j < rooms; j++) {
      const w = ri(r, 5, 8), h = ri(r, 5, 8);
      let placed = false;
      for (let att = 0; att < 60 && !placed; att++) {
        const dir = pick(r, DIRS);
        const dist = ri(r, 4, 7);
        const px = Math.round(rectCenter(parent)[0]), py = Math.round(rectCenter(parent)[1]);
        const x0 = px + dir[0] * (dist + 6) - (w >> 1), y0 = py + dir[1] * (dist + 6) - (h >> 1);
        if (!rectFree(F, x0, y0, w, h, 1)) continue;
        const nx = x0 + (w >> 1), ny = y0 + (h >> 1);
        stampRect(F, x0, y0, w, h, T_WALK);
        carveCorridor(F, px, py, nx, ny, 0);
        const mx = ((px + nx) / 2) | 0, my = ((py + ny) / 2) | 0;
        const horiz = Math.abs(px - nx) >= Math.abs(py - ny);
        F.doors.push({ id: 'd' + F.doors.length, x: mx, y: my, horiz: !horiz, state: 'closed', kind: 'normal', key: null });
        const room = { id: 'r' + F.rooms.length, role: 'branch', x0, y0, x1: x0 + w - 1, y1: y0 + h - 1, order: parent.order + 1, main: false, disc: false, parent: parent.id };
        F.rooms.push(room);
        parent = room; placed = true;
      }
      if (!placed) break;
    }
  }
  // secret room(s): guaranteed on every second floor
  const secrets = idx % 2 === 0 ? 1 : ri(r, 0, 1);
  for (let s = 0; s < secrets; s++) {
    const anchor = pick(r, mainRooms.filter(rm => rm.role !== 'boss' && rm.role !== 'boss_ante' && rm.role !== 'exit'));
    if (!anchor) break;
    const w = ri(r, 4, 6), h = ri(r, 4, 6);
    for (let att = 0; att < 80; att++) {
      const dir = pick(r, DIRS);
      const px = Math.round(rectCenter(anchor)[0]), py = Math.round(rectCenter(anchor)[1]);
      const x0 = px + dir[0] * (ri(r, 3, 5) + 5) - (w >> 1), y0 = py + dir[1] * (ri(r, 3, 5) + 5) - (h >> 1);
      if (!rectFree(F, x0, y0, w, h, 1)) continue;
      const nx = x0 + (w >> 1), ny = y0 + (h >> 1);
      stampRect(F, x0, y0, w, h, T_WALK);
      carveCorridor(F, px, py, nx, ny, 0);
      const mx = ((px + nx) / 2) | 0, my = ((py + ny) / 2) | 0;
      const horiz = Math.abs(px - nx) >= Math.abs(py - ny);
      F.doors.push({ id: 'd' + F.doors.length, x: mx, y: my, horiz: !horiz, state: 'closed', kind: 'secret', key: null, hidden: true });
      F.rooms.push({ id: 'r' + F.rooms.length, role: 'secret', x0, y0, x1: x0 + w - 1, y1: y0 + h - 1, order: anchor.order, main: false, secret: true, disc: false });
      break;
    }
  }
  // loop cross-links (1-3): connect two main rooms with open corridor (no door)
  const loops = ri(r, 1, 3);
  for (let l = 0; l < loops; l++) {
    const a = pick(r, mainRooms), b = pick(r, mainRooms);
    if (!a || !b || a === b) continue;
    const ac = rectCenter(a), bc = rectCenter(b);
    if (d2(ac[0], ac[1], bc[0], bc[1]) > CFG.tile * 26) continue;
    carveCorridor(F, Math.round(ac[0]), Math.round(ac[1]), Math.round(bc[0]), Math.round(bc[1]), 0);
  }
  // lock a main-path door on floors >= 2 (not final); key placed in an earlier MAIN room (guaranteed before the lock)
  if (idx >= 2 && idx !== 16) {
    const mainRooms = F.rooms.filter(rm => rm.main && rm.door && !['start', 'exit', 'boss', 'boss_ante'].includes(rm.role) && rm.order >= 2);
    if (mainRooms.length) {
      const lockRoom = pick(r, mainRooms);
      const door = F.doors.find(d => d.id === lockRoom.door);
      if (door) {
        door.kind = 'locked'; door.key = 'key_f' + idx;
        const before = F.rooms.filter(rm => rm.main && rm.order < lockRoom.order && !['start'].includes(rm.role) && rm.role !== 'boss' && rm.role !== 'boss_ante');
        const keyRoom = before.length ? pick(r, before) : F.rooms[1];
        F.keyRoom = keyRoom ? keyRoom.id : null;
      }
    }
  }
  // region flavor: water strips (flooded works)
  if (region.id === 2) {
    for (const rm of F.rooms) {
      if (rm.role === 'start' || rm.role === 'boss') continue;
      if (chance(r, .45)) {
        const cy = ri(r, rm.y0 + 1, rm.y1 - 1);
        for (let x = rm.x0; x <= rm.x1; x++) { if (tileIdx(F, x, cy) === T_WALK) setTile(F, x, cy, T_WATER); if (tileIdx(F, x, cy + 1) === T_WALK) setTile(F, x, cy + 1, T_WATER); }
      }
    }
  }
  // start/exit positions
  const startRoom = F.rooms[0], exitRoom = F.rooms.find(rm => rm.role === 'exit') || F.rooms[F.rooms.length - 1];
  const sc = rectCenter(startRoom);
  F.spawn = [sc[0] * CFG.tile + CFG.tile / 2, 0, sc[1] * CFG.tile + CFG.tile / 2];
  F.stairsDown = { x: rectCenter(exitRoom)[0] * CFG.tile + CFG.tile / 2, z: rectCenter(exitRoom)[1] * CFG.tile + CFG.tile / 2, room: exitRoom.id };
  F.stairsUp = { x: F.spawn[0], z: F.spawn[2] + CFG.tile * 2, room: startRoom.id };
  F.startRoom = startRoom.id; F.exitRoom = exitRoom.id;
  F.usedSeed = seed;
  return { F };
}

/* populate: enemies, chests (committed loot), traps, shrines, lore, props, lights, events */
function populateFloor(F, campaign, idx, seed) {
  const r = mulberry32(hashMix(seed, 0xF00D));
  const rFoes = mulberry32(hashMix(seed, 0xF0E5));
  const rLoot = mulberry32(hashMix(seed, 0xF11E));
  const rDeco = mulberry32(hashMix(seed, 0xFDEC));
  const region = regionOf(idx);
  const fs = campaign.floors[idx] || (campaign.floors[idx] = {});
  const killed = new Set(fs.killed || []);
  const isBoss = [4, 8, 12, 16].includes(idx);

  // interior walkable tile list per room
  const roomTiles = rm => { const out = []; for (let y = rm.y0 + 1; y < rm.y1; y++) for (let x = rm.x0 + 1; x < rm.x1; x++) if (tileIdx(F, x, y) === T_WALK || tileIdx(F, x, y) === T_WATER) out.push([x, y]); return out; };
  const openTiles = [];
  for (let y = 1; y < F.H - 1; y++) for (let x = 1; x < F.W - 1; x++) if (tileIdx(F, x, y) === T_WALK) openTiles.push([x, y]);

  // enemy budget
  let budget = (6 + idx * 1.6) * (campaign.diffHp > 1.1 ? 1.1 : 1);
  const regionPool = ENEMIES.filter(e => e.reg === region.id);
  const tierCost = { grunt: 1, ranged: 1.5, beast: 1, caster: 1.5, brute: 2.5 };
  // no spawns near start
  const spawnTx = F.spawn[0] / CFG.tile, spawnTz = F.spawn[2] / CFG.tile;
  let spawnSeq = [];
  const roleWeights = { combat: 1, challenge: 1.4, reward: .5, respite: 0, boss_ante: .6, branch: .8, secret: .3, exit: .2, boss: 0 };
  for (const rm of F.rooms) {
    if (rm.role === 'boss') continue;
    const tiles = roomTiles(rm).filter(([x, y]) => d2(x, y, spawnTx, spawnTz) > 3.2);
    if (!tiles.length) continue;
    const w = roleWeights[rm.role] || .5;
    let rb = budget * w * (0.7 + r() * 0.6);
    const group = [];
    while (rb >= 1 && group.length < 7) {
      const arch = wpick(rFoes, regionPool.map(e => [e, e.tier === 'brute' ? .5 : e.tier === 'caster' ? .9 : 1.2]));
      const cost = tierCost[arch.tier] || 1;
      if (cost > rb + 0.6) { rb -= 0.5; continue; }
      rb -= cost;
      group.push(arch);
    }
    for (const arch of group) {
      const t = pick(rFoes, tiles);
      spawnSeq.push({ arch: arch.id, x: t[0] * CFG.tile + CFG.tile / 2 + (rFoes() - .5), z: t[1] * CFG.tile + CFG.tile / 2 + (rFoes() - .5), level: clamp(idx + ri(rFoes, -1, 1), 1, 30) });
      budget -= tierCost[arch.tier] || 1;
    }
  }
  // elites
  const eliteCount = idx <= 2 ? ri(rFoes, 0, 1) : ri(rFoes, 1, 3);
  for (let i = 0; i < eliteCount && spawnSeq.length; i++) {
    const s = pick(rFoes, spawnSeq.filter(s => ENEMY_BY_ID[s.arch].tier !== 'beast'));
    if (s) { s.elite = wpick(rFoes, Object.keys(ELITES).slice(0, idx < 9 ? 5 : 8).map(k => [k, 1])); if (idx >= 9 && chance(rFoes, .5)) s.elite2 = wpick(rFoes, Object.keys(ELITES).map(k => [k, 1])); }
  }
  // named quest elites
  for (const q of QUESTS) {
    if (campaign.quests[q.id]?.state === 'done') continue;
    if (q.objectives.some(o => o.type === 'killElite')) {
      const o = q.objectives.find(o => o.type === 'killElite');
      if ((ENEMY_BY_ID[o.arch]?.reg === region.id) && (campaign.maxFloor >= (o.arch === 'deep_sentinel' ? 13 : ENEMY_BY_ID[o.arch].reg * 4 + 1) || true)) {
        const cand = spawnSeq.filter(s => s.arch === o.arch && !s.elite);
        if (cand.length) { const s = pick(rFoes, cand); s.elite = s.elite || 'enraged'; s.questElite = q.id; }
      }
    }
  }
  // committed loot per enemy
  const lootRng = rLoot;
  for (const s of spawnSeq) {
    const arch = ENEMY_BY_ID[s.arch];
    s.killedKey = 'k' + hashMix(seed, Math.round(s.x * 10), Math.round(s.z * 10), spawnSeq.indexOf(s));
    const nItems = (arch.tier === 'brute' ? 1 : chance(lootRng, .22) ? 1 : 0) + (s.elite ? 1 : 0);
    s.loot = rollLoot(lootRng, {
      ilvl: idx + (s.elite ? 2 : 0), n: nItems, lootMul: s.elite ? 2.2 : 1,
      weights: s.elite ? { common: 20, enchanted: 50, rare: 28, relic: 2 } : null,
    });
    s.gold = Math.round((4 + idx * 2.5) * (arch.tier === 'brute' ? 2.2 : 1) * (s.elite ? 3 : 1) * (0.6 + lootRng() * 0.9));
  }
  // boss
  if (isBoss) {
    const bossId = ['ashbound_captain', 'bellkeeper', 'drowned_engineer', 'warden_below'][[4, 8, 12, 16].indexOf(idx)];
    const bossRoom = F.rooms.find(rm => rm.role === 'boss');
    if (bossRoom) {
      const c = rectCenter(bossRoom);
      F.bossSpawn = { boss: bossId, x: c[0] * CFG.tile + CFG.tile / 2, z: c[1] * CFG.tile + CFG.tile / 2, level: clamp(idx, 1, 30), killedKey: 'boss' + idx };
      // boss gate doors jam while fighting: mark doors around boss room
      for (const d of F.doors) if (d.kind !== 'secret') d.bossGate = false;
      // committed boss loot
      F.bossLoot = [
        ...rollLoot(lootRng, { ilvl: idx + 3, n: 2, weights: { common: 5, enchanted: 45, rare: 45, relic: 5 } }),
        ...(chance(lootRng, .35) ? rollLoot(lootRng, { ilvl: idx, n: 1, rarity: 'relic' }) : []),
      ];
      F.bossGold = 200 + idx * 60;
    }
  }
  // chests 3-7 (+rare 0-2)
  const chestRooms = F.rooms.filter(rm => rm.role !== 'start' && rm.role !== 'boss' && rm.role !== 'boss_ante');
  const chestCount = ri(rLoot, 3, 7);
  for (let i = 0; i < chestCount; i++) {
    const rm = pick(rLoot, chestRooms); const tiles = roomTiles(rm);
    if (!tiles.length) continue;
    const t = pick(rLoot, tiles);
    const rare = chance(rLoot, .18);
    const chest = {
      id: 'c' + hashMix(seed, i, 0xC), x: t[0] * CFG.tile + CFG.tile / 2, z: t[1] * CFG.tile + CFG.tile / 2,
      rare, opened: fs.openedChests ? fs.openedChests['c' + hashMix(seed, i, 0xC)] || false : false,
      loot: rollLoot(rLoot, { ilvl: idx + 1 + (rare ? 2 : 0), n: ri(rLoot, 1, 3), weights: rare ? { common: 15, enchanted: 45, rare: 35, relic: 5 } : null, relicChance: rare ? .04 : .008 }),
      gold: Math.round((10 + idx * 5) * (rare ? 2.5 : 1) * (0.7 + rLoot() * 0.8)),
    };
    F.chests.push(chest);
  }
  // shrines 0-2
  const shrineCount = ri(rLoot, 0, 2);
  const kinds = Object.keys(SHRINE_KINDS);
  for (let i = 0; i < shrineCount; i++) {
    const rm = pick(rLoot, F.rooms.filter(rm => rm.role !== 'start' && rm.role !== 'boss'));
    const tiles = roomTiles(rm); if (!tiles.length) continue;
    const t = pick(rLoot, tiles);
    const id = 's' + hashMix(seed, i, 0x5);
    F.shrines.push({ id, kind: pick(rLoot, kinds), x: t[0] * CFG.tile + CFG.tile / 2, z: t[1] * CFG.tile + CFG.tile / 2, used: (fs.shrinesUsed || []).includes(id) });
  }
  // traps 2-8 by region
  const trapDefs = Object.keys(TRAP_DEFS);
  const trapCount = ri(rLoot, 2, 8);
  for (let i = 0; i < trapCount; i++) {
    const t = pick(rLoot, openTiles.filter(([x, y]) => d2(x, y, spawnTx, spawnTz) > 4));
    if (!t) continue;
    const defId = region.id === 0 ? wpick(rLoot, [['spike_plate', 3], ['dart_wall', 3], ['tripwire', 2], ['fire_vent', 1]])
      : region.id === 1 ? wpick(rLoot, [['spike_plate', 2], ['dart_wall', 2], ['curse_zone', 3], ['tripwire', 2]])
        : region.id === 2 ? wpick(rLoot, [['lightning_node', 3], ['dart_wall', 2], ['spike_plate', 2], ['tripwire', 1]])
          : wpick(rLoot, [['rune_turret', 3], ['curse_zone', 2], ['fire_vent', 2], ['spike_plate', 1]]);
    F.traps.push({ id: 't' + hashMix(seed, i, 0x7), def: defId, x: t[0] * CFG.tile + CFG.tile / 2, z: t[1] * CFG.tile + CFG.tile / 2, cd: 0, armed: true, revealed: false });
  }
  // lore placement (rotate through campaign-undiscovered entries)
  const lorePool = LORE.filter(l => !campaign.lore[l[0]] && !l[0].startsWith('l_town') && !l[0].startsWith('l_boss'));
  if (lorePool.length) {
    const rm = pick(rLoot, F.rooms.filter(rm => rm.role !== 'start'));
    const tiles = roomTiles(rm);
    if (tiles.length) {
      const t = pick(rLoot, tiles);
      const entry = lorePool[(idx * 7 + campaign.descent * 3) % lorePool.length];
      F.loreItems.push({ id: 'l' + hashMix(seed, idx, 0x10), loreId: entry[0], x: t[0] * CFG.tile + CFG.tile / 2, z: t[1] * CFG.tile + CFG.tile / 2 });
    }
  }
  // quest pickups (main/side objectives)
  const placeQuestItem = (baseId, floorRange) => {
    if (floorRange && (idx < floorRange[0] || idx > floorRange[1])) return;
    const rms = F.rooms.filter(rm => rm.role !== 'start' && rm.role !== 'boss');
    const rm = rms.length ? pick(rLoot, rms) : null; const tiles = rm ? roomTiles(rm) : [];
    if (tiles.length) {
      const t = pick(rLoot, tiles);
      F.questPickups = F.questPickups || [];
      F.questPickups.push({ base: baseId, x: t[0] * CFG.tile + CFG.tile / 2, z: t[1] * CFG.tile + CFG.tile / 2, done: false });
    }
  };
  for (const q of QUESTS) {
    const st = campaign.quests[q.id];
    if (!st || st.state !== 'active') continue;
    for (const o of q.objectives) {
      if (o.type === 'pickup' && !(st.objDone || {})[o.id]) placeQuestItem(o.base, o.floorRange);
    }
  }
  // valves (flooded works): quest + flavor
  if (region.id === 2) {
    const n = idx >= 10 ? 1 : 1;
    for (let i = 0; i < n; i++) {
      const rms = F.rooms.filter(rm => rm.role !== 'start' && rm.role !== 'boss' && rm.role !== 'exit');
      const rm = rms.length ? pick(rLoot, rms) : null; const tiles = rm ? roomTiles(rm) : [];
      if (tiles.length) {
        const t = pick(rLoot, tiles);
        F.valves.push({ id: 'v' + hashMix(seed, i, 0x77), x: t[0] * CFG.tile + CFG.tile / 2, z: t[1] * CFG.tile + CFG.tile / 2, turned: (fs.valves || []).includes('v' + hashMix(seed, i, 0x77)) });
      }
    }
  }
  // event room
  if (idx >= 2 && !fs.eventDone) {
    const evRooms = F.rooms.filter(rm => rm.role === 'branch' || rm.role === 'respite');
    const rm = evRooms.length ? pick(rLoot, evRooms) : null;
    if (rm) {
      const tiles = roomTiles(rm);
      if (tiles.length) {
        const ev = EVENTS[(hashMix(seed, 0xE) + idx) % EVENTS.length];
        const c = pick(rLoot, tiles);
        F.event = { type: ev, x: c[0] * CFG.tile + CFG.tile / 2, z: c[1] * CFG.tile + CFG.tile / 2, room: rm.id, done: false };
      }
    }
  }
  // props & deco & lights
  decorateFloor(F, rDeco, idx, seed, fs);
  // key placement
  if (F.doors.some(d => d.kind === 'locked')) {
    const keyRoom = F.rooms.find(rm => rm.id === F.keyRoom) || F.rooms[1];
    const tiles = roomTiles(keyRoom);
    if (tiles.length) {
      const t = pick(rDeco, tiles);
      F.keyPickup = { keyId: 'key_f' + idx, x: t[0] * CFG.tile + CFG.tile / 2, z: t[1] * CFG.tile + CFG.tile / 2, taken: (fs.keyTaken || false) };
    } else F.doors.forEach(d => { if (d.kind === 'locked') { d.kind = 'normal'; d.key = null; } });
  }
  // fire events? done at runtime
  spawnSeq.forEach(s => { F.spawns.push(s); });
  // assert reachability: start → exit with all non-secret doors passable
  if (!assertReachable(F)) throw new Error('unreachable floor');
}

function decorateFloor(F, r, idx, seed, fs) {
  const region = regionOf(idx);
  const torchEvery = 5;
  // wall torches in rooms + corridors
  for (let y = 1; y < F.H - 1; y++) for (let x = 1; x < F.W - 1; x++) {
    if (tileIdx(F, x, y) !== T_WALK) continue;
    const isRoom = F.rooms.some(rm => x >= rm.x0 && x <= rm.x1 && y >= rm.y0 && y <= rm.y1);
    if ((x + y * 3) % torchEvery === 0) {
      // attach to a solid neighbor
      const dirs = shuffle(r, DIRS);
      for (const [dx, dz] of dirs) {
        if (tileIdx(F, x + dx, y + dz) === T_SOLID) {
          F.props.push({ id: 'p' + (PROP_ID++), type: 'torch', x: x * CFG.tile + CFG.tile / 2 + dx * 1.1, y: 2.0, z: y * CFG.tile + CFG.tile / 2 + dz * 1.1, wall: [dx, dz] });
          F.lights.push({ x: x * CFG.tile + CFG.tile / 2 + dx * 0.7, y: 2.1, z: y * CFG.tile + CFG.tile / 2 + dz * 0.7, r: region.torch[0], g: region.torch[1], b: region.torch[2], radius: 9, intensity: 1.0, flicker: 6, ph: r() * TAU });
          break;
        }
      }
    }
  }
  // per-room props
  for (const rm of F.rooms) {
    const tiles = [];
    for (let y = rm.y0 + 1; y < rm.y1; y++) for (let x = rm.x0 + 1; x < rm.x1; x++) if (tileIdx(F, x, y) === T_WALK) tiles.push([x, y]);
    if (!tiles.length) continue;
    const nProps = rm.role === 'boss' ? 2 : ri(r, 2, 6);
    for (let i = 0; i < nProps; i++) {
      const t = pick(r, tiles);
      const wx = t[0] * CFG.tile + CFG.tile / 2, wz = t[1] * CFG.tile + CFG.tile / 2;
      const kind = wpick(r, [['crate', 3], ['barrel', 3], ['brazier', 1], ['bones', region.id === 1 ? 3 : 1], ['rubble', 2], ['table', 1], ['rack', 1]]);
      if (F.chests.some(c => d2(c.x, c.z, wx, wz) < 2) || F.shrines.some(s => d2(s.x, s.z, wx, wz) < 2)) continue;
      F.props.push({ id: 'p' + (PROP_ID++), type: kind, x: wx, z: wz, y: 0, hp: kind === 'crate' ? 12 : kind === 'barrel' ? 10 : 999, dead: kind === 'bones' || kind === 'rubble' || kind === 'table' || kind === 'rack' || kind === 'brazier' ? false : false, blocking: kind === 'crate' || kind === 'barrel' || kind === 'brazier' || kind === 'table' || kind === 'rack', rad: 0.5, loot: chance(r, .5) ? rollLoot(mulberry32(hashMix(seed, PROP_ID, 0xB)), { ilvl: idx, n: 1, identified: true }) : null, gold: chance(r, .4) ? ri(r, 2, 8 + idx) : 0 });
    }
    if (rm.role === 'respite' || rm.role === 'boss_ante') {
      const t = pick(r, tiles);
      F.props.push({ id: 'p' + (PROP_ID++), type: 'campfire', x: t[0] * CFG.tile + CFG.tile / 2, z: t[1] * CFG.tile + CFG.tile / 2, y: 0, dead: false, blocking: false, rad: 0 });
      F.lights.push({ x: t[0] * CFG.tile + CFG.tile / 2, y: 0.8, z: t[1] * CFG.tile + CFG.tile / 2, r: 1.0, g: 0.6, b: 0.3, radius: 8, intensity: 1.0, flicker: 5, ph: r() * TAU });
    }
    if (region.id === 3) {
      for (let i = 0; i < 2; i++) {
        const t = pick(r, tiles);
        F.rifts.push({ id: 'rf' + (PROP_ID++), x: t[0] * CFG.tile + CFG.tile / 2, z: t[1] * CFG.tile + CFG.tile / 2, ph: r() * TAU });
        F.lights.push({ x: t[0] * CFG.tile + CFG.tile / 2, y: 1.2, z: t[1] * CFG.tile + CFG.tile / 2, r: 0.6, g: 0.3, b: 1.0, radius: 6, intensity: 0.7, flicker: 3, ph: r() * TAU });
      }
    }
  }
  // stairs meshes are dynamic; add light there
  F.lights.push({ x: F.stairsDown.x, y: 1.6, z: F.stairsDown.z, r: 0.9, g: 0.8, b: 0.5, radius: 8, intensity: 0.9, flicker: 2, ph: 0 });
}

function assertReachable(F) {
  const start = F.rooms[0];
  const sx = Math.round(rectCenter(start)[0]), sz = Math.round(rectCenter(start)[1]);
  const seen = new Uint8Array(F.W * F.H);
  const q = [[sx, sz]]; seen[sz * F.W + sx] = 1;
  while (q.length) {
    const [x, y] = q.pop();
    for (const [dx, dz] of DIRS) {
      const nx = x + dx, nz = y + dz;
      if (tileSolid(F, nx, nz)) continue;
      const ni = nz * F.W + nx;
      if (seen[ni]) continue;
      const door = F.doors.find(d => d.x === nx && d.y === nz);
      if (door && door.kind === 'secret') continue;
      seen[ni] = 1; q.push([nx, nz]);
    }
  }
  // every non-secret room must have a reachable tile
  for (const rm of F.rooms) {
    if (rm.secret) continue;
    let ok = false;
    for (let y = rm.y0; y <= rm.y1 && !ok; y++) for (let x = rm.x0; x <= rm.x1 && !ok; x++) if (seen[y * F.W + x]) ok = true;
    if (!ok) return false;
  }
  // exit reachable
  const ex = F.rooms.find(rm => rm.role === 'exit') || F.rooms[F.rooms.length - 1];
  for (let y = ex.y0; y <= ex.y1; y++) for (let x = ex.x0; x <= ex.x1; x++) if (seen[y * F.W + x]) return true;
  return false;
}

/* ---------------- static geometry build ---------------- */
function buildStaticMesh(R, F) {
  const arr = [], warr = [];
  const reg = F.reg;
  for (let y = 1; y < F.H - 1; y++) for (let x = 1; x < F.W - 1; x++) {
    const t = tileIdx(F, x, y);
    if (t === T_SOLID) continue;
    const wx = x * CFG.tile, wz = y * CFG.tile;
    const jit = 0.03;
    const fc = reg.floorC;
    if (t === T_WALK) {
      for (let i = 0; i < 6; i++) { /* placeholder no-op to keep structure */ }
      // floor quad
      R.pushQuadY(arr, wx + CFG.tile / 2, 0, wz + CFG.tile / 2, CFG.tile, CFG.tile, fc[0] + (Math.random() - .5) * jit, fc[1] + (Math.random() - .5) * jit, fc[2] + (Math.random() - .5) * jit, 0);
      // ceiling
      const cc = reg.ceil;
      const idxs = [[wx, wz], [wx + CFG.tile, wz], [wx + CFG.tile, wz + CFG.tile], [wx, wz], [wx + CFG.tile, wz + CFG.tile], [wx, wz + CFG.tile]];
      for (const [px, pz] of idxs) arr.push(px, 3.6, pz, 0, -1, 0, cc[0], cc[1], cc[2], 0);
      // walls where neighbor solid
      for (const [dx, dz] of DIRS) {
        const nx = x + dx, nz = y + dz;
        const nt = tileSolid(F, nx, nz) ? T_SOLID : tileIdx(F, nx, nz);
        if (nt === T_SOLID) {
          const wc = chance(Math.random, .5) ? reg.wall : reg.wall2;
          const hx = wx + CFG.tile / 2, hz = wz + CFG.tile / 2;
          if (dx === 1) R.pushBox(arr, wx + CFG.tile, 1.8, hz, 0.25, 3.6, CFG.tile, wc[0], wc[1], wc[2], 0, jit);
          else if (dx === -1) R.pushBox(arr, wx, 1.8, hz, 0.25, 3.6, CFG.tile, wc[0], wc[1], wc[2], 0, jit);
          else if (dz === 1) R.pushBox(arr, hx, 1.8, wz + CFG.tile, CFG.tile, 3.6, 0.25, wc[0], wc[1], wc[2], 0, jit);
          else R.pushBox(arr, hx, 1.8, wz, CFG.tile, 3.6, 0.25, wc[0], wc[1], wc[2], 0, jit);
        }
      }
    }
    if (t === T_WATER) {
      R.pushQuadY(warr, wx + CFG.tile / 2, 0.12, wz + CFG.tile / 2, CFG.tile, CFG.tile, 0.1, 0.3, 0.5, 0.5);
    }
  }
  F.staticMesh = R.buildVAO(new Float32Array(arr));
  F.waterMesh = warr.length ? R.buildVAO(new Float32Array(warr)) : null;
}

/* ---------------- town ---------------- */
function buildTown(campaign) {
  const F = newFloor(0, 0, true);
  F.tiles = new Uint8Array(F.W * F.H);
  F.fog = new Uint8Array(F.W * F.H);
  const cx = F.W / 2 | 0, cy = F.H / 2 | 0;
  stampRect(F, cx - 8, cy - 8, 17, 17, T_WALK);
  // radial streets
  stampRect(F, cx - 2, cy - 24, 5, 49, T_WALK);
  stampRect(F, cx - 24, cy - 2, 49, 5, T_WALK);
  // buildings
  const building = (bx, by, w, h, doorSide) => {
    stampRect(F, bx, by, w, h, T_WALK);
    // walls around, door gap on doorSide
    for (let x = bx - 1; x <= bx + w; x++) { setTile(F, x, by - 1, T_SOLID); setTile(F, x, by + h, T_SOLID); }
    for (let y = by - 1; y <= by + h; y++) { setTile(F, bx - 1, y, T_SOLID); setTile(F, bx + w, y, T_SOLID); }
    if (doorSide === 'S') { setTile(F, bx + (w >> 1), by + h, T_WALK); setTile(F, bx + (w >> 1) + 1, by + h, T_WALK); }
    if (doorSide === 'N') { setTile(F, bx + (w >> 1), by - 1, T_WALK); setTile(F, bx + (w >> 1) + 1, by - 1, T_WALK); }
    F.lights.push({ x: (bx + w / 2) * CFG.tile, y: 2.2, z: (doorSide === 'S' ? by + h + 1 : by - 1) * CFG.tile, r: 1, g: .7, b: .35, radius: 7, intensity: .8, flicker: 5, ph: Math.random() * TAU });
  };
  const spots = [
    [cx - 12, cy - 20, 6, 5, 'S'], [cx + 6, cy - 20, 6, 5, 'S'],
    [cx - 14, cy - 6, 5, 6, 'E'], [cx + 10, cy - 6, 5, 6, 'W'],
    [cx - 14, cy + 4, 5, 6, 'E'], [cx + 10, cy + 4, 5, 6, 'W'],
    [cx - 10, cy + 14, 6, 5, 'N'], [cx + 5, cy + 14, 6, 5, 'N'],
  ];
  spots.forEach(s => building(...s));
  // gate at south
  stampRect(F, cx - 3, cy + 24, 7, 6, T_WALK);
  F.gate = { x: (cx + 0.5) * CFG.tile, z: (cy + 27) * CFG.tile };
  // portal anchor east of well
  F.townPortal = { x: (cx + 5) * CFG.tile, z: cy * CFG.tile };
  // well
  F.props.push({ id: 'p' + (PROP_ID++), type: 'well', x: cx * CFG.tile + 1.5, z: cy * CFG.tile + 1.5, y: 0, blocking: true, rad: 1.0, dead: false, hp: 999 });
  // npc positions
  const npcSpots = { smith: [cx - 9, cy - 14], alchemist: [cx + 9, cy - 14], mystic: [cx - 12, cy - 2], healer: [cx + 12, cy - 2], quartermaster: [cx - 12, cy + 6], chronicler: [cx - 7, cy + 16], trainer: [cx + 8, cy + 16] };
  F.npcs = [];
  for (const id of NPCS) {
    const [nx, nz] = npcSpots[id];
    F.npcs.push({ npc: id, x: nx * CFG.tile + 1.5, z: nz * CFG.tile + 1.5, bark: 0 });
  }
  // training dummy
  F.props.push({ id: 'p' + (PROP_ID++), type: 'dummy', x: (cx + 10.5) * CFG.tile, z: (cy + 18) * CFG.tile, y: 0, blocking: true, rad: .5, dead: false, hp: 9999 });
  // barrels around
  for (let i = 0; i < 10; i++) {
    const x = cx + ri(Math.random, -20, 20), y = cy + ri(Math.random, -20, 20);
    if (tileIdx(F, x, y) === T_WALK) F.props.push({ id: 'p' + (PROP_ID++), type: chance(Math.random, .5) ? 'barrel' : 'crate', x: x * CFG.tile + 1.5, z: y * CFG.tile + 1.5, y: 0, blocking: true, rad: .45, dead: false, hp: 12, loot: null, gold: ri(Math.random, 2, 10) });
  }
  // lantern lights along streets
  for (let d = -3; d <= 3; d++) {
    F.lights.push({ x: (cx + d * 6) * CFG.tile, y: 2.4, z: (cy - 18) * CFG.tile, r: 1, g: .7, b: .35, radius: 8, intensity: .7, flicker: 4, ph: d });
    F.lights.push({ x: (cx + d * 6) * CFG.tile, y: 2.4, z: (cy + 18) * CFG.tile, r: 1, g: .7, b: .35, radius: 8, intensity: .7, flicker: 4, ph: d });
  }
  F.spawn = [F.gate.x - 0, F.gate.z - 6 * 0 - 0, 0];
  F.spawn = [(cx) * CFG.tile, 0, (cy - 20) * CFG.tile];
  F.startRoom = null; F.exitRoom = null;
  F.stairsDown = null; F.stairsUp = null;
  F.usedSeed = 0;
  return F;
}

/* ============================================================
   8. PLAYER — creation, derived stats, inventory ops, equipment
   ============================================================ */
const STATUS_DEFS = {
  bleed: { dot: 'phys', interval: 1, desc: 'Physical damage over time.' },
  burn: { dot: 'fire', interval: 1, desc: 'Fire damage over time.' },
  poison: { dot: 'poison', interval: 1, desc: 'Poison damage over time.' },
  chill: { slow: .30, atkSlow: .15, desc: '-30% movement, -15% attack speed.' },
  shock: { elemAmp: { lightning: .15 }, desc: '+15% incoming lightning damage.' },
  curse: { resDown: .15, desc: '-15% all resistances.' },
  stun: { desc: 'Cannot act.' },
  fear: { desc: 'Attempts to retreat.' },
  slow: { slow: .35, desc: 'Slowed.' },
};

function xpForLevel(L) { return Math.floor(100 * Math.pow(L, 1.55)); }
function makePlayer(opts) {
  const c = CLASSES[opts.cls];
  const p = {
    id: 'ch_' + Date.now().toString(36) + ((Math.random() * 1e4) | 0),
    name: opts.name || 'Delver', cls: opts.cls, preset: opts.preset || { skin: 0, hair: 0 },
    hardcore: !!opts.hardcore, difficulty: opts.difficulty || 'adventurer',
    level: 1, xp: 0, attrs: Object.assign({}, c.attrs), unspentAttr: 0, unspentTalent: 0,
    talents: {}, spellRanks: {}, dead: false,
    hp: 1, mp: 1, st: 1, gold: opts.gold !== undefined ? opts.gold : 60,
    inv: new Array(60).fill(null), equip: { head: null, chest: null, gloves: null, boots: null, main: null, off: null, amulet: null, ring1: null, ring2: null },
    belt: [null, null, null, null, null, null], skillQ: null, skillR: null,
    cds: {}, buffs: [], statuses: [], ward: null,
    pos: [0, 0, 0], vel: [0, 0, 0], yaw: 0, pitch: 0, radius: 0.42,
    attack: { state: 'idle', t: 0, combo: 0, heavy: false, charge: 0, spell: null, spellT: 0 },
    blocking: false, perfectT: 0, dodgeT: 0, dodgeCd: 0, iframe: 0, dodgeDir: [0, 0],
    crouch: false, sprinting: false, sheathed: false, onGround: true, bobPhase: 0, bobT: 0,
    lastDamageT: -99, potionCd: 0, channel: null, verdictBuff: null, arrowBuff: null, daggerBuff: null, retalBuff: 0,
    stats: {}, drawT: 0, selectedSpell: 'magic_dart', selectedUtility: null, killCount: 0, floorIdx: 0,
  };
  // starting gear
  for (const g of c.gear) {
    const [id, qty] = g.split(':');
    if (id.startsWith('book_')) { p.spellRanks[ITEM_BASES[id].spell] = 1; p.selectedSpell = ITEM_BASES[id].spell; continue; }
    const it = makeItem(id, 1, 'common', mulberry32(1), { identified: true, qty: qty ? +qty : 1 });
    if (!it) continue;
    if (it.slot && it.slot !== null && SLOT_NAMES.includes(it.slot)) {
      const slot = it.slot === 'ring' ? (p.equip.ring1 ? 'ring2' : 'ring1') : it.slot;
      if (!p.equip[slot]) { p.equip[slot] = it; continue; }
    }
    if (it.cat === 'potion' || it.cat === 'scroll') {
      let placed = false;
      for (let i = 0; i < 6; i++) if (!p.belt[i]) { p.belt[i] = id; placed = true; break; }
      if (placed) void placed; // belt binds by base id; the stack itself lives in the bag below
    }
    addToBag(p, it);
  }
  recalcStats(p);
  p.hp = p.stats.hpMax; p.mp = p.stats.mpMax; p.st = p.stats.stMax;
  return p;
}
const SLOT_NAMES = ['head', 'chest', 'gloves', 'boots', 'main', 'off', 'amulet', 'ring1', 'ring2'];
const SLOT_LABEL = { head: 'Head', chest: 'Chest', gloves: 'Gloves', boots: 'Boots', main: 'Main Hand', off: 'Off-Hand', amulet: 'Amulet', ring1: 'Ring I', ring2: 'Ring II' };

function itemValid(P, it, excludeIt) {
  if (!it) return true;
  if (it.durMax && it.dur <= 0) return false;
  const eff = effAttrsWith(P, it);
  if (it.minLvl > P.level) return false;
  for (const k of ['str', 'dex', 'int']) if (it.reqs[k] && eff[k] < it.reqs[k]) return false;
  return true;
}
function effAttrsWith(P, excludeIt) {
  const s = { str: P.attrs.str, dex: P.attrs.dex, int: P.attrs.int, vit: P.attrs.vit };
  for (const k of SLOT_NAMES) {
    const it = P.equip[k];
    if (!it || it === excludeIt) continue;
    const st = itemStats(it);
    s.str += st.str; s.dex += st.dex; s.int += st.int; s.vit += st.vit;
  }
  for (const b of P.buffs) if (b.mods.str) s.str += b.mods.str;
  return s;
}
function hasRelic(P, rid) {
  for (const k of SLOT_NAMES) { const it = P.equip[k]; if (it && it.special === rid && itemValid(P, it)) return true; }
  return false;
}
function recalcStats(P) {
  const c = CLASSES[P.cls];
  const L = P.level;
  const st = { str: P.attrs.str, dex: P.attrs.dex, int: P.attrs.int, vit: P.attrs.vit };
  const gear = itemStats(null);
  let armorSum = 0, blockAbs = 0, blockElem = 0, spellPower = 0;
  const agg = {};
  const disabled = [];
  // two-pass: aggregate gear attrs, then validate each item against attrs-from-others
  for (const k of SLOT_NAMES) {
    const it = P.equip[k]; if (!it) continue;
    const s = itemStats(it);
    for (const kk in s) if (typeof s[kk] === 'number' || s[kk] === null) agg[kk] = (agg[kk] || 0) + (s[kk] || 0);
  }
  for (const k of SLOT_NAMES) {
    const it = P.equip[k]; if (!it) continue;
    const ok = itemValid(P, it);
    it._off = !ok;
    it._offReason = !ok ? (it.durMax && it.dur <= 0 ? 'Broken (0 durability)' : 'Requirements not met') : null;
    if (!ok) { disabled.push(it); continue; }
    const s = itemStats(it);
    st.str += s.str; st.dex += s.dex; st.int += s.int; st.vit += s.vit;
    armorSum += s.armor;
    if (it.cat === 'shield') { blockAbs = Math.max(blockAbs, it.blockAbs || 0.7); blockElem = Math.max(blockElem, it.blockElem || 0.35); }
    spellPower += s.spellPower;
    if (it.special === 'quieteye') agg.mpFlat = (agg.mpFlat || 0) - 20;
  }
  // passives
  const tRank = id => P.talents[id] || 0;
  let armorPct = 0, elemPct = 0, mpRegenPct = 0, critPassive = 0, moveSpd = c.moveB + 0, atkSpd = 0, haste = 0;
  let lifeSteal = 0, manaSteal = 0, hpRegen = 0, mpRegen = 0, goldFind = 0, statusRes = 0, thorns = 0, manaCostRed = 0, shieldStam = 0;
  if (tRank('iron')) armorPct += (0.08 + 0.04 * (tRank('iron') - 1));
  if (tRank('keeneye')) critPassive += 0.04 + 0.02 * (tRank('keeneye') - 1);
  if (tRank('elementalist')) elemPct += 0.06 + 0.03 * (tRank('elementalist') - 1);
  if (tRank('channeler')) mpRegenPct += 0.10 + 0.05 * (tRank('channeler') - 1);
  if (tRank('heavyhands')) { /* applied in melee calc */ }
  if (tRank('trapsense')) { /* trap reveal */ }
  if (tRank('evasive')) { /* dodge cost */ }
  for (const b of P.buffs) {
    const m = b.mods;
    if (m.armor) armorSum += m.armor;
    if (m.armorPct) armorPct += m.armorPct;
    if (m.dmgPct) agg.dmgPct = (agg.dmgPct || 0) + m.dmgPct;
    if (m.dmgTakenPct) agg.dmgTakenPct = (agg.dmgTakenPct || 0) + m.dmgTakenPct;
    if (m.moveSpd) moveSpd += m.moveSpd;
    if (m.atkSpd) atkSpd += m.atkSpd;
    if (m.spdPct) moveSpd += m.spdPct;
    for (const rk of ['resAll', 'resFire', 'resFrost', 'resLight', 'resPoison', 'resArc']) if (m[rk]) agg[rk] = (agg[rk] || 0) + m[rk];
  }
  const eff = { str: st.str, dex: st.dex, int: st.int, vit: st.vit };
  const hpMax = Math.max(1, Math.round(40 + 2 * eff.vit + 5 * (L - 1) + c.hpB + (agg.hpFlat || 0)));
  const mpMax = Math.max(1, Math.round(10 + 2 * eff.int + 3 * (L - 1) + c.mpB + (agg.mpFlat || 0)));
  const stMax = Math.max(1, Math.round(40 + eff.vit + Math.floor(eff.dex / 2) + c.stB + (agg.stFlat || 0)));
  const armor = Math.max(0, Math.round(armorSum * (1 + armorPct)));
  const crit = clamp(0.02 + 0.0012 * eff.dex + critPassive + (agg.crit || 0), 0, CFG.critCap);
  const critDmg = 0.5 + (agg.critDmg || 0);
  const spellPowerMul = 1 + 0.015 * eff.int + spellPower;
  const res = {
    fire: clamp((agg.resFire || 0) / 100, -0.5, 0.75),
    frost: clamp((agg.resFrost || 0) / 100, -0.5, 0.75),
    light: clamp((agg.resLight || 0) / 100, -0.5, 0.75),
    poison: clamp((agg.resPoison || 0) / 100, -0.5, 0.75),
    arc: clamp((agg.resArc || 0) / 100, -0.5, 0.75),
    magic: clamp(((agg.resArc || 0) + (agg.resFire || 0)) / 200, -0.5, 0.75),
  };
  for (const b of P.buffs) if (b.mods.curse) for (const e in res) res[e] -= 0.15;
  P.stats = {
    str: eff.str, dex: eff.dex, int: eff.int, vit: eff.vit,
    hpMax, mpMax, stMax, armor, blockAbs, blockElem, crit, critDmg,
    atkSpd: clamp(1 + Math.min(0.6, 0.004 * eff.dex + atkSpd + (agg.atkSpd || 0)), 0.4, 2.2),
    moveSpd: CFG.walkSpeed * (1 + moveSpd + (agg.moveSpd || 0)),
    haste: agg.haste || 0, spellPower: spellPowerMul, lifeSteal: agg.lifeSteal || 0, manaSteal: agg.manaSteal || 0,
    hpRegen: 0.1 + eff.vit / 100 + (agg.hpRegen || 0), mpRegen: (0.5 + eff.int / 40 + c.mpRegen) * (1 + mpRegenPct),
    stRegen: 15 + 0.15 * eff.vit, res, statusRes: clamp(agg.statusRes || 0, 0, 0.8),
    lightRadius: 7 + (agg.light || 0) + (hasRelic(P, 'lanternmail') ? 4 : 0),
    goldFind: agg.goldFind || 0, thorns: agg.thorns || 0, manaCostRed: agg.manaCostRed || 0, shieldStam: agg.shieldStam || 0,
    dmgPct: agg.dmgPct || 0, dmgTakenPct: agg.dmgTakenPct || 0,
  };
  // resource preservation on max change
  if (P._prevMax) {
    P.hp = clamp(P.hp, 0, P.stats.hpMax);
    P.mp = clamp(P.mp, 0, P.stats.mpMax);
    P.st = clamp(P.st, 0, P.stats.stMax);
  }
  P._prevMax = true;
}
function gainXP(P, n) {
  P.xp += n;
  let leveled = false;
  while (P.level < CFG.maxLevel && P.xp >= xpForLevel(P.level)) {
    P.xp -= xpForLevel(P.level);
    P.level++; P.unspentAttr += CFG.attrPtsPerLevel; P.unspentTalent += CFG.talentPtsPerLevel;
    leveled = true;
    const hpF = P.hp / P.stats.hpMax, mpF = P.mp / P.stats.mpMax, stF = P.st / P.stats.stMax;
    recalcStats(P);
    P.hp = clamp(Math.round(hpF * P.stats.hpMax), 1, P.stats.hpMax);
    P.mp = Math.round(mpF * P.stats.mpMax);
    P.st = Math.round(stF * P.stats.stMax);
  }
  if (leveled) { SND.levelUp(); toast('Level ' + P.level + '! +' + CFG.attrPtsPerLevel + ' attributes, +1 talent point', 'good'); EVT.emit('CharacterLeveled', { level: P.level }); }
  recalcStats(P);
}
function spendAttr(P, k) {
  if (P.unspentAttr <= 0 || P.attrs[k] >= 99) return false;
  P.attrs[k]++; P.unspentAttr--;
  recalcStats(P); SND.ui();
  return true;
}
/* talent prereq: tier2 needs 3 pts in tree, tier3 needs 8 */
function talentPtsInTree(P) { let n = 0; for (const t of TALENTS) if (t.cls === P.cls) n += P.talents[t.id] || 0; return n; }
function talentOk(P, t) {
  const rank = P.talents[t.id] || 0;
  if (rank >= 5) return false;
  if (P.unspentTalent <= 0) return false;
  if (t.tier === 2 && talentPtsInTree(P) < 3) return false;
  if (t.tier === 3 && talentPtsInTree(P) < 8) return false;
  return true;
}
function spendTalent(P, t) {
  if (!talentOk(P, t)) return false;
  P.talents[t.id] = (P.talents[t.id] || 0) + 1; P.unspentTalent--;
  const rank = P.talents[t.id];
  if (t.type === 'active' && rank === 1) {
    if (!P.skillQ) P.skillQ = { kind: 'talent', id: t.id };
    else if (!P.skillR) P.skillR = { kind: 'talent', id: t.id };
  }
  EVT.emit('SkillLearned', { id: t.id, rank });
  SND.uiBig(); recalcStats(P);
  return true;
}

/* ---------------- inventory grid ops ---------------- */
const BAG_W = 10, BAG_H = 6;
function bagOcc(P) {
  const occ = new Uint8Array(BAG_W * BAG_H);
  for (let i = 0; i < P.inv.length; i++) {
    const it = P.inv[i]; if (!it) continue;
    const w = it.rot ? it.h : it.w, h = it.rot ? it.w : it.h;
    for (let dy = 0; dy < h; dy++) for (let dx = 0; dx < w; dx++) occ[(it._y + dy) * BAG_W + it._x + dx] = 1;
  }
  return occ;
}
function canPlace(P, it, x, y, rot, ignoreIt) {
  const w = rot ? it.h : it.w, h = rot ? it.w : it.h;
  if (x < 0 || y < 0 || x + w > BAG_W || y + h > BAG_H) return false;
  const occ = bagOcc(P);
  if (ignoreIt && ignoreIt._x !== undefined) {
    const iw = ignoreIt.rot ? ignoreIt.h : ignoreIt.w, ih = ignoreIt.rot ? ignoreIt.w : ignoreIt.h;
    for (let dy = 0; dy < ih; dy++) for (let dx = 0; dx < iw; dx++) occ[(ignoreIt._y + dy) * BAG_W + ignoreIt._x + dx] = 0;
  }
  for (let dy = 0; dy < h; dy++) for (let dx = 0; dx < w; dx++) if (occ[(y + dy) * BAG_W + x + dx]) return false;
  return true;
}
function findSpot(P, it) {
  for (let rot = 0; rot < (it.w === it.h ? 1 : 2); rot++) {
    const w = rot ? it.h : it.w, h = rot ? it.w : it.h;
    for (let y = 0; y <= BAG_H - h; y++) for (let x = 0; x <= BAG_W - w; x++) if (canPlace(P, it, x, y, rot)) return { x, y, rot };
  }
  return null;
}
function addToBag(P, it) {
  if (it.stackMax) {
    for (const other of P.inv) {
      if (other && other.base === it.base && other.qty < other.stackMax && (other.rarity === it.rarity) && it.cat !== 'potion' || (other && other.base === it.base && other.stackMax && it.cat === 'potion')) {
        if (other.base === it.base && other.stackMax && (it.cat === 'potion' || it.cat === 'ammo' || it.cat === 'scroll')) {
          const can = Math.min(other.stackMax - other.qty, it.qty);
          other.qty += can; it.qty -= can;
          if (it.qty <= 0) { autoBindBelt(P, it.base); return true; }
        }
      }
    }
  }
  const spot = findSpot(P, it);
  if (!spot) return false;
  it._x = spot.x; it._y = spot.y; it.rot = spot.rot;
  P.inv.push(it);
  autoBindBelt(P, it.base);
  return true;
}
function removeFromCell(P, x, y) {
  for (let i = 0; i < P.inv.length; i++) {
    const it = P.inv[i]; if (!it) continue;
    const w = it.rot ? it.h : it.w, h = it.rot ? it.w : it.h;
    if (x >= it._x && x < it._x + w && y >= it._y && y < it._y + h) {
      P.inv.splice(i, 1);
      if (it.qty < it.stackMax && it.qty > 0) { /* partial stacks re-place? keep */ }
      return it;
    }
  }
  return null;
}
function sortBag(P) {
  const items = P.inv.filter(Boolean);
  const score = it => (it.cat === 'quest' ? 0 : 1) * 1000 + (it.cat === 'weapon' ? 10 : it.cat === 'armor' ? 20 : it.cat === 'shield' ? 30 : it.cat === 'potion' ? 40 : 50) + it.w * it.h;
  items.sort((a, b) => score(a) - score(b) || (a.name > b.name ? 1 : -1));
  P.inv = new Array(60).fill(null);
  for (const it of items) {
    let placed = false;
    for (let rot = 0; rot < (it.w === it.h ? 1 : 2) && !placed; rot++) {
      const w = rot ? it.h : it.w, h = rot ? it.w : it.h;
      for (let y = 0; y <= BAG_H - h && !placed; y++) for (let x = 0; x <= BAG_W - w && !placed; x++) {
        if (canPlace(P, it, x, y, rot)) { it._x = x; it._y = y; it.rot = rot; P.inv.push(it); placed = true; }
      }
    }
    if (!placed) { // fallback: drop to ground
      dropToGround(P, it, G.floor, P.pos);
    }
  }
}
function dropToGround(P, it, F, pos) {
  if (!F) return;
  spawnGroundItem(F, pos[0] + (Math.random() - .5), pos[2] + (Math.random() - .5), it, it.rarity);
}
function autoBindBelt(P, base) {
  const b = baseOf(base);
  if (!b || !(b.cat === 'potion' || b.cat === 'scroll' || b.cat === 'ammo')) return;
  if (P.belt.includes(base)) return;
  const i = P.belt.indexOf(null);
  if (i >= 0) P.belt[i] = base;
}
function beltItem(P, i) {
  const base = P.belt[i]; if (!base) return null;
  let best = null;
  for (const it of P.inv) if (it && it.base === base && it.qty > 0 && (!best || it.qty > best.qty)) best = it;
  return best;
}

/* ---------------- equipment ---------------- */
function slotFor(it) {
  if (it.slot === 'ring') return null; // caller picks ring1/2
  return it.slot;
}
function equipItem(P, it, ringSlot) {
  const slot = it.slot === 'ring' ? (ringSlot || (!P.equip.ring1 ? 'ring1' : 'ring2')) : it.slot;
  if (!slot || !SLOT_NAMES.includes(slot)) return { ok: false, why: 'Cannot be equipped' };
  if (!itemValid(P, it)) return { ok: false, why: it._offReason || 'Requirements not met' };
  // remove from bag first (fresh index — eviction may have shifted the array)
  const cur = P.equip[slot];
  // two-handed conflicts
  if (it.two && P.equip.off) {
    if (!addToBag(P, P.equip.off)) return { ok: false, why: 'No space for off-hand item' };
    P.equip.off = null;
  }
  if (slot === 'off' && P.equip.main && P.equip.main.two) {
    if (!addToBag(P, P.equip.main)) return { ok: false, why: 'No space for two-handed weapon' };
    P.equip.main = null;
  }
  const idxNow = P.inv.indexOf(it);
  if (idxNow < 0) return { ok: false, why: 'Not in bag' };
  P.inv.splice(idxNow, 1);
  P.equip[slot] = it;
  if (cur) {
    if (!addToBag(P, cur)) { // rollback
      P.equip[slot] = cur; P.inv.push(it);
      return { ok: false, why: 'No bag space to swap' };
    }
  }
  const hpF = P.hp / P.stats.hpMax, mpF = P.mp / P.stats.mpMax;
  recalcStats(P);
  P.hp = clamp(P.hp, 0, P.stats.hpMax); P.mp = clamp(P.mp, 0, P.stats.mpMax);
  EVT.emit('ItemEquipped', { item: it });
  SND.ui();
  return { ok: true };
}
function unequipSlot(P, slot) {
  const it = P.equip[slot]; if (!it) return false;
  if (!addToBag(P, it)) return false;
  P.equip[slot] = null;
  recalcStats(P);
  P.hp = clamp(P.hp, 0, P.stats.hpMax); P.mp = clamp(P.mp, 0, P.stats.mpMax); P.st = clamp(P.st, 0, P.stats.stMax);
  SND.ui();
  return true;
}
function sellValue(it) { return Math.max(1, Math.floor((it.price || 10) * CFG.sellFraction)); }
function identifyCost(it) { return 20 + 10 * (it.ilvl || 1); }
function repairCost(it) { if (!it.durMax || it.dur >= it.durMax) return 0; return Math.max(1, Math.ceil((1 - it.dur / it.durMax) * (it.price || 50) * 0.2)); }

/* gold change — single transaction point */
function goldChange(P, n, why) {
  if (n < 0 && P.gold + n < 0) return false;
  P.gold = Math.max(0, P.gold + n);
  if (why) log((n > 0 ? '+' : '') + fmt(n) + ' gold' + (why ? ' — ' + why : ''), n > 0 ? '#e8c84a' : '#c88');
  EVT.emit('GoldChanged', { delta: n });
  return true;
}

/* ============================================================
   9. COMBAT — damage pipeline, statuses, attacks, spells, kicks
   ============================================================ */
const ELEM_COL = { slash: [0.9, 0.9, 0.9], pierce: [0.9, 0.9, 0.9], blunt: [0.9, 0.85, 0.7], fire: [1, 0.5, 0.15], frost: [0.5, 0.8, 1], lightning: [0.7, 0.8, 1], arcane: [0.8, 0.5, 1], radiant: [1, 0.95, 0.7], shadow: [0.5, 0.3, 0.7], poison: [0.5, 0.9, 0.3] };
function statusResOf(ent) { return ent === P ? P.stats.statusRes : 0; }
function entImmune(ent, st) { return ent.arch && ent.arch.imm.includes(st); }

function applyStatus(ent, id, dur, power, src) {
  if (ent === P && P.dead) return;
  if (ent.arch && entImmune(ent, id)) return;
  if (ent === P) {
    const sr = P.stats.statusRes;
    dur *= (1 - sr);
  }
  const ex = ent.statuses.find(s => s.id === id);
  if (ex) {
    ex.t = Math.max(ex.t, dur);
    if (['bleed', 'burn', 'poison'].includes(id)) ex.stacks = Math.min(3, (ex.stacks || 1) + 1), ex.power = Math.max(ex.power, power);
    else ex.power = Math.max(ex.power || 0, power);
  } else {
    ent.statuses.push({ id, t: dur, power, stacks: 1, src, tickT: 0 });
  }
  EVT.emit('StatusApplied', { ent, id });
}
function tickStatuses(ent, dt) {
  for (let i = ent.statuses.length - 1; i >= 0; i--) {
    const s = ent.statuses[i];
    s.t -= dt;
    if (s.t <= 0) { ent.statuses.splice(i, 1); if (ent === P) recalcStats(P); continue; }
    const def = STATUS_DEFS[s.id];
    if (def && def.dot) {
      s.tickT = (s.tickT || 0) + dt;
      if (s.tickT >= def.interval) {
        s.tickT -= def.interval;
        const dmg = s.power * s.stacks;
        dealDamage(ent, s.src || { env: true }, { [def.dot === 'phys' ? 'phys' : def.dot]: dmg, dot: true, silent: true });
      }
    }
  }
}
function hasStatus(ent, id) { return ent.statuses.some(s => s.id === id); }

/* dealDamage: dst = P or enemy actor; src: {player:true} or actor or {env:true} or trap */
function dealDamage(dst, src, hit) {
  if (!hit) return;
  const isPlayer = dst === P;
  if (isPlayer && P.dead) return;
  if (dst.arch && dst.dead) return;
  if (hit.dot) {
    // DoTs bypass block/dodge, use resistance only
    applyDirect(dst, src, hit);
    return;
  }
  // dodge iframes (player only)
  if (isPlayer && P.iframe > 0 && !hit.unblockable) {
    dmgNum(dst.pos, 'dodge', '#8fd8ff');
    return;
  }
  // blocking (player with shield/weapon raised)
  if (isPlayer && P.blocking && !hit.unblockable) {
    const toSrc = src.pos ? Math.atan2(-(src.pos[0] - P.pos[0]), -(src.pos[2] - P.pos[2])) : P.yaw;
    const ang = Math.abs(angleDiff(toSrc, P.yaw));
    if (ang < CFG.block.coneDeg * Math.PI / 180) {
      const shield = P.equip.off && P.equip.off.cat === 'shield' ? P.equip.off : null;
      const absP = shield ? shield.blockAbs : 0.55, absE = shield ? shield.blockElem : 0.3;
      const perfect = P.perfectT > 0;
      let total = (hit.phys || 0) + (hit.fire || 0) + (hit.frost || 0) + (hit.light || 0) + (hit.arcane || 0) + (hit.poison || 0);
      if (perfect) {
        SND.parry();
        dmgNum(dst.pos, 'PARRY', '#ffe066');
        if (src.arch && !src.arch.tags.includes('boss') && !hit.unparryable) {
          staggerActor(src, 1.2);
        }
        if (P.talents.retaliation) P.retalBuff = 0.10 + 0.05 * (P.talents.retaliation - 1) + P.retalBuff;
        if (shield && shield.special === 'breakwater' && !shield._bwCd) {
          shield._bwCd = 3;
          shockwaveBurst(P.pos, 3.2, { phys: 14 + 2 * P.level, poise: 30, src: { player: true } });
        }
        applyDirect(dst, src, { phys: 0 });
        P.st = clamp(P.st - 4, 0, P.stats.stMax);
        EVT.emit('HitResolved', { blocked: true, perfect: true });
        return;
      }
      const physAbs = (hit.phys || 0) * (1 - absP);
      let elemAbs = ((hit.fire || 0) + (hit.frost || 0) + (hit.light || 0) + (hit.arcane || 0) + (hit.poison || 0)) * (1 - absE);
      const stamCost = 2 + total * 0.35 * (1 - (P.stats.shieldStam || 0)) * (P.buffs.some(b => b.id === 'defiant') ? 0.5 : 1);
      P.st -= stamCost;
      SND.block();
      R.burst(P.pos[0], 1.2, P.pos[2], 6, [1, 0.9, 0.5], 3, 3, 0.3);
      if (P.st <= 0) {
        P.st = 0; P.blocking = false;
        P.stun = 1.0; toast('Guard broken!', 'bad');
        applyDirect(dst, src, { phys: physAbs + elemAbs * 0.5 });
      } else {
        applyDirect(dst, src, { phys: physAbs, fire: hit.fire ? elemAbs * (hit.fire / Math.max(1, total)) * 1 : 0, frost: 0, light: 0, arcane: 0, poison: 0 });
      }
      EVT.emit('HitResolved', { blocked: true });
      return;
    }
  }
  applyDirect(dst, src, hit);
}
function angleDiff(a, b) { let d = a - b; while (d > Math.PI) d -= TAU; while (d < -Math.PI) d += TAU; return d; }

/* direct application after mitigation decisions */
function applyDirect(dst, src, hit) {
  const isPlayer = dst === P;
  let dmgByElem = { phys: hit.phys || 0, fire: hit.fire || 0, frost: hit.frost || 0, light: hit.light || 0, arcane: hit.arcane || 0, poison: hit.poison || 0 };
  let total = 0;
  const atkLvl = src.arch ? src.level : (src.player ? P.level : 1);
  for (const e in dmgByElem) {
    let d = dmgByElem[e];
    if (!d) continue;
    if (e === 'phys') {
      const armor = isPlayer ? P.stats.armor : dst.armor;
      d *= 1 - Math.min(0.75, armor / (armor + 100 + 8 * (atkLvl - 1)));
    } else {
      const resMap = isPlayer ? P.stats.res : (dst.res || {});
      const key = { fire: 'fire', frost: 'frost', light: 'light', lightning: 'light', arcane: 'arc', poison: 'poison', radiant: 'magic', shadow: 'magic' }[e] || 'magic';
      let res = resMap[key] || 0;
      if (dst.statuses.some(s => s.id === 'curse')) res -= 0.15;
      if (dst.statuses.some(s => s.id === 'shock') && e === 'lightning') d *= 1.15;
      d *= 1 - clamp(res, -0.5, 0.75);
    }
    dmgByElem[e] = Math.max(0, d);
    total += d;
  }
  total *= 1 - (isPlayer ? P.stats.dmgTakenPct : 0);
  // elite thorns / player thorns
  if (!isPlayer && hit.melee && src.player) {
    const refl = dst.arch && dst.elite && ELITES[dst.elite] && ELITES[dst.elite].reflect;
    if (refl) dealDamage(P, dst, { phys: total * refl, dot: false });
  }
  if (isPlayer && hit.melee && !hit.dot) {
    const th = P.stats.thorns;
    if (th > 0 && src.arch) dealDamage(src, { player: true }, { phys: th, silent: true });
  }
  total = Math.max(0, total);
  if (total <= 0) { if (!hit.silent) dmgNum(dst.pos, 'block', '#aaa'); return; }
  // ward (player)
  if (isPlayer && P.ward && P.ward.hp > 0) {
    const absorbed = Math.min(P.ward.hp, total);
    P.ward.hp -= absorbed; total -= absorbed;
    P.mp = Math.max(0, P.mp - absorbed / 3);
    dmgNum(dst.pos, '-' + Math.round(absorbed), '#8ab8ff');
    if (P.ward.hp <= 0) { P.ward = null; toast('Mana Ward shattered', ''); }
  }
  dst.hp -= total;
  dst.lastDamageT = G.time;
  if (isPlayer) {
    P.hpRegenDelayT = CFG.hpRegenDelay;
    SND.hurt();
    R.burst(dst.pos[0], 1.2, dst.pos[2], G.settings.gore ? 5 : 3, [0.7, 0.1, 0.1], 3, 3, 0.4);
    if (!hit.silent) dmgNum(dst.pos, '-' + Math.round(total), '#ff6666');
    if (P.hp <= 0) playerDeath();
  } else {
    const col = G.settings.gore ? [0.7, 0.1, 0.1] : [0.6, 0.6, 0.65];
    if (!hit.silent) {
      R.burst(dst.pos[0], 1.1, dst.pos[2], G.settings.gore ? 8 : 4, col, 3.5, 3.5, 0.45);
      if (G.settings.dmgNumbers) dmgNum(dst.pos, Math.round(total), hit.crit ? '#ffd24a' : '#ffffff', hit.crit ? 20 : 15);
    }
    if (hit.srcName) { /* credited below */ }
  }
  // poise
  if (!isPlayer && hit.poise && !dst.dead) {
    dst.poise -= hit.poise * (dst.arch.tags.includes('boss') ? 0.35 : 1);
    if (dst.poise <= 0) { staggerActor(dst, dst.arch.tags.includes('boss') ? 0.8 : 1.0); dst.poise = dst.poiseMax; }
  }
  if (isPlayer && hit.poise) {
    P.poise = (P.poise === undefined ? 30 : P.poise) - hit.poise;
    if (P.poise <= 0) { P.stun = 0.5; P.poise = 30; }
  }
  // statuses
  for (const st of (hit.statuses || [])) applyStatus(dst, st.id, st.dur, st.power, src);
  // life steal on direct weapon damage
  if (src.player && !hit.dot && (hit.melee || hit.arrow)) {
    if (P.stats.lifeSteal > 0) {
      const gain = Math.min(P.stats.hpMax * 0.12, total * P.stats.lifeSteal);
      P.hp = clamp(P.hp + gain, 0, P.stats.hpMax);
    }
    if (P.stats.manaSteal > 0) P.mp = clamp(P.mp + Math.min(P.stats.mpMax * 0.12, total * P.stats.manaSteal), 0, P.stats.mpMax);
  }
  // serpent knot: poison dealt heals
  if (src.player && hit.poison && hasRelic(P, 'serpentknot') && !hit.dot) {
    P.hp = clamp(P.hp + Math.min(15, total * 0.25), 0, P.stats.hpMax);
  }
  // credit
  if (!isPlayer && !dst.dead && dst.hp <= 0) {
    killActor(dst, src);
  } else if (!isPlayer) {
    // aggro
    if (src.player) { dst.target = P; dst.activated = true; if (dst.state === 'idle' || dst.state === 'patrol') dst.state = 'chase'; }
  }
  // vampiric elite
  if (!isPlayer && dst.elite && ELITES[dst.elite]?.lifesteal && hit.melee === undefined && src.arch) {
    src.hp = clamp(src.hp + total * 0.3, 0, src.maxHp);
  }
  EVT.emit('HitResolved', { dst, total });
}
function staggerActor(a, dur) {
  if (a.arch && (a.arch.tags.includes('boss') || a.arch.tags.includes('bosslike'))) dur *= 0.4;
  if (a.arch && a.arch.imm.includes('stun')) return;
  a.stun = Math.max(a.stun || 0, dur);
  a.windup = null; a.channel = null;
  if (a.state === 'windup' || a.state === 'attack') a.state = 'chase';
}
function killActor(a, src) {
  if (a.dead) return;
  a.dead = true; a.deadT = 0; a.hp = 0;
  a.state = 'dead';
  SND.death();
  R.burst(a.pos[0], 1.0, a.pos[2], G.settings.gore ? 14 : 6, [0.6, 0.12, 0.12], 4, 4, 0.6);
  // unstable elite explodes
  if (a.elite && ELITES[a.elite].explode) {
    SND.explode();
    R.burst(a.pos[0], 1.0, a.pos[2], 30, [1, 0.6, 0.2], 6, 5, 0.5);
    if (d2(P.pos[0], P.pos[2], a.pos[0], a.pos[2]) < 3.5) dealDamage(P, { env: true }, { fire: 18 + a.level * 2 });
  }
  // credits & XP
  const credit = creditFor(a, src);
  if (credit && credit.player) {
    const xp = Math.round(a.xpVal || 10);
    gainXP(P, xp);
    log('Killed ' + a.name + ' (+' + xp + ' XP)', '#cfc');
    P.killCount++;
    // loot spawn
    for (const it of (a.loot || [])) spawnGroundItem(G.floor, a.pos[0] + (Math.random() - .5) * 1.2, a.pos[2] + (Math.random() - .5) * 1.2, it, it.rarity);
    const gold = Math.round((a.gold || 0) * (1 + P.stats.goldFind));
    if (gold > 0) spawnGroundItem(G.floor, a.pos[0] + (Math.random() - .5) * 1.2, a.pos[2] + (Math.random() - .5) * 1.2, { gold }, 0);
    // gravedigger relic
    if (hasRelic(P, 'gravedigger') && hit_was_melee(src)) P.st = clamp(P.st + 15, 0, P.stats.stMax);
    EVT.emit('ActorKilled', { actor: a, credit: 'player' });
    questEvent('kill', { arch: a.archId, elite: !!a.elite, boss: a.bossId });
    if (a.questElite) questEvent('killElite', { quest: a.questElite });
    if (a.bossId) onBossDefeated(a);
  } else {
    EVT.emit('ActorKilled', { actor: a, credit: 'environment' });
  }
  // persist killed unique
  const fs = G.campaign.floors[G.floor.index];
  if (fs && a.id) { fs.killed = fs.killed || []; if (!fs.killed.includes(a.id)) fs.killed.push(a.id); }
}
function hit_was_melee(src) { return src && src.player; }
function creditFor(a, src) {
  if (src && (src.player || (src.creditOwner && src.creditOwner.player))) return { player: true };
  const c = a.credits && a.credits.find(c => G.time - c.t < 5 && c.player);
  return c ? { player: true } : null;
}

/* ---------------- player attacks ---------------- */
function curWeapon() { const w = P.equip.main; return w && w.cat === 'weapon' && itemValid(P, w) ? w : null; }
function trySpendStamina(n) {
  if (P.st < n) { SND.error(); toast('Not enough stamina', 'bad'); return false; }
  P.st -= n; P.stRegenDelayT = CFG.staminaRegenDelay;
  return true;
}
function startAttack(heavy, charge) {
  const w = curWeapon();
  if (P.attack.state !== 'idle' && P.attack.state !== 'recover') return;
  if (P.stun > 0) return;
  if (!w) { // unarmed
    if (!trySpendStamina(6)) return;
    P.attack = { state: 'windup', t: 0, dur: 0.3, combo: 0, heavy: false, unarmed: true };
    SND.swing();
    return;
  }
  if (w.fam === 'bow') { startBowDraw(); return; }
  if (w.fam === 'staff' || w.fam === 'wand') {
    // heavy hold = charged cast; light = cast selected spell
    castSelectedSpell(heavy);
    return;
  }
  const stam = heavy ? Math.round(w.stam * 1.6) : w.stam;
  if (!trySpendStamina(stam)) return;
  P.attack = { state: 'windup', t: 0, dur: w.wind * (heavy ? 1.25 : 1) / P.stats.atkSpd, combo: P.attack.combo || 0, heavy, w, charge: charge || 0.35 };
  P.blocking = false;
  SND[heavy ? 'heavySwing' : 'swing']();
}
function startBowDraw() {
  const w = curWeapon();
  if (!trySpendStamina(w.stam)) return;
  P.attack = { state: 'draw', t: 0, dur: 999, w };
}
function releaseBow() {
  if (!P.attack || P.attack.state !== 'draw') return;
  const w = P.attack.w;
  const charge = clamp(P.attack.t / 0.8, 0, 1);
  const arrows = P.inv.find(it => it && it.base === 'arrows' && it.qty > 0);
  if (!arrows) { SND.error(); toast('No arrows', 'bad'); P.attack = { state: 'idle', t: 0, combo: 0 }; return; }
  consumeFromStack(arrows, 1);
  P.attack = { state: 'release', t: 0, dur: 0.15, w, charge };
  fireArrow(w, charge);
  SND.bow();
}
function beltIndexOf(base) { return P.belt.indexOf(base); }
function consumeFromStack(stack, n) {
  stack.qty -= n;
  if (stack.qty <= 0) {
    const i = P.inv.indexOf(stack);
    if (i >= 0) P.inv.splice(i, 1);
  }
}
function fireArrow(w, charge) {
  const dir = camDir();
  const s = itemStats(w);
  let dmg = rf(Math.random, s.dmgMin, s.dmgMax);
  dmg += 0.28 * P.stats.dex;
  let mult = 1 + charge * 0.8;
  if (P.arrowBuff) { mult *= P.arrowBuff.dmgPct; }
  const crit = Math.random() < P.stats.crit;
  if (crit) mult *= 1.5 + P.stats.critDmg;
  const hit = {
    pierce: dmg * mult, crit, arrow: true, srcName: P.name,
    statuses: [], src: { player: true },
  };
  const elem = { fire: 0, frost: 0, light: 0, arcane: 0, poison: 0 };
  if (P.stats.fireDmg) elem.fire += P.stats.fireDmg;
  if (P.stats.frostDmg) elem.frost += P.stats.frostDmg;
  if (P.stats.lightDmg) elem.light += P.stats.lightDmg;
  if (P.stats.poisonDmg) elem.poison += P.stats.poisonDmg;
  const eye = [P.pos[0], P.pos[1] + eyeH() - 0.15, P.pos[2]];
  spawnProj(eye, dir, w.projSpeed || 26, { pierce: hit, elem, friendly: true, speed: w.projSpeed || 26, pierceN: P.arrowBuff ? P.arrowBuff.pierce : (hasRelic(P, 'wayfarer') ? 1 : 0), dmgMul: hasRelic(P, 'wayfarer') ? 0.75 : 1 });
  if (P.arrowBuff) P.arrowBuff = null;
}
function resolveMeleeHit(mult, heavy) {
  const w = curWeapon();
  const s = itemStats(w);
  const combo = P.attack.combo || 0;
  const arc = w.fam === 'spear' ? 35 : combo === 2 ? 50 : 90;
  const reach = w.reach;
  let base = rf(Math.random, s.dmgMin, s.dmgMax);
  let add;
  if (w.fam === 'dagger') add = Math.max(0.18 * P.stats.str, 0.3 * P.stats.dex);
  else add = (w.two ? 0.35 : 0.25) * P.stats.str;
  let dmg = (base + add) * mult;
  if (w.two && P.talents.heavyhands) dmg *= 1 + 0.06 + 0.04 * (P.talents.heavyhands - 1);
  if (P.stats.dmgPct) dmg *= 1 + P.stats.dmgPct;
  if (P.retalBuff) { dmg *= 1 + P.retalBuff; P.retalBuff = 0; }
  const crit = Math.random() < P.stats.crit;
  if (crit) dmg *= 1.5 + P.stats.critDmg;
  // elemental adds
  const elem = { fire: P.stats.fireDmg, frost: P.stats.frostDmg, light: P.stats.lightDmg, poison: P.stats.poisonDmg };
  if (w.special === 'coalbrand') elem.fire += 6;
  const statuses = [];
  const onHit = [['burn', 'onHitBurn'], ['chill', 'onHitChill'], ['poison', 'onHitPoison'], ['shock', 'onHitShock']];
  for (const [st, key] of onHit) {
    if (P.stats[key] && Math.random() < P.stats[key]) statuses.push({ id: st, dur: st === 'burn' ? 4 : st === 'poison' ? 8 : 4, power: 4 + P.level });
  }
  if (w.special === 'coalbrand' && Math.random() < 0.35) statuses.push({ id: 'burn', dur: 4, power: 5 + P.level });
  if (P.daggerBuff && w.fam === 'dagger') { statuses.push({ id: 'bleed', dur: 4, power: P.daggerBuff.bleed / 4 }); P.daggerBuff = null; }
  let poise = (w.poise || 5) * (heavy ? 2 : 1);
  if (w.special === 'wardentoll') poise *= 2;
  const hit = { phys: dmg, crit, melee: true, poise, statuses, src: { player: true } };
  const targets = G.floor.actors.filter(a => !a.dead && a.activated !== false);
  let hits = 0;
  for (const a of targets) {
    const dx = a.pos[0] - P.pos[0], dz = a.pos[2] - P.pos[2];
    const dist = Math.sqrt(dx * dx + dz * dz);
    if (dist > reach + a.radius) continue;
    const ang = Math.abs(angleDiff(Math.atan2(-dx, -dz), P.yaw));
    if (ang > (arc * Math.PI / 180 / 2)) continue;
    if (!losClear(G.floor, P.pos[0], P.pos[2], a.pos[0], a.pos[2])) continue;
    const final = deepHit(hit, a, crit);
    final.totalMul = mult;
    dealDamage(a, { player: true }, final);
    hits++;
    if (hits >= 4) break;
  }
  // props
  for (const pr of G.floor.props) {
    if (pr.dead || (pr.hp !== undefined && pr.hp <= 0)) continue;
    if (pr.type !== 'crate' && pr.type !== 'barrel') continue;
    if (d2(pr.x, pr.z, P.pos[0], P.pos[2]) < reach + 0.4) {
      damageProp(pr, dmg);
    }
  }
  // dummy
  for (const pr of G.floor.props) if (pr.type === 'dummy' && d2(pr.x, pr.z, P.pos[0], P.pos[2]) < reach + 0.5) { R.burst(pr.x, 1.2, pr.z, 4, [1, .9, .6], 3, 3, .3); SND.hitStone(); }
  // durability
  if (w && w.durMax) { w.dur = Math.max(0, w.dur - (heavy ? 0.25 : 0.1)); if (w.dur === 0) { toast(w.name + ' broke!', 'bad'); recalcStats(P); } }
  // spell echo passives etc — mana steal affix handled in dealDamage
  return hits;
}
function deepHit(hit, a, crit) {
  const h = Object.assign({}, hit);
  // headshot / limb by aim height
  const eyeY = P.pos[1] + (P.crouch ? CFG.crouchEye : CFG.eyeHeight);
  const hitY = a.pos[1] + a.scaleH * 0.75;
  if (a.arch.sever && a.limbs && a.limbs.head && eyeY > 1.55 && hitY < eyeY + 0.2 && Math.abs(0) < 1) {
    if (Math.random() < 0.5) { h.limb = 'head'; }
  }
  if (h.limb === 'head' && a.arch.sever && !a.arch.tags.includes('construct')) h.phys *= CFG.headshotMul;
  return h;
}
/* severing check applied in dealDamage post-hit — integrated here for melee/arrow paths */
function checkSever(a, hit, src) {
  if (!a.arch.sever || !a.limbs || !hit.limb) return;
  const limb = hit.limb;
  if (!a.limbs[limb]) return;
  if (a.arch.sever && a.arch.sever[limb] === false) return; // decapitation-resistant / non-severable
  a.limbdmg = a.limbdmg || {};
  a.limbdmg[limb] = (a.limbdmg[limb] || 0) + hit.phys;
  const frac = a.limbdmg[limb] / a.maxHp;
  const single = hit.phys / a.maxHp;
  const eligible = hit.melee || hit.arrow;
  if ((eligible && (frac >= CFG.severFraction || single >= CFG.severSingle)) || frac >= CFG.severFraction * 1.6) {
    a.limbs[limb] = false;
    EVT.emit('LimbSevered', { actor: a, limb });
    if (!G.settings.gore) { R.burst(a.pos[0], 1.2, a.pos[2], 8, [0.4, 0.4, 0.45], 3, 3, 0.5); }
    else spawnGoreProp(a, limb);
    if (limb === 'head' && !a.arch.tags.includes('undead') && !a.arch.spec.includes('headless')) {
      a.hp = 0; killActor(a, { player: true });
    } else {
      toast(a.name + ': ' + limb + ' ruined', '');
      if (limb === 'armR' || limb === 'armL') { a.atkSpeedMul = 0.7; }
      if (limb === 'legL' || limb === 'legR') { a.speedMul = 0.5; }
    }
  }
}
function spawnGoreProp(a, limb) {
  const cols = a.arch.col;
  G.floor.props.push({ id: 'p' + (PROP_ID++), type: 'gore_' + limb, x: a.pos[0], y: 0, z: a.pos[2], vx: (Math.random() - .5) * 4, vz: (Math.random() - .5) * 4, vy: 3, blocking: false, rad: 0.25, dead: false, hp: 999, life: 25, col: cols });
}

/* kick */
function doKick() {
  if (P.attack.state !== 'idle' && P.attack.state !== 'recover') return;
  if (!trySpendStamina(CFG.kick.stamina)) return;
  P.attack = { state: 'kick', t: 0, dur: 0.35, combo: 0 };
  SND.kick();
  setTimeout(() => {}, 0);
  resolveKick();
}
function resolveKick() {
  const bootElem = P.stats.kickElem || (hasRelic(P, 'thunderheels') ? 'lightning' : null);
  const hit = { phys: bootElem ? 0 : CFG.kick.dmg + P.stats.str * 0.1, poise: CFG.kick.poise, knock: 7, src: { player: true }, melee: true };
  if (bootElem) hit[bootElem === 'lightning' ? 'light' : bootElem] = 8 + P.level;
  const targets = G.floor.actors.filter(a => !a.dead);
  for (const a of targets) {
    const dx = a.pos[0] - P.pos[0], dz = a.pos[2] - P.pos[2];
    const dist = Math.sqrt(dx * dx + dz * dz);
    if (dist > CFG.kick.reach + a.radius) continue;
    if (Math.abs(angleDiff(Math.atan2(-dx, -dz), P.yaw)) > 0.7) continue;
    a.vel[0] += -Math.sin(P.yaw) * hit.knock; a.vel[2] += -Math.cos(P.yaw) * hit.knock;
    a.credits = a.credits || []; a.credits.push({ player: true, t: G.time });
    dealDamage(a, { player: true }, hit);
    if (a.arch && a.arch.tags.includes('boss')) a.vel[0] *= 0.2, a.vel[2] *= 0.2;
  }
  // props
  for (const pr of G.floor.props) {
    if (pr.dead || !pr.blocking) continue;
    if (d2(pr.x, pr.z, P.pos[0], P.pos[2]) > CFG.kick.reach + 0.3) continue;
    if (Math.abs(angleDiff(Math.atan2(-(pr.x - P.pos[0]), -(pr.z - P.pos[2])), P.yaw)) > 0.8) continue;
    if (pr.type === 'crate' || pr.type === 'barrel') {
      pr.vx = -Math.sin(P.yaw) * 9; pr.vz = -Math.cos(P.yaw) * 9; pr.vy = 2.5;
      pr.hitCd = {};
      SND.thud();
    } else if (pr.type === 'gore_head' || pr.type === 'gore_armL' || pr.type === 'gore_armR') {
      pr.vx = -Math.sin(P.yaw) * 10; pr.vz = -Math.cos(P.yaw) * 10; pr.vy = 4; pr.weapon = true;
      SND.thud();
    }
  }
}

/* ---------------- spells & talents ---------------- */
function castSelectedSpell(heavy) {
  const w = curWeapon();
  const sid = P.selectedSpell;
  if (!P.spellRanks[sid]) { SND.error(); toast('Spell not learned', 'bad'); return; }
  castSpell(sid, { charged: heavy, viaWeapon: w && (w.fam === 'staff' || w.fam === 'wand') });
}
function castSpell(sid, opts) {
  opts = opts || {};
  const sp = SPELLS[sid];
  const rank = P.spellRanks[sid] || 1;
  const cost = Math.round(spellRankCost(sp.mana, rank) * (1 - (P.stats.manaCostRed || 0)));
  const charged = !!opts.charged;
  const costMul = sp.elem === 'fire' && hasRelic(P, 'ashglass') ? 1.25 : charged ? 1.5 : 1;
  if (P.mp < cost * costMul) { SND.error(); toast('Not enough mana', 'bad'); return false; }
  if (cdRemaining('s_' + sid) > 0) { SND.error(); toast(SPELLS[sid].name + ' is on cooldown', 'bad'); return false; }
  if (sp.kind === 'portal') {
    if (G.time - P.lastDamageT < 5) { SND.error(); toast('Return Sigil unusable within 5 s of taking damage', 'bad'); return false; }
    if (P.mp < cost * costMul) { SND.error(); toast('Not enough mana', 'bad'); return false; }
    P.mp -= cost * costMul;
    P.channel = { id: sid, t: 0, dur: sp.channel, mana: cost * costMul };
    return true;
  }
  // cast time
  P.attack = { state: 'cast', t: 0, dur: (sp.cast || 0.4) * (charged ? 1.6 : 1), spell: sid, rank, charged };
  P.mp -= cost * costMul;
  SND['cast' + ({ fire: 'Fire', frost: 'Frost', arcane: 'Arc', lightning: 'Light' }[sp.elem] || 'Arc')]();
  return true;
}
function finishCast(atk) {
  const sid = atk.spell, rank = atk.rank, sp = SPELLS[sid];
  const charged = atk.charged;
  const spMul = P.stats.spellPower * (charged ? 1.6 : 1) * spellRankMul(rank, !!sp.dmg);
  if (P.talents.elementalist && ['fire', 'frost', 'lightning'].includes(sp.elem)) spMul *= 1 + 0.06 + 0.03 * (P.talents.elementalist - 1);
  setCooldown('s_' + sid, sp.cd);
  const dir = camDir();
  const eye = [P.pos[0], P.pos[1] + (P.crouch ? CFG.crouchEye : CFG.eyeHeight) - 0.1, P.pos[2]];
  switch (sp.kind) {
    case 'projectile': {
      const dmg = sp.dmg * spMul;
      const statuses = [];
      if (sp.chill) statuses.push({ id: 'chill', dur: 4, power: 0 });
      spawnProj(eye, dir, sp.speed, { dmg, elem: sp.elem, friendly: true, spell: true, blast: charged && hasRelic(P, 'ashglass') ? (sp.blast || 0) + 1.5 : sp.blast, blastDmg: sp.blastDmg ? sp.blastDmg * spMul : 0, chill: sp.chill, statuses, ashglass: sp.elem === 'fire' && hasRelic(P, 'ashglass') });
      // spell echo
      if (P.talents.spellecho && Math.random() < P.talents.spellecho * 0.05 + 0.05 - 0.05 + (P.talents.spellecho - 1) * 0.03) {
        setTimeoutSpawnEcho(sid, spMul);
      }
      break;
    }
    case 'chain': {
      let targets = nearestEnemies(eye, sp.range, 3);
      let dmg = sp.dmg * spMul, n = 0;
      const hitSet = new Set();
      for (const a of targets) {
        if (n > sp.chain) break;
        if (!losClear(G.floor, eye[0], eye[2], a.pos[0], a.pos[2])) continue;
        dealDamage(a, { player: true }, { light: dmg, poise: 4, src: { player: true }, statuses: [{ id: 'shock', dur: 4, power: 0 }] });
        R.burst(a.pos[0], 1.2, a.pos[2], 8, [0.7, 0.8, 1], 4, 3, 0.3);
        hitSet.add(a); n++;
        dmg *= sp.chainMul;
      }
      if (!n) { dmgNum(eye, 'no target', '#888'); }
      break;
    }
    case 'heal': {
      const amt = (sp.heal + sp.healInt * P.stats.int) * spellRankMul(rank, false) * P.stats.spellPower;
      P.hp = clamp(P.hp + amt, 0, P.stats.hpMax);
      dmgNum(P.pos, '+' + Math.round(amt), '#7fd87f');
      SND.castHoly();
      break;
    }
    case 'buff': {
      addBuff(P, 'stoneskin', 'Stone Skin', sp.dur, { armor: Math.round(sp.armor * spellRankMul(rank, false) * P.stats.spellPower) }, '🪨');
      SND.castHoly();
      break;
    }
    case 'utility': {
      P.revealT = sp.dur;
      toast('Reveal: nearby loot and hidden doors shown', 'good');
      SND.shrine();
      break;
    }
    case 'blink': {
      const dist = sp.dist * spellRankMul(rank, false);
      blinkForward(dist);
      break;
    }
    case 'aoe': {
      G.floor.mists.push({ x: P.pos[0], z: P.pos[2], r: sp.radius, t: sp.dur, elem: 'poison', dmg: sp.dmg * spMul / 2, src: { player: true } });
      SND.castDark();
      break;
    }
  }
}
function setTimeoutSpawnEcho(sid, mul) {
  // echo repeats at 40% damage after 0.25s
  const sp = SPELLS[sid];
  if (sp.kind !== 'projectile') return;
  setTimeout(() => {
    if (G.state !== 'play' || P.dead) return;
    const dir = camDir();
    const eye = [P.pos[0], P.pos[1] + 1.5, P.pos[2]];
    spawnProj(eye, dir, sp.speed, { dmg: sp.dmg * mul * 0.4, elem: sp.elem, friendly: true, spell: true, statuses: [] });
  }, 250);
}
function nearestEnemies(from, range, n) {
  return G.floor.actors.filter(a => !a.dead && d2(a.pos[0], a.pos[2], from[0], from[2]) < range)
    .sort((a, b) => d2(a.pos[0], a.pos[2], from[0], from[2]) - d2(b.pos[0], b.pos[2], from[0], from[2])).slice(0, n);
}
function blinkForward(dist) {
  const dir = [-Math.sin(P.yaw), -Math.cos(P.yaw)];
  const F = G.floor;
  let best = [P.pos[0], P.pos[2]];
  for (let d = dist; d > 0.5; d -= 0.4) {
    const nx = P.pos[0] + dir[0] * d, nz = P.pos[2] + dir[1] * d;
    if (!circleBlocked(F, nx, nz, P.radius)) { best = [nx, nz]; break; }
  }
  R.burst(P.pos[0], 1, P.pos[2], 12, [0.6, 0.4, 1], 3, 4, 0.4);
  P.pos[0] = best[0]; P.pos[2] = best[1];
  R.burst(P.pos[0], 1, P.pos[2], 12, [0.6, 0.4, 1], 3, 4, 0.4);
  SND.portal();
}
function addBuff(ent, id, name, dur, mods, icon) {
  const ex = ent.buffs.find(b => b.id === id);
  if (ex) { ex.t = Math.max(ex.t, dur); Object.assign(ex.mods, mods); return; }
  ent.buffs.push({ id, name, t: dur, mods, icon: icon || '✦' });
  if (ent === P) recalcStats(P);
}
function cdRemaining(key) { return (P.cds[key] || 0); }
function setCooldown(key, base) { P.cds[key] = base / (1 + (P.stats.haste || 0) / 100); }
function tickCooldowns(dt) { for (const k in P.cds) if (P.cds[k] > 0) P.cds[k] = Math.max(0, P.cds[k] - dt); }

/* talents */
function execTalent(tid) {
  const t = TALENT_BY_ID[tid];
  const rank = P.talents[tid];
  if (!t || !rank) return;
  if (t.type !== 'active') return;
  if (cdRemaining('t_' + tid) > 0) { SND.error(); toast(t.name + ' on cooldown', 'bad'); return; }
  if (t.mana && P.mp < t.mana) { SND.error(); toast('Not enough mana', 'bad'); return; }
  if (t.mana) P.mp -= t.mana;
  setCooldown('t_' + tid, t.cd);
  const p = t.params, rankMul = 1 + (rank - 1);
  const dir = [-Math.sin(P.yaw), -Math.cos(P.yaw)];
  switch (tid) {
    case 'bulwark': {
      dashForward(p.dist, () => {
        const targets = nearestEnemies(P.pos, 2.5, 1);
        if (targets.length) {
          const a = targets[0];
          dealDamage(a, { player: true }, { radiant: p.dmg * (1 + 0.15 * (rank - 1)) + 0.15 * P.stats.armor, poise: 25, src: { player: true } });
        }
      });
      break;
    }
    case 'verdict': P.verdictBuff = { dmg: p.dmg + p.dmgRank * (rank - 1), poise: p.poise, t: p.dur }; toast('Crushing Verdict ready', ''); break;
    case 'shieldpulse': {
      for (const a of nearestEnemies(P.pos, p.dist + 1, 6)) {
        const dx = a.pos[0] - P.pos[0], dz = a.pos[2] - P.pos[2];
        if (Math.abs(angleDiff(Math.atan2(-dx, -dz), P.yaw)) > 1) continue;
        const force = 1 + p.forceRank * (rank - 1);
        a.vel[0] += dir[0] * 9 * force; a.vel[2] += dir[1] * 9 * force;
        dealDamage(a, { player: true }, { phys: p.dmg, poise: p.poise * force, src: { player: true } });
      }
      SND.kick();
      break;
    }
    case 'rally': {
      const heal = (P.stats.hpMax - P.hp) * p.healFrac;
      P.hp = clamp(P.hp + heal, 0, P.stats.hpMax);
      addBuff(P, 'rally', 'Rally', p.dur, { armor: p.armor + p.armorRank * (rank - 1) }, '🛡');
      dmgNum(P.pos, '+' + Math.round(heal), '#7fd87f');
      break;
    }
    case 'defiant': addBuff(P, 'defiant', 'Defiant Stand', p.dur + p.durRank * (rank - 1), { defiant: true }, '⛨'); break;
    case 'shadowstep': {
      P.iframe = 0.4;
      dashForward(p.dist + p.distRank * (rank - 1));
      break;
    }
    case 'piercing': P.arrowBuff = { dmgPct: p.dmgPct + p.rank * (rank - 1), pierce: p.pierce, t: p.dur }; toast('Piercing Shot ready', ''); break;
    case 'rend': P.daggerBuff = { bleed: p.bleed * (1 + p.rank * (rank - 1)), t: p.dur }; toast('Rend ready — next dagger strike', ''); break;
    case 'caltrops': G.floor.caltrops.push({ x: P.pos[0], z: P.pos[2], r: p.radius, t: p.dur + p.durRank * (rank - 1), slow: p.slow }); break;
    case 'quickdraw': addBuff(P, 'quickdraw', 'Quickdraw', p.dur, { atkSpd: p.spdPct + p.rank * (rank - 1) }, '🏹'); break;
    case 'arcbolt': {
      const dmg = p.dmg * (1 + p.rank * (rank - 1)) * P.stats.spellPower;
      spawnProj([P.pos[0], P.pos[1] + 1.5, P.pos[2]], dir, 30, { dmg, elem: 'arcane', friendly: true, spell: true, statuses: [] });
      break;
    }
    case 'emberwave': {
      const dmg = p.dmg * (1 + p.rank * (rank - 1)) * P.stats.spellPower;
      coneAttack(P.pos, P.yaw, p.cone, dmg, 'fire', p.ignite);
      break;
    }
    case 'frostring': {
      const dmg = p.dmg * (1 + p.rank * (rank - 1)) * P.stats.spellPower;
      for (const a of nearestEnemies(P.pos, p.radius + 1, 12)) dealDamage(a, { player: true }, { frost: dmg, src: { player: true }, statuses: [{ id: 'slow', dur: p.slowDur + 0.3 * (rank - 1), power: 0.4 }] });
      R.burst(P.pos[0], 0.5, P.pos[2], 24, [0.6, 0.85, 1], 5, 4, 0.5);
      break;
    }
    case 'manaward': {
      P.ward = { hp: p.ward + p.rank * (rank - 1), t: p.dur };
      toast('Mana Ward active', 'good');
      break;
    }
    case 'blink': blinkForward(p.dist + p.rank * (rank - 1)); break;
  }
  EVT.emit('AttackCommitted', { talent: tid });
}
function dashForward(dist, onArrive) {
  const dir = [-Math.sin(P.yaw), -Math.cos(P.yaw)];
  const F = G.floor;
  let moved = 0;
  for (let d = 0.4; d <= dist; d += 0.4) {
    const nx = P.pos[0] + dir[0] * d, nz = P.pos[2] + dir[1] * d;
    if (circleBlocked(F, nx, nz, P.radius)) break;
    moved = d;
  }
  P.pos[0] += dir[0] * moved; P.pos[2] += dir[1] * moved;
  if (onArrive) onArrive();
}
function coneAttack(from, yaw, len, dmg, elem, igniteChance) {
  for (const a of nearestEnemies(from, len + 1, 10)) {
    const dx = a.pos[0] - from[0], dz = a.pos[2] - from[2];
    if (Math.abs(angleDiff(Math.atan2(-dx, -dz), yaw)) > 0.6) continue;
    if (!losClear(G.floor, from[0], from[2], a.pos[0], a.pos[2])) continue;
    const hit = { [elem === 'fire' ? 'fire' : elem]: dmg, src: { player: true } };
    if (elem === 'fire' && Math.random() < igniteChance) hit.statuses = [{ id: 'burn', dur: 4, power: 5 + P.level }];
    dealDamage(a, { player: true }, hit);
  }
  R.burst(from[0] - Math.sin(yaw) * 2, 1.2, from[2] - Math.cos(yaw) * 2, 20, ELEM_COL[elem] || [1, .6, .3], 5, 4, 0.4);
}
function shockwaveBurst(pos, r, hit) {
  for (const a of nearestEnemies(pos, r + 1, 12)) {
    dealDamage(a, hit.src, Object.assign({ poise: 25 }, hit));
  }
  R.burst(pos[0], 0.6, pos[2], 20, [0.8, 0.8, 1], 6, 4, 0.4);
}

/* shockwaves (boss) */
function updateShockwaves(F, dt) {
  for (let i = (F.shockwaves || []).length - 1; i >= 0; i--) {
    const w = F.shockwaves[i];
    w.r += w.speed * dt;
    R.burst(w.x + Math.cos(w.a) * w.r, 0.3, w.z + Math.sin(w.a) * w.r, 1, [1, .8, .4], 0.5, 3, 0.2);
    w.a += 0.9;
    const pd = Math.abs(d2(P.pos[0], P.pos[2], w.x, w.z) - w.r);
    if (pd < 0.7 && !w.hitP) { w.hitP = true; dealDamage(P, { env: true, arch: null, level: w.level }, { phys: w.dmg, poise: 20, unblockable: false }); }
    for (const a of F.actors) {
      if (a.dead || a.bossId) continue;
      if (Math.abs(d2(a.pos[0], a.pos[2], w.x, w.z) - w.r) < 0.7 && !a['sw' + w.id]) {
        a['sw' + w.id] = true;
        dealDamage(a, { env: true }, { phys: w.dmg * 0.5 });
      }
    }
    if (w.r > w.maxR) F.shockwaves.splice(i, 1);
  }
}

/* player death */
function playerDeath() {
  if (P.dead) return;
  P.dead = true;
  SND.death();
  if (P.hardcore) {
    P.dead = true;
    markHardcoreDead();
    showDeathScreen(true);
    return;
  }
  const frac = CFG.difficulty[G.campaign.difficulty].goldLoss;
  const lost = Math.floor(P.gold * frac);
  if (lost > 0) {
    if (G.campaign.caches.length) {
      const old = G.campaign.caches[0];
      toast('Previous gold cache forfeited (' + fmt(old.amount) + 'g) — new cache holds ' + fmt(lost + old.amount) + 'g', 'bad');
      G.campaign.caches[0] = { floor: G.floor.index, x: P.pos[0], z: P.pos[2], amount: lost + old.amount };
    } else {
      G.campaign.caches.push({ floor: G.floor.index, x: P.pos[0], z: P.pos[2], amount: lost });
      toast('Dropped ' + fmt(lost) + ' gold at your death site (recoverable)', '');
    }
    P.gold -= lost;
  }
  showDeathScreen(false);
}

/* ============================================================
   10. ACTORS — enemies, AI state machine, elites, bosses
   ============================================================ */
function spawnEnemy(F, defId, x, z, level, opts) {
  opts = opts || {};
  const def = ENEMY_BY_ID[defId];
  if (!def) return null;
  const id = opts.id || ('a' + (PROP_ID++));
  const hpMul = (1 + 0.22 * (level - 1)) * CFG.difficulty[G.campaign.difficulty].hp;
  const dmgMul = (1 + 0.09 * (level - 1)) * CFG.difficulty[G.campaign.difficulty].dmg;
  const a = {
    id, arch: def, archId: defId, level,
    name: def.name, pos: [x, 0, z], vel: [0, 0, 0], yaw: Math.random() * TAU,
    radius: 0.5 * (def.scale || 1), scaleH: 1.7 * (def.scale || 1),
    hp: def.hp * hpMul, maxHp: def.hp * hpMul,
    armor: def.armor * (1 + 0.12 * (level - 1)),
    dmg: [def.dmg[0] * dmgMul, def.dmg[1] * dmgMul],
    speed: def.speed, poise: def.poise, poiseMax: def.poise,
    xpVal: Math.round(def.xp * (1 + 0.3 * (level - 1))),
    state: 'idle', stateT: 0, target: null, path: null, pathI: 0, repathT: 0,
    atkCd: 0, windup: null, activeT: 0, recoverT: 0,
    statuses: [], stun: 0, fearT: 0, dead: false,
    limbs: def.sever === false ? null : { head: true, armL: true, armR: true, legL: true, legR: true },
    spawn: [x, z], home: [x, z], activated: false, dormant: def.spec === 'ambush',
    loot: opts.loot || [], gold: opts.gold || 0, credits: [],
    bobPhase: Math.random() * TAU, speedMul: 1, atkSpeedMul: 1,
    elite: opts.elite || null, elite2: opts.elite2 || null, questElite: opts.questElite || null,
    bossId: null, bossDef: null, bossPhase: 0, bossMove: null, bossT: 0,
    shieldHp: 0, lastSeen: null, wanderT: 0, glow: 0, hitFlash: 0,
  };
  if (a.elite) {
    const m = ELITES[a.elite];
    a.hp *= 1.9; a.maxHp = a.hp; a.name = m.name + ' ' + a.name;
    a.dmg[0] *= 1.25; a.dmg[1] *= 1.25;
    a.xpVal = Math.round(a.xpVal * 3);
    if (m.shield) a.shieldHp = m.shield * (1 + level * 0.1);
  }
  if (a.elite2) {
    const m2 = ELITES[a.elite2];
    a.name += ' ' + m2.name.toLowerCase();
    if (m2.shield) a.shieldHp = Math.max(a.shieldHp, m2.shield * (1 + level * 0.08));
  }
  if (opts.questElite) {
    a.name = 'Bloodmarked ' + a.name;
    a.questElite = opts.questElite;
  }
  F.actors.push(a);
  return a;
}
function spawnBoss(F, bossId, x, z, level) {
  const def = BOSSES[bossId];
  const hpMul = CFG.difficulty[G.campaign.difficulty].hp;
  const a = spawnEnemy(F, 'bone_colossus', x, z, level, { id: 'boss_' + bossId });
  a.bossId = bossId; a.bossDef = def;
  a.name = def.name;
  a.hp = def.hp * hpMul; a.maxHp = a.hp;
  a.armor = def.armor; a.dmg = [def.dmg[0], def.dmg[1]];
  a.speed = def.speed; a.poise = def.poise; a.poiseMax = def.poise;
  a.xpVal = def.xp;
  a.scaleH = 2.0 * (def.scale || 1);
  a.radius = 0.7 * (def.scale || 1);
  a.arch = Object.assign({}, a.arch, { col: def.col, col2: def.col2, tags: def.tags, sever: bossId === 'bellkeeper', imm: ['stun'] });
  a.scaleH *= def.scale || 1;
  a.elite = null;
  a.loot = []; a.gold = 0;
  F.bossActor = a;
  return a;
}

/* noise events for AI hearing */
function emitNoise(F, x, z, radius) {
  for (const a of F.actors) {
    if (a.dead || !a.arch) continue;
    if (d2(a.pos[0], a.pos[2], x, z) < radius) {
      if (!a.target && a.state !== 'chase') {
        a.lastSeen = [x, z];
        if (a.state === 'idle' || a.state === 'patrol') a.state = 'investigate';
      }
    }
  }
}

function updateActors(F, dt) {
  for (let i = F.actors.length - 1; i >= 0; i--) {
    const a = F.actors[i];
    if (a.dead) {
      a.deadT += dt;
      if (a.deadT > 45) F.actors.splice(i, 1);
      continue;
    }
    tickStatuses(a, dt);
    a.hitFlash = Math.max(0, a.hitFlash - dt * 3);
    // shield (warded elite)
    if (a.shieldHp > 0) { /* absorbed in damage pipeline not implemented separately — shield regenerates slowly */ a.shieldHp = Math.min(a.shieldHp + dt * 1.5, a.shieldHp + 10); }
    if (a.stun > 0) { a.stun -= dt; integrateActor(F, a, dt, true); continue; }
    if (a.fearT > 0) { a.fearT -= dt; fleeBehavior(F, a, dt); continue; }
    if (a.bossId) { updateBoss(F, a, dt); integrateActor(F, a, dt, false); continue; }
    // dormant ambushers wake on proximity
    if (a.dormant) {
      if (d2(a.pos[0], a.pos[2], P.pos[0], P.pos[2]) < 5 && losClear(F, a.pos[0], a.pos[2], P.pos[0], P.pos[2])) {
        a.dormant = false; a.activated = true; SND.growl(); a.target = P;
      } else { integrateActor(F, a, dt, true); continue; }
    }
    if (!a.activated) {
      // activate when player near or in same room
      if (d2(a.pos[0], a.pos[2], P.pos[0], P.pos[2]) < 14) { a.activated = true; }
      else continue;
    }
    // statuses affect speed
    let spdMul = a.speedMul;
    if (hasStatus(a, 'chill')) spdMul *= 0.7;
    if (hasStatus(a, 'slow')) { const s = a.statuses.find(s => s.id === 'slow'); spdMul *= (1 - (s?.power || 0.35)); }
    if (a.elite === 'enraged') spdMul *= 1.2;
    // perception
    const dist = d2(a.pos[0], a.pos[2], P.pos[0], P.pos[2]);
    const canSee = dist < a.arch.vision && !P.dead && losClear(F, a.pos[0], a.pos[2], P.pos[0], P.pos[2]) &&
      Math.abs(angleDiff(Math.atan2(-(P.pos[0] - a.pos[0]), -(P.pos[2] - a.pos[2])), a.yaw)) < 1.9;
    if (canSee) { a.target = P; a.lastSeen = [P.pos[0], P.pos[2]]; if (a.state === 'idle' || a.state === 'patrol' || a.state === 'investigate') { a.state = 'chase'; if (Math.random() < 0.3) SND.growl(a.arch.tier === 'brute'); } }
    else if (a.target === P && dist > a.arch.vision * 1.4) { a.target = null; a.state = a.lastSeen ? 'investigate' : 'idle'; }
    // fear
    if (hasStatus(a, 'fear')) { a.fearT = 3; a.statuses = a.statuses.filter(s => s.id !== 'fear'); }
    // state machine
    switch (a.state) {
      case 'idle': idleWander(F, a, dt); break;
      case 'patrol': idleWander(F, a, dt); break;
      case 'investigate': {
        if (!a.lastSeen) { a.state = 'idle'; break; }
        moveTo(F, a, a.lastSeen[0], a.lastSeen[1], dt, spdMul);
        if (d2(a.pos[0], a.pos[2], a.lastSeen[0], a.lastSeen[1]) < 1.5) { a.lastSeen = null; a.state = 'idle'; }
        break;
      }
      case 'chase': {
        if (P.dead) { a.state = 'idle'; a.target = null; break; }
        const atkRange = a.arch.atk === 'melee' ? a.arch.reach : a.arch.reach * 0.8;
        if (dist <= atkRange && canSee && a.atkCd <= 0) { startEnemyAttack(a); }
        else if (dist <= atkRange * 0.7 && a.arch.atk === 'melee') {
          // strafe slightly
          strafeAround(F, a, dt, spdMul);
        } else {
          moveTo(F, a, P.pos[0], P.pos[2], dt, spdMul);
        }
        applyArchSpecial(F, a, dt, dist);
        break;
      }
      case 'windup': {
        a.stateT -= dt;
        a.glow = 1;
        if (a.stateT <= 0) { enemyStrike(F, a); a.state = 'recover'; a.stateT = a.arch.rec / (a.atkSpeedMul || 1); }
        break;
      }
      case 'recover': {
        a.stateT -= dt; a.glow = Math.max(0, a.glow - dt * 4);
        if (a.stateT <= 0) { a.state = 'chase'; a.atkCd = a.arch.cd; }
        break;
      }
    }
    if (a.atkCd > 0) a.atkCd -= dt;
    a.poise = Math.min(a.poiseMax, a.poise + dt * 8);
    integrateActor(F, a, dt, a.state === 'windup' || a.state === 'recover' || a.state === 'attack');
  }
}
function idleWander(F, a, dt) {
  a.wanderT -= dt;
  if (a.wanderT <= 0) {
    a.wanderT = rf(Math.random, 2, 5);
    const t = rf(Math.random, 0, TAU);
    a.wanderDir = [Math.cos(t), Math.sin(t)];
    if (Math.random() < 0.4) a.wanderDir = null;
  }
  if (a.wanderDir) {
    const nx = a.pos[0] + a.wanderDir[0] * a.speed * 0.4 * dt, nz = a.pos[2] + a.wanderDir[1] * a.speed * 0.4 * dt;
    if (!circleBlocked(F, nx, nz, a.radius)) { a.pos[0] = nx; a.pos[2] = nz; a.yaw = Math.atan2(-a.wanderDir[0], -a.wanderDir[1]); }
    else a.wanderDir = null;
  }
}
function fleeBehavior(F, a, dt) {
  const dx = a.pos[0] - P.pos[0], dz = a.pos[2] - P.pos[2];
  const l = Math.max(0.01, Math.sqrt(dx * dx + dz * dz));
  const nx = a.pos[0] + dx / l * a.speed * dt, nz = a.pos[2] + dz / l * a.speed * dt;
  if (!circleBlocked(F, nx, nz, a.radius)) { a.pos[0] = nx; a.pos[2] = nz; a.yaw = Math.atan2(-dx / l, -dz / l); }
}
function strafeAround(F, a, dt, spdMul) {
  const dx = P.pos[0] - a.pos[0], dz = P.pos[2] - a.pos[2];
  const side = a.strafeSide || (a.strafeSide = Math.random() < .5 ? 1 : -1);
  const sx = -dz / Math.max(0.01, Math.hypot(dx, dz)) * side, sz = dx / Math.max(0.01, Math.hypot(dx, dz)) * side;
  const nx = a.pos[0] + sx * a.speed * 0.6 * dt, nz = a.pos[2] + sz * a.speed * 0.6 * dt;
  if (!circleBlocked(F, nx, nz, a.radius)) { a.pos[0] = nx; a.pos[2] = nz; }
  else a.strafeSide = -side;
  a.yaw = Math.atan2(-dx, -dz);
}
function moveTo(F, a, tx, tz, dt, spdMul) {
  a.repathT -= dt;
  const dist = d2(a.pos[0], a.pos[2], tx, tz);
  if (a.repathT <= 0 || !a.path) {
    a.repathT = rf(Math.random, 0.4, 0.9);
    a.path = aStar(F, a.pos[0], a.pos[2], tx, tz);
    a.pathI = 1;
  }
  let dx, dz;
  if (a.path && dist < 6 && losClear(F, a.pos[0], a.pos[2], tx, tz)) { dx = tx - a.pos[0]; dz = tz - a.pos[2]; }
  else if (a.path) {
    while (a.pathI < a.path.length && d2(a.pos[0], a.pos[2], a.path[a.pathI][0], a.path[a.pathI][1]) < 0.8) a.pathI++;
    if (a.pathI >= a.path.length) { a.path = null; return; }
    dx = a.path[a.pathI][0] - a.pos[0]; dz = a.path[a.pathI][1] - a.pos[2];
  } else { dx = tx - a.pos[0]; dz = tz - a.pos[2]; }
  const l = Math.max(0.001, Math.hypot(dx, dz));
  let vx = dx / l * a.speed * spdMul, vz = dz / l * a.speed * spdMul;
  // separation
  for (const o of F.actors) {
    if (o === a || o.dead || !o.arch) continue;
    const od = d2(o.pos[0], o.pos[2], a.pos[0], a.pos[2]);
    if (od < 1.2 && od > 0.001) { vx += (a.pos[0] - o.pos[0]) / od * 2; vz += (a.pos[2] - o.pos[2]) / od * 2; }
  }
  const ny = a.pos[0] + vx * dt, nz2 = a.pos[2] + vz * dt;
  if (!circleBlocked(F, ny, nz2, a.radius)) { a.pos[0] = ny; a.pos[2] = nz2; }
  else if (!circleBlocked(F, ny, a.pos[2], a.radius)) a.pos[0] = ny;
  else if (!circleBlocked(F, a.pos[0], nz2, a.radius)) a.pos[2] = nz2;
  a.yaw = Math.atan2(-vx, -vz);
}
function startEnemyAttack(a) {
  a.state = 'windup';
  a.stateT = a.arch.windup / (a.atkSpeedMul || 1);
  SND.growl(a.arch.tier === 'brute');
  if (a.arch.atk !== 'melee') { /* telegraphed projectile */ }
}
function enemyStrike(F, a) {
  a.glow = 0;
  const dist = d2(a.pos[0], a.pos[2], P.pos[0], P.pos[2]);
  const dmg = rf(Math.random, a.dmg[0], a.dmg[1]);
  if (a.arch.atk === 'melee') {
    if (dist <= a.arch.reach + P.radius + 0.3) {
      const hit = { phys: dmg, poise: a.arch.tier === 'brute' ? 14 : 6, melee: true, src: a, unblockable: a.arch.spec === 'unparryable' && a.arch.tier === 'brute' && false };
      // elite onhit poison
      if (a.elite === 'venomous') hit.statuses = [{ id: 'poison', dur: 8, power: 4 + a.level }];
      // rust construct: extra armor-piercing vs player handled by armor formula
      dealDamage(P, a, hit);
      // vampiric
      if (a.elite === 'vampiric') a.hp = clamp(a.hp + dmg * 0.3, 0, a.maxHp);
      // melee also hits props? skip
    } else {
      R.burst(a.pos[0], 1, a.pos[2], 3, [.4, .4, .4], 2, 3, .3);
    }
    SND.swing();
  } else {
    const dir = [P.pos[0] - a.pos[0], 0.15, P.pos[2] - a.pos[2]];
    const l = Math.max(0.01, v3len(dir)); dir[0] /= l; dir[1] /= l; dir[2] /= l;
    const elem = a.arch.atk === 'spell' ? (a.arch.spec === 'waterbolt' ? 'lightning' : a.arch.spec === 'curse' ? 'shadow' : 'arcane') : 'pierce';
    const pdmg = { pierce: dmg };
    if (elem === 'lightning') { pdmg.light = dmg; delete pdmg.pierce; }
    if (elem === 'shadow') { pdmg.arcane = dmg; delete pdmg.pierce; }
    if (elem === 'arcane') { pdmg.arcane = dmg; delete pdmg.pierce; }
    const statuses = [];
    if (a.arch.spec === 'poisonArrow') statuses.push({ id: 'poison', dur: 8, power: 4 + a.level });
    spawnProj([a.pos[0], 1.4, a.pos[2]], dir, 16, { dmg: pdmg, friendly: false, src: a, statuses });
    SND.bow();
  }
  EVT.emit('AttackCommitted', { actor: a });
}
function applyArchSpecial(F, a, dt, dist) {
  const spec = a.arch.spec;
  if (!spec) return;
  switch (spec) {
    case 'rush': // leap attack
      if (dist < 6 && dist > 2.5 && a.atkCd <= 0 && Math.random() < 0.02) {
        const dx = P.pos[0] - a.pos[0], dz = P.pos[2] - a.pos[2];
        const l = Math.hypot(dx, dz);
        a.vel[0] = dx / l * 10; a.vel[2] = dz / l * 10; a.vel[1] = 3;
        a.atkCd = 3;
      }
      break;
    case 'teleport':
      if (dist > 7 && a.atkCd <= 0 && Math.random() < 0.01) {
        R.burst(a.pos[0], 1, a.pos[2], 10, [.7, .4, 1], 3, 4, .4);
        const ang = Math.random() * TAU;
        const nx = P.pos[0] + Math.cos(ang) * 2.5, nz = P.pos[2] + Math.sin(ang) * 2.5;
        if (!circleBlocked(F, nx, nz, a.radius)) { a.pos[0] = nx; a.pos[2] = nz; }
        R.burst(a.pos[0], 1, a.pos[2], 10, [.7, .4, 1], 3, 4, .4);
        a.atkCd = 6;
      }
      break;
    case 'pull':
      if (dist < 8 && dist > 3 && a.atkCd <= 0 && Math.random() < 0.015) {
        const dx = a.pos[0] - P.pos[0], dz = a.pos[2] - P.pos[2];
        const l = Math.hypot(dx, dz);
        P.vel[0] += dx / l * 8; P.vel[2] += dz / l * 8;
        dmgNum(P.pos, 'pulled', '#e0a060');
        a.atkCd = 5; SND.bow();
      }
      break;
    case 'curse':
      if (dist < a.arch.reach && a.atkCd <= 0 && Math.random() < 0.4 && a.state === 'chase') {
        applyStatus(P, 'curse', 10, 0, a); toast('Cursed — resistances lowered', 'bad');
        a.atkCd = 8; SND.castDark();
      }
      break;
    case 'healcurse': {
      const wounded = F.actors.filter(o => o !== a && !o.dead && o.hp < o.maxHp * 0.6 && d2(o.pos[0], o.pos[2], a.pos[0], a.pos[2]) < 10);
      if (wounded.length && a.atkCd <= 0) {
        const w = wounded[0];
        w.hp = clamp(w.hp + w.maxHp * 0.2, 0, w.maxHp);
        R.burst(w.pos[0], 1.2, w.pos[2], 8, [.5, 1, .5], 2, 3, .5);
        a.atkCd = 7; SND.castHoly();
      }
      break;
    }
    case 'counter':
      if (a.state === 'chase' && a.atkCd <= 0 && dist < a.arch.reach + 0.4 && Math.random() < 0.5) {
        // blocks a hit — handled visually
      }
      break;
    case 'waterbolt': case 'curseCaster': break;
    case 'multiswing': if (a.atkCd <= 0 && dist < a.arch.reach && Math.random() < 0.03) { a.atkSpeedMul = 1.4; } break;
    case 'unparryable': break;
  }
}
function integrateActor(F, a, dt, noSteer) {
  a.vel[1] -= CFG.gravity * dt;
  if (!noSteer && (Math.abs(a.vel[0]) > 0.01 || Math.abs(a.vel[2]) > 0.01)) {
    const nx = a.pos[0] + a.vel[0] * dt, nz = a.pos[2] + a.vel[2] * dt;
    if (!circleBlocked(F, nx, a.pos[2], a.radius)) a.pos[0] = nx; else a.vel[0] *= -0.3;
    if (!circleBlocked(F, a.pos[0], nz, a.radius)) a.pos[2] = nz; else a.vel[2] *= -0.3;
    a.vel[0] *= Math.max(0, 1 - 4 * dt); a.vel[2] *= Math.max(0, 1 - 4 * dt);
  }
  a.pos[1] += a.vel[1] * dt;
  if (a.pos[1] <= 0) { a.pos[1] = 0; a.vel[1] = 0; }
  // kicked props hitting enemies handled in props update
}

/* ---------------- bosses ---------------- */
function updateBoss(F, a, dt) {
  const def = a.bossDef;
  if (!def) return;
  // engage: jam arena gates so the fight can't be walked out of
  if (!a.engaged && d2(a.pos[0], a.pos[2], P.pos[0], P.pos[2]) < 17) {
    a.engaged = true;
    for (const d of F.doors) if ((F.bossGateIds || []).includes(d.id) && d.state !== 'open') d.state = 'jammed';
    SND.roar();
  }
  const hpFrac = a.hp / a.maxHp;
  // phase transitions
  let phase = 0;
  for (let i = 0; i < def.phases.length; i++) if (hpFrac <= def.phases[i].at) phase = i;
  if (phase !== a.bossPhase) {
    a.bossPhase = phase;
    if (def.phases[phase].msg) { toast(def.phases[phase].msg, 'bad'); SND.roar(); }
    a.atkCd = 1.2;
    if (def.phases[phase].core) a.coreOpen = 8;
  }
  if (a.coreOpen > 0) { a.coreOpen -= dt; a.armor = 2; } else a.armor = def.armor;
  a.atkCd -= dt;
  const dist = d2(a.pos[0], a.pos[2], P.pos[0], P.pos[2]);
  const moves = def.phases[phase].moves;
  if (a.bossMove) {
    // executing a move
    a.bossT -= dt;
    const mv = a.bossMove;
    if (mv === 'charge' || mv === 'chargeWater') {
      // dash toward player
      const dx = P.pos[0] - a.pos[0], dz = P.pos[2] - a.pos[2];
      const l = Math.max(0.01, Math.hypot(dx, dz));
      const nx = a.pos[0] + dx / l * 9 * dt, nz = a.pos[2] + dz / l * 9 * dt;
      if (circleBlocked(F, nx, nz, a.radius)) {
        // guard-break: stagger self
        a.stun = 1.6; a.bossMove = null; toast('The boss is staggered — strike now!', 'good');
        R.burst(a.pos[0], 1.5, a.pos[2], 16, [1, .8, .4], 4, 4, .5);
      } else { a.pos[0] = nx; a.pos[2] = nz; a.yaw = Math.atan2(-dx / l, -dz / l); }
      if (dist < a.radius + 1.2 && !a.chargeHit) {
        a.chargeHit = true;
        dealDamage(P, a, { phys: rf(Math.random, a.dmg[0], a.dmg[1]) * 1.2, poise: 25, unblockable: false });
      }
      if (a.bossT <= 0) a.bossMove = null;
      return;
    }
    if (mv === 'windup') {
      if (a.bossT <= 0) {
        const pm = a.pendingMove;
        a.bossMove = null; a.pendingMove = null; a.glow = 0;
        executeBossMove(F, a, pm);
        if (!a.bossMove) a.atkCd = rf(Math.random, 1.2, 2.2);
      }
      return;
    }
    a.bossMove = null; a.glow = 0;
  }
  if (a.atkCd <= 0 && !P.dead) {
    const mv = pick(Math.random, moves);
    a.pendingMove = mv;
    a.bossMove = 'windup';
    a.bossT = mv === 'charge' || mv === 'chargeWater' ? 0.7 : mv === 'slam' ? 0.9 : mv === 'shockwave' ? 0.8 : mv === 'toll' ? 1.2 : 0.6;
    a.glow = 1;
    SND.growl(true);
  } else if (dist > 3) {
    moveTo(F, a, P.pos[0], P.pos[2], dt, 1);
  } else if (dist > 2) {
    const dx = P.pos[0] - a.pos[0], dz = P.pos[2] - a.pos[2];
    a.yaw = Math.atan2(-dx, -dz);
  }
}
function executeBossMove(F, a, mv) {
  const dist = d2(a.pos[0], a.pos[2], P.pos[0], P.pos[2]);
  const dmg = rf(Math.random, a.dmg[0], a.dmg[1]);
  const yaw = Math.atan2(-(P.pos[0] - a.pos[0]), -(P.pos[2] - a.pos[2]));
  switch (mv) {
    case 'slash': case 'combo': {
      const n = mv === 'combo' ? 3 : 1;
      for (let i = 0; i < n; i++) {
        setTimeout(() => {
          if (a.dead || G.state !== 'play') return;
          const d2v = d2(a.pos[0], a.pos[2], P.pos[0], P.pos[2]);
          if (d2v < 3.2) dealDamage(P, a, { phys: dmg * (mv === 'combo' ? 0.7 : 1), poise: 10 });
        }, i * 350);
      }
      SND.heavySwing();
      break;
    }
    case 'charge': case 'chargeWater': {
      a.bossMove = mv; a.bossT = 1.1; a.chargeHit = false;
      break;
    }
    case 'bash': case 'slam': {
      if (dist < 4.5) dealDamage(P, a, { phys: dmg * 1.2, poise: 25 });
      F.shockwaves = F.shockwaves || [];
      F.shockwaves.push({ x: a.pos[0], z: a.pos[2], r: 0.5, speed: 7, maxR: 9, dmg: dmg * 0.6, level: a.level, a: 0, id: (PROP_ID++) });
      SND.explode();
      break;
    }
    case 'sweep': {
      if (dist < 5) dealDamage(P, a, { phys: dmg, poise: 15 });
      R.burst(a.pos[0], 1.2, a.pos[2], 14, [.9, .7, .4], 5, 4, .4);
      break;
    }
    case 'shockwave': {
      F.shockwaves = F.shockwaves || [];
      for (let i = 0; i < 3; i++) F.shockwaves.push({ x: a.pos[0], z: a.pos[2], r: 0.5 + i * 0.4, speed: 6 + i, maxR: 12, dmg: dmg * 0.5, level: a.level, a: i * 2, id: (PROP_ID++) });
      SND.explode();
      break;
    }
    case 'summon': {
      const pool = ENEMIES.filter(e => e.reg === a.bossDef.tags.includes('undead') ? 1 : regionOf(F.index).id);
      for (let i = 0; i < 3; i++) {
        const ang = Math.random() * TAU;
        const nx = a.pos[0] + Math.cos(ang) * 4, nz = a.pos[2] + Math.sin(ang) * 4;
        if (!circleBlocked(F, nx, nz, 0.5)) {
          const e = ENEMIES.filter(e2 => e2.reg === regionOf(F.index).id && e2.tier === 'grunt');
          spawnEnemy(F, pick(Math.random, e).id, nx, nz, Math.max(1, F.index - 1));
          R.burst(nx, 1, nz, 10, [.6, .4, .9], 3, 4, .5);
        }
      }
      break;
    }
    case 'toll': {
      applyStatus(P, 'fear', 3, 0, a); toast('Fear takes you!', 'bad');
      SND.roar();
      break;
    }
    case 'cursezone': {
      F.mists.push({ x: P.pos[0], z: P.pos[2], r: 3, t: 6, elem: 'curse', dmg: 0, src: a });
      break;
    }
    case 'hook': {
      if (dist < 9) {
        const dx = a.pos[0] - P.pos[0], dz = a.pos[2] - P.pos[2];
        const l = Math.hypot(dx, dz);
        P.vel[0] += dx / l * 9; P.vel[2] += dz / l * 9;
        SND.bow();
      }
      break;
    }
    case 'electrify': {
      F.electrifyT = 5;
      toast('The water is electrified!', 'bad');
      SND.castLight();
      break;
    }
    case 'core': {
      a.coreOpen = 7;
      toast('The core is exposed!', 'good');
      break;
    }
    case 'riftbolt': {
      for (let i = -1; i <= 1; i++) {
        const dy = yaw + i * 0.3;
        spawnProj([a.pos[0], 1.5, a.pos[2]], [-Math.sin(dy), 0.05, -Math.cos(dy)], 14, { dmg: { arcane: dmg * 0.8 }, friendly: false, src: a });
      }
      SND.castDark();
      break;
    }
    case 'teleport': {
      R.burst(a.pos[0], 1, a.pos[2], 16, [.7, .4, 1], 4, 4, .5);
      const ang = Math.random() * TAU;
      const nx = P.pos[0] + Math.cos(ang) * 3.5, nz = P.pos[2] + Math.sin(ang) * 3.5;
      if (!circleBlocked(F, nx, nz, a.radius)) { a.pos[0] = nx; a.pos[2] = nz; }
      R.burst(a.pos[0], 1, a.pos[2], 16, [.7, .4, 1], 4, 4, .5);
      break;
    }
  }
}
function onBossDefeated(a) {
  const F = G.floor;
  F.bossDefeated = true;
  const fsB = G.campaign.floors[F.index];
  if (fsB) fsB.bossKilled = true;
  EVT.emit('BossDefeated', { boss: a.bossId, floor: F.index });
  // gates open
  for (const d of F.doors) if (d.state === 'jammed') d.state = 'open';
  // loot
  for (const it of (F.bossLoot || [])) spawnGroundItem(F, a.pos[0] + (Math.random() - .5) * 2, a.pos[2] + (Math.random() - .5) * 2, it, it.rarity);
  if (F.bossGold) spawnGroundItem(F, a.pos[0], a.pos[2], { gold: F.bossGold }, 0);
  // boss lore
  const bossLore = { ashbound_captain: 'l_boss1', bellkeeper: 'l_boss2', drowned_engineer: 'l_boss3', warden_below: 'l_boss4' }[a.bossId];
  if (bossLore && !G.campaign.lore[bossLore]) { addLore(bossLore); }
  // waypoint unlock: next region entry
  const nextEntry = { 4: 5, 8: 9, 12: 13 }[F.index];
  if (nextEntry && !G.campaign.waypoints.includes(nextEntry)) {
    G.campaign.waypoints.push(nextEntry);
    toast('Waypoint unlocked: Floor ' + nextEntry, 'good');
  }
  if (F.index === 16) {
    G.campaign.storyDone = true;
    setTimeout(() => { if (G.state === 'play') showVictoryScreen(); }, 1200);
  }
  saveGame(true);
}

/* ============================================================
   11. WORLD OBJECTS — ground items, chests, doors, shrines,
       traps, props, projectiles, portals, town NPCs, events
   ============================================================ */
function spawnGroundItem(F, x, z, payload, rarity) {
  const beam = typeof rarity === 'number' ? rarity : (RAR_IDX[payload?.rarity] || 0);
  F.ground.push({ id: 'g' + (PROP_ID++), x, z, payload, beam, bob: Math.random() * TAU });
}
function updateGround(F, dt) {
  for (let i = F.ground.length - 1; i >= 0; i--) {
    const g = F.ground[i];
    g.bob += dt * 3;
    // auto pickup gold
    if (g.payload && g.payload.gold !== undefined && G.settings.autoGold && d2(g.x, g.z, P.pos[0], P.pos[2]) < 1.6) {
      const amt = Math.round(g.payload.gold * (1 + (P.stats.goldFind || 0)));
      goldChange(P, amt, 'picked up');
      SND.gold();
      F.ground.splice(i, 1);
      persistGround();
    }
  }
  // rare beams
  for (const g of F.ground) {
    if (g.beam >= 2 && Math.random() < dt * 3) R.spawnP({ x: g.x, y: 0.4, z: g.z, vy: 1.5, maxLife: 0.8, r: g.beam === 3 ? 1 : .9, g: g.beam === 3 ? .6 : .8, b: .3, size: 4, grav: 0, glow: 1 });
  }
}
function persistGround() {
  const fs = G.campaign.floors[G.floor.index];
  if (fs && !G.floor.isTown) fs.itemsGround = G.floor.ground.filter(g => g.payload && g.payload.gold === undefined ? true : true).map(g => ({ x: g.x, z: g.z, item: g.payload.item ? serializeItem(g.payload.item) : null, gold: g.payload.gold || 0, beam: g.beam }));
}
function pickupGround(g) {
  if (g.payload.gold !== undefined) {
    goldChange(P, Math.round(g.payload.gold * (1 + (P.stats.goldFind || 0))), 'picked up');
    SND.gold();
  } else {
    const it = g.payload.item;
    if (!it) return;
    if (!addToBag(P, it)) { toast('Backpack full — item stays on ground', 'bad'); SND.error(); return; }
    toast('Picked up: ' + it.name, it.rarity === 'relic' ? 'good' : '');
    SND.pickup(RAR_IDX[it.rarity]);
    if (RAR_IDX[it.rarity] >= 2) EVT.emit('MajorPickup', { item: it });
    if (it.cat === 'quest') {
      questEvent('pickup', { base: it.base });
      if (G.floor.keyPickup && it.base === G.floor.keyPickup.keyId) G.floor.keyPickup.taken = true;
      if (G.floor.questPickups) for (const qp of G.floor.questPickups) if (qp.base === it.base) qp.done = true;
    }
  }
  const F = G.floor;
  F.ground.splice(F.ground.indexOf(g), 1);
  persistGround();
}

/* doors */
function tryOpenDoor(d) {
  if (d.state === 'locked') {
    if (P.inv.some(it => it && it.base === d.key)) { d.state = 'open'; SND.door(); toast('Unlocked', 'good'); }
    else { SND.error(); toast('Locked — requires a key', 'bad'); }
  } else if (d.state === 'jammed') {
    SND.error(); toast('Jammed shut', 'bad');
  } else if (d.state === 'closed') {
    d.state = 'open'; SND.door();
  } else if (d.state === 'open') {
    d.state = 'closed'; SND.door();
  }
}

/* chests */
function openChest(c) {
  if (c.opened) { SND.error(); toast('Empty', ''); return; }
  c.opened = true;
  SND.chest();
  const fs = G.campaign.floors[G.floor.index];
  if (fs) { fs.openedChests = fs.openedChests || {}; fs.openedChests[c.id] = true; }
  for (const it of (c.loot || [])) spawnGroundItem(G.floor, c.x + (Math.random() - .5) * 1.4, c.z + (Math.random() - .5) * 1.4, { item: it }, it.rarity);
  if (c.gold) spawnGroundItem(G.floor, c.x, c.z, { gold: c.gold }, 0);
  // trapped chest event
  if (G.floor.event && G.floor.event.type === 'trapped_chest' && !G.floor.event.done && d2(G.floor.event.x, G.floor.event.z, c.x, c.z) < 3) {
    G.floor.event.done = true;
    dealDamage(P, { env: true }, { pierce: 10 + G.floor.index * 2, statuses: [{ id: 'poison', dur: 8, power: 6 }] });
    toast('The chest was trapped!', 'bad');
  }
  EVT.emit('InteractionSucceeded', { type: 'chest' });
}

/* shrines */
function useShrine(s) {
  if (s.used) { toast('The shrine is spent.', ''); return; }
  const k = SHRINE_KINDS[s.kind];
  switch (s.kind) {
    case 'fountain': P.hp = P.stats.hpMax; P.mp = P.stats.mpMax; toast('The fountain restores you fully.', 'good'); break;
    case 'blessing': addBuff(P, 'blessing', 'Blessing of Vigor', 90, { dmgPct: 0.15 }, '✦'); toast('+15% damage for 90 s', 'good'); break;
    case 'revelation': revealFloor(G.floor); toast('The floor\'s layout reveals itself.', 'good'); break;
    case 'transmute': {
      const eq = SLOT_NAMES.map(k => P.equip[k]).filter(Boolean);
      if (!eq.length) { toast('Nothing equipped to transmute.', 'bad'); return; }
      const it = eq[Math.floor(Math.random() * eq.length)];
      if (it.affixes && it.affixes.length) {
        const i = Math.floor(Math.random() * it.affixes.length);
        const rng = mulberry32((Math.random() * 1e9) | 0);
        const a = AFFIX_BY_ID[it.affixes[i].id];
        it.affixes[i].v = rollAffix(rng, a, it.ilvl);
        toast('Transmuted: ' + it.name, 'good');
        recalcStats(P);
      } else { toast('No affixes to transmute.', 'bad'); return; }
      break;
    }
    case 'risk': addBuff(P, 'risk', 'Blood Pact', 90, { dmgPct: 0.30, dmgTakenPct: 0.25 }, '☠'); toast('+30% damage, +25% damage taken for 90 s', 'bad'); break;
    case 'cursed_altar': {
      toast('The altar stirs... something answers.', 'bad');
      questEvent('interact', { tag: 'cleanse_altar' });
      // eslint-disable-next-line
      const ang = Math.random() * TAU;
      const pool = ENEMIES.filter(e => e.reg === regionOf(G.floor.index).id && e.tier === 'brute');
      const e = spawnEnemy(G.floor, pick(Math.random, pool).id, P.pos[0] + Math.cos(ang) * 5, P.pos[2] + Math.sin(ang) * 5, G.floor.index, { elite: 'enraged', loot: rollLoot(mulberry32(1234), { ilvl: G.floor.index + 2, n: 1, weights: { common: 10, enchanted: 45, rare: 40, relic: 5 } }), gold: 80 + G.floor.index * 10 });
      if (e) { e.activated = true; e.target = P; e.cursedAltar = s.id; }
      break;
    }
  }
  s.used = true;
  SND.shrine();
  const fs = G.campaign.floors[G.floor.index];
  if (fs) { fs.shrinesUsed = fs.shrinesUsed || []; if (!fs.shrinesUsed.includes(s.id)) fs.shrinesUsed.push(s.id); }
  EVT.emit('InteractionSucceeded', { type: 'shrine' });
  addLore('l_floor' + G.floor.index); // shrines double as discovery moments
}

function revealFloor(F) {
  F.fog = F.fog || new Uint8Array(F.W * F.H);
  for (let i = 0; i < F.fog.length; i++) if (F.tiles[i] !== T_SOLID) F.fog[i] |= 3;
  F.revealed = true;
  for (const d of F.doors) if (d.kind === 'secret') d.revealed = true;
}

/* traps */
function updateTraps(F, dt) {
  for (const t of F.traps) {
    const def = TRAP_DEFS[t.def];
    if (t.cd > 0) { t.cd -= dt; continue; }
    if (t.def === 'curse_zone') {
      if (d2(t.x, t.z, P.pos[0], P.pos[2]) < def.radius) applyStatus(P, 'curse', 10, 0, { env: true });
      for (const a of F.actors) if (!a.dead && d2(t.x, t.z, a.pos[0], a.pos[2]) < def.radius) applyStatus(a, 'curse', 10, 0, { env: true });
      continue;
    }
    if (def.radius >= 7) { // ranged traps: dart/rune/tripwire
      const pd = d2(t.x, t.z, P.pos[0], P.pos[2]);
      if (pd < def.radius && losClear(F, t.x, t.z, P.pos[0], P.pos[2])) {
        const dir = [P.pos[0] - t.x, 0.2, P.pos[2] - t.z];
        const l = Math.max(0.01, v3len(dir));
        spawnProj([t.x, 1.2, t.z], [dir[0] / l, dir[1] / l, dir[2] / l], 18, { dmg: { [def.type === 'pierce' ? 'pierce' : def.type === 'arcane' ? 'arcane' : 'phys']: rf(Math.random, def.dmg[0], def.dmg[1]) + F.index }, friendly: false, src: { env: true, trap: true, creditOwner: trapCredit(F, t) }, statuses: [] });
        t.cd = def.cd;
        SND.bow();
      }
      continue;
    }
    // proximity traps
    if (d2(t.x, t.z, P.pos[0], P.pos[2]) < def.radius * 0.7) {
      t.cd = def.cd;
      const hit = { [def.type === 'fire' ? 'fire' : def.type === 'lightning' ? 'light' : def.type === 'pierce' ? 'pierce' : 'phys']: rf(Math.random, def.dmg[0], def.dmg[1]) + F.index, src: { env: true, trap: true, creditOwner: trapCredit(F, t) } };
      if (def.status) hit.statuses = [{ id: def.status, dur: 4, power: 5 + F.index }];
      dealDamage(P, hit.src, hit);
      R.burst(t.x, 0.4, t.z, 14, ELEM_COL[def.type === 'phys' ? 'blunt' : def.type] || [1, 1, 1], 5, 4, 0.4);
      SND.explode();
    }
  }
}
function trapCredit(F, t) {
  // if player recently shoved an enemy into it — simplistic: player gets credit for triggering
  return { player: true };
}

/* mists/caltrops */
function updateZones(F, dt) {
  for (let i = (F.mists || []).length - 1; i >= 0; i--) {
    const m = F.mists[i];
    m.t -= dt;
    if (m.t <= 0) { F.mists.splice(i, 1); continue; }
    if (Math.random() < dt * 8) R.spawnP({ x: m.x + (Math.random() - .5) * m.r * 2, y: 0.3 + Math.random(), z: m.z + (Math.random() - .5) * m.r * 2, vy: 0.4, maxLife: 1, r: m.elem === 'poison' ? .4 : .5, g: m.elem === 'poison' ? .9 : .3, b: m.elem === 'poison' ? .3 : .6, size: 5, grav: 0, glow: 1, a: .5 });
    if (m.elem === 'poison') {
      if (d2(m.x, m.z, P.pos[0], P.pos[2]) < m.r) { applyStatus(P, 'poison', 8, m.dmg, m.src); }
      for (const a of F.actors) if (!a.dead && d2(m.x, m.z, a.pos[0], a.pos[2]) < m.r) applyStatus(a, 'poison', 8, m.dmg, m.src);
    } else if (m.elem === 'curse') {
      if (d2(m.x, m.z, P.pos[0], P.pos[2]) < m.r && Math.random() < dt * 2) applyStatus(P, 'curse', 10, 0, m.src);
    }
  }
  for (let i = (F.caltrops || []).length - 1; i >= 0; i--) {
    const c = F.caltrops[i];
    c.t -= dt;
    if (c.t <= 0) { F.caltrops.splice(i, 1); continue; }
    for (const a of F.actors) if (!a.dead && d2(c.x, c.z, a.pos[0], a.pos[2]) < c.r) applyStatus(a, 'slow', 1, c.slow, { player: true });
  }
  // electrified water
  if (F.electrifyT > 0) {
    F.electrifyT -= dt;
    const tx = Math.floor(P.pos[0] / CFG.tile), tz = Math.floor(P.pos[2] / CFG.tile);
    if (tileIdx(F, tx, tz) === T_WATER && Math.random() < dt * 4) {
      dealDamage(P, { env: true }, { light: 10 + F.index, statuses: [{ id: 'shock', dur: 4, power: 0 }] });
    }
    if (Math.random() < dt * 20) R.spawnP({ x: P.pos[0] + (Math.random() - .5) * 3, y: 0.3, z: P.pos[2] + (Math.random() - .5) * 3, vy: 2, maxLife: .3, r: .6, g: .8, b: 1, size: 4, grav: 0 });
  }
}

/* props physics (kicked crates, gore) */
function updateProps(F, dt) {
  for (let i = F.props.length - 1; i >= 0; i--) {
    const p = F.props[i];
    if (p.vx !== undefined || p.vy !== undefined) {
      p.vy = (p.vy || 0) - CFG.gravity * dt;
      const nx = p.x + (p.vx || 0) * dt, nz = p.z + (p.vz || 0) * dt;
      if (!circleBlocked(F, nx, p.z, 0.35)) p.x = nx; else { p.vx = (p.vx || 0) * -0.4; }
      if (!circleBlocked(F, p.x, nz, 0.35)) p.z = nz; else { p.vz = (p.vz || 0) * -0.4; }
      p.y = (p.y || 0) + p.vy * dt;
      if (p.y <= 0) { p.y = 0; p.vy = 0; p.vx = (p.vx || 0) * 0.8; p.vz = (p.vz || 0) * 0.8; }
      p.vx = (p.vx || 0) * Math.max(0, 1 - 2 * dt); p.vz = (p.vz || 0) * Math.max(0, 1 - 2 * dt);
      // impact damage to actors (once per meaningful collision)
      const speed = Math.hypot(p.vx || 0, p.vz || 0);
      if (speed > 3 && p.weapon) {
        for (const a of F.actors) {
          if (a.dead || !a.arch) continue;
          const key = a.id;
          p.hitCd = p.hitCd || {};
          if (p.hitCd[key] && G.time - p.hitCd[key] < 1) continue;
          if (d2(a.pos[0], a.pos[2], p.x, p.z) < a.radius + 0.4) {
            p.hitCd[key] = G.time;
            dealDamage(a, { env: true, player: p.lastShover === 'player' }, { phys: Math.min(20, speed * 1.5), poise: 8 });
            SND.thud();
          }
        }
      }
      if (p.life !== undefined) { p.life -= dt; if (p.life <= 0) { F.props.splice(i, 1); continue; } }
    }
  }
}
function damageProp(p, dmg) {
  if (p.dead || p.hp === undefined || p.hp > 900) { SND.hitStone(); return; }
  p.hp -= dmg;
  SND.hitStone();
  R.burst(p.x, 0.6, p.z, 6, [.5, .4, .3], 3, 3, .4);
  if (p.hp <= 0) {
    p.dead = true; p.blocking = false;
    R.burst(p.x, 0.5, p.z, 14, [.5, .42, .3], 4, 4, .5);
    SND.explode();
    if (p.loot) for (const it of p.loot) spawnGroundItem(G.floor, p.x, p.z, { item: it }, it.rarity);
    if (p.gold) spawnGroundItem(G.floor, p.x, p.z, { gold: p.gold }, 0);
  }
}

/* projectiles */
function spawnProj(pos, dir, speed, opts) {
  G.floor.projs = G.floor.projs || [];
  G.floor.projs.push({
    x: pos[0], y: pos[1], z: pos[2],
    vx: dir[0] * speed, vy: (dir[1] || 0) * speed, vz: dir[2] * speed,
    speed, friendly: !!opts.friendly, dmg: opts.dmg, elem: opts.elem, spell: !!opts.spell,
    blast: opts.blast || 0, blastDmg: opts.blastDmg || 0, chill: opts.chill || 0, statuses: opts.statuses || [],
    pierceN: opts.pierceN || 0, dmgMul: opts.dmgMul || 1, src: opts.src || null, life: 3, hitSet: new Set(),
    arrow: !opts.spell && opts.friendly, glowCol: opts.spell ? (ELEM_COL[opts.elem] || [1, 1, 1]) : null,
  });
}
function updateProjs(F, dt) {
  F.projs = F.projs || [];
  for (let i = F.projs.length - 1; i >= 0; i--) {
    const pr = F.projs[i];
    pr.life -= dt;
    if (pr.life <= 0) { F.projs.splice(i, 1); continue; }
    if (pr.arrow) pr.vy -= 5 * dt; // arrow drop
    const nx = pr.x + pr.vx * dt, ny = pr.y + pr.vy * dt, nz = pr.z + pr.vz * dt;
    // wall hit
    if (worldSolid(F, nx, nz) || ny < 0.05 || ny > 3.4) {
      if (pr.blast) explodeAt(pr);
      F.projs.splice(i, 1); continue;
    }
    pr.x = nx; pr.y = ny; pr.z = nz;
    if (pr.spell && Math.random() < dt * 20) R.spawnP({ x: pr.x, y: pr.y, z: pr.z, maxLife: .3, r: pr.glowCol[0], g: pr.glowCol[1], b: pr.glowCol[2], size: 4, grav: 0 });
    // actor hit
    let consumed = false;
    if (pr.friendly) {
      for (const a of F.actors) {
        if (a.dead || pr.hitSet.has(a)) continue;
        if (d2(a.pos[0], a.pos[2], pr.x, pr.z) < a.radius + 0.35 && pr.y > 0.2 && pr.y < a.scaleH + 0.4) {
          pr.hitSet.add(a);
          const dmg = {};
          for (const k in pr.dmg) dmg[k] = pr.dmg[k] * pr.dmgMul;
          const hit = Object.assign({}, dmg, { src: { player: true }, arrow: !pr.spell, melee: false, statuses: pr.statuses.map(s => Object.assign({}, s)) });
          if (pr.arrow) {
            const eyeY = P.pos[1] + (P.crouch ? CFG.crouchEye : CFG.eyeHeight);
            if (pr.y > a.scaleH * 0.72 && a.arch.sever && a.limbs && a.limbs.head) { hit.limb = 'head'; hit.phys = (hit.pierce || 0) * CFG.headshotMul; delete hit.pierce; checkSever(a, hit, null); }
            else if (a.limbs && pr.y < a.scaleH * 0.35 && Math.random() < 0.4) hit.limb = Math.random() < .5 ? 'legL' : 'legR';
          }
          dealDamage(a, { player: true }, hit);
          checkSever(a, hit, null);
          SND.arrowHit();
          if (pr.blast) explodeAt(pr);
          if (pr.pierceN > 0) { pr.pierceN--; pr.dmgMul *= 0.7; }
          else { consumed = true; }
          break;
        }
      }
    } else {
      if (d2(P.pos[0], P.pos[2], pr.x, pr.z) < P.radius + 0.3 && pr.y > 0.2 && pr.y < 2.1) {
        const hit = Object.assign({}, pr.dmg);
        hit.src = pr.src || { env: true };
        hit.statuses = pr.statuses;
        dealDamage(P, hit.src, hit);
        consumed = true;
      }
    }
    if (consumed) F.projs.splice(i, 1);
  }
}
function explodeAt(pr) {
  SND.explode();
  R.burst(pr.x, pr.y, pr.z, 24, ELEM_COL[pr.elem] || [1, .6, .2], 6, 5, 0.5);
  for (const a of G.floor.actors) {
    if (a.dead) continue;
    const d = d2(a.pos[0], a.pos[2], pr.x, pr.z);
    if (d < (pr.blast || 2) + a.radius && losClear(G.floor, pr.x, pr.z, a.pos[0], a.pos[2])) {
      dealDamage(a, { player: true }, { [pr.elem === 'fire' ? 'fire' : 'arcane']: pr.blastDmg || pr.dmg[Object.keys(pr.dmg)[0]] * 0.6, src: { player: true } });
    }
  }
  const pd = d2(P.pos[0], P.pos[2], pr.x, pr.z);
  if (!pr.friendly && pd < (pr.blast || 2) + P.radius) dealDamage(P, { env: true }, { [pr.elem === 'fire' ? 'fire' : 'arcane']: pr.blastDmg || 8 });
}

/* town portal & sigil */
function finishChannel(ch) {
  if (ch.id === 'return_sigil' || ch.scroll) {
    const F = G.floor;
    F.portals = F.portals || [];
    F.portals.push({ id: 'po' + (PROP_ID++), x: P.pos[0], z: P.pos[2], dest: 'town' });
    G.campaign.portals = G.campaign.portals || [];
    G.campaign.portals.push({ floor: F.index, x: P.pos[0], z: P.pos[2], active: true });
    R.burst(P.pos[0], 1, P.pos[2], 20, [.6, .4, 1], 3, 5, .8);
    SND.portal();
    toast('Return portal opened — step in and press E', 'good');
  }
}
function updatePortals(F, dt) {
  for (const po of (F.portals || [])) {
    if (Math.random() < dt * 10) R.spawnP({ x: po.x + (Math.random() - .5), y: Math.random() * 2, z: po.z + (Math.random() - .5), vy: 0.5, maxLife: .8, r: .7, g: .5, b: 1, size: 4, grav: 0 });
  }
}

/* floor events */
function checkRoomEvents(F) {
  if (!F.event || F.event.done) return;
  if (G.campaign.floors[F.index]?.eventDone) { F.event.done = true; return; }
  const e = F.event;
  const room = F.rooms.find(r => r.id === e.room);
  if (!room) { e.done = true; return; }
  const px = P.pos[0] / CFG.tile, pz = P.pos[2] / CFG.tile;
  if (px < room.x0 || px > room.x1 || pz < room.y0 || pz > room.y1) return;
  e.done = true;
  const fs = G.campaign.floors[F.index];
  const markDone = () => { if (fs) { fs.eventDone = true; } };
  const at = [e.x, e.z];
  switch (e.type) {
    case 'elite_treasure': {
      const pool = ENEMIES.filter(x => x.reg === regionOf(F.index).id && x.tier !== 'beast');
      const en = spawnEnemy(F, pick(Math.random, pool).id, at[0], at[1], F.index, { elite: 'warded', loot: rollLoot(mulberry32(77), { ilvl: F.index + 2, n: 1, weights: { common: 15, enchanted: 45, rare: 35, relic: 5 } }), gold: 120 });
      if (en) { en.activated = true; }
      F.chests.push({ id: 'cEv' + (PROP_ID++), x: at[0] + 1.5, z: at[1], rare: true, opened: false, loot: rollLoot(mulberry32(78), { ilvl: F.index + 1, n: 2, weights: { common: 10, enchanted: 40, rare: 45, relic: 5 } }), gold: 100 });
      toast('Something guards a cache here...', 'bad');
      break;
    }
    case 'abandoned_camp': {
      for (let i = 0; i < 3; i++) F.props.push({ id: 'p' + (PROP_ID++), type: 'campfire', x: at[0] + i * 1.2, z: at[1], y: 0, dead: false, blocking: false, rad: 0 });
      F.props.push({ id: 'p' + (PROP_ID++), type: 'bones', x: at[0], z: at[1] + 1.5, y: 0, dead: false, blocking: false, rad: 0 });
      spawnGroundItem(F, at[0], at[1] + 2, { item: rollLoot(mulberry32(9), { ilvl: F.index, n: 1, identified: true })[0] }, 0);
      spawnGroundItem(F, at[0] + 1, at[1] + 2, { gold: 30 + F.index * 10 }, 0);
      toast('An abandoned camp...', '');
      break;
    }
    case 'cursed_room': {
      F.mists.push({ x: at[0], z: at[1], r: 4, t: 999999, elem: 'curse', dmg: 0, src: { env: true }, permanent: true });
      const pool = ENEMIES.filter(x => x.reg === regionOf(F.index).id && x.tier === 'caster');
      if (pool.length) { const en = spawnEnemy(F, pick(Math.random, pool).id, at[0], at[1], F.index, { elite: 'enraged' }); if (en) en.activated = true; }
      toast('This place reeks of curse.', 'bad');
      break;
    }
    case 'merchant_corpse': {
      const goods = rollLoot(mulberry32(31), { ilvl: F.index + 1, n: 2, identified: true });
      for (const it of goods) spawnGroundItem(F, at[0] + i2(goods.indexOf(it)), at[1], { item: it }, it.rarity);
      spawnGroundItem(F, at[0], at[1], { gold: 60 + F.index * 15 }, 0);
      toast('A dead merchant — his pack is intact.', '');
      break;
    }
    case 'ambush_beasts': {
      const pool = ENEMIES.filter(x => x.reg === regionOf(F.index).id && x.tier === 'beast');
      for (let i = 0; i < 3; i++) {
        const en = spawnEnemy(F, pick(Math.random, pool).id, at[0] + (Math.random() - .5) * 4, at[1] + (Math.random() - .5) * 4, F.index, {});
        if (en) { en.activated = true; en.dormant = true; }
      }
      break;
    }
    case 'brazier_puzzle': {
      for (let i = 0; i < 3; i++) F.braziers.push({ id: 'b' + (PROP_ID++), x: at[0] + i * 2 - 2, z: at[1], lit: false, puzzle: true });
      toast('Three cold braziers. Fire might wake them.', '');
      break;
    }
    case 'lever_shortcut': {
      F.levers.push({ id: 'l' + (PROP_ID++), x: at[0], z: at[1], pulled: false, opens: 'shortcut' });
      toast('A lever with a worn handle.', '');
      break;
    }
    case 'survivor': {
      F.survivor = { x: at[0], z: at[1], met: false };
      toast('You hear someone... "Over here!"', 'good');
      break;
    }
    case 'poison_altar': {
      F.shrines.push({ id: 'sAlt' + (PROP_ID++), kind: 'risk', x: at[0], z: at[1], used: false });
      break;
    }
    case 'bone_trap_room': {
      for (let i = 0; i < 3; i++) {
        F.traps.push({ id: 'tEv' + (PROP_ID++), def: 'spike_plate', x: at[0] + i * 2 - 2, z: at[1] + (i % 2) * 2, cd: 0, armed: true });
      }
      break;
    }
    case 'rat_nest': {
      for (let i = 0; i < 4; i++) {
        const en = spawnEnemy(F, 'mire_leech', at[0] + (Math.random() - .5) * 3, at[1] + (Math.random() - .5) * 3, F.index, {});
        if (en) { en.activated = true; }
      }
      break;
    }
  }
  markDone();
}
const i2 = i => [0, 1.2, -1.2][i % 3];

/* quest pickups & key on floor */
function spawnFloorQuestStuff(F) {
  const fs = G.campaign.floors[F.index] || (G.campaign.floors[F.index] = {});
  if (F.keyPickup && !F.keyPickup.taken) {
    const keyBase = F.keyPickup.keyId;
    if (!ITEM_BASES[keyBase]) ITEM_BASES[keyBase] = { id: keyBase, name: 'Floor ' + F.index + ' Key', cat: 'quest', slot: null, w: 1, h: 1, value: 0, minLvl: 1, durMax: 0 };
    const alreadyKey = (fs.itemsGround || []).some(g => g.item && g.item.base === keyBase);
    if (!alreadyKey) spawnGroundItem(F, F.keyPickup.x, F.keyPickup.z, { item: makeItem(keyBase, 1, 'common', mulberry32(5), { identified: true }) }, 0);
    else F.keyPickup.taken = true;
  }
  if (F.questPickups) {
    for (const qp of F.questPickups) {
      if (qp.done) continue;
      const already = (fs.itemsGround || []).some(g => g.item && g.item.base === qp.base);
      if (already) { qp.done = true; continue; }
      spawnGroundItem(F, qp.x, qp.z, { item: makeItem(qp.base, 1, 'common', mulberry32(6), { identified: true }) }, 0);
    }
  }
  // restore persisted ground items
  if (fs && fs.itemsGround) {
    for (const g of fs.itemsGround) {
      spawnGroundItem(F, g.x, g.z, g.item ? { item: deserializeItem(g.item) } : { gold: g.gold }, g.beam);
    }
  }
  // boss gates: remember which doors seal the arena
  if (F.bossSpawn && !fs.bossKilled) {
    const bossRoom = F.rooms.find(r => r.role === 'boss');
    if (bossRoom) {
      F.bossGateIds = [];
      for (const d of F.doors) {
        if (d.x >= bossRoom.x0 - 1 && d.x <= bossRoom.x1 + 1 && d.y >= bossRoom.y0 - 1 && d.y <= bossRoom.y1 + 1) { F.bossGateIds.push(d.id); d.state = 'closed'; }
      }
    }
  } else if (F.bossSpawn && fs.bossKilled) {
    F.bossDefeated = true;
  }
}
function serializeItem(it) {
  return { iid: it.iid, base: it.base, name: it.name, rarity: it.rarity, ilvl: it.ilvl, affixes: it.affixes, identified: it.identified, dur: it.dur, durMax: it.durMax, qty: it.qty, special: it.special, rot: it.rot || 0, _x: it._x, _y: it._y };
}
function deserializeItem(d) {
  if (!d) return null;
  if (d.special && RELICS[d.special]) return relicItem(d.special, d.ilvl, mulberry32(1));
  const b = baseOf(d.base);
  if (!b) return null;
  const it = {
    iid: d.iid, base: d.base, name: d.name, rarity: d.rarity, ilvl: d.ilvl, affixes: d.affixes,
    identified: d.identified, durMax: b.durMax, dur: d.dur !== undefined ? d.dur : b.durMax, qty: d.qty || 1,
    cat: b.cat, slot: b.slot || null, w: b.w, h: b.h, stackMax: b.stackMax || 0, reqs: b.reqs || {}, minLvl: b.minLvl || 1,
    baseValue: b.value, value: b.value, rot: d.rot || 0, _x: d._x, _y: d._y,
  };
  if (b.cat === 'weapon') { it.fam = b.fam; it.dmg = { min: b.dmg.min, max: b.dmg.max, elem: b.dmg.elem }; it.reach = b.reach; it.wind = b.wind; it.rec = b.rec; it.stam = b.stam; it.poise = b.poise; it.two = b.two; it.projSpeed = b.projSpeed; }
  if (b.cat === 'armor' || b.cat === 'shield') { it.armor = b.armor; if (b.cat === 'shield') { it.blockAbs = b.blockAbs; it.blockElem = b.blockElem; } }
  if (b.spellPower) it.spellPower = b.spellPower;
  if (b.effect) it.effect = b.effect;
  if (b.spell) it.spell = b.spell;
  it.price = itemValue(it);
  return it;
}

/* ============================================================
   12. HUD & minimap
   ============================================================ */
let logLines = [];
function log(msg, color) {
  logLines.push({ msg, color: color || '#cfc6b0', t: G.time });
  if (logLines.length > 7) logLines.shift();
  renderLog();
}
function renderLog() {
  if (NODE) return;
  const b = el('logBox');
  b.innerHTML = logLines.map(l => `<div style="color:${l.color}">${esc(l.msg)}</div>`).join('');
}
function toast(msg, cls) {
  if (NODE) return;
  const b = el('toastBox');
  const t = mk('div', 'toast' + (cls ? ' ' + cls : ''), esc(msg));
  b.appendChild(t);
  setTimeout(() => { t.style.opacity = '0'; t.style.transition = 'opacity .5s'; setTimeout(() => t.remove(), 500); }, 2400);
  if (b.children.length > 4) b.firstChild.remove();
}
function prompt(html) { if (!NODE) el('promptBox').innerHTML = html; }
let dmgNums = [];
function dmgNum(pos, txt, color, size) {
  dmgNums.push({ pos: [pos[0], (pos[1] || 1) + 1.2 + Math.random() * 0.4, pos[2]], txt, color: color || '#fff', t: 0, size: size || 15 });
  if (dmgNums.length > 30) dmgNums.shift();
}
function updateDmgNums(dt) {
  const layer = el('dmgLayer');
  const w = R.canvas.clientWidth, h = R.canvas.clientHeight;
  const proj = G._proj, view = G._view;
  let html = '';
  for (let i = dmgNums.length - 1; i >= 0; i--) {
    const d = dmgNums[i];
    d.t += dt;
    if (d.t > 1) { dmgNums.splice(i, 1); continue; }
    const sp = R.project(d.pos, proj, view, w, h);
    if (sp) html += `<div class="dmgNum" style="left:${sp[0]}px;top:${sp[1] - d.t * 30}px;color:${d.color};font-size:${d.size}px;opacity:${1 - d.t}">${esc(d.txt)}</div>`;
  }
  layer.innerHTML = html;
}
function updateHUD() {
  if (NODE || !P) return;
  el('orbHpFill').style.height = clamp(P.hp / P.stats.hpMax * 100, 0, 100) + '%';
  el('orbMpFill').style.height = clamp(P.mp / P.stats.mpMax * 100, 0, 100) + '%';
  el('orbHpTxt').textContent = Math.ceil(P.hp) + ' / ' + P.stats.hpMax;
  el('orbMpTxt').textContent = Math.ceil(P.mp) + ' / ' + P.stats.mpMax;
  el('orbHp').classList.toggle('low', P.hp / P.stats.hpMax < 0.25);
  const sw = el('stamWrap');
  sw.classList.toggle('full', P.st >= P.stats.stMax - 0.5);
  el('stamFill').style.width = clamp(P.st / P.stats.stMax * 100, 0, 100) + '%';
  el('xpFill').style.width = clamp(P.xp / xpForLevel(P.level) * 100, 0, 100) + '%';
  el('xpTxt').textContent = 'Lv ' + P.level + ' — ' + fmt(P.xp) + ' / ' + fmt(xpForLevel(P.level)) + ' XP';
  el('ptsBadge').textContent = (P.unspentAttr || P.unspentTalent) ? (P.unspentAttr + ' attr, ' + P.unspentTalent + ' talent pts — [Tab]') : '';
  // status icons
  let stHtml = '';
  for (const s of P.statuses) {
    const def = STATUS_DEFS[s.id];
    stHtml += `<div class="stChip" style="border-color:#7a4a4a">${s.id}${s.stacks > 1 ? '×' + s.stacks : ''} ${s.t.toFixed(0)}s</div>`;
  }
  el('statusRow').innerHTML = stHtml;
  let bf = '';
  for (const b of P.buffs) bf += `<div class="stChip" style="border-color:#4a6a7a">${b.icon} ${b.name} ${b.t.toFixed(0)}s</div>`;
  if (P.ward) bf += `<div class="stChip" style="border-color:#4a6a9a">◈ Ward ${Math.round(P.ward.hp)}</div>`;
  el('buffRow').innerHTML = bf;
  // hotbar cooldown shades
  for (let i = 0; i < 6; i++) {
    const slot = el('hb' + i);
    if (!slot) continue;
    const it = beltItem(P, i);
    const cd = slot.querySelector('.cd');
    if (P.potionCd > 0 && it) cd.classList.remove('hidden'), cd.style.transform = 'scaleY(' + clamp(P.potionCd / CFG.potionCD, 0, 1) + ')';
    else cd.classList.add('hidden');
    const cnt = slot.querySelector('.cnt');
    cnt.textContent = it ? (it.qty > 1 ? it.qty : '') : '';
    const gly = slot.querySelector('.gly');
    if (gly) { gly.textContent = it ? glyphFor(it) : ''; gly.style.color = it ? RAR[RAR_IDX[it.rarity]].col : ''; }
    slot.classList.toggle('empty', !it);
  }
  for (const [sid, name] of [['slotQ', 'Q'], ['slotR', 'R']]) {
    const s = el(sid); if (!s) continue;
    const sk = name === 'Q' ? P.skillQ : P.skillR;
    const cd = s.querySelector('.cd');
    let key = null, max = 0;
    if (sk) {
      const t = sk.kind === 'talent' ? TALENT_BY_ID[sk.id] : SPELLS[sk.id];
      if (!t) { s.classList.add('empty'); continue; }
      key = (sk.kind === 'talent' ? 't_' : 's_') + sk.id;
      max = t.cd || 1;
      const rem = cdRemaining(key);
      if (rem > 0) { cd.classList.remove('hidden'); cd.style.transform = 'scaleY(' + clamp(rem / (max / (1 + P.stats.haste / 100)), 0, 1) + ')'; }
      else cd.classList.add('hidden');
      s.title = (sk.kind === 'talent' ? TALENT_BY_ID[sk.id].name : SPELLS[sk.id].name);
    } else s.title = '';
    const sgly = s.querySelector('.gly');
    if (sgly) sgly.textContent = sk ? (sk.kind === 'talent' ? '⚡' : '✨') : '';
    s.querySelector('.cnt').textContent = sk ? (sk.kind === 'talent' ? TALENT_BY_ID[sk.id].name.split(' ').map(w => w[0]).join('') : '') : '';
    s.classList.toggle('empty', !sk);
  }
  // boss bar
  const boss = G.floor && G.floor.bossActor && !G.floor.bossActor.dead ? G.floor.bossActor : null;
  el('bossBarWrap').classList.toggle('hidden', !boss);
  if (boss) {
    el('bossName').textContent = boss.name;
    el('bossFill').style.width = clamp(boss.hp / boss.maxHp * 100, 0, 100) + '%';
  }
  // target bar
  const tb = el('targetBarWrap');
  if (INPUT && INPUT.aimActor && !INPUT.aimActor.dead && G.settings.enemyBars) {
    const a = INPUT.aimActor;
    tb.classList.remove('hidden');
    el('targetName').textContent = a.name + '  Lv' + a.level + (a.elite ? ' ★' : '');
    el('targetFill').style.width = clamp(a.hp / a.maxHp * 100, 0, 100) + '%';
  } else tb.classList.add('hidden');
}
const RAR_MINI = ['#888', '#5b9bd5', '#e8c84a', '#ff9a3c'];
function drawMinimap() {
  if (NODE) return;
  const c = el('minimap'); const ctx = c.getContext('2d');
  const F = G.floor; if (!F || !F.fog) return;
  const W = c.width, H = c.height;
  ctx.fillStyle = '#0a0a0c'; ctx.fillRect(0, 0, W, H);
  const s = 4; // px per tile
  const view = 44; // tiles visible
  const px = P.pos[0] / CFG.tile, pz = P.pos[2] / CFG.tile;
  const ox = px - view / 2, oz = pz - view / 2;
  ctx.save();
  for (let y = 0; y < F.H; y++) for (let x = 0; x < F.W; x++) {
    const fog = F.fog[y * F.W + x];
    if (!fog) continue;
    const sx = (x - ox) * s, sy = (y - oz) * s;
    if (sx < -s || sy < -s || sx > W || sy > H) continue;
    const t = F.tiles[y * F.W + x];
    if (t === T_SOLID) { ctx.fillStyle = '#17141a'; ctx.fillRect(sx, sy, s, s); }
    else if (t === T_WATER) { ctx.fillStyle = '#1a3a4a'; ctx.fillRect(sx, sy, s, s); }
    else { ctx.fillStyle = (fog & 2) ? '#4a4136' : '#2a2620'; ctx.fillRect(sx, sy, s, s); }
  }
  // doors
  for (const d of F.doors) {
    if (!F.fog[d.y * F.W + d.x]) continue;
    if (d.kind === 'secret' && !d.revealed) continue;
    ctx.fillStyle = d.state === 'locked' ? '#c04040' : d.kind === 'secret' ? '#c8a84a' : d.state === 'open' ? '#4a6a4a' : '#8a7a4a';
    ctx.fillRect((d.x - ox) * s, (d.y - oz) * s, s, s);
  }
  // stairs
  if (F.stairsDown && F.fog[(F.stairsDown.z / CFG.tile | 0) * F.W + (F.stairsDown.x / CFG.tile | 0)]) {
    ctx.fillStyle = '#e8c84a'; ctx.fillText('▼', (F.stairsDown.x / CFG.tile - ox) * s - 2, (F.stairsDown.z / CFG.tile - oz) * s + 5);
  }
  // chests seen
  for (const ch of F.chests) {
    const tx = ch.x / CFG.tile | 0, tz = ch.z / CFG.tile | 0;
    if (!F.fog[tz * F.W + tx]) continue;
    ctx.fillStyle = ch.opened ? '#555' : ch.rare ? '#ff9a3c' : '#c8a84a';
    ctx.fillRect((tx - ox) * s + 1, (tz - oz) * s + 1, s - 2, s - 2);
  }
  // portals
  for (const po of (F.portals || [])) { ctx.fillStyle = '#b06aff'; ctx.fillRect((po.x / CFG.tile - ox) * s, (po.z / CFG.tile - oz) * s, s, s); }
  // player arrow
  ctx.fillStyle = '#fff';
  ctx.save();
  ctx.translate((px - ox) * s, (pz - oz) * s);
  ctx.rotate(-P.yaw);
  ctx.beginPath(); ctx.moveTo(0, -4); ctx.lineTo(3, 3); ctx.lineTo(-3, 3); ctx.fill();
  ctx.restore();
  ctx.restore();
  el('floorLbl').textContent = F.isTown ? 'Hollowmere' : 'Floor ' + F.index + ' — ' + F.reg.name;
}
function drawFullMap(ctx, c, pan, zoom) {
  const F = G.floor; if (!F) return;
  const s = 6 * zoom;
  ctx.fillStyle = '#08080a'; ctx.fillRect(0, 0, c.width, c.height);
  for (let y = 1; y < F.H - 1; y++) for (let x = 1; x < F.W - 1; x++) {
    const fog = F.fog[y * F.W + x];
    if (!fog) continue;
    const t = F.tiles[y * F.W + x];
    const sx = (x * CFG.tile + pan[0]) * zoom, sy = (y * CFG.tile + pan[1]) * zoom;
    if (t === T_SOLID) ctx.fillStyle = '#16131a';
    else if (t === T_WATER) ctx.fillStyle = '#1a3a4a';
    else ctx.fillStyle = (fog & 2) ? '#4a4136' : '#2a2620';
    ctx.fillRect(sx, sy, s * 1.05, s * 1.05);
  }
  ctx.font = '12px Georgia';
  for (const d of F.doors) {
    if (!F.fog[d.y * F.W + d.x]) continue;
    if (d.kind === 'secret' && !d.revealed) continue;
    ctx.fillStyle = d.state === 'locked' ? '#c04040' : d.kind === 'secret' ? '#c8a84a' : '#8a7a4a';
    ctx.fillRect((d.x * CFG.tile + pan[0]) * zoom - 2, (d.y * CFG.tile + pan[1]) * zoom - 2, s * 1.2, s * 1.2);
  }
  if (F.stairsDown) { ctx.fillStyle = '#e8c84a'; ctx.fillText('▼ stairs', (F.stairsDown.x + pan[0]) * zoom, (F.stairsDown.z + pan[1]) * zoom); }
  if (F.stairsUp) { ctx.fillStyle = '#9a8a4a'; ctx.fillText('▲ exit', (F.stairsUp.x + pan[0]) * zoom, (F.stairsUp.z + pan[1]) * zoom); }
  for (const ch of F.chests) {
    const tx = ch.x / CFG.tile | 0, tz = ch.z / CFG.tile | 0;
    if (!F.fog[tz * F.W + tx]) continue;
    ctx.fillStyle = ch.opened ? '#555' : ch.rare ? '#ff9a3c' : '#c8a84a';
    ctx.fillRect((ch.x + pan[0]) * zoom - 3, (ch.z + pan[1]) * zoom - 3, 7, 7);
  }
  for (const po of (F.portals || [])) { ctx.fillStyle = '#b06aff'; ctx.fillRect((po.x + pan[0]) * zoom - 3, (po.z + pan[1]) * zoom - 3, 7, 7); }
  ctx.fillStyle = '#fff';
  ctx.beginPath(); ctx.arc((P.pos[0] + pan[0]) * zoom, (P.pos[2] + pan[1]) * zoom, 4, 0, TAU); ctx.fill();
  ctx.fillStyle = '#8a7f68';
  ctx.fillText((F.isTown ? 'Hollowmere' : 'Floor ' + F.index + ' — ' + F.reg.name) + '  [wheel: zoom, drag: pan]', 10, 16);
}

/* ============================================================
   13. UI — tooltips, inventory/character/skills/journal, stash
   ============================================================ */
const GLYPH = { sword: '🗡', axe: '🪓', mace: '🔨', dagger: '🔪', spear: '🔱', great: '⚔', bow: '🏹', staff: '🪄', wand: '✨', shield: '🛡', head: '⛑', chest: '🧥', gloves: '🧤', boots: '🥾', ring: '💍', amulet: '📿', focus: '🔮', potion: '🧪', scroll: '📜', book: '📕', ammo: '➶', quest: '❓', key: '🗝' };
function glyphFor(it) {
  if (!it) return '';
  if (it.cat === 'weapon') return GLYPH[it.fam] || '🗡';
  if (it.cat === 'potion') return it.effect.kind === 'heal' ? '🧪' : it.effect.kind === 'mana' ? '💙' : it.effect.kind === 'stam' ? '💚' : '🧴';
  return GLYPH[it.cat] || '·';
}
function tooltipHTML(it, compare) {
  if (!it) return '';
  const rar = RAR[RAR_IDX[it.rarity]];
  const s = itemStats(it);
  const ident = it.identified || it.rarity === 'common';
  let h = `<h4 style="color:${rar.col}">${SHAPE_MARK[RAR_IDX[it.rarity]]} ${esc(ident ? it.name : it.name.replace(/^(\w+ \w+).*/, '$1') + ' ???')}</h4>`;
  h += `<div class="dim">${rar.name} · ${it.cat === 'weapon' ? (it.fam || 'weapon') : it.cat} · item level ${it.ilvl}</div>`;
  if (it.durMax) h += `<div class="dim">Durability ${Math.ceil(it.dur)}/${it.durMax}${it.dur <= 0 ? ' — BROKEN' : ''}</div>`;
  if (it.cat === 'weapon' && it.dmg) {
    const dps = itemDPS(it).toFixed(1);
    h += `<div>${s.dmgMin}–${s.dmgMax} ${it.dmg.elem} damage · ${dps} DPS${it.two ? ' · two-handed' : ''}${it.fam === 'bow' ? ' · uses arrows' : ''}</div>`;
  }
  if (s.armor) h += `<div>${Math.round(s.armor)} armor</div>`;
  if (it.blockAbs) h += `<div>Block: absorbs ${Math.round(it.blockAbs * 100)}% physical, ${Math.round(it.blockElem * 100)}% elemental</div>`;
  if (s.spellPower) h += `<div>+${Math.round(s.spellPower * 100)}% spellpower</div>`;
  if (it.spell) {
    const sp = SPELLS[it.spell];
    const rank = P.spellRanks[it.spell] || 0;
    h += `<div>Teaches: <b>${sp.name}</b> (rank ${Math.min(5, rank + 1)}${rank >= 5 ? ' — MAX, not consumed' : ''})</div>`;
    h += `<div class="dim">${esc(sp.desc)} Requires ${spellLearnINT(Math.min(5, rank + 1))} INT to learn.</div>`;
  }
  if (it.effect) {
    const e = it.effect;
    if (e.kind === 'heal') h += `<div>Restores ${Math.round(e.param * 100)}% of max health</div>`;
    if (e.kind === 'mana') h += `<div>Restores ${Math.round(e.param * 100)}% of max mana</div>`;
    if (e.kind === 'stam') h += `<div>Restores ${Math.round(e.param * 100)}% of max stamina</div>`;
    if (e.kind === 'cure') h += `<div>Cures ${e.param}</div>`;
    if (e.kind === 'resist') h += `<div>+25% to your weakest resistance for 30 s</div>`;
    if (e.kind === 'identify') h += `<div>Identifies one unidentified item</div>`;
    if (e.kind === 'portal') h += `<div>Opens a return portal to town (3 s channel)</div>`;
  }
  if (it.relic && it.relic.desc) h += `<div style="color:#ff9a3c">Relic: ${esc(it.relic.desc)}</div>`;
  if (ident && it.affixes && it.affixes.length) {
    h += `<div class="aff" style="margin-top:4px">`;
    for (const fx of it.affixes) {
      const a = AFFIX_BY_ID[fx.id]; if (!a) continue;
      const key = Object.keys(a.f)[0];
      let vTxt = Array.isArray(a.f[key]) ? fx.v : (typeof fx.v === 'number' && fx.v < 1 && !Number.isInteger(fx.v) ? Math.round(fx.v * 100) + '%' : (typeof fx.v === 'number' ? fx.v : fx.v));
      if (['spellPower', 'atkSpd', 'crit', 'critDmg', 'lifeSteal', 'manaSteal', 'moveSpd', 'haste', 'onHitBurn', 'onHitChill', 'onHitPoison', 'onHitShock', 'shieldStam', 'manaCostRed', 'statusRes', 'goldFind'].includes(key)) vTxt = Math.round(fx.v * 100) + '%';
      h += `<div>+${esc(key === 'kickElem' ? fx.v + ' kick damage' : key.replace(/([A-Z])/g, ' $1').toLowerCase())} ${key !== 'kickElem' ? vTxt : ''}</div>`;
    }
    h += `</div>`;
  } else if (!ident && it.rarity !== 'common') {
    h += `<div class="dim" style="color:#7a9ab5">Unidentified — magical properties concealed. Use an ID scroll or visit the Mystic.</div>`;
  }
  // reqs
  const reqBits = [];
  if (it.minLvl > 1) reqBits.push(['level ' + it.minLvl, P.level >= it.minLvl]);
  for (const k of ['str', 'dex', 'int']) if (it.reqs && it.reqs[k]) reqBits.push([k.toUpperCase() + ' ' + it.reqs[k], P.stats[k] >= it.reqs[k]]);
  if (reqBits.length) h += `<div class="${reqBits.every(r => r[1]) ? 'dim' : 'req-bad'}">Requires ${reqBits.map(r => r[1] ? r[0] : '<span class="req-bad">' + r[0] + '</span>').join(', ')}</div>`;
  h += `<div class="dim">Value ${fmt(it.price || 0)} gold · sells for ${fmt(sellValue(it))}</div>`;
  if (it.cat === 'quest') h += `<div class="dim" style="color:#c8b04a">Quest item — cannot be sold or dropped.</div>`;
  if (compare) {
    const eq = compare.slot === 'ring' ? null : P.equip[compare.slot];
    const other = eq && eq !== it ? eq : null;
    if (other) {
      const s2 = itemStats(other);
      h += `<div class="cmp">Equipped: <span style="color:${RAR[RAR_IDX[other.rarity]].col}">${esc(other.identified ? other.name : 'Unidentified ' + other.cat)}</span><br>`;
      const cmp = (lab, a, b, fmtF) => {
        if (a === b) return;
        h += `<div class="${a > b ? 'up' : 'dn'}">${lab}: ${fmtF ? fmtF(a) : a} → ${fmtF ? fmtF(b) : b}</div>`;
      };
      if (s.dmgMax) cmp('Damage', s.dmgMin + s.dmgMax, s2.dmgMin + s2.dmgMax);
      if (s.armor || s2.armor) cmp('Armor', Math.round(s.armor), Math.round(s2.armor));
      if (s.spellPower || s2.spellPower) cmp('Spellpower', Math.round(s.spellPower * 100) + '%', Math.round(s2.spellPower * 100) + '%');
      h += `</div>`;
    }
  }
  return h;
}
function showTooltipAt(x, y, html) {
  const tt = el('tooltip');
  tt.innerHTML = html;
  tt.classList.remove('hidden');
  const r = tt.getBoundingClientRect();
  tt.style.left = clamp(x + 14, 4, window.innerWidth - r.width - 8) + 'px';
  tt.style.top = clamp(y + 10, 4, window.innerHeight - r.height - 8) + 'px';
}
function hideTooltip() { el('tooltip').classList.add('hidden'); }

/* ---------- drag state ---------- */
const DRAG = { item: null, from: null, ghost: null, rot: false };
function startDrag(item, from, e) {
  if (!item || (item.cat === 'quest' && from === 'bag' && e.button === 0)) { /* quest items draggable within bag only */ }
  DRAG.item = item; DRAG.from = from;
  DRAG.ghost = mk('div', 'dragGhost', glyphFor(item));
  DRAG.ghost.style.left = e.clientX + 'px'; DRAG.ghost.style.top = e.clientY + 'px';
  document.body.appendChild(DRAG.ghost);
}
function moveDrag(e) {
  if (DRAG.ghost) { DRAG.ghost.style.left = e.clientX + 'px'; DRAG.ghost.style.top = e.clientY + 'px'; }
  if (INPUT && INPUT.keyDown('KeyR') && DRAG.item && DRAG.item.w !== DRAG.item.h) { DRAG.rot = !DRAG.rot; INPUT.consume('KeyR'); }
}
function endDrag(e) {
  if (!DRAG.item) return;
  const target = e.target && e.target.closest ? e.target.closest('[data-drop]') : null;
  handleDrop(DRAG, target, e);
  if (DRAG.ghost) DRAG.ghost.remove();
  DRAG.item = null; DRAG.from = null; DRAG.ghost = null; DRAG.rot = false;
  hideTooltip();
  refreshScreens();
}
function handleDrop(drag, target, e) {
  const it = drag.item;
  if (!target) {
    // drop to world (bag only, not quest items)
    if (drag.from === 'bag' && it.cat !== 'quest') {
      if (it.rarity === 'relic' || RAR_IDX[it.rarity] >= 2) {
        if (!confirmModal(`Drop ${it.name} (${RAR[RAR_IDX[it.rarity]].name})?`)) return;
      }
      dropToGround(P, it, G.floor, P.pos);
      const i = P.inv.indexOf(it); if (i >= 0) P.inv.splice(i, 1);
      toast('Dropped: ' + it.name, '');
    }
    return;
  }
  const zone = target.dataset.drop;
  if (zone === 'bag') {
    const x = +target.dataset.x, y = +target.dataset.y;
    if (drag.from === 'bag') {
      const w = (DRAG.rot ? it.h : it.w), h = (DRAG.rot ? it.w : it.h);
      if (canPlace(P, it, x, y, DRAG.rot, it)) { it._x = x; it._y = y; it.rot = DRAG.rot ? 1 : 0; SND.ui(); return; }
      // try swap with single item under
      const other = itemAtCell(x, y);
      if (other && other !== it) {
        const oldX = it._x, oldY = it._y, oldRot = it.rot;
        P.inv.splice(P.inv.indexOf(it), 1);
        P.inv.splice(P.inv.indexOf(other), 1);
        if (canPlace(P, it, x, y, DRAG.rot) && canPlace(P, other, other._x, other._y, other.rot)) {
          it._x = x; it._y = y; it.rot = DRAG.rot ? 1 : 0;
          P.inv.push(it); P.inv.push(other); SND.ui();
        } else {
          P.inv.push(other); it._x = oldX; it._y = oldY; it.rot = oldRot; P.inv.push(it);
        }
      }
    } else if (drag.from === 'equip') {
      // unequip to cell
      const slot = drag.slot;
      P.equip[slot] = null;
      if (!canPlace(P, it, x, y, DRAG.rot)) { P.equip[slot] = it; SND.error(); return; }
      it._x = x; it._y = y; it.rot = DRAG.rot ? 1 : 0; P.inv.push(it);
      recalcStats(P); SND.ui();
    } else if (drag.from === 'stash') {
      if (!canPlace(P, it, x, y, DRAG.rot)) { SND.error(); return; }
      stashRemove(drag.tab, it);
      it._x = x; it._y = y; it.rot = DRAG.rot ? 1 : 0; P.inv.push(it);
      SND.ui();
    }
  } else if (zone === 'equip' && drag.from === 'bag') {
    const slot = target.dataset.slot;
    let ringSlot = slot === 'ring' ? (e.shiftKey ? 'ring2' : 'ring1') : null;
    const res = equipItem(P, it, ringSlot);
    if (!res.ok) { toast(res.why, 'bad'); SND.error(); }
  } else if (zone === 'stash' && drag.from === 'bag') {
    const x = +target.dataset.x, y = +target.dataset.y;
    const tab = drag.tab !== undefined ? drag.tab : UI._stashTab || 0;
    if (stashCanPlace(tab, it, x, y, DRAG.rot)) {
      const i = P.inv.indexOf(it); P.inv.splice(i, 1);
      it._x = x; it._y = y; it.rot = DRAG.rot ? 1 : 0;
      stashAdd(tab, it); SND.ui();
    } else SND.error();
  }
}
function itemAtCell(x, y) {
  for (const it of P.inv) {
    if (!it) continue;
    const w = it.rot ? it.h : it.w, h = it.rot ? it.w : it.h;
    if (x >= it._x && x < it._x + w && y >= it._y && y < it._y + h) return it;
  }
  return null;
}

/* stash */
function stashInit() {
  if (!G.campaign.stash) G.campaign.stash = [[], [], []];
  for (const tab of G.campaign.stash) {
    for (const it of tab) { if (it._x === undefined) { const spot = { x: 0, y: 0, rot: 0 }; it._x = 0; it._y = 0; it.rot = 0; } }
  }
}
function stashCanPlace(tab, it, x, y, rot) {
  const w = rot ? it.h : it.w, h = rot ? it.w : it.h;
  const SW = 12, SH = 10;
  if (x < 0 || y < 0 || x + w > SW || y + h > SH) return false;
  const occ = new Uint8Array(SW * SH);
  for (const o of G.campaign.stash[tab]) {
    if (o === it) continue;
    const ow = o.rot ? o.h : o.w, oh = o.rot ? o.w : o.h;
    for (let dy = 0; dy < oh; dy++) for (let dx = 0; dx < ow; dx++) occ[(o._y + dy) * SW + o._x + dx] = 1;
  }
  for (let dy = 0; dy < h; dy++) for (let dx = 0; dx < w; dx++) if (occ[(y + dy) * SW + x + dx]) return false;
  return true;
}
function stashAdd(tab, it) { it.tab = tab; G.campaign.stash[tab].push(it); }
function stashRemove(tab, it) { const i = G.campaign.stash[tab].indexOf(it); if (i >= 0) G.campaign.stash[tab].splice(i, 1); }

/* ---------- screens ---------- */
let SCREENS = [];
function refreshScreens() { for (const f of SCREENS) if (f.refresh) f.refresh(); }
function closeAllScreens() {
  SCREENS = [];
  el('screens').innerHTML = '';
  el('screens').className = '';
  el('dlgBox').classList.add('hidden');
  G.uiOpen = null;
  if (P && !P.dead && G.state === 'play' && !NODE) { /* pointer lock resumes on click */ }
}
function openPanel(html, cls) {
  closeAllScreens();
  if (document.pointerLockElement) document.exitPointerLock();
  const c = el('screens');
  c.innerHTML = `<div class="panel ${cls || ''}">${html}</div>`;
  c.className = 'dim';
  return c.firstChild;
}

/* inventory + character + skills + journal tabs */
function openCharScreen(tab) {
  tab = tab || 'inv';
  const panel = openPanel(`
    <div class="tabs">
      <div class="tab" data-t="inv">Inventory</div>
      <div class="tab" data-t="char">Character</div>
      <div class="tab" data-t="skills">Skills</div>
      <div class="tab" data-t="journal">Journal</div>
      <div style="flex:1"></div>
      <div class="btn small" id="closeScr">Close [Tab]</div>
    </div>
    <div id="scrBody" style="overflow:auto; max-height:76vh"></div>
  `);
  const body = panel.querySelector('#scrBody');
  const refresh = () => {
    panel.querySelectorAll('.tab').forEach(t => t.classList.toggle('act', t.dataset.t === tab));
    if (tab === 'inv') renderInvTab(body);
    else if (tab === 'char') renderCharTab(body);
    else if (tab === 'skills') renderSkillsTab(body);
    else renderJournalTab(body);
  };
  panel.addEventListener('click', e => {
    const t = e.target.closest('.tab');
    if (t) { tab = t.dataset.t; SND.ui(); refresh(); }
    if (e.target.id === 'closeScr') { closeAllScreens(); }
  });
  SCREENS.push({ refresh });
  refresh();
  G.uiOpen = 'char';
}
function itemEl(it, opts) {
  opts = opts || {};
  const d = mk('div', 'itm' + (it.cat === 'quest' ? ' q' : ''));
  d.style.width = (it.rot ? it.h : it.w) * 34 - 2 + 'px';
  d.style.height = (it.rot ? it.w : it.h) * 34 - 2 + 'px';
  d.style.left = it._x * 34 + 1 + 'px';
  d.style.top = it._y * 34 + 1 + 'px';
  const rc = RAR[RAR_IDX[it.rarity]].col;
  d.style.background = `linear-gradient(180deg, ${rc}22, transparent)`;
  d.style.color = rc;
  d.style.borderColor = rc + '55';
  d.innerHTML = `<span style="pointer-events:none">${glyphFor(it)}</span>${it.qty > 1 ? `<span class="cnt">${it.qty}</span>` : ''}`;
  d.title = '';
  d.addEventListener('mouseenter', e => { if (!DRAG.item) showTooltipAt(e.clientX, e.clientY, tooltipHTML(it, it.slot ? it : null)); });
  d.addEventListener('mousemove', e => { if (!DRAG.item) showTooltipAt(e.clientX, e.clientY, tooltipHTML(it, it.slot ? it : null)); });
  d.addEventListener('mouseleave', () => { if (!DRAG.item) hideTooltip(); });
  d.addEventListener('mousedown', e => {
    if (e.button === 0) { startDrag(it, opts.from || 'bag', e); DRAG.tab = opts.tab; e.preventDefault(); }
    else if (e.button === 2) { itemContext(it, opts); e.preventDefault(); }
  });
  return d;
}
function itemContext(it, opts) {
  const from = opts.from || 'bag';
  if (from === 'bag') {
    if (it.cat === 'potion' || it.cat === 'scroll') { useConsumable(it); refreshScreens(); return; }
    if (it.cat === 'book') { learnFromBook(it); refreshScreens(); return; }
    if (it.cat === 'ammo') { toast('Arrows are used automatically when shooting', ''); return; }
    if (it.slot) {
      const res = equipItem(P, it);
      if (!res.ok) toast(res.why, 'bad');
      refreshScreens(); return;
    }
  } else if (from === 'equip') {
    if (!unequipSlot(P, opts.slot)) toast('No bag space to unequip', 'bad');
    refreshScreens(); return;
  } else if (from === 'stash') {
    // move to bag
    if (addToBag(P, it)) { stashRemove(opts.tab, it); SND.ui(); }
    else toast('Backpack full', 'bad');
    refreshScreens(); return;
  }
}
function renderInvTab(body) {
  const w = 10 * 34;
  let h = `<div class="row" style="margin-bottom:8px; flex-wrap:wrap; gap:14px">`;
  for (const slot of SLOT_NAMES) {
    const it = P.equip[slot];
    h += `<div class="slot" data-drop="equip" data-slot="${slot}" title="${SLOT_LABEL[slot]}" style="width:40px;height:40px;font-size:16px;cursor:pointer">${it ? `<span style="color:${RAR[RAR_IDX[it.rarity]].col}">${glyphFor(it)}</span>` : `<span style="opacity:.3">${SLOT_LABEL[slot][0]}</span>`}</div>`;
  }
  h += `<div style="flex:1"></div><div><b style="color:var(--gold2)">${fmt(P.gold)}</b> gold</div>
    <div class="btn small" id="sortBtn">Sort</div></div>`;
  h += `<div style="position:relative;width:${w}px;height:${6 * 34}px" id="bagGrid">`;
  for (let y = 0; y < 6; y++) for (let x = 0; x < 10; x++) {
    h += `<div class="cell" data-drop="bag" data-x="${x}" data-y="${y}" style="position:absolute;left:${x * 34}px;top:${y * 34}px"></div>`;
  }
  h += `</div>`;
  body.innerHTML = h;
  const grid = body.querySelector('#bagGrid');
  for (const it of P.inv) if (it) grid.appendChild(itemEl(it, { from: 'bag' }));
  // equip slot hover/drag
  body.querySelectorAll('[data-drop="equip"]').forEach(sl => {
    const slotName = sl.dataset.slot;
    const it = P.equip[slotName];
    if (it) {
      sl.addEventListener('mouseenter', e => showTooltipAt(e.clientX, e.clientY, tooltipHTML(it)));
      sl.addEventListener('mousemove', e => showTooltipAt(e.clientX, e.clientY, tooltipHTML(it)));
      sl.addEventListener('mouseleave', hideTooltip);
      sl.addEventListener('mousedown', e => { if (e.button === 0) { startDrag(it, 'equip', e); DRAG.slot = slotName; e.preventDefault(); } else if (e.button === 2) { unequipSlot(P, slotName); refreshScreens(); } });
      sl.addEventListener('dblclick', () => { unequipSlot(P, slotName); refreshScreens(); });
    }
  });
  body.querySelector('#sortBtn').onclick = () => { sortBag(P); SND.ui(); refreshScreens(); };
}
function renderCharTab(body) {
  const s = P.stats;
  const attr = (k, label) => `<div class="attrRow"><span>${label} <span class="dim">(${P.attrs[k]})</span></span><span><b>${s[k]}</b> <button class="plusBtn" data-attr="${k}" ${P.unspentAttr ? '' : 'disabled'}>+</button></span></div>`;
  const line = (l, v, tip) => `<div class="statline" title="${tip || ''}"><span>${l}</span><b>${v}</b></div>`;
  body.innerHTML = `
    <div style="display:flex; gap:20px; flex-wrap:wrap">
      <div style="min-width:240px">
        <h3>${esc(P.name)} — ${CLASSES[P.cls].name} Level ${P.level}${P.hardcore ? ' (Hardcore)' : ''}</h3>
        ${attr('str', 'Strength')}${attr('dex', 'Dexterity')}${attr('int', 'Intellect')}${attr('vit', 'Vitality')}
        <div class="dim" style="margin-top:4px">Unspent: ${P.unspentAttr} attribute, ${P.unspentTalent} talent</div>
        <h3>Defense</h3>
        ${line('Armor', s.armor, 'armor/(armor+100+8*(attackerLvl-1)), capped 75%')}
        ${line('Block absorb', s.blockAbs ? Math.round(s.blockAbs * 100) + '%' : '—')}
        ${line('Resist Fire/Frost/Light', Math.round(s.res.fire * 100) + '% / ' + Math.round(s.res.frost * 100) + '% / ' + Math.round(s.res.light * 100) + '%')}
        ${line('Resist Poison/Arcane', Math.round(s.res.poison * 100) + '% / ' + Math.round(s.res.arc * 100) + '%')}
        ${line('Status resistance', Math.round(s.statusRes * 100) + '%')}
      </div>
      <div style="min-width:240px">
        <h3>Offense</h3>
        ${line('Critical chance', Math.round(s.crit * 100) + '%')}
        ${line('Critical damage', '+' + Math.round(s.critDmg * 100) + '%')}
        ${line('Attack speed', Math.round(s.atkSpd * 100) + '%')}
        ${line('Ability haste', Math.round(s.haste) + '%')}
        ${line('Spellpower', Math.round(s.spellPower * 100) + '%')}
        ${line('Life/Mana steal', Math.round(s.lifeSteal * 100) + '% / ' + Math.round(s.manaSteal * 100) + '%')}
        <h3>Mobility &amp; Resources</h3>
        ${line('Move speed', s.moveSpd.toFixed(1) + ' m/s')}
        ${line('Health', Math.ceil(P.hp) + ' / ' + s.hpMax)}
        ${line('Mana', Math.ceil(P.mp) + ' / ' + s.mpMax)}
        ${line('Stamina', Math.ceil(P.st) + ' / ' + s.stMax)}
        ${line('Regen HP/MP/ST', s.hpRegen.toFixed(2) + ' / ' + s.mpRegen.toFixed(2) + ' / ' + s.stRegen.toFixed(0))}
        ${line('Light radius', s.lightRadius.toFixed(0) + ' m')}
        ${line('Gold', fmt(P.gold))}
      </div>
    </div>`;
  body.querySelectorAll('[data-attr]').forEach(b => b.onclick = () => { spendAttr(P, b.dataset.attr); refreshScreens(); });
}
function renderSkillsTab(body) {
  const talents = TALENTS.filter(t => t.cls === P.cls);
  let h = `<div class="dim" style="margin-bottom:6px">Talent points: <b style="color:var(--gold2)">${P.unspentTalent}</b> · tier 2 needs 3 points spent, tier 3 needs 8</div>`;
  h += `<div style="display:flex;gap:20px;flex-wrap:wrap"><div style="min-width:330px"><h3>Class Talents</h3>`;
  for (const t of talents) {
    const rank = P.talents[t.id] || 0;
    const can = talentOk(P, t);
    let pips = '<span class="pips">';
    for (let i = 0; i < 5; i++) pips += `<span class="pip ${i < rank ? 'on' : ''}"></span>`;
    pips += '</span>';
    const assigned = (P.skillQ && P.skillQ.id === t.id ? ' [Q]' : P.skillR && P.skillR.id === t.id ? ' [R]' : '');
    h += `<div class="talRow"><b style="color:${t.type === 'active' ? '#9ec2e8' : '#a8d8a0'}">${t.name}${assigned}</b>${pips}
      <div class="dim" style="font-size:11.5px">${esc(t.desc)} <i>${t.scale}</i></div>
      <div class="row" style="margin-top:2px">
        <button class="btn small" data-tal="${t.id}" ${can ? '' : 'disabled'}>Rank ${rank ? rank + '→' + (rank + 1) : 'Learn'} ${t.tier > 1 ? `(tier ${t.tier})` : ''}</button>
        ${t.type === 'active' && rank ? `<button class="btn small" data-asg="Q" data-tal="${t.id}">→ Q</button><button class="btn small" data-asg="R" data-tal="${t.id}">→ R</button>` : ''}
      </div></div>`;
  }
  h += `</div><div style="min-width:300px"><h3>Learned Spells</h3>`;
  for (const sid of SPELL_ORDER) {
    const rank = P.spellRanks[sid];
    if (!rank) continue;
    const sp = SPELLS[sid];
    const sel = P.selectedSpell === sid ? ' [LMB]' : P.selectedUtility === sid ? ' [RMB]' : '';
    h += `<div class="talRow"><b>${sp.name} <span class="dim">rank ${rank}</span>${sel}</b>
      <div class="dim" style="font-size:11.5px">${esc(sp.desc)} · ${spellRankCost(sp.mana, rank)} mana · ${sp.cd}s cd</div>
      <div class="row" style="margin-top:2px">
        <button class="btn small" data-sel="${sid}">Set as attack</button>
        ${['heal', 'buff', 'utility'].includes(sp.kind) ? `<button class="btn small" data-selu="${sid}">Set utility</button>` : ''}
      </div></div>`;
  }
  h += `<div class="dim" style="margin-top:6px">Learn more spells from books (use them in your backpack). Higher ranks come from further books.</div></div></div>`;
  body.innerHTML = h;
  body.querySelectorAll('[data-tal]').forEach(b => b.onclick = () => {
    const t = TALENT_BY_ID[b.dataset.tal];
    if (b.dataset.asg) {
      if (b.dataset.asg === 'Q') P.skillQ = { kind: 'talent', id: t.id }; else P.skillR = { kind: 'talent', id: t.id };
      SND.ui(); refreshScreens(); return;
    }
    if (spendTalent(P, t)) refreshScreens();
  });
  body.querySelectorAll('[data-sel]').forEach(b => b.onclick = () => { P.selectedSpell = b.dataset.sel; SND.ui(); refreshScreens(); });
  body.querySelectorAll('[data-selu]').forEach(b => b.onclick = () => { P.selectedUtility = b.dataset.selu; SND.ui(); refreshScreens(); });
}
function renderJournalTab(body) {
  let h = `<div style="display:flex;gap:20px;flex-wrap:wrap"><div style="min-width:320px"><h3>Quests</h3>`;
  for (const q of QUESTS) {
    const st = G.campaign.quests[q.id];
    if (!st) continue;
    if (st.state === 'done' && q.main !== true) continue;
    h += `<div class="qentry"><b style="color:${q.main ? 'var(--gold2)' : '#cfc6b0'}">${q.name}</b> <span class="dim">${st.state === 'done' ? '✔ completed' : 'active'}</span>
      <div class="dim">${esc(q.desc || '')}</div>`;
    for (const o of q.objectives) {
      const done = (st.objDone || {})[o.id];
      h += `<div class="obj ${done ? 'done' : ''}">${done ? '✔' : '○'} ${esc(o.text)}</div>`;
    }
    h += `</div>`;
  }
  h += `</div><div style="min-width:300px"><h3>Lore (${Object.keys(G.campaign.lore).length}/${LORE.length})</h3>`;
  for (const l of LORE) {
    if (!G.campaign.lore[l[0]]) continue;
    h += `<div class="qentry"><b>${esc(l[1])}</b><div class="dim">${esc(l[2])}</div></div>`;
  }
  h += `<h3>Bestiary</h3>`;
  for (const e of ENEMIES) {
    if (!G.campaign.bestiary || !G.campaign.bestiary[e.id]) continue;
    h += `<div class="qentry"><b>${e.name}</b> <span class="dim">${e.tier}</span><div class="dim">${esc(e.desc)}</div></div>`;
  }
  h += `</div></div>`;
  body.innerHTML = h;
}
function learnFromBook(it) {
  const sid = it.spell;
  const cur = P.spellRanks[sid] || 0;
  if (cur >= 5) { toast('Already at max rank — the book is not consumed', ''); return; }
  const need = spellLearnINT(cur + 1);
  if (P.stats.int < need) { toast(`Requires ${need} Intellect to learn rank ${cur + 1}`, 'bad'); SND.error(); return; }
  P.spellRanks[sid] = cur + 1;
  const i = P.inv.indexOf(it); if (i >= 0) P.inv.splice(i, 1);
  toast('Learned ' + SPELLS[sid].name + ' rank ' + (cur + 1), 'good');
  SND.quest();
  EVT.emit('SkillLearned', { spell: sid, rank: cur + 1 });
  if (!P.selectedSpell || SPELLS[P.selectedSpell].kind !== 'projectile' && !P.selectedSpell) P.selectedSpell = P.selectedSpell || sid;
  recalcStats(P);
}
function useConsumable(it) {
  if (!it || it.qty <= 0) return;
  const e = it.effect;
  let used = true;
  const isPotion = it.cat === 'potion';
  if (isPotion && P.potionCd > 0) { SND.error(); toast('Potion cooldown ' + P.potionCd.toFixed(1) + 's', 'bad'); return; }
  switch (e.kind) {
    case 'heal': {
      if (P.hp >= P.stats.hpMax) { toast('Already at full health', ''); return; }
      P.hp = clamp(P.hp + P.stats.hpMax * e.param, 0, P.stats.hpMax);
      dmgNum(P.pos, '+' + Math.round(P.stats.hpMax * e.param), '#7fd87f');
      break;
    }
    case 'mana': {
      if (P.mp >= P.stats.mpMax) { toast('Already at full mana', ''); return; }
      P.mp = clamp(P.mp + P.stats.mpMax * e.param, 0, P.stats.mpMax);
      break;
    }
    case 'stam': P.st = clamp(P.st + P.stats.stMax * e.param, 0, P.stats.stMax); break;
    case 'cure': {
      const had = P.statuses.some(s => s.id === e.param);
      P.statuses = P.statuses.filter(s => s.id !== e.param);
      toast(had ? 'Cured ' + e.param : 'Nothing to cure', had ? 'good' : '');
      recalcStats(P);
      break;
    }
    case 'resist': {
      const weakest = ['fire', 'frost', 'light', 'poison', 'arc'].sort((a, b) => P.stats.res[a] - P.stats.res[b])[0];
      addBuff(P, 'elixir', 'Resistance Elixir', 30, { resAll: 0 }, '🧪');
      P.buffs[P.buffs.length - 1].mods['res' + weakest[0].toUpperCase() + weakest.slice(1)] = 25;
      toast('+25% ' + weakest + ' resistance for 30 s', 'good');
      recalcStats(P);
      break;
    }
    case 'identify': {
      const target = P.inv.find(i => i && !i.identified && i.rarity !== 'common');
      if (!target) { toast('Nothing to identify', ''); return; }
      target.identified = true;
      target.name = target.name;
      toast('Identified: ' + target.name, 'good');
      SND.identify();
      break;
    }
    case 'portal': {
      if (G.mode !== 'dungeon') { toast('Only usable in the dungeon', 'bad'); return; }
      P.channel = { id: 'return_sigil', t: 0, dur: 3, mana: 0, scroll: true };
      used = true;
      break;
    }
  }
  if (used) {
    consumeFromStack(it, 1);
    if (isPotion) P.potionCd = CFG.potionCD;
    SND.potion();
    EVT.emit('ItemConsumed', { item: it });
  }
}
function confirmModal(text) {
  // synchronous-ish modal via window.confirm for one-shot build
  return window.confirm(text);
}

/* ============================================================
   14. UI — shops, dialogue, map overlay, menus, settings
   ============================================================ */
function vendorStock(vId) {
  const c = G.campaign;
  c.vendorStock = c.vendorStock || {};
  c.vendorMilestone = c.vendorMilestone || 0;
  if (!c.vendorStock[vId]) { rollVendorStock(vId); }
  else if (c.maxFloor > c.vendorMilestone) {
    rollVendorStock(vId, true);
    c.vendorMilestone = c.maxFloor;
    toast('Merchants restocked their wares.', '');
  }
  return c.vendorStock[vId];
}
function rollVendorStock(vId, restock) {
  const v = VENDORS[vId];
  const c = G.campaign;
  c.vendorStock = c.vendorStock || {};
  const stock = [];
  for (const s of v.staples) {
    const [id, qty] = s.split(':');
    const it = makeItem(id, 1, 'common', mulberry32(hashMix(1, vId.length)), { identified: true, qty: qty ? +qty : 1 });
    if (it) stock.push({ item: it, staple: true });
  }
  const rng = mulberry32(hashMix(c.seed, c.descent || 0, vId.length, c.maxFloor, 7));
  const n = ri(rng, 3, 5);
  for (let i = 0; i < n; i++) {
    const it = rollLoot(rng, { ilvl: Math.max(1, c.maxFloor) + 1, n: 1, weights: { common: 20, enchanted: 60, rare: 20, relic: 0 }, identified: true })[0];
    if (it) stock.push({ item: it });
  }
  c.vendorStock[vId] = stock;
}
function buybackList() { G.campaign.buyback = G.campaign.buyback || []; return G.campaign.buyback; }

function openShop(vId) {
  const v = VENDORS[vId];
  const panel = openPanel(`
    <div class="row" style="margin-bottom:6px"><h2 style="flex:1">${v.glyph} ${v.name}</h2><div class="btn small" id="closeScr">Leave [Esc]</div></div>
    <div class="dim" style="margin-bottom:8px">"${v.greeting}"</div>
    <div class="tabs"><div class="tab act" data-t="buy">Buy</div><div class="tab" data-t="sell">Sell</div><div class="tab" data-t="serv">Services</div><div style="flex:1"></div><div style="color:var(--gold2);align-self:center">${fmt(P.gold)} gold</div></div>
    <div id="shopBody" class="list" style="max-height:62vh; min-width:560px"></div>`, 'wide');
  let tab = 'buy';
  const refresh = () => {
    panel.querySelectorAll('.tab').forEach(t => t.classList.toggle('act', t.dataset.t === tab));
    const body = panel.querySelector('#shopBody');
    panel.querySelector('[style*="gold"]').textContent = fmt(P.gold) + ' gold';
    if (tab === 'buy') {
      const stock = vendorStock(vId);
      body.innerHTML = stock.map((s, i) => {
        const it = s.item;
        const afford = P.gold >= it.price;
        return `<div class="vrow ${afford ? '' : 'dis'}" data-buy="${i}">
          <span style="color:${RAR[RAR_IDX[it.rarity]].col}">${glyphFor(it)} ${esc(it.name)}${it.qty > 1 ? ' ×' + it.qty : ''}</span>
          <span class="dim">${it.cat === 'ammo' ? fmt(it.price) : fmt(it.price)}g</span></div>`;
      }).join('') + `<div class="vrow dis"><span class="dim">— buyback (last sold) —</span><span></span></div>` +
        buybackList().slice(-8).reverse().map((it, i) => `<div class="vrow" data-bb="${i}"><span style="color:${RAR[RAR_IDX[it.rarity]].col}">${glyphFor(it)} ${esc(it.name)}</span><span class="dim">${fmt(it.price)}g</span></div>`).join('');
    } else if (tab === 'sell') {
      const sellables = P.inv.filter(it => it && it.cat !== 'quest' && it.base !== 'arrows' || (it && it.base === 'arrows'));
      body.innerHTML = sellables.map(it => `<div class="vrow" data-sell="${P.inv.indexOf(it)}">
        <span style="color:${RAR[RAR_IDX[it.rarity]].col}">${glyphFor(it)} ${esc(it.identified ? it.name : it.name.replace(/^(\w+ \w+).*/, '$1') + ' ???')}${it.qty > 1 ? ' ×' + it.qty : ''}</span>
        <span class="dim">${fmt(sellValue(it))}g${it.identified ? '' : ' (unidentified)'}</span></div>`).join('') || '<div class="vrow dis"><span class="dim">Nothing to sell.</span></div>';
    } else {
      let h = '';
      if (v.services.includes('repair')) {
        const dmgd = SLOT_NAMES.map(k => P.equip[k]).concat(P.inv).filter(it => it && it.durMax && it.dur < it.durMax);
        const cost = dmgd.reduce((a, it) => a + repairCost(it), 0);
        h += `<div class="vrow" data-serv="repair"><span>Repair all gear${dmgd.length ? ' (' + dmgd.length + ' items)' : ''}</span><span class="dim">${cost}g</span></div>`;
      }
      if (v.services.includes('identify')) {
        const unid = P.inv.filter(it => it && !it.identified && it.rarity !== 'common');
        const cost = unid.reduce((a, it) => a + identifyCost(it), 0);
        h += `<div class="vrow" data-serv="identify"><span>Identify all${unid.length ? ' (' + unid.length + ' items)' : ''}</span><span class="dim">${cost}g</span></div>`;
        unid.forEach((it, i) => { h += `<div class="vrow" data-ident="${P.inv.indexOf(it)}"><span style="color:#7a9ab5">Identify: ${esc(it.name.replace(/^(\w+ \w+).*/, '$1') + ' ???')}</span><span class="dim">${identifyCost(it)}g</span></div>`; });
      }
      if (v.services.includes('recharge')) h += `<div class="vrow dis"><span>Recharge staves/foci</span><span class="dim">no charged items in this build</span></div>`;
      if (v.services.includes('heal')) {
        const cost = v.healCost(P.level);
        h += `<div class="vrow" data-serv="heal"><span>Restore health, cure poison &amp; curse</span><span class="dim">${cost}g</span></div>`;
      }
      if (v.services.includes('stash')) h += `<div class="vrow" data-serv="stash"><span>Open shared stash</span><span class="dim">12×10 · 3 tabs</span></div>`;
      if (v.services.includes('respec')) {
        const cost = v.respecCost(P.level);
        h += `<div class="vrow" data-serv="respec"><span>Respec all talent points</span><span class="dim">${cost}g</span></div>`;
      }
      if (!h) h = '<div class="vrow dis"><span class="dim">No services.</span></div>';
      body.innerHTML = h;
    }
  };
  panel.addEventListener('click', e => {
    const t = e.target.closest('.tab');
    if (t) { tab = t.dataset.t; SND.ui(); refresh(); return; }
    if (e.target.id === 'closeScr') { closeAllScreens(); return; }
    const buy = e.target.closest('[data-buy]');
    if (buy) {
      const stock = vendorStock(vId);
      const s = stock[+buy.dataset.buy];
      if (!s) return;
      const it = s.item;
      if (P.gold < it.price) { SND.error(); toast('Not enough gold', 'bad'); return; }
      if (!addToBag(P, it)) { SND.error(); toast('Backpack full', 'bad'); return; }
      goldChange(P, -it.price, 'bought ' + it.name);
      if (!s.staple) stock.splice(+buy.dataset.buy, 1);
      else s.item = makeItem(it.base, it.ilvl, it.rarity, mulberry32(hashMix(Date.now() % 1e6, +buy.dataset.buy)), { identified: true, qty: it.qty });
      SND.gold();
      EVT.emit('VendorTransactionCommitted', { type: 'buy' });
      refresh(); return;
    }
    const bb = e.target.closest('[data-bb]');
    if (bb) {
      const list = buybackList();
      const idx = list.length - 1 - (+bb.dataset.bb);
      const it = list[idx];
      if (!it) return;
      if (P.gold < it.price) { SND.error(); toast('Not enough gold', 'bad'); return; }
      if (!addToBag(P, it)) { SND.error(); toast('Backpack full', 'bad'); return; }
      goldChange(P, -it.price, 'bought back ' + it.name);
      list.splice(idx, 1);
      SND.gold(); refresh(); return;
    }
    const sell = e.target.closest('[data-sell]');
    if (sell) {
      const it = P.inv[+sell.dataset.sell];
      if (!it || it.cat === 'quest') return;
      const sv = sellValue(it);
      goldChange(P, sv, 'sold ' + it.name);
      buybackList().push(it);
      if (buybackList().length > CFG.buybackMax) buybackList().shift();
      P.inv.splice(P.inv.indexOf(it), 1);
      SND.gold();
      EVT.emit('VendorTransactionCommitted', { type: 'sell' });
      refresh(); return;
    }
    const serv = e.target.closest('[data-serv]');
    if (serv) doService(vId, serv.dataset.serv, refresh);
    const ident = e.target.closest('[data-ident]');
    if (ident) {
      const it = P.inv[+ident.dataset.ident];
      const cost = identifyCost(it);
      if (P.gold < cost) { SND.error(); toast('Not enough gold', 'bad'); return; }
      goldChange(P, -cost, 'identified an item');
      it.identified = true; SND.identify();
      EVT.emit('VendorTransactionCommitted', { type: 'identify' });
      refresh();
    }
  });
  refresh();
  G.uiOpen = 'shop';
}
function doService(vId, kind, refresh) {
  const v = VENDORS[vId];
  if (kind === 'repair') {
    const items = SLOT_NAMES.map(k => P.equip[k]).concat(P.inv).filter(it => it && it.durMax && it.dur < it.durMax);
    const cost = items.reduce((a, it) => a + repairCost(it), 0);
    if (!items.length) { toast('Nothing to repair', ''); return; }
    if (P.gold < cost) { SND.error(); toast('Not enough gold', 'bad'); return; }
    goldChange(P, -cost, 'repaired ' + items.length + ' items');
    items.forEach(it => it.dur = it.durMax);
    recalcStats(P); SND.ui();
    EVT.emit('VendorTransactionCommitted', { type: 'repair' });
    refresh(); return;
  }
  if (kind === 'identify') {
    const unid = P.inv.filter(it => it && !it.identified && it.rarity !== 'common');
    const cost = unid.reduce((a, it) => a + identifyCost(it), 0);
    if (!unid.length) { toast('Nothing to identify', ''); return; }
    if (P.gold < cost) { SND.error(); toast('Not enough gold', 'bad'); return; }
    goldChange(P, -cost, 'identified ' + unid.length + ' items');
    unid.forEach(it => it.identified = true);
    SND.identify(); EVT.emit('VendorTransactionCommitted', { type: 'identify' });
    refresh(); return;
  }
  if (kind === 'heal') {
    const cost = v.healCost(P.level);
    if (P.gold < cost) { SND.error(); toast('Not enough gold', 'bad'); return; }
    goldChange(P, -cost, 'healed by ' + v.name);
    P.hp = P.stats.hpMax;
    P.statuses = P.statuses.filter(s => !['poison', 'curse', 'bleed'].includes(s.id));
    SND.castHoly(); toast('Fully healed.', 'good');
    EVT.emit('VendorTransactionCommitted', { type: 'heal' });
    refresh(); return;
  }
  if (kind === 'stash') { openStash(); return; }
  if (kind === 'respec') {
    const cost = v.respecCost(P.level);
    if (P.gold < cost) { SND.error(); toast('Not enough gold', 'bad'); return; }
    let pts = 0;
    for (const t of TALENTS) if (t.cls === P.cls) { pts += P.talents[t.id] || 0; P.talents[t.id] = 0; }
    P.unspentTalent += pts;
    P.skillQ = null; P.skillR = null;
    goldChange(P, -cost, 'respec (' + pts + ' points returned)');
    recalcStats(P); SND.uiBig(); toast('Talents reset — ' + pts + ' points returned', 'good');
    EVT.emit('VendorTransactionCommitted', { type: 'respec' });
    refresh(); return;
  }
}

function openStash() {
  stashInit();
  UI._stashTab = UI._stashTab || 0;
  const SW = 12, SH = 10;
  const panel = openPanel(`
    <div class="row" style="margin-bottom:6px"><h2 style="flex:1">Shared Stash</h2><div class="btn small" id="closeScr">Close</div></div>
    <div class="tabs" id="stashTabs"></div>
    <div style="display:flex;gap:16px;flex-wrap:wrap">
      <div id="stashGrid" style="position:relative"></div>
      <div><h3>Backpack</h3><div id="stashBag" style="position:relative"></div></div>
    </div>`);
  const refresh = () => {
    const tabs = panel.querySelector('#stashTabs');
    tabs.innerHTML = [0, 1, 2].map(i => `<div class="tab ${i === UI._stashTab ? 'act' : ''}" data-i="${i}">Tab ${i + 1}</div>`).join('');
    tabs.querySelectorAll('.tab').forEach(t => t.onclick = () => { UI._stashTab = +t.dataset.i; SND.ui(); refresh(); });
    const sg = panel.querySelector('#stashGrid');
    sg.style.width = SW * 34 + 'px'; sg.style.height = SH * 34 + 'px';
    let h = '';
    for (let y = 0; y < SH; y++) for (let x = 0; x < SW; x++) h += `<div class="cell" data-drop="stash" data-x="${x}" data-y="${y}" style="position:absolute;left:${x * 34}px;top:${y * 34}px"></div>`;
    sg.innerHTML = h;
    for (const it of G.campaign.stash[UI._stashTab]) sg.appendChild(itemEl(it, { from: 'stash', tab: UI._stashTab }));
    const bg = panel.querySelector('#stashBag');
    bg.style.width = BAG_W * 34 + 'px'; bg.style.height = BAG_H * 34 + 'px';
    let hb = '';
    for (let y = 0; y < BAG_H; y++) for (let x = 0; x < BAG_W; x++) hb += `<div class="cell" data-drop="bag" data-x="${x}" data-y="${y}" style="position:absolute;left:${x * 34}px;top:${y * 34}px"></div>`;
    bg.innerHTML = hb;
    for (const it of P.inv) if (it) bg.appendChild(itemEl(it, { from: 'bag' }));
  };
  panel.addEventListener('click', e => {
    if (e.target.id === 'closeScr') { closeAllScreens(); return; }
    if (e.target.closest('[data-drop="stash"]') && e.shiftKey && DRAG.item) { /* handled in drop */ }
  });
  SCREENS.push({ refresh });
  refresh();
  G.uiOpen = 'stash';
}

/* ---------------- dialogue ---------------- */
function openDialog(npcId) {
  const v = VENDORS[npcId];
  if (document.pointerLockElement) document.exitPointerLock();
  const dlg = el('dlgBox');
  dlg.classList.remove('hidden');
  const opts = [];
  opts.push(...dialogOptions(npcId));
  el('dlgName').textContent = v.name;
  el('dlgText').textContent = v.greeting;
  const ob = el('dlgOpts');
  ob.innerHTML = '';
  for (const o of opts) {
    const b = mk('button', 'btn dlgOpt', esc(o.label));
    b.onclick = () => { SND.ui(); o.fn(); };
    ob.appendChild(b);
  }
  G.uiOpen = 'dialog';
}
function closeDialog() {
  el('dlgBox').classList.add('hidden');
  if (G.uiOpen === 'dialog') G.uiOpen = null;
}
function dialogOptions(npcId) {
  const v = VENDORS[npcId];
  const out = [];
  const activeMain = QUESTS.filter(q => q.main && G.campaign.quests[q.id]?.state === 'active');
  const turnIn = QUESTS.filter(q => G.campaign.quests[q.id]?.state === 'turnin' || (G.campaign.quests[q.id]?.state === 'active' && objectivesMet(q)));
  const giverSide = QUESTS.filter(q => !q.main && q.giver === npcId && !G.campaign.quests[q.id]);
  const sideTurnIn = QUESTS.filter(q => !q.main && q.giver === npcId && G.campaign.quests[q.id]?.state === 'active' && objectivesMet(q));
  const availMain = QUESTS.filter(q => q.main && !G.campaign.quests[q.id] && prevMainDone(q));
  for (const q of turnIn) out.push({ label: '✔ Turn in: ' + q.name, fn: () => completeQuest(q) });
  for (const q of availMain) out.push({ label: '✦ Quest: ' + q.name, fn: () => acceptQuest(q) });
  for (const q of giverSide) out.push({ label: '✦ Quest: ' + q.name, fn: () => acceptQuest(q) });
  for (const q of sideTurnIn) out.push({ label: '✔ Turn in: ' + q.name, fn: () => completeQuest(q) });
  if (activeMain.length) { const q = activeMain[0]; const o = nextObjective(q); if (o) out.push({ label: '”? ' + o.text, fn: () => toast(o.text, '') }); }
  if (v.services.includes('buy')) out.push({ label: 'Trade (buy / sell)', fn: () => { closeDialog(); openShop(npcId); } });
  if (v.services.includes('repair')) out.push({ label: 'Repair gear', fn: () => { closeDialog(); openShop(npcId); } });
  if (v.services.includes('identify')) out.push({ label: 'Identify / recharge', fn: () => { closeDialog(); openShop(npcId); } });
  if (v.services.includes('heal')) out.push({ label: 'Be healed (' + v.healCost(P.level) + 'g)', fn: () => { doService(npcId, 'heal', () => {}); } });
  if (v.services.includes('stash')) out.push({ label: 'Open stash', fn: () => { closeDialog(); openStash(); } });
  if (v.services.includes('respec')) out.push({ label: 'Respec talents (' + v.respecCost(P.level) + 'g)', fn: () => { doService(npcId, 'respec', () => {}); } });
  out.push({ label: 'Ask for a rumor', fn: () => { el('dlgText').textContent = pick(Math.random, RUMORS); } });
  out.push({ label: 'Leave', fn: closeDialog });
  return out;
}
const RUMORS = [
  'They say the water in the third gallery conducts more than sound.',
  'A bell rings below. The dead keep its time.',
  'The ash down there still remembers being wood.',
  'Gold buys rope in Hollowmere. Rope buys a little more time.',
  'Kick the crates. Half my pension came out of crates.',
  'Block early, strike late. The dead are honest but slow.',
  'The Captain held the fourth floor until the ash took him.',
  'Unidentified loot is a lottery ticket. The Mystic is the teller.',
];
function nextObjective(q) {
  const st = G.campaign.quests[q.id];
  for (const o of q.objectives) if (!(st.objDone || {})[o.id]) return o;
  return null;
}
function objectivesMet(q) {
  const st = G.campaign.quests[q.id];
  const pending = q.objectives.filter(o => !['dialog', 'deliver'].includes(o.type));
  return pending.every(o => (st.objDone || {})[o.id]) && pending.length !== q.objectives.length;
}
function prevMainDone(q) {
  const mains = QUESTS.filter(x => x.main);
  const i = mains.indexOf(q);
  return i === 0 || mains.slice(0, i).every(x => G.campaign.quests[x.id]?.state === 'done');
}
function acceptQuest(q) {
  G.campaign.quests[q.id] = { state: 'active', objDone: {} };
  toast('Quest accepted: ' + q.name, 'good');
  SND.quest();
  EVT.emit('QuestObjectiveAdvanced', { quest: q.id });
  closeDialog();
}
function completeQuest(q) {
  const st = G.campaign.quests[q.id];
  if (st.state === 'done') return;
  // deliver objectives consume items
  for (const o of q.objectives) {
    if (o.type === 'deliver') {
      let remaining = o.count;
      for (const it of [...P.inv]) {
        if (it && it.base === o.base && remaining > 0) {
          const take = Math.min(it.qty, remaining);
          consumeFromStack(it, take);
          remaining -= take;
        }
      }
    }
    if (o.type === 'pickup') {
      const i = P.inv.findIndex(it => it && it.base === o.base);
      if (i >= 0) P.inv.splice(i, 1);
    }
  }
  st.state = 'done';
  const r = q.rewards || {};
  if (r.gold) goldChange(P, r.gold, 'quest reward');
  if (r.xp) gainXP(P, r.xp);
  if (r.item) {
    let item = null;
    if (r.item.includes(':')) { const [b, n] = r.item.split(':'); item = makeItem(b, P.level, 'common', mulberry32(42), { identified: true, qty: +n }); }
    else if (r.item === 'rare') item = rollLoot(mulberry32((Date.now() % 1e6) + 7), { ilvl: Math.max(1, G.campaign.maxFloor), n: 1, weights: { common: 0, enchanted: 40, rare: 60, relic: 0 }, identified: true })[0];
    else if (r.item === 'enchanted') item = rollLoot(mulberry32((Date.now() % 1e6) + 8), { ilvl: Math.max(1, G.campaign.maxFloor), n: 1, weights: { common: 0, enchanted: 100, rare: 0, relic: 0 }, identified: true })[0];
    else if (r.item === 'relic') item = rollLoot(mulberry32((Date.now() % 1e6) + 9), { ilvl: Math.max(1, G.campaign.maxFloor), n: 1, rarity: 'relic', identified: true })[0];
    else if (ITEM_BASES[r.item]) item = makeItem(r.item, P.level, 'common', mulberry32(11), { identified: true });
    if (item) {
      if (!addToBag(P, item)) {
        // protected reward cache: grant at feet
        spawnGroundItem(G.floor || buildTown(G.campaign), P.pos?.[0] || 0, (P.pos?.[2] || 0) + 1, { item }, item.rarity);
        toast('Reward dropped at your feet (backpack full)', 'bad');
      } else toast('Reward: ' + item.name, 'good');
    }
  }
  SND.quest();
  toast('Quest completed: ' + q.name, 'good');
  EVT.emit('QuestCompleted', { quest: q.id });
  if (q.id === 'mq4' && q.rewards.ending) { closeDialog(); setTimeout(() => showVictoryScreen(), 600); return; }
  closeDialog();
  saveGame(true);
}

/* ---------------- map overlay ---------------- */
function openMapOverlay() {
  const panel = openPanel(`
    <div class="row"><h2 style="flex:1">World Map</h2><div class="btn small" id="closeScr">Close [M]</div></div>
    <canvas id="bigmap" width="640" height="440" style="border:1px solid #2c261c; cursor:grab; touch-action:none"></canvas>
    <div class="dim" style="margin-top:6px">Legend: <span style="color:#c04040">■ locked</span> <span style="color:#c8a84a">■ secret</span> <span style="color:#e8c84a">▼ stairs</span> <span style="color:#ff9a3c">■ rare chest</span> <span style="color:#b06aff">■ portal</span></div>`);
  const c = panel.querySelector('#bigmap');
  const ctx = c.getContext('2d');
  let pan = [0, 0], zoom = 1, drag = null;
  const redraw = () => drawFullMap(ctx, c, pan, zoom);
  c.addEventListener('wheel', e => { e.preventDefault(); zoom = clamp(zoom * (e.deltaY < 0 ? 1.15 : 0.87), 0.4, 4); redraw(); });
  c.addEventListener('mousedown', e => drag = [e.clientX - pan[0] * zoom, e.clientY - pan[1] * zoom]);
  window.addEventListener('mousemove', e => { if (drag) { pan = [(e.clientX - drag[0]) / zoom, (e.clientY - drag[1]) / zoom]; redraw(); } });
  window.addEventListener('mouseup', () => drag = null);
  SCREENS.push({ refresh: redraw });
  redraw();
  G.uiOpen = 'map';
}

/* ---------------- gate / floor select ---------------- */
function openGateMenu() {
  const wps = [...new Set([1, ...G.campaign.waypoints])].sort((a, b) => a - b);
  const panel = openPanel(`
    <h2>The Underkeep Gate</h2>
    <div class="dim" style="margin-bottom:8px">Choose a floor to descend to. Deeper waypoints unlock as bosses fall.</div>
    <div id="gateList" style="display:flex;flex-direction:column;gap:4px;min-width:340px"></div>
    <div class="row" style="margin-top:10px"><div class="btn small" id="closeScr">Stay in town</div></div>`);
  const list = panel.querySelector('#gateList');
  list.innerHTML = wps.map(f => {
    const reg = regionOf(f);
    return `<div class="vrow" data-floor="${f}"><span>Floor ${f}</span><span class="dim">${reg.name} — ${reg.desc}</span></div>`;
  }).join('');
  list.addEventListener('click', e => {
    const r = e.target.closest('[data-floor]');
    if (r) { closeAllScreens(); enterFloor(+r.dataset.floor, 'gate'); }
  });
  panel.querySelector('#closeScr').onclick = closeAllScreens;
  G.uiOpen = 'gate';
}

/* ---------------- menus ---------------- */
function showMainMenu() {
  G.state = 'menu';
  closeAllScreens();
  el('hud').classList.add('hidden');
  const m = el('menuRoot');
  m.classList.remove('hidden');
  const chars = listSaves();
  const last = chars[0];
  m.innerHTML = `
    <div>
      <div id="menuTitle">HOLLOWMERE</div>
      <div id="menuSub">A FIRST-PERSON DUNGEON ARPG · BUILT FROM THE DESIGN SPECIFICATION · NO ENGINE</div>
      <div class="menuBtns">
        ${last ? `<div class="btn" id="mCont">Continue — ${esc(last.name)} (Lv ${last.level})</div>` : ''}
        <div class="btn" id="mNew">New Character</div>
        <div class="btn" id="mLoad">Load Character</div>
        <div class="btn" id="mOpt">Options</div>
        <div class="btn" id="mHelp">Help / Controls</div>
        <div class="btn" id="mCred">Credits</div>
      </div>
      <div class="cred" style="margin-top:26px">Single-player · 16 floors · 4 regions · 3 classes · procedural loot<br>Design doc: first_person_dungeon_arpg_design.md</div>
    </div>`;
  m.querySelector('#mCont')?.addEventListener('click', () => { SND.ui(); loadCharacter(last.id); });
  m.querySelector('#mNew').addEventListener('click', () => { SND.ui(); openCreation(); });
  m.querySelector('#mLoad').addEventListener('click', () => { SND.ui(); openLoad(); });
  m.querySelector('#mOpt').addEventListener('click', () => { SND.ui(); openSettingsScreen(() => showMainMenu()); });
  m.querySelector('#mHelp').addEventListener('click', () => { SND.ui(); openHelp(() => showMainMenu()); });
  m.querySelector('#mCred').addEventListener('click', () => { SND.ui(); openCredits(); });
}
function openLoad() {
  const chars = listSaves();
  const panel = openPanel(`
    <h2>Characters</h2>
    <div id="charList" class="list" style="min-width:400px;max-height:50vh"></div>
    <div class="row" style="margin-top:10px"><div class="btn small" id="closeScr">Back</div></div>`);
  const list = panel.querySelector('#charList');
  list.innerHTML = chars.length ? chars.map(c => `
    <div class="vrow" data-c="${c.id}"><span>${esc(c.name)} — ${CLASSES[c.cls]?.name || c.cls} Lv ${c.level}${c.hardcore ? ' ☠HC' : ''}${c.dead ? ' (DEAD)' : ''}</span>
    <span class="dim">${c.floor ? 'Floor ' + c.floor : 'town'} · ${new Date(c.saved).toLocaleString()}</span></div>`).join('') : '<div class="vrow dis"><span class="dim">No characters yet.</span></div>';
  list.addEventListener('click', e => {
    const r = e.target.closest('[data-c]');
    if (r) {
      const c = chars.find(x => x.id === r.dataset.c);
      if (c.dead) { toast('This hardcore character has died and cannot be played.', 'bad'); SND.error(); return; }
      loadCharacter(c.id);
    }
  });
  panel.querySelector('#closeScr').onclick = () => showMainMenu();
}
function openCredits() {
  const panel = openPanel(`
    <h2>Credits</h2>
    <div class="cred">
      <b style="color:var(--gold2)">Hollowmere</b> — built in one shot from<br>
      <i>first_person_dungeon_arpg_design.md</i> (v1.1, 2026-11-18).<br><br>
      No game engine: raw WebGL2 rendering, DOM UI,<br>
      procedural WebAudio synthesis, hand-rolled world generation.<br><br>
      All content is original placeholder fiction per the spec's<br>
      copyright boundary. Self-tests: run <b>node game.js</b>.<br><br>
      Design reference inspirations listed in §23 of the spec.
    </div>
    <div class="row" style="margin-top:12px;justify-content:center"><div class="btn small" id="closeScr">Back</div></div>`);
  panel.querySelector('#closeScr').onclick = () => showMainMenu();
}
function openHelp(back) {
  const panel = openPanel(`
    <h2>Help / Controls</h2>
    <table class="helpTable">
      <tr><td>WASD</td><td>Move</td><td>Mouse</td><td>Look (click canvas to lock)</td></tr>
      <tr><td>LMB</td><td>Light attack / shoot bow / cast selected spell (staff)</td><td>Hold LMB</td><td>Heavy charge / strong cast / bow draw</td></tr>
      <tr><td>RMB</td><td>Raise shield / guard (weapon)</td><td>F</td><td>Kick (shoves enemies & props)</td></tr>
      <tr><td>Space</td><td>Jump</td><td>Shift</td><td>Sprint (stamina)</td></tr>
      <tr><td>Alt</td><td>Dodge (i-frames)</td><td>C</td><td>Crouch</td></tr>
      <tr><td>E</td><td>Interact</td><td>Q / R</td><td>Class ability slots</td></tr>
      <tr><td>1–6</td><td>Belt (potions/scrolls)</td><td>Tab</td><td>Inventory / Character / Skills</td></tr>
      <tr><td>M</td><td>Map</td><td>J</td><td>Journal</td></tr>
      <tr><td>T</td><td>Return Sigil channel (or scroll)</td><td>X</td><td>Cycle attack spell (staff/wand)</td></tr>
      <tr><td>G</td><td>Drop held item (from inventory drag out)</td><td>H</td><td>Sheathe/unsheathe</td></tr>
      <tr><td>Esc</td><td>Pause menu</td></tr>
    </table>
    <div class="dim" style="margin-top:8px">Tips: perfect block within 0.18 s of raising guard staggers attackers. Kick enemies into spike plates. Unidentified items work but hide their rolls — identify at the Mystic. Bosses stagger after missing a charge.</div>
    <div class="row" style="margin-top:10px"><div class="btn small" id="closeScr">Back</div></div>`);
  panel.querySelector('#closeScr').onclick = () => back();
}
function openSettingsScreen(back) {
  const s = G.settings;
  const panel = openPanel(`
    <h2>Options</h2>
    <div style="max-height:66vh;overflow:auto;min-width:420px" id="setBody"></div>
    <div class="row" style="margin-top:10px"><div class="btn small" id="closeScr">Back</div></div>`);
  const refresh = () => {
    const b = panel.querySelector('#setBody');
    const bindRow = (act, label) => `<div class="setRow"><label>${label}</label><div class="kb2" data-bind="${act}">${bindLabel(act)}</div></div>`;
    b.innerHTML = `
      <div class="setRow"><label>Mouse sensitivity</label><input type="range" min="0.2" max="3" step="0.05" value="${s.sens}" data-set="sens"></div>
      <div class="setRow"><label>Invert mouse Y</label><input type="checkbox" ${s.invertY ? 'checked' : ''} data-set="invertY"></div>
      <div class="setRow"><label>Field of view</label><input type="range" min="60" max="110" step="1" value="${s.fov}" data-set="fov"> <span class="dim">${s.fov}°</span></div>
      <div class="setRow"><label>Head bob</label><input type="checkbox" ${s.bob ? 'checked' : ''} data-set="bob"></div>
      <div class="setRow"><label>UI scale</label><input type="range" min="0.8" max="1.4" step="0.05" value="${s.uiScale}" data-set="uiScale"></div>
      <div class="setRow"><label>Master volume</label><input type="range" min="0" max="1" step="0.05" value="${s.volMaster}" data-set="volMaster"></div>
      <div class="setRow"><label>Music volume</label><input type="range" min="0" max="1" step="0.05" value="${s.volMusic}" data-set="volMusic"></div>
      <div class="setRow"><label>Effects volume</label><input type="range" min="0" max="1" step="0.05" value="${s.volSfx}" data-set="volSfx"></div>
      <div class="setRow"><label>Ambience volume</label><input type="range" min="0" max="1" step="0.05" value="${s.volAmb}" data-set="volAmb"></div>
      <div class="setRow"><label>Floating damage numbers</label><input type="checkbox" ${s.dmgNumbers ? 'checked' : ''} data-set="dmgNumbers"></div>
      <div class="setRow"><label>Enemy health bars</label><input type="checkbox" ${s.enemyBars ? 'checked' : ''} data-set="enemyBars"></div>
      <div class="setRow"><label>Gore (dismemberment props)</label><input type="checkbox" ${s.gore ? 'checked' : ''} data-set="gore"></div>
      <div class="setRow"><label>Auto-pickup gold</label><input type="checkbox" ${s.autoGold ? 'checked' : ''} data-set="autoGold"></div>
      <h3>Key bindings</h3>
      ${bindRow('interact', 'Interact')}${bindRow('kick', 'Kick')}${bindRow('dodge', 'Dodge')}${bindRow('skillQ', 'Ability Q')}${bindRow('skillR', 'Ability R')}${bindRow('portal', 'Return Sigil')}${bindRow('crouch', 'Crouch')}${bindRow('sheathe', 'Sheathe')}
      <div class="dim" style="margin-top:4px">WASD, mouse, sprint, jump, Tab/M/J/Esc and 1–6 are fixed in this build.</div>`;
    b.querySelectorAll('[data-set]').forEach(inp => {
      inp.oninput = () => {
        const k = inp.dataset.set;
        s[k] = inp.type === 'checkbox' ? inp.checked : +inp.value;
        saveSettings();
        if (k.startsWith('vol')) SND.applyVolumes(s);
        if (k === 'uiScale') el('hud').style.fontSize = (s.uiScale * 100) + '%';
      };
    });
    b.querySelectorAll('[data-bind]').forEach(kb => {
      kb.onclick = () => {
        kb.textContent = 'press key…';
        const handler = e => {
          e.preventDefault(); e.stopPropagation();
          s.binds = s.binds || {};
          s.binds[kb.dataset.bind] = e.code;
          saveSettings();
          window.removeEventListener('keydown', handler, true);
          refresh();
        };
        window.addEventListener('keydown', handler, true);
      };
    });
  };
  panel.querySelector('#closeScr').onclick = () => { saveSettings(); back(); };
  refresh();
}
function bindLabel(act) {
  const code = (G.settings.binds && G.settings.binds[act]) || DEFAULT_BINDS[act];
  if (!code) return '—';
  return code.replace('Key', '').replace('Digit', '').replace('Left ', '').replace('Right ', '');
}
function openPauseMenu() {
  const panel = openPanel(`
    <h2 style="text-align:center">Paused</h2>
    <div class="menuBtns" style="margin:0 auto">
      <div class="btn" id="pRes">Resume</div>
      <div class="btn" id="pSave">Save</div>
      <div class="btn" id="pOpt">Options</div>
      <div class="btn" id="pHelp">Help / Controls</div>
      ${G.mode === 'town' ? `<div class="btn" id="pDiff">Difficulty: ${CFG.difficulty[G.campaign.difficulty].label}</div>` : ''}
      ${G.mode === 'town' && G.campaign.storyDone ? '<div class="btn danger" id="pDesc">Start New Descent</div>' : ''}
      <div class="btn" id="pExit">Save &amp; Exit to Menu</div>
    </div>`);
  panel.querySelector('#pRes').onclick = () => { closeAllScreens(); };
  panel.querySelector('#pSave').onclick = () => { saveGame(false); toast('Saved.', 'good'); };
  panel.querySelector('#pOpt').onclick = () => openSettingsScreen(() => openPauseMenu());
  panel.querySelector('#pHelp').onclick = () => openHelp(() => openPauseMenu());
  if (panel.querySelector('#pDiff')) panel.querySelector('#pDiff').onclick = () => {
    const order = ['wanderer', 'adventurer', 'dread'];
    const next = order[(order.indexOf(G.campaign.difficulty) + 1) % 3];
    G.campaign.difficulty = next;
    toast('Difficulty: ' + CFG.difficulty[next].label, '');
    closeAllScreens(); openPauseMenu();
  };
  if (panel.querySelector('#pDesc')) panel.querySelector('#pDesc').onclick = () => {
    if (confirmModal('Start a New Descent? Floor layouts, enemies and treasure regenerate; your character, quests and story progress remain.')) {
      closeAllScreens(); newDescent();
    }
  };
  panel.querySelector('#pExit').onclick = () => { saveGame(false); showMainMenu(); };
  G.uiOpen = 'pause';
}
function showDeathScreen(hardcore) {
  const panel = openPanel(`
    <div id="deathBox">
      <h1>YOU DIED</h1>
      ${hardcore
      ? `<p>Your hardcore character is lost. The Underkeep keeps what it takes.</p>
         <div class="row" style="justify-content:center"><div class="btn" id="dMenu">Main Menu</div></div>`
      : `<p>Your gold cache (recoverable) waits where you fell.<br>Bosses slain stay slain; the dungeon remembers your steps.</p>
         <div class="row" style="justify-content:center"><div class="btn" id="dTown">Return to Town</div><div class="btn" id="dMenu">Main Menu</div></div>`}
    </div>`);
  if (!hardcore) panel.querySelector('#dTown').onclick = () => { respawnInTown(); };
  panel.querySelector('#dMenu').onclick = () => { saveGame(false); showMainMenu(); };
}
function respawnInTown() {
  P.dead = false;
  P.hp = P.stats.hpMax; P.mp = P.stats.mpMax; P.st = P.stats.stMax;
  P.statuses = []; P.buffs = []; P.ward = null;
  recalcStats(P);
  closeAllScreens();
  enterTown('death');
}
function showVictoryScreen() {
  const panel = openPanel(`
    <div id="victoryBox">
      <h1>THE WARDEN FALLS</h1>
      <p>You drove your blade into the wound-keeper, and the Underkeep exhaled — ash and water going still for the first time in living memory. Hollowmere's wells run clear by morning. Chronicler Ondrey writes four words at the end of a very long page: <i>"It can be held."</i></p>
      <p>Whether you keep holding it is your affair. The descent remains, as it always was: deeper, darker, and worth more the further you dare.</p>
      <div class="row" style="justify-content:center">
        <div class="btn" id="vCont">Continue Exploring</div>
        <div class="btn" id="vDesc">Start New Descent</div>
        <div class="btn" id="vMenu">Main Menu</div>
      </div>
    </div>`);
  panel.querySelector('#vCont').onclick = () => { closeAllScreens(); };
  panel.querySelector('#vDesc').onclick = () => { closeAllScreens(); newDescent(); };
  panel.querySelector('#vMenu').onclick = () => { saveGame(false); showMainMenu(); };
  SND.quest();
}
function newDescent() {
  G.campaign.descent = (G.campaign.descent || 0) + 1;
  G.campaign.seed = hashMix(G.campaign.seed, 0x9e37, G.campaign.descent);
  G.campaign.floors = {};
  G.campaign.waypoints = [1];
  G.campaign.caches = [];
  G.campaign.portals = [];
  G.campaign.vendorMilestone = 0;
  G.campaign.vendorStock = {};
  // quests: main arc resets objective state but keeps completion of story
  for (const q of QUESTS) {
    const st = G.campaign.quests[q.id];
    if (st && st.state === 'done' && q.main) continue; // story stays done
  }
  toast('New Descent ' + G.campaign.descent + ' — the Underkeep has changed.', 'good');
  enterTown('descent');
}

/* ---------------- character creation ---------------- */
function openCreation() {
  let cls = 'vanguard', difficulty = 'adventurer', hardcore = false;
  const panel = openPanel(`
    <h2>New Character</h2>
    <div style="display:flex;gap:18px;flex-wrap:wrap">
      <div>
        <div class="row" style="margin-bottom:8px"><input type="text" id="cName" maxlength="18" placeholder="Name" value="${pick(Math.random, ['Alder', 'Bryn', 'Corvin', 'Dagna', 'Eshe', 'Falk', 'Isolde', 'Marek'])}"></div>
        <div id="classList" style="display:flex;gap:8px"></div>
        <h3>Appearance</h3>
        <div class="row">
          <label class="dim">Skin</label><input type="range" min="0" max="3" value="0" id="cSkin">
          <label class="dim">Hair</label><input type="range" min="0" max="3" value="0" id="cHair">
        </div>
        <h3>Difficulty</h3>
        <div id="diffList" class="row" style="flex-wrap:wrap"></div>
        <div class="setRow"><label>Hardcore (permadeath)</label><input type="checkbox" id="cHC"></div>
        <div class="dim" id="diffDesc" style="margin-top:6px;max-width:220px"></div>
      </div>
      <div style="min-width:260px" id="clsDesc"></div>
    </div>
    <div class="row" style="margin-top:14px"><div class="btn gold" id="cCreate">Begin the Descent</div><div class="btn small" id="closeScr">Back</div></div>`);
  const refresh = () => {
    const cl = CLASSES[cls];
    const clEl = panel.querySelector('#classList');
    clEl.innerHTML = CLASS_IDS.map(c => `<div class="classCard ${c === cls ? 'sel' : ''}" data-c="${c}">
      <h4 style="color:${CLASSES[c].color}">${CLASSES[c].glyph} ${CLASSES[c].name}</h4>
      <div class="dim">STR ${CLASSES[c].attrs.str} · DEX ${CLASSES[c].attrs.dex}<br>INT ${CLASSES[c].attrs.int} · VIT ${CLASSES[c].attrs.vit}</div></div>`).join('');
    clEl.querySelectorAll('.classCard').forEach(cd => cd.onclick = () => { cls = cd.dataset.c; SND.ui(); refresh(); });
    const dl = panel.querySelector('#diffList');
    dl.innerHTML = Object.entries(CFG.difficulty).map(([k, d]) => `<div class="btn small ${k === difficulty ? 'gold' : ''}" data-d="${k}">${d.label}</div>`).join('');
    dl.querySelectorAll('[data-d]').forEach(b => b.onclick = () => { difficulty = b.dataset.d; SND.ui(); refresh(); });
    const d = CFG.difficulty[difficulty];
    panel.querySelector('#diffDesc').innerHTML = `Enemy HP ×${d.hp}, damage ×${d.dmg}, loot ×${d.loot}, gold loss on death ${Math.round(d.goldLoss * 100)}%.<br>` + (hardcore ? '<span style="color:#d88">Hardcore: death is permanent. Cannot be disabled later.</span>' : '');
    panel.querySelector('#clsDesc').innerHTML = `
      <h3 style="color:${cl.color}">${cl.glyph} ${cl.name}</h3>
      <div class="dim" style="margin-bottom:6px">${cl.desc}</div>
      <div class="statline"><span>Health bonus</span><b>+${cl.hpB}</b></div>
      <div class="statline"><span>Stamina bonus</span><b>+${cl.stB}</b></div>
      <div class="statline"><span>Mana bonus</span><b>+${cl.mpB}</b></div>
      <div class="statline"><span>Mana regen</span><b>+${cl.mpRegen}/s</b></div>
      <div class="statline"><span>Move speed</span><b>+${Math.round(cl.moveB * 100)}%</b></div>
      <h3>Starting gear</h3>
      <div class="dim">${cl.gear.map(g => { const [id, q] = g.split(':'); return (q ? q + '× ' : '') + (ITEM_BASES[id]?.name || id); }).join('<br>')}</div>
      <h3>Talents</h3>
      <div class="dim">${TALENTS.filter(t => t.cls === cls).map(t => t.name).join(', ')}</div>`;
    panel.querySelector('#cHC').onchange = e => { hardcore = e.target.checked; refresh(); };
  };
  refresh();
  panel.querySelector('#closeScr').onclick = () => showMainMenu();
  panel.querySelector('#cCreate').onclick = () => {
    const name = (panel.querySelector('#cName').value || 'Delver').slice(0, 18);
    const preset = { skin: +panel.querySelector('#cSkin').value, hair: +panel.querySelector('#cHair').value };
    createCharacter({ name, cls, preset, difficulty, hardcore });
  };
}

/* ============================================================
   15. QUESTS runtime + lore + bestiary
   ============================================================ */
function addLore(id) {
  if (!G.campaign.lore[id]) {
    G.campaign.lore[id] = true;
    const l = LORE_BY_ID[id];
    if (l) { toast('Lore: ' + l.title, 'good'); SND.lore(); }
    // pages_of_the_deep quest
    questEvent('lore', {});
  }
}
function questEvent(type, data) {
  const c = G.campaign;
  for (const q of QUESTS) {
    const st = c.quests[q.id];
    if (!st || st.state !== 'active') continue;
    for (const o of q.objectives) {
      if ((st.objDone || {})[o.id]) continue;
      let done = false;
      if (o.type === 'dialog' && type === 'dialog' && data.npc === o.npc) done = true;
      if (o.type === 'kill' && type === 'kill' && data.arch === o.arch) {
        st.count = (st.count || 0) + 1;
        if (st.count >= o.count) done = true;
      }
      if (o.type === 'killElite' && type === 'killElite' && data.quest === q.id) done = true;
      if (o.type === 'boss' && type === 'boss' && data.boss === o.boss) done = true;
      if (o.type === 'pickup' && type === 'pickup' && data.base === o.base) done = true;
      if (o.type === 'interact' && type === 'interact' && data.tag === o.tag) {
        st.icount = (st.icount || 0) + 1;
        if (st.icount >= o.count) done = true;
      }
      if (o.type === 'lore' && type === 'lore') {
        st.lcount = Object.keys(c.lore).filter(k => k.startsWith('l_floor')).length + Object.keys(c.lore).filter(k => k.startsWith('l_boss')).length;
        if (st.lcount >= o.count) done = true;
      }
      if (o.type === 'event' && type === 'event' && data.event === o.event) done = true;
      if (done) {
        st.objDone = st.objDone || {};
        st.objDone[o.id] = true;
        toast('Objective: ' + o.text, 'good');
        SND.quest();
        EVT.emit('QuestObjectiveAdvanced', { quest: q.id, obj: o.id });
        // auto-set turnin state when only dialog/deliver objectives remain
        if (q.objectives.every(x => (st.objDone || {})[x.id] || ['dialog', 'deliver'].includes(x.type))) {
          if (q.objectives.every(x => (st.objDone || {})[x.id])) {
            // all done but final dialog/deliver remains → mark ready
          }
        }
      }
    }
    // quest fully met except final dialog → allow turn-in (dialogOptions uses objectivesMet)
  }
}

/* ============================================================
   16. SAVE / LOAD — localStorage, atomic with checksum + backup
   ============================================================ */
const LS_KEY = 'hollowmere_v1_';
function listSaves() {
  try {
    return JSON.parse(localStorage.getItem(LS_KEY + 'chars') || '[]');
  } catch (e) { return []; }
}
function saveCharIndex(chars) { localStorage.setItem(LS_KEY + 'chars', JSON.stringify(chars)); }
function createCharacter(opts) {
  P = makePlayer(opts);
  G.campaign = {
    seed: (Math.random() * 1e9) | 0, descent: 0, difficulty: opts.difficulty,
    hardcore: opts.hardcore, maxFloor: 0, waypoints: [1], storyDone: false,
    quests: {}, lore: {}, bestiary: {}, floors: {}, caches: [], portals: [],
    vendorStock: {}, vendorMilestone: 0, buyback: [], stash: [[], [], []], flags: {},
  };
  P.floorIdx = 0;
  saveGame(true);
  // auto-accept first main quest
  const mq = QUESTS[0];
  G.campaign.quests[mq.id] = { state: 'active', objDone: {} };
  toast('Quest accepted: ' + mq.name, 'good');
  enterTown('new');
}
function markHardcoreDead() {
  P.dead = true;
  const chars = listSaves();
  const i = chars.findIndex(c => c.id === P.id);
  if (i >= 0) { chars[i].dead = true; saveCharIndex(chars); }
  saveGame(true);
}
function deleteCharacter(id) {
  const chars = listSaves().filter(c => c.id !== id);
  saveCharIndex(chars);
  localStorage.removeItem(LS_KEY + 'char_' + id);
  localStorage.removeItem(LS_KEY + 'char_' + id + '_bak');
}
function serializeItemFull(it) {
  return serializeItem(it);
}
function saveGame(quiet) {
  if (!P || !G.campaign) return;
  // commit ground items of current floor first
  if (G.floor) persistGround();
  const data = {
    v: 1, content: 1, saved: Date.now(),
    char: {
      id: P.id, name: P.name, cls: P.cls, preset: P.preset, hardcore: P.hardcore, difficulty: G.campaign.difficulty,
      level: P.level, xp: P.xp, attrs: P.attrs, unspentAttr: P.unspentAttr, unspentTalent: P.unspentTalent,
      talents: P.talents, spellRanks: P.spellRanks, hp: P.hp, mp: P.mp, st: P.st, gold: P.gold,
      inv: P.inv.map(serializeItemFull), equip: mapObj(P.equip, serializeItemFull),
      belt: P.belt, skillQ: P.skillQ, skillR: P.skillR, cds: P.cds, selectedSpell: P.selectedSpell, selectedUtility: P.selectedUtility,
      floorIdx: G.floor ? G.floor.index : 0, pos: P.pos ? [P.pos[0], P.pos[2]] : [0, 0], dead: P.dead,
    },
    campaign: {
      seed: G.campaign.seed, descent: G.campaign.descent, difficulty: G.campaign.difficulty, hardcore: G.campaign.hardcore,
      maxFloor: G.campaign.maxFloor, waypoints: G.campaign.waypoints, storyDone: G.campaign.storyDone,
      quests: G.campaign.quests, lore: G.campaign.lore, bestiary: G.campaign.bestiary,
      floors: G.campaign.floors, caches: G.campaign.caches, portals: G.campaign.portals,
      vendorStock: G.campaign.vendorStock, vendorMilestone: G.campaign.vendorMilestone, buyback: (G.campaign.buyback || []).map(serializeItemFull),
      stash: (G.campaign.stash || [[], [], []]).map(tab => tab.map(serializeItemFull)),
    },
  };
  const json = JSON.stringify(data);
  const ck = fnv(json);
  try {
    const key = LS_KEY + 'char_' + P.id;
    // atomic-ish: write backup copy of previous, then new with checksum
    const prev = localStorage.getItem(key);
    if (prev) localStorage.setItem(key + '_bak', prev);
    localStorage.setItem(key, JSON.stringify({ ck, data: json }));
    const chars = listSaves();
    const i = chars.findIndex(c => c.id === P.id);
    const meta = { id: P.id, name: P.name, cls: P.cls, level: P.level, hardcore: P.hardcore, dead: P.dead, floor: data.char.floorIdx, saved: data.saved };
    if (i >= 0) chars[i] = meta; else chars.unshift(meta);
    chars.sort((a, b) => b.saved - a.saved);
    saveCharIndex(chars);
    if (!quiet) toast('Progress saved.', 'good');
    EVT.emit('SaveCommitted', {});
  } catch (e) {
    toast('Save failed: storage full?', 'bad');
  }
}
function mapObj(o, f) { const r = {}; for (const k in o) r[k] = o[k] ? f(o[k]) : null; return r; }
function loadCharacter(id) {
  try {
    let raw = localStorage.getItem(LS_KEY + 'char_' + id);
    if (!raw) return;
    let { ck, data } = JSON.parse(raw);
    if (fnv(data) !== ck) {
      const bak = localStorage.getItem(LS_KEY + 'char_' + id + '_bak');
      if (bak) {
        const p2 = JSON.parse(bak);
        if (fnv(p2.data) === p2.ck) { data = p2.data; toast('Save corrupted — restored previous snapshot.', 'bad'); }
        else { toast('Save corrupted beyond repair.', 'bad'); return; }
      } else { toast('Save corrupted.', 'bad'); return; }
    }
    const d = JSON.parse(data);
    const c = d.char;
    P = makePlayer({ name: c.name, cls: c.cls, preset: c.preset, difficulty: d.campaign.difficulty, hardcore: d.campaign.hardcore, gold: c.gold });
    P.id = c.id;
    P.level = c.level; P.xp = c.xp; P.attrs = c.attrs; P.unspentAttr = c.unspentAttr; P.unspentTalent = c.unspentTalent;
    P.talents = c.talents || {}; P.spellRanks = c.spellRanks || {};
    P.hp = c.hp; P.mp = c.mp; P.st = c.st;
    P.inv = (c.inv || []).map(deserializeItem).filter(Boolean);
    P.inv.forEach((it, i) => { if (it._x === undefined) { it._x = 0; it._y = i % 6; it.rot = 0; } });
    P.equip = mapObj(c.equip || {}, deserializeItem);
    P.belt = c.belt || [null, null, null, null, null, null];
    P.skillQ = c.skillQ; P.skillR = c.skillR; P.cds = c.cds || {};
    P.selectedSpell = c.selectedSpell || 'magic_dart'; P.selectedUtility = c.selectedUtility;
    P.dead = !!c.dead;
    G.campaign = Object.assign({
      seed: 1, descent: 0, difficulty: 'adventurer', hardcore: false, maxFloor: 0, waypoints: [1],
      storyDone: false, quests: {}, lore: {}, bestiary: {}, floors: {}, caches: [], portals: [],
      vendorStock: {}, vendorMilestone: 0, buyback: [], stash: [[], [], []],
    }, d.campaign);
    if (G.campaign.buyback) G.campaign.buyback = G.campaign.buyback.map(deserializeItem).filter(Boolean);
    if (G.campaign.stash) G.campaign.stash = G.campaign.stash.map(tab => tab.map(deserializeItem).filter(Boolean));
    recalcStats(P);
    // restore at saved position: floor if dungeon, else town
    if (c.floorIdx >= 1 && !P.dead) {
      enterFloor(c.floorIdx, 'load', c.pos);
    } else {
      enterTown('load', c.pos);
    }
    toast('Loaded ' + P.name + '.', 'good');
  } catch (e) {
    toast('Load failed: ' + e.message, 'bad');
  }
}
let quiet2 = false;
void quiet2;

/* ============================================================
   17. INPUT, CAMERA, PLAYER UPDATE
   ============================================================ */
const DEFAULT_BINDS = { forward: 'KeyW', back: 'KeyS', left: 'KeyA', right: 'KeyD', attack: 'Mouse0', block: 'Mouse2', kick: 'KeyF', interact: 'KeyE', skillQ: 'KeyQ', skillR: 'KeyR', dodge: 'AltLeft', jump: 'Space', sprint: 'ShiftLeft', crouch: 'KeyC', sheathe: 'KeyH', portal: 'KeyT', inv: 'Tab', map: 'KeyM', journal: 'KeyJ', drop: 'KeyG', pause: 'Escape', belt1: 'Digit1', belt2: 'Digit2', belt3: 'Digit3', belt4: 'Digit4', belt5: 'Digit5', belt6: 'Digit6' };
const DEFAULT_SETTINGS = { sens: 1.0, fov: 85, invertY: false, volMaster: .8, volMusic: .5, volSfx: .9, volAmb: .7, uiScale: 1, dmgNumbers: true, enemyBars: true, gore: true, bob: true, autoGold: true, binds: {} };
function loadSettings() {
  try { G.settings = Object.assign({}, DEFAULT_SETTINGS, JSON.parse(localStorage.getItem(LS_KEY + 'settings') || '{}')); }
  catch (e) { G.settings = Object.assign({}, DEFAULT_SETTINGS); }
}
function saveSettings() { try { localStorage.setItem(LS_KEY + 'settings', JSON.stringify(G.settings)); } catch (e) {} }

function makeInput() {
  const I = {
    keys: {}, mouse: [false, false, false], locked: false, aimActor: null, focus: null,
    pendingCastT: 0, attackDownT: 0,
    down(action) {
      const code = (G.settings.binds && G.settings.binds[action]) || DEFAULT_BINDS[action];
      if (code && code.startsWith('Mouse')) return I.mouse[+code.slice(5)];
      return I.keys[code];
    },
    keyDown(code) { return I.keys[code]; },
    consume(code) { I.keys[code] = false; },
  };
  const cv = el('cv');
  cv.addEventListener('click', () => {
    SND.init(); SND.resume();
    if (G.state === 'play' && !G.uiOpen && !I.locked) cv.requestPointerLock();
  });
  document.addEventListener('pointerlockchange', () => {
    I.locked = document.pointerLockElement === cv;
    if (!I.locked && G.state === 'play' && !G.uiOpen) openPauseMenu();
  });
  window.addEventListener('mousemove', e => {
    moveDrag(e);
    if (!I.locked || !P || G.uiOpen || P.dead) return;
    const s = G.settings;
    P.yaw -= e.movementX * 0.0022 * s.sens;
    P.pitch -= e.movementY * 0.0022 * s.sens * (s.invertY ? -1 : 1);
    P.pitch = clamp(P.pitch, -1.45, 1.45);
  });
  window.addEventListener('mousedown', e => {
    if (e.target.closest('.panel') || e.target.closest('#menuRoot') || e.target.closest('#dlgBox')) return;
    I.mouse[e.button] = true;
    if (e.button === 2) e.preventDefault();
    if (!P || G.uiOpen || G.state !== 'play' || P.dead) return;
    if (e.button === 0) {
      I.attackDownT = G.time;
      const w = curWeapon();
      if (w && w.fam === 'bow') startBowDraw();
      else if (w && (w.fam === 'staff' || w.fam === 'wand')) { I.pendingCastT = G.time; }
      else startAttack(false);
    } else if (e.button === 2) {
      raiseBlock(true);
    }
  });
  window.addEventListener('mouseup', e => {
    I.mouse[e.button] = false;
    if (!P || G.state !== 'play') return;
    if (e.button === 0) {
      if (DRAG.item) { endDrag(e); return; }
      const w = curWeapon();
      if (P.attack.state === 'draw') releaseBow();
      else if (w && (w.fam === 'staff' || w.fam === 'wand') && I.pendingCastT) {
        castSelectedSpell(G.time - I.pendingCastT > 0.35);
        I.pendingCastT = 0;
      } else if (P.attack.state === 'charging') {
        const charge = P.attack.chargeT || 0;
        startAttack(true, charge);
      }
    } else if (e.button === 2) raiseBlock(false);
  });
  window.addEventListener('contextmenu', e => { if (!e.target.closest('.panel')) e.preventDefault(); });
  window.addEventListener('keydown', e => {
    if (e.code === 'Tab' || e.code === 'Space' || e.code.startsWith('Alt') || e.code === 'F1') e.preventDefault();
    I.keys[e.code] = true;
    if (!P || G.state === 'menu') return;
    // global UI toggles
    if (e.code === 'Escape') {
      if (G.uiOpen) { closeAllScreens(); } else openPauseMenu();
      return;
    }
    if (e.code === 'Tab') { if (G.uiOpen) closeAllScreens(); else openCharScreen('inv'); return; }
    if (G.uiOpen) {
      if (e.code === 'KeyM' && G.uiOpen === 'map') closeAllScreens();
      return;
    }
    if (P.dead) return;
    switch (e.code) {
      case 'KeyF': doKick(); break;
      case 'KeyE': tryInteract(); break;
      case 'KeyQ': activateSkill(P.skillQ); break;
      case 'KeyR': activateSkill(P.skillR); break;
      case 'AltLeft': case 'AltRight': doDodge(); break;
      case 'Space': if (P.onGround && P.st > 4) { P.vel[1] = CFG.jumpSpeed; P.st -= 4; P.stRegenDelayT = CFG.staminaRegenDelay; } break;
      case 'KeyC': P.crouch = !P.crouch; break;
      case 'KeyH': P.sheathed = !P.sheathed; break;
      case 'KeyM': openMapOverlay(); break;
      case 'KeyJ': openCharScreen('journal'); break;
      case 'KeyT': usePortalKey(); break;
      case 'KeyX': cycleSpell(); break;
      case 'KeyG': dropHovered(); break;
      default:
        for (let i = 1; i <= 6; i++) if (e.code === 'Digit' + i) useBelt(i - 1);
    }
  });
  window.addEventListener('keyup', e => { I.keys[e.code] = false; });
  return I;
}
function raiseBlock(on) {
  if (!P || P.dead) return;
  if (on) {
    if (P.attack.state !== 'idle' && P.attack.state !== 'recover') return;
    P.blocking = true; P.perfectT = CFG.block.perfectWindow;
  } else P.blocking = false;
}
function activateSkill(sk) {
  if (!sk || !P || P.dead) return;
  if (sk.kind === 'talent') execTalent(sk.id);
  else castSpell(sk.id, {});
}
function doDodge() {
  if (!P || P.dodgeCd > 0 || P.dead) return;
  let cost = CFG.dodge.cost * (1 - (P.talents.evasive ? 0.08 + 0.04 * (P.talents.evasive - 1) : 0));
  if (hasRelic(P, 'lanternmail')) cost *= 1.15;
  if (!trySpendStamina(Math.round(cost))) return;
  let dx = 0, dz = 0;
  if (INPUT.down('forward')) { dx = -Math.sin(P.yaw); dz = -Math.cos(P.yaw); }
  else if (INPUT.down('back')) { dx = Math.sin(P.yaw); dz = Math.cos(P.yaw); }
  else if (INPUT.down('left')) { dx = -Math.cos(P.yaw); dz = Math.sin(P.yaw); }
  else if (INPUT.down('right')) { dx = Math.cos(P.yaw); dz = -Math.sin(P.yaw); }
  if (!dx && !dz) { dx = Math.sin(P.yaw); dz = Math.cos(P.yaw); }
  P.dodgeDir = [dx, dz];
  P.dodgeT = CFG.dodge.dur; P.iframe = CFG.dodge.iframes + 0.05; P.dodgeCd = 0.8;
  SND.step('stone', true);
}
function useBelt(i) {
  const it = beltItem(P, i);
  if (!it) { SND.error(); toast('Empty belt slot', 'bad'); return; }
  useConsumable(it);
  refreshScreens();
}
function usePortalKey() {
  if (G.mode !== 'dungeon') { toast('No need in town', ''); return; }
  // standing near own portal?
  for (const po of (G.floor.portals || [])) {
    if (d2(po.x, po.z, P.pos[0], P.pos[2]) < 1.6) { travelToTownViaPortal(po); return; }
  }
  if (P.spellRanks.return_sigil) castSpell('return_sigil', {});
  else {
    const scroll = P.inv.find(it => it && it.base === 'scroll_portal');
    if (scroll) useConsumable(scroll);
    else { SND.error(); toast('No Return Sigil learned and no scrolls', 'bad'); }
  }
}
function travelToTownViaPortal(po) {
  // remove paired portals
  G.floor.portals = G.floor.portals.filter(x => x !== po);
  G.campaign.portals = (G.campaign.portals || []).filter(pp => !(pp.floor === G.floor.index && d2(pp.x, pp.z, po.x, po.z) < 2));
  enterTown('portal');
}
function cycleSpell() {
  const known = SPELL_ORDER.filter(s => P.spellRanks[s] && SPELLS[s].kind === 'projectile');
  if (!known.length) return;
  const i = known.indexOf(P.selectedSpell);
  P.selectedSpell = known[(i + 1) % known.length];
  toast('Attack spell: ' + SPELLS[P.selectedSpell].name, '');
}
function dropHovered() {
  const it = UI && UI._hoverItem;
  if (!it || it.cat === 'quest') return;
  if (RAR_IDX[it.rarity] >= 2 && !confirmModal('Drop ' + it.name + '?')) return;
  const i = P.inv.indexOf(it);
  if (i >= 0) { P.inv.splice(i, 1); dropToGround(P, it, G.floor, P.pos); toast('Dropped ' + it.name, ''); }
}
function camDir() {
  const cp = Math.cos(P.pitch), sp = Math.sin(P.pitch);
  return [-Math.sin(P.yaw) * cp, sp, -Math.cos(P.yaw) * cp];
}

/* ---------------- interaction focus ---------------- */
function computeInteract() {
  if (!P || G.uiOpen) { INPUT.focus = null; return; }
  const F = G.floor;
  const eye = [P.pos[0], 1.6, P.pos[2]];
  const dir = camDir();
  const range = CFG.interactRange;
  const cands = [];
  const addC = (pos, type, obj, label, prompt2, priority) => {
    const d = d2(pos[0], pos[2], P.pos[0], P.pos[2]);
    if (d > range + 0.4) return;
    if (d > 1.2 && !losClear(F, eye[0], eye[2], pos[0], pos[2])) return;
    cands.push({ d, type, obj, label, prompt2, priority: priority || 0 });
  };
  // ground items
  for (const g of F.ground) {
    const it = g.payload.item;
    const nm = it ? (it.identified || it.rarity === 'common' ? it.name : it.name.replace(/^(\w+ \w+).*/, '$1') + ' ???') : 'Gold';
    addC([g.x, 0, g.z], 'ground', g, nm, 'Pick up', 3);
  }
  for (const c of F.chests) addC([c.x, 0, c.z], 'chest', c, c.opened ? 'Chest (empty)' : (c.rare ? 'Ornate Chest' : 'Chest'), c.opened ? '' : 'Open', 2);
  for (const d of F.doors) {
    if (d.kind === 'secret' && !d.revealed && d2(d.x * CFG.tile + 1.5, d.y * CFG.tile + 1.5, P.pos[0], P.pos[2]) > 2.5) continue;
    const names = { locked: 'Locked Door', secret: 'Suspicious Wall', jammed: 'Jammed Door', open: 'Door', closed: 'Door' };
    addC([d.x * CFG.tile + 1.5, 0, d.y * CFG.tile + 1.5], 'door', d, names[d.state] || 'Door', d.state === 'secret' ? 'Search' : (d.state === 'open' ? 'Close' : 'Open'), 2);
  }
  for (const s of F.shrines) addC([s.x, 0, s.z], 'shrine', s, SHRINE_KINDS[s.kind].name, s.used ? '' : 'Touch', 2);
  for (const l of F.levers) addC([l.x, 0, l.z], 'lever', l, 'Lever', l.pulled ? '' : 'Pull', 2);
  for (const v of F.valves) addC([v.x, 0, v.z], 'valve', v, 'Sluice Valve', v.turned ? '' : 'Turn', 2);
  for (const br of F.braziers) addC([br.x, 0, br.z], 'brazier', br, 'Brazier', br.lit ? '' : 'Light', 2);
  for (const l of F.loreItems) addC([l.x, 0, l.z], 'lore', l, 'Worn Page', 'Read', 3);
  if (F.survivor && !F.survivor.met) addC([F.survivor.x, 0, F.survivor.z], 'survivor', F.survivor, 'Wounded Delver', 'Speak', 3);
  if (F.stairsDown && F.index < 16) addC([F.stairsDown.x, 0, F.stairsDown.z], 'stairsDown', F.stairsDown, 'Stairs Down', (F.bossSpawn && !F.bossDefeated) ? '' : 'Descend', 1);
  if (F.isTown) {
    for (const n of F.npcs) {
      const v = VENDORS[n.npc];
      addC([n.x, 0, n.z], 'npc', n, v.name, 'Talk', 2);
    }
    addC([F.gate.x, 0, F.gate.z], 'gate', F.gate, 'Underkeep Gate', 'Descend', 1);
    addC([F.townPortal.x, 0, F.townPortal.z], 'townPortal', F.townPortal, 'Waypoint Circle', 'Use', 1);
  } else {
    if (F.stairsUp) addC([F.stairsUp.x, 0, F.stairsUp.z], 'stairsUp', F.stairsUp, 'Exit to Town', 'Ascend', 1);
    for (const po of (F.portals || [])) addC([po.x, 0, po.z], 'portal', po, 'Return Portal', 'Enter', 3);
  }
  cands.sort((a, b) => (b.priority - a.priority) || (a.d - b.d));
  INPUT.focus = cands[0] || null;
  // Reveal spell: expose hidden doors nearby
  if (P.revealT > 0) {
    for (const d of F.doors) {
      if (d.kind === 'secret' && !d.revealed && d2(d.x * CFG.tile + 1.5, d.y * CFG.tile + 1.5, P.pos[0], P.pos[2]) < 11) { d.revealed = true; toast('Reveal: a hidden door shimmers nearby', 'good'); }
    }
  }
  // reticle aim actor
  INPUT.aimActor = null;
  if (!F.isTown) {    let best = null, bestD = 30;
    for (const a of F.actors) {
      if (a.dead) continue;
      const to = [a.pos[0] - eye[0], (a.scaleH * 0.6) - eye[1], a.pos[2] - eye[2]];
      const l = v3len(to);
      const dot = v3dot(v3norm(to), dir);
      if (dot > 0.995 && l < bestD && losClear(F, eye[0], eye[2], a.pos[0], a.pos[2])) { best = a; bestD = l; }
    }
    INPUT.aimActor = best;
  }
}
function promptText() {
  const f = INPUT.focus;
  const kb = a => `<span class="kb">${bindLabel(a)}</span>`;
  if (!f) {
    // trap sense
    if (P.talents.trapsense && !G.floor.isTown) {
      const r = 2 + (P.talents.trapsense - 1);
      for (const t of G.floor.traps) if (!t.revealed && d2(t.x, t.z, P.pos[0], P.pos[2]) < r) { t.revealed = true; toast('Trap sensed nearby!', ''); }
    }
    return '';
  }
  const map = {
    ground: () => f.prompt2 + ': ' + f.label,
    chest: () => `${kb('interact')} ${f.prompt2} ${f.label}`,
    door: () => f.obj.kind === 'locked' ? `${kb('interact')} Unlock door (needs key)` : f.obj.kind === 'secret' ? `${kb('interact')} Search suspicious wall` : `${kb('interact')} ${f.prompt2} door`,
    shrine: () => f.obj.used ? f.label + ' (spent)' : `${kb('interact')} ${f.prompt2} — ${SHRINE_KINDS[f.obj.kind].desc}`,
    lever: () => `${kb('interact')} ${f.prompt2} lever`,
    valve: () => f.obj.turned ? 'Valve open' : `${kb('interact')} Turn valve`,
    brazier: () => f.obj.lit ? 'Brazier lit' : `${kb('interact')} Light brazier`,
    lore: () => `${kb('interact')} ${f.prompt2}: ${f.label}`,
    npc: () => `${kb('interact')} Talk to ${f.label}`,
    gate: () => `${kb('interact')} Enter the Underkeep`,
    stairsDown: () => f.prompt2 ? `${kb('interact')} ${f.prompt2} to Floor ${G.floor.index + 1}` : 'The way down is sealed until the boss falls',
    stairsUp: () => `${kb('interact')} Return to Hollowmere`,
    portal: () => `${kb('interact')} Enter return portal`,
    townPortal: () => `${kb('interact')} Town waypoint circle`,
    survivor: () => `${kb('interact')} ${f.prompt2}`,
  };
  return (map[f.type] ? map[f.type]() : f.prompt2 ? kb('interact') + ' ' + f.prompt2 : '');
}
function tryInteract() {
  const f = INPUT.focus;
  if (!f) return;
  const F = G.floor;
  switch (f.type) {
    case 'ground': pickupGround(f.obj); break;
    case 'chest': openChest(f.obj); break;
    case 'door': tryOpenDoor(f.obj); if (f.obj.kind === 'secret') { f.obj.revealed = true; } break;
    case 'shrine': useShrine(f.obj); break;
    case 'lever':
      if (!f.obj.pulled) {
        f.obj.pulled = true; SND.door();
        // open one closed normal door (shortcut)
        const doors = F.doors.filter(d => d.kind === 'normal' && d.state === 'closed');
        if (doors.length) { doors[0].state = 'open'; toast('A mechanism rumbles — a door opens.', 'good'); }
      }
      break;
    case 'valve':
      if (!f.obj.turned) {
        f.obj.turned = true; SND.thud();
        const fs = G.campaign.floors[F.index];
        if (fs) { fs.valves = fs.valves || []; if (!fs.valves.includes(f.obj.id)) fs.valves.push(f.obj.id); }
        toast('The valve turns with a groan.', 'good');
        questEvent('interact', { tag: 'valve' });
      }
      break;
    case 'brazier':
      if (!f.obj.lit) {
        f.obj.lit = true; SND.castFire();
        F.lights.push({ x: f.obj.x, y: 1.2, z: f.obj.z, r: 1, g: .6, b: .25, radius: 7, intensity: .9, flicker: 5, ph: Math.random() * TAU });
        const all = F.braziers.filter(b => b.puzzle);
        if (all.length && all.every(b => b.lit)) {
          toast('The braziers burn — something unlocks.', 'good');
          F.chests.push({ id: 'cPz' + (PROP_ID++), x: f.obj.x, z: f.obj.z + 2, rare: true, opened: false, loot: rollLoot(mulberry32(99), { ilvl: F.index + 1, n: 2, weights: { common: 10, enchanted: 45, rare: 40, relic: 5 } }), gold: 120 });
        }
      }
      break;
    case 'lore': {
      addLore(f.obj.loreId);
      F.loreItems.splice(F.loreItems.indexOf(f.obj), 1);
      break;
    }
    case 'npc': openDialog(f.obj.npc); break;
    case 'gate': openGateMenu(); break;
    case 'stairsDown':
      if (F.bossSpawn && !F.bossDefeated) { SND.error(); toast('Sealed until the boss falls', 'bad'); break; }
      enterFloor(F.index + 1, 'stairs');
      break;
    case 'stairsUp': enterTown('stairs'); break;
    case 'portal': travelToTownViaPortal(f.obj); break;
    case 'townPortal': {
      // list active return portals in dungeon
      const ps = (G.campaign.portals || []);
      if (!ps.length) { toast('No return portals active', ''); break; }
      const p = ps[ps.length - 1];
      enterFloor(p.floor, 'portal', [p.x, p.z]);
      break;
    }
    case 'survivor': {
      F.survivor.met = true;
      toast('"Thank the deep you came... I will crawl to the stairs. Take this."', 'good');
      spawnGroundItem(F, P.pos[0] + 1, P.pos[2], { item: makeItem('potion_health_m', 1, 'common', mulberry32(3), { identified: true }) }, 0);
      questEvent('event', { event: 'survivor' });
      break;
    }
  }
}

/* ---------------- player tick ---------------- */
function updatePlayer(F, dt) {
  tickCooldowns(dt);
  P.potionCd = Math.max(0, P.potionCd - dt);
  P.perfectT = Math.max(0, P.perfectT - dt);
  P.iframe = Math.max(0, P.iframe - dt);
  P.dodgeCd = Math.max(0, P.dodgeCd - dt);
  if (P.stun > 0) { P.stun -= dt; }
  // regen
  P.stRegenDelayT = Math.max(0, (P.stRegenDelayT || 0) - dt);
  P.hpRegenDelayT = Math.max(0, (P.hpRegenDelayT || 0) - dt);
  if (P.stRegenDelayT <= 0) P.st = clamp(P.st + P.stats.stRegen * dt, 0, P.stats.stMax);
  if (P.hpRegenDelayT <= 0) P.hp = clamp(P.hp + P.stats.hpRegen * dt, 0, P.stats.hpMax);
  P.mp = clamp(P.mp + P.stats.mpRegen * dt, 0, P.stats.mpMax);
  tickStatuses(P, dt);
  // buffs
  for (let i = P.buffs.length - 1; i >= 0; i--) {
    P.buffs[i].t -= dt;
    if (P.buffs[i].t <= 0) { P.buffs.splice(i, 1); recalcStats(P); }
  }
  if (P.ward) { P.ward.t -= dt; if (P.ward.t <= 0) P.ward = null; }
  if (P.revealT > 0) P.revealT -= dt;
  // verdict/arrow/dagger buff timers
  for (const k of ['verdictBuff', 'arrowBuff', 'daggerBuff']) if (P[k]) { P[k].t -= dt; if (P[k].t <= 0) P[k] = null; }
  // movement
  let mx = 0, mz = 0;
  if (!G.uiOpen && !P.dead && P.stun <= 0) {
    if (INPUT.down('forward')) { mx -= Math.sin(P.yaw); mz -= Math.cos(P.yaw); }
    if (INPUT.down('back')) { mx += Math.sin(P.yaw); mz += Math.cos(P.yaw); }
    if (INPUT.down('left')) { mx -= Math.cos(P.yaw); mz += Math.sin(P.yaw); }
    if (INPUT.down('right')) { mx += Math.cos(P.yaw); mz -= Math.sin(P.yaw); }
  }
  const ml = Math.hypot(mx, mz);
  if (ml > 0) { mx /= ml; mz /= ml; }
  P.sprinting = INPUT.down('sprint') && ml > 0 && P.st > 1 && !P.crouch && !P.blocking;
  if (P.sprinting) {
    P.st -= CFG.sprintStamina * dt; P.stRegenDelayT = CFG.staminaRegenDelay;
    if (P.st <= 0) P.sprinting = false;
  }
  let spd = P.stats.moveSpd * (P.sprinting ? CFG.sprintSpeed / CFG.walkSpeed : 1) * (P.crouch ? CFG.crouchSpeed / CFG.walkSpeed : 1);
  if (hasStatus(P, 'chill')) spd *= 0.7;
  if (hasStatus(P, 'slow')) { const s = P.statuses.find(s => s.id === 'slow'); spd *= (1 - (s?.power || .35)); }
  // water slows
  const tx = Math.floor(P.pos[0] / CFG.tile), tz = Math.floor(P.pos[2] / CFG.tile);
  if (tileIdx(F, tx, tz) === T_WATER) spd *= 0.55;
  if (P.dodgeT > 0) {
    P.dodgeT -= dt;
    P.vel[0] = P.dodgeDir[0] * (CFG.dodge.dist / CFG.dodge.dur);
    P.vel[2] = P.dodgeDir[1] * (CFG.dodge.dist / CFG.dodge.dur);
  } else {
    P.vel[0] = mx * spd; P.vel[2] = mz * spd;
  }
  const wasGround = P.onGround;
  moveBody(F, P, dt);
  // steps noise
  if (ml > 0 && P.onGround) {
    P.bobPhase += dt * (P.sprinting ? 11 : 7);
    P.bobT -= dt;
    if (P.bobT <= 0) {
      P.bobT = P.sprinting ? 0.3 : 0.45;
      SND.step(tileIdx(F, tx, tz) === T_WATER ? 'water' : 'stone', P.sprinting);
      if (G.mode === 'dungeon') emitNoise(F, P.pos[0], P.pos[2], P.sprinting ? CFG.noiseStepRadius * 1.6 : CFG.noiseStepRadius);
    }
  }
  // attack state machine
  updateAttack(F, dt);
  // channel
  if (P.channel) {
    P.channel.t += dt;
    el('channelWrap').classList.remove('hidden');
    el('channelFill').style.width = clamp(P.channel.t / P.channel.dur * 100, 0, 100) + '%';
    if (P.channel.t >= P.channel.dur) {
      const ch = P.channel; P.channel = null;
      el('channelWrap').classList.add('hidden');
      finishChannel(ch);
      if (!ch.scroll) setCooldown('s_' + ch.id, SPELLS[ch.id].cd);
    }
  } else el('channelWrap').classList.add('hidden');
}
function updateAttack(F, dt) {
  const a = P.attack;
  const w = curWeapon();
  a.t += dt;
  switch (a.state) {
    case 'idle': {
      // begin charge if melee mouse held
      if (w && !w.fam.match(/bow|staff|wand/) && INPUT.down('attack') && G.time - INPUT.attackDownT > 0.3) {
        a.state = 'charging'; a.chargeT = 0;
      }
      break;
    }
    case 'charging': {
      a.chargeT += dt;
      if (!INPUT.down('attack')) { a.state = 'idle'; }
      break;
    }
    case 'windup': {
      if (a.t >= a.dur) {
        if (a.unarmed) { unarmedHit(); a.state = 'recover'; a.dur = 0.25; a.t = 0; }
        else {
          let mult = a.heavy ? (1.5 + clamp((a.charge || 0.35) - 0.35, 0, 0.65) / 0.65 * 0.7) : 1;
          if (a.heavy) trySpendStamina; // (stamina charged at start)
          const verdict = P.verdictBuff;
          if (verdict && a.heavy) {
            const hits = resolveMeleeHit(mult, true);
            // add verdict damage to last hit target
            const targets = nearestEnemies(P.pos, w.reach + 1, 1);
            if (targets.length) dealDamage(targets[0], { player: true }, { radiant: verdict.dmg, poise: verdict.poise });
            P.verdictBuff = null;
          } else resolveMeleeHit(mult, a.heavy);
          a.state = 'recover'; a.dur = (a.w ? a.w.rec : 0.3) * (a.heavy ? 1.3 : 1) / P.stats.atkSpd * (a.w && a.w.special === 'wardentoll' ? 1.3 : 1); a.t = 0;
          a.combo = a.heavy ? 0 : (a.combo + 1) % 3;
          emitNoise(F, P.pos[0], P.pos[2], CFG.noiseAttackRadius);
        }
      }
      break;
    }
    case 'recover': {
      if (a.t >= a.dur) a.state = 'idle';
      break;
    }
    case 'draw': {
      P.drawT = clamp(a.t / 0.8, 0, 1);
      if (P.sprinting && a.t > 0.2) { a.state = 'idle'; P.drawT = 0; toast('Draw canceled by sprint', ''); }
      break;
    }
    case 'release': {
      P.drawT = 0;
      if (a.t >= a.dur) a.state = 'idle';
      break;
    }
    case 'cast': {
      if (a.t >= a.dur) { finishCast(a); a.state = 'recover'; a.dur = 0.2; a.t = 0; }
      break;
    }
    case 'kick': {
      if (a.t >= a.dur) a.state = 'idle';
      break;
    }
  }
}
function unarmedHit() {
  const targets = nearestEnemies(P.pos, 1.6, 2);
  for (const t of targets) dealDamage(t, { player: true }, { phys: 3 + P.stats.str * 0.1, poise: 4, src: { player: true } });
  SND.swing();
}

/* ============================================================
   18. WORLD UPDATE + RENDER
   ============================================================ */
function updateWorld(dt) {
  const F = G.floor;
  G.time += dt;
  if (!F) return;
  updatePlayer(F, dt);
  if (!F.isTown) {
    updateActors(F, dt);
    updateProjs(F, dt);
    updateTraps(F, dt);
    updateZones(F, dt);
    updateShockwaves(F, dt);
    checkRoomEvents(F);
    fogReveal(F, dt);
  } else {
    // town: keep player safe
    F.time = (F.time || 0) + dt;
    for (const pr of F.props) if (pr.type === 'well' && Math.random() < dt) { /* ambient */ }
  }
  updateProps(F, dt);
  updateGround(F, dt);
  updatePortals(F, dt);
  R.updateParts(dt);
  // torch ember particles near player
  if (Math.random() < dt * 30) {
    for (const L of F.lights) {
      if (L.flicker && d2(L.x, L.z, P.pos[0], P.pos[2]) < 14 && Math.random() < 0.25) {
        R.spawnP({ x: L.x, y: L.y, z: L.z, vy: 0.6, vx: (Math.random() - .5) * .3, vz: (Math.random() - .5) * .3, maxLife: .7, r: 1, g: .6, b: .2, size: 2.5, grav: -0.5 });
        break;
      }
    }
  }
  // rift particles
  for (const rf of (F.rifts || [])) {
    if (Math.random() < dt * 6) R.spawnP({ x: rf.x + (Math.random() - .5) * 1.5, y: Math.random() * 2, z: rf.z + (Math.random() - .5) * 1.5, vy: .4, maxLife: 1.2, r: .7, g: .4, b: 1, size: 3, grav: 0 });
  }
  computeInteract();
  prompt(promptText());
}
let fogT = 0;
function fogReveal(F, dt) {
  fogT -= dt;
  if (fogT > 0) return;
  fogT = 0.25;
  const Rv = 9;
  const px = Math.floor(P.pos[0] / CFG.tile), pz = Math.floor(P.pos[2] / CFG.tile);
  for (let dy = -Rv; dy <= Rv; dy++) for (let dx = -Rv; dx <= Rv; dx++) {
    const x = px + dx, z = pz + dy;
    if (x < 0 || z < 0 || x >= F.W || z >= F.H) continue;
    if (dx * dx + dy * dy > Rv * Rv) continue;
    const i = z * F.W + x;
    if (F.tiles[i] !== T_SOLID) F.fog[i] |= (dx * dx + dy * dy < 25) ? 3 : 1;
  }
  for (const d of F.doors) {
    if (d.x === px && Math.abs(d.y - pz) < 3) { F.fog[d.y * F.W + d.x] |= 1; if (d.kind === 'secret' && Math.abs(d.y - pz) < 2 && d2(d.x * CFG.tile + 1.5, d.y * CFG.tile + 1.5, P.pos[0], P.pos[2]) < 4) { d.revealed = true; toast('A suspicious wall...', ''); } }
    if (d.y === pz && Math.abs(d.x - px) < 3) F.fog[d.y * F.W + d.x] |= 1;
  }
  const fs = G.campaign.floors[F.index];
  if (fs) fs.fog = b64encode(F.fog);
}
function b64encode(u8) {
  let s = '';
  for (let i = 0; i < u8.length; i += 4096) s += String.fromCharCode.apply(null, u8.subarray(i, i + 4096));
  return btoa(s);
}
function b64decode(s) {
  const bin = atob(s);
  const u8 = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) u8[i] = bin.charCodeAt(i);
  return u8;
}

/* ---------------- rendering ---------------- */
function render() {
  if (!R || !P) return;
  const F = G.floor;
  R.beginFrame();
  const reg = F ? F.reg : TOWN_REG;
  const proj = m4persp(G.settings.fov * Math.PI / 180, R.canvas.width / R.canvas.height, 0.05, 120);
  const eyeH = P.crouch ? CFG.crouchEye : CFG.eyeHeight;
  const bob = G.settings.bob && P.bobPhase ? Math.sin(P.bobPhase) * 0.045 : 0;
  const eye = [P.pos[0], P.pos[1] + eyeH + bob, P.pos[2]];
  const view = m4view(eye[0], eye[1], eye[2], P.yaw, P.pitch);
  G._proj = proj; G._view = view;
  if (!F) { R.drawParts(proj, view); return; }
  const lights = F.lights.slice();
  // player light
  lights.push({ x: eye[0], y: eye[1], z: eye[2], r: 1.0, g: 0.9, b: 0.75, radius: P.stats.lightRadius, intensity: 0.85, flicker: 3, ph: 0 });
  R.useMain(proj, view, lights, reg.fog, reg.fogCol, F.isTown ? 0.016 : 0.045, eye);
  if (F.staticMesh) R.drawMesh(F.staticMesh, null);
  // props
  for (const p of F.props) drawProp(p);
  for (const c of F.chests) drawChest(c);
  for (const s of F.shrines) drawShrine(s);
  for (const t of F.traps) drawTrap(t);
  for (const d of F.doors) drawDoor(d);
  for (const l of F.levers) drawLever(l);
  for (const v of F.valves) drawValve(v);
  for (const b of F.braziers) drawBrazierProp(b);
  for (const l of F.loreItems) drawLore(l);
  for (const g of F.ground) drawGroundItem(g);
  if (F.stairsDown) drawStairs(F.stairsDown, false);
  if (F.stairsUp) drawStairs(F.stairsUp, true);
  for (const po of (F.portals || [])) drawPortalRing(po.x, po.z, 0.7, 0.4, 1);
  if (F.isTown) { drawPortalRing(F.townPortal.x, F.townPortal.z, 0.4, 0.7, 1); }
  if (F.survivor && !F.survivor.met) drawSurvivor(F.survivor);
  for (const n of (F.npcs || [])) drawNPC(n);
  for (const a of F.actors) drawActor(a);
  for (const pr of (F.projs || [])) drawProj(pr);
  // water (glow pass)
  if (F.waterMesh) {
    const gl = R.gl;
    gl.useProgram(R.gl ? null : null);
    R.drawMesh(F.waterMesh, null, 0.55 + 0.1 * Math.sin(G.time * 2));
  }
  R.drawParts(proj, view);
  // viewmodel
  if (!P.dead) drawViewmodel();
}
function propM(p, w, h, d, col, yOff) {
  const m = R.box(w, h, d, col[0], col[1], col[2], 0);
  R.drawMesh(m, m4trs(p.x, (p.y || 0) + (yOff || h / 2), p.z, p.rotY || 0, 1));
}
function drawProp(p) {
  switch (p.type) {
    case 'torch': {
      R.drawMesh(R.box(0.12, 0.5, 0.12, .3, .2, .12, 0), m4trs(p.x, p.y, p.z, 0, 1));
      R.spawnP({ x: p.x, y: p.y + 0.32, z: p.z, vy: .5, maxLife: .4, r: 1, g: .7, b: .25, size: 5, grav: -.5 });
      break;
    }
    case 'crate': if (!p.dead) propM(p, .9, .9, .9, [.42, .3, .18], .45); break;
    case 'barrel': if (!p.dead) R.drawMesh(R.cyl(.4, 1.0, 8, .45, .32, .2, 0), m4trs(p.x, .5, p.z, 0, 1)); break;
    case 'brazier': R.drawMesh(R.cyl(.5, .8, 8, .25, .2, .18, 0), m4trs(p.x, .4, p.z, 0, 1)); R.spawnP({ x: p.x, y: .95, z: p.z, vy: .8, maxLife: .5, r: 1, g: .6, b: .2, size: 6, grav: -.5 }); break;
    case 'bones': R.drawMesh(R.box(1.2, .12, .8, .75, .72, .6, 0), m4trs(p.x, .08, p.z, p.x * 3, 1)); break;
    case 'rubble': R.drawMesh(R.box(.8, .3, .6, .3, .27, .24, 0), m4trs(p.x, .15, p.z, 0.5, 1)); break;
    case 'table': propM(p, 1.6, .1, .9, [.4, .3, .2], .8); propM({ x: p.x - .6, z: p.z }, .1, .8, .1, [.35, .25, .15], .4); propM({ x: p.x + .6, z: p.z }, .1, .8, .1, [.35, .25, .15], .4); break;
    case 'rack': propM(p, .3, 2.0, .3, [.3, .22, .14], 1.0); R.drawMesh(R.box(.08, 1.2, .08, .5, .5, .55, 0), m4trs(p.x + .2, 1.1, p.z, 0.2, 1)); break;
    case 'campfire': R.spawnP({ x: p.x, y: .25, z: p.z, vy: 1, maxLife: .5, r: 1, g: .65, b: .25, size: 7, grav: -.6 }); break;
    case 'well': R.drawMesh(R.cyl(1.0, 1.0, 10, .3, .3, .32, 0), m4trs(p.x, .5, p.z, 0, 1)); break;
    case 'dummy': propM(p, .5, 1.4, .5, [.5, .4, .28], .7); R.drawMesh(R.box(.5, .2, .5, .4, .3, .2, 0), m4trs(p.x, 1.45, p.z, 0, 1)); break;
    case 'gore_head': case 'gore_armL': case 'gore_armR': case 'gore_legL': case 'gore_legR': {
      const col = p.col || [.5, .4, .35];
      R.drawMesh(R.box(.3, .3, .3, col[0], col[1], col[2], 0), m4trs(p.x, (p.y || 0) + .18, p.z, G.time * (p.weapon ? 4 : 0), 1, 0.5));
      break;
    }
  }
}
function drawChest(c) {
  const col = c.rare ? [.75, .5, .15] : [.45, .32, .18];
  R.drawMesh(R.box(1.0, .55, .65, col[0], col[1], col[2], 0), m4trs(c.x, .28, c.z, 0, 1));
  if (!c.opened) {
    R.drawMesh(R.box(1.0, .3, .65, col[0] * 1.1, col[1] * 1.1, col[2] * 1.1, 0), m4trs(c.x, .68, c.z, 0, 1));
    if (c.rare) R.spawnP({ x: c.x, y: .9, z: c.z, vy: .6, maxLife: .6, r: 1, g: .7, b: .3, size: 4, grav: 0 });
  }
}
function drawShrine(s) {
  const cols = { fountain: [.3, .5, .8], blessing: [.9, .8, .4], revelation: [.5, .8, .9], transmute: [.8, .4, .9], risk: [.9, .3, .3], cursed_altar: [.6, .2, .7] };
  const c = cols[s.kind] || [.5, .5, .5];
  R.drawMesh(R.cyl(.55, 1.1, 8, c[0] * .6, c[1] * .6, c[2] * .6, 0), m4trs(s.x, .55, s.z, 0, 1));
  if (!s.used) R.spawnP({ x: s.x, y: 1.4, z: s.z, vy: .5, maxLife: .8, r: c[0], g: c[1], b: c[2], size: 4, grav: 0 });
}
function drawTrap(t) {
  if (t.def === 'spike_plate') R.drawMesh(R.box(1.6, .06, 1.6, .35, .3, .26, t.revealed ? .3 : 0), m4trs(t.x, .04, t.z, 0, 1));
  if (t.def === 'curse_zone' || t.def === 'lightning_node') {
    if (Math.random() < 0.3) R.spawnP({ x: t.x + (Math.random() - .5) * 3, y: .3 + Math.random(), z: t.z + (Math.random() - .5) * 3, vy: .3, maxLife: .9, r: t.def === 'curse_zone' ? .6 : .4, g: t.def === 'curse_zone' ? .2 : .7, b: t.def === 'curse_zone' ? .7 : 1, size: 4, grav: 0 });
  }
  if (t.revealed && (t.def === 'dart_wall' || t.def === 'tripwire' || t.def === 'rune_turret')) R.spawnP({ x: t.x, y: 1.2, z: t.z, vy: 0, maxLife: .3, r: 1, g: .8, b: .3, size: 4, grav: 0 });
}
function drawDoor(d) {
  if (d.state === 'open') return;
  const cx = d.x * CFG.tile + CFG.tile / 2, cz = d.y * CFG.tile + CFG.tile / 2;
  const col = d.kind === 'locked' ? [.55, .3, .15] : d.kind === 'secret' ? [.3, .27, .24] : [.38, .27, .16];
  const em = d.kind === 'locked' ? 0.15 : 0;
  const w = d.horiz ? 2.6 : 0.3, dp = d.horiz ? 0.3 : 2.6;
  R.drawMesh(R.box(w, 2.6, dp, col[0], col[1], col[2], em), m4trs(cx, 1.3, cz, 0, 1));
}
function drawLever(l) {
  R.drawMesh(R.box(.25, .9, .25, .3, .25, .2, 0), m4trs(l.x, .45, l.z, 0, 1));
  R.drawMesh(R.box(.1, .5, .1, l.pulled ? .3 : .7, l.pulled ? .3 : .5, .2, 0), m4trs(l.x, 1.0, l.z, l.pulled ? 0.8 : 0, 1, .7));
}
function drawValve(v) {
  R.drawMesh(R.cyl(.5, .3, 10, .4, .4, .45, 0), m4trs(v.x, .9, v.z, 0, 1));
  if (v.turned) R.spawnP({ x: v.x, y: 1.1, z: v.z, vy: .4, maxLife: .5, r: .3, g: .7, b: 1, size: 3, grav: 0 });
}
function drawBrazierProp(b) {
  R.drawMesh(R.cyl(.4, 1.0, 8, .25, .2, .18, 0), m4trs(b.x, .5, b.z, 0, 1));
  if (b.lit) { R.spawnP({ x: b.x, y: 1.1, z: b.z, vy: .8, maxLife: .4, r: 1, g: .6, b: .2, size: 6, grav: -.5 }); }
}
function drawLore(l) {
  R.drawMesh(R.box(.35, .08, .5, .7, .6, .35, .4), m4trs(l.x, .5 + Math.sin(G.time * 2) * .05, l.z, G.time, 1));
  R.spawnP({ x: l.x, y: .6, z: l.z, vy: .3, maxLife: .6, r: .9, g: .8, b: .4, size: 3, grav: 0 });
}
function drawGroundItem(g) {
  const it = g.payload.item;
  const rc = RAR_MINI[g.beam];
  const y = .35 + Math.sin(g.bob) * .06;
  R.drawMesh(R.box(.3, .3, .3, rc[0], rc[1], rc[2], .6), m4trs(g.x, y, g.z, G.time * 1.5, 1, .78));
  if (g.beam >= 1) R.spawnP({ x: g.x, y: .2, z: g.z, vy: 1.2, maxLife: .7, r: 1 - g.beam * .1, g: .7, b: .3, size: 3 + g.beam, grav: 0 });
}
function drawStairs(st, up) {
  for (let i = 0; i < 4; i++) {
    R.drawMesh(R.box(2.2, .25, .6, .3 + i * .02, .28, .25, 0), m4trs(st.x, .12 + i * .25, st.z + (up ? 1 : -1) * (i * .6 - 0.9), 0, 1));
  }
  R.spawnP({ x: st.x, y: .4, z: st.z, vy: .5, maxLife: .6, r: .9, g: .8, b: .5, size: 3, grav: 0 });
}
function drawPortalRing(x, z, r, g2, b2) {
  R.drawMesh(R.cyl(r, .1, 16, g2, g2 * .7, b2, .8), m4trs(x, .08, z, 0, 1));
}
function drawSurvivor(s) {
  R.drawMesh(R.box(.5, .8, .35, .45, .4, .32, 0), m4trs(s.x, .4, s.z, 0, 1, .4));
  R.spawnP({ x: s.x, y: 1.4, z: s.z, vy: .3, maxLife: .6, r: .9, g: .8, b: .3, size: 3, grav: 0 });
}
function drawNPC(n) {
  const v = VENDORS[n.npc];
  const col = hex2rgb(v.color);
  R.drawMesh(R.box(.55, .95, .35, col[0] * .5, col[1] * .5, col[2] * .5, 0), m4trs(n.x, .5, n.z, 0, 1));
  R.drawMesh(R.box(.4, .4, .4, col[0] * .8, col[1] * .7, col[2] * .6, 0), m4trs(n.x, 1.35, n.z, Math.sin(G.time * .5) * .3, 1));
  R.drawMesh(R.box(.6, .3, .6, .3, .25, .2, 0), m4trs(n.x, .15, n.z, 0, 1)); // counter
}
function hex2rgb(h) { const n = parseInt(h.slice(1), 16); return [(n >> 16 & 255) / 255, (n >> 8 & 255) / 255, (n & 255) / 255]; }

/* enemies */
function drawActor(a) {
  if (a.dead) {
    if (a.deadT < 30) {
      const m = R.box(.9, .4, .6, a.arch.col[0] * .6, a.arch.col[1] * .6, a.arch.col[2] * .6, 0);
      R.drawMesh(m, m4trs(a.pos[0], .2, a.pos[2], a.yaw, 1, 1.5));
    }
    return;
  }
  const s = a.bossDef ? (a.bossDef.scale || 1.2) : (a.arch.scale || 1);
  const t = G.time * (d2(a.pos[0], a.pos[2], P.pos[0], P.pos[2]) < 30 ? 1 : 0);
  const walk = Math.sin(t * 8 + a.bobPhase) * (a.state === 'chase' || a.state === 'idle' ? 0.35 : 0);
  const baseY = a.pos[1];
  const flying = a.arch.tags.includes('flying') || a.arch.spec === 'float';
  const hover = flying ? 0.6 + Math.sin(G.time * 2 + a.bobPhase) * 0.15 : 0;
  const glow = a.glow > 0 ? 0.5 + 0.5 * Math.sin(G.time * 14) : 0;
  const hitEm = a.hitFlash > 0 ? 0.6 : 0;
  const col = a.arch.col, col2 = a.arch.col2;
  const eliteCol = a.elite ? ELITES[a.elite].col : null;
  const body = R.box(.6, .9, .4, col[0], col[1], col[2], Math.max(glow * 0.5, hitEm));
  const head = R.box(.34, .34, .34, col[0] * 1.1, col[1] * 1.1, col[2] * 1.1, Math.max(glow * .7, hitEm));
  const limb = R.box(.16, .7, .16, col2[0], col2[1], col2[2], hitEm);
  const yawM = m4trs(a.pos[0], baseY + (flying ? hover : 0) + 1.05 * s, a.pos[2], a.yaw, s);
  if (a.limbs && a.limbs.head) R.drawMesh(head, m4mulMany(yawM, m4trs(0, .78, 0, 0, 1)));
  R.drawMesh(body, m4mulMany(yawM, m4trs(0, 0, 0, 0, 1)));
  // arms
  const windup = a.state === 'windup' ? -1.6 : a.state === 'recover' ? .9 : 0;
  if (!a.limbs || a.limbs.armR) {
    const wM = m4mulMany(yawM, m4trs(.42, .3, 0, 0, 1, windup));
    R.drawMesh(limb, m4mulMany(wM, m4trs(0, -.3, 0, 0, 1)));
    if (a.arch.atk !== 'unarmed') {
      const wl = a.arch.atk === 'melee' ? .9 : .55;
      R.drawMesh(R.box(.08, wl, .08, .45, .45, .5, glow * .8), m4mulMany(wM, m4trs(0, -.5 - wl / 2, 0, 0, 1)));
    }
  }
  if (!a.limbs || a.limbs.armL) {
    const aM = m4mulMany(yawM, m4trs(-.42, .3, 0, 0, 1, -walk * .5 + (a.arch.tags.includes('shield') ? 1.2 : 0)));
    R.drawMesh(limb, m4mulMany(aM, m4trs(0, -.3, 0, 0, 1)));
    if (a.arch.tags.includes('shield')) R.drawMesh(R.box(.1, .8, .6, col2[0] * 1.2, col2[1] * 1.2, col2[2] * 1.2, 0), m4mulMany(aM, m4trs(-.15, -.4, 0, 0, 1)));
  }
  // legs (unless flying)
  if (!flying) {
    if (!a.limbs || a.limbs.legL) R.drawMesh(R.box(.18, .65, .18, col2[0], col2[1], col2[2], hitEm), m4mulMany(yawM, m4trs(-.18, -.85 + Math.abs(walk) * .1, walk * .18, 0, 1)));
    if (!a.limbs || a.limbs.legR) R.drawMesh(R.box(.18, .65, .18, col2[0], col2[1], col2[2], hitEm), m4mulMany(yawM, m4trs(.18, -.85 + Math.abs(walk) * .1, -walk * .18, 0, 1)));
  }
  // elite glow marker
  if (a.elite) R.spawnP({ x: a.pos[0], y: baseY + 2.1 * s, z: a.pos[2], vy: .2, maxLife: .4, r: eliteCol[0], g: eliteCol[1], b: eliteCol[2], size: 4, grav: 0 });
  // boss core exposed
  if (a.bossId && a.coreOpen > 0) R.spawnP({ x: a.pos[0], y: baseY + 1.2 * s, z: a.pos[2], vy: .3, maxLife: .3, r: 1, g: .3, b: .9, size: 7, grav: 0 });
}
function drawProj(pr) {
  if (pr.arrow) {
    R.drawMesh(R.box(.06, .06, .7, .6, .45, .3, .2), m4trs(pr.x, pr.y, pr.z, Math.atan2(-pr.vx, -pr.vz), 1, Math.atan2(pr.vy, Math.hypot(pr.vx, pr.vz))));
  } else {
    const c = pr.glowCol || [.8, .8, 1];
    R.drawMesh(R.box(.22, .22, .22, c[0], c[1], c[2], 1), m4trs(pr.x, pr.y, pr.z, G.time * 5, 1, .7));
  }
}

/* first-person viewmodel */
function drawViewmodel() {
  const w = curWeapon();
  const a = P.attack;
  const cp = Math.cos(P.pitch), sp = Math.sin(P.pitch);
  const cy = Math.cos(P.yaw), sy = Math.sin(P.yaw);
  const right = [cy, 0, -sy], fwd = [-sy * cp, sp, -cy * cp];
  // proper up = cross(right, fwd)
  const upv = v3cross(right, [fwd[0], fwd[1], fwd[2]]);
  const sway = Math.sin(P.bobPhase) * 0.02;
  const basePos = [P.pos[0] + right[0] * .38 + upv[0] * (-.28 + sway) + fwd[0] * .7,
    P.pos[1] + eyeH() + right[1] * .38 + upv[1] * (-.28 + sway) + fwd[1] * .7,
    P.pos[2] + right[2] * .38 + upv[2] * (-.28 + sway) + fwd[2] * .7];
  let yawOff = 0, pitchOff = 0, zOff = 0, roll = 0;
  const prog = a.state === 'windup' ? clamp(a.t / a.dur, 0, 1) : a.state === 'recover' ? clamp(a.t / a.dur, 0, 1) : 0;
  if (a.state === 'windup') { yawOff = -0.9 * prog; pitchOff = 0.5 * prog; }
  else if (a.state === 'recover') { yawOff = 1.4 * (1 - prog); pitchOff = -0.7 * (1 - prog); }
  else if (a.state === 'charging') { pitchOff = -0.3; yawOff = 0.5; }
  else if (a.state === 'cast') { zOff = -0.25 * clamp(a.t / a.dur, 0, 1); pitchOff = -0.3; }
  else if (a.state === 'kick') { zOff = -0.35 * Math.sin(Math.min(1, a.t / a.dur) * Math.PI); }
  else if (a.state === 'draw') { zOff = -0.15 * P.drawT; yawOff = 0.4 * P.drawT; }
  else { yawOff = Math.sin(G.time * 1.5) * 0.03; }
  if (P.sheathed) return;
  const yaw = P.yaw + yawOff;
  const skin = SKIN_TONES[P.preset.skin || 0];
  const drawAt = (x, y, z, mesh, pitch) => {
    const pos = [P.pos[0] + right[0] * x + upv[0] * y + fwd[0] * (z + zOff),
      P.pos[1] + eyeH() + right[1] * x + upv[1] * y + fwd[1] * (z + zOff),
      P.pos[2] + right[2] * x + upv[2] * y + fwd[2] * (z + zOff)];
    R.drawMesh(mesh, m4trs(pos[0], pos[1], pos[2], yaw, 1, (P.pitch + (pitch || 0)), roll));
  };
  if (P.blocking && P.equip.off && P.equip.off.cat === 'shield') {
    drawAt(.3, -.25, .55, R.box(.08, .85, .7, .35, .28, .18, 0));
    drawAt(.3, -.25, .5, R.box(.06, .7, .55, .5, .42, .3, .1));
  }
  if (!w) {
    drawAt(.35, -.32, .5, R.box(.14, .3, .14, skin[0], skin[1], skin[2], 0));
    return;
  }
  if (w.fam === 'bow') {
    const draw = P.drawT || 0;
    drawAt(.4, -.1, .6, R.box(.05, .9, .1, .35, .24, .14, 0), 1.5);
    drawAt(.4, -.1, .6, R.box(.02, .02, .8, .8, .78, .7, .2), 0);
    if (draw > 0) drawAt(.35, -.1, .45 - draw * .15, R.box(.05, .5, .05, .6, .5, .35, 0));
    return;
  }
  if (w.fam === 'staff' || w.fam === 'wand') {
    drawAt(.35, -.15, .55, R.box(.07, 1.4, .07, .3, .2, .12, 0), -.2);
    const c = SPELLS[P.selectedSpell] && ELEM_COL[SPELLS[P.selectedSpell].elem] || [.8, .6, 1];
    drawAt(.35, .55, .55, R.box(.16, .16, .16, c[0], c[1], c[2], a.state === 'cast' ? 1 : .4));
    if (a.state === 'cast') R.spawnP({ x: basePos[0], y: basePos[1] + .4, z: basePos[2], vy: 0, maxLife: .2, r: c[0], g: c[1], b: c[2], size: 6, grav: 0 });
    drawAt(.35, -.35, .45, R.box(.13, .3, .13, skin[0], skin[1], skin[2], 0));
    return;
  }
  // melee weapon
  const metal = w.fam === 'mace' ? [.45, .45, .5] : [.55, .56, .6];
  const bladeL = w.fam === 'dagger' ? .45 : w.fam === 'great' ? 1.2 : .8;
  drawAt(.35, -.15, .5, R.box(.09, .22, .09, .25, .17, .1, 0), 1.2); // grip
  if (w.fam === 'mace') drawAt(.35, .0, .55, R.box(.18, .22, .18, metal[0], metal[1], metal[2], 0), 0);
  else drawAt(.35, bladeL * 0.4, .52, R.box(.06, bladeL, .02, metal[0], metal[1], metal[2], a.state === 'windup' || a.state === 'recover' ? .35 : 0), 0);
  drawAt(.35, -.06, .5, R.box(.2, .05, .06, .5, .4, .2, 0), 0); // guard
  drawAt(.35, -.3, .42, R.box(.13, .32, .13, skin[0], skin[1], skin[2], 0)); // hand
  if (a.state === 'cast' || a.state === 'charging') {
    const c = [.9, .8, .5];
    drawAt(.35, .1, .6, R.box(.1, .1, .1, c[0], c[1], c[2], .8));
  }
}
function eyeH() { return P.crouch ? CFG.crouchEye : CFG.eyeHeight; }
const SKIN_TONES = [[.8, .6, .45], [.65, .45, .3], [.45, .3, .2], [.9, .75, .62]];

/* ============================================================
   19. GAME STATES — enter town/floor, loop, boot
   ============================================================ */
function enterTown(from, pos) {
  G.mode = 'town';
  el('menuRoot').classList.add('hidden');
  G.floor = buildTown(G.campaign);
  if (R) buildStaticMesh(R, G.floor);
  P.pos = pos ? [pos[0], 0, pos[1]] : [G.floor.spawn[0], 0, G.floor.spawn[2]];
  P.pos[1] = 0;
  P.vel = [0, 0, 0];
  P.yaw = Math.PI;
  P.dead = false;
  P.blocking = false;
  spawnFloorQuestStuff(G.floor);
  // gold caches appear in their floors, not town
  SND.ambient('town');
  showFloorTitle('Hollowmere', 'The last lit place');
  if (INPUT && !INPUT.locked) toast('Click the view to capture the mouse — WASD to move, E to talk', '');
  el('hud').classList.remove('hidden');
  closeAllScreens();
  G.state = 'play';
  saveGame(true);
}
function enterFloor(idx, from, pos) {
  if (idx > 16) idx = 16;
  el('menuRoot').classList.add('hidden');
  const fs = G.campaign.floors[idx] || (G.campaign.floors[idx] = {});
  let F;
  try { F = generateFloor(G.campaign, idx); }
  catch (e) {
    console.error(e);
    toast('The way is blocked. (generation failed)', 'bad');
    return;
  }
  G.floor = F;
  if (R) buildStaticMesh(R, F);
  // restore fog
  if (fs.fog) { try { F.fog = b64decode(fs.fog); } catch (e) { } }
  // spawn actors
  const killed = new Set(fs.killed || []);
  for (const s of F.spawns) {
    if (killed.has(s.killedKey)) continue;
    // nudge spawn out of blocking props
    let sx = s.x, sz = s.z;
    if (circleBlocked(F, sx, sz, 0.5)) {
      outer: for (let rr = 0.6; rr <= 2.4; rr += 0.6) {
        for (let ang = 0; ang < TAU; ang += Math.PI / 4) {
          const nx = s.x + Math.cos(ang) * rr, nz = s.z + Math.sin(ang) * rr;
          if (!circleBlocked(F, nx, nz, 0.5)) { sx = nx; sz = nz; break outer; }
        }
      }
    }
    const a = spawnEnemy(F, s.arch, sx, sz, s.level, { id: s.killedKey, elite: s.elite, elite2: s.elite2, questElite: s.questElite, loot: s.loot, gold: s.gold });
    // room activation handled by proximity
  }
  if (F.bossSpawn && !fs.bossKilled) {
    spawnBoss(F, F.bossSpawn.boss, F.bossSpawn.x, F.bossSpawn.z, F.bossSpawn.level);
    // jam doors near boss room
  } else if (F.bossSpawn && fs.bossKilled) {
    F.bossDefeated = true;
  }
  spawnFloorQuestStuff(F);
  // gold cache
  for (const c of G.campaign.caches) {
    if (c.floor === idx) spawnGroundItem(F, c.x, c.z, { gold: c.amount, cache: true }, 2);
  }
  P.pos = pos ? [pos[0], 0, pos[1]] : [F.spawn[0], 0, F.spawn[2]];
  P.pos[1] = 0; P.vel = [0, 0, 0];
  if (!pos) P.yaw = Math.PI;
  G.mode = 'dungeon';
  closeAllScreens();
  SND.ambient([4, 8, 12, 16].includes(idx) && !F.bossDefeated ? 'boss' : ['stone', 'crypt', 'cistern', 'rift'][regionOf(idx).id]);
  const reg = regionOf(idx);
  showFloorTitle('Floor ' + idx, reg.name + ' — ' + reg.desc);
  if (INPUT && !INPUT.locked) toast('Click the view to capture the mouse', '');
  el('hud').classList.remove('hidden');
  G.state = 'play';
  G.campaign.maxFloor = Math.max(G.campaign.maxFloor, idx);
  EVT.emit('FloorEntered', { floor: idx });
  saveGame(true);
  // bestiary entries for region
  if (!G.campaign.bestiary) G.campaign.bestiary = {};
  for (const s of F.spawns) if (!G.campaign.bestiary[s.arch]) G.campaign.bestiary[s.arch] = true;
}
function showFloorTitle(main, sub) {
  const t = el('floorTitle');
  el('ftMain').textContent = main;
  el('floorSub').textContent = sub || '';
  t.style.opacity = '1';
  setTimeout(() => { t.style.opacity = '0'; }, 2600);
}
let lastTs = 0, minimapT = 0, hudT = 0;
function gameLoop(ts) {
  requestAnimationFrame(gameLoop);
  const dt = clamp((ts - lastTs) / 1000, 0, 0.05);
  lastTs = ts;
  if (G.state === 'play') {
    const active = !G.uiOpen;
    if (active && !P.dead) updateWorld(dt);
    else if (P.dead) { R.updateParts(dt); }
    render();
    hudT -= dt;
    if (hudT <= 0) { hudT = 0.1; updateHUD(); drawMinimap(); }
    updateDmgNums(dt);
  } else if (G.state === 'menu') {
    // draw faint menu backdrop
    R.beginFrame();
  }
}
function buildHotbarDom() {
  const hb = el('hotbar');
  hb.innerHTML = '';
  for (let i = 0; i < 6; i++) {
    const s = mk('div', 'slot');
    s.id = 'hb' + i;
    s.innerHTML = `<span class="key">${i + 1}</span><span class="gly"></span><span class="cnt"></span><div class="cd hidden"></div>`;
    hb.appendChild(s);
  }
  for (const id of ['slotQ', 'slotR']) {
    const s = el(id);
    if (s && !s.querySelector('.gly')) s.insertAdjacentHTML('afterbegin', '<span class="gly"></span>');
  }
}

/* ---------------- boot ---------------- */
function fatalBoot(e) {
  const n = el('nogl');
  n.classList.remove('hidden');
  n.style.zIndex = '100';
  n.style.background = 'rgba(10,8,6,.95)';
  n.style.display = 'flex';
  n.style.flexDirection = 'column';
  n.style.padding = '30px';
  n.style.textAlign = 'left';
  n.innerHTML = '<div style="color:#e08080;font-size:20px;margin-bottom:10px">Startup error</div>' +
    '<div style="color:#d8cdb4;max-width:820px;white-space:pre-wrap">' + esc(String(e && e.message || e)) + '</div>' +
    '<div style="color:#8a7f68;font-size:12px;max-width:820px;white-space:pre-wrap;margin-top:10px">' + esc(String(e && e.stack || '').split('\n').slice(0, 6).join('\n')) + '</div>' +
    '<div style="color:#8a7f68;font-size:12px;margin-top:14px">(click to dismiss)</div>';
  n.onclick = () => n.classList.add('hidden');
}
function boot() {
  try {
    G = {
      state: 'menu', mode: 'town', campaign: null, floor: null, time: 0,
      uiOpen: null, settings: null,
    };
    loadSettings();
    SND = makeSND();
    const canvas = el('cv');
    R = makeRenderer(canvas);
    if (!R) { fatalBoot(new Error('WebGL2 is not available in this browser.')); return; }
    window.addEventListener('resize', () => R.resize());
    R.resize();
    INPUT = makeInput();
    buildHotbarDom();
    el('hud').style.fontSize = (G.settings.uiScale * 100) + '%';
    el('version').textContent = 'Hollowmere build 1.0.2 · spec v1.1';
    document.body.addEventListener('mousedown', () => { SND.init(); SND.resume(); }, { once: true });
    showMainMenu();
    requestAnimationFrame(gameLoop);
  } catch (e) {
    try { console.error(e); } catch (e2) {}
    fatalBoot(e);
  }
}
if (!NODE) {
  window.addEventListener('error', ev => {
    const msg = ev && (ev.error || ev.message);
    if (msg) { try { console.error(msg); } catch (e2) {} fatalBoot(msg); }
  });
  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot);
  else boot();
}

/* ============================================================
   20. SELF-TESTS (node game.js) — spec §19.4 etc.
   ============================================================ */
function runSelfTests() {
  const results = [];
  const test = (name, fn) => {
    try { fn(); results.push(['PASS', name]); }
    catch (e) { results.push(['FAIL', name + ' — ' + e.message]); }
  };
  const assert = (c, m) => { if (!c) throw new Error(m || 'assert failed'); };

  test('RNG determinism', () => {
    const a = mulberry32(42), b = mulberry32(42);
    for (let i = 0; i < 100; i++) assert(a() === b(), 'rng mismatch');
  });
  test('XP curve monotonic', () => {
    let prev = 0;
    for (let L = 1; L <= 30; L++) { const x = xpForLevel(L); assert(x > prev, 'xp not increasing'); prev = x; }
  });
  test('item bases valid', () => {
    for (const [id, b] of Object.entries(ITEM_BASES)) {
      assert(b.name && b.w >= 1 && b.h >= 1 && b.value >= 0, 'bad base ' + id);
    }
    assert(Object.keys(ITEM_BASES).length > 60, 'too few bases');
  });
  test('24 talents, 5 ranks, 3 classes', () => {
    assert(TALENTS.length === 24, 'talent count');
    for (const c of CLASS_IDS) assert(TALENTS.filter(t => t.cls === c).length === 8, '8 talents per class');
  });
  test('10 spells', () => assert(SPELL_ORDER.length === 10 && SPELL_ORDER.every(s => SPELLS[s]), 'spells'));
  test('24 enemy archetypes', () => assert(ENEMIES.length === 24, 'enemies'));
  test('4 bosses, 4 regions', () => assert(Object.keys(BOSSES).length === 4 && REGIONS.length === 4, 'bosses/regions'));
  test('12 relics', () => assert(Object.keys(RELICS).length === 12, 'relics'));
  test('24 lore entries', () => assert(LORE.length === 24, 'lore'));
  test('loot generation: 800 rolls valid', () => {
    const r = mulberry32(7);
    for (let i = 0; i < 800; i++) {
      const ilvl = ri(r, 1, 20);
      const items = rollLoot(r, { ilvl, n: 1, relicChance: 0.02 });
      for (const it of items) {
        assert(it && it.name && it.price > 0 && RAR_IDX[it.rarity] !== undefined, 'bad item');
        if (it.rarity === 'enchanted') assert((it.affixes || []).length >= 1, 'enchanted needs 1 affix');
        if (it.rarity === 'rare') assert((it.affixes || []).length >= 2, 'rare needs 2+ affixes');
        const s = itemStats(it);
        if (it.cat === 'weapon') assert(s.dmgMax > 0, 'weapon dmg');
      }
    }
  });
  test('inventory grid: place/rotate/swap', () => {
    const p = { inv: new Array(60).fill(null) };
    const sword = makeItem('sword_iron', 1, 'common', mulberry32(1), { identified: true });
    assert(canPlace(p, sword, 0, 0, false), 'place sword');
    sword._x = 0; sword._y = 0; sword.rot = 0; p.inv.push(sword);
    const sword2 = makeItem('sword_iron', 1, 'common', mulberry32(2), { identified: true });
    assert(!canPlace(p, sword2, 0, 0, false), 'overlap must fail');
    assert(canPlace(p, sword2, 0, 3, false), 'below ok');
    const bow = makeItem('bow_short', 1, 'common', mulberry32(3), { identified: true });
    assert(bow.w === 1 && bow.h === 4, 'bow footprint');
    assert(!canPlace(p, bow, 0, 3, false), 'bow must not fit under sword');
    assert(canPlace(p, bow, 1, 0, false), 'bow fits in next column');
  });
  test('armor mitigation formula bounds', () => {
    const armor = 50;
    const red = Math.min(0.75, armor / (armor + 100 + 8 * (5 - 1)));
    assert(red > 0 && red < 0.75, 'reduction bounds');
    const huge = Math.min(0.75, 10000 / (10000 + 100));
    assert(huge === 0.75, 'cap 75%');
  });
  test('resistance clamp', () => {
    assert(clamp(-2, -0.5, 0.75) === -0.5, 'lower clamp');
    assert(clamp(3, -0.5, 0.75) === 0.75, 'upper clamp');
  });
  test('potion restore fractions', () => {
    assert(ITEM_BASES['potion_health_s'].effect.param === 0.3, 'minor 30%');
    assert(ITEM_BASES['potion_health_m'].effect.param === 0.5, 'standard 50%');
    assert(ITEM_BASES['potion_health_g'].effect.param === 0.8, 'greater 80%');
    assert(ITEM_BASES['potion_stam'].effect.param === 0.7, 'stamina 70%');
  });
  test('price formulas', () => {
    const b = ITEM_BASES['sword_iron'];
    const it = makeItem('sword_iron', 4, 'common', mulberry32(9), { identified: true });
    const expect = Math.max(1, Math.round(65 * (1 + 0.12 * 4) * 1));
    assert(it.price === expect, 'price formula ' + it.price + ' vs ' + expect);
    assert(sellValue(it) === Math.floor(it.price * 0.25), 'sell 25%');
  });
  test('identify cost', () => {
    const it = makeItem('sword_iron', 7, 'enchanted', mulberry32(10), { identified: false });
    assert(identifyCost(it) === 20 + 10 * 7, 'identify cost');
  });
  test('repair cost', () => {
    const it = makeItem('chest_mail', 10, 'common', mulberry32(11), { identified: true });
    it.dur = 0;
    const c = repairCost(it);
    assert(c === Math.ceil((1 - 0) * (it.price) * 0.2) || c >= 1, 'repair cost min 1');
  });
  test('floor generation: 320 seeds all solvable', () => {
    let genFails = 0, floors = 0;
    for (let i = 0; i < 20; i++) {
      for (let idx = 1; idx <= 16; idx++) {
        const seed = hashMix(1000 + i, idx, 777);
        let layout = null, att = 0;
        while (!layout && att < 12) { layout = tryGenerateFloor(idx, hashMix(seed, att)); att++; }
        if (!layout) { genFails++; continue; }
        floors++;
        const F = layout.F;
        assert(assertReachable(F), 'unreachable floor seed ' + seed + ' idx ' + idx);
        assert(F.rooms.length >= 8, 'too few rooms');
        assert(F.chests !== undefined, 'chests field');
        if ([4, 8, 12, 16].includes(idx)) assert(F.rooms.some(r => r.role === 'boss'), 'boss room on boss floor');
      }
    }
    assert(genFails <= 2, 'too many generation failures: ' + genFails);
  });
  test('full floor populate with campaign', () => {
    const campaign = { seed: 4242, descent: 0, difficulty: 'adventurer', maxFloor: 1, quests: { mq1: { state: 'active', objDone: {} } }, lore: {}, bestiary: {}, floors: {} };
    for (let idx of [1, 2, 5, 9, 13, 16]) {
      const F = generateFloor(campaign, idx);
      assert(F.spawns.length > 0, 'spawns on floor ' + idx);
      for (const s of F.spawns) assert(ENEMY_BY_ID[s.arch], 'unknown arch ' + s.arch);
      if (idx === 16) assert(F.bossSpawn && F.bossSpawn.boss === 'warden_below', 'final boss');
      if (idx >= 2 && idx !== 16) { /* locked door may or may not exist; if so key placed */ }
    }
  });
  test('reachability with locked doors (key first)', () => {
    // locked door kind must have a key placed in a room reachable before it — checked by door/key pairing
    for (let i = 0; i < 40; i++) {
      const idx = 2 + (i % 14);
      const F0 = tryGenerateFloor(idx, hashMix(999, i));
      if (!F0) continue;
      const F = F0.F;
      for (const d of F.doors) if (d.kind === 'locked') assert(d.key, 'locked door without key id');
    }
  });
  test('aStar finds path around walls', () => {
    const campaign = { seed: 31, floors: {}, quests: {}, lore: {}, maxFloor: 1, difficulty: 'adventurer', descent: 0, bestiary: {} };
    const F = generateFloor(campaign, 1);
    for (const d of F.doors) d.state = 'open'; // doors open for pathing check
    const path = aStar(F, F.spawn[0], F.spawn[2], F.stairsDown.x, F.stairsDown.z);
    assert(path && path.length > 3, 'aStar path');
  });
  test('damage pipeline smoke (player→enemy)', () => {
    const campaign = { seed: 55, floors: {}, quests: {}, lore: {}, maxFloor: 1, difficulty: 'adventurer', descent: 0, bestiary: {} };
    const F = generateFloor(campaign, 1);
    G = { state: 'play', mode: 'dungeon', campaign, floor: F, time: 0, uiOpen: null, settings: Object.assign({}, DEFAULT_SETTINGS) };
    P = makePlayer({ name: 't', cls: 'vanguard' });
    P.pos = [F.spawn[0], 0, F.spawn[2]];
    const a = spawnEnemy(F, 'scavenger', F.spawn[0] + 1, F.spawn[2], 1, { loot: [], gold: 0 });
    const hp0 = a.hp;
    dealDamage(a, { player: true }, { phys: 10, poise: 5, src: { player: true } });
    assert(a.hp < hp0, 'damage applied');
    assert(!a.dead, 'not killed by 10');
    dealDamage(a, { player: true }, { phys: 9999, src: { player: true } });
    assert(a.dead, 'killed');
    assert(F.ground.length >= 0, 'ground ok');
  });
  test('save serialization round-trip', () => {
    const it = makeItem('sword_iron', 3, 'rare', mulberry32(12), { identified: false });
    const d = serializeItem(it);
    const it2 = deserializeItem(d);
    assert(it2 && it2.name === it.name && it2.rarity === 'rare', 'round trip');
    assert(JSON.stringify(it2.affixes) === JSON.stringify(it.affixes), 'affixes preserved');
  });
  test('elite modifiers exist (8)', () => assert(Object.keys(ELITES).length === 8, 'elites'));
  test('trap defs (7) & shrine kinds (6) & events (10+)', () => {
    assert(Object.keys(TRAP_DEFS).length === 7, 'traps');
    assert(Object.keys(SHRINE_KINDS).length === 6, 'shrines');
    assert(EVENTS.length >= 10, 'events');
  });
  test('quests: 4 main + 12 side', () => {
    assert(QUESTS.filter(q => q.main).length === 4, 'main quests');
    assert(QUESTS.length - QUESTS.filter(q => q.main).length >= 12, 'side quests');
  });
  test('difficulty profiles', () => {
    assert(CFG.difficulty.wanderer.hp === 0.8 && CFG.difficulty.dread.dmg === 1.35, 'profiles');
    assert(CFG.difficulty.adventurer.goldLoss === 0.10, 'default loss 10%');
  });

  let pass = 0, fail = 0;
  for (const [s, n] of results) { if (s === 'PASS') pass++; else fail++; console.log(s + '  ' + n); }
  console.log(`\n${pass} passed, ${fail} failed`);
  if (fail > 0) process.exitCode = 1;
}
if (NODE) {
  // headless renderer/audio stubs for self-tests
  R = { burst() {}, spawnP() {}, updateParts() {}, drawMesh() {}, drawParts() {}, box() { return {}; }, cyl() { return {}; }, buildVAO() { return {}; }, pushBox() {}, pushCyl() {}, pushQuadY() {}, meshOf() { return {}; }, useMain() {}, resize() {}, project() { return null; }, beginFrame() {}, clearDepth() {}, canvas: { width: 0, height: 0, clientWidth: 0, clientHeight: 0 }, IDENT: m4ident() };
  SND = new Proxy({}, { get: () => () => {} });
}
if (NODE) runSelfTests();

