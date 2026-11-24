/* Ember · Bend Grounds — browser shell (protocol v3).
 * This file renders server observations and submits strings from `legalActions`.
 * It holds NO game rules: legality, costs, effects, combat, bots and RNG all live in the Bend server.
 * Battle playback replays the server's structured combat events (before/after snapshots);
 * it never computes damage, deaths or stat changes itself.
 */
'use strict';

(() => {
  const $ = (sel, root = document) => root.querySelector(sel);
  const $$ = (sel, root = document) => [...root.querySelectorAll(sel)];
  const el = (tag, attrs = {}, ...kids) => {
    const n = document.createElement(tag);
    for (const [k, v] of Object.entries(attrs)) {
      if (v == null || v === false) continue;
      if (k === 'class') n.className = v;
      else if (k === 'html') n.innerHTML = v;
      else if (k === 'text') n.textContent = v;
      else if (k.startsWith('on')) n.addEventListener(k.slice(2), v);
      else if (k === 'dataset') Object.assign(n.dataset, v);
      else n.setAttribute(k, v === true ? '' : v);
    }
    for (const kid of kids.flat()) if (kid != null && kid !== false) n.append(kid instanceof Node ? kid : document.createTextNode(String(kid)));
    return n;
  };
  const icon = (id, cls = '') => `<svg class="${cls}" aria-hidden="true"><use href="#i-${id}"/></svg>`;
  const esc = (s) => String(s ?? '').replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));

  // ---------- Transport ----------
  const API = (() => {
    const q = new URLSearchParams(location.search).get('api');
    if (q) {
      try {
        const url = new URL(q);
        if (url.protocol === 'http:' && ['127.0.0.1', 'localhost', '[::1]'].includes(url.hostname)
            && !url.username && !url.password && url.pathname === '/' && !url.search && !url.hash) return url.origin;
      } catch { /* Ignore malformed overrides; only loopback HTTP origins are accepted. */ }
      console.warn('Ignoring api override: expected a loopback HTTP origin.');
    }
    if (location.protocol === 'file:') return 'http://127.0.0.1:8765';
    return '';
  })();
  // Protocol v2 changed what `buy` means (shop -> hand). v1 saves stay under their old key and are never auto-replayed.
  const STORE = 'bendgrounds.v2';
  const LEGACY_STORE = 'bendgrounds.v1';
  const MOVE_RE = /^[a-z]+(?::\d+)*$/;
  const parseSeed = (v) => (/^\d{1,10}$/.test(String(v ?? '').trim()) && +v <= 4294967295 ? +v : null); // u32

  const CLIENT_PROTOCOL = 3;
  const gamePath = (seed, mode, moves) => `/api/game?seed=${seed}&mode=${mode}&moves=${moves.join(',')}&v=${CLIENT_PROTOCOL}`;
  const absUrl = (p) => (API || location.origin) + p;

  async function getJSON(path) {
    let res;
    try {
      res = await fetch(API + path, { cache: 'no-store' });
    } catch (e) {
      const err = new Error(`Cannot reach the Bend server at ${API || location.origin}. Start it with scripts/start.sh, then retry.`);
      err.network = true;
      throw err;
    }
    const text = await res.text();
    let body = null;
    try { body = JSON.parse(text); } catch { /* not JSON */ }
    if (!body) {
      const err = new Error(`Server returned HTTP ${res.status} without JSON${text ? ': ' + text.slice(0, 120) : ''}`);
      err.status = res.status;
      throw err;
    }
    return { status: res.status, body };
  }

  // ---------- State ----------
  const S = {
    seed: null,
    mode: 'bots',
    moves: [],
    data: null,
    rules: null,
    scout: null,       // seat id being scouted (null = follow next opponent)
    selected: null,    // board index selected for reordering
    busy: false,
    autoplay: false,
    lastRetry: null,
  };

  // Protocol of the running server: rules.protocolVersion when published, else 1.
  const serverProtocol = () => {
    const v = D()?.protocolVersion ?? S.protocol ?? S.rules?.protocolVersion;
    if (v == null && S.protocol === null) return CLIENT_PROTOCOL; // server unreachable: assume ours, the load will fail visibly anyway
    return v != null && Number.isFinite(+v) ? +v : 1;
  };
  // Learn the server protocol before touching saves: rules first, else an empty game observation.
  async function detectProtocol() {
    if (S.rules?.protocolVersion != null) { S.protocol = +S.rules.protocolVersion; return; }
    try {
      const { body } = await getJSON(gamePath(0, 'bots', []));
      S.protocol = body?.protocolVersion != null ? +body.protocolVersion : body?.error?.code === 'unsupported_version' ? null : 1;
    } catch { S.protocol = null; }
  }
  const save = () => {
    try { localStorage.setItem(STORE, JSON.stringify({ protocol: serverProtocol(), seed: S.seed, mode: S.mode, moves: S.moves, t: Date.now() })); } catch { /* private mode */ }
  };
  const validSave = (v) => v && parseSeed(v.seed) != null && Array.isArray(v.moves) && v.moves.every((m) => typeof m === 'string' && MOVE_RE.test(m));
  const readStore = (key) => { try { return JSON.parse(localStorage.getItem(key) || 'null'); } catch { return null; } };
  // A saved transcript is replayed only under the protocol it was recorded with.
  const loadSaved = () => {
    const v = readStore(STORE);
    if (!validSave(v)) return null;
    const proto = Number.isFinite(+v.protocol) ? +v.protocol : 1;
    return { seed: +v.seed, mode: v.mode === 'manual' ? 'manual' : 'bots', moves: v.moves, protocol: proto, compatible: proto === serverProtocol() };
  };
  const legacySave = () => { const v = readStore(LEGACY_STORE); return validSave(v) ? { seed: +v.seed, mode: v.mode === 'manual' ? 'manual' : 'bots', moves: v.moves } : null; };

  // ---------- Helpers over the observation ----------
  const D = () => S.data;
  const legal = () => {
    const la = D()?.legalActions || [];
    return la.map((a) => (typeof a === 'string' ? a : a?.action || a?.id || '')).filter(Boolean);
  };
  const isLegal = (a) => !!a && legal().includes(a);
  const players = () => D()?.players || [];
  const seatOf = (id) => players().find((p) => p.id === id) || players()[id];
  const meId = () => (D() ? D().player ?? 0 : 0);
  const me = () => seatOf(meId());
  const nameOf = (id) => (id == null || id < 0 ? 'Ghost' : seatOf(id)?.name || `Seat ${id + 1}`);
  const costs = () => ({ ...(S.rules?.costs || {}), ...(D()?.costs || {}) });
  const finished = () => D()?.phase === 'finished';
  const human = () => (S.mode === 'manual' ? meId() : 0);
  const findSwap = (i, j) => [`swap:${i}:${j}`, `swap:${j}:${i}`].find(isLegal);
  const hasHand = () => Array.isArray(me()?.hand);
  const handMax = () => costs().handMax ?? 7;
  const boardMax = () => costs().boardMax ?? 5;
  // play:i deploys to the right end; play:i:pos (if the engine offers it) to a position.
  const playActionsFor = (i) => legal().filter((a) => a === `play:${i}` || a.startsWith(`play:${i}:`));
  const playAt = (i, pos) => (isLegal(`play:${i}:${pos}`) ? `play:${i}:${pos}` : isLegal(`play:${i}`) ? `play:${i}` : null);

  // Rules text, preferably from /api/rules. Fallbacks are plain labels, not rules.
  function ruleText(action) {
    const r = S.rules;
    if (!r) return '';
    const a = r.actions;
    if (Array.isArray(a)) {
      const hit = a.find((x) => x && typeof x === 'object' && (x.action === action || x.name === action || x.id === action || String(x.syntax || x.format || '').split(':')[0] === action));
      if (hit) return hit.text || hit.description || hit.desc || hit.help || '';
    } else if (a && typeof a === 'object') {
      const v = a[action];
      if (typeof v === 'string') return v;
      if (v && typeof v === 'object') return v.text || v.description || '';
    }
    if (Array.isArray(r.rules)) {
      const sentences = r.rules.flatMap((t) => String(t).split(/(?<=\.)\s+/));
      const hit = sentences.find((t) => t.toLowerCase().startsWith(action + ' ') || t.toLowerCase().startsWith(action + ':'));
      if (hit) return hit[0].toUpperCase() + hit.slice(1);
    }
    return '';
  }

  // Catalog lookup: combat snapshots carry compact units {id, attack, health, shield, guard};
  // name/tribe/tier/text come from the /api/rules card list (display only).
  const catalog = () => S.rules?.cards || S.rules?.units || [];
  const cardById = (id) => catalog().find((c) => c.id === id);
  function enrich(u) {
    if (!u || typeof u !== 'object') return u;
    const c = cardById(u.id) || {};
    // Protocol 3: every unit carries `golden` plus its effective text/baseAttack/baseHealth. A golden unit
    // never borrows the printed (catalog) base or text, which would show non-doubled values.
    const g = u.golden === true;
    return { ...c, ...u, golden: g, name: u.name ?? c.name ?? `Unit ${u.id}`, tribe: u.tribe ?? c.tribe, tier: u.tier ?? c.tier,
      text: u.text ?? (g ? null : c.text), abilities: u.abilities ?? (g ? undefined : c.abilities),
      baseAttack: u.baseAttack ?? (g ? null : c.attack), baseHealth: u.baseHealth ?? (g ? null : c.health) };
  }
  // Keyword badges: names from the engine's `keywords`, numbers from armor/rally/income fields.
  const keywordsOf = (u) => {
    const k = new Set((Array.isArray(u.keywords) ? u.keywords : []).map((x) => String(x).toLowerCase().split(/\s+/)[0]));
    if (u.shield) k.add('shield'); else if (u.shield === false) k.delete('shield'); // shield can break in combat
    if (u.guard) k.add('guard');
    const num = (n) => (typeof u[n] === 'number' && u[n] > 0 ? u[n] : null);
    for (const n of ['armor', 'rally', 'income']) if (num(n)) k.add(n);
    return [...k].map((name) => ({ name, label: (KW_LABEL[name] || name[0].toUpperCase() + name.slice(1)) + (num(name) ? ` ${num(name)}` : '') }));
  };

  const KW_LABEL = { shield: 'Shield', guard: 'Guard', armor: 'Armor', rally: 'Rally', income: 'Income' };

  /* GLOSSARY-BEGIN
   * Explanations of keywords, ability triggers and effects. Pure data and functions (no DOM, no state):
   * tests/v3_ui_test.py evaluates exactly this block in Node against the engine's /api/rules.
   * Sources, in order:
   *  1. An optional glossary published by the server in /api/rules (`glossary` or `definitions`, as an
   *     array of {key|term, text, kind?, scope?} or an object term -> text). It always wins.
   *  2. The entries below. They restate the CURRENT Bend semantics (engine/game.bend: attack_with/hurt/rally
   *     for combat, play_fx/observe for Play and After-you-play, endturn, sell_apply). Each one names an
   *     `anchor`: a phrase of the server's own rules text (for effects: of the engine-generated card text).
   *     When the anchor is absent the entry is NOT used and the UI says that no definition is published,
   *     so a rules change can never leave a stale explanation on screen. Nothing here decides anything.
   */
  const GLOSS_FALLBACK = [
    { key: 'guard', kind: 'keyword', term: 'Guard', scope: 'Every combat', anchor: 'a Guard must be attacked first',
      text: 'While a warband has a Guard, every enemy attack must target one of its Guards (chosen at random among them). Guard does not reduce damage and does not change the attack order of its own side.' },
    { key: 'shield', kind: 'keyword', term: 'Shield', scope: 'Every combat, breaks once', anchor: 'on a Shield breaks',
      text: 'The first hit with more than 0 attack that this unit takes in a combat (while attacking or while being attacked) deals no damage at all and breaks the Shield. Armor plays no part in that hit. The Shield is back at the start of every combat, because combat never changes your real board.' },
    { key: 'armor', kind: 'keyword', term: 'Armor', scope: 'Every combat', anchor: 'Armor n reduces the hit by n',
      text: 'Armor n lowers every hit this unit takes by n, never below 0, whether it is attacking or being attacked. While the unit still has a Shield, the Shield takes the hit instead.' },
    { key: 'rally', kind: 'keyword', term: 'Rally', scope: 'Combat only, gains reset', anchor: 'Rally n: before each of its attacks a unit gains +n attack for the rest of the combat',
      text: 'Right before each attack this unit makes, it gains +n attack, and that hit already uses the new value. Gains stack: its 1st attack uses +n, its 2nd +2n, its 3rd +3n. The extra attack also counts when it is attacked later in the same combat. Rally does not fire when the unit is attacked, and every gain is gone after the combat.' },
    { key: 'income', kind: 'keyword', term: 'Income', scope: 'Every round', anchor: 'Income units on the board',
      text: 'While this unit is on your board, your gold for each new round grows by n. Unlike base income it is not capped at 10. It does nothing in combat.' },
    { key: 'play', kind: 'trigger', term: 'Play', scope: 'Once, on deploy', anchor: 'resolves its Play abilities',
      text: 'Fires once, when you deploy this card from your hand to your board (play). It resolves before the card joins the board, so "other allies" means the units already there. Buying the card does not fire it.' },
    { key: 'kinplay', kind: 'trigger', term: 'After you play another card of its tribe', scope: 'Each matching deploy', anchor: 'After-you-play abilities',
      text: 'Fires while this unit is on your board, each time you deploy a different card of the same tribe. It resolves after that card\'s own Play ability and after it has joined the board, so "other allies" includes the new card. Units fire left to right. Buying a card, or an ability adding one to your hand, does not fire it.' },
    { key: 'endturn', kind: 'trigger', term: 'End of turn', scope: 'Every round on the board', anchor: 'End of turn abilities fire at the end of every recruit phase',
      text: 'Fires for every unit on your board when your recruit phase ends (end), left to right, before combat. It fires again every round the unit stays on your board. Cards in your hand do not fire it.' },
    { key: 'sell', kind: 'trigger', term: 'Sell', scope: 'Once, when sold', anchor: 'its Sell abilities fire',
      text: 'Fires when you sell this unit from your board (sell), after it has left the board and after the base refund. Only board units can be sold; cards in your hand cannot.' },
    { key: 'nochain', kind: 'concept', term: 'No chain reactions', scope: 'Always', anchor: 'Abilities never trigger other abilities',
      text: 'An ability never sets off another ability. A card that an ability adds to your hand waits there until you deploy it yourself.' },
    { key: 'combatcopy', kind: 'concept', term: 'Combat is fought on a copy', scope: 'Every combat', anchor: 'Combat never changes your real board',
      text: 'Damage, deaths, broken Shields and Rally gains exist only during that combat. Afterwards your warband is exactly as it was before the fight: same units, same stats, Shields intact.' },
    { key: 'otherallies', kind: 'concept', term: 'Other allies', scope: 'Ability targets', anchor: "'Other X allies' never includes the source itself",
      text: '"Other Ember allies" (or Tide, Stone) means every unit of that tribe on your board except the card whose ability is resolving. Cards in your hand are never affected.' },
    { key: 'counts', kind: 'concept', term: 'Counts', scope: 'Ability multipliers', anchor: 'count at most 4',
      text: '"For each card in your hand" and "for each card you played" stop counting at 4. During a play, the card being played has already left your hand and is not yet counted as played.' },
    { key: 'damagecap', kind: 'concept', term: 'Damage cap', scope: 'After each fight', anchor: 'but at most',
      text: 'Only player damage is capped: the loser of a fight loses the winner\'s tier plus the tiers of the winner\'s surviving units, but never more than 3 + the round number. Unit stats have no such cap.' },
    { key: 'stats', kind: 'effect', term: 'Stat gain', scope: 'Permanent', cardAnchor: /(gain|allies) \+\d+(\/\+\d+)?/,
      text: 'Permanent: the unit keeps the gain on your board for the rest of the game, through every combat.' },
    { key: 'statsPerHand', kind: 'effect', term: 'For each card in your hand', scope: 'Permanent', cardAnchor: /for each card in your hand \(max 4\)/,
      text: 'The gain is multiplied by the number of cards in your hand when the ability fires, counting at most 4. When it fires on Play, the deployed card has already left your hand. The result is permanent.' },
    { key: 'statsPerPlay', kind: 'effect', term: 'For each card you played this turn', scope: 'Permanent', cardAnchor: /for each card you played (earlier )?this turn \(max 4\)/,
      text: 'The gain is multiplied by the number of cards you deployed this recruit phase, counting at most 4. On Play or After you play, only cards played earlier count, not the one being played now. At End of turn every card you played this turn counts. The result is permanent.' },
    { key: 'gold', kind: 'effect', term: 'Gain gold', scope: 'This turn', cardAnchor: /gain \d+ gold/,
      text: 'Adds gold you can spend right now. Gold is reset every round, so unspent gold is lost.' },
    { key: 'make', kind: 'effect', term: 'Add a card to your hand', scope: 'Card in hand', cardAnchor: /add a random \w+ card of tier \d+ or lower to your hand/,
      text: 'Adds a random card of this card\'s tribe, of the given tier or lower, to the right end of your hand. Nothing is added if your hand is full. The new card does nothing until you deploy it.' },
  ];
  // V4 triples. Shown only when the server's rules text mentions golden cards (anchor); a server
  // `golden`/`triple` glossary entry replaces it. The engine card text of a golden unit is authoritative.
  GLOSS_FALLBACK.push(
    { key: 'golden', kind: 'concept', term: 'Golden', scope: 'Permanent', anchor: 'golden',
      text: 'When you own three plain (non-golden) copies of the same card across your hand and board, they merge into one golden copy at the right end of your hand. Copies in your hand are used first, then board copies. The golden copy keeps the stat gains all three copies had. Its stat gains, gold, Rally and Income are doubled, an ability that adds a card adds two, and Armor is unchanged. Its card text shows the exact values. Golden copies never merge again. Buying the third copy still needs a free hand slot.' });
  // Card-text prefixes the engine generates for each trigger (engine/game.bend trig_text).
  const TRIGGER_PREFIX = [
    { key: 'play', re: /^Play:/ },
    { key: 'kinplay', re: /^After you play another [A-Za-z]+ card:/ },
    { key: 'endturn', re: /^End of turn:/ },
    { key: 'sell', re: /^Sell:/ },
  ];
  const TRIGGER_TEXT_RE = /(Play:|After you play another [A-Za-z]+ card:|End of turn:|Sell:)/g;
  const GLOSS_ALIAS = { 'after you play': 'kinplay', 'other allies': 'otherallies', 'counts': 'counts', 'damage cap': 'damagecap', 'end of turn': 'endturn', 'stat gain': 'stats' };
  const glossKey = (s) => {
    const t = String(s ?? '').trim();
    const alias = GLOSS_ALIAS[t.toLowerCase()];
    if (alias) return alias;
    const trig = TRIGGER_PREFIX.find((x) => x.re.test(t.endsWith(':') ? t : `${t}:`));
    if (trig) return trig.key;
    if (/^(kinplay|endturn|statsPerHand|statsPerPlay)$/.test(t)) return t;
    return t.toLowerCase().split(/[^a-z]+/).filter(Boolean)[0] || '';
  };
  function ruleSentences(rules) {
    const out = [];
    for (const t of Array.isArray(rules?.rules) ? rules.rules : []) out.push(...String(t).split(/(?<=[.!?])\s+(?=[A-Z])/));
    return out;
  }
  function serverGlossary(rules) {
    const g = rules && (rules.glossary ?? rules.definitions);
    const list = Array.isArray(g) ? g : g && typeof g === 'object' ? Object.entries(g).map(([k, v]) => (typeof v === 'string' ? { key: k, text: v } : { key: k, ...v })) : [];
    return list.filter((x) => x && typeof (x.text ?? x.description) === 'string' && (x.key ?? x.id ?? x.term ?? x.name))
      .map((x) => ({ key: glossKey(x.key ?? x.id ?? x.term ?? x.name), term: String(x.term ?? x.name ?? x.key ?? x.id), kind: x.kind || null, scope: x.scope || x.duration || '', text: String(x.text ?? x.description), rule: null, source: 'server' }));
  }
  // -> Map key -> {key, term, kind, scope, text, rule (quoted engine sentence or null), source, cardAnchor?}
  function buildGlossary(rules) {
    const m = new Map();
    const sentences = ruleSentences(rules);
    const all = sentences.join(' ').toLowerCase();
    for (const f of GLOSS_FALLBACK) {
      if (f.anchor) {
        if (!all.includes(f.anchor.toLowerCase())) continue;
        const rule = sentences.find((s) => s.toLowerCase().includes(f.anchor.toLowerCase())) || null;
        m.set(f.key, { ...f, rule, source: 'client' });
      } else m.set(f.key, { ...f, rule: null, source: 'client' });
    }
    // A server entry is authoritative: its text leads; an anchored client restatement stays as `detail`.
    for (const s of serverGlossary(rules)) {
      const f = m.get(s.key);
      m.set(s.key, { ...(f || {}), ...s, kind: s.kind || f?.kind || 'keyword', scope: s.scope || f?.scope || '', rule: f?.rule ?? null, detail: f && f.text !== s.text ? f.text : null, source: 'server' });
    }
    return m;
  }
  const TARGET_TEXT = { self: 'this unit', kin: (tribe) => `every other ${tribe} unit on your board` };
  // A card's engine text split into its sentences: keyword sentences first, then one per ability
  // (engine/game.bend card_text = keywords with dots, then abils_text in order).
  const textSentences = (text) => String(text || '').split(/(?<=\.)\s+(?=[A-Z])/).filter(Boolean);
  // -> {keywords:[{key,label,value,entry}], abilities:[{sentence, trigger, triggerEntry, effect, effectEntry, target}], missing:[term]}
  function explainCard(card, gloss) {
    const c = card || {};
    const tribe = c.tribe || 'tribe';
    const missing = [];
    const kwLabels = (Array.isArray(c.keywords) ? c.keywords : []).map(String);
    const keywords = kwLabels.map((label) => {
      const key = glossKey(label);
      const n = Number(String(label).split(/\s+/)[1]);
      const entry = gloss.get(key) || null;
      if (!entry) missing.push(label);
      return { key, label, value: Number.isFinite(n) ? n : null, entry };
    });
    const sents = textSentences(c.text);
    const abilSents = sents.slice(kwLabels.length);
    let abilities;
    if (Array.isArray(c.abilities)) {
      abilities = c.abilities.map((a, i) => {
        const sentence = abilSents[i] || '';
        const trigger = glossKey(a?.trigger);
        const triggerEntry = gloss.get(trigger) || null;
        const ek = String(a?.effect ?? '');
        let effectEntry = gloss.get(ek) || null;
        if (effectEntry?.cardAnchor && !effectEntry.cardAnchor.test(sentence)) effectEntry = null;
        if (!triggerEntry) missing.push(`trigger ${a?.trigger}`);
        if (!effectEntry) missing.push(`effect ${ek}`);
        const t = a?.target === 'kin' ? TARGET_TEXT.kin(tribe) : a?.target === 'self' ? TARGET_TEXT.self : null;
        return { sentence, trigger, triggerEntry, effect: ek, effectEntry, target: t };
      });
    } else {
      // No structured abilities (unknown schema): explain only the trigger read from the engine text.
      abilities = abilSents.map((sentence) => {
        const tp = TRIGGER_PREFIX.find((x) => x.re.test(sentence));
        const triggerEntry = tp ? gloss.get(tp.key) || null : null;
        if (!triggerEntry) missing.push(sentence);
        return { sentence, trigger: tp?.key || null, triggerEntry, effect: null, effectEntry: null, target: null };
      });
    }
    return { keywords, abilities, missing };
  }
  // Display only: big numbers stay readable on small stat badges; the exact value goes to labels.
  function fmtStat(v) {
    const n = Number(v);
    if (!Number.isFinite(n)) return String(v ?? '?');
    const a = Math.abs(n);
    if (a < 1000) return String(n);
    if (a < 10000) return `${(n / 1000).toFixed(1).replace(/\.0$/, '')}k`;
    if (a < 1e6) return `${Math.round(n / 1000)}k`;
    return `${(n / 1e6).toFixed(1).replace(/\.0$/, '')}M`;
  }
  /* GLOSSARY-END */
  // ---------- Art (original procedural SVG, no external assets) ----------
  // Every catalog card has a bespoke painter (ART_CARDS, keyed by card name): a layered tribe
  // environment, a hand-composed creature with ink outlines, form shading and its own light,
  // and tier-scaled backlight. Unknown names fall back to tribe archetypes (BODY) so a catalog
  // change never breaks rendering. Pure presentation: nothing here reads or affects rules.
  const TRIBES = ['Ember', 'Tide', 'Stone', 'Neutral'];
  const PAL = {
    Ember: [{ a: '#ffb347', b: '#e2481b', d: '#4a1006', e: '#fff3b0' }, { a: '#ff8a5c', b: '#b8261a', d: '#3e0b07', e: '#ffe08a' }, { a: '#ffd36e', b: '#d9611c', d: '#431604', e: '#fffbe0' }],
    Tide: [{ a: '#7fe3ff', b: '#1b6d9b', d: '#06243a', e: '#e9fdff' }, { a: '#8ff0d0', b: '#127a75', d: '#05302c', e: '#f0fff8' }, { a: '#a9c4ff', b: '#3552a8', d: '#0b1638', e: '#eef3ff' }],
    Stone: [{ a: '#e6cf9e', b: '#7a5f3a', d: '#241b12', e: '#ffe6a0' }, { a: '#cfc8b6', b: '#5d5a52', d: '#1b1916', e: '#b8f0ff' }, { a: '#e0b88c', b: '#8a4e2e', d: '#28140a', e: '#ffd27a' }],
    // Neutral: tribeless tools and constructs; palette picked by the metal in the card name (brass, steel, copper).
    Neutral: [{ a: '#ecc77e', b: '#8a6a34', d: '#2a1e0e', e: '#9fe8ff' }, { a: '#cfd6de', b: '#5a6470', d: '#1a1e24', e: '#ffd27a' }, { a: '#eaa274', b: '#8a4a2a', d: '#2a140a', e: '#a0ffd8' }],
    Other: [{ a: '#ffe2a0', b: '#8a6424', d: '#21170c', e: '#fff4d0' }],
  };
  const NEUTRAL_METAL = [[1, /\b(tin|iron|steel|mirror)\b/i], [2, /\b(copper|bronze)\b/i], [0, /\b(brass|gold|bounty|grand|siege)\b/i]];
  function hashStr(s) { let h = 2166136261; for (const ch of String(s)) { h ^= ch.charCodeAt(0); h = Math.imul(h, 16777619); } return h >>> 0; }
  function rng(seed) { let t = seed >>> 0; return () => { t += 0x6d2b79f5; let r = Math.imul(t ^ (t >>> 15), 1 | t); r ^= r + Math.imul(r ^ (r >>> 7), 61 | r); return ((r ^ (r >>> 14)) >>> 0) / 4294967296; }; }

  // --- drawing kit (viewBox 100x80; ground near y=70; keep faces clear of the top corners) ---
  const INK = '#150b07';
  const n1 = (v) => +v.toFixed(1);
  const inkA = (w = 0.9) => `stroke="${INK}" stroke-width="${w}" stroke-linejoin="round" stroke-linecap="round"`;
  // shaded path: flat/gradient fill + ink outline + bounding-box form shading (light from upper left)
  const sp = (c, d, fill, w) => `<path d="${d}" fill="${fill || c.B}" ${inkA(w)}/><path d="${d}" fill="${c.H}"/>`;
  const se = (c, cx, cy, rx, ry, fill, rot) => {
    const t = rot ? ` transform="rotate(${rot} ${cx} ${cy})"` : '';
    return `<ellipse cx="${cx}" cy="${cy}" rx="${rx}" ry="${ry}" fill="${fill || c.B}" ${inkA()}${t}/><ellipse cx="${cx}" cy="${cy}" rx="${rx}" ry="${ry}" fill="${c.H}"${t}/>`;
  };
  const fp = (d, fill, op = 1) => `<path d="${d}" fill="${fill}"${op < 1 ? ` opacity="${op}"` : ''}/>`;
  const ln = (d, col, w, op = 1) => `<path d="${d}" fill="none" stroke="${col}" stroke-width="${w}" stroke-linecap="round" stroke-linejoin="round"${op < 1 ? ` opacity="${op}"` : ''}/>`;
  const inkLn = (d, col, w, op = 1) => ln(d, INK, w + 1.6, op) + ln(d, col, w, op);
  const dot = (x, y, r, col, op = 1) => `<circle cx="${n1(x)}" cy="${n1(y)}" r="${n1(r)}" fill="${col}"${op < 1 ? ` opacity="${op}"` : ''}/>`;
  const glow = (c, x, y, r, op = 1, g = 'G') => `<circle cx="${x}" cy="${y}" r="${r}" fill="${c[g]}"${op < 1 ? ` opacity="${op}"` : ''}/>`;
  const shadow = (x, y, rx, ry) => `<ellipse cx="${x}" cy="${y}" rx="${rx}" ry="${ry || rx * 0.22}" fill="#000" opacity=".5"/>`;
  // glowing eye: halo, iris, optional slit pupil, specular
  const eye = (x, y, r, col, pupil) => `<circle cx="${x}" cy="${y}" r="${n1(r * 2)}" fill="${col}" opacity=".22"/><circle cx="${x}" cy="${y}" r="${r}" fill="${col}" stroke="${INK}" stroke-width=".5"/>` +
    (pupil ? `<ellipse cx="${x}" cy="${y}" rx="${n1(r * 0.32)}" ry="${n1(r * 0.85)}" fill="${pupil}"/>` : '') + `<circle cx="${n1(x - r * 0.35)}" cy="${n1(y - r * 0.35)}" r="${n1(r * 0.3)}" fill="#fff"/>`;
  // cute dark eye with big highlight
  const peye = (x, y, r) => `<circle cx="${x}" cy="${y}" r="${r}" fill="#0b0705"/><circle cx="${n1(x - r * 0.3)}" cy="${n1(y - r * 0.35)}" r="${n1(r * 0.38)}" fill="#fff"/><circle cx="${n1(x + r * 0.35)}" cy="${n1(y + r * 0.3)}" r="${n1(r * 0.15)}" fill="#fff" opacity=".8"/>`;
  // flame tongue rooted at (x,y), height h, width w, tip lean; optional rotation in degrees about the root
  const flame = (c, x, y, h, w, lean = 0, rot = 0) => {
    const t = x + lean;
    const d = (s) => `M${n1(x - w * s / 2)} ${y}C${n1(x - w * s / 2)} ${n1(y - h * s * 0.42)} ${n1(t - w * s * 0.3)} ${n1(y - h * s * 0.55)} ${n1(t)} ${n1(y - h * s)}C${n1(t + w * s * 0.18)} ${n1(y - h * s * 0.62)} ${n1(x + w * s / 2)} ${n1(y - h * s * 0.45)} ${n1(x + w * s / 2)} ${y}Q${x} ${n1(y + w * s * 0.4)} ${n1(x - w * s / 2)} ${y}Z`;
    const g = rot ? ` transform="rotate(${rot} ${x} ${y})"` : '';
    return `<g${g}><path d="${d(1)}" fill="${c.F}"/><path d="${d(0.55)}" fill="#fff6c8" opacity=".9"/></g>`;
  };
  const scatter = (r, n, box, fn) => Array.from({ length: n }, () => fn(box[0] + r() * box[2], box[1] + r() * box[3], r())).join('');
  const embers = (r, n, col = '#ffb347', box = [4, 6, 92, 66]) => scatter(r, n, box, (x, y, k) => dot(x, y, 0.4 + k * 1.1, k > 0.6 ? '#fff3b0' : col, 0.35 + k * 0.6));
  const bubbles = (r, n, box = [4, 6, 92, 66]) => scatter(r, n, box, (x, y, k) => `<circle cx="${n1(x)}" cy="${n1(y)}" r="${n1(0.7 + k * 1.8)}" fill="none" stroke="#e9fdff" stroke-width=".5" opacity="${n1(0.3 + k * 0.4)}"/>`);
  const motes = (r, n, col, box = [4, 6, 92, 66]) => scatter(r, n, box, (x, y, k) => dot(x, y, 0.3 + k * 0.7, col, 0.25 + k * 0.5));
  const star4 = (x, y, s, col) => fp(`M${x} ${n1(y - s)}L${n1(x + s * 0.25)} ${n1(y - s * 0.25)}L${n1(x + s)} ${y}L${n1(x + s * 0.25)} ${n1(y + s * 0.25)}L${x} ${n1(y + s)}L${n1(x - s * 0.25)} ${n1(y + s * 0.25)}L${n1(x - s)} ${y}L${n1(x - s * 0.25)} ${n1(y - s * 0.25)}Z`, col);
  // cog wheel centred at (x,y): n teeth, outer radius r
  const gear = (x, y, r, col, n = 8, op = 1) => {
    const pts = [];
    for (let k = 0; k < n * 4; k++) { const a = (Math.PI * 2 * k) / (n * 4); const rr = k % 4 < 2 ? r : r * 0.78; pts.push(`${n1(x + rr * Math.cos(a))} ${n1(y + rr * Math.sin(a))}`); }
    return `<path d="M${pts.join('L')}Z M${n1(x + r * 0.32)} ${y}A${n1(r * 0.32)} ${n1(r * 0.32)} 0 1 0 ${n1(x - r * 0.32)} ${y}A${n1(r * 0.32)} ${n1(r * 0.32)} 0 1 0 ${n1(x + r * 0.32)} ${y}Z" fill="${col}" fill-rule="evenodd"${op < 1 ? ` opacity="${op}"` : ''}/>`;
  };
  const coin = (x, y, rx, tilt = 0.45) => `<ellipse cx="${n1(x)}" cy="${n1(y + 0.8)}" rx="${rx}" ry="${n1(rx * tilt)}" fill="#7a4a10"/><ellipse cx="${n1(x)}" cy="${n1(y)}" rx="${rx}" ry="${n1(rx * tilt)}" fill="#ffd36e" stroke="#7a4a10" stroke-width=".5"/><ellipse cx="${n1(x)}" cy="${n1(y)}" rx="${n1(rx * 0.55)}" ry="${n1(rx * tilt * 0.55)}" fill="none" stroke="#b07a1e" stroke-width=".4"/>`;
  const leaf = (x, y, len, ang, col) => `<path d="M0 0Q${n1(len * 0.5)} ${n1(-len * 0.32)} ${len} 0Q${n1(len * 0.5)} ${n1(len * 0.32)} 0 0Z" transform="translate(${n1(x)} ${n1(y)}) rotate(${n1(ang)})" fill="${col}" stroke="${INK}" stroke-width=".5"/>`;
  const crown = (c, x, y, w, h) => sp(c, `M${x - w / 2} ${y}L${n1(x - w / 2 + 0.6)} ${y - h}L${n1(x - w / 4)} ${n1(y - h * 0.45)}L${x} ${n1(y - h * 1.15)}L${n1(x + w / 4)} ${n1(y - h * 0.45)}L${n1(x + w / 2 - 0.6)} ${y - h}L${x + w / 2} ${y}Z`, c.M, 0.7) + dot(x, y - h * 0.3, Math.max(0.8, w * 0.07), '#ff4d6d');
  const wave = (y, amp, col, w, op) => ln(`M-4 ${y}q6 -${amp} 12 0t12 0 12 0 12 0 12 0 12 0 12 0 12 0 12 0`, col, w, op);
  const rays = (x, y, n, len, col, op, spread = 360, start = 0) => fp(Array.from({ length: n }, (_, k) => {
    const a = ((start + (spread * (k + 0.5)) / n) * Math.PI) / 180, b = a + 0.07, cc = a - 0.07;
    return `M${x} ${y}L${n1(x + Math.cos(b) * len)} ${n1(y + Math.sin(b) * len)}L${n1(x + Math.cos(cc) * len)} ${n1(y + Math.sin(cc) * len)}Z`;
  }).join(''), col, op);

  // --- environments: sky gradient K, rock material R, water W are set per environment ---
  const ENV = {
    // Ember: volcanic forge plain
    forge: { k: ['#1d0605', '#8a2a0c'], r: ['#5a3328', '#170b08'], w: ['#ff9a3a', '#7a1a06'], paint: (c, r) =>
      fp('M0 52L14 44L22 47L34 34L40 36L46 30L52 33L60 44L72 39L84 45L100 40V80H0Z', '#2b0d08') +
      ln('M46 31Q44 38 47 44', '#ff6a1a', 0.9, 0.8) + ln('M40 36Q38 42 41 47', '#ff8a3a', 0.5, 0.6) +
      `<ellipse cx="50" cy="56" rx="62" ry="9" fill="${c.G}" opacity=".55"/>` +
      fp('M0 63Q24 58 50 62T100 60V80H0Z', c.R) +
      ln('M8 70l6 -2l4 3l7 -2M62 74l7 -3l5 2l8 -3M30 77l5 -2l6 1', '#ff4d0d', 2, 0.35) + ln('M8 70l6 -2l4 3l7 -2M62 74l7 -3l5 2l8 -3M30 77l5 -2l6 1', '#ffc06a', 0.6, 0.9) +
      embers(r, 12) },
    kiln: { k: ['#200a06', '#4a1a0c'], r: ['#6a3a26', '#1e0d07'], w: ['#ff9a3a', '#7a1a06'], paint: (c, r) => {
      let d = '';
      for (let y = 4, row = 0; y < 62; y += 6, row++) {
        d += `M0 ${y}H100`;
        for (let x = (row % 2) * 7; x < 100; x += 14) d += `M${x} ${y}v6`;
      }
      const bricks = ln(d, '#120604', 0.6, 0.8);
      return `<rect width="100" height="80" fill="#3a160c"/>` + `<g opacity=".55">${bricks}</g>` +
        fp('M26 64V30Q26 10 50 10Q74 10 74 30V64Z', '#0c0402') + `<ellipse cx="50" cy="52" rx="24" ry="20" fill="${c.G}" opacity=".85"/>` +
        ln('M26 64V30Q26 10 50 10Q74 10 74 30V64', '#7a3a1e', 2.4) + ln('M26 64V30Q26 10 50 10Q74 10 74 30V64', '#c26a3a', 0.6, 0.7) +
        fp('M0 64H100V80H0Z', c.R) + ln('M0 64H100M0 71H100M18 64v7M44 64v7M70 64v7M30 71v9M58 71v9M86 71v9', '#0e0503', 0.6, 0.7) + embers(r, 8, '#ffb347', [28, 14, 44, 46]);
    } },
    pyre: { k: ['#2a0a24', '#ff7b2e'], r: ['#4a2420', '#120606'], w: ['#ffd36e', '#c2210d'], paint: (c, r) =>
      `<ellipse cx="50" cy="66" rx="40" ry="24" fill="${c.G}" opacity=".6"/>` +
      fp('M-4 22q14 -6 26 -1t24 -2 22 3 34 -3v6q-14 4 -30 1t-26 2 -24 -2 -26 2Z', '#4a1430', 0.75) +
      fp('M-4 36q18 -5 32 0t30 -2 46 1v5q-20 3 -40 0t-30 1 -38 0Z', '#6a1c26', 0.6) +
      fp('M0 66L10 60L18 64L30 56L42 63L54 58L66 64L80 57L92 62L100 59V80H0Z', '#1a0606') + embers(r, 14, '#ffd36e') +
      scatter(r, 7, [6, 8, 88, 50], (x, y, k) => fp(`M${n1(x)} ${n1(y)}l1.6 .5l-.4 1.2l-1.5 -.5Z`, '#9a8a86', 0.4 + k * 0.4)) },
    // Tide
    deep: { k: ['#1d86a8', '#03151f'], r: ['#3f6672', '#0c2028'], w: ['#8fe6ff', '#0b3550'], paint: (c, r) =>
      fp('M30 -2L46 -2L34 80L10 80Z', '#d8fbff', 0.08) + fp('M56 -2L66 -2L74 80L52 80Z', '#d8fbff', 0.07) + fp('M78 -2L86 -2L100 60L94 80Z', '#d8fbff', 0.05) +
      inkLn('M8 80Q4 66 10 56Q16 46 10 34', '#1f5a46', 1.6, 0.8) + ln('M8 80Q4 66 10 56Q16 46 10 34', '#3f8a5a', 0.6) +
      inkLn('M92 80Q96 64 90 54Q86 44 92 36', '#1f5a46', 1.6, 0.8) + ln('M92 80Q96 64 90 54Q86 44 92 36', '#3f8a5a', 0.6) +
      fp('M0 68Q20 64 40 67T80 66T100 66V80H0Z', '#a89a6a') + fp('M0 72Q22 70 44 73T100 71V80H0Z', '#6a6244') +
      scatter(r, 5, [6, 70, 88, 8], (x, y) => `<ellipse cx="${n1(x)}" cy="${n1(y)}" rx="2.4" ry="1.3" fill="#5a5238"/>`) + bubbles(r, 9) },
    storm: { k: ['#0a1224', '#3d5a74'], r: ['#41505c', '#0e161c'], w: ['#5fb8d8', '#06243a'], paint: (c, r) =>
      fp('M-4 14q10 -10 22 -4q8 -10 20 -2q10 -8 22 0q12 -6 20 2q10 -4 24 2V-4H-4Z', '#05080f', 0.85) +
      fp('M-4 24q14 -6 26 0q12 -6 26 0q14 -6 26 0q14 -6 30 0v-8H-4Z', '#121a2a', 0.6) +
      ln('M84 6L78 18L83 19L75 34', '#bff4ff', 2.2, 0.35) + ln('M84 6L78 18L83 19L75 34', '#ffffff', 0.7) +
      fp('M0 58Q12 52 24 57T48 56T72 57T100 55V80H0Z', c.W) + wave(58, 3, '#e9fdff', 0.7, 0.55) +
      fp('M0 68Q14 62 28 67T56 66T84 67T100 66V80H0Z', '#0b3550') + wave(67, 3.5, '#bff4ff', 0.6, 0.5) +
      scatter(r, 14, [2, 4, 96, 50], (x, y, k) => ln(`M${n1(x)} ${n1(y)}l-1.4 4`, '#9fc8e0', 0.35, 0.25 + k * 0.3)) },
    grotto: { k: ['#04101e', '#0f3d52'], r: ['#2a4250', '#08121a'], w: ['#6ad8f0', '#06243a'], paint: (c, r) =>
      `<circle cx="62" cy="24" r="16" fill="${c.G}" opacity=".55"/>` + dot(62, 24, 6.5, '#eefcff', 0.9) + dot(64, 22.5, 5.5, '#cfeef8', 0.5) +
      fp('M0 0H24Q14 16 16 34Q18 52 8 66L0 70Z', c.R) + fp('M100 0H82Q90 14 86 30Q82 48 94 62L100 64Z', c.R) +
      ln('M18 6Q12 20 15 36M86 8Q92 22 88 34', '#5a8a9a', 0.6, 0.5) +
      fp('M0 66Q30 62 50 64T100 63V80H0Z', '#0a2a3a') + ln('M12 70h18M44 73h22M70 69h16', '#9fe8ff', 0.5, 0.45) + ln('M56 66h12', '#eefcff', 0.7, 0.6) +
      scatter(r, 6, [14, 66, 72, 10], (x, y) => dot(x, y, 0.9, '#f4f0ff', 0.85)) + motes(r, 10, '#bff4ff') },
    abyss: { k: ['#010509', '#06222e'], r: ['#1a2a34', '#04080c'], w: ['#2a6a8a', '#020a10'], paint: (c, r) =>
      `<ellipse cx="50" cy="44" rx="46" ry="34" fill="${c.G}" opacity=".18"/>` + motes(r, 26, '#9fd8e8') +
      fp('M0 74Q16 66 30 72T60 70T100 72V80H0Z', '#020608') + scatter(r, 3, [10, 64, 80, 6], (x, y) => ln(`M${n1(x)} ${n1(y + 10)}q-2 -6 1 -12`, '#3a8a7a', 0.8, 0.6)) },
    // Stone
    cliff: { k: ['#22263c', '#d08a58'], r: ['#7a705e', '#241f18'], w: ['#9fc8e0', '#2a3a4a'], paint: (c, r) =>
      `<circle cx="70" cy="46" r="14" fill="#ffd9a0" opacity=".35"/>` +
      fp('M0 46L12 36L22 40L36 26L46 34L58 28L70 38L82 30L100 40V80H0Z', '#6a6278', 0.75) +
      fp('M0 54L16 46L28 50L42 42L56 50L70 44L86 52L100 48V80H0Z', '#4a4252') +
      fp('M0 64Q20 58 40 62T80 61T100 60V80H0Z', c.R) + ln('M6 70l8 -1M60 72l10 -2M30 76l9 -1', '#2e2820', 0.8, 0.7) +
      scatter(r, 4, [6, 66, 86, 10], (x, y) => `<ellipse cx="${n1(x)}" cy="${n1(y)}" rx="2.6" ry="1.4" fill="#6a6050" stroke="${INK}" stroke-width=".4"/>`) },
    cave: { k: ['#0e0a12', '#2c2034'], r: ['#5a5060', '#16121a'], w: ['#ffd27a', '#7a3a10'], paint: (c, r) => {
      const cl = (x, y, s, col) => fp(`M${x} ${y}L${n1(x - s * 0.5)} ${n1(y - s * 1.6)}L${x} ${n1(y - s * 2.4)}L${n1(x + s * 0.5)} ${n1(y - s * 1.6)}Z`, col) + fp(`M${x} ${y}L${x} ${n1(y - s * 2.4)}L${n1(x + s * 0.5)} ${n1(y - s * 1.6)}Z`, '#ffffff', 0.25);
      return fp('M0 0H100V14Q80 22 70 12Q58 4 46 12Q32 22 18 12Q8 6 0 14Z', '#07050a') + fp('M0 0V60Q10 46 8 30Q6 14 0 0Z', '#0a070e') + fp('M100 0V60Q90 46 92 30Q94 14 100 0Z', '#0a070e') +
        `<circle cx="12" cy="62" r="10" fill="${c.G2}" opacity=".6"/><circle cx="88" cy="60" r="10" fill="${c.G2}" opacity=".6"/>` +
        cl(10, 66, 3, '#b48cff') + cl(14, 67, 2, '#d8b8ff') + cl(88, 64, 3.2, '#b48cff') + cl(84, 66, 2, '#d8b8ff') + cl(92, 66, 1.8, '#e8d0ff') +
        fp('M0 66Q24 61 50 64T100 63V80H0Z', c.R) + motes(r, 10, '#e8d0ff');
    } },
    grove: { k: ['#0d2013', '#4a6a30'], r: ['#5a4630', '#1a120a'], w: ['#9fe8a0', '#1a4a20'], paint: (c, r) =>
      fp('M8 0H16Q14 30 18 70H4Q8 40 8 0Z', '#0f1a0c', 0.85) + fp('M80 0H90Q88 34 94 70H78Q82 40 80 0Z', '#0f1a0c', 0.85) + fp('M60 0H64Q63 30 66 66H58Q60 30 60 0Z', '#18281a', 0.6) +
      fp('M28 -2L40 -2L58 70L36 70Z', '#fff2b0', 0.09) + fp('M66 -2L72 -2L84 70L74 70Z', '#fff2b0', 0.07) +
      fp('M0 64Q20 58 40 62T80 61T100 60V80H0Z', '#2e4a1a') + fp('M0 70Q24 66 50 70T100 68V80H0Z', '#1e3210') +
      scatter(r, 9, [4, 62, 92, 12], (x, y) => ln(`M${n1(x)} ${n1(y)}l-1 -3M${n1(x)} ${n1(y)}l.2 -3.6M${n1(x)} ${n1(y)}l1.2 -2.8`, '#6aa040', 0.5, 0.8)) +
      `<g><path d="M86 72v-3" stroke="#e8dcc0" stroke-width="1"/><path d="M83.5 69.5a2.5 1.8 0 0 1 5 0Z" fill="#d0432f"/>${dot(85, 68.6, 0.4, '#fff')}</g>` + motes(r, 8, '#e8ff9a') },
    quarry: { k: ['#241a14', '#b07a48'], r: ['#9a8a6c', '#3a3026'], w: ['#9fc8e0', '#2a3a4a'], paint: (c, r) =>
      fp('M0 40H22V30H44V40H58V24H78V36H100V80H0Z', '#7a6550', 0.6) + ln('M22 30V40M44 30V40M58 24V40M78 24V36M0 50H100', '#3a2e22', 0.6, 0.5) +
      ln('M88 70V12L70 14M88 12L96 22', '#3a2416', 1.2, 0.8) + ln('M72 14v10', '#3a2416', 0.4, 0.8) +
      fp('M0 56H30V50H62V58H100V80H0Z', '#8a7a62') + ln('M0 56H30V50H62V58H100', '#d8c8a8', 0.5, 0.6) +
      fp('M0 66Q22 63 48 65T100 64V80H0Z', c.R) + scatter(r, 8, [4, 64, 92, 12], (x, y) => dot(x, y, 0.6, '#5a4e40', 0.8)) + motes(r, 10, '#f0d8a8', [4, 20, 92, 40]) },
    // Neutral: lamp-lit artificer's workshop
    workshop: { k: ['#120e12', '#3e2c1c'], r: ['#6a5034', '#1c140c'], w: ['#ffd27a', '#7a4a10'], paint: (c, r) =>
      gear(84, 26, 15, '#2c2218', 10, 0.9) + gear(66, 12, 8, '#261d14', 8, 0.85) + gear(12, 30, 10, '#2a2016', 8, 0.8) +
      ln('M0 44H100M0 48H100', '#5a4228', 1.4, 0.7) + ln('M24 44V36M76 48V58', '#5a4228', 1.4, 0.7) +
      `<circle cx="30" cy="16" r="12" fill="${c.G}" opacity=".35"/>` + dot(30, 16, 1.8, '#ffe9a8') +
      fp('M0 64H100V80H0Z', c.R) + ln('M0 64H100M0 71H100M20 64v7M52 64v7M84 64v7M36 71v9M70 71v9', '#120c06', 0.6, 0.7) +
      motes(r, 8, '#ffd27a', [6, 30, 88, 30]) },
    peaks: { k: ['#18213c', '#a8c0dc'], r: ['#8a96a8', '#2a3240'], w: ['#e8f4ff', '#6a88aa'], paint: (c, r) =>
      fp('M0 44L14 26L24 34L38 14L50 28L62 18L76 32L88 22L100 30V80H0Z', '#5a6a8a', 0.8) + fp('M38 14L33 21L37 20L40 24L43 19L46 23Z', '#eef6ff', 0.9) + fp('M62 18L58 23L61 22L64 25L66 22Z', '#eef6ff', 0.9) +
      fp('M0 58L18 48L30 54L46 46L62 54L78 46L100 56V80H0Z', '#3a4660') +
      fp('M0 66Q22 60 48 64T100 62V80H0Z', '#dfeaf6') + fp('M0 72Q30 68 60 72T100 70V80H0Z', '#b8cade') + motes(r, 22, '#ffffff', [2, 2, 96, 74]) },
  };

  // --- per-card painters: (c, p, r) => creature markup inside .art-body ---
  const ART_CARDS = {
    // ===== Ember =====
    'Spark Imp': { env: 'forge', pal: { a: '#ff9a4a', b: '#c8361a', d: '#3e0b07', e: '#fff3b0' }, paint: (c, p) =>
      shadow(50, 71, 16) + inkLn('M58 64Q74 70 76 58Q77 50 72 48', p.d, 1.6) + sp(c, 'M69 44L77 46L72 52Z', p.b) +
      sp(c, 'M40 46C30 30 20 30 13 34C17 38 17 42 15 47C21 44 25 48 25 53C29 49 33 51 36 55Z', c.D) + sp(c, 'M60 46C70 30 80 30 87 34C83 38 83 42 85 47C79 44 75 48 75 53C71 49 67 51 64 55Z', c.D) +
      ln('M38 47L19 36M37 50L21 46M36 53L27 51M62 47L81 36M63 50L79 46M64 53L73 51', p.a, 0.6, 0.55) +
      sp(c, 'M42 62L39 70H45L46 63Z') + sp(c, 'M58 62L61 70H55L54 63Z') + se(c, 50, 57, 11, 10) + `<ellipse cx="50" cy="60" rx="6" ry="5" fill="${p.e}" opacity=".25"/>` +
      sp(c, 'M41 53Q33 56 31 62L34 63Q37 59 43 58Z') + sp(c, 'M59 52Q68 46 71 35L74 36Q72 49 61 56Z') +
      glow(c, 73, 30, 13) + ln('M73 21v18M64 30h18M67 24l12 12M79 24L67 36', '#ffd36e', 0.7, 0.9) + dot(73, 30, 3.4, '#fffbe0') +
      sp(c, 'M42 32Q34 22 38 13Q41 22 46 27Z', p.d) + sp(c, 'M58 32Q66 22 62 13Q59 22 54 27Z', p.d) +
      sp(c, 'M38 38L26 32L37 45Z') + sp(c, 'M62 38L74 32L63 45Z') + se(c, 50, 39, 13, 12) +
      ln('M41 34l6 2M59 34l-6 2', p.d, 1.4) + eye(45, 38.5, 2.5, '#fff3b0', '#3e0b07') + eye(55, 38.5, 2.5, '#fff3b0', '#3e0b07') +
      fp('M42 44Q50 51 58 44Q50 47.5 42 44Z', p.d) + fp('M45 45.3l1 2 1-1.6M53 45.3l1 1.6 1-2', '#fff') },
    'Cinder Whelp': { env: 'forge', pal: { a: '#ffb347', b: '#d9481b', d: '#4a1006', e: '#fff3b0' }, paint: (c, p) =>
      shadow(50, 71, 24) + se(c, 34, 71, 7, 3, '#2a0f08') + se(c, 50, 72, 8, 3.4, '#33120a') + se(c, 66, 71, 7, 3, '#2a0f08') + ln('M30 71l3 -1l3 1M47 72l3 -1l4 1M63 71l3 -1l3 .8', '#ff7a1a', 0.7) +
      sp(c, 'M34 64Q18 66 17 56Q17 47 26 49Q21 53 25 58Q30 61 38 58Z') + flame(c, 25, 50, 9, 5, -1) +
      sp(c, 'M48 46Q40 25 29 22Q33 30 29 34Q35 36 33 42Q39 42 44 51Z', c.D) + ln('M46 46L31 25M44 48L31 35', p.a, 0.6, 0.5) +
      se(c, 46, 57, 16, 13) + `<ellipse cx="50" cy="61" rx="9" ry="8" fill="${p.e}" opacity=".3"/>` + ln('M43 56h12M42 60h14M43 64h12', p.b, 0.7, 0.7) +
      sp(c, 'M52 64Q54 71 61 70L60 65Z') + sp(c, 'M37 66Q37 72 44 71L44 66Z') +
      sp(c, 'M53 51Q57 38 64 34L71 44Q64 50 60 57Z') + sp(c, 'M63 27L61 18L67 26Z', p.d) + sp(c, 'M69 26L72 18L74 28Z', p.d) +
      se(c, 68, 36, 12, 10, null, -10) + sp(c, 'M73 35Q84 35 85 41Q80 46 72 44Z') + dot(81, 38.5, 0.8, p.d) +
      `<circle cx="67" cy="34" r="3.6" fill="#fff"/>` + peye(67.6, 34.4, 2.5) + ln('M63 30q4 -2 8 0', p.d, 0.9) +
      dot(89, 36, 2.2, '#6b5550', 0.55) + dot(92, 31, 1.7, '#6b5550', 0.45) + dot(94, 26.5, 1.2, '#6b5550', 0.35) + dot(88, 33, 0.7, '#ffd36e') },
    'Kindler': { env: 'kiln', pal: { a: '#c8643a', b: '#6a2a12', d: '#2a0c06', e: '#ffe08a' }, paint: (c, p) =>
      shadow(48, 71, 16) + inkLn('M40 52L30 71', '#4a2a14', 1.4) + flame(c, 29, 71, 4, 3) +
      sp(c, 'M35 71Q35 48 42 38H56Q62 48 64 71Z', c.D) + ln('M40 60q10 3 20 0', '#e2a15a', 0.6, 0.6) + ln('M37 68q12 3 25 0', '#e2a15a', 0.6, 0.6) +
      sp(c, 'M38 43Q35 24 50 19Q65 24 62 43Q56 47 50 47Q44 47 38 43Z', c.B) + sp(c, 'M50 19Q54 12 60 13Q56 16 56 22Z', c.B) +
      `<ellipse cx="50" cy="37" rx="8" ry="7" fill="#120604"/>` + eye(47, 37, 1.5, '#ffd36e') + eye(53, 37, 1.5, '#ffd36e') +
      sp(c, 'M57 47Q66 49 71 53L69 57Q62 54 56 53Z', c.D) + inkLn('M72 54V49', '#2a1408', 0.6) +
      glow(c, 74, 60, 18) + sp(c, 'M69 53H79L80 56H68Z', c.M, 0.6) + `<rect x="69.5" y="56" width="9" height="9" rx="1.5" fill="${c.G}" stroke="#7a4a10" stroke-width=".8"/>` +
      ln('M74 56v9', '#7a4a10', 0.6) + flame(c, 74, 64, 6.5, 4) + sp(c, 'M68 65H80L79 67H69Z', c.M, 0.6) + embers(rng(42), 6, '#ffb347', [64, 40, 22, 14]) },
    'Ember Herald': { env: 'forge', pal: { a: '#ff7a4a', b: '#a8201a', d: '#3e0b07', e: '#fff3b0' }, paint: (c, p) =>
      shadow(50, 71, 18) + inkLn('M30 72V14', '#3a1a0a', 1.3) + dot(30, 13, 1.6, '#ffd36e') +
      sp(c, 'M31 16L54 18Q47 24 54 31L31 31Z', c.B) + flame(c, 40, 29, 10, 7) +
      sp(c, 'M42 71L44 49Q51 45 59 49L63 71Z', c.D) + sp(c, 'M43 60H61L61.5 63H42.5Z', c.M, 0.6) + dot(52, 61.5, 1.3, '#ff4d6d') +
      se(c, 44, 49, 6, 4, c.M) + se(c, 60, 49, 6, 4, c.M) +
      sp(c, 'M48 34Q40 27 43 18Q46 26 51 30Z', '#2a120a') + sp(c, 'M58 34Q66 27 64 18Q62 26 56 30Z', '#2a120a') +
      se(c, 53, 39, 8, 8, '#d8643a') + eye(51, 37.5, 1.4, '#fff3b0') + eye(56, 37.5, 1.4, '#fff3b0') +
      sp(c, 'M57 51Q65 49 70 41L72 43Q67 53 59 55Z', c.D) +
      sp(c, 'M58 40Q68 41 74 33L81 25Q86 30 84 37L78 37Q70 45 59 43Z', c.M) + `<ellipse cx="83" cy="31" rx="2" ry="5.5" transform="rotate(35 83 31)" fill="#5a2a08"/>` +
      flame(c, 85, 28, 14, 9, 2, 55) + ln('M88 18q6 8 3 18M92 14q8 12 4 24', p.e, 0.8, 0.6) },
    'Flame Dancer': { env: 'pyre', pal: { a: '#ffcf6e', b: '#e2481b', d: '#4a1006', e: '#fff3b0' }, paint: (c, p) =>
      glow(c, 50, 50, 26, 0.7) + ln('M34 20Q18 30 27 46Q36 58 24 68', '#ff7a1a', 2.6, 0.5) + ln('M34 20Q18 30 27 46Q36 58 24 68', '#ffd36e', 0.9) +
      ln('M66 16Q84 24 75 40Q66 54 79 66', '#ff7a1a', 2.6, 0.5) + ln('M66 16Q84 24 75 40Q66 54 79 66', '#ffd36e', 0.9) +
      flame(c, 50, 74, 28, 20, 2) + flame(c, 42, 72, 16, 9, -6) + flame(c, 58, 72, 16, 9, 6) +
      sp(c, 'M46 52Q44 43 48 37H54Q58 44 56 52Q51 56 46 52Z', '#ffcf9e') + fp('M44 52Q51 58 58 52L60 58Q51 62 42 58Z', '#e2481b') +
      sp(c, 'M47 40Q39 33 34 20L36.5 19Q42 30 49 36Z', '#ffcf9e') + sp(c, 'M54 40Q62 30 65 16L67.5 17Q67 32 56 41Z', '#ffcf9e') +
      flame(c, 47, 30, 14, 9, -12, -35) + flame(c, 49, 28, 11, 6, -6, -15) + se(c, 51, 32, 5, 6, '#ffcf9e') +
      ln('M48.5 32q1.3 1 2.6 0M52.5 32q1.3 1 2.6 0', '#4a1006', 0.6) + dot(52, 35.5, 0.7, '#c8361a') + dot(34.5, 19.5, 1.4, '#fffbe0') + dot(66.5, 16.5, 1.4, '#fffbe0') },
    'Blaze Charger': { env: 'forge', pal: { a: '#ff9a4a', b: '#b8261a', d: '#3e0b07', e: '#fff3b0' }, paint: (c, p) =>
      shadow(52, 71, 26) + ln('M74 40h18M78 46h16M76 52h14', '#ffb347', 1, 0.45) + flame(c, 78, 47, 20, 9, 4, 72) +
      sp(c, 'M68 54L81 64L83 61L72 51Z') + sp(c, 'M71 52L76 68L72 69.5L67 56Z') + sp(c, 'M74 66.5H78.5L78 70H74Z', '#1a0805') +
      se(c, 56, 50, 20, 10.5) + ln('M44 46q10 -3 22 -1', p.e, 0.7, 0.5) +
      sp(c, 'M40 54L28 60L27 64L31 63L42 58Z') + sp(c, 'M45 56L38 66L41 68L49 58Z') + sp(c, 'M37 65L40.5 67.6L38.4 70.5L35.4 68Z', '#1a0805') +
      sp(c, 'M43 47Q37 35 31 31L21 37Q23 42 31 43Q35 49 40 55Z') + sp(c, 'M31 28Q20 28 13 36Q15 42 24 41L33 36Z') +
      sp(c, 'M28 29Q31 20 24 15Q28 23 25 30Z', c.M, 0.6) + eye(23.5, 33, 1.5, '#fff3b0') + dot(15, 38, 0.8, p.d) +
      flame(c, 36, 37, 11, 6, 6) + flame(c, 40, 41, 12, 6, 7) + flame(c, 45, 45, 11, 6, 7) + flame(c, 31, 34, 9, 5, 5) + flame(c, 12, 40, 6, 3, -2, -80) },
    'Inferno Drake': { env: 'pyre', pal: { a: '#ff8a3a', b: '#a8201a', d: '#2e0806', e: '#fff3b0' }, paint: (c, p) =>
      shadow(56, 71, 24) + sp(c, 'M55 42Q61 17 84 9Q80 19 88 23Q80 27 86 33Q76 33 78 41Q68 39 63 47Z', c.D) + ln('M57 43L82 12M59 44L84 24M61 46L78 36', p.a, 0.7, 0.5) +
      sp(c, 'M45 41Q39 23 23 17Q27 25 21 29Q29 31 27 37Q35 37 41 45Z', c.D) +
      sp(c, 'M66 62Q84 70 93 60Q91 67 82 73Q72 75 62 67Z') + fp('M93 60l-2 6l4 -2Z', p.e) +
      se(c, 55, 57, 16, 12) + `<ellipse cx="52" cy="62" rx="8" ry="6" fill="${p.e}" opacity=".3"/>` + ln('M46 58h12M46 62h12M48 66h9', p.b, 0.7, 0.7) +
      sp(c, 'M46 66L44 72H52L51 66Z') + sp(c, 'M47 51Q41 39 37 33L47 29Q51 39 57 47Z') +
      sp(c, 'M45 22Q33 22 27 30L22 34Q30 37 38 36Q46 36 50 30Z') + sp(c, 'M26 36Q32 43 40 40L38 37Z', p.d) +
      sp(c, 'M45 22Q51 14 59 14Q53 18 49 26Z', '#e8d6b0', 0.7) + sp(c, 'M41 23Q43 15 49 12Q45 17 44 24Z', '#e8d6b0', 0.7) +
      eye(40, 27, 1.8, '#ffe066', '#2e0806') + glow(c, 18, 36, 12) + flame(c, 24, 35, 22, 14, 0, -100) },
    'Ash Phoenix': { env: 'pyre', pal: { a: '#ffd36e', b: '#e2481b', d: '#4a1006', e: '#fffbe0' }, paint: (c, p) =>
      glow(c, 50, 42, 30, 0.7) + flame(c, 50, 54, 22, 10, -4, 180) + flame(c, 45, 54, 18, 7, -6, 160) + flame(c, 55, 54, 18, 7, 6, 200) +
      sp(c, 'M46 41Q30 21 9 18Q17 24 13 28Q22 30 17 34Q26 36 21 40Q31 42 29 46Q37 46 44 50Z') + sp(c, 'M54 41Q70 21 91 18Q83 24 87 28Q78 30 83 34Q74 36 79 40Q69 42 71 46Q63 46 56 50Z') +
      ln('M44 44L16 25M43 46L20 35M43 48L28 43M56 44L84 25M57 46L80 35M57 48L72 43', p.e, 0.6, 0.6) +
      flame(c, 14, 26, 6, 4, -3, -60) + flame(c, 86, 26, 6, 4, 3, 60) +
      se(c, 50, 46, 7, 11) + `<ellipse cx="50" cy="49" rx="4" ry="6" fill="${p.e}" opacity=".45"/>` +
      flame(c, 50, 26, 11, 6, 0) + flame(c, 47, 27, 8, 4, -4) + flame(c, 53, 27, 8, 4, 4) + se(c, 50, 31, 6, 6) +
      sp(c, 'M51 31L58 34L51 36Z', c.M, 0.6) + eye(51, 30, 1.4, '#fffbe0', '#4a1006') },
    'Pyre Captain': { env: 'forge', pal: { a: '#ff8a5c', b: '#8a1e14', d: '#2e0806', e: '#ffe08a' }, paint: (c, p) =>
      sp(c, 'M30 52Q20 62 22 78H40Z', '#7a1414') + sp(c, 'M70 52Q80 62 78 78H60Z', '#7a1414') +
      glow(c, 78, 30, 16) + `<path d="M65 66L80 12L84 13.5L70 67Z" fill="${c.F}" stroke="${INK}" stroke-width=".8"/>` + flame(c, 81, 30, 12, 5, 2, 15) + flame(c, 78, 44, 10, 5, 2, 15) +
      sp(c, 'M61 64L75 69L74 72L60 67Z', c.M, 0.6) + sp(c, 'M28 78Q30 56 40 51H60Q70 56 72 78Z', '#4a2a22') + ln('M50 52V78', '#ffd36e', 0.6, 0.6) +
      se(c, 34, 55, 9, 6, c.M) + se(c, 66, 55, 9, 6, c.M) + flame(c, 50, 70, 11, 7) +
      flame(c, 50, 29, 17, 8) + flame(c, 45, 31, 11, 5, -4) + flame(c, 55, 31, 11, 5, 4) +
      sp(c, 'M40 47Q38 31 50 27Q62 31 60 47Q50 51 40 47Z', '#5a3a30') + sp(c, 'M40 47Q38 31 50 27L50 49Q44 50 40 47Z', '#6a4a3e') +
      fp('M42 39H58L57 42H43Z', '#120604') + eye(46, 40.5, 1.2, '#ffd36e') + eye(54, 40.5, 1.2, '#ffd36e') + ln('M50 28V47', '#ffd36e', 0.8) },
    'Kiln Matron': { env: 'kiln', pal: { a: '#c8643a', b: '#7a2a14', d: '#2a0c06', e: '#ffe08a' }, paint: (c, p) =>
      shadow(50, 72, 26) + sp(c, 'M28 72Q26 40 50 30Q74 40 72 72Z') +
      ln('M30 60H70M29 50H71M34 40H66M40 40v10M60 40v10M34 50v10M50 50v10M66 50v10M44 60v12M56 60v12', '#2a0c06', 0.6, 0.6) +
      glow(c, 50, 63, 18) + fp('M41 72V59Q50 49 59 59V72Z', '#ffe9a0') + fp('M41 72V59Q50 49 59 59V72Z', c.F, 0.6) + ln('M41 72V59Q50 49 59 59V72', '#2a0c06', 1.4) +
      fp('M45 72v-5l-1 -2l2 1l1 -1v7ZM53 72v-4l-1 -2l2 1l1 -1l1 2v4Z', '#3a0c06', 0.85) +
      sp(c, 'M30 50Q20 52 17 62L20 63Q24 56 32 56Z') + inkLn('M19 62L12 66M19 62L13 69', '#5a5a5a', 0.6) + dot(12, 67.5, 1.6, '#ffb347') + glow(c, 12, 67.5, 4) +
      sp(c, 'M70 50Q80 54 78 64L75 63Q75 58 68 56Z') +
      sp(c, 'M47 18H53V24H47Z', '#5a2416') + ln('M50 17q-3 -4 0 -7t1 -6', '#8a7a72', 1.1, 0.6) +
      se(c, 50, 27, 10, 8, '#d8784a') + ln('M44.5 26.5q2 -1.6 4 0M51.5 26.5q2 -1.6 4 0', '#2a0c06', 0.9) + dot(43.5, 29.5, 1.4, '#ff6a4a', 0.5) + dot(56.5, 29.5, 1.4, '#ff6a4a', 0.5) +
      ln('M47 30.5q3 2 6 0', '#2a0c06', 0.8) + dot(46.5, 26, 0.6, '#ffe08a') + dot(53.5, 26, 0.6, '#ffe08a') },
    'Sunfire Tyrant': { env: 'pyre', pal: { a: '#ffb347', b: '#b8261a', d: '#2a0604', e: '#fffbe0' }, paint: (c, p) =>
      glow(c, 50, 32, 30) + dot(50, 32, 13, '#fff1b0', 0.85) + rays(50, 32, 14, 40, '#ffe08a', 0.18) +
      sp(c, 'M16 78Q18 52 35 46H65Q82 52 84 78Z', c.D) + ln('M30 60l6 4l-2 6M64 56l4 6l6 2M46 66l4 -4l5 3', '#ffd36e', 0.8) +
      sp(c, 'M26 56Q14 44 16 31L23 31Q23 44 33 50Z', c.D) + sp(c, 'M74 56Q86 44 84 31L77 31Q77 44 67 50Z', c.D) +
      se(c, 19.5, 28, 5.5, 5, c.D) + se(c, 80.5, 28, 5.5, 5, c.D) + flame(c, 19.5, 25, 11, 7, -2) + flame(c, 80.5, 25, 11, 7, 2) +
      glow(c, 50, 60, 9) + dot(50, 60, 3, '#fffbe0') +
      sp(c, 'M40 47Q38 32 50 28Q62 32 60 47Q50 53 40 47Z', c.B) + crown(c, 50, 32, 22, 11) + flame(c, 50, 22, 9, 5) +
      fp('M43 39L48 40.5L43.5 41.5Z', '#fffbe0') + fp('M57 39L52 40.5L56.5 41.5Z', '#fffbe0') + fp('M46 45Q50 47.5 54 45Q50 46 46 45Z', '#fff1b0') },
    'Cinder Queen': { env: 'pyre', pal: { a: '#8a7a72', b: '#4a3a36', d: '#1a1210', e: '#ffb347' }, paint: (c, p) =>
      shadow(50, 74, 22) + sp(c, 'M33 44Q28 26 39 20L44 40Z', '#3a1612') + sp(c, 'M67 44Q72 26 61 20L56 40Z', '#3a1612') + ln('M33 44Q28 26 39 20M67 44Q72 26 61 20', '#ff7a1a', 0.7, 0.8) +
      sp(c, 'M29 78Q38 56 42 46H58Q62 56 71 78Z', c.D) + ln('M31 76q8 -3 12 0t12 0 14 0M36 64l4 4l-1 4M62 62l-3 5l2 3', '#ff8a3a', 0.8, 0.9) +
      sp(c, 'M43 51Q42 43 46 39H54Q58 43 57 51Z', c.B) + ln('M44 46q6 3 12 0', '#ffb347', 0.6) +
      flame(c, 44, 32, 14, 7, -8, -20) + flame(c, 56, 32, 14, 7, 8, 20) + se(c, 50, 31, 6, 7, '#a08a80') + crown(c, 50, 25, 12, 7) +
      eye(48, 31, 1, '#ffb347') + eye(52.4, 31, 1, '#ffb347') + ln('M49 35q1.2 .6 2.4 0', '#3a1612', 0.6) +
      inkLn('M60 66L65 24', '#2a1612', 0.9) + glow(c, 65, 22, 7) + dot(65, 22, 2.4, '#ffd36e') },
    // ===== Tide =====
    'Purse Moth': { env: 'grotto', pal: { a: '#b8d8e8', b: '#4a6a8a', d: '#122436', e: '#f0fbff' }, paint: (c, p) =>
      sp(c, 'M48 41Q30 15 13 21Q11 36 25 44Q35 49 48 47Z') + sp(c, 'M52 41Q70 15 87 21Q89 36 75 44Q65 49 52 47Z') +
      sp(c, 'M48 47Q34 50 30 62Q40 66 48 55Z', c.D) + sp(c, 'M52 47Q66 50 70 62Q60 66 52 55Z', c.D) +
      coin(28, 32, 5, 1) + coin(72, 32, 5, 1) + fp('M27 30h2v4h-2zM71 30h2v4h-2z', '#7a4a10') + scatter(rng(7), 10, [16, 22, 68, 22], (x, y) => dot(x, y, 0.5, '#e9fdff', 0.6)) +
      se(c, 50, 46, 4, 13, '#cfc1a0') + ln('M47 42h6M47 46h6M47 50h6', '#7a6a50', 0.6) + se(c, 50, 32, 4.5, 4, '#cfc1a0') +
      ln('M48 29Q44 19 38 17M52 29Q56 19 62 17', '#7a6a50', 0.7) + ln('M46 25l-2 -1M44 22l-2 0M54 25l2 -1M56 22l2 0', '#7a6a50', 0.5) +
      eye(48, 32, 1, '#ffd36e') + eye(52, 32, 1, '#ffd36e') + ln('M50 59V63', '#cfc1a0', 0.6) +
      sp(c, 'M42 67Q42 75 50 75Q58 75 58 67Q54 63 50 64Q46 63 42 67Z', '#8a5a2a') + sp(c, 'M46 64.5H54L53 66.5H47Z', c.M, 0.5) + coin(60, 73, 2) + coin(63.5, 74.5, 1.8) },
    'Tide Pup': { env: 'deep', pal: { a: '#d6e6ee', b: '#6a8a9e', d: '#1a2a36', e: '#e9fdff' }, paint: (c, p) =>
      sp(c, 'M16 74Q20 61 36 60H66Q80 62 86 74Z', c.R) + ln('M26 66q6 -2 10 0M64 66q6 -1 10 1', '#8ab0bc', 0.6, 0.6) +
      sp(c, 'M30 62Q20 58 15 51Q22 55 30 56Z') + sp(c, 'M29 63Q25 48 40 42Q54 36 66 44Q76 50 74 61Q60 67 29 63Z') +
      scatter(rng(4), 6, [36, 46, 26, 12], (x, y) => dot(x, y, 0.9, '#4a6a7e', 0.5)) + sp(c, 'M45 58Q41 66 32 67Q38 60 40 55Z') +
      se(c, 64, 41, 11, 10) + `<ellipse cx="66" cy="46" rx="6" ry="3.6" fill="#f4fbff" opacity=".9"/>` +
      peye(60.5, 39, 2.6) + peye(69, 39, 2.6) + `<ellipse cx="65" cy="44" rx="1.6" ry="1.1" fill="#120a0a"/>` +
      ln('M63 45.5q2 1.6 4 0', '#120a0a', 0.6) + ln('M61 45l-6 -1M61 46l-6 1M69 45l6 -1M69 46l6 1', '#ffffff', 0.35, 0.8) },
    'Shell Scout': { env: 'deep', pal: { a: '#ff9a6a', b: '#c84a2a', d: '#3a1008', e: '#fff3e0' }, paint: (c, p) =>
      shadow(48, 71, 22) + ln('M34 64l-5 7M40 66l-3 6M56 64l5 7M62 63l7 6', p.b, 1.6) +
      se(c, 40, 52, 16, 14, '#f1d6b0') + ln('M40 52m-2 0a2 2 0 1 1 4 0a5 5 0 1 1 -9 1a9 9 0 1 1 17 -3a13 13 0 1 1 -24 4', '#8a5a3a', 1) +
      sp(c, 'M30 42L26 36L33 39Z', '#e8c8a0') + sp(c, 'M40 38L39 31L44 37Z', '#e8c8a0') + sp(c, 'M50 40L54 34L54 42Z', '#e8c8a0') +
      sp(c, 'M52 58Q54 50 62 50Q68 52 68 60Q62 64 54 62Z') + sp(c, 'M54 62Q66 58 73 62Q72 68 64 69L56 66Z') + fp('M73 62L76 64L70 66Z', p.d) +
      inkLn('M58 50L59 40M63 50L66 41', p.b, 0.8) + `<circle cx="59" cy="39" r="2.3" fill="#fff"/>` + peye(59.4, 39, 1.6) + `<circle cx="66.3" cy="40" r="2.3" fill="#fff"/>` + peye(66.6, 40, 1.6) +
      sp(c, 'M64 47L84 36L86 39.5L66 50Z', c.M, 0.7) + ln('M70 44.3l1.6 3M76 41l1.6 3', '#7a4a10', 0.6) + glow(c, 86, 37, 5) + dot(86, 37.6, 1.6, '#e9fdff') +
      sp(c, 'M62 52Q66 48 66 46L68 48Q67 51 64 54Z') },
    'Reef Warden': { env: 'deep', pal: { a: '#7fe3d8', b: '#127a75', d: '#05302c', e: '#f0fff8' }, paint: (c, p) =>
      inkLn('M73 74L77 13', '#f08a6a', 1.4) + ln('M77 16l-4 -6M77 16l4 -7M77 16v-9M75 26l-4 -4M76 22l4 -3', '#f08a6a', 1.1) +
      sp(c, 'M40 72Q35 60 44 52H57Q63 62 59 70Q66 74 72 70Q69 79 56 77Z') + ln('M44 60q2 2 4 0t4 0 4 0M45 66q2 2 4 0t4 0', p.a, 0.5, 0.7) + sp(c, 'M70 70L78 64L77 74Z', c.D) +
      sp(c, 'M42 55Q40 42 44 36H58Q62 44 58 55Z', '#5fbfb0') + sp(c, 'M57 42Q66 42 71 36L74 38Q68 47 58 48Z', '#5fbfb0') +
      se(c, 34, 48, 12, 13, '#f3e3c8') + ln('M34 60L26 39M34 60L31 36M34 60L37 36M34 60L42 39M34 60L23 47M34 60L45 47', '#b89a72', 0.7) +
      sp(c, 'M44 27Q46 14 52 12Q54 18 61 20Q58 24 58 29Z', p.a) + ln('M48 15L50 26M53 16L54 26M57 20L56 27', p.d, 0.5, 0.6) +
      se(c, 51, 29, 6, 7, '#5fbfb0') + eye(49, 29, 1.1, '#e9fdff') + eye(53.5, 29, 1.1, '#e9fdff') + ln('M49.5 33q1.6 .8 3 0', p.d, 0.6) },
    'Tidecaller': { env: 'storm', pal: { a: '#8fd8ff', b: '#1b5d8b', d: '#06243a', e: '#e9fdff' }, paint: (c, p) =>
      sp(c, 'M60 78Q70 40 88 34Q97 34 99 43Q91 40 86 48Q84 62 93 78Z', c.W) + ln('M64 70Q72 44 88 36Q96 36 98 42', '#e9fdff', 0.9, 0.8) +
      sp(c, 'M34 75Q38 52 44 42H56Q62 52 66 75Z', c.D) + ln('M35 70q4 -3 8 0t8 0 8 0 8 0', p.a, 0.7, 0.8) +
      sp(c, 'M43 46Q34 38 30 27L33 26Q38 36 47 42Z', '#7ab8c8') + sp(c, 'M56 46Q62 50 60 58L57 57Q58 51 54 49Z', '#7ab8c8') +
      sp(c, 'M21 21Q30 13 38 21Q34 28 26 30Z', '#f3dcc0') + ln('M24 22q4 -4 9 -1M26 26q3 -2 6 0', '#a87a5a', 0.6) +
      ln('M18 14q-4 6 0 12M14 10q-6 10 0 20', p.e, 0.8, 0.6) +
      sp(c, 'M40 41Q38 26 50 23Q62 26 60 41Q55 45 50 45Q45 45 40 41Z', c.B) + `<ellipse cx="50" cy="37" rx="6.5" ry="6" fill="#7ab8c8"/>` +
      eye(47.5, 36, 1.2, '#e9fdff') + eye(52.5, 36, 1.2, '#e9fdff') + ln('M48 40.5q2 1 4 0', p.d, 0.6) +
      scatter(rng(13), 8, [62, 26, 34, 20], (x, y) => dot(x, y, 0.7, '#e9fdff', 0.7)) },
    'Coin Eel': { env: 'grotto', pal: { a: '#9fe8c8', b: '#1a7a6a', d: '#05302c', e: '#f0fff8' }, paint: (c, p) =>
      sp(c, 'M26 73Q34 59 50 57Q67 59 74 73Z', c.M) + coin(40, 64, 4) + coin(50, 60, 4.4) + coin(60, 65, 4) + coin(46, 69, 3.6) + coin(57, 70, 3.4) + coin(33, 70, 3.2) +
      inkLn('M20 67Q16 50 34 50Q52 50 56 40Q60 28 72 30', p.b, 6) + ln('M20 67Q16 50 34 50Q52 50 56 40Q60 28 72 30', p.a, 2, 0.6) + ln('M22 64Q19 52 34 52', '#fff', 0.5, 0.5) +
      ln('M24 56Q30 46 40 47M52 44Q58 32 68 31', p.e, 0.7, 0.6) + fp('M20 67l-6 4l5 1Z', p.b) +
      se(c, 74, 30, 7, 5, null, -15) + fp('M79 31l4 1.5l-4 1.5Z', '#05302c') + coin(84, 31.5, 2.2, 1) + eye(74, 28, 1.5, '#e9ff8a', '#05302c') +
      star4(36, 60, 2.2, '#fff8d0') + star4(62, 58, 1.8, '#fff8d0') },
    'Storm Siren': { env: 'storm', pal: { a: '#7ad8ff', b: '#1b5d9b', d: '#061a3a', e: '#e9fdff' }, paint: (c, p) =>
      sp(c, 'M20 75Q26 62 44 60H64Q78 64 82 75Z', c.R) +
      sp(c, 'M44 62Q38 71 52 73Q66 75 74 67Q80 61 85 65Q83 56 74 58Q66 66 56 64Z') + ln('M54 68q2 2 4 0t4 0M60 71q2 1.6 4 0', p.a, 0.5, 0.7) + sp(c, 'M84 64L91 58L89 68Z', c.D) +
      sp(c, 'M46 27Q30 21 16 33Q25 31 23 40Q31 35 33 46Q39 37 44 40Z', '#2a3a8a') + ln('M44 28Q32 25 22 33M42 31Q34 31 28 38', p.a, 0.6, 0.6) +
      sp(c, 'M44 63Q42 49 46 40H56Q60 50 58 63Z', '#bfe6f0') + sp(c, 'M56 44Q64 36 68 22L71 23Q68 40 58 49Z', '#bfe6f0') +
      glow(c, 70, 20, 8) + ln('M70 20l4 -6l-2 0l4 -6', '#ffffff', 0.8) +
      se(c, 51, 31, 6, 7, '#bfe6f0') + fp('M45 28Q48 22 54 23Q57 25 57 29Q52 25 45 28Z', '#2a3a8a') +
      eye(48.8, 30.5, 1.1, '#e9fdff') + eye(53.2, 30.5, 1.1, '#e9fdff') + `<ellipse cx="51.2" cy="34.6" rx="1.2" ry="1.4" fill="#1a0a1a"/>` +
      ln('M58 33q3 2 0 5M61 31q5 4 0 9', p.e, 0.6, 0.7) },
    'Tide Oracle': { env: 'deep', pal: { a: '#b89aff', b: '#5a3aa8', d: '#1a0e3a', e: '#f4eaff' }, paint: (c, p) =>
      inkLn('M38 50Q26 58 30 68Q34 74 26 76', p.b, 3) + inkLn('M62 50Q74 58 70 68Q66 74 74 76', p.b, 3) + inkLn('M44 52Q40 64 34 72', p.b, 2.6) + inkLn('M56 52Q60 64 66 72', p.b, 2.6) +
      ln('M30 66v.1M31 70v.1M70 66v.1M69 70v.1M38 66v.1M62 66v.1', '#e8d8ff', 1.4) +
      glow(c, 50, 62, 13, 1, 'G2') + `<circle cx="50" cy="62" r="7" fill="${c.P}" stroke="${INK}" stroke-width=".6"/>` + dot(47.5, 59.5, 1.8, '#fff', 0.9) +
      inkLn('M42 53Q40 60 45 64', p.b, 2.2) + inkLn('M58 53Q60 60 55 64', p.b, 2.2) +
      sp(c, 'M33 45Q31 18 50 14Q69 18 67 45Q59 53 50 53Q41 53 33 45Z') + scatter(rng(21), 7, [36, 18, 28, 20], (x, y) => dot(x, y, 0.9, '#d8c0ff', 0.55)) +
      sp(c, 'M34 33Q50 39 66 33L66 36Q50 42 34 36Z', c.M, 0.6) + dot(50, 38.4, 1.4, '#7fe3ff') +
      eye(50, 26, 2.6, '#7fe3ff', '#1a0e3a') + ln('M40 44q3 -1.6 6 0M54 44q3 -1.6 6 0', '#1a0e3a', 0.9) },
    'Pearl Broker': { env: 'grotto', pal: { a: '#c8a08a', b: '#6a4a3a', d: '#2a1810', e: '#f4f0ff' }, paint: (c, p) =>
      shadow(50, 74, 26) + se(c, 50, 62, 24, 14) + sp(c, 'M40 50Q50 54 60 50L62 74H38Z', '#1b6d9b') + dot(50, 58, 1, '#ffd36e') + dot(50, 64, 1, '#ffd36e') + dot(50, 70, 1, '#ffd36e') +
      sp(c, 'M68 56Q78 50 79 43L82 44Q83 53 72 60Z') + glow(c, 81, 40, 7, 1, 'G2') + `<circle cx="81" cy="40" r="3.6" fill="${c.P}" stroke="${INK}" stroke-width=".5"/>` + dot(80, 39, 1, '#fff') +
      se(c, 50, 38, 16, 13) + scatter(rng(26), 9, [40, 47, 20, 3], (x, y) => dot(x, y, 1, '#f4f0ff')) +
      sp(c, 'M45 47Q44 59 47 63Q48 56 48.5 47Z', '#f4ead0', 0.6) + sp(c, 'M55 47Q56 59 53 63Q52 56 51.5 47Z', '#f4ead0', 0.6) +
      se(c, 45, 44, 6, 5) + se(c, 55, 44, 6, 5) + scatter(rng(9), 8, [40, 42, 20, 4], (x, y) => dot(x, y, 0.4, '#2a1810')) + `<ellipse cx="50" cy="41" rx="2" ry="1.4" fill="#2a1810"/>` +
      peye(43, 35, 1.4) + peye(57, 35, 1.4) + `<circle cx="57" cy="35" r="3" fill="#cfefff" fill-opacity=".25" stroke="${INK}" stroke-width="1.2"/><circle cx="57" cy="35" r="3" fill="none" stroke="#ffd36e" stroke-width=".6"/>` + ln('M60 37Q64 46 60 52', '#ffd36e', 0.4) +
      sp(c, 'M38 27Q50 21 62 27L60 29Q50 25 40 29Z', '#1a2a3a') + sp(c, 'M42 27Q42 15 50 15Q58 15 58 27Z', '#1a2a3a') + fp('M42.4 24H57.6V26H42.4Z', '#ffd36e') },
    'Abyss Choir': { env: 'abyss', pal: { a: '#6a7ac8', b: '#2a346a', d: '#0a1022', e: '#c8fff4' }, paint: (c, p) => {
      const ang = (x, y, s, flip, glowOp) => `<g transform="translate(${x} ${y}) scale(${flip ? -s : s} ${s})">` +
        glow(c, 14, -19, 7, glowOp) + ln('M-2 -11Q4 -24 14 -20', '#4a5a8a', 0.8) + dot(14, -19.5, 2.2, '#c8fff4') +
        sp(c, 'M-14 0L-22 -7L-20 7Z', c.D) + sp(c, 'M-14 0Q-14 -12 0 -12Q12 -12 16 -2L18 4Q10 12 0 12Q-12 12 -14 0Z') +
        fp('M5 -2Q15 -1 18 4Q12 10 3 6Z', '#02040a') + fp('M7 -1l1 2.4l1 -2.2l1 2.4l1 -2.2l1 2.6l1 -2.4M5 5.6l1.2 -2l1 2l1.2 -2l1 2.2l1.2 -2', '#e8f4ff') +
        eye(2, -5, 1.8, '#c8fff4') + ln('M-6 -8q-2 4 0 8M-9 -6q-2 4 0 6', '#8a9ad8', 0.5, 0.6) + '</g>';
      return ang(28, 44, 0.75, false, 0.7) + ang(73, 40, 0.75, true, 0.7) + ang(48, 58, 1.15, false, 1) +
        ln('M70 56q4 -6 8 -4M74 62q6 -8 12 -5', '#c8fff4', 0.6, 0.5) + fp('M84 50a1.5 1.2 0 1 0 .1 0ZM84.6 50.2V44l3 1', '#c8fff4', 0.6);
    } },
    'Maelstrom Queen': { env: 'storm', pal: { a: '#8fe6ff', b: '#1b6d9b', d: '#06243a', e: '#e9fdff' }, paint: (c, p) =>
      fp('M40 72Q30 42 18 6H82Q70 42 60 72Z', c.W, 0.55) + ln('M30 30Q50 38 70 30M34 44Q50 50 66 44M38 56Q50 61 62 56M26 18Q50 26 74 18', '#e9fdff', 0.7, 0.5) +
      `<ellipse cx="50" cy="70" rx="34" ry="7" fill="#06243a" stroke="#e9fdff" stroke-width=".7" stroke-opacity=".7"/>` + ln('M22 70Q36 64 52 66T74 70M30 72Q44 76 62 72', '#9fe8ff', 0.8, 0.8) + ln('M38 69Q50 66 60 69', '#ffffff', 0.6, 0.8) +
      inkLn('M65 72L70 15', '#c89a3a', 0.9) + sp(c, 'M63 19L64 9L67 16L70 5L73 16L76 9L77 19Z', c.M, 0.6) +
      ln('M44 32Q34 44 38 60Q40 66 34 70M56 32Q66 44 62 58', p.a, 2.6, 0.8) +
      sp(c, 'M42 67Q40 47 45 39H55Q60 47 58 67Z', '#9fd8e6') + sp(c, 'M55 45Q62 44 66 38L68 40Q64 48 56 50Z', '#9fd8e6') +
      se(c, 50, 31, 6, 7, '#9fd8e6') + sp(c, 'M42 26L43 14L47 21L50 10L53 21L57 14L58 26Z', c.M, 0.6) + dot(50, 21, 1.2, '#f4f0ff') + dot(44.5, 20, 0.8, '#f4f0ff') + dot(55.5, 20, 0.8, '#f4f0ff') +
      eye(48, 31, 1.1, '#ffffff') + eye(52.4, 31, 1.1, '#ffffff') + ln('M48.6 35q1.6 .8 3 0', p.d, 0.6) },
    'Tidal Sovereign': { env: 'storm', pal: { a: '#7a9ad0', b: '#2a4a7a', d: '#0a1830', e: '#e9fdff' }, paint: (c, p) =>
      sp(c, 'M12 66Q16 38 44 25Q66 15 82 29Q91 39 85 53Q71 66 40 68Z') + fp('M24 62Q44 64 72 56L80 52Q70 64 40 67Q28 67 24 62Z', '#c8d8f0', 0.8) +
      ln('M28 64Q48 64 74 56M32 66Q52 66 76 58', '#5a7aa8', 0.6, 0.8) + scatter(rng(33), 8, [30, 30, 40, 18], (x, y) => `<circle cx="${n1(x)}" cy="${n1(y)}" r="1" fill="#c8d0d8" stroke="${INK}" stroke-width=".3"/>`) +
      eye(68, 36, 2.2, '#e9fdff', '#0a1830') + ln('M64 33q4 -3 8 0', '#0a1830', 0.8) + ln('M82 46q-4 4 -10 4', '#0a1830', 0.9) +
      crown(c, 56, 24, 18, 10) + ln('M22 58v14M34 62v12M70 56v14M78 52v12', '#e9fdff', 0.8, 0.6) +
      fp('M4 68q8 -6 16 -1q10 -6 20 0q12 -5 22 0q12 -6 24 0q8 -3 14 0V80H4Z', '#e9fdff', 0.85) + coin(30, 74, 2.2) + coin(66, 75, 2) },
    // ===== Stone =====
    'Pebble Guard': { env: 'quarry', pal: { a: '#e0cfa6', b: '#8a7454', d: '#2a221a', e: '#ffe6a0' }, paint: (c, p) =>
      shadow(48, 71, 18) + inkLn('M64 72L70 18', '#7a4a2a', 1) + sp(c, 'M68 20L71 9L73.5 20Z', '#d8dce0', 0.6) +
      se(c, 41, 70, 4, 2.4, c.B) + se(c, 53, 70, 4, 2.4, c.B) + se(c, 47, 56, 14, 13, c.B) + scatter(rng(6), 9, [37, 47, 20, 18], (x, y) => dot(x, y, 0.6, '#5a5040', 0.7)) +
      se(c, 47, 38, 9, 8, c.B) + se(c, 47, 29.5, 5, 3.4, c.B) + fp('M38 52q3 -2 6 0', '#6a9a3a') + fp('M43 31q2 -2 5 -1q-1 2 -5 1Z', '#6a9a3a') +
      ln('M42 34.5l4 1.3M53 34.5l-4 1.3', '#2a251e', 1.1) + peye(44, 37.5, 1.5) + peye(51, 37.5, 1.5) + ln('M45 42h4', '#2a251e', 0.8) +
      sp(c, 'M58 52Q64 46 66 40L69 41Q67 50 60 56Z', c.B) + se(c, 32, 56, 10, 11, '#9a6a3a') + `<ellipse cx="32" cy="56" rx="10" ry="11" fill="none" stroke="#c89a3a" stroke-width="1.2"/>` +
      ln('M32 45v22M23 56h18', '#6a4424', 0.6, 0.7) + se(c, 32, 56, 2.6, 2.6, c.M) },
    'Moss Turtle': { env: 'grove', pal: { a: '#b8b098', b: '#6a6450', d: '#22201a', e: '#e8ff9a' }, paint: (c, p) =>
      shadow(50, 71, 30) + sp(c, 'M28 64L26 72H34L35 64Z', '#7a9060') + sp(c, 'M64 64L63 72H71L70 64Z', '#7a9060') + sp(c, 'M20 62Q16 64 14 62Q17 59 21 59Z', '#7a9060') +
      sp(c, 'M73 56Q78 50 86 51Q91 55 88 60Q83 63 76 61Z', '#8aa070') + peye(84, 54.6, 1.4) + ln('M85 58.6q2 .4 3 -1', '#22201a', 0.6) +
      sp(c, 'M21 62Q21 34 48 31Q75 34 76 62Z', c.B) + ln('M48 36L58 42V52L48 58L38 52V42ZM38 42L28 47M58 42L68 47M38 52L27 59M58 52L69 59M48 58V62M48 36V32', '#2a261e', 0.9, 0.7) +
      fp('M23 52Q22 34 48 31Q72 33 75 50Q70 46 66 49Q62 42 56 46Q52 39 46 44Q40 39 36 46Q30 42 28 50Q25 47 23 52Z', '#6aa034') + ln('M30 41Q40 34 52 34', '#9ad04a', 0.7, 0.7) +
      dot(36, 38, 1.1, '#ffffff') + dot(36, 38, 0.45, '#ffd36e') + dot(58, 36, 1.1, '#ffb0d0') + dot(58, 36, 0.45, '#ffd36e') + dot(46, 34, 0.9, '#ffffff') +
      ln('M64 38v-3', '#e8dcc0', 1) + fp('M61.5 35.5a2.6 2 0 0 1 5.2 0Z', '#d0432f') + `<rect x="19" y="60" width="59" height="5" rx="2.5" fill="#6a6450" stroke="${INK}" stroke-width=".8"/>` },
    'Root Sprout': { env: 'grove', pal: { a: '#c89a62', b: '#6a4626', d: '#2a1a0c', e: '#c8ff8a' }, paint: (c, p) =>
      shadow(50, 71, 16) + inkLn('M42 64Q36 70 30 70Q26 70 25 73M47 66Q46 72 42 75M54 66Q56 72 61 74M58 63Q64 68 71 68', '#6a4a2a', 1.2) +
      sp(c, 'M40 58Q32 56 28 50L30 48Q34 53 41 54Z') + sp(c, 'M60 58Q68 56 71 50L69 48Q66 53 59 54Z') +
      sp(c, 'M38 64Q34 48 44 40Q50 36 56 40Q66 48 62 64Q50 70 38 64Z') + ln('M42 46q2 6 0 12M50 44v4M57 48q-2 6 0 10', '#2a1a0c', 0.6, 0.6) +
      eye(45, 53, 2, '#c8ff8a', '#1a3a0a') + eye(55, 53, 2, '#c8ff8a', '#1a3a0a') + `<ellipse cx="50" cy="59" rx="1.4" ry="1.7" fill="#1a0c06"/>` +
      inkLn('M50 39V25', '#5aa030', 0.8) + sp(c, 'M50 28Q38 16 29 22Q37 33 50 28Z', '#7ac03a') + sp(c, 'M50 26Q62 9 75 15Q67 31 50 26Z', '#8ad04a') +
      ln('M50 28Q40 23 32 22M50 26Q62 17 72 15', '#2a5a10', 0.5, 0.7) + dot(72, 18.5, 1.3, '#e9fdff', 0.9) },
    'Boulder Ox': { env: 'cliff', pal: { a: '#d4b48a', b: '#6e543c', d: '#22180f', e: '#ffc85a' }, paint: (c, p) =>
      shadow(50, 72, 32) + sp(c, 'M34 62H42L41 72H33Z', c.B) + sp(c, 'M68 62H76L77 72H69Z', c.B) +
      sp(c, 'M24 66Q20 44 38 38L64 36Q83 40 83 57Q81 68 70 68L30 70Z', c.B) + ln('M44 42l4 8l-3 6M64 44l-3 7l4 5M54 58l6 2', '#2a261e', 0.8, 0.7) +
      fp('M40 38Q52 33 64 36Q70 38 74 42Q62 39 52 40Q44 41 40 38Z', '#6a8a3a', 0.9) +
      sp(c, 'M44 62H52L51 72H43Z', c.B) + sp(c, 'M30 46Q18 46 13 56Q15 66 26 66Q34 62 36 54Z', c.B) +
      sp(c, 'M24 47Q14 37 5 41Q11 43 14 49Z', '#e8dcc0') + sp(c, 'M31 45Q35 33 45 30Q39 37 37 45Z', '#e8dcc0') +
      eye(24, 52, 1.6, '#ffc85a', '#22201a') + `<circle cx="17" cy="62" r="2.4" fill="none" stroke="#e0a83a" stroke-width="1"/>` + dot(15, 59, 0.7, '#22201a') + dot(19.5, 60, 0.7, '#22201a') +
      dot(9, 63, 2, '#d8c8a8', 0.4) + dot(6, 60, 1.4, '#d8c8a8', 0.3) },
    'Cairn Mason': { env: 'quarry', pal: { a: '#c8c0b4', b: '#5e5a56', d: '#1e1c1a', e: '#ffc85a' }, paint: (c, p) =>
      shadow(50, 72, 26) + se(c, 78, 68, 9, 4, c.B) + se(c, 78, 61.4, 7, 3.4, c.B) + se(c, 78, 55.6, 5, 3, c.B) + se(c, 78, 50.6, 3.2, 2.2, c.B) +
      sp(c, 'M32 72Q30 52 40 46H58Q66 52 64 72Z', '#7a5a3a') + sp(c, 'M33 62H64L64 65H33Z', c.M, 0.6) +
      sp(c, 'M40 48Q30 52 31 62L35 62Q36 55 43 53Z', c.B) + se(c, 33, 63, 3.5, 3, c.B) +
      inkLn('M60 54L67 24', '#7a4a2a', 1) + sp(c, 'M59 18L77 22.5L75 31L57 26.5Z', '#9aa0a8') + sp(c, 'M57 50Q62 52 64 46L61 44Q60 48 56 47Z', c.B) + se(c, 61, 50, 3.5, 3, c.B) +
      se(c, 48, 38, 9, 8, c.B) + sp(c, 'M39 39Q39 55 48 57Q57 55 57 39Q48 44 39 39Z', '#d8cfc0') + ln('M44 44v8M48 45v10M52 44v8', '#9a9080', 0.5) +
      sp(c, 'M38.5 36Q39 26 48 26Q57 26 57.5 36Z', c.M) + ln('M38 36H58', '#7a4a10', 1) + eye(44.5, 38, 1, '#ffc85a') + eye(51.5, 38, 1, '#ffc85a') + ln('M42 36.4l4 .6M54 36.4l-4 .6', '#2a251e', 0.9) },
    'Rootwarden': { env: 'grove', pal: { a: '#b08a5a', b: '#5a3a1e', d: '#22140a', e: '#b8ff7a' }, paint: (c, p) =>
      shadow(50, 72, 22) + inkLn('M70 74Q66 50 73 30Q70 22 73 14', '#6a4626', 1.2) + leaf(73, 26, 6, -30, '#7ac03a') + leaf(71, 36, 5, 200, '#6ab030') + glow(c, 73, 13, 8, 1, 'G2') + dot(73, 13, 2, '#e8ffb0') +
      inkLn('M36 72Q30 74 26 72M62 72Q68 74 74 73M44 73Q42 76 38 77', '#5a3a1e', 1.2) +
      sp(c, 'M36 73Q38 50 40 36Q50 30 60 36Q62 50 64 73Z') + ln('M42 44q-1 12 1 26M50 48v20M57 42q2 14 0 28', '#22140a', 0.6, 0.6) +
      inkLn('M42 36Q38 26 33 20M40 30L30 26M58 36Q63 24 66 18M60 28L68 26', '#5a3a1e', 1.1) +
      se(c, 32, 19, 6, 4, '#5a9a2a') + se(c, 66, 17, 6, 4, '#6aaa30') + se(c, 28, 25, 4, 3, '#4a8a20') + se(c, 69, 25, 4, 3, '#5a9a2a') +
      sp(c, 'M40 48Q30 52 28 62L32 63Q34 56 42 54Z') + sp(c, 'M60 48Q66 50 69 54L67 57Q63 53 59 54Z') +
      eye(45.5, 44, 1.6, '#b8ff7a') + eye(54.5, 44, 1.6, '#b8ff7a') + `<ellipse cx="50" cy="52" rx="2" ry="3" fill="#120a04"/>` + fp('M38 60q4 -3 8 0q-4 2 -8 0Z', '#6a9a3a') },
    'Granite Titan': { env: 'cliff', pal: { a: '#dcb8a8', b: '#6a4e46', d: '#1e1614', e: '#ffc85a' }, paint: (c, p) =>
      shadow(50, 74, 36) + sp(c, 'M18 78Q16 46 32 38H68Q84 46 82 78Z', c.B) +
      sp(c, 'M28 42Q16 46 13 60L23 62Q25 52 32 48Z', c.B) + sp(c, 'M72 42Q84 46 87 60L77 62Q75 52 68 48Z', c.B) +
      se(c, 17, 64, 8.5, 7.5, c.B) + se(c, 83, 64, 8.5, 7.5, c.B) + ln('M13 62h8M79 62h8', '#2a261e', 0.6, 0.7) +
      ln('M40 50L50 56L60 50M50 56V68M44 62h12', '#ffc85a', 2.2, 0.35) + ln('M40 50L50 56L60 50M50 56V68M44 62h12', '#fff1b0', 0.8) +
      ln('M24 70l6 -4l2 4M70 66l6 4', '#2a261e', 0.7, 0.7) + sp(c, 'M40 39Q40 24 50 22Q60 24 60 39Z', c.B) +
      fp('M43 31H48.5L48 33.4H43.6ZM51.5 31H57L56.4 33.4H52Z', '#ffc85a') + ln('M42 29.4l7 1M58 29.4l-7 1', '#1e1c1a', 1.2) +
      dot(26, 34, 1.2, '#8a8478') + dot(78, 30, 1, '#8a8478') },
    'Mountain Heart': { env: 'cave', pal: { a: '#a8a0b0', b: '#4a4452', d: '#16121a', e: '#ffd27a' }, paint: (c, p) =>
      shadow(50, 72, 34) + sp(c, 'M16 74Q18 46 34 36Q50 28 66 36Q82 46 84 74Z', c.B) +
      ln('M50 52L30 42L22 50M50 52L72 40L80 48M50 52L26 64M50 52L76 66M50 52L44 34', '#ffb347', 2.2, 0.3) + ln('M50 52L30 42L22 50M50 52L72 40L80 48M50 52L26 64M50 52L76 66M50 52L44 34', '#ffe9a0', 0.6) +
      glow(c, 50, 52, 24) + `<path d="M50 67L36 51Q32 41 42 39Q48 39 50 45Q52 39 58 39Q68 41 64 51Z" fill="${c.P}" stroke="${INK}" stroke-width=".9"/>` +
      ln('M50 45L50 67M42 39L46 52L50 67M58 39L54 52L50 67M36 51H64', '#7a2a10', 0.5, 0.6) + fp('M42 41Q38 43 39 48L44 46Z', '#fffbe0', 0.7) +
      ln('M24 56l5 -3M70 58l6 2M38 66l4 3', '#16121a', 0.7, 0.7) },
    'Basalt Bastion': { env: 'cliff', pal: { a: '#7a7e88', b: '#3a3c44', d: '#121318', e: '#ffb347' }, paint: (c, p) =>
      shadow(50, 74, 32) + sp(c, 'M30 66H40L40 74H29Z', c.D) + sp(c, 'M60 66H70L71 74H60Z', c.D) +
      sp(c, 'M22 68V34L26 30L30 34V68Z', c.D) + sp(c, 'M70 68V32L74 28L78 32V68Z', c.D) +
      sp(c, 'M30 68V24L35 20L40 24V68Z') + sp(c, 'M60 68V22L65 18L70 22V68Z') + sp(c, 'M40 68V16L45 12H55L60 16V68Z') +
      sp(c, 'M38 16H62V20H38Z', c.D) + fp('M39 13h4v3h-4zM48 13h4v3h-4zM57 13h4v3h-4z', '#3a3c44') +
      fp('M43 68V54Q50 46 57 54V68Z', '#0a0806') + ln('M45 68V54M48 68V51M52 68V51M55 68V54M43 58H57M43 63H57', '#7a6a5a', 0.6) + fp('M44 68l1 -3l1 3l1 -3l1 3l1 -3l1 3l1 -3l1 3l1 -3l1 3l1 -3l1 3Z', '#ffb347', 0.85) +
      fp('M44 30h4v6h-4zM52 30h4v6h-4z', '#ffb347') + glow(c, 46, 33, 5) + glow(c, 54, 33, 5) +
      fp('M30 44q4 -4 10 -2q-2 6 -10 6ZM62 50q4 -2 8 0v4q-4 0 -8 -4Z', '#4a6a2a', 0.9) + ln('M33 30v30M65 28v30M74 36v28M26 40v24', '#121318', 0.5, 0.6) },
    'Quarry Drummer': { env: 'quarry', pal: { a: '#b4bccc', b: '#4a5266', d: '#161a22', e: '#ffc85a' }, paint: (c, p) =>
      sp(c, 'M24 60Q24 34 50 30Q76 34 76 60Z', c.B) + sp(c, 'M30 42Q18 36 20 22L25 22Q25 33 35 37Z', c.B) + sp(c, 'M70 42Q82 36 80 22L75 22Q75 33 65 37Z', c.B) +
      inkLn('M22 22L30 10', '#7a4a2a', 0.8) + se(c, 31, 9, 3.6, 3, c.B) + inkLn('M78 22L70 10', '#7a4a2a', 0.8) + se(c, 69, 9, 3.6, 3, c.B) +
      se(c, 50, 25, 9, 8, c.B) + ln('M43 22l5 1.5M57 22l-5 1.5', '#22201a', 1.3) + eye(46, 25, 1.1, '#ffc85a') + eye(54, 25, 1.1, '#ffc85a') + fp('M46 29Q50 32 54 29Q50 30 46 29Z', '#22201a') +
      sp(c, 'M29 56H71L68 75H32Z', '#8a5a32') + ln('M31 58L38 74L45 58L52 74L59 58L66 74', '#e8d8b0', 0.7) + ln('M30 62H70M31 70H69', '#5a3a1e', 0.8) +
      `<ellipse cx="50" cy="56" rx="21" ry="4.4" fill="#e0d0a8" stroke="${INK}" stroke-width=".9"/>` + ln('M14 48q-4 6 0 12M10 44q-6 10 0 20M86 48q4 6 0 12M90 44q6 10 0 20', '#ffc85a', 0.9, 0.7) +
      dot(40, 52, 1.2, '#f0d8a8', 0.6) + dot(60, 51, 1, '#f0d8a8', 0.6) },
    'Worldroot': { env: 'grove', pal: { a: '#a8825a', b: '#4a321c', d: '#1a1008', e: '#ffe9a0' }, paint: (c, p) =>
      inkLn('M34 72Q22 70 10 75M38 72Q32 76 24 79M62 72Q76 70 90 75M58 72Q66 77 74 79M48 74v6', '#4a321c', 1.6) +
      se(c, 20, 73, 6, 3.4, c.B) + se(c, 80, 73, 6, 3.4, c.B) +
      sp(c, 'M32 75Q37 56 38 42Q30 32 21 34Q29 25 40 30Q44 20 50 18Q57 20 60 30Q71 25 79 34Q70 32 62 42Q63 56 68 75Z') +
      ln('M42 44q-2 14 0 28M50 48v24M58 44q2 14 0 28', '#1a1008', 0.6, 0.6) +
      se(c, 32, 20, 13, 9, '#3a7a20') + se(c, 68, 20, 13, 9, '#3a7a20') + se(c, 50, 13, 14, 9, '#4a8a2a') + se(c, 22, 30, 8, 5, '#2e6a1a') + se(c, 78, 30, 8, 5, '#2e6a1a') +
      ln('M24 17q8 -5 16 -2M42 9q8 -4 16 0M62 17q7 -4 14 -1', '#9ad04a', 0.8, 0.7) +
      eye(44, 48, 1.8, '#ffe9a0') + eye(56, 48, 1.8, '#ffe9a0') + ln('M41 45q3 -2 6 0M53 45q3 -2 6 0', '#1a1008', 0.9) +
      glow(c, 50, 61, 10) + `<ellipse cx="50" cy="61" rx="3.4" ry="4.4" fill="#fff1b0" stroke="${INK}" stroke-width=".6"/>` +
      motes(rng(34), 8, '#e8ff9a', [10, 30, 80, 30]) },
    'Avalanche Lord': { env: 'peaks', pal: { a: '#b8c4d4', b: '#5a667a', d: '#1a2030', e: '#9fe8ff' }, paint: (c, p) =>
      shadow(50, 74, 38) + sp(c, 'M8 78L28 38L40 30L50 24L60 30L72 38L92 78Z', c.B) +
      fp('M28 38L22 50L27 48L30 53L34 46L38 50L40 30Z', '#f4faff') + fp('M72 38L78 50L73 48L70 53L66 46L62 50L60 30Z', '#f4faff') +
      sp(c, 'M30 46Q16 54 14 68L22 70Q24 58 34 52Z', c.B) + sp(c, 'M70 46Q84 54 86 68L78 70Q76 58 66 52Z', c.B) +
      se(c, 12, 70, 5, 4, '#f4faff') + se(c, 18, 74, 4, 3, '#e4eef8') + se(c, 88, 70, 5, 4, '#f4faff') + se(c, 82, 74, 4, 3, '#e4eef8') +
      ln('M40 56l6 4l-2 6M58 60l4 -4l6 2', '#1a2030', 0.8, 0.7) +
      sp(c, 'M42 29Q34 21 35 11Q38 19 44 25Z', '#dff4ff') + sp(c, 'M58 29Q66 21 65 11Q62 19 56 25Z', '#dff4ff') +
      sp(c, 'M40 40Q40 26 50 22Q60 26 60 40Q50 44 40 40Z', c.B) + fp('M42 30Q50 22 58 30Q54 27 50 28Q46 27 42 30Z', '#f4faff') +
      eye(45.5, 34, 1.4, '#9fe8ff') + eye(54.5, 34, 1.4, '#9fe8ff') + ln('M43 31.6l5 1.4M57 31.6l-5 1.4', '#1a2030', 1.1) },
  };

  // --- fallback archetypes for cards not in ART_CARDS (kept from v1 art) ---
  const VARIANT = {
    Ember: [['imp', /imp|fiend|devil|gremlin|goblin|scamp|rascal/i], ['drake', /drake|dragon|salamander|wyrm|phoenix|whelp|raptor/i], ['wisp', /wisp|spirit|flame|blaze|cinder|candle|torch|brazier|spark|ash|kindl|herald|inferno/i]],
    Tide: [['jelly', /jelly|medusa|anemone|bloom|polyp|mist|foam/i], ['fish', /eel|fish|shark|ray|serpent|carp|pike|angler|pup|current/i]],
    Stone: [['golem', /golem|guard|sentinel|warden|giant|colossus|titan|bulwark|keeper|mason/i], ['crystal', /crystal|geode|shard|gem|obelisk|idol|quartz|pebble|monolith|heart/i]],
    Neutral: [['ram', /ram|siege|catapult|engine/i], ['warden', /mirror|warden|shield/i], ['drill', /drill|forge|smith/i], ['artificer', /artificer|grand|master|king|queen/i],
      ['clerk', /clerk|bounty|merchant|broker|banker/i], ['apprentice', /apprentice|smith|novice/i], ['tinker', /tinker|gnome|mechanic/i], ['sentry', /sentry|sentinel|guard|automaton|construct|golem/i]],
  };
  const FALLBACK_ENV = { Ember: 'forge', Tide: 'deep', Stone: 'cliff', Neutral: 'workshop', Other: 'cave' };
  function artKind(u) {
    const tribe = TRIBES.includes(u.tribe) ? u.tribe : 'Other';
    if (ART_CARDS[u.name]) return { tribe, kind: 'card' };
    if (tribe === 'Other') return { tribe, kind: 'orb' };
    const name = String(u.name || '');
    const hit = VARIANT[tribe].find(([, re]) => re.test(name));
    const id = Number.isFinite(u.id) ? u.id : hashStr(name);
    return { tribe, kind: hit ? hit[0] : VARIANT[tribe][id % VARIANT[tribe].length][0] };
  }
  const BODY = {
    imp: (c, p) => shadow(50, 71, 16) + sp(c, 'M37 33 30 15 44 28ZM63 33 70 15 56 28Z', p.d) + se(c, 50, 49, 19, 18) + eye(43, 46, 3, p.e, p.d) + eye(57, 46, 3, p.e, p.d) + ln('M41 56q9 7 18 0', p.d, 2),
    wisp: (c, p) => flame(c, 50, 72, 56, 34) + eye(43, 52, 2.6, p.d) + eye(57, 52, 2.6, p.d),
    drake: (c, p) => shadow(50, 71, 18) + sp(c, 'M48 46 18 24 26 45 13 50 46 56Z', c.D) + sp(c, 'M52 46 82 24 74 45 87 50 54 56Z', c.D) + se(c, 50, 54, 13, 15) + se(c, 50, 33, 10, 10) + eye(46, 31, 2, p.e, p.d) + eye(54, 31, 2, p.e, p.d),
    jelly: (c, p) => [32, 41, 50, 59, 68].map((x, k) => ln(`M${x} 50q${k % 2 ? 5 : -5} 7 0 13t0 12`, p.a, 2.4, 0.8)).join('') + sp(c, 'M27 52c0-17 10-29 23-29s23 12 23 29c-7 4-39 4-46 0z') + eye(43, 44, 2.6, p.e, p.d) + eye(57, 44, 2.6, p.e, p.d),
    fish: (c, p) => sp(c, 'M69 46 87 32 82 46 87 60z', c.D) + se(c, 49, 46, 23, 15) + eye(34, 43, 3.6, p.e, p.d),
    golem: (c, p) => shadow(50, 72, 22) + sp(c, 'M30 34h40v36H30z', c.R) + sp(c, 'M38 15h24v21H38z', c.R) + eye(45, 25, 1.6, p.e) + eye(55, 25, 1.6, p.e),
    crystal: (c, p) => glow(c, 50, 44, 26) + sp(c, 'M50 10 61 32 57 68 43 68 39 32z', c.P) + sp(c, 'M30 66 25 40 33 30 38 44 37 66z', c.P) + sp(c, 'M70 66 75 42 67 32 62 46 63 66z', c.P),
    orb: (c, p) => glow(c, 50, 44, 26) + se(c, 50, 44, 18, 18) + dot(50, 44, 7, p.e, 0.7),
    // --- Neutral constructs: one riveted chassis, with a role-specific attachment ---
    sentry: (c, p) => construct(c, p),
    warden: (c, p) => construct(c, p, { wide: true }) + glow(c, 26, 48, 14, 0.6) + sp(c, 'M14 34Q26 28 38 34V56Q26 66 14 56Z', '#dfe8f0') +
      fp('M17 37Q26 32 35 37V54Q26 61 17 54Z', '#9fd8ff', 0.55) + ln('M20 40l10 10M24 38l8 8', '#ffffff', 0.8, 0.7),
    drill: (c, p) => construct(c, p, { wide: true }) + sp(c, 'M68 44h10v8H68z', c.D) + sp(c, 'M78 41L96 48L78 55Z', c.M) +
      ln('M80 43.5l2 9M85 45l2 6.5M90 46.5l1 3.5', '#7a4a10', 0.6, 0.8) + gear(26, 58, 6, '#7a5a2a'),
    artificer: (c, p) => glow(c, 50, 40, 30, 0.7) + construct(c, p, { wide: true }) + crown(c, 50, 15, 16, 7) +
      gear(20, 30, 7, '#c89a4a', 8, 0.95) + gear(80, 30, 7, '#c89a4a', 8, 0.95) + ln('M27 32Q34 36 34 42M73 32Q66 36 66 42', p.e, 0.8, 0.7),
    ram: (c, p) => shadow(50, 74, 36) + sp(c, 'M12 50H74V60H12Z', '#6a4a2a') + ln('M18 50L30 60M30 50L42 60M42 50L54 60M54 50L66 60', '#3a2414', 0.8, 0.8) +
      se(c, 24, 66, 7, 7, '#3a2a1a') + se(c, 60, 66, 7, 7, '#3a2a1a') + dot(24, 66, 1.6, '#c89a4a') + dot(60, 66, 1.6, '#c89a4a') +
      sp(c, 'M10 40H76V49H10Z', '#8a6a3a') + sp(c, 'M74 34Q92 36 94 44Q92 52 74 54Z', c.B) + sp(c, 'M84 36Q90 28 82 24Q86 32 80 37Z', c.M) +
      eye(85, 42, 1.8, p.e) + ln('M16 44h56', '#4a3018', 0.6, 0.6),
    tinker: (c, p) => shadow(50, 72, 16) + sp(c, 'M40 70L42 52H58L60 70Z', c.D) + se(c, 50, 50, 11, 10) + se(c, 50, 34, 10, 9, '#e8c8a0') +
      sp(c, 'M39 30Q50 20 61 30Z', c.D) + se(c, 45.5, 33, 3.6, 3.2, c.M) + se(c, 54.5, 33, 3.6, 3.2, c.M) + eye(45.5, 33, 1.8, p.e) + eye(54.5, 33, 1.8, p.e) +
      inkLn('M60 50L72 40', '#a8b0b8', 1.4) + ln('M70 37l4 2l-1 3l-3 -1', '#a8b0b8', 1.2) + gear(30, 60, 5, '#b08a3a'),
    apprentice: (c, p) => shadow(50, 72, 20) + sp(c, 'M58 70L60 62H78L80 70Z', '#3a3a40') + sp(c, 'M56 62H82L78 56H60Z', '#5a5a64') +
      sp(c, 'M34 70L36 52H50L52 70Z', c.D) + se(c, 43, 50, 10, 9) + se(c, 43, 34, 9, 8.5, '#e8c8a0') + sp(c, 'M34 30Q43 22 52 30Z', c.D) +
      peye(40, 35, 1.4) + peye(47, 35, 1.4) + inkLn('M51 48L64 40', '#8a6a3a', 1.3) + sp(c, 'M61 35H70V42H61Z', c.B) + motes(rng(5), 6, '#ffd27a', [58, 44, 22, 12]),
    clerk: (c, p) => shadow(50, 72, 18) + sp(c, 'M38 70L40 50H60L62 70Z', c.D) + se(c, 50, 48, 12, 10) + se(c, 50, 32, 9, 9, '#e8c8a0') +
      sp(c, 'M40 26H60L58 22H42Z', c.D) + se(c, 46, 32, 2.4, 2, c.M) + eye(46, 32, 1.2, p.e) + eye(54, 32, 1.2, '#2a1810') +
      sp(c, 'M22 50H40V64H22Z', '#efe2c0') + ln('M25 54h12M25 57h10M25 60h12', '#7a5a2a', 0.5, 0.8) + coin(70, 60, 4) + coin(74, 56, 3.6) + coin(68, 53, 3.2),
  };
  // Riveted metal construct: legs, torso with a cog, visor head with two glowing eyes.
  function construct(c, p, { wide = false } = {}) {
    const w = wide ? 22 : 17;
    return shadow(50, 72, w + 6) + sp(c, `M${41 - w / 3} 72V60H${46 - w / 4}V72Z`, c.D) + sp(c, `M${54 + w / 4} 72V60H${59 + w / 3}V72Z`, c.D) +
      sp(c, `M${50 - w} 36H${50 + w}L${48 + w} 62H${52 - w}Z`, c.B) + gear(50, 49, 7, c.M) +
      [-1, 1].map((s) => dot(50 + s * (w - 3), 40, 0.9, '#2a1e0e') + dot(50 + s * (w - 4), 58, 0.9, '#2a1e0e')).join('') +
      sp(c, 'M40 15H60L62 34H38Z', c.B) + fp('M42 22H58V28H42Z', '#0c0805') + eye(45.5, 25, 1.6, p.e) + eye(54.5, 25, 1.6, p.e) +
      ln(`M${50 - w} 40L${44 - w} 56M${50 + w} 40L${56 + w} 56`, '#3a2a1a', 2.4, 0.9);
  }

  const artCache = new Map();
  let artSeq = 0;
  // Build the markup once per card identity with a '@@' id placeholder; each render swaps in a fresh
  // document-unique prefix so gradient ids never collide between cards on the page.
  function artTemplate(u) {
    const { tribe, kind } = artKind(u);
    const id = Number.isFinite(u.id) ? u.id : hashStr(u.name);
    const spec = ART_CARDS[u.name];
    const pals = PAL[tribe];
    const metal = tribe === 'Neutral' ? NEUTRAL_METAL.find(([, re]) => re.test(String(u.name || ''))) : null;
    const p = spec ? spec.pal : metal ? pals[metal[0]] : pals[(id >> 1) % pals.length];
    const envKey = spec ? spec.env : FALLBACK_ENV[tribe];
    const env = ENV[envKey];
    const r = rng(hashStr(u.name || String(id)) + 7);
    const tier = Math.max(1, Math.min(5, u.tier | 0));
    const c = {}; for (const k of 'BDHMGFKRWVPL') c[k] = `url(#@@${k})`; c.G2 = 'url(#@@L)';
    const g2 = spec && spec.env === 'grove' ? '#d8ff8a' : envKey === 'cave' ? '#c89aff' : p.e;
    const stops = (a) => a.map(([o, col, op = 1]) => `<stop offset="${o}" stop-color="${col}"${op < 1 ? ` stop-opacity="${op}"` : ''}/>`).join('');
    const lin = (k, a, x2 = 0, y2 = 1, x1 = 0, y1 = 0) => `<linearGradient id="@@${k}" x1="${x1}" y1="${y1}" x2="${x2}" y2="${y2}">${stops(a)}</linearGradient>`;
    const rad = (k, a, cx = 0.5, cy = 0.5, rr = 0.5) => `<radialGradient id="@@${k}" cx="${cx}" cy="${cy}" r="${rr}">${stops(a)}</radialGradient>`;
    const defs = lin('B', [[0, p.a], [1, p.b]], 0.75, 1, 0.25, 0) + lin('D', [[0, p.b], [1, p.d]], 0.6, 1, 0.3, 0) +
      lin('H', [[0, '#fff', 0.32], [0.38, '#fff', 0], [0.58, '#000', 0], [1, '#000', 0.55]], 1, 1) +
      lin('M', [[0, '#fff3c0'], [0.45, '#e8b04a'], [1, '#7a4a10']]) +
      rad('G', [[0, p.e, 0.95], [0.35, p.a, 0.45], [1, p.a, 0]]) + rad('L', [[0, g2, 0.95], [0.4, g2, 0.35], [1, g2, 0]]) +
      lin('F', [[0, '#fffbe0'], [0.3, '#ffd34a'], [0.7, '#ff6a1a'], [1, '#c2210d', 0.85]], 0, 0, 0, 1) +
      lin('K', [[0, env.k[0]], [1, env.k[1]]]) + lin('R', [[0, env.r[0]], [1, env.r[1]]], 0.8, 1, 0.2, 0) + lin('W', [[0, env.w[0]], [1, env.w[1]]]) +
      rad('P', [[0, '#ffffff'], [0.45, p.e], [1, p.b]], 0.38, 0.35, 0.75) +
      rad('V', [[0.55, '#000', 0], [1, '#000', 0.72]], 0.5, 0.45, 0.72);
    const back = tier < 3 ? `<ellipse cx="50" cy="46" rx="30" ry="24" fill="${c.G}" opacity=".14"/>` : tier >= 3 ? `<ellipse cx="50" cy="44" rx="${16 + tier * 5}" ry="${14 + tier * 4}" fill="${c.G}" opacity="${(0.12 + tier * 0.07).toFixed(2)}"/>` : '';
    const legend = tier >= 5 ? rays(50, 44, 16, 70, p.e, 0.1, 360, 7) : '';
    const body = spec ? spec.paint(c, p, r) : (BODY[kind] || BODY.orb)(c, p, r);
    const sheen = `<path d="M0 0H100V9Q50 15 0 9Z" fill="#fff" opacity=".05"/>`;
    return `<svg viewBox="0 0 100 80" preserveAspectRatio="xMidYMid slice" aria-hidden="true" data-art="${spec ? 'card' : kind}"><defs>${defs}</defs>` +
      `<rect width="100" height="80" fill="${c.K}"/>${env.paint(c, r)}${legend}${back}<g class="art-body">${body}</g>${sheen}<rect width="100" height="80" fill="${c.V}"/></svg>`;
  }
  function unitArt(u) {
    const key = `${u.name}|${u.tribe}|${u.tier}|${u.id}`;
    let t = artCache.get(key);
    if (!t) { t = artTemplate(u); artCache.set(key, t); }
    return t.replace(/@@/g, `a${++artSeq}`);
  }
  function tribeGlyph(tribe) {
    if (tribe === 'Ember') return icon('flame');
    if (tribe === 'Tide') return icon('drop');
    if (tribe === 'Stone') return icon('rock');
    if (tribe === 'Neutral') return icon('gear');
    return icon('star');
  }
  const SEAT_COLORS = ['#e8b95c', '#ff7a3a', '#4fb3d9', '#b78be0', '#8fcf7a', '#d0432f'];
  function seatSigil(p) {
    const c = SEAT_COLORS[(p.id ?? 0) % SEAT_COLORS.length];
    const nm = (p.name || '?').trim();
    const letter = esc(/^seat\b/i.test(nm) ? String((p.id ?? 0)) : nm[0] || '?');
    const sides = 5 + ((p.id ?? 0) % 3);
    const pts = Array.from({ length: sides }, (_, k) => {
      const a = (Math.PI * 2 * k) / sides - Math.PI / 2;
      return `${(20 + 15 * Math.cos(a)).toFixed(1)},${(20 + 15 * Math.sin(a)).toFixed(1)}`;
    }).join(' ');
    return `<svg viewBox="0 0 40 40" aria-hidden="true"><polygon points="${pts}" fill="none" stroke="${c}" stroke-width="1.6"/><text x="20" y="25.5" text-anchor="middle" font-family="Georgia,serif" font-weight="700" font-size="15" fill="${c}">${letter}</text></svg>`;
  }

  // ---------- Card ----------
  // Append a sentence to an accessible label without doubling the period
  // when the label already ends with card text such as "Rally: +1/+1.".
  function appendLabel(node, sentence) {
    const base = (node.getAttribute('aria-label') || '').replace(/[.\s]+$/, '');
    node.setAttribute('aria-label', `${base}. ${sentence}`);
  }

  // Engine card text with each trigger prefix marked as a tappable term (presentation only).
  function cardTextHtml(text) {
    return esc(text).replace(TRIGGER_TEXT_RE, (m) => {
      const key = TRIGGER_PREFIX.find((x) => x.re.test(m))?.key;
      return key ? `<span class="trig" data-term="${key}">${m}</span>` : m;
    });
  }
  function statHtml(kind, v, cls) {
    const txt = fmtStat(v);
    const size = txt.length >= 4 ? ' s4' : txt.length === 3 ? ' s3' : '';
    return `<span class="stat ${kind}${cls}${size}" title="${kind === 'atk' ? 'Attack' : 'Health'} ${esc(v)}">${icon(kind === 'atk' ? 'atk' : 'heart')}<span>${esc(txt)}</span></span>`;
  }

  function unitCard(raw, { mini = false, dead = false, explain = false } = {}) {
    const u = enrich(raw);
    const tribe = TRIBES.includes(u.tribe) ? u.tribe : 'Other';
    const tierN = Math.max(0, Math.min(6, u.tier | 0));
    const kws = keywordsOf(u);
    const atkCls = u.baseAttack != null && u.attack > u.baseAttack ? ' up' : u.baseAttack != null && u.attack < u.baseAttack ? ' down' : '';
    const hpCls = u.baseHealth != null && u.health > u.baseHealth ? ' up' : u.baseHealth != null && u.health < u.baseHealth ? ' down' : '';
    const label = `${u.golden ? 'Golden ' : ''}${u.name}, ${u.tribe || 'unknown tribe'}, tier ${u.tier ?? '?'}, attack ${u.attack}, health ${u.health}${kws.length ? ', ' + kws.map((k) => k.label).join(', ') : ''}${u.text ? '. ' + u.text : ''}`;
    const c = el('div', {
      class: `card t-${tribe}${u.golden ? ' golden' : ''}${kws.some((k) => k.name === 'shield') ? ' has-shield' : ''}${kws.some((k) => k.name === 'guard') ? ' has-guard' : ''}${dead ? ' dead' : ''}${mini ? ' is-mini' : ''}`,
      title: `${u.golden ? 'Golden ' : ''}${u.name} — ${u.tribe || '?'} · tier ${u.tier ?? '?'}${u.baseAttack != null ? ` · base ${u.baseAttack}/${u.baseHealth}` : ''}${u.text ? '\n' + u.text : ''}`,
      role: 'img',
      'aria-label': label,
    });
    c._unit = u;
    c.dataset.tribe = u.tribe || '';
    if (u.golden) c.dataset.golden = '1';
    if (fmtStat(u.attack).length >= 3 || fmtStat(u.health).length >= 3) c.classList.add('wide-stats');
    c.innerHTML = `
      <div class="card-art">${unitArt(u)}
        <span class="card-tier">${Array.from({ length: tierN }, () => icon('star')).join('')}</span>
        <span class="card-tribe" title="${esc(u.tribe || '')}">${tribeGlyph(tribe)}</span>
        ${u.golden ? '<span class="golden-badge" data-term="golden" title="Golden: three copies merged">Golden</span>' : ''}
      </div>
      <div class="card-name">${esc(u.name)}</div>
      ${kws.length ? `<div class="card-kw">${kws.map((k) => `<span class="kw ${esc(k.name)}" data-term="${esc(k.name)}">${esc(k.label)}</span>`).join('')}</div>` : ''}
      ${!mini && u.text ? `<div class="card-text">${cardTextHtml(u.text)}</div>` : ''}
      ${statHtml('atk', u.attack, atkCls)}
      ${statHtml('hp', u.health, hpCls)}`;
    if (explain) {
      // Cards with no other click role (rules, scouting, unlocks, battle) open their explanation.
      c.tabIndex = 0;
      c.setAttribute('role', 'button');
      c.classList.add('explainable');
      appendLabel(c, 'Press Enter for how it works.');
      c.addEventListener('click', () => openExplain({ card: u }, c));
      c.addEventListener('keydown', (e) => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); openExplain({ card: u }, c); } });
    }
    return c;
  }
  // Small "i" button laid over the bottom centre of a card (outside the card node, so it never nests
  // inside a card that is itself a button). Opens the card's explanation; keyboard and touch reachable.
  function infoBtn(u) {
    const name = enrich(u).name;
    const b = el('button', { type: 'button', class: 'card-info', title: `How ${name} works`, 'aria-label': `How ${name} works`, text: 'i' });
    b.addEventListener('click', (e) => { e.stopPropagation(); openExplain({ card: u }, b); });
    return b;
  }


  // ---------- Explanations (presentation over /api/rules; see GLOSSARY above) ----------
  const gloss = () => { if (S._glossFor !== S.rules || !S._gloss) { S._glossFor = S.rules; S._gloss = buildGlossary(S.rules || {}); } return S._gloss; };
  const tribeTerm = (e, tribe) => (e?.key === 'kinplay' && tribe ? `After you play another ${tribe} card` : e?.term);
  const scopeCls = (sc) => (/combat only/i.test(sc) ? 'temp' : /permanent|every round|every combat/i.test(sc) ? 'perm' : /this turn/i.test(sc) ? 'turn' : '');
  function termNode(e, { label = null, value = null, tribe = null } = {}) {
    if (!e) {
      return el('div', { class: 'gloss-item missing' }, el('h4', { text: label || 'Unknown term' }),
        el('p', { class: 'muted', text: `This server publishes no definition for "${label || 'this term'}". The card text from the engine is the authoritative description.` }));
    }
    const kids = [el('h4', {}, tribeTerm(e, tribe) || label, e.scope ? el('span', { class: `scope ${scopeCls(e.scope)}`, text: e.scope }) : null), el('p', { text: e.text })];
    if (e.key === 'rally' && value > 0) kids.push(el('p', { class: 'gloss-n', text: `Rally ${value}: its 1st, 2nd and 3rd attacks in a combat use +${value}, +${2 * value} and +${3 * value} attack.` }));
    else if (e.key === 'armor' && value > 0) kids.push(el('p', { class: 'gloss-n', text: `Armor ${value}: a hit of ${value + 2} deals ${2}; a hit of ${value} or less deals nothing.` }));
    else if (e.key === 'income' && value > 0) kids.push(el('p', { class: 'gloss-n', text: `Income ${value}: +${value} gold every round while it stays on your board.` }));
    if (e.detail) kids.push(el('p', { class: 'gloss-detail', text: e.detail }));
    if (e.rule) kids.push(el('blockquote', { class: 'gloss-rule' }, el('span', { class: 'q-label', text: 'Engine rule' }), ' ', e.rule));
    return el('div', { class: `gloss-item k-${e.kind || 'keyword'}` }, kids);
  }
  function cardExplainNode(raw) {
    const u = enrich(raw);
    const g = gloss();
    const x = explainCard(u, g);
    const box = el('div', { class: 'explain-card' });
    const base = u.baseAttack != null && (u.baseAttack !== u.attack || u.baseHealth !== u.health) ? ` (${u.golden ? 'golden' : 'card'} base ${u.baseAttack}/${u.baseHealth})` : '';
    const preview = unitCard(u);
    preview.classList.add('preview');
    preview.removeAttribute('role');
    preview.setAttribute('aria-hidden', 'true');
    box.append(el('div', { class: 'explain-top' }, preview, el('div', { class: 'explain-facts' },
      el('p', { class: 'explain-meta', text: `${u.golden ? 'Golden \u00b7 ' : ''}${u.tribe || 'Unknown tribe'} \u00b7 tier ${u.tier ?? '?'}` }),
      el('p', { class: 'explain-stats', html: `<b>${esc(u.attack)}</b> attack \u00b7 <b>${esc(u.health)}</b> health${esc(base)}` }),
      el('blockquote', { class: 'engine-text' }, el('span', { class: 'q-label', text: u.golden ? 'Golden card text' : 'Card text' }), ' ', u.text || 'No keywords or abilities.'))));
    if (u.golden) {
      box.append(el('h3', { text: 'Golden' }));
      const ge = goldenEntries(g);
      if (ge.length) ge.forEach((e) => box.append(termNode(e)));
      else box.append(el('p', { class: 'muted small', text: 'Golden: three copies merged into this one. The card text above shows its exact doubled values.' }));
    }
    if (x.keywords.length) {
      box.append(el('h3', { text: 'Keywords' }));
      x.keywords.forEach((k) => box.append(termNode(k.entry, { label: k.label, value: k.value })));
    }
    if (x.abilities.length) {
      box.append(el('h3', { text: 'Abilities' }));
      for (const a of x.abilities) {
        const dl = el('dl', { class: 'abil-dl' });
        const row = (dt, dd) => { if (dd) dl.append(el('dt', { text: dt }), el('dd', { text: dd })); };
        row('When', a.triggerEntry ? `${tribeTerm(a.triggerEntry, u.tribe)} \u2014 ${a.triggerEntry.text}` : 'No published definition for this trigger.');
        row('Affects', /^stats/.test(a.effect || '') ? a.target : null);
        row('Effect', a.effectEntry ? a.effectEntry.text : a.effect ? 'No published definition for this effect; the card text is authoritative.' : null);
        row('Lasts', a.effectEntry?.scope || null);
        box.append(el('div', { class: 'gloss-item ability' }, el('p', { class: 'abil-text', html: cardTextHtml(a.sentence || '') }), dl));
      }
      const extra = [];
      if (x.abilities.some((a) => a.target && a.target !== 'this unit') && g.get('otherallies')) extra.push(g.get('otherallies'));
      if (x.abilities.some((a) => /statsPer/.test(a.effect || '')) && g.get('counts')) extra.push(g.get('counts'));
      if (g.get('nochain')) extra.push(g.get('nochain'));
      extra.forEach((e) => box.append(termNode(e)));
    }
    const combatRelevant = x.keywords.some((k) => ['guard', 'shield', 'armor', 'rally'].includes(k.key)) || x.abilities.some((a) => /^stats/.test(a.effect || ''));
    if (combatRelevant && g.get('combatcopy')) box.append(termNode(g.get('combatcopy')));
    if (x.missing.length) box.append(el('p', { class: 'muted small', text: `Not explained here (no published definition): ${x.missing.join(', ')}.` }));
    return box;
  }
  // Server `golden`/`triple` glossary entries (or the anchored fallback), golden first.
  const goldenEntries = (g) => ['golden', 'triple'].map((k) => g.get(k)).filter(Boolean);
  function openExplain(q, opener) {
    const dlg = $('#dlgExplain');
    const body = $('#explainBody');
    if (!dlg || !body) return;
    if ($('#dlgBattle')?.open && B.playing) stopPlay();
    body.replaceChildren();
    if (q.card) {
      $('#explainH').textContent = enrich(q.card).name || 'Unit';
      body.append(cardExplainNode(q.card));
    } else {
      const e = gloss().get(q.term) || null;
      const label = String(q.label || q.term || '').replace(/:$/, '');
      const value = Number(label.split(/\s+/)[1]);
      $('#explainH').textContent = tribeTerm(e, q.tribe) || label || 'Term';
      body.append(termNode(e, { label, value: Number.isFinite(value) ? value : null, tribe: q.tribe }));
      if (e?.kind === 'keyword' && e.key !== 'income' && gloss().get('combatcopy')) body.append(termNode(gloss().get('combatcopy')));
      if (e?.kind === 'trigger' && gloss().get('nochain')) body.append(termNode(gloss().get('nochain')));
      if (q.term === 'golden' && gloss().get('triple')) body.append(termNode(gloss().get('triple')));
      body.append(el('p', {}, el('button', { type: 'button', class: 'btn small', text: 'Full rules reference', onclick: () => { dlg.close(); openRules(); } })));
    }
    S.explainOpener = opener || document.activeElement;
    if (!dlg.open) dlg.showModal();
    body.scrollTop = 0;
    dlg.querySelector('.close')?.focus();
  }
  // Per-step battle notes, read from the server's event fields and snapshots only (never computed).
  function combatHints(e) {
    if (!e || e.kind !== 'attack') return [];
    const g = gloss();
    const s = sideKey(e.side);
    const attB = s === 'a' ? e.beforeA : e.beforeB;
    const defB = s === 'a' ? e.beforeB : e.beforeA;
    const att = enrich(attB?.[e.attackerIndex] || {});
    const tgt = enrich(defB?.[e.targetIndex] || {});
    const out = [];
    if (e.rally > 0 && g.get('rally')) out.push(['rally', `Rally: ${att.name} gained +${e.rally} attack right before this attack and keeps it until the combat ends.`]);
    if (tgt.guard && (defB || []).some((u) => !u.guard) && g.get('guard')) out.push(['guard', `Guard: ${tgt.name} had to be attacked before units without Guard.`]);
    const sb = [e.targetShieldBroken ? tgt.name : null, e.attackerShieldBroken ? att.name : null].filter(Boolean);
    if (sb.length && g.get('shield')) out.push(['shield', `Shield: the hit on ${sb.join(' and ')} dealt no damage; the Shield broke.`]);
    if (/Armor absorbs/.test(e.text || '') && g.get('armor')) out.push(['armor', 'Armor: each damaging hit on an Armor unit is lowered by its Armor value.']);
    return out;
  }
  function paintHints(e) {
    const box = $('#arenaHint');
    if (!box) return;
    const hs = combatHints(e);
    box.replaceChildren(...hs.map(([k, t]) => el('button', { type: 'button', class: `hint-chip ${k}`, title: 'What does this mean?', onclick: (ev) => openExplain({ term: k }, ev.currentTarget), text: t })));
    box.hidden = !hs.length;
  }
  function combatLegend() {
    const g = gloss();
    const items = ['guard', 'shield', 'armor', 'rally', 'combatcopy', 'damagecap'].map((k) => g.get(k)).filter(Boolean);
    const order = ruleSentences(S.rules || {}).filter((t) => /^Combat:|Units attack from the front|deal damage simultaneously|Combat stops after/i.test(t))
      .sort((x, y) => (/^Combat:/.test(y) ? 1 : 0) - (/^Combat:/.test(x) ? 1 : 0));
    if (!items.length && !order.length) return null;
    const names = items.filter((i) => i.kind === 'keyword').map((i) => i.term);
    return el('details', { class: 'combat-legend' },
      el('summary', { text: `How combat works${names.length ? `: ${names.join(' \u00b7 ')}` : ''}` }),
      order.length ? el('blockquote', { class: 'gloss-rule' }, el('span', { class: 'q-label', text: 'Engine rule' }), ' ', order.join(' ')) : null,
      el('div', { class: 'gloss-list' }, items.map((i) => termNode(i))));
  }
  // Rules reference: the glossary grouped by what players ask: keywords, timing, what lasts, effects.
  function rulesGuide() {
    const g = gloss();
    const wrap = el('div', { class: 'rules-guide' });
    const secs = [];
    const sec = (id, title, ...kids) => { const k = kids.flat().filter(Boolean); if (!k.length) return; secs.push([id, title]); wrap.append(el('section', { id, class: 'guide-sec' }, el('h3', { text: title }), k)); };
    const shown = new Set();
    const list = (items) => (items.length ? el('div', { class: 'gloss-list' }, items) : null);
    const pick = (keys) => keys.map((k) => g.get(k)).filter(Boolean).map((e) => { shown.add(e.key); return termNode(e); });
    sec('rg-kw', 'Keywords', list(pick(['guard', 'shield', 'armor', 'rally', 'income'])));
    const trig = pick(['play', 'kinplay', 'endturn', 'sell', 'nochain']);
    sec('rg-when', 'When abilities fire', trig.length ? el('ol', { class: 'flow', 'aria-label': 'Order of a round' },
      el('li', { html: '<b>Recruit</b> buy puts a card in your hand; nothing fires' }),
      el('li', { html: '<b>play</b> <span class="trig">Play:</span> fires, the card joins the board, then <span class="trig">After you play</span> on its tribe mates, left to right' }),
      el('li', { html: '<b>sell</b> board units only: base refund, then <span class="trig">Sell:</span> fires after the unit leaves' }),
      el('li', { html: '<b>end</b> <span class="trig">End of turn:</span> fires for the whole board, left to right' }),
      el('li', { html: '<b>Combat</b> fought on a copy of your board' })) : null, list(trig));
    const cc = g.get('combatcopy');
    if (cc) {
      shown.add('combatcopy');
      sec('rg-last', 'What lasts', el('div', { class: 'lasts' },
        el('div', { class: 'last-col perm' }, el('h4', { text: 'Permanent, on your board' }), el('ul', {}, ['Stat gains from Play, After you play, End of turn and Sell abilities', 'Keywords printed on the card', 'The board order you set with swap'].map((t) => el('li', { text: t })))),
        el('div', { class: 'last-col temp' }, el('h4', { text: 'Only during one combat' }), el('ul', {}, ['Damage taken and deaths', 'Broken Shields', 'Rally attack gains'].map((t) => el('li', { text: t })))),
        el('div', { class: 'last-col turn' }, el('h4', { text: 'Only this turn' }), el('ul', {}, ['Gold, including gold from abilities and sales'].map((t) => el('li', { text: t }))))),
      termNode(cc));
    }
    sec('rg-gold', 'Triples and golden cards', list(pick(['golden', 'triple'])));
    sec('rg-fx', 'Ability effects', list(pick(['stats', 'statsPerHand', 'statsPerPlay', 'gold', 'make', 'otherallies', 'counts'])));
    sec('rg-dmg', 'Damage to players', list(pick(['damagecap'])));
    const rest = [...g.values()].filter((e) => !shown.has(e.key));
    sec('rg-more', 'More terms', list(rest.map((e) => termNode(e))));
    const nav = el('nav', { class: 'chips guide-nav', 'aria-label': 'Rules sections' }, [...secs, ['rg-units', 'Units'], ['rg-all', 'All rules']].map(([id, t]) =>
      el('button', { type: 'button', class: 'chip-btn', text: t, onclick: () => document.getElementById(id)?.scrollIntoView({ block: 'start', behavior: reduceMotion() ? 'auto' : 'smooth' }) })));
    wrap.prepend(nav);
    return wrap;
  }

  // ---------- UI chrome ----------
  let statusTimer;
  function status(msg) {
    const s = $('#status');
    s.textContent = msg;
    s.classList.add('show');
    clearTimeout(statusTimer);
    statusTimer = setTimeout(() => s.classList.remove('show'), 2200);
  }
  function banner(msg, { kind = 'error', retry = null } = {}) {
    const b = $('#banner');
    $('#bannerText').textContent = msg;
    b.classList.toggle('info', kind === 'info');
    b.hidden = false;
    S.lastRetry = retry;
    $('#bannerRetry').hidden = !retry;
  }
  const hideBanner = () => { $('#banner').hidden = true; S.lastRetry = null; };
  function setBusy(v) {
    S.busy = v;
    document.body.classList.toggle('busy', v);
    $('#table').setAttribute('aria-busy', v ? 'true' : 'false');
  }
  const shake = (node) => { if (!node) return; node.classList.remove('shake'); void node.offsetWidth; node.classList.add('shake'); };
  const errMessage = (e) => (typeof e === 'string' ? e : e?.message ? `${e.message}${e.code ? ` [${e.code}]` : ''}` : e?.code || JSON.stringify(e));

  // ---------- Core: replay and act ----------
  let gameRequest = 0; // Only the latest game request may commit state or release busy.
  async function load(seed, mode, moves, { fromResume = false } = {}) {
    const request = ++gameRequest;
    setBusy(true);
    try {
      const { body } = await getJSON(gamePath(seed, mode, moves));
      if (request !== gameRequest) return false;
      let keep = moves;
      if (!Array.isArray(body.players)) {
        // Request-level error (bad_request, too_many_moves, routing): no game state to show.
        // Keep S.moves, S.data and localStorage untouched so a good saved replay is never erased.
        banner(`Server refused the request: ${errMessage(body.error || 'response has no game state')}`);
        return false;
      }
      if (body.error) {
        const n = Number.isFinite(body.movesApplied) ? body.movesApplied : (Number.isFinite(body.error.index) ? body.error.index : 0);
        keep = moves.slice(0, n);
        banner(`${fromResume ? 'Transcript partly invalid' : 'Move rejected'}: ${errMessage(body.error)}. Resumed after ${n} accepted moves.`);
      } else hideBanner();
      Object.assign(S, { seed, mode, moves: keep, data: body, selected: null });
      if (S.scout != null && !seatOf(S.scout)) S.scout = null;
      save();
      render();
      if (finished() && fromResume) openOver();
      return true;
    } catch (e) {
      if (request !== gameRequest) return false;
      banner(e.message, { retry: () => load(seed, mode, moves, { fromResume }) });
      return false;
    } finally {
      if (request === gameRequest) setBusy(false);
    }
  }

  async function act(action, { quiet = false } = {}) {
    if (S.busy || !S.data || !action) return false;
    if (!MOVE_RE.test(action)) { banner(`Not a move string: ${action}`); return false; }
    const request = ++gameRequest;
    const seed = S.seed, mode = S.mode;
    const prev = S.data;
    const next = [...S.moves, action];
    setBusy(true);
    try {
      const { body } = await getJSON(gamePath(seed, mode, next));
      if (request !== gameRequest) return false;
      if (body.error || !Array.isArray(body.players)) {
        banner(`“${action}” rejected by the engine: ${errMessage(body.error || 'response has no game state')}`);
        shake($('#warband'));
        return false; // keep the prior observation (identical to the server's pre-move state)
      }
      hideBanner();
      S.moves = next;
      S.data = body;
      S.selected = null;
      save();
      render();
      flashNew(prev, action);
      const merged = newGoldens(prev, body);
      if (!quiet) status(merged.length ? `Sent ${action}. Triple! ${merged.map((n) => `Three ${n} copies merged into a golden ${n} in your hand`).join('; ')}.` : `Sent ${action}`);
      afterRoundChange(prev, body, quiet);
      return true;
    } catch (e) {
      if (request !== gameRequest) return false;
      banner(e.message, { retry: () => act(action) });
      return false;
    } finally {
      if (request === gameRequest) setBusy(false);
    }
  }

  // Cosmetic: name the cards that became golden between two observations of the same seat and pulse them.
  function newGoldens(prev, now) {
    const seat = now.player ?? 0;
    if ((prev.player ?? 0) !== seat) return [];
    const pick = (d) => (d.players || []).find((x) => x.id === seat) || (d.players || [])[seat];
    const before = goldenCount(pick(prev)), after = goldenCount(pick(now));
    const ids = [...after].filter(([id, n]) => n > (before.get(id) || 0)).map(([id]) => id);
    for (const id of ids) $$(`#hand .card.golden, #board .card.golden`).filter((c) => c._unit?.id === id).forEach((c) => c.classList.add('golden-new'));
    return ids.map((id) => enrich({ id }).name);
  }
  // Purely cosmetic: highlight the zone that received a unit after buy/play.
  function flashNew(prev, action) {
    const [verb] = action.split(':');
    const zone = verb === 'buy' && hasHand() ? '#hand' : verb === 'play' || verb === 'buy' ? '#board' : null;
    if (!zone) return;
    const wraps = $$(`${zone} .card-wrap`);
    const target = verb === 'play' && action.split(':')[2] != null ? wraps[+action.split(':')[2]] : wraps[wraps.length - 1];
    target?.querySelector('.card')?.classList.add('enter');
  }

  function afterRoundChange(prev, now, quiet) {
    const roundAdvanced = now.round !== prev.round || (now.phase === 'finished' && prev.phase !== 'finished');
    if (!roundAdvanced) return;
    // `combat` carries full detail (events) only for the latest resolved round; `history` has every fight.
    const detail = fightDetails(now);
    const pool = (now.history && now.history.length ? now.history : now.combat || [])
      .filter((h) => !Number.isFinite(h.round) || h.round >= prev.round)
      .map((h) => detail.get(`${h.round}:${h.a}:${h.b}`) || h);
    const mine = S.mode === 'manual'
      ? pool.filter((c) => c.round === prev.round)
      : pool.filter((c) => c.a === human() || c.b === human());
    if (now.phase === 'finished') {
      if (!quiet && mine.length) openBattle(mine, () => openOver());
      else openOver();
      return;
    }
    if (!quiet && mine.length) openBattle(mine);
  }

  // ---------- Render ----------
  function render() {
    const d = D();
    if (!d) return;
    $('#roundNum').textContent = d.round ?? '–';
    $('#roundOf').textContent = d.maxRounds ? `/ ${d.maxRounds}` : '';
    const chip = $('#phaseChip');
    chip.textContent = d.phase === 'finished' ? 'finished' : S.mode === 'manual' ? `${nameOf(meId())} to act` : 'recruit';
    chip.className = 'phase-chip' + (d.phase === 'finished' ? ' finished' : '');
    $('#seedVal').textContent = `${d.seed ?? S.seed}${S.mode === 'manual' ? ' · manual' : ''}`;
    document.body.classList.toggle('v2', hasHand());
    renderSeats();
    renderScout();
    renderEcon();
    renderShop();
    renderCommands();
    renderTierPanel();
    renderHand();
    renderBoard();
    renderEndRow();
    renderLog();
    renderCmdList();
    renderMoves();
    renderAgentDoc();
  }

  function renderSeats() {
    const d = D();
    const list = $('#seats');
    list.replaceChildren();
    const scouted = currentScout();
    for (const p of players()) {
      const isMe = p.id === meId();
      const dead = p.alive === false || p.hp <= 0;
      const maxHp = costs().startHp || Math.max(1, ...players().map((x) => x.hp || 0));
      const tags = [];
      if (isMe) tags.push(`<span class="tag ${S.mode === 'manual' ? 'turn' : 'you'}">${S.mode === 'manual' ? 'acting' : 'you'}</span>`);
      if (p.id === d.nextOpponent && !isMe) tags.push('<span class="tag foe">next foe</span>');
      if (p.bot && S.mode !== 'manual') tags.push(`<span class="tag bot" title="Built-in bot${p.style ? ': ' + esc(p.style) : ''}">${p.style ? esc(p.style) : 'bot'}</span>`);
      if (dead) tags.push(`<span class="tag out">out${p.eliminatedRound != null ? ' R' + esc(p.eliminatedRound) : ''}</span>`);
      if (p.ready && !dead && !finished()) tags.push('<span class="tag bot">ready</span>');
      const units = Array.from({ length: boardMax() }, (_, i) => {
        const u = p.board?.[i] && enrich(p.board[i]);
        return `<i class="${u ? 'u-' + (TRIBES.includes(u.tribe) ? u.tribe : 'other') : ''}"></i>`;
      }).join('');
      const handN = Array.isArray(p.hand) ? p.hand.length : p.handCount;
      const btn = el('button', {
        type: 'button',
        class: `seat${isMe ? ' me' : ''}${dead ? ' dead' : ''}`,
        'aria-pressed': String(p.id === scouted && !isMe),
        'aria-label': `${p.name}${isMe ? ' (you)' : ''}: ${p.hp} health, tier ${p.tier}, investment ${p.investment}, ${p.board?.length || 0} units${handN != null ? `, ${handN} in hand` : ''}${p.id === d.nextOpponent ? ', next opponent' : ''}${dead ? ', eliminated' : ''}. ${isMe ? 'Jump to your warband.' : 'Scout this player.'}`,
        onclick: () => {
          if (isMe) { $('#warband').focus(); $('#warband').scrollIntoView({ behavior: 'smooth', block: 'center' }); return; }
          S.scout = p.id; renderSeats(); renderScout();
          if (matchMedia('(max-width: 860px)').matches) $('#scout').scrollIntoView({ behavior: 'smooth', block: 'start' });
        },
      });
      btn.innerHTML = `
        <span class="sigil">${seatSigil(p)}</span>
        <span class="seat-name">${esc(p.name)} ${tags.join('')}</span>
        <span class="hpbar" aria-hidden="true"><i style="width:${Math.max(0, Math.min(100, (p.hp / maxHp) * 100))}%"></i></span>
        <span class="seat-meta"><span>${icon('heart')} <b>${esc(p.hp)}</b></span><span>Tier <b>${esc(p.tier)}</b></span><span>Inv <b>${esc(p.investment ?? 0)}</b></span>${handN != null ? `<span title="Cards in hand (count is public, contents are private)">${icon('hand')} <b>${esc(handN)}</b></span>` : ''}${p.gold != null ? `<span>${icon('coin')} <b>${esc(p.gold)}</b></span>` : ''}</span>
        <span class="seat-units" aria-hidden="true">${units}</span>`;
      list.append(el('li', {}, btn));
    }
  }

  function currentScout() {
    const d = D();
    const valid = (id) => id != null && id !== meId() && seatOf(id);
    if (valid(S.scout)) return S.scout;
    if (valid(d.nextOpponent) && d.nextOpponent >= 0) return d.nextOpponent;
    return players().find((p) => p.id !== meId() && p.alive !== false)?.id ?? null;
  }

  function renderScout() {
    const d = D();
    const id = currentScout();
    const p = id != null ? seatOf(id) : null;
    const board = $('#scoutBoard');
    board.replaceChildren();
    const stats = $('#scoutStats');
    if (!p) {
      $('#scoutName').textContent = d.nextOpponent === -1 && !finished() ? 'Bye — no opponent next round' : 'Scouting';
      stats.replaceChildren();
      board.append(el('p', { class: 'empty', text: 'No opponent to scout.' }));
      return;
    }
    const isNext = p.id === d.nextOpponent;
    $('#scoutName').innerHTML = `${isNext ? 'Next foe' : 'Scouting'}: ${esc(p.name)}${d.nextOpponent === -1 && !finished() ? ' <span class="hint">you have a bye next round</span>' : ''}`;
    const last = [...(d.history || [])].reverse().find((h) => (h.a === human() && h.b === p.id) || (h.b === human() && h.a === p.id));
    let lastTxt = '';
    if (last) {
      const res = last.winner === human() ? 'you won' : last.winner === -1 || last.winner == null ? 'draw' : 'you lost';
      lastTxt = `<span class="pill" title="Your last fight against ${esc(p.name)}">R${esc(last.round)}: ${res}${last.damage ? ` · ${esc(last.damage)} dmg` : ''}</span>`;
    }
    const handN = Array.isArray(p.hand) ? p.hand.length : p.handCount;
    const tribes = (p.board || []).map((u) => enrich(u).tribe).filter(Boolean);
    const lean = TRIBES.map((t) => [t, tribes.filter((x) => x === t).length]).filter(([, n]) => n).sort((a, b) => b[1] - a[1]);
    stats.innerHTML = `
      <span class="pill hp">${icon('heart')} ${esc(p.hp)}</span>
      <span class="pill tier">${icon('star')} Tier ${esc(p.tier)}</span>
      <span class="pill inv" title="Investment level: permanent extra income">${icon('seed')} Inv ${esc(p.investment ?? 0)}</span>
      ${(p.nextIncome ?? p.income) != null ? `<span class="pill income" title="Their gold next round (public)">${icon('coin')} +${esc(p.nextIncome ?? p.income)} next</span>` : ''}
      ${handN != null ? `<span class="pill" title="Undeployed cards in hand (contents hidden)">${icon('hand')} ${esc(handN)} in hand</span>` : ''}
      ${lean.length ? `<span class="pill" title="Tribes on their warband">${lean.map(([t, n]) => `<span class="tribe-dot t-${t}">${tribeGlyph(t)}${n}</span>`).join(' ')}</span>` : ''}
      ${p.style && p.bot ? `<span class="pill" title="Built-in bot personality">${esc(p.style)}</span>` : ''}
      ${lastTxt}`;
    if (p.alive === false) board.append(el('p', { class: 'empty', text: `${p.name} has been eliminated.` }));
    else if (!p.board?.length) board.append(el('p', { class: 'empty', text: `${p.name} has no units on the warband.` }));
    else p.board.forEach((u) => board.append(unitCard(u, { mini: true, explain: true })));
  }

  function renderEcon() {
    const p = me();
    const c = costs();
    const econ = $('#econ');
    if (!p) { econ.replaceChildren(); return; }
    econ.innerHTML = `
      <span class="pill gold" title="Gold to spend this turn">${icon('coin')} ${esc(p.gold ?? '?')} <span class="sub">gold</span></span>
      ${(p.nextIncome ?? p.income) != null ? `<span class="pill income" title="Gold you will receive next round (server-computed)">+${esc(p.nextIncome ?? p.income)} <span class="sub">next round</span></span>` : ''}
      <span class="pill tier" title="Tavern tier — higher tiers offer stronger units">${icon('star')} Tier ${esc(p.tier)}</span>
      <span class="pill inv" title="Investment level — each level adds income every later round">${icon('seed')} Inv ${esc(p.investment ?? 0)}${c.maxInvestment != null ? `<span class="sub">/${esc(c.maxInvestment)}</span>` : ''}</span>
      <span class="pill hp" title="Health — reach 0 and you are out">${icon('heart')} ${esc(p.hp)}</span>`;
    $('#frozenTag').hidden = !p.frozen;
    $('#meStats').innerHTML = `<span class="pill">${icon('sword')} ${esc(p.board?.length || 0)}/${esc(boardMax())} on warband</span>`;
    $('#tavernTitle').firstChild.textContent = S.mode === 'manual' ? `Tavern — ${p.name} ` : 'Tavern ';
  }

  // Plain (non-golden) copies of a card id in a player's hand and board: display only.
  const plainCopies = (p, id) => [...(p?.hand || []), ...(p?.board || [])].filter((x) => x && x.id === id && x.golden !== true).length;
  const goldenCount = (p) => { const m = new Map(); for (const x of [...(p?.hand || []), ...(p?.board || [])]) if (x?.golden === true) m.set(x.id, (m.get(x.id) || 0) + 1); return m; };
  function renderShop() {
    const p = me();
    const row = $('#shop');
    row.replaceChildren();
    if (finished()) { row.append(el('p', { class: 'empty', text: 'The game is over. Start a new game or inspect the final warbands.' })); return; }
    const shop = p?.shop;
    if (!shop) { row.append(el('p', { class: 'empty', text: 'Shop hidden.' })); return; }
    if (!shop.length) { row.append(el('p', { class: 'empty', text: 'The shop is empty. Roll for new offers.' })); return; }
    const price = costs().buy;
    const v2 = hasHand();
    $('#shopHint').textContent = v2 ? 'recruits go to your hand' : 'recruits join your warband';
    shop.forEach((u, i) => {
      if (!u) { row.append(el('div', { class: 'slot', text: 'sold' })); return; }
      const a = `buy:${i}`;
      const ok = isLegal(a);
      const card = unitCard(u);
      if (ok) card.addEventListener('click', () => act(a));
      const short = p.gold != null && price != null && p.gold < price;
      const full = v2 ? (p.hand.length >= handMax()) : (p.board?.length || 0) >= boardMax();
      const why = ok ? '' : short ? 'Not enough gold' : full ? (v2 ? 'Hand is full' : 'Warband is full') : 'Not available now';
      const btn = el('button', {
        type: 'button', class: 'btn buy', disabled: !ok,
        title: ok ? `Recruit ${u.name} ${v2 ? 'into your hand' : 'onto your warband'} (${a})` : why,
        'aria-label': ok ? `Recruit ${u.name} for ${price ?? '?'} gold${v2 ? ' into your hand' : ''}` : `Cannot recruit ${u.name}: ${why}`,
        onclick: () => act(a),
        html: ok ? `Recruit${price != null ? ` · ${esc(price)} ${icon('coin')}` : ''} <kbd>${i + 1}</kbd>` : esc(why),
      });
      const own = plainCopies(p, u.id);
      const ownTag = own > 0 && own < 3 ? el('div', { class: `copies${own === 2 ? ' two' : ''}`, title: 'Plain copies of this card in your hand and on your board. Three copies merge into a golden card.', text: own === 1 ? '1 of 3 owned' : ok ? '2 of 3 owned: buy for golden' : full ? '2 of 3 owned \u00b7 hand full, cannot buy' : '2 of 3 owned' }) : null; // `ok` = buy:i in legalActions
      row.append(el('div', { class: `card-wrap${!ok ? ' unaffordable' : ''}` }, card, infoBtn(u), ownTag, el('div', { class: 'card-actions' }, btn)));
    });
  }

  function renderCommands() {
    const p = me();
    const c = costs();
    const row = $('#commandRow');
    row.replaceChildren();
    if (!p || finished()) return;
    const roundsLeft = D().maxRounds != null ? Math.max(0, D().maxRounds - D().round) : null;
    const left = roundsLeft != null ? ` ${roundsLeft} round${roundsLeft === 1 ? '' : 's'} left after this one.` : '';
    const invHint = (ruleText('invest') || (c.invest != null ? `Pay ${c.invest} now for more income in later rounds.` : 'Long-term income.')) + left;
    const upHint = ruleText('upgrade') || 'Raise tavern tier: stronger offers and more combat damage.';
    const defs = [
      { a: 'roll', label: 'Reroll', ic: 'roll', cost: c.roll, desc: ruleText('roll') || 'Replace the offers with new ones.' },
      { a: 'freeze', label: p.frozen ? 'Unfreeze' : 'Freeze', ic: 'freeze', cost: null, desc: ruleText('freeze') || (p.frozen ? 'Offers are kept for next round. Click to release.' : 'Keep these offers for next round. Free.'), active: p.frozen },
      { a: 'upgrade', label: (p.tier ?? 1) >= maxTier() ? `Tier ${maxTier()}` : `Tier ${(p.tier ?? 0) + 1}`, ic: 'up', cost: p.upgradeCost, desc: upHint },
      { a: 'invest', label: 'Invest', ic: 'seed', cost: c.invest, desc: invHint },
    ];
    for (const x of defs) {
      const ok = isLegal(x.a);
      const short = x.cost != null && p.gold != null && p.gold < x.cost;
      const maxed = (x.a === 'invest' && c.maxInvestment != null && p.investment >= c.maxInvestment) || (x.a === 'upgrade' && c.maxTier != null && p.tier >= c.maxTier);
      const why = ok ? '' : maxed ? 'Maxed' : short ? 'Not enough gold' : 'Not available now';
      row.append(el('button', {
        type: 'button', class: `btn cmd${x.active ? ' active' : ''}`, disabled: !ok,
        'aria-pressed': x.a === 'freeze' ? String(!!p.frozen) : null,
        title: `${x.desc}${ok ? ` (${x.a})` : ` — ${why}`}`,
        'aria-label': `${x.label}${x.cost != null ? `, costs ${x.cost} gold` : ''}. ${ok ? x.desc : why}`,
        onclick: () => act(x.a),
        html: `<span class="cmd-top">${icon(x.ic)}<span>${esc(x.label)}</span>${x.cost != null && !(maxed && x.a === 'upgrade') ? `<span class="cost">${esc(x.cost)}${icon('coin')}</span>` : `<span class="cost muted">${maxed ? 'max' : 'free'}</span>`}</span><span class="cmd-desc">${esc(ok ? x.desc : why)}</span>`,
      }));
    }
  }

  // Upgrade panel: display-only arithmetic over server-published numbers (gold, upgradeCost, buy price).
  // The engine alone decides legality; this just makes the tempo cost of levelling visible.
  // Published lowest upgrade price from the player's CURRENT tier: rules.upgradeFloors is keyed by current tier
  // ("1": floor of 1->2, ..., "4": floor of 4->5), exactly like rules.upgradeCosts.
  function upgradeFloor(currentTier) {
    const t = S.rules?.upgradeFloors ?? S.rules?.costs?.upgradeFloors;
    const v = t && typeof t === 'object' ? t[String(currentTier)] : null;
    return typeof v === 'number' ? v : null;
  }
  const maxTier = () => costs().maxTier ?? Math.max(1, ...catalog().map((c) => c.tier || 1));
  function renderTierPanel() {
    const box = $('#tierPanel');
    const p = me();
    box.replaceChildren();
    if (!p || finished()) { box.hidden = true; return; }
    box.hidden = false;
    const max = maxTier();
    const tier = p.tier ?? 1;
    const track = el('div', { class: 'tier-track', 'aria-label': `Tavern tier ${tier} of ${max}` },
      Array.from({ length: max }, (_, k) => el('span', { class: `tier-step${k + 1 <= tier ? ' on' : ''}${k + 1 === tier + 1 ? ' next' : ''}`, title: `Tier ${k + 1}`, html: `${icon('star')}<b>${k + 1}</b>` })));
    box.append(track);
    if (tier >= max) { box.append(el('p', { class: 'tier-note', text: `Top tier reached. Every offer can now come from tiers 1\u2013${max}.` })); return; }
    const cost = p.upgradeCost;
    const gold = p.gold ?? 0;
    const buy = costs().buy || null;
    const ok = isLegal('upgrade');
    const spend = el('div', { class: 'spend' });
    if (cost != null) {
      const left = Math.max(0, gold - cost);
      const nowN = buy ? Math.floor(gold / buy) : null;
      const afterN = buy ? Math.floor(left / buy) : null;
      const pct = gold > 0 ? Math.min(100, (cost / Math.max(gold, cost)) * 100) : 100;
      spend.append(el('div', { class: `spend-bar${cost > gold ? ' short' : ''}`, 'aria-hidden': 'true' }, el('i', { class: 'spent', style: `width:${pct}%` }), el('i', { class: 'left' })));
      const lost = nowN != null && afterN != null ? nowN - afterN : null;
      spend.append(el('p', { class: 'spend-text', html: cost > gold
        ? `Tier ${tier + 1} costs <b>${esc(cost)}</b>${icon('coin')} \u2014 you have ${esc(gold)}.`
        : `Tier ${tier + 1}: spend <b>${esc(cost)}</b> of ${esc(gold)}${icon('coin')} \u2192 <b>${esc(left)}</b> left${lost ? ` \u00b7 <span class="warn">${lost} fewer recruit${lost === 1 ? '' : 's'} this turn</span>` : ''}.` }));
      const fl = upgradeFloor(tier);
      if (fl != null) spend.append(el('p', { class: 'tier-note', text: fl < cost ? `Waiting lowers this to no less than ${fl}.` : `This is already the lowest price for tier ${tier + 1}.` }));
      const foe = seatOf(D().nextOpponent);
      if (cost <= gold && foe) spend.append(el('p', { class: 'tier-note', text: `Your warband fights this round as it stands: ${p.board?.length || 0} unit(s) vs ${foe.name}'s ${foe.board?.length || 0}; you have ${p.hp} HP.` }));
    }
    box.append(spend);
    const unlock = catalog().filter((c) => c.tier === tier + 1);
    if (unlock.length) {
      const det = el('details', { class: 'unlock' }, el('summary', { html: `${icon('eye')} Tier ${tier + 1} unlocks ${unlock.length} unit${unlock.length === 1 ? '' : 's'}: ${unlock.slice(0, 4).map((c) => `<span class="tribe-dot t-${esc(c.tribe)}">${tribeGlyph(c.tribe)}${esc(c.name)}</span>`).join(' ')}${unlock.length > 4 ? ' \u2026' : ''}` }));
      det.addEventListener('toggle', () => {
        if (!det.open || det.querySelector('.unit-grid')) return;
        det.append(el('div', { class: 'unit-grid mini' }, unlock.map((c) => unitCard(c, { explain: true }))));
      }, { once: false });
      box.append(det);
    }
    box.classList.toggle('can', ok);
  }

  function renderHand() {
    const zone = $('#handZone');
    const p = me();
    if (!hasHand()) { zone.hidden = true; return; }
    zone.hidden = false;
    const row = $('#hand');
    row.replaceChildren();
    const hand = p.hand;
    $('#handCount').innerHTML = `<span class="pill" title="Cards in hand / hand limit">${icon('hand')} ${esc(hand.length)}/${esc(handMax())}</span>`;
    if (!hand.length) {
      row.append(el('p', { class: 'empty', text: finished() ? 'No cards in hand.' : 'Your hand is empty. Recruit from the tavern — recruits wait here until you deploy them.' }));
      return;
    }
    const boardFull = (p.board?.length || 0) >= boardMax();
    hand.forEach((u, i) => {
      const card = unitCard(u);
      const plays = playActionsFor(i);
      const playA = isLegal(`play:${i}`) ? `play:${i}` : plays[plays.length - 1];
      card.dataset.hand = i;
      if (plays.length) {
        card.draggable = true;
        card.tabIndex = 0;
        card.setAttribute('role', 'button');
        appendLabel(card, 'In hand. Enter to deploy to the warband, question mark for how it works.');
        card.addEventListener('dragstart', (e) => { e.dataTransfer.setData('text/plain', `hand:${i}`); card.classList.add('dragging'); document.body.classList.add('dragging-hand'); });
        card.addEventListener('dragend', () => { card.classList.remove('dragging'); document.body.classList.remove('dragging-hand'); });
        card.addEventListener('dblclick', () => act(playA));
        card.addEventListener('keydown', (e) => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); act(playA); } });
      }
      const why = boardFull ? 'Warband is full' : 'Not available now';
      const acts = el('div', { class: 'card-actions' },
        el('button', { type: 'button', class: 'btn play', disabled: !playA, title: playA ? `Deploy ${u.name} to the warband (${playA})` : why, 'aria-label': playA ? `Deploy ${u.name} to the warband` : `Cannot deploy ${u.name}: ${why}`, onclick: () => act(playA), html: playA ? `${icon('up')} Deploy` : esc(boardFull ? 'Board full' : 'Deploy') }),
      );
      row.append(el('div', { class: 'card-wrap in-hand', style: `--fan:${(i - (hand.length - 1) / 2).toFixed(2)}` }, card, infoBtn(u), finished() ? null : acts));
    });
  }

  function dropOnBoard(e, pos) {
    const v = e.dataTransfer.getData('text/plain');
    if (v.startsWith('hand:')) { const a = playAt(+v.slice(5), pos); if (a) act(a); else render(); return true; }
    return false;
  }

  function renderBoard() {
    const p = me();
    const row = $('#board');
    row.replaceChildren();
    const max = boardMax();
    const board = p?.board || [];
    const canAct = !finished();
    for (let i = 0; i < max; i++) {
      const u = board[i];
      if (!u) {
        const slot = el('div', { class: 'slot', 'aria-label': `Empty slot ${i + 1}` }, hasHand() ? 'deploy here' : 'empty');
        slot.addEventListener('dragover', (e) => { e.preventDefault(); slot.classList.add('drop-ok'); });
        slot.addEventListener('dragleave', () => slot.classList.remove('drop-ok'));
        slot.addEventListener('drop', (e) => { e.preventDefault(); slot.classList.remove('drop-ok'); dropOnBoard(e, board.length); });
        row.append(slot);
        continue;
      }
      const card = unitCard(u);
      card.tabIndex = 0;
      card.dataset.index = i;
      if (S.selected === i) card.classList.add('selected');
      const sell = `sell:${i}`;
      const leftA = i > 0 ? findSwap(i, i - 1) : null;
      const rightA = i < board.length - 1 ? findSwap(i, i + 1) : null;
      card.addEventListener('dragover', (e) => { e.preventDefault(); card.classList.add('drop-target'); });
      card.addEventListener('dragleave', () => card.classList.remove('drop-target'));
      card.addEventListener('drop', (e) => {
        e.preventDefault();
        card.classList.remove('drop-target');
        if (dropOnBoard(e, i)) return;
        const from = +e.dataTransfer.getData('text/plain');
        const a = Number.isFinite(from) && from !== i ? findSwap(from, i) : null;
        if (a) act(a); else render();
      });
      if (canAct && board.length > 1) {
        card.draggable = true;
        card.addEventListener('dragstart', (e) => { e.dataTransfer.setData('text/plain', String(i)); card.classList.add('dragging'); });
        card.addEventListener('dragend', () => card.classList.remove('dragging'));
        const pick = () => {
          if (S.selected == null) { S.selected = i; renderBoard(); status(`${enrich(u).name} selected — choose another unit to swap with`); $(`#board .card[data-index="${i}"]`)?.focus(); }
          else if (S.selected === i) { S.selected = null; renderBoard(); }
          else { const a = findSwap(S.selected, i); S.selected = null; if (a) act(a); else renderBoard(); }
        };
        card.addEventListener('click', pick);
        card.addEventListener('keydown', (e) => {
          if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); pick(); }
          if (e.key === 'ArrowLeft' && leftA) { e.preventDefault(); act(leftA); }
          if (e.key === 'ArrowRight' && rightA) { e.preventDefault(); act(rightA); }
        });
        appendLabel(card, `Slot ${i + 1}. Enter to select for swap, arrow keys to move, question mark for how it works.`);
        card.setAttribute('role', 'button');
      }
      const refund = costs().sellRefund;
      const eu = enrich(u);
      const name = `${eu.golden ? 'golden ' : ''}${eu.name}`;
      const gain = Number.isFinite(u.sellGold) ? u.sellGold : refund; // engine total: base refund + direct Sell gold
      const extra = Number.isFinite(u.sellGold) && refund != null ? u.sellGold - refund : 0;
      const sellHasAbility = /(^|\s)Sell:/.test(eu.text || '');
      const sellWhy = `Sell ${name} from the warband (${sell})${gain != null ? `: +${gain} gold` : ''}${extra > 0 ? ` (${refund} base + ${extra} from its Sell ability)` : ''}.${sellHasAbility ? ' Its Sell: ability fires after it leaves.' : ''}`;
      const acts = el('div', { class: 'card-actions' },
        el('button', { type: 'button', class: 'btn', disabled: !leftA, 'aria-label': `Move ${name} left`, title: 'Move left (attacks earlier)', onclick: () => act(leftA), text: '◀' }),
        el('button', { type: 'button', class: `btn sell${extra > 0 ? ' bonus' : ''}`, disabled: !isLegal(sell), 'aria-label': sellWhy, title: sellWhy, onclick: () => act(sell), html: `Sell${gain != null ? ` +${esc(gain)}${icon('coin')}` : ''}` }),
        el('button', { type: 'button', class: 'btn', disabled: !rightA, 'aria-label': `Move ${name} right`, title: 'Move right (attacks later)', onclick: () => act(rightA), text: '▶' }),
      );
      row.append(el('div', { class: 'card-wrap' }, card, infoBtn(u), canAct ? acts : null));
    }
  }

  function renderEndRow() {
    $('#btnEnd').disabled = !isLegal('end');
    $('#btnAuto').disabled = !isLegal('auto');
    const last = S.moves[S.moves.length - 1];
    $('#btnUndo').disabled = finished() || !S.moves.length || last === 'end' || last === 'auto';
    const p = me();
    const waiting = hasHand() && !finished() ? p.hand.length : 0;
    const deployable = waiting && legal().some((a) => a.startsWith('play:'));
    const note = $('#endNote');
    note.hidden = !deployable;
    if (deployable) note.textContent = `${waiting} card${waiting === 1 ? '' : 's'} still in hand — only the warband fights.`;
    syncFab();
  }

  // Full fight records keyed by round:a:b — `combat` (latest round) plus `lastFight`, the viewer's most
  // recent fight with events, which the engine keeps even when an elimination fast-forwards the game.
  function fightDetails(d) {
    const m = new Map();
    const put = (c) => { if (c && typeof c === 'object' && c.round != null) { const k = `${c.round}:${c.a}:${c.b}`; const old = m.get(k); if (!old || (!fightEvents(old).length && fightEvents(c).length)) m.set(k, c); } };
    (d.combat || []).forEach(put);
    put(d.lastFight);
    return m;
  }

  // ---------- Battle log ----------
  function fightOutcome(f, seat) {
    if (f.winner == null || f.winner === -1) return 'tie';
    if (seat == null || (f.a !== seat && f.b !== seat)) return 'neutral';
    return f.winner === seat ? 'win' : 'loss';
  }
  const possessive = (n) => (n === 'You' ? 'Your' : `${n}'s`);
  function fightResult(f, seat) {
    const o = fightOutcome(f, seat);
    const dmg = f.damage ? ` · ${f.damage} damage` : '';
    if (o === 'tie') return 'Draw — no damage';
    if (o === 'win') return `Victory${dmg} dealt`;
    if (o === 'loss') return `Defeat${dmg} taken`;
    const w = nameOf(f.winner);
    return `${w} ${w === 'You' ? 'win' : 'wins'}${dmg}`;
  }
  const fixGrammar = (s) => String(s).replace(/\bYou wins and deals\b/g, 'You win and deal').replace(/\bYou wins\b/g, 'You win').replace(/\bYou's\b/g, 'Your');
  function renderLog() {
    const d = D();
    const log = $('#log');
    log.replaceChildren();
    const only = $('#onlyMine').checked;
    $('#onlyMineText').textContent = S.mode === 'manual' ? 'Only the acting seat\'s fights' : 'Only my fights';
    const seat = human();
    const details = fightDetails(d);
    let rows = (d.history && d.history.length ? d.history : d.combat || []).slice();
    if (only) rows = rows.filter((f) => f.a === seat || f.b === seat);
    rows.sort((x, y) => (y.round ?? 0) - (x.round ?? 0));
    if (!rows.length) { log.append(el('p', { class: 'empty', text: 'No battles yet. End your turn to fight.' })); return; }
    for (const f of rows) {
      const full = details.get(`${f.round}:${f.a}:${f.b}`);
      const o = fightOutcome(f, seat);
      const lines = full ? fightLines(full) : [];
      const box = el(lines.length ? 'details' : 'div', { class: `fight ${o}` });
      const head = `<span class="fight-head"><b>${esc(nameOf(f.a))} vs ${esc(nameOf(f.b))}</b><span class="fight-round">R${esc(f.round)}</span></span><span class="fight-res ${o}">${esc(fightResult(f, seat))}</span>`;
      if (lines.length) {
        box.append(el('summary', { html: head }));
        box.append(el('ol', {}, lines.map((line) => el('li', { text: line }))));
        box.append(el('button', { type: 'button', class: 'btn small', html: `${icon('play')} Watch battle`, onclick: () => openBattle([full]) }));
      } else box.innerHTML = head;
      log.append(box);
    }
  }

  // ---------- Battle playback ----------
  // Engine events (protocol v2): {kind:'attack', step, side:'a'|'b', attackerIndex, targetIndex,
  //   beforeA, beforeB, afterA, afterB, attackerShieldBroken, targetShieldBroken, attackerDied, targetDied, text}
  // and exactly one final {kind:'end', step, winner, damage, afterA, afterB, text}.
  // Indexes refer to the BEFORE snapshots. After each event the displayed boards are replaced by the
  // server's AFTER snapshots, so nothing here derives damage, deaths or stat changes.
  const sideKey = (s) => (s === 'a' || s === 0 || s === 'A' ? 'a' : s === 'b' || s === 1 || s === 'B' ? 'b' : null);
  const otherSide = (s) => (s === 'a' ? 'b' : 'a');
  const fightEvents = (f) => (Array.isArray(f?.events) ? f.events.filter((e) => e && typeof e === 'object') : []);
  function fightLines(f) {
    const ev = fightEvents(f);
    if (ev.length) return ev.map((e) => fixGrammar(e.text || describeEvent(f, e)));
    return (f.log || []).map(fixGrammar);
  }
  function describeEvent(f, e) {
    if (e.kind === 'end') return e.winner === -1 || e.winner == null ? 'Draw.' : `${nameOf(e.winner)} ${nameOf(e.winner) === 'You' ? 'win' : 'wins'}${e.damage ? ` and deal${nameOf(e.winner) === 'You' ? '' : 's'} ${e.damage} damage` : ''}.`;
    if (e.kind === 'attack') {
      const s = sideKey(e.side);
      const att = enrich((s === 'a' ? e.beforeA : e.beforeB)?.[e.attackerIndex] || {});
      const tgt = enrich((s === 'a' ? e.beforeB : e.beforeA)?.[e.targetIndex] || {});
      return `${att.name || 'A unit'} attacks ${tgt.name || 'a unit'}.`;
    }
    return String(e.kind || 'event');
  }
  // Integrity check over server data only: each event's BEFORE equals the previous AFTER.
  const proj = (b) => JSON.stringify((b || []).map((u) => [u.id, u.attack, u.health, !!u.shield, !!u.guard]));
  function chainCheck(f) {
    const ev = fightEvents(f);
    if (!ev.length) return null;
    let a = proj(f.aBoard), b = proj(f.bBoard);
    let ok = true;
    for (const e of ev) {
      if (e.beforeA && e.beforeB && (proj(e.beforeA) !== a || proj(e.beforeB) !== b)) ok = false;
      if (e.afterA) a = proj(e.afterA);
      if (e.afterB) b = proj(e.afterB);
    }
    const end = ev[ev.length - 1];
    const endOk = end.kind === 'end' && end.winner === f.winner && (end.damage ?? 0) === (f.damage ?? 0);
    return { ok: ok && endOk, attacks: ev.filter((e) => e.kind === 'attack').length };
  }

  const reduceMotion = () => matchMedia('(prefers-reduced-motion: reduce)').matches;
  const B = { fights: [], idx: 0, step: 0, playing: false, speed: 1, token: 0, then: null };

  function openBattle(fights, then) {
    B.fights = fights;
    B.idx = 0;
    B.then = then || null;
    try { B.speed = +(localStorage.getItem('bendgrounds.speed') || 1) || 1; }
    catch { B.speed = 1; }
    const dlg = $('#dlgBattle');
    dlg.onclose = () => { B.playing = false; B.token++; const t = B.then; B.then = null; if (t) t(); };
    dlg.showModal();
    showFight(0);
  }

  function showFight(k) {
    B.animating = 0;
    B.idx = k;
    B.step = 0;
    B.playing = false;
    B.token++;
    const f = B.fights[k];
    const body = $('#battleBody');
    body.replaceChildren();
    const seat = human();
    if (B.fights.length > 1) {
      body.append(el('div', { class: 'fight-tabs', role: 'tablist', 'aria-label': 'Fights this round' }, B.fights.map((x, i) => el('button', {
        type: 'button', role: 'tab', class: `chip-btn ${fightOutcome(x, seat)}`, 'aria-selected': String(i === k),
        text: `R${x.round} · ${nameOf(x.a)} vs ${nameOf(x.b)}`, onclick: () => showFight(i),
      }))));
    }
    const ev = fightEvents(f);
    // Perspective: the human (or acting) seat fights from the bottom row.
    const bottom = f.b === seat ? 'b' : 'a';
    const top = otherSide(bottom);
    const who = (s) => nameOf(s === 'a' ? f.a : f.b);
    const arena = el('div', { class: 'arena', dataset: { bottom } },
      el('div', { class: 'arena-side top' }, el('div', { class: 'arena-name', html: `${seatMini(s2id(f, top))} ${esc(who(top))}` }), el('div', { class: 'arena-row', dataset: { side: top } })),
      el('div', { class: 'arena-mid' }, el('div', { class: 'arena-caption', 'aria-live': 'polite', id: 'arenaCaption', text: ev.length ? 'Ready.' : 'Starting warbands — the server sent no step events for this fight.' }), el('div', { class: 'arena-hint', id: 'arenaHint', hidden: true })),
      el('div', { class: 'arena-side bottom' }, el('div', { class: 'arena-row', dataset: { side: bottom } }), el('div', { class: 'arena-name', html: `${seatMini(s2id(f, bottom))} ${esc(who(bottom))}` })),
    );
    body.append(arena);
    const verdict = el('div', { class: 'verdict', id: 'arenaVerdict', hidden: true });
    body.append(verdict);
    const chk = chainCheck(f);
    if (ev.length) {
      const ctr = el('div', { class: 'playback', role: 'group', 'aria-label': 'Battle playback' },
        el('button', { type: 'button', class: 'btn small', id: 'pbRestart', title: 'Restart', 'aria-label': 'Restart battle', html: icon('restart'), onclick: () => { stopPlay(); paintFrame(f, 0); } }),
        el('button', { type: 'button', class: 'btn small primary', id: 'pbPlay', 'aria-label': 'Play', html: `${icon('play')}<span>Play</span>`, onclick: () => (B.playing ? stopPlay() : startPlay()) }),
        el('button', { type: 'button', class: 'btn small', id: 'pbStep', title: 'Next step (→)', 'aria-label': 'Next step', html: `${icon('step')}<span>Step</span>`, onclick: () => { stopPlay(); stepOnce(true); } }),
        el('button', { type: 'button', class: 'btn small', id: 'pbSkip', title: 'Skip to the result', 'aria-label': 'Skip to the result', html: `${icon('skip')}<span>Skip</span>`, onclick: () => { stopPlay(); paintFrame(f, ev.length); } }),
        el('label', { class: 'speed' }, 'Speed ', el('select', { id: 'pbSpeed', 'aria-label': 'Playback speed', onchange: (e) => { B.speed = +e.target.value; try { localStorage.setItem('bendgrounds.speed', String(B.speed)); } catch { /* ignore */ } } },
          [0.5, 1, 2, 4].map((v) => el('option', { value: v, selected: v === B.speed, text: `${v}×` })))),
        el('span', { class: 'pb-progress', id: 'pbProgress' }),
      );
      body.append(ctr);
    }
    const legend = combatLegend();
    if (legend) body.append(legend);
    const lines = fightLines(f);
    const ol = el('ol', { class: 'battle-log', id: 'battleLog', 'aria-label': 'Combat steps' }, lines.map((t, i) => el('li', { text: t, dataset: { i } })));
    if (lines.length) body.append(el('details', { class: 'log-details', open: !ev.length }, el('summary', { text: `Combat log (${lines.length} ${lines.length === 1 ? 'line' : 'lines'})` }), ol));
    else body.append(el('p', { class: 'muted small', text: 'Summary only: the server keeps the full combat record for the latest round.' }));
    if (chk) body.append(el('p', { class: `chain ${chk.ok ? 'ok' : 'bad'}`, text: chk.ok ? `Event chain consistent: ${chk.attacks} attacks, each starting from the previous server snapshot; result matches the engine.` : 'Warning: the server event chain is inconsistent with its own snapshots. The final boards shown are the server\'s.' }));
    if (!ev.length) {
      paintBoards(f.aBoard || [], f.bBoard || [], f);
      showVerdict(f);
      return;
    }
    paintFrame(f, 0);
    if (!reduceMotion()) setTimeout(() => { if (B.fights[B.idx] === f && !B.playing && B.step === 0) startPlay(); }, 350);
  }
  const humanReason = (r) => ({ fuel: 'attack limit reached', empty: 'a warband had no units' })[r] || String(r).replace(/_/g, ' ');
  const s2id = (f, s) => (s === 'a' ? f.a : f.b);
  function seatMini(id) { const p = seatOf(id); return p ? `<span class="sigil-mini">${seatSigil(p)}</span>` : ''; }

  // Compact combat snapshots omit effective golden keywords/text. Keep those from
  // the server's initial full units; dynamic stats and shield always come from snapshots.
  const combatMetadata = new WeakMap();
  const combatKey = (u) => `${u.id}:${u.golden === true}`;
  function combatUnit(f, u) {
    let units = combatMetadata.get(f);
    if (!units) {
      units = new Map([...(f.aBoard || []), ...(f.bBoard || [])].map((unit) => [combatKey(unit), unit]));
      combatMetadata.set(f, units);
    }
    return { ...(units.get(combatKey(u)) || {}), ...u };
  }
  function paintBoards(a, b, f) {
    for (const [s, list] of [['a', a], ['b', b]]) {
      const row = $(`.arena-row[data-side="${s}"]`);
      if (!row) continue;
      row.replaceChildren(...(list.length ? list.map((u, i) => { const c = unitCard(combatUnit(f, u), { mini: true, explain: true }); c.dataset.i = i; return c; }) : [el('p', { class: 'empty', text: 'No units' })]));
    }
  }
  // Frame n = state after the first n events (frame 0 = initial boards).
  function paintFrame(f, n) {
    const ev = fightEvents(f);
    B.step = n;
    const prev = ev[n - 1];
    paintBoards(prev ? prev.afterA || [] : f.aBoard || [], prev ? prev.afterB || [] : f.bBoard || [], f);
    const cap = $('#arenaCaption');
    if (cap) cap.textContent = prev ? fixGrammar(prev.text || describeEvent(f, prev)) : 'Ready.';
    paintHints(prev);
    $$('#battleLog li').forEach((li) => li.classList.toggle('current', +li.dataset.i === n - 1));
    const pr = $('#pbProgress');
    if (pr) pr.textContent = `${n}/${ev.length}`;
    if (n >= ev.length) showVerdict(f); else $('#arenaVerdict').hidden = true;
    syncPlayback(f);
  }
  function showVerdict(f) {
    const v = $('#arenaVerdict');
    const o = fightOutcome(f, human());
    v.className = `verdict ${o === 'neutral' ? '' : o}`;
    const end = fightEvents(f).find((e) => e.kind === 'end');
    const why = end?.finishReason;
    v.textContent = fightResult(f, human()) + (why && why !== 'elimination' ? ` (${humanReason(why)})` : '');
    v.hidden = false;
  }
  function syncPlayback(f) {
    const ev = fightEvents(f);
    const done = B.step >= ev.length;
    const play = $('#pbPlay');
    if (!play) return;
    play.innerHTML = B.playing ? `${icon('pause')}<span>Pause</span>` : `${icon('play')}<span>${done ? 'Replay' : 'Play'}</span>`;
    play.setAttribute('aria-label', B.playing ? 'Pause' : done ? 'Replay' : 'Play');
    $('#pbStep').disabled = done;
    $('#pbSkip').disabled = done;
  }
  function stopPlay() { B.playing = false; B.animating = 0; B.token++; const f = B.fights[B.idx]; if (f) syncPlayback(f); }
  async function startPlay() {
    const f = B.fights[B.idx];
    if (!f) return;
    if (B.step >= fightEvents(f).length) paintFrame(f, 0);
    B.playing = true;
    const token = ++B.token;
    syncPlayback(f);
    while (B.playing && token === B.token && B.step < fightEvents(f).length) {
      await stepOnce(false, token);
      if (token !== B.token) return;
      await sleep(260 / B.speed);
    }
    if (token === B.token) { B.playing = false; syncPlayback(f); }
  }

  // Animate event `B.step` (lunge from attacker to target on the BEFORE boards), then paint its AFTER snapshot.
  async function stepOnce(manual, token = B.token) {
    const f = B.fights[B.idx];
    const ev = fightEvents(f);
    if (!f || B.step >= ev.length) return;
    // A manual step while a strike is animating completes that strike at once (server AFTER snapshot).
    if (B.animating) { const t = B.animating; B.animating = 0; paintFrame(f, t); return; }
    const e = ev[B.step];
    const base = B.step;
    const n = base + 1;
    const motion = !reduceMotion();
    B.animating = n;
    const dur = (ms) => ms / B.speed;
    if (e.kind === 'attack') {
      if (e.beforeA && e.beforeB) paintBoards(e.beforeA, e.beforeB, f);
      const s = sideKey(e.side);
      const att = $(`.arena-row[data-side="${s}"] .card[data-i="${e.attackerIndex}"]`);
      const tgt = $(`.arena-row[data-side="${otherSide(s)}"] .card[data-i="${e.targetIndex}"]`);
      const cap = $('#arenaCaption');
      if (cap) cap.textContent = fixGrammar(e.text || describeEvent(f, e));
      att?.classList.add('attacking');
      tgt?.classList.add('targeted');
      // Rally: BEFORE snapshots are pre-Rally; the engine reports the gain (`rally`) and the attack actually
      // used for this strike (`attackerAttack`). Show both as given, never derive them.
      if (att && e.rally > 0) {
        const atk = att.querySelector('.stat.atk span');
        if (atk && e.attackerAttack != null) atk.textContent = fmtStat(e.attackerAttack);
        att.querySelector('.stat.atk')?.classList.add('rallied');
        att.append(el('span', { class: 'rally-tag', 'aria-hidden': 'true', text: `Rally +${e.rally}` }));
      }
      if (att && tgt && motion) {
        const ra = att.getBoundingClientRect(), rt = tgt.getBoundingClientRect();
        const dx = (rt.left + rt.width / 2) - (ra.left + ra.width / 2), dy = (rt.top + rt.height / 2) - (ra.top + ra.height / 2);
        const lunge = att.animate([
          { transform: 'translate(0,0) scale(1)', offset: 0 },
          { transform: `translate(${dx * -0.06}px,${dy * -0.06}px) scale(1.04)`, offset: 0.25 },
          { transform: `translate(${dx * 0.72}px,${dy * 0.72}px) scale(1.08)`, offset: 0.6 },
          { transform: 'translate(0,0) scale(1)', offset: 1 },
        ], { duration: dur(560), easing: 'ease-in-out' });
        await sleep(dur(330));
        if (token !== B.token && !manual) { lunge.cancel(); if (B.animating === n) B.animating = 0; return; }
        impact(tgt, e.targetShieldBroken, e.targetDied, dur);
        impact(att, e.attackerShieldBroken, e.attackerDied, dur, true);
        await sleep(dur(420));
      } else {
        // Reduced motion: no movement; hold a highlight briefly so the step is still readable.
        if (e.targetShieldBroken) tgt?.classList.add('shield-break');
        if (e.targetDied) tgt?.classList.add('dying');
        if (e.attackerDied) att?.classList.add('dying');
        await sleep(manual ? 0 : dur(500));
      }
      if (token !== B.token && !manual) { if (B.animating === n) B.animating = 0; return; }
    }
    if (B.animating === n) B.animating = 0;
    if (B.step !== base || B.fights[B.idx] !== f) return; // completed, restarted or skipped meanwhile, or fight switched
    paintFrame(f, n);
    if (e.kind === 'attack') {
      // Engine-reported positions of the two fighters in the AFTER boards (-1 = died); no JS reconstruction.
      const s = sideKey(e.side);
      const mark = (side, i, cls) => { if (Number.isInteger(i) && i >= 0) $(`.arena-row[data-side="${side}"] .card[data-i="${i}"]`)?.classList.add(cls); };
      mark(s, e.attackerAfterIndex, 'was-attacker');
      mark(otherSide(s), e.targetAfterIndex, 'was-target');
    }
    if (e.kind === 'end' && motion) $('#arenaVerdict')?.animate([{ transform: 'scale(.8)', opacity: 0 }, { transform: 'scale(1)', opacity: 1 }], { duration: dur(300), easing: 'ease-out' });
  }
  function impact(node, shieldBroken, died, dur, recoil = false) {
    if (!node) return;
    const burst = el('span', { class: `burst${shieldBroken ? ' shield' : ''}`, 'aria-hidden': 'true' });
    node.append(burst);
    if (shieldBroken) node.classList.add('shield-break');
    node.animate([{ transform: 'translateX(0)' }, { transform: `translateX(${recoil ? 3 : -6}px)` }, { transform: `translateX(${recoil ? -3 : 6}px)` }, { transform: 'translateX(0)' }], { duration: dur(240) });
    if (died) node.animate([{ opacity: 1, filter: 'none', transform: 'scale(1)' }, { opacity: 0.15, filter: 'grayscale(1) brightness(.5)', transform: 'scale(.82) rotate(-4deg)' }], { duration: dur(420), delay: dur(160), fill: 'forwards' });
  }

  function openOver() {
    const d = D();
    const rank = Array.isArray(d.rank) ? d.rank : null;
    const seat = human();
    const list = $('#standings');
    list.replaceChildren();
    const order = rank || players().map((p) => p.id);
    order.forEach((id, i) => {
      const p = seatOf(id);
      if (!p) return;
      list.append(el('li', { class: id === seat && S.mode !== 'manual' ? 'me' : '', html: `<span class="place">${rank ? i + 1 : '–'}</span><span class="nm">${esc(p.name)}</span><span class="pill hp">${icon('heart')} ${esc(p.hp)}</span><span class="pill tier">${icon('star')} ${esc(p.tier)}</span>` }));
    });
    const place = rank ? rank.indexOf(seat) + 1 : null;
    $('#overLead').textContent = S.mode === 'manual'
      ? `${nameOf(d.winner)} ${nameOf(d.winner) === 'You' ? 'take' : 'takes'} the grounds.`
      : d.winner === seat ? 'Your warband stands alone. Victory.' : `${nameOf(d.winner)} wins.${place ? ` You finished #${place} of ${rank.length}.` : ''}`;
    $('#dlgOver').showModal();
  }

  // ---------- Side panels ----------
  function renderCmdList() {
    const box = $('#cmdList');
    box.replaceChildren();
    const la = legal();
    if (!la.length) { box.append(el('p', { class: 'empty', text: finished() ? 'Game finished — no legal moves.' : 'No legal moves.' })); }
    la.forEach((a) => box.append(el('button', { type: 'button', class: 'btn small', text: a, onclick: () => act(a) })));
    $('#btnAutoAll').disabled = !isLegal('auto') && !S.autoplay;
    $('#btnAutoAll').textContent = S.autoplay ? 'Stop autoplay' : 'Autoplay to the end';
  }

  function renderMoves() {
    const ol = $('#moves');
    ol.replaceChildren();
    let turn = [];
    let n = 1;
    const flush = (open) => {
      if (!turn.length && !open) return;
      ol.append(el('li', {}, el('b', { text: `T${n}` }), turn.length ? turn.map((m) => el('span', { class: `mv${m === 'end' || m === 'auto' ? ' end' : ''}`, text: m })) : el('span', { class: 'muted', text: '…' })));
      turn = [];
      n++;
    };
    for (const m of S.moves) { turn.push(m); if (m === 'end' || m === 'auto') flush(); }
    if (!finished()) flush(true); else flush();
    if (!S.moves.length) ol.replaceChildren(el('li', { class: 'muted', text: 'No moves yet.' }));
  }

  function renderAgentDoc() {
    const p = gamePath(S.seed ?? 42, S.mode, S.moves);
    $('#agentCurl').textContent = `curl -s '${absUrl(p)}'\ncurl -s '${absUrl('/api/rules')}'`;
  }

  // ---------- Rules ----------
  async function fetchRules() {
    try { S.rules = (await getJSON('/api/rules')).body; } catch { /* shown on open */ }
    return S.rules;
  }
  function renderValue(v) {
    if (v == null) return el('span', { class: 'muted', text: '—' });
    if (Array.isArray(v)) {
      if (v.every((x) => typeof x !== 'object')) return el('span', { text: v.join(', ') });
      return el('ul', {}, v.map((x) => el('li', {}, typeof x === 'object' ? renderDl(x) : String(x))));
    }
    if (typeof v === 'object') return renderDl(v);
    return el('span', { text: String(v) });
  }
  function renderDl(obj) {
    const dl = el('dl');
    for (const [k, v] of Object.entries(obj)) dl.append(el('dt', { text: k }), el('dd', {}, renderValue(v)));
    return dl;
  }
  async function openRules() {
    const body = $('#rulesBody');
    if (!$('#dlgRules').open) $('#dlgRules').showModal();
    const r = S.rules || (await fetchRules());
    body.replaceChildren();
    if (!r) { body.append(el('p', { class: 'empty', text: 'Could not load /api/rules. Is the server running?' })); return; }
    const used = new Set(['protocolVersion', 'schemaVersion', 'glossary', 'definitions']);
    if (r.game) { used.add('game'); body.append(el('h3', { text: `${r.game}${r.protocolVersion ? ` · protocol ${r.protocolVersion}` : ''}` })); }
    body.append(rulesGuide());
    const cards = r.cards || r.units;
    const tribeInfo = r.tribes && !Array.isArray(r.tribes) ? r.tribes : null; // {Ember: "text"} if published
    if (Array.isArray(cards)) {
      used.add('cards'); used.add('units'); used.add('tribes');
      body.append(el('h3', { id: 'rg-units', text: `Units (${cards.length})` }), el('p', { class: 'muted small', text: 'Tap or focus a unit and press Enter for how it works; tap a keyword or a trigger on any card for its definition.' }));
      const tribes = [...new Set(cards.map((c) => c.tribe))];
      const tabs = el('div', { class: 'fight-tabs', role: 'tablist', 'aria-label': 'Tribes' });
      const pane = el('div', { class: 'tribe-pane' });
      const show = (t) => {
        $$('button', tabs).forEach((b) => b.setAttribute('aria-selected', String(b.dataset.t === t)));
        pane.replaceChildren();
        const info = tribeInfo?.[t];
        if (info) pane.append(el('p', { class: 'muted', text: typeof info === 'string' ? info : info.text || info.description || '' }));
        const tiers = [...new Set(cards.filter((c) => c.tribe === t).map((c) => c.tier))].sort((a, b) => a - b);
        for (const tier of tiers) {
          pane.append(el('div', { class: 'tier-head', html: `${icon('star')} Tier ${esc(tier)}` }));
          const g = el('div', { class: 'unit-grid' });
          cards.filter((c) => c.tribe === t && c.tier === tier).forEach((c) => g.append(unitCard(c, { explain: true })));
          pane.append(g);
        }
      };
      tribes.forEach((t) => tabs.append(el('button', { type: 'button', role: 'tab', class: `chip-btn t-${t}`, dataset: { t }, html: `${tribeGlyph(t)} ${esc(t)} · ${cards.filter((c) => c.tribe === t).length}`, onclick: () => show(t) })));
      body.append(tabs, pane);
      if (tribes.length) show(tribes[0]);
    }
    if (Array.isArray(r.rules)) {
      used.add('rules');
      body.append(el('h3', { id: 'rg-all', text: 'All rules (engine text)' }), el('ol', { class: 'rule-list' }, r.rules.map((t) => el('li', { text: String(t) }))));
    }
    if (Array.isArray(r.actions) && r.actions.every((x) => typeof x === 'string')) {
      used.add('actions');
      body.append(el('h3', { text: 'Move grammar' }), el('p', { class: 'chips' }, r.actions.map((a) => el('code', { class: 'chip', text: a }))));
    }
    if (r.modes && typeof r.modes === 'object') { used.add('modes'); body.append(el('h3', { text: 'Modes' }), renderValue(r.modes)); }
    for (const k of ['summary', 'text', 'overview', 'description']) {
      if (typeof r[k] === 'string') { body.append(el('p', { text: r[k] })); used.add(k); }
      else if (Array.isArray(r[k])) { r[k].forEach((t) => body.append(el('p', { text: String(t) }))); used.add(k); }
    }
    for (const k of ['costs', 'upgradeCosts', 'economy', 'combat', 'scoring', 'keywords']) {
      if (r[k] != null) { used.add(k); body.append(el('h3', { text: ({ upgradeCosts: 'Upgrade costs (from tier)' })[k] || k[0].toUpperCase() + k.slice(1) }), renderValue(r[k])); }
    }
    const rest = Object.fromEntries(Object.entries(r).filter(([k]) => !used.has(k)));
    if (Object.keys(rest).length) body.append(el('h3', { text: 'More' }), renderDl(rest));
    body.append(el('details', {}, el('summary', { text: 'Raw JSON' }), el('pre', { class: 'code', text: JSON.stringify(r, null, 2) })));
  }

  // ---------- Dialogs / new game ----------
  function openTitle() {
    const saved = loadSaved();
    const resumable = saved && saved.compatible;
    $('#resumeBox').hidden = !resumable;
    if (resumable) $('#resumeInfo').textContent = `· seed ${saved.seed}${saved.mode === 'manual' ? ' · manual' : ''} · ${saved.moves.length} moves`;
    // Older saves (v1 key, or a v2-key save recorded under another protocol) are kept, never replayed automatically.
    const old = legacySave() || (saved && !saved.compatible ? saved : null);
    const lg = $('#legacyBox');
    lg.hidden = !old;
    if (old) {
      $('#legacyInfo').textContent = `A saved game from an older protocol (seed ${old.seed}, ${old.moves.length} moves) is kept but not replayed: in protocol ${serverProtocol()} the same moves can mean something different.`;
      $('#btnLegacyCopy').onclick = () => copy(`seed=${old.seed} mode=${old.mode} moves=${old.moves.join(',')}`, 'Old transcript copied');
    }
    $('#seedInput').value = String(Math.floor(Math.random() * 1e6));
    $('#btnTitleCancel').hidden = !S.data;
    const err = $('#banner').hidden ? '' : $('#bannerText').textContent;
    $('#titleErr').textContent = err;
    $('#titleErr').hidden = !err;
    $('#dlgTitle').showModal();
  }
  async function startNew(seed, mode) {
    S.autoplay = false;
    S.scout = null;
    $('#dlgTitle').close();
    const ok = await load(seed, mode, []);
    if (ok) status(`New game · seed ${seed}`);
  }

  async function autoplayLoop() {
    if (S.autoplay) { S.autoplay = false; renderCmdList(); return; }
    S.autoplay = true;
    renderCmdList();
    while (S.autoplay && !finished() && isLegal('auto')) {
      const ok = await act('auto', { quiet: true });
      if (!ok) break;
      await sleep(120);
    }
    S.autoplay = false;
    renderCmdList();
    if (finished()) openOver();
  }

  function wire() {
    $('#btnNew').onclick = openTitle;
    $('#btnRules').onclick = openRules;
    $('#btnAgent').onclick = () => { renderAgentDoc(); $('#dlgAgent').showModal(); };
    $('#btnRandomSeed').onclick = () => { $('#seedInput').value = String(Math.floor(Math.random() * 1e6)); };
    $('#btnTitleCancel').onclick = () => $('#dlgTitle').close();
    $('#formNew').addEventListener('submit', (e) => {
      e.preventDefault();
      const seed = parseSeed($('#seedInput').value);
      if (seed == null) { shake($('#seedInput')); $('#seedInput').focus(); return; }
      const mode = (new FormData(e.target).get('mode')) === 'manual' ? 'manual' : 'bots';
      startNew(seed, mode);
    });
    $('#btnResume').onclick = () => { const s = loadSaved(); $('#dlgTitle').close(); if (s && s.compatible) load(s.seed, s.mode, s.moves, { fromResume: true }); };
    $('#btnEnd').onclick = () => act('end');
    $('#btnEndFab').onclick = () => act('end');
    S.endVisible = true;
    if ('IntersectionObserver' in window) {
      new IntersectionObserver(([e]) => { S.endVisible = e.isIntersecting; syncFab(); }).observe($('#btnEnd'));
    }
    $('#btnAuto').onclick = () => act('auto');
    $('#btnAutoAll').onclick = autoplayLoop;
    $('#btnUndo').onclick = undo;
    $('#btnOverNew').onclick = () => { $('#dlgOver').close(); openTitle(); };
    $('#bannerClose').onclick = hideBanner;
    $('#bannerRetry').onclick = () => { const r = S.lastRetry; hideBanner(); if (r) r(); };
    $('#onlyMine').onchange = renderLog;
    $('#btnCopyUrl').onclick = () => copy(shareLink(), 'Replay link copied');
    $('#btnCopyApi').onclick = () => copy(absUrl(gamePath(S.seed, S.mode, S.moves)), 'API URL copied');
    $('#btnCopyMoves').onclick = () => copy(S.moves.join(','), 'Moves copied');
    $('#btnCopyCurl').onclick = () => copy($('#agentCurl').textContent, 'Command copied');
    $$('dialog [data-close]').forEach((b) => (b.onclick = () => b.closest('dialog').close()));
    // Tapping a keyword or a trigger on any card explains that term. Capture phase, so the tap never
    // also buys, deploys or selects the card underneath (works for touch, mouse and pen).
    document.addEventListener('click', (e) => {
      const t = e.target.closest?.('.card [data-term]');
      if (!t || t.closest('#dlgExplain')) return;
      e.preventDefault();
      e.stopPropagation();
      openExplain({ term: t.dataset.term, label: t.textContent.trim(), tribe: t.closest('.card')?.dataset.tribe }, t.closest('.card-wrap')?.querySelector('.card-info') || t.closest('.card'));
    }, true);
    document.addEventListener('dblclick', (e) => { if (e.target.closest?.('.card [data-term]')) { e.preventDefault(); e.stopPropagation(); } }, true);
    $('#dlgExplain').addEventListener('close', () => { const o = S.explainOpener; S.explainOpener = null; if (o && o.isConnected && typeof o.focus === 'function') o.focus({ preventScroll: true }); });
    $$('dialog').forEach((d) => d.addEventListener('click', (e) => { if (e.target === d && d.id !== 'dlgTitle') d.close(); }));

    // Tabs (WAI-ARIA pattern)
    const tabs = $$('.side [role="tab"]');
    const select = (t) => {
      tabs.forEach((x) => { const on = x === t; x.setAttribute('aria-selected', String(on)); x.tabIndex = on ? 0 : -1; $('#' + x.getAttribute('aria-controls')).hidden = !on; });
      t.focus();
    };
    tabs.forEach((t, i) => {
      t.onclick = () => select(t);
      t.onkeydown = (e) => {
        if (e.key === 'ArrowRight') select(tabs[(i + 1) % tabs.length]);
        if (e.key === 'ArrowLeft') select(tabs[(i - 1 + tabs.length) % tabs.length]);
      };
    });

    // Browsers freeze timers and animations in hidden tabs: pause playback instead of stalling mid-strike.
    document.addEventListener('visibilitychange', () => {
      if (document.hidden && B.playing) { stopPlay(); const f = B.fights[B.idx]; if (f) paintFrame(f, B.step); }
    });

    // Keyboard shortcuts: each maps to an exact legal action string.
    document.addEventListener('keydown', (e) => {
      if (e.metaKey || e.ctrlKey || e.altKey) return;
      if (/^(INPUT|TEXTAREA|SELECT)$/.test(e.target.tagName)) return;
      // "?" on a focused card (or its buttons) explains it.
      if (e.key === '?' && !$('#dlgExplain').open) {
        const c = e.target.closest?.('.card-wrap')?.querySelector('.card') || e.target.closest?.('.card');
        if (c?._unit) { e.preventDefault(); openExplain({ card: c._unit }, e.target); return; }
      }
      if ($('#dlgExplain').open) return;
      if ($('#dlgBattle').open) {
        const f = B.fights[B.idx];
        if (!f || !fightEvents(f).length) return;
        if (e.key === ' ' && e.target.tagName !== 'BUTTON') { e.preventDefault(); B.playing ? stopPlay() : startPlay(); }
        if (e.key === 'ArrowRight') { e.preventDefault(); stopPlay(); stepOnce(true); }
        if (e.key.toLowerCase() === 's') { e.preventDefault(); stopPlay(); paintFrame(f, fightEvents(f).length); }
        return;
      }
      if (document.querySelector('dialog[open]')) return;
      const k = e.key.toLowerCase();
      const map = { r: 'roll', f: 'freeze', u: 'upgrade', i: 'invest', e: 'end' };
      let a = map[k];
      if (/^[1-9]$/.test(e.key)) a = `buy:${+e.key - 1}`;
      // Shift+digit deploys hand card N.
      const shifted = { '!': 1, '@': 2, '#': 3, '$': 4, '%': 5, '^': 6, '&': 7 }[e.key] || (e.shiftKey && /^Digit[1-7]$/.test(e.code) ? +e.code.slice(5) : null);
      if (shifted) a = playAt(shifted - 1, me()?.board?.length ?? 0);
      if (k === 'z') { e.preventDefault(); undo(); return; }
      if (k === 'escape' && S.selected != null) { S.selected = null; renderBoard(); return; }
      if (a && isLegal(a)) { e.preventDefault(); act(a); }
    });
  }

  function syncFab() {
    $('#btnEndFab').hidden = S.endVisible !== false || !isLegal('end');
  }

  function undo() {
    const last = S.moves[S.moves.length - 1];
    if (S.busy || finished() || !last || last === 'end' || last === 'auto') return;
    load(S.seed, S.mode, S.moves.slice(0, -1)).then((ok) => ok && status(`Undid ${last}`));
  }

  async function copy(text, msg) {
    try { await navigator.clipboard.writeText(text); status(msg); }
    catch { window.prompt('Copy:', text); }
  }

  // Unversioned replay link: let the player choose explicitly. Resolves true if a game was loaded.
  function askLegacyLink(seed, mode, moves) {
    return new Promise((resolve) => {
      const dlg = $('#dlgLegacyLink');
      $('#legacyLinkInfo').textContent = `Seed ${seed}, ${mode} mode, ${moves.length} move${moves.length === 1 ? '' : 's'}${moves.length ? `: ${moves.slice(0, 8).join(',')}${moves.length > 8 ? ',…' : ''}` : ''}.`;
      let done = false;
      const finish = async (replay) => {
        if (done) return; done = true;
        dlg.close();
        resolve(replay ? await load(seed, mode, moves, { fromResume: true }) : false);
      };
      $('#btnLegacyReplay').onclick = () => finish(true);
      $('#btnLegacyFresh').onclick = () => finish(false);
      dlg.onclose = () => finish(false);
      dlg.showModal();
    });
  }
  const shareLink = () => `${location.origin === 'null' ? '' : location.origin}${location.pathname}?seed=${S.seed}&mode=${S.mode}&moves=${S.moves.join(',')}&v=${CLIENT_PROTOCOL}`;

  // ---------- Boot ----------
  async function boot() {
    wire();
    await fetchRules(); // needed first: card catalog for combat snapshots, and the protocol for save compatibility
    await detectProtocol();
    if (S.rules?.maxRounds != null) $('#leadRounds').textContent = S.rules.maxRounds;
    if (S.rules?.costs?.startHp != null) $('#leadHp').textContent = S.rules.costs.startHp;
    const params = new URLSearchParams(location.search);
    if (params.has('seed')) {
      const seed = parseSeed(params.get('seed'));
      const moves = (params.get('moves') || '').split(',').filter(Boolean);
      const mode = params.get('mode') === 'manual' ? 'manual' : 'bots';
      const vs = params.getAll('v');
      // Shared replay link: load it once, then drop the query so reloads resume the live game from localStorage.
      history.replaceState(null, '', location.pathname + (params.get('api') ? `?api=${encodeURIComponent(params.get('api'))}` : ''));
      const shapeOk = seed != null && moves.every((m) => MOVE_RE.test(m));
      if (!shapeOk) banner('Ignored replay link: seed must be 0–4294967295 and moves must look like buy:0,play:0,end.');
      else if (vs.length === 1 && vs[0] === String(CLIENT_PROTOCOL)) {
        if (await load(seed, mode, moves, { fromResume: true })) return;
      } else if (vs.length === 0) {
        // Unversioned link: made before protocol 2, where the same moves meant something else. Never replay silently.
        if (await askLegacyLink(seed, mode, moves)) return;
      } else banner(`Ignored replay link: it was made for protocol ${vs.join(',')}, and this server speaks protocol ${CLIENT_PROTOCOL} only.`);
      const keepMsg = $('#banner').hidden ? null : $('#bannerText').textContent;
      const prev = loadSaved();
      if (prev?.compatible && await load(prev.seed, prev.mode, prev.moves, { fromResume: true })) {
        if (keepMsg) banner(`${keepMsg} Your saved game was resumed instead.`);
        return;
      }
      if (keepMsg) banner(keepMsg);
      openTitle();
      return;
    }
    const saved = loadSaved();
    if (saved?.compatible) {
      const ok = await load(saved.seed, saved.mode, saved.moves, { fromResume: true });
      if (ok) { status(`Resumed seed ${saved.seed}`); return; }
    }
    openTitle();
  }
  boot();
})();
