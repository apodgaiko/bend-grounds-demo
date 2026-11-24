/* Focused browser-shell logic tests using real app source and deferred transport; no UI or server. */
'use strict';
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');
const source = fs.readFileSync(path.join(__dirname, '../web/app.js'), 'utf8');
function section(start, end) {
  const a = source.indexOf(start), b = source.indexOf(end, a);
  assert(a >= 0 && b > a, `source section ${start}`);
  return source.slice(a, b);
}
function requestHarness() {
  const pending = [], saved = [], banners = [];
  const S = { seed: 1, mode: 'bots', moves: [], data: { players: [], phase: 'recruit' }, busy: false };
  const context = vm.createContext({ S, MOVE_RE: /^[a-z]+(?::\d+)*$/,
    getJSON: () => new Promise((resolve, reject) => pending.push({ resolve, reject })),
    gamePath: (...args) => args, setBusy: value => { S.busy = value; },
    save: () => saved.push(JSON.stringify(S)), render() {}, finished: () => false,
    banner: message => banners.push(message), hideBanner() {}, seatOf: () => null,
    errMessage: String, openOver() {}, shake() {}, $: () => ({}), flashNew() {},
    newGoldens: () => [], status() {}, afterRoundChange() {},
  });
  vm.runInContext(section('  let gameRequest =', '  // Cosmetic:')+'\nglobalThis.api = { load, act };', context);
  return { ...context.api, pending, saved, banners, S };
}
const response = label => ({ body: { players: [], phase: 'recruit', label } });
async function races() {
  // An old action cannot write/save after a new game completes.
  let h = requestHarness(), old = h.act('end'), fresh = h.load(99, 'manual', []);
  h.pending[1].resolve(response('new')); await fresh;
  h.pending[0].resolve(response('old')); assert.equal(await old, false);
  assert.equal(h.S.seed, 99); assert.equal(h.S.data.label, 'new');
  assert.equal(h.saved.length, 1); assert.equal(h.S.busy, false);
  // An old completion must not unlock the UI while the newer request is pending.
  h = requestHarness(); old = h.act('end'); fresh = h.load(99, 'manual', []);
  h.pending[0].resolve(response('old')); await old;
  assert.equal(h.S.busy, true); assert.equal(h.saved.length, 0);
  h.pending[1].resolve(response('new')); await fresh; assert.equal(h.S.busy, false);
  // Stale errors neither publish retry banners nor release the new request's busy state.
  h = requestHarness(); old = h.load(2, 'bots', []); fresh = h.load(3, 'bots', []);
  h.pending[0].reject(new Error('stale')); await old;
  assert.equal(h.banners.length, 0); assert.equal(h.S.busy, true);
  h.pending[1].resolve(response('latest')); await fresh;
  assert.equal(h.S.seed, 3); assert.equal(h.saved.length, 1);
}
function metadata() {
  const catalog = { id: 7, name: 'Spark Imp', rally: 1, income: 1, keywords: ['Rally', 'Income'], text: 'Regular' };
  const context = vm.createContext({ S: { rules: { cards: [catalog] } } });
  const labelsEnd = source.indexOf('\n', source.indexOf('  const KW_LABEL ='));
  const cards = source.slice(source.indexOf('  const catalog ='), labelsEnd);
  vm.runInContext(cards + section('  const combatMetadata =', '  function paintBoards(') + '\nglobalThis.api = { combatUnit, enrich, keywordsOf };', context);
  const golden = { ...catalog, golden: true, rally: 2, income: 2, text: 'Effective golden', abilities: ['effective'], attack: 4, health: 6, shield: true };
  const f = { aBoard: [golden], bBoard: [{ ...catalog, golden: false }] };
  const compact = { id: 7, golden: true, attack: 8, health: 3, shield: false, guard: false };
  const unit = context.api.enrich(context.api.combatUnit(f, compact));
  assert.equal(unit.rally, 2); assert.equal(unit.income, 2); assert.equal(unit.text, 'Effective golden');
  assert.equal(unit.attack, 8); assert.equal(unit.health, 3); assert.equal(unit.shield, false);
  const labels = Array.from(context.api.keywordsOf(unit), x => x.label);
  assert(labels.includes('Rally 2')); assert(labels.includes('Income 2')); assert(!labels.includes('Shield'));
  const plain = context.api.enrich(context.api.combatUnit(f, { ...compact, golden: false }));
  assert.equal(plain.rally, 1);
  const otherFight = { aBoard: [{ ...golden, rally: 9 }], bBoard: [] };
  assert.equal(context.api.combatUnit(otherFight, compact).rally, 9);
}
function origins() {
  for (const [input, expected] of [
    ['http://127.0.0.1:9999', 'http://127.0.0.1:9999'], ['http://localhost:8765/', 'http://localhost:8765'],
    ['http://[::1]:8765', 'http://[::1]:8765'], ['https://example.org', ''],
    ['http://example.org', ''], ['http://localhost.evil.test', ''], ['http://user@localhost', ''],
    ['http://localhost/path', ''], ['http://localhost/?q=1', ''], ['not a url', ''],
  ]) {
    const context = vm.createContext({ URL, URLSearchParams, location: { search: '?api='+encodeURIComponent(input), protocol: 'http:' }, console: { warn() {} } });
    vm.runInContext(section('  const API =', '  // Protocol v2')+'\nglobalThis.result = API;', context);
    assert.equal(context.result, expected, input);
  }
}
(async () => { await races(); metadata(); origins(); console.log('PASS: request races/busy ownership, golden metadata, loopback origins'); })().catch(error => { console.error(error); process.exitCode = 1; });
