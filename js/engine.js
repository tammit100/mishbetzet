// School timetable engine: model, generator, conflicts, rooms, substitutes, demo data.
// Pure JS, no DOM. Usable in the page, a Web Worker, and Node.
function SchoolEngine() {
  const E = {};

  // ---------- utils ----------
  E.rng = function (seed) {
    let a = (seed >>> 0) || 1;
    return function () {
      a |= 0; a = (a + 0x6D2B79F5) | 0;
      let t = Math.imul(a ^ (a >>> 15), 1 | a);
      t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
      return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
  };
  E.uid = function (prefix) { return (prefix || "x") + Math.random().toString(36).slice(2, 9); };
  E.pidOf = function (reqId, k) { return reqId + ":" + k; };
  E.reqOfPid = function (pid) { return pid.slice(0, pid.lastIndexOf(":")); };
  E.DAY_NAMES = ["א", "ב", "ג", "ד", "ה", "ו"];

  // ---------- model ----------
  // data = {config, teachers, classes, rooms, reqs}
  // config: {schoolName, days:["א",...], periods:[9,9,...], firstPeriod:1, times:[[start,end],...]}
  // teacher: {id,name,subjects:[],off:["2","3-4"],maxPerDay?}
  // class: {id,name,grade,homeRoom?}
  // room: {id,name,type}
  // req: {id, classIds:[], hours, maxPerDay, double:false, label?, groups:[{subject,teacherId,roomType}]}
  E.buildModel = function (data) {
    const cfg = data.config;
    const D = cfg.days.length;
    const P = Math.max.apply(null, cfg.periods);
    const nS = D * P;
    const valid = new Uint8Array(nS);
    for (let d = 0; d < D; d++) for (let p = 0; p < cfg.periods[d]; p++) valid[d * P + p] = 1;
    const tIdx = new Map(), cIdx = new Map(), rIdx = new Map();
    data.teachers.forEach((t, i) => tIdx.set(t.id, i));
    data.classes.forEach((c, i) => cIdx.set(c.id, i));
    data.rooms.forEach((r, i) => rIdx.set(r.id, i));
    const types = new Map(); // type -> supply
    data.rooms.forEach(r => types.set(r.type, (types.get(r.type) || 0) + 1));
    const tOff = data.teachers.map(t => {
      const s = new Uint8Array(nS);
      (t.off || []).forEach(o => {
        const parts = String(o).split("-");
        const d = +parts[0];
        if (!(d >= 0 && d < D)) return;
        if (parts.length === 1) for (let p = 0; p < P; p++) s[d * P + p] = 1;
        else { const p = +parts[1]; if (p >= 0 && p < P) s[d * P + p] = 1; }
      });
      return s;
    });
    const reqs = data.reqs.map((r, i) => {
      const classes = (r.classIds || []).map(id => cIdx.get(id)).filter(x => x !== undefined);
      const teachers = [];
      const typeNeed = new Map();
      (r.groups || []).forEach(g => {
        const ti = tIdx.get(g.teacherId);
        if (ti !== undefined && teachers.indexOf(ti) < 0) teachers.push(ti);
        const ty = g.roomType || "";
        if (ty && ty !== "none") typeNeed.set(ty, (typeNeed.get(ty) || 0) + 1);
      });
      return {
        i, id: r.id, src: r, classes, teachers, typeNeed: Array.from(typeNeed.entries()),
        hours: Math.max(0, r.hours | 0), maxPerDay: r.maxPerDay || 1, double: !!r.double,
      };
    });
    const reqIdx = new Map(); reqs.forEach(r => reqIdx.set(r.id, r.i));
    // ----- capacity: students per group vs seats per room -----
    // For every room type we build nested resources "rooms of this type with >= T seats".
    // A group needing n seats uses one unit of every threshold <= n. Because the sets are nested,
    // "demand <= supply at every threshold" guarantees a valid room assignment (Hall's condition).
    const capOf = rm => (+rm.capacity > 0 ? +rm.capacity : Infinity);
    const classStudents = new Map(data.classes.map(c => [c.id, +c.students || 0]));
    const maxCap = new Map();
    data.rooms.forEach(rm => maxCap.set(rm.type, Math.max(maxCap.get(rm.type) || 0, capOf(rm))));
    const needOf = (r, g) => {
      if (+g.students > 0) return +g.students;
      const tot = (r.classIds || []).reduce((a, id) => a + (classStudents.get(id) || 0), 0);
      return tot ? Math.ceil(tot / Math.max(1, (r.groups || []).length)) : 0;
    };
    const thrByType = new Map();
    const tooBig = [];
    reqs.forEach(r => {
      r.needs = (r.src.groups || []).map(g => needOf(r.src, g));
      (r.src.groups || []).forEach((g, gi) => {
        const ty = g.roomType || ""; if (!ty || ty === "none") return;
        let n = r.needs[gi];
        const mc = maxCap.get(ty) || 0;
        if (n > mc && mc > 0) { tooBig.push({ reqId: r.id, gi, need: n, max: mc, type: ty }); n = mc; }
        let a = thrByType.get(ty); if (!a) thrByType.set(ty, a = new Set([0])); a.add(n);
      });
    });
    const resources = [], resKey = new Map();
    thrByType.forEach((set, ty) => {
      Array.from(set).sort((a, b) => a - b).forEach((thr, j) => {
        resKey.set(ty + "|" + j, resources.length);
        resources.push({ type: ty, j, thr, supply: data.rooms.filter(rm => rm.type === ty && capOf(rm) >= thr).length });
      });
    });
    const thrIndex = (ty, n) => { const arr = Array.from(thrByType.get(ty) || [0]).sort((a, b) => a - b); let k = 0; arr.forEach((t, i) => { if (t <= n) k = i; }); return k; };
    reqs.forEach(r => {
      const perType = new Map();
      (r.src.groups || []).forEach((g, gi) => {
        const ty = g.roomType || ""; if (!ty || ty === "none") return;
        const mc = maxCap.get(ty) || 0;
        const k = thrIndex(ty, Math.min(r.needs[gi], mc || Infinity));
        let a = perType.get(ty); if (!a) perType.set(ty, a = []); a.push(k);
      });
      r.resNeed = [];
      perType.forEach((ks, ty) => {
        const top = Math.max.apply(null, ks);
        for (let j = 0; j <= top; j++) { const add = ks.filter(k => k >= j).length; if (add) r.resNeed.push([resKey.get(ty + "|" + j), add]); }
      });
    });
    // room restrictions: noEvents = not for exams/activities/re-seating; reservedFor = only these classes
    const roomFor = (rm, classIds, purpose) => {
      if (!rm) return false;
      const res = rm.reservedFor || [];
      if (res.length) { if (purpose === "event") return false; if (!(classIds || []).length || !(classIds || []).every(c => res.indexOf(c) >= 0)) return false; }
      if (rm.noEvents && purpose !== "keep") return false;
      return true;
    };
    return { data, cfg, D, P, nS, valid, tIdx, cIdx, rIdx, types, tOff, reqs, reqIdx, resources, capOf, tooBig, roomFor };
  };

  E.slotDP = function (M, s) { return { d: Math.floor(s / M.P), p: s % M.P }; };
  E.slotLabel = function (M, s) {
    const d = Math.floor(s / M.P), p = s % M.P;
    return "יום " + M.cfg.days[d] + "׳ שעה " + (p + (M.cfg.firstPeriod || 0));
  };

  // all units (pids) required by the data
  E.allPids = function (M) {
    const out = [];
    M.reqs.forEach(r => { for (let k = 0; k < r.hours; k++) out.push(E.pidOf(r.id, k)); });
    return out;
  };

  // ---------- conflicts & occupancy ----------
  E.occupancy = function (M, placements) {
    const byClass = new Map(), byTeacher = new Map(), byRoom = new Map(), bySlot = new Map();
    const push = (map, key, v) => { let a = map.get(key); if (!a) map.set(key, a = []); a.push(v); };
    for (const pid in placements) {
      const pl = placements[pid];
      const ri = M.reqIdx.get(E.reqOfPid(pid));
      if (ri === undefined || pl == null || pl.s == null) continue;
      const r = M.reqs[ri];
      if (+pid.split(":").pop() >= r.hours) continue;
      push(bySlot, pl.s, pid);
      r.classes.forEach(c => push(byClass, c + "|" + pl.s, pid));
      r.teachers.forEach(t => push(byTeacher, t + "|" + pl.s, pid));
      (pl.rooms || []).forEach(rid => { if (rid) push(byRoom, rid + "|" + pl.s, pid); });
    }
    return { byClass, byTeacher, byRoom, bySlot };
  };

  E.conflicts = function (M, placements) {
    const occ = E.occupancy(M, placements);
    const out = [];
    const data = M.data;
    occ.byClass.forEach((pids, key) => {
      if (pids.length > 1) { const [c, s] = key.split("|"); out.push({ kind: "class", who: data.classes[+c].name, s: +s, pids }); }
    });
    occ.byTeacher.forEach((pids, key) => {
      if (pids.length > 1) { const [t, s] = key.split("|"); out.push({ kind: "teacher", who: data.teachers[+t].name, s: +s, pids }); }
    });
    occ.byRoom.forEach((pids, key) => {
      const [rid, s] = key.split("|");
      // the same pid can list a room once per group; count distinct uses
      let uses = 0; pids.forEach(pid => { (placements[pid].rooms || []).forEach(x => { if (x === rid) uses++; }); });
      const ri = M.rIdx.get(rid);
      if (uses > pids.length || pids.length > 1) out.push({ kind: "room", who: ri !== undefined ? data.rooms[ri].name : rid, s: +s, pids: Array.from(new Set(pids)) });
    });
    for (const pid in placements) {
      const pl = placements[pid]; const ri = M.reqIdx.get(E.reqOfPid(pid));
      if (ri === undefined || !pl || pl.s == null) continue;
      if (!M.valid[pl.s]) out.push({ kind: "slot", who: "", s: pl.s, pids: [pid] });
      M.reqs[ri].teachers.forEach(t => {
        if (M.tOff[t][pl.s]) out.push({ kind: "off", who: data.teachers[t].name, s: pl.s, pids: [pid] });
      });
      const r = M.reqs[ri];
      (r.src.groups || []).forEach((g, gi) => {
        const rid = (pl.rooms || [])[gi];
        if (g.roomType && g.roomType !== "none" && !rid) out.push({ kind: "noroom", who: g.subject, s: pl.s, pids: [pid] });
        else if (rid && M.rIdx.has(rid)) { const rm = data.rooms[M.rIdx.get(rid)]; const need = (r.needs || [])[gi] || 0; if (need > M.capOf(rm)) out.push({ kind: "small", who: g.subject + " (" + need + " תלמידים) בחדר " + rm.name + " (" + rm.capacity + " מקומות)", s: pl.s, pids: [pid] }); }
      });
    }
    return out;
  };

  E.CONFLICT_TEXT = {
    class: "כיתה משובצת פעמיים", teacher: "מורה משובץ/ת פעמיים", room: "חדר תפוס פעמיים",
    off: "מורה ביום/שעת חופש", slot: "שעה מחוץ למערכת", noroom: "אין חדר", small: "חדר קטן מדי",
  };

  // check placing pid at slot s (ignoring pid's current placement)
  E.checkMove = function (M, placements, pid, s) {
    const ri = M.reqIdx.get(E.reqOfPid(pid));
    if (ri === undefined) return { ok: false, issues: ["שיעור לא קיים"] };
    const r = M.reqs[ri];
    const issues = [];
    if (!M.valid[s]) issues.push("השעה לא קיימת במערכת");
    const data = M.data;
    r.teachers.forEach(t => { if (M.tOff[t][s]) issues.push(data.teachers[t].name + " בחופש בשעה זו"); });
    const d = Math.floor(s / M.P);
    let sameDay = 0;
    for (const q in placements) {
      if (q === pid) continue;
      const pl = placements[q]; if (!pl || pl.s == null) continue;
      const qi = M.reqIdx.get(E.reqOfPid(q)); if (qi === undefined) continue;
      if (qi === ri && Math.floor(pl.s / M.P) === d) sameDay++;
      if (pl.s !== s) continue;
      const qr = M.reqs[qi];
      r.classes.forEach(c => { if (qr.classes.indexOf(c) >= 0) issues.push("הכיתה " + data.classes[c].name + " כבר לומדת: " + E.reqTitle(M, qi)); });
      r.teachers.forEach(t => { if (qr.teachers.indexOf(t) >= 0) issues.push(data.teachers[t].name + " כבר מלמד/ת: " + E.reqTitle(M, qi)); });
    }
    if (sameDay + 1 > r.maxPerDay) issues.push("חריגה ממקסימום " + r.maxPerDay + " שעות ביום לשיעור זה");
    // room supply by type and size
    r.resNeed.forEach(([res, n]) => {
      let used = 0;
      for (const q in placements) {
        if (q === pid) continue; const pl = placements[q]; if (!pl || pl.s !== s) continue;
        const qi = M.reqIdx.get(E.reqOfPid(q)); if (qi === undefined) continue;
        M.reqs[qi].resNeed.forEach(([r2, n2]) => { if (r2 === res) used += n2; });
      }
      const R = M.resources[res];
      if (used + n > R.supply) issues.push(R.thr > 0 ? "אין מספיק חדרים מסוג " + R.type + " עם " + R.thr + " מקומות ומעלה" : "אין מספיק חדרים מסוג " + R.type);
    });
    return { ok: issues.length === 0, issues: Array.from(new Set(issues)) };
  };

  E.reqTitle = function (M, ri) {
    const r = M.reqs[ri].src;
    if (r.label) return r.label;
    const subj = Array.from(new Set((r.groups || []).map(g => g.subject)));
    const cls = (r.classIds || []).map(id => { const i = M.cIdx.get(id); return i === undefined ? id : M.data.classes[i].name; });
    return subj.join("/") + " " + cls.join(",");
  };

  // ---------- costs ----------
  // per class-day: gaps are expensive, late start mildly
  function classDayCost(occ, P, from) {
    let first = -1, last = -1, n = 0;
    for (let p = 0; p < P; p++) if (occ[from + p]) { if (first < 0) first = p; last = p; n++; }
    if (n === 0) return 0;
    return (last - first + 1 - n) * 12 + first * 3 + (n > 8 ? (n - 8) * 4 : 0);
  }
  function teacherDayCost(occ, P, from) {
    let first = -1, last = -1, n = 0;
    for (let p = 0; p < P; p++) if (occ[from + p]) { if (first < 0) first = p; last = p; n++; }
    if (n === 0) return 0;
    return 3 + (last - first + 1 - n) * 2;
  }
  function reqDayCost(slotsOfDay, dbl) {
    const n = slotsOfDay.length;
    if (n <= 1) return 0;
    if (dbl && n === 2 && Math.abs(slotsOfDay[0] - slotsOfDay[1]) === 1) return -2;
    return (n - 1) * 9;
  }

  // ---------- generator ----------
  // opts: {seed, placements (existing), keepLocked, keepAll, timeMs, onProgress}
  E.generate = function (data, opts) {
    opts = opts || {};
    const M = E.buildModel(data);
    const rnd = E.rng(opts.seed || Date.now());
    const { D, P, nS, valid } = M;
    const nC = data.classes.length, nT = data.teachers.length;
    const typeList = M.resources;
    const typeSupply = M.resources.map(x => x.supply);
    const units = [];
    M.reqs.forEach(r => {
      for (let k = 0; k < r.hours; k++) units.push({ r: r.i, pid: E.pidOf(r.id, k), locked: false, s: -1 });
    });
    const nU = units.length;
    const classUnit = new Int32Array(nC * nS).fill(-1);
    const teacherUnit = new Int32Array(nT * nS).fill(-1);
    const typeUse = typeList.map(() => new Int32Array(nS));
    const reqDay = new Int16Array(M.reqs.length * D);
    const slotUnits = Array.from({ length: nS }, () => []);
    const reqTypeNeed = M.reqs.map(r => r.resNeed);
    const classOcc = new Uint8Array(nC * nS), teacherOcc = new Uint8Array(nT * nS);

    function place(u, s) {
      const U = units[u], r = M.reqs[U.r];
      U.s = s;
      r.classes.forEach(c => { classUnit[c * nS + s] = u; classOcc[c * nS + s] = 1; });
      r.teachers.forEach(t => { teacherUnit[t * nS + s] = u; teacherOcc[t * nS + s] = 1; });
      reqTypeNeed[U.r].forEach(([ti, n]) => { typeUse[ti][s] += n; });
      reqDay[U.r * D + Math.floor(s / P)]++;
      slotUnits[s].push(u);
    }
    function unplace(u) {
      const U = units[u], s = U.s; if (s < 0) return;
      const r = M.reqs[U.r];
      r.classes.forEach(c => { classUnit[c * nS + s] = -1; classOcc[c * nS + s] = 0; });
      r.teachers.forEach(t => { teacherUnit[t * nS + s] = -1; teacherOcc[t * nS + s] = 0; });
      reqTypeNeed[U.r].forEach(([ti, n]) => { typeUse[ti][s] -= n; });
      reqDay[U.r * D + Math.floor(s / P)]--;
      const a = slotUnits[s]; a.splice(a.indexOf(u), 1);
      U.s = -1;
    }
    function staticOk(u, s) {
      if (!valid[s]) return false;
      const r = M.reqs[units[u].r];
      for (const t of r.teachers) if (M.tOff[t][s]) return false;
      return true;
    }
    function feasible(u, s) {
      if (!staticOk(u, s)) return false;
      const U = units[u], r = M.reqs[U.r];
      for (const c of r.classes) if (classUnit[c * nS + s] >= 0) return false;
      for (const t of r.teachers) if (teacherUnit[t * nS + s] >= 0) return false;
      for (const [ti, n] of reqTypeNeed[U.r]) if (typeUse[ti][s] + n > typeSupply[ti]) return false;
      if (reqDay[U.r * D + Math.floor(s / P)] >= r.maxPerDay) return false;
      return true;
    }
    // conflicting units if u placed at s (null if a locked unit blocks)
    function blockers(u, s) {
      const U = units[u], r = M.reqs[U.r];
      const set = new Set();
      for (const c of r.classes) { const v = classUnit[c * nS + s]; if (v >= 0) set.add(v); }
      for (const t of r.teachers) { const v = teacherUnit[t * nS + s]; if (v >= 0) set.add(v); }
      for (const [ti, n] of reqTypeNeed[U.r]) {
        let over = typeUse[ti][s] + n - typeSupply[ti];
        if (over > 0) {
          for (const v of slotUnits[s]) {
            if (over <= 0) break;
            if (set.has(v)) continue;
            const need = reqTypeNeed[units[v].r].find(x => x[0] === ti);
            if (need) { set.add(v); over -= need[1]; }
          }
          if (over > 0) return null;
        }
      }
      const d = Math.floor(s / P);
      if (reqDay[U.r * D + d] >= r.maxPerDay) {
        // evict one same-req unit on that day
        for (let p = 0; p < P; p++) {
          for (const v of slotUnits[d * P + p]) if (units[v].r === U.r && v !== u) { set.add(v); break; }
          if (set.size && Array.from(set).some(v => units[v].r === U.r)) break;
        }
      }
      for (const v of set) if (units[v].locked) return null;
      return set;
    }
    function localCost(u, s) {
      const U = units[u], r = M.reqs[U.r];
      const d = Math.floor(s / P), p = s % P;
      let cost = 0;
      for (const c of r.classes) {
        const base = c * nS + d * P;
        let n = 0, adj = false;
        for (let q = 0; q < P; q++) if (classOcc[base + q]) n++;
        if ((p > 0 && classOcc[base + p - 1]) || (p < P - 1 && classOcc[base + p + 1])) adj = true;
        if (n === 0) cost += p * 4;
        else if (adj) cost -= 3;
        else cost += 10;
        cost += n * 0.6;
      }
      for (const t of r.teachers) {
        const base = t * nS + d * P;
        let n = 0, adj = false;
        for (let q = 0; q < P; q++) if (teacherOcc[base + q]) n++;
        if ((p > 0 && teacherOcc[base + p - 1]) || (p < P - 1 && teacherOcc[base + p + 1])) adj = true;
        if (n === 0) cost += 0.8; else if (adj) cost -= 0.5; else cost += 0.6;
      }
      const same = reqDay[U.r * D + d];
      if (same > 0) {
        let adjSame = false;
        for (const v of slotUnits[d * P + Math.max(0, p - 1)]) if (units[v].r === U.r) adjSame = true;
        if (p < P - 1) for (const v of slotUnits[d * P + p + 1]) if (units[v].r === U.r) adjSame = true;
        cost += (r.double && adjSame) ? -4 : 9;
      }
      return cost + rnd() * 2.5;
    }

    // seed with existing placements
    const existing = opts.placements || {};
    const pidUnit = new Map(); units.forEach((U, i) => pidUnit.set(U.pid, i));
    const keep = [];
    for (const pid in existing) {
      const u = pidUnit.get(pid); const pl = existing[pid];
      if (u === undefined || !pl || pl.s == null) continue;
      if ((opts.keepLocked !== false && pl.locked) || opts.keepAll) keep.push([u, pl.s, !!pl.locked]);
    }
    keep.sort((a, b) => (b[2] ? 1 : 0) - (a[2] ? 1 : 0));
    keep.forEach(([u, s, locked]) => {
      if (feasible(u, s) || (locked && valid[s] && blockers(u, s) && blockers(u, s).size === 0)) {
        place(u, s); units[u].locked = locked;
      }
    });

    // difficulty ordering
    const tLoad = new Float32Array(nT);
    units.forEach(U => M.reqs[U.r].teachers.forEach(t => tLoad[t]++));
    const tFree = new Float32Array(nT);
    for (let t = 0; t < nT; t++) { let f = 0; for (let s = 0; s < nS; s++) if (valid[s] && !M.tOff[t][s]) f++; tFree[t] = f; }
    const diff = units.map(U => {
      const r = M.reqs[U.r];
      let x = r.teachers.length * 3 + r.classes.length * 2 + r.resNeed.length * 2;
      r.teachers.forEach(t => { x += 10 * tLoad[t] / Math.max(1, tFree[t]); });
      return x + rnd();
    });
    let queue = [];
    for (let u = 0; u < nU; u++) if (units[u].s < 0) queue.push(u);
    queue.sort((a, b) => diff[b] - diff[a]);

    const evicted = new Int32Array(nU);
    const t0 = Date.now();
    const timeMs = opts.timeMs || 6000;
    let iter = 0;
    const maxIter = opts.maxIter || 60000;
    while (queue.length && iter < maxIter && Date.now() - t0 < timeMs * 0.7) {
      iter++;
      const u = queue.shift();
      let best = -1, bestC = Infinity;
      for (let s = 0; s < nS; s++) {
        if (!feasible(u, s)) continue;
        const c = localCost(u, s);
        if (c < bestC) { bestC = c; best = s; }
      }
      if (best >= 0) { place(u, best); continue; }
      // repair: choose slot with cheapest eviction
      let bs = -1, bScore = Infinity, bSet = null;
      for (let s = 0; s < nS; s++) {
        if (!staticOk(u, s)) continue;
        const set = blockers(u, s);
        if (!set) continue;
        let sc = 0; for (const v of set) sc += 1 + evicted[v] * 0.7 + diff[v] * 0.02;
        sc += rnd() * 1.5;
        if (sc < bScore) { bScore = sc; bs = s; bSet = set; }
      }
      if (bs < 0) { evicted[u] += 5; queue.push(u); if (evicted[u] > 200) queue.pop(); continue; }
      for (const v of bSet) { unplace(v); evicted[v]++; queue.push(v); }
      if (feasible(u, bs)) place(u, bs); else queue.push(u);
      if (opts.onProgress && iter % 500 === 0) opts.onProgress({ phase: "build", placed: nU - queue.length, total: nU });
    }

    // ---------- improvement (hill climbing with sideways moves) ----------
    const reqSlots = (ri, d) => {
      const a = [];
      for (let p = 0; p < P; p++) for (const v of slotUnits[d * P + p]) if (units[v].r === ri) a.push(p);
      return a;
    };
    function affectedCost(u, d) {
      const r = M.reqs[units[u].r];
      let c = 0;
      for (const ci of r.classes) c += classDayCost(classOcc, P, ci * nS + d * P);
      for (const t of r.teachers) c += teacherDayCost(teacherOcc, P, t * nS + d * P) * 0.5;
      c += reqDayCost(reqSlots(units[u].r, d), r.double);
      return c;
    }
    const movable = []; for (let u = 0; u < nU; u++) if (!units[u].locked) movable.push(u);
    let impIter = 0;
    while (movable.length && Date.now() - t0 < timeMs) {
      impIter++;
      const u = movable[(rnd() * movable.length) | 0];
      const s0 = units[u].s; if (s0 < 0) continue;
      const d0 = Math.floor(s0 / P);
      const before0 = affectedCost(u, d0);
      unplace(u);
      const after0 = affectedCost(u, d0);
      let best = s0, bestDelta = 0;
      const cand = [];
      for (let s = 0; s < nS; s++) if (s !== s0 && feasible(u, s)) cand.push(s);
      for (const s of cand) {
        const d = Math.floor(s / P);
        let delta;
        if (d === d0) {
          place(u, s); const a = affectedCost(u, d); unplace(u);
          delta = a - before0;
        } else {
          const b1 = affectedCost(u, d);
          place(u, s); const a1 = affectedCost(u, d); unplace(u);
          delta = (after0 - before0) + (a1 - b1);
        }
        if (delta < bestDelta || (delta === bestDelta && delta === 0 && rnd() < 0.05)) { bestDelta = delta; best = s; }
      }
      place(u, best);
      // try swap with a same-class unit when stuck (classes' gaps)
      if (best === s0 && rnd() < 0.3) trySwap(u);
      if (opts.onProgress && impIter % 2000 === 0) opts.onProgress({ phase: "improve", placed: nU - queue.length, total: nU });
    }
    function trySwap(u) {
      const r = M.reqs[units[u].r];
      if (!r.classes.length) return;
      const c = r.classes[(rnd() * r.classes.length) | 0];
      const s0 = units[u].s;
      const s1 = ((rnd() * nS) | 0); if (!valid[s1] || s1 === s0) return;
      const v = classUnit[c * nS + s1]; if (v < 0 || v === u || units[v].locked) return;
      const dA = Math.floor(s0 / P), dB = Math.floor(s1 / P);
      const total = () => affectedCost(u, dA) + affectedCost(u, dB) + affectedCost(v, dA) + affectedCost(v, dB);
      const before = total();
      unplace(u); unplace(v);
      if (feasible(u, s1)) { place(u, s1); if (feasible(v, s0)) { place(v, s0); if (total() < before) return; unplace(v); } unplace(u); }
      place(u, s0); place(v, s1);
    }

    const placements = {};
    const unplaced = [];
    units.forEach(U => {
      if (U.s >= 0) placements[U.pid] = { s: U.s, rooms: [], locked: U.locked };
      else unplaced.push(U.pid);
    });
    // carry rooms from locked existing
    for (const pid in placements) {
      const ex = existing[pid];
      if (ex && ex.s === placements[pid].s && ex.rooms) placements[pid].rooms = ex.rooms.slice();
    }
    E.assignRooms(M, placements, { keepExisting: true });
    return { placements, unplaced, stats: E.stats(M, placements, unplaced), iterations: iter + impIter };
  };

  // ---------- rooms ----------
  E.assignRooms = function (M, placements, opts) {
    opts = opts || {};
    const data = M.data;
    const bySlot = new Map();
    for (const pid in placements) { const pl = placements[pid]; if (pl.s == null) continue; let a = bySlot.get(pl.s); if (!a) bySlot.set(pl.s, a = []); a.push(pid); }
    const roomsByType = new Map();
    data.rooms.forEach(r => { let a = roomsByType.get(r.type); if (!a) roomsByType.set(r.type, a = []); a.push(r); });
    roomsByType.forEach(a => a.sort((x, y) => M.capOf(x) - M.capOf(y)));
    const homes = new Set(data.classes.map(c => c.homeRoom).filter(Boolean));
    bySlot.forEach(pids => {
      const used = new Set();
      const jobs = [];
      pids.forEach(pid => {
        const ri = M.reqIdx.get(E.reqOfPid(pid)); if (ri === undefined) return;
        const R = M.reqs[ri]; const r = R.src; const pl = placements[pid];
        pl.rooms = (pl.rooms || []).slice(0, (r.groups || []).length);
        (r.groups || []).forEach((g, gi) => {
          if (!g.roomType || g.roomType === "none") { pl.rooms[gi] = null; return; }
          const need = R.needs[gi] || 0;
          const cur = pl.rooms[gi];
          const rm = cur && M.rIdx.has(cur) ? data.rooms[M.rIdx.get(cur)] : null;
          const curOk = rm && !used.has(cur) && ((rm.type === g.roomType && M.capOf(rm) >= need) || pl.locked);
          if (opts.keepExisting && curOk) { used.add(cur); return; }
          pl.rooms[gi] = null;
          jobs.push({ pid, gi, g, r, need });
        });
      });
      // biggest groups first, then the ones with fewest suitable rooms
      jobs.sort((a, b) => (b.need - a.need) || ((roomsByType.get(a.g.roomType) || []).length - (roomsByType.get(b.g.roomType) || []).length));
      const busyClasses = new Set();
      pids.forEach(pid => { const ri = M.reqIdx.get(E.reqOfPid(pid)); if (ri !== undefined) (M.reqs[ri].src.classIds || []).forEach(c => busyClasses.add(c)); });
      jobs.forEach(job => {
        const pl = placements[job.pid];
        const pool = (roomsByType.get(job.g.roomType) || []).filter(rm => !used.has(rm.id) && (M.roomFor(rm, job.r.classIds, "lesson") || rm.id === job.g.room));
        const fits = pool.filter(rm => M.capOf(rm) >= job.need);
        const ownHomes = [];
        if (job.g.room) ownHomes.push(job.g.room);
        (job.r.classIds || []).forEach(cid => { const ci = M.cIdx.get(cid); if (ci !== undefined && data.classes[ci].homeRoom) ownHomes.push(data.classes[ci].homeRoom); });
        const otherBusyHome = rm => { const c = data.classes.find(c => c.homeRoom === rm.id); return c && busyClasses.has(c.id) && (job.r.classIds || []).indexOf(c.id) < 0; };
        const pick = fits.find(rm => ownHomes.indexOf(rm.id) >= 0)
          || fits.find(rm => !homes.has(rm.id))
          || fits.find(rm => !otherBusyHome(rm))
          || fits[0]
          || pool[pool.length - 1] || null; // nothing big enough: the largest free room (reported as too small)
        if (pick) { used.add(pick.id); pl.rooms[job.gi] = pick.id; }
      });
    });
    return placements;
  };

  E.freeRooms = function (M, placements, s, exceptPid) {
    const used = new Set();
    for (const pid in placements) { if (pid === exceptPid) continue; const pl = placements[pid]; if (pl && pl.s === s) (pl.rooms || []).forEach(r => r && used.add(r)); }
    return M.data.rooms.filter(r => !used.has(r.id));
  };

  // ---------- stats ----------
  E.stats = function (M, placements, unplaced) {
    const { D, P, nS } = M;
    const nC = M.data.classes.length, nT = M.data.teachers.length;
    const cOcc = new Uint8Array(nC * nS), tOcc = new Uint8Array(nT * nS);
    for (const pid in placements) {
      const ri = M.reqIdx.get(E.reqOfPid(pid)); if (ri === undefined) continue;
      const s = placements[pid].s;
      M.reqs[ri].classes.forEach(c => cOcc[c * nS + s] = 1);
      M.reqs[ri].teachers.forEach(t => tOcc[t * nS + s] = 1);
    }
    const gaps = (occ, base) => { let f = -1, l = -1, n = 0; for (let p = 0; p < P; p++) if (occ[base + p]) { if (f < 0) f = p; l = p; n++; } return n ? l - f + 1 - n : 0; };
    let classGaps = 0, teacherGaps = 0;
    const classGapList = [];
    for (let c = 0; c < nC; c++) { let g = 0; for (let d = 0; d < D; d++) g += gaps(cOcc, c * nS + d * P); classGaps += g; if (g) classGapList.push({ name: M.data.classes[c].name, gaps: g }); }
    for (let t = 0; t < nT; t++) for (let d = 0; d < D; d++) teacherGaps += gaps(tOcc, t * nS + d * P);
    const total = E.allPids(M).length;
    return {
      total, placed: Object.keys(placements).filter(pid => M.reqIdx.has(E.reqOfPid(pid))).length,
      unplaced: (unplaced || E.allPids(M).filter(pid => !placements[pid])).length,
      classGaps, teacherGaps, classGapList,
      conflicts: E.conflicts(M, placements).length,
    };
  };

  // ---------- daily / substitutes ----------
  // daily doc: {date, absentTeachers:[id], absentClasses:[{classId,note}], changes:{ "pid|gi": {type:'sub',teacherId}|{type:'cancel'}|{type:'room',roomId} }, notes}
  E.dateToDay = function (dateStr) {
    const [y, m, d] = dateStr.split("-").map(Number);
    return new Date(Date.UTC(y, m - 1, d)).getUTCDay(); // 0 = Sunday = א
  };
  E.weekDates = function (dateStr) {
    const [y, m, d] = dateStr.split("-").map(Number);
    const base = new Date(Date.UTC(y, m - 1, d));
    const wd = base.getUTCDay();
    const out = [];
    for (let i = 0; i < 6; i++) { const x = new Date(base.getTime() + (i - wd) * 864e5); out.push(x.toISOString().slice(0, 10)); }
    return out;
  };

  // lessons of a weekday with daily overlay. Returns [{pid, s, p, gi, group, req, teacherId, effTeacherId, status, roomId}]
  // Normalized view of a daily doc.
  // daily: {absences:[{teacherId, reason?, from?, to?}], events:[{id,title,kind,from?,to?,classIds:[],groups:[{reqId,group?}],escorts:[{period,teacherIds:[]}],note}],
  //         changes:{"pid|gi": {type:'sub'|'cancel'|'room', ...}}, notes,  legacy: absentTeachers:[id], absentClasses:[{classId,note}]}
  // Periods in absences/events are DISPLAY numbers (as the school writes them); p below is the 0-based slot index.
  E.normDaily = function (M, daily) {
    const fp = M.cfg.firstPeriod || 0;
    const doc = daily || {};
    const inRange = (o, p) => { const n = p + fp; return (o.from == null || o.from === "" || n >= +o.from) && (o.to == null || o.to === "" || n <= +o.to); };
    const absences = (doc.absences || []).slice();
    (doc.absentTeachers || []).forEach(id => { if (!absences.some(a => a.teacherId === id)) absences.push({ teacherId: id }); });
    // exam proctors behave like escorts (busy at that period)
    const events = (doc.events || []).map(ev => {
      const extra = [];
      if (ev.exam) (ev.exam.rooms || []).forEach(r => (r.proctors || []).forEach(pr => extra.push({ period: +pr.period, teacherIds: pr.teacherIds || [] })));
      if (ev.workshop) {
        (ev.workshop.slots || []).forEach(sl => (sl.assign || []).forEach(a => { if ((a.escortIds || []).length) extra.push({ period: +sl.period, teacherIds: a.escortIds }); }));
        (ev.workshop.stations || []).forEach(st => { if (st.teacherId) (ev.workshop.slots || []).forEach(sl => extra.push({ period: +sl.period, teacherIds: [st.teacherId] })); });
      }
      return extra.length ? Object.assign({}, ev, { escorts: (ev.escorts || []).concat(extra) }) : ev;
    });
    const examRoomAt = (rid, p) => events.find(ev => inRange(ev, p) && ((ev.exam && (ev.exam.rooms || []).some(r => r.roomId === rid)) || (ev.workshop && (ev.workshop.stations || []).some(st => st.roomId === rid)))) || null;
    const legacyAway = new Set((doc.absentClasses || []).map(x => x.classId));
    const N = {
      absences, events, examRoomAt,
      absentAt: (tid, p) => absences.some(a => a.teacherId === tid && inRange(a, p)),
      absenceOf: tid => absences.find(a => a.teacherId === tid) || null,
      escortAt: (tid, p) => events.some(ev => (ev.escorts || []).some(e => +e.period === p + fp && (e.teacherIds || []).indexOf(tid) >= 0)),
      escortEventAt: (tid, p) => events.find(ev => (ev.escorts || []).some(e => +e.period === p + fp && (e.teacherIds || []).indexOf(tid) >= 0)) || null,
      classAwayAt: (cid, p) => legacyAway.has(cid) || events.some(ev => inRange(ev, p) && (ev.classIds || []).indexOf(cid) >= 0),
      groupAwayAt: (reqId, gi, p) => events.some(ev => inRange(ev, p) && (ev.groups || []).some(g => g.reqId === reqId && (g.group == null || g.group === "" || +g.group === gi))),
    };
    N.unavailableAt = (tid, p) => N.absentAt(tid, p) || N.escortAt(tid, p);
    N.reasonAt = (tid, p) => { if (N.absentAt(tid, p)) { const a = N.absenceOf(tid); return a && a.reason ? a.reason : "נעדר/ת"; } const ev = N.escortEventAt(tid, p); return ev ? "מלווה: " + (ev.title || "אירוע") : ""; };
    return N;
  };

  E.dayLessons = function (M, placements, daily, d) {
    const out = [];
    const N = E.normDaily(M, daily);
    const ch = (daily && daily.changes) || {};
    for (const pid in placements) {
      const pl = placements[pid]; if (!pl || pl.s == null) continue;
      if (Math.floor(pl.s / M.P) !== d) continue;
      const ri = M.reqIdx.get(E.reqOfPid(pid)); if (ri === undefined) continue;
      const req = M.reqs[ri].src;
      const mv = ch[pid + "|0"] && ch[pid + "|0"].type === "move" ? ch[pid + "|0"] : null;
      const fromP = pl.s % M.P;
      const p = mv ? +mv.toP : fromP;
      const sNow = d * M.P + p;
      const cls = req.classIds || [];
      const awayCount = cls.filter(cid => N.classAwayAt(cid, p)).length;
      (req.groups || []).forEach((g, gi) => {
        const c = ch[pid + "|" + gi] || ch[pid + "|*"];
        let status = "normal", eff = g.teacherId, roomId = (pl.rooms || [])[gi] || null, reason = "";
        const away = (cls.length > 0 && awayCount === cls.length) || N.groupAwayAt(req.id, gi, p);
        const duty = !cls.length; // פרטני, תומכות הוראה, שהייה, ישיבות – teacher time without a class
        if (away) status = "class-away";
        else if (N.unavailableAt(g.teacherId, p)) { status = duty ? "duty-off" : "uncovered"; reason = N.reasonAt(g.teacherId, p); }
        if (mv) { status = status === "class-away" ? status : "moved"; if (mv.roomId) roomId = mv.roomId; }
        if (c && c.type !== "move" && status !== "class-away") {
          if (c.type === "sub") { status = "sub"; eff = c.teacherId; }
          else if (c.type === "cancel") { status = "cancel"; eff = null; }
          else if (c.type === "room") { roomId = c.roomId; }
          if (c.roomId && c.type !== "room") roomId = c.roomId;
        }
        const clash = roomId && status !== "class-away" && status !== "cancel" ? N.examRoomAt(roomId, p) : null;
        out.push({ pid, s: sNow, p, fromP, gi, group: g, req, duty, teacherId: g.teacherId, effTeacherId: eff, status, roomId, reason, change: c || null, partialAway: !away && awayCount > 0 ? awayCount : 0, roomClash: clash ? clash.title : null });
      });
    }
    out.sort((a, b) => a.p - b.p);
    return out;
  };

  // who can't take a substitution at slot s on that date: teaching, escorting, absent
  E.busyTeachersAt = function (M, placements, daily, s) {
    const d = Math.floor(s / M.P), p = s % M.P;
    const busy = new Set();
    E.dayLessons(M, placements, daily, d).forEach(L => {
      if (L.s !== s || L.duty) return;
      if (L.status === "cancel" || L.status === "class-away" || L.status === "uncovered") return;
      if (L.effTeacherId) busy.add(L.effTeacherId);
    });
    const N = E.normDaily(M, daily);
    M.data.teachers.forEach(t => { if (N.unavailableAt(t.id, p)) busy.add(t.id); });
    return busy;
  };

  // is this lesson at the start/end of each of its classes' day (nothing left before or after it)?
  // -> cancelling it shortens the day ("מבוטל"); otherwise it leaves a gap ("חלון")
  E.isEdgeLesson = function (dayAll, L) {
    const cls = L.req.classIds || [];
    if (!cls.length) return false;
    return cls.every(cid => {
      const rest = dayAll.filter(x => x.pid !== L.pid && (x.req.classIds || []).indexOf(cid) >= 0 && x.status !== "cancel" && x.status !== "class-away" && x.status !== "uncovered").map(x => x.p);
      return !rest.some(q => q < L.p) || !rest.some(q => q > L.p);
    });
  };
  E.cancelLabel = function (dayAll, L) {
    if (L.change && L.change.label) return L.change.label;
    return E.isEdgeLesson(dayAll, L) ? "מבוטל" : "חלון";
  };

  // weekSubs: map teacherId -> count of substitutions this week
  // Returns, for each lesson of teacherId on day d where the teacher is unavailable (absent / escorting), ranked substitutes.
  E.findSubstitutes = function (M, placements, daily, d, teacherId, weekSubs) {
    const data = M.data;
    const N = E.normDaily(M, daily);
    const dayAll = E.dayLessons(M, placements, daily, d);
    const lessons = dayAll.filter(L => !L.duty && L.teacherId === teacherId && L.status !== "class-away" && (N.unavailableAt(teacherId, L.p) || L.status === "sub" || L.status === "cancel"));
    const MEETING = /ישיב|מליא|הנהלה|תורנ/;
    const present = new Map();
    dayAll.forEach(L => { if (L.effTeacherId && L.status !== "cancel" && L.status !== "class-away" && L.status !== "uncovered") { let a = present.get(L.effTeacherId); if (!a) present.set(L.effTeacherId, a = []); a.push(L.p); } });
    N.events.forEach(ev => (ev.escorts || []).forEach(e => (e.teacherIds || []).forEach(tid => { let a = present.get(tid); if (!a) present.set(tid, a = []); a.push(+e.period - (M.cfg.firstPeriod || 0)); })));
    return lessons.map(L => {
      const busy = E.busyTeachersAt(M, placements, daily, L.s);
      const subj = L.group.subject;
      const cands = [];
      data.teachers.forEach((t, ti) => {
        if (t.id === teacherId || busy.has(t.id)) return;
        if (M.tOff[ti][L.s]) return;
        let score = 0; const why = [];
        if ((t.subjects || []).indexOf(subj) >= 0) { score += 4; why.push("אותו מקצוע"); }
        const teachesClass = M.reqs.some(r => r.teachers.indexOf(ti) >= 0 && (r.src.classIds || []).some(cid => (L.req.classIds || []).indexOf(cid) >= 0));
        if (teachesClass) { score += 3; why.push("מכיר/ה את הכיתה"); }
        const ps = present.get(t.id) || [];
        if (ps.length) {
          const before = ps.some(p => p < L.p), after = ps.some(p => p > L.p);
          if (before && after) { score += 5; why.push("בחלון בבית הספר"); }
          else { score += 2; why.push("נמצא/ת בבית הספר היום"); }
        } else { score -= 4; why.push("לא מלמד/ת היום"); }
        if (N.absenceOf(t.id)) { score -= 3; why.push("נעדר/ת בחלק מהיום"); }
        const dutyNow = dayAll.find(Y => Y.duty && Y.teacherId === t.id && Y.p === L.p && Y.status === "normal");
        if (dutyNow) { if (MEETING.test(dutyNow.group.subject)) { score -= 2; why.push("בישיבה: " + dutyNow.group.subject); } else { score += 3; why.push("בשעת " + dutyNow.group.subject); } }
        const ws = (weekSubs && weekSubs[t.id]) || 0;
        score -= ws * 1.5; if (ws) why.push(ws + " מילויים השבוע");
        cands.push({ teacherId: t.id, name: t.name, score: Math.round(score * 10) / 10, why: why.join(", ") });
      });
      cands.sort((a, b) => b.score - a.score);
      return {
        pid: L.pid, gi: L.gi, p: L.p, period: L.p + (M.cfg.firstPeriod || 0), subject: subj,
        classes: (L.req.classIds || []).map(cid => { const ci = M.cIdx.get(cid); return ci === undefined ? cid : data.classes[ci].name; }).join(","),
        isBlock: (L.req.groups || []).length > 1, status: L.status, reason: L.reason || N.reasonAt(teacherId, L.p), currentSub: L.status === "sub" ? L.effTeacherId : null,
        canRelease: E.isEdgeLesson(dayAll, L), cancelLabel: E.cancelLabel(dayAll, L), candidates: cands.slice(0, 6),
      };
    });
  };

  // Close the gap left by an absent teacher: another teacher of the same class moves a lesson
  // from the start/end of the class's day into the empty period, so the class finishes earlier
  // (or starts later) instead of sitting in a window. Single-class, single-group lessons only.
  E.findMoves = function (M, placements, daily, d, L) {
    if ((L.req.groups || []).length !== 1 || !(L.req.classIds || []).length) return [];
    const key = (L.req.classIds || []).slice().sort().join(",");
    const dayAll = E.dayLessons(M, placements, daily, d);
    const N = E.normDaily(M, daily);
    const busy = E.busyTeachersAt(M, placements, daily, L.s);
    const out = [];
    const seenPid = new Set();
    dayAll.forEach(X => {
      if (X.pid === L.pid || seenPid.has(X.pid)) return;
      seenPid.add(X.pid);
      if ((X.req.classIds || []).slice().sort().join(",") !== key) return;
      const parts = dayAll.filter(Y => Y.pid === X.pid);
      if (parts.some(Y => Y.status !== "normal")) return;
      // every teacher of the lesson (all groups of a הקבצה) must be free at the empty period
      const free = parts.every(Y => { const tt = Y.teacherId; const ti2 = M.tIdx.get(tt); return tt && !busy.has(tt) && !N.unavailableAt(tt, L.p) && !(ti2 !== undefined && M.tOff[ti2][L.s]); });
      if (!free) return;
      const t = X.teacherId;
      // after the move: the class has lessons at all its periods except X.p (and L.p is filled again)
      const ok = (L.req.classIds || []).every(cid => {
        const ps = dayAll.filter(Y => Y.pid !== X.pid && Y.pid !== L.pid && (Y.req.classIds || []).indexOf(cid) >= 0 && Y.status !== "cancel" && Y.status !== "class-away" && Y.status !== "uncovered").map(Y => Y.p).concat([L.p]);
        return !ps.some(q => q > X.p) || !ps.some(q => q < X.p);
      });
      if (!ok) return;
      const later = X.p > L.p;
      out.push({ pid: X.pid, gi: 0, fromP: X.p, toP: L.p, teacherId: t, subject: X.req.groups.length > 1 ? (X.req.label || X.group.subject) : X.group.subject, roomId: X.req.groups.length > 1 ? null : X.roomId, why: later ? "מקדים/ה את השיעור – הכיתה מסיימת מוקדם" : "מאחר/ת את השיעור – הכיתה מתחילה מאוחר", score: 10 - Math.abs(X.p - L.p) * 0.1 });
    });
    return out.sort((a, b) => b.score - a.score);
  };

  // Proposed fixes for every uncovered lesson of the day: a good substitute, otherwise release at the edge of the day, otherwise a window.
  E.autoArrange = function (M, placements, daily, d, date, weekSubs) {
    const doc = JSON.parse(JSON.stringify(daily || {}));
    doc.changes = doc.changes || {};
    const changes = [];
    const ws = Object.assign({}, weekSubs || {});
    // teachers that need cover, in period order of their first uncovered lesson
    const N = E.normDaily(M, doc);
    const tids = Array.from(new Set(E.dayLessons(M, placements, doc, d).filter(L => L.status === "uncovered").map(L => L.teacherId)));
    tids.forEach(tid => {
      E.findSubstitutes(M, placements, doc, d, tid, ws).filter(x => x.status === "uncovered").forEach(x => {
        const best = x.candidates[0];
        let ch;
        const fp0 = M.cfg.firstPeriod || 0;
        const Lx = E.dayLessons(M, placements, doc, d).find(L => L.pid === x.pid && L.gi === x.gi);
        const moves = !x.canRelease && Lx ? E.findMoves(M, placements, doc, d, Lx) : [];
        if (x.canRelease) ch = { op: "cancel", date, pid: x.pid, group: x.gi, release: true };
        else if (moves.length) ch = { op: "day_move", date, pid: moves[0].pid, toPeriod: moves[0].toP + fp0, replacesPid: x.pid, replacesGroup: x.gi, roomId: (Lx && Lx.roomId) || moves[0].roomId || undefined };
        else if (best && best.score >= 5) ch = { op: "sub", date, pid: x.pid, group: x.gi, teacherId: best.teacherId };
        else ch = { op: "cancel", date, pid: x.pid, group: x.gi, label: "חלון" };
        changes.push(ch);
        // apply to the scratch doc so later choices see it
        if (ch.op === "day_move") { doc.changes[ch.pid + "|0"] = { type: "move", toP: ch.toPeriod - fp0, roomId: ch.roomId }; doc.changes[x.pid + "|" + x.gi] = { type: "cancel", label: "הוחלף", by: ch.pid }; }
        else doc.changes[x.pid + "|" + x.gi] = ch.op === "sub" ? { type: "sub", teacherId: ch.teacherId } : { type: "cancel", release: !!ch.release, label: ch.label };
        if (ch.op === "sub") ws[ch.teacherId] = (ws[ch.teacherId] || 0) + 1;
      });
    });
    // lessons whose room is taken by an exam: find another free room that fits
    E.dayLessons(M, placements, doc, d).filter(L => L.roomClash).forEach(L => {
      const alt = E.freeRoomFor(M, placements, doc, d, L);
      if (alt) { changes.push({ op: "daily_room", date, pid: L.pid, group: L.gi, roomId: alt.id }); doc.changes[L.pid + "|" + L.gi] = Object.assign({}, doc.changes[L.pid + "|" + L.gi] || { type: "room" }, { roomId: alt.id }); }
    });
    return changes;
  };

  // rooms in use at period p of day d (lessons after overlay + exams)
  E.roomsInUse = function (M, placements, daily, d, p) {
    const used = new Map();
    E.dayLessons(M, placements, daily, d).forEach(L => { if (L.p === p && L.roomId && L.status !== "cancel" && L.status !== "class-away") used.set(L.roomId, L); });
    const N = E.normDaily(M, daily);
    M.data.rooms.forEach(r => { const ev = N.examRoomAt(r.id, p); if (ev) used.set(r.id, { exam: ev }); });
    return used;
  };
  // a free room for lesson L (same type, big enough, smallest that fits)
  E.freeRoomFor = function (M, placements, daily, d, L, exclude) {
    const used = E.roomsInUse(M, placements, daily, d, L.p);
    const ri = M.reqIdx.get(L.req.id); const need = ri !== undefined ? (M.reqs[ri].needs[L.gi] || 0) : 0;
    const type = L.group.roomType || "כיתה";
    return M.data.rooms.filter(r => r.type === type && !used.has(r.id) && !(exclude && exclude.has(r.id)) && M.capOf(r) >= need && M.roomFor(r, L.req.classIds, "lesson")).sort((a, b) => M.capOf(a) - M.capOf(b))[0] || null;
  };

  // ---------- room optimizer for an existing timetable ----------
  // Re-seats every lesson so each group gets a room of the right type that holds it, with the least
  // wasted seats, moving as few lessons as possible. Lessons without a known size keep their room.
  E.optimizeRooms = function (M, placements, opts) {
    opts = opts || {};
    const data = M.data;
    const slack = opts.slack == null ? 8 : opts.slack; // keep the current room if it wastes at most this many more seats than the best fit
    const bySlot = new Map();
    for (const pid in placements) { const pl = placements[pid]; if (!pl || pl.s == null) continue; let a = bySlot.get(pl.s); if (!a) bySlot.set(pl.s, a = []); a.push(pid); }
    const changes = [];
    let tooSmallBefore = 0, tooSmallAfter = 0, wasteBefore = 0, wasteAfter = 0, sized = 0;
    bySlot.forEach((pids, s) => {
      const jobs = [];
      pids.forEach(pid => {
        const ri = M.reqIdx.get(E.reqOfPid(pid)); if (ri === undefined) return;
        const R = M.reqs[ri]; const pl = placements[pid];
        (R.src.groups || []).forEach((g, gi) => {
          if (!g.roomType || g.roomType === "none") return;
          const cur = (pl.rooms || [])[gi] || null; const rm = cur && M.rIdx.has(cur) ? data.rooms[M.rIdx.get(cur)] : null;
          jobs.push({ pid, gi, type: g.roomType, need: R.needs[gi] || 0, cur, curCap: rm ? M.capOf(rm) : 0, locked: !!pl.locked || !!(rm && (rm.noEvents || (rm.reservedFor || []).length)), classIds: R.src.classIds || [] });
        });
      });
      jobs.forEach(j => { if (j.need && j.cur) { sized++; if (j.curCap < j.need) tooSmallBefore++; else if (j.curCap < Infinity) wasteBefore += j.curCap - j.need; } });
      const used = new Set();
      // fixed: locked lessons and lessons without a known size keep their room
      jobs.filter(j => j.locked || !j.need).forEach(j => { if (j.cur) used.add(j.cur); j.to = j.cur; });
      jobs.filter(j => !j.locked && j.need).sort((a, b) => b.need - a.need).forEach(j => {
        const pool = data.rooms.filter(r => r.type === j.type && !used.has(r.id) && M.roomFor(r, j.classIds, "lesson"));
        const fit = pool.filter(r => M.capOf(r) >= j.need).sort((a, b) => M.capOf(a) - M.capOf(b));
        let pick = null;
        if (fit.length) {
          const curFits = j.cur && !used.has(j.cur) && j.curCap >= j.need;
          pick = curFits && j.curCap - M.capOf(fit[0]) <= slack ? data.rooms[M.rIdx.get(j.cur)] : fit[0];
        } else pick = j.cur && !used.has(j.cur) ? data.rooms[M.rIdx.get(j.cur)] : (pool.sort((a, b) => M.capOf(b) - M.capOf(a))[0] || null);
        j.to = pick ? pick.id : j.cur; if (j.to) used.add(j.to);
      });
      jobs.forEach(j => {
        if (j.need && j.to) { const rm = data.rooms[M.rIdx.get(j.to)]; const cap = rm ? M.capOf(rm) : 0; if (cap < j.need) tooSmallAfter++; else if (cap < Infinity) wasteAfter += cap - j.need; }
        if (j.to && j.to !== j.cur) changes.push({ op: "room", pid: j.pid, group: j.gi, roomId: j.to, from: j.cur });
      });
    });
    return { changes, stats: { sized, tooSmallBefore, tooSmallAfter, wasteBefore, wasteAfter, moved: changes.length } };
  };

  // ---------- homerooms by class size ----------
  // The biggest classes get the biggest rooms. Rooms reserved for a class stay with it; rooms marked
  // noEvents are not used. Returns {map: {classId: roomId}, changes: [{op:'room', pid, group, roomId}]}
  // where lessons that sat in a class's old homeroom move to its new one (when free at that hour).
  E.assignHomerooms = function (M, placements, opts) {
    opts = opts || {};
    const data = M.data;
    const reservedOf = cid => data.rooms.find(r => (r.reservedFor || []).length === 1 && r.reservedFor[0] === cid);
    const pool = data.rooms.filter(r => r.type === "כיתה" && !r.noEvents && !(r.reservedFor || []).length && M.capOf(r) < Infinity && (!opts.onlyRooms || opts.onlyRooms.indexOf(r.id) >= 0));
    const classes = data.classes.slice();
    const map = {}; const notes = [];
    classes.filter(c => reservedOf(c.id)).forEach(c => { map[c.id] = reservedOf(c.id).id; });
    const rest = classes.filter(c => !map[c.id]).sort((a, b) => (+b.students || 0) - (+a.students || 0));
    if (rest.some(c => !(+c.students))) notes.push("חסר מספר תלמידים ל-" + rest.filter(c => !(+c.students)).length + " כיתות – הן שובצו אחרונות.");
    // rank matching: the N largest free classrooms for the N classes; biggest class -> biggest room.
    // Among rooms of equal size a class keeps its current homeroom.
    const rooms = pool.slice().sort((a, b) => (M.capOf(b) - M.capOf(a)) || ((rest.some(c => c.homeRoom === b.id) ? 1 : 0) - (rest.some(c => c.homeRoom === a.id) ? 1 : 0))).slice(0, rest.length);
    if (rooms.length < rest.length) notes.push("יש רק " + rooms.length + " חדרים מתאימים ל-" + rest.length + " כיתות.");
    const left = rooms.slice();
    rest.forEach(c => {
      if (!left.length) { notes.push("אין חדר אם פנוי לכיתה " + c.name); return; }
      const topCap = M.capOf(left[0]);
      const same = left.filter(r => M.capOf(r) === topCap);
      const pick = same.find(r => r.id === c.homeRoom) || same[0];
      left.splice(left.indexOf(pick), 1);
      map[c.id] = pick.id;
      const need = +c.students || 0;
      if (need && M.capOf(pick) < need) notes.push("כיתה " + c.name + " (" + need + ") גדולה מחדר " + pick.name + " (" + pick.capacity + ")");
    });
    // move lessons that used the old homeroom
    const changes = [];
    const usedAt = new Map();
    for (const pid in placements) { const pl = placements[pid]; (pl.rooms || []).forEach(r => { if (r) { let set = usedAt.get(pl.s); if (!set) usedAt.set(pl.s, set = new Set()); set.add(r); } }); }
    const oldHome = new Map(data.classes.map(c => [c.id, c.homeRoom]));
    for (const pid in placements) {
      const ri = M.reqIdx.get(E.reqOfPid(pid)); if (ri === undefined) continue;
      const r = M.reqs[ri].src; if ((r.classIds || []).length !== 1 || r.groups.length !== 1) continue;
      const cid = r.classIds[0]; const pl = placements[pid];
      const from = (pl.rooms || [])[0]; const to = map[cid];
      if (!to || from === to || from !== oldHome.get(cid)) continue;
      const set = usedAt.get(pl.s);
      if (set && set.has(to)) continue; // the new room is busy at that hour; keep for the optimizer
      set.delete(from); set.add(to);
      changes.push({ op: "room", pid, group: 0, roomId: to, from });
    }
    return { map, changes, notes };
  };

  // ---------- workshop / lecture rotation ----------
  // spec: {id, title, from, to, classIds, stations:[{name, roomId?, teacherId?}], escortsPerGroup?}
  E.planWorkshops = function (M, placements, daily, d, spec, weekLoad) {
    const fp = M.cfg.firstPeriod || 0; const data = M.data;
    const from = +spec.from, to = +(spec.to || spec.from);
    const periods = []; for (let n = from; n <= to; n++) periods.push(n);
    const stations = (spec.stations || []).filter(st => st && st.name);
    const notes = [];
    if (!stations.length) return { error: "צריך לפחות תחנה אחת" };
    const G = stations.length;
    // balance classes into G groups by student count (keeps grade order inside a group)
    const cls = (spec.classIds || []).map(id => data.classes.find(c => c.id === id)).filter(Boolean);
    const groups = Array.from({ length: G }, () => ({ classIds: [], students: 0 }));
    cls.slice().sort((a, b) => (+b.students || 30) - (+a.students || 30)).forEach(c => { const g = groups.slice().sort((x, y) => x.students - y.students)[0]; g.classIds.push(c.id); g.students += (+c.students || 30); });
    if (periods.length < G) notes.push("יש " + G + " תחנות ורק " + periods.length + " שעות – לא כל הקבוצות יעברו בכל התחנות.");
    // the day with the participating classes away (their lessons are cancelled) but without this rotation's rooms/escorts
    const base = JSON.parse(JSON.stringify(daily || {}));
    base.events = (base.events || []).filter(e => e.id !== spec.id).concat([{ id: spec.id, title: spec.title, from, to, classIds: spec.classIds || [], escorts: [] }]);
    const dayAll = E.dayLessons(M, placements, base, d);
    // rooms: station's own room, else the best-fitting room that is free in every period
    const maxGroup = Math.max.apply(null, groups.map(g => g.students).concat([0]));
    const usedRooms = new Set(stations.map(st => st.roomId).filter(Boolean));
    const freeAll = r => periods.every(n => !E.roomsInUse(M, placements, base, d, n - fp).has(r.id));
    stations.forEach(st => {
      if (st.roomId) return;
      const pool = data.rooms.filter(r => ["כיתה", "אולם"].indexOf(r.type) >= 0 && !usedRooms.has(r.id) && M.roomFor(r, [], "event") && freeAll(r));
      const fit = pool.filter(r => M.capOf(r) >= maxGroup).sort((a, b) => M.capOf(a) - M.capOf(b));
      const pick = fit[0] || pool.sort((a, b) => M.capOf(b) - M.capOf(a))[0];
      if (pick) { st.roomId = pick.id; usedRooms.add(pick.id); } else notes.push("לא נמצא חדר פנוי לתחנה " + st.name);
    });
    // rotation + escorts: the teacher who would have taught the class at that period, else a free teacher at school
    const load = Object.assign({}, weekLoad || {});
    const slots = periods.map((n, k) => {
      const p = n - fp; const taken = new Set(stations.map(st => st.teacherId).filter(Boolean));
      const assign = groups.map((g, gi) => {
        const station = (gi + k) % G;
        const want = Math.max(1, spec.escortsPerGroup || 1);
        const esc = [];
        g.classIds.forEach(cid => { if (esc.length >= want) return; const L = dayAll.find(x => x.p === p && x.status === "class-away" && (x.req.classIds || []).indexOf(cid) >= 0 && !taken.has(x.teacherId)); if (L) { esc.push(L.teacherId); taken.add(L.teacherId); } });
        if (esc.length < want) {
          const busy = E.busyTeachersAt(M, placements, base, d * M.P + p);
          const present = new Set(dayAll.filter(x => x.status !== "class-away").map(x => x.teacherId));
          const cand = data.teachers.filter((t, ti) => !busy.has(t.id) && !taken.has(t.id) && present.has(t.id) && !M.tOff[ti][d * M.P + p]).sort((a, b) => (load[a.id] || 0) - (load[b.id] || 0));
          while (esc.length < want && cand.length) { const t = cand.shift(); esc.push(t.id); taken.add(t.id); load[t.id] = (load[t.id] || 0) + 1; }
        }
        if (esc.length < want) notes.push("חסר מלווה לקבוצה " + (gi + 1) + " בשעה " + n);
        return { group: gi, classIds: g.classIds, station, escortIds: esc };
      });
      return { period: n, assign };
    });
    const ev = Object.assign({}, spec, { from, to, kind: spec.kind || "סדנאות", classIds: spec.classIds || [], workshop: { stations: stations.map(st => ({ name: st.name, roomId: st.roomId || null, teacherId: st.teacherId || null })), groups: groups.map(g => ({ classIds: g.classIds, students: g.students })), slots } });
    delete ev.stations;
    return { event: ev, notes };
  };

  // ---------- exams: rooms + proctors ----------
  // ev: {id,title,from,to,classIds,groups, exam:{students, perRoom, ratio, seatPct, roomTypes:[...], rooms:[{roomId,students,proctors:[{period,teacherIds}]}]}}
  // Returns a plan that keeps what already works (rooms/proctors) and adds what is missing.
  E.planExam = function (M, placements, daily, d, ev, weekLoad) {
    const fp = M.cfg.firstPeriod || 0;
    const ex = Object.assign({ students: 0, perRoom: 1, ratio: 30, seatPct: 100, roomTypes: ["כיתה", "אולם"] }, ev.exam || {});
    const from = +(ev.from || fp), to = +(ev.to || ev.from || fp);
    const ps = []; for (let n = from; n <= to; n++) ps.push(n - fp);
    // the day without this exam's rooms/proctors (but with its classes away)
    const base = JSON.parse(JSON.stringify(daily || {}));
    base.events = (base.events || []).filter(e => e.id !== ev.id).concat([Object.assign({}, ev, { exam: null, escorts: ev.escorts || [] })]);
    base.changes = base.changes || {};
    const data = M.data;
    const seatsOf = r => Math.floor(Math.min(M.capOf(r), 400) * (ex.seatPct || 100) / 100);
    const notes = [];
    const changes = [];
    // ----- rooms -----
    const used = ps.map(p => E.roomsInUse(M, placements, base, d, p));
    const candidates = data.rooms.filter(r => ex.roomTypes.indexOf(r.type) >= 0 && M.capOf(r) < Infinity && seatsOf(r) > 0 && M.roomFor(r, [], "event"));
    const prevRooms = new Map(((ev.exam || {}).rooms || []).map(r => [r.roomId, r]));
    const isFree = r => used.every(u => !u.has(r.id));
    const movesFor = r => { // can every lesson in room r during the exam move elsewhere?
      const mv = []; const taken = ps.map(() => new Set());
      for (let k = 0; k < ps.length; k++) {
        const L = used[k].get(r.id); if (!L) continue;
        if (L.exam) return null;
        const alt = E.freeRoomFor(M, placements, base, d, L, new Set([r.id].concat(Array.from(taken[k])).concat(Array.from(reserved[k] || []))));
        if (!alt) return null;
        taken[k].add(alt.id); mv.push({ L, alt, k });
      }
      return mv;
    };
    const reserved = ps.map(() => new Set());
    // fewest rooms, least wasted seats: keep rooms already planned, then take the largest rooms
    // until the rest fits in one room, and then the smallest room that holds the rest (best fit).
    // Free rooms first; rooms that need lessons moved out only when free ones are not enough.
    let remaining = ex.students;
    const rooms = [];
    const usedIds = new Set();
    const pickNext = () => {
      const prev = candidates.find(r => prevRooms.has(r.id) && !usedIds.has(r.id));
      if (prev) return prev;
      for (const tier of [true, false]) {
        const pool = candidates.filter(r => !usedIds.has(r.id) && isFree(r) === tier);
        if (!pool.length) continue;
        const fit = pool.filter(r => seatsOf(r) >= remaining).sort((a, b) => seatsOf(a) - seatsOf(b));
        if (fit.length) return fit[0];
        const freeSeats = pool.reduce((a, r) => a + seatsOf(r), 0);
        if (tier && freeSeats < remaining && candidates.some(r => !usedIds.has(r.id) && !isFree(r))) { /* free rooms alone are not enough: still use them, biggest first */ }
        return pool.sort((a, b) => seatsOf(b) - seatsOf(a))[0];
      }
      return null;
    };
    for (let guard = 0; guard < candidates.length && remaining > 0; guard++) {
      const r = pickNext(); if (!r) break;
      usedIds.add(r.id);
      let mv = [];
      if (!isFree(r)) { mv = movesFor(r); if (!mv) continue; }
      const st = Math.min(seatsOf(r), remaining);
      remaining -= st;
      rooms.push({ roomId: r.id, students: st, proctors: [] });
      ps.forEach((p, k) => reserved[k].add(r.id));
      mv.forEach(m => { changes.push({ op: "daily_room", date: null, pid: m.L.pid, group: m.L.gi, roomId: m.alt.id }); reserved[m.k].add(m.alt.id); base.changes[m.L.pid + "|" + m.L.gi] = Object.assign({}, base.changes[m.L.pid + "|" + m.L.gi] || { type: "room" }, { roomId: m.alt.id }); });
    }
    if (remaining > 0) notes.push("חסרים מקומות ל-" + remaining + " תלמידים: אין עוד חדרים פנויים מתאימים בשעות האלה. אפשר להוסיף סוגי חדרים (למשל מעבדה) או להעלות את אחוז המקומות.");
    // ----- proctors -----
    const N0 = E.normDaily(M, base);
    const dayAll = E.dayLessons(M, placements, base, d);
    const presentAt = new Map();
    dayAll.forEach(L => { if (L.effTeacherId && L.status !== "cancel" && L.status !== "class-away" && L.status !== "uncovered") { let a = presentAt.get(L.effTeacherId); if (!a) presentAt.set(L.effTeacherId, a = []); a.push(L.p); } });
    const freedBy = new Map(); // teacher -> periods whose lesson is gone because of this exam
    dayAll.forEach(L => { if (L.status === "class-away" && ps.indexOf(L.p) >= 0) { let a = freedBy.get(L.teacherId); if (!a) freedBy.set(L.teacherId, a = new Set()); a.add(L.p); } });
    const load = Object.assign({}, weekLoad || {});
    const chosenAt = ps.map(() => new Set());
    let shortage = 0;
    const releasable = []; // lessons we may cancel to free a teacher
    rooms.forEach(room => {
      const need = Math.max(ex.perRoom || 1, Math.ceil(room.students / (ex.ratio || 30)));
      const prev = prevRooms.get(room.roomId);
      ps.forEach((p, k) => {
        const busy = E.busyTeachersAt(M, placements, base, d * M.P + p);
        const prevIds = prev ? ((prev.proctors || []).find(x => +x.period === p + fp) || {}).teacherIds || [] : [];
        const prevRoomIds = k > 0 ? ((room.proctors.find(x => x.period === ps[k - 1] + fp) || {}).teacherIds || []) : [];
        const cands = [];
        data.teachers.forEach((t, ti) => {
          if (busy.has(t.id) || chosenAt[k].has(t.id) || M.tOff[ti][d * M.P + p] || N0.unavailableAt(t.id, p)) return;
          let score = 0; const why = [];
          const pr = presentAt.get(t.id) || [];
          if (freedBy.has(t.id) && freedBy.get(t.id).has(p)) { score += 7; why.push("השיעור שלו/ה בוטל בגלל הבחינה"); }
          else if (pr.some(x => x < p) && pr.some(x => x > p)) { score += 5; why.push("בחלון"); }
          else if (pr.length || freedBy.has(t.id)) { score += 3; why.push("נמצא/ת בבית הספר"); }
          else { score -= 6; why.push("לא עובד/ת היום"); }
          const dutyNow = dayAll.find(Y => Y.duty && Y.teacherId === t.id && Y.p === p && Y.status === "normal");
          if (dutyNow) { if (/ישיב|מליא|הנהלה|תורנ/.test(dutyNow.group.subject)) score -= 2; else { score += 2; why.push("בשעת " + dutyNow.group.subject); } }
          if (prevIds.indexOf(t.id) >= 0) { score += 3; why.push("כבר שובץ/ה"); }
          if (prevRoomIds.indexOf(t.id) >= 0) score += 1.5;
          score -= (load[t.id] || 0) * 1.2;
          cands.push({ id: t.id, score, why: why.join(", ") });
        });
        cands.sort((a, b) => b.score - a.score);
        const picked = [];
        for (const c of cands) { if (picked.length >= need) break; if (c.score < -2 && picked.length >= 1) break; picked.push(c); }
        // still short: free a teacher by releasing a lesson at the edge of its classes' day
        while (picked.length < need) {
          const L = dayAll.find(x => x.p === p && x.status === "normal" && x.req.groups.length === 1 && !chosenAt[k].has(x.teacherId) && !picked.some(q => q.id === x.teacherId) && releasable.indexOf(x) < 0 && E.isEdgeLesson(dayAll, x));
          if (!L) break;
          releasable.push(L);
          changes.push({ op: "cancel", date: null, pid: L.pid, group: L.gi, release: true });
          picked.push({ id: L.teacherId, score: 0, why: "שוחרר/ה משיעור בקצה היום" });
        }
        if (picked.length < need) shortage += need - picked.length;
        picked.forEach(c => { chosenAt[k].add(c.id); load[c.id] = (load[c.id] || 0) + 1; });
        room.proctors.push({ period: p + fp, teacherIds: picked.map(c => c.id), why: picked.map(c => c.why) });
      });
    });
    if (shortage) notes.push("חסרים " + shortage + " משגיחים (שעה-חדר). אפשר להוסיף מורים שלא עובדים היום או לשחרר עוד שיעורים.");
    const nextEv = Object.assign({}, ev, { exam: Object.assign({}, ex, { rooms: rooms.map(r => ({ roomId: r.roomId, students: r.students, proctors: r.proctors.map(x => ({ period: x.period, teacherIds: x.teacherIds })) })) }) });
    return { event: nextEv, rooms, changes, notes, seats: ex.students - Math.max(0, remaining), shortage: { students: Math.max(0, remaining), proctors: shortage } };
  };

  // why can't a lesson be placed? (static reasons only)
  E.diagnose = function (M, reqId) {
    const ri = M.reqIdx.get(reqId); if (ri === undefined) return [];
    const r = M.reqs[ri]; const out = [];
    const days = new Set();
    for (let s = 0; s < M.nS; s++) {
      if (!M.valid[s]) continue;
      if (r.teachers.some(t => M.tOff[t][s])) continue;
      days.add(Math.floor(s / M.P));
    }
    if (days.size * r.maxPerDay < r.hours) out.push("יש רק " + days.size + " ימים שבהם כל המורים זמינים, ומותר " + r.maxPerDay + " שעות ביום – לא מספיק ל-" + r.hours + " שעות. כדאי להגדיל את 'מקסימום ביום' או לשנות יום חופש.");
    r.teachers.forEach(t => {
      let free = 0; for (let s = 0; s < M.nS; s++) if (M.valid[s] && !M.tOff[t][s]) free++;
      let load = 0; M.reqs.forEach(q => { if (q.teachers.indexOf(t) >= 0) load += q.hours; });
      if (load > free) out.push(M.data.teachers[t].name + " צריך/ה ללמד " + load + " שעות אבל זמין/ה רק " + free + ".");
    });
    r.classes.forEach(c => {
      let load = 0; M.reqs.forEach(q => { if (q.classes.indexOf(c) >= 0) load += q.hours; });
      let slots = 0; for (let s = 0; s < M.nS; s++) if (M.valid[s]) slots++;
      if (load > slots) out.push("לכיתה " + M.data.classes[c].name + " יש " + load + " שעות אבל רק " + slots + " משבצות בשבוע.");
    });
    r.resNeed.forEach(([res, n]) => { const R = M.resources[res]; if (R.supply < n) out.push("השיעור צריך " + n + " חדרים מסוג " + R.type + (R.thr ? " עם " + R.thr + " מקומות ומעלה" : "") + " בו-זמנית, ויש רק " + R.supply + "."); });
    M.tooBig.filter(x => x.reqId === r.id).forEach(x => out.push("קבוצת " + r.src.groups[x.gi].subject + " גדולה מדי (" + x.need + " תלמידים) – החדר הגדול ביותר מסוג " + x.type + " מכיל " + x.max + "."));
    if (!out.length) out.push("אין סתירה ישירה בנתונים – כנראה צפיפות. אפשר להריץ שוב את המחולל, לשחרר נעילות או להוסיף זמינות למורים.");
    return out;
  };

  // ---------- demo school ----------
  E.demoData = function (seed) {
    const rnd = E.rng(seed || 7);
    const pick = a => a[(rnd() * a.length) | 0];
    const config = {
      schoolName: "תיכון לדוגמה",
      days: ["א", "ב", "ג", "ד", "ה"],
      periods: [9, 9, 9, 9, 8],
      firstPeriod: 1,
      times: [["08:00", "08:45"], ["08:45", "09:30"], ["09:45", "10:30"], ["10:30", "11:15"], ["11:30", "12:15"], ["12:15", "13:00"], ["13:15", "14:00"], ["14:00", "14:45"], ["14:45", "15:30"], ["15:30", "16:15"]],
      roomTypes: ["כיתה", "מעבדה", "מחשבים", "ספורט", "אולם"],
    };
    const grades = ["ט", "י", "יא", "יב"];
    const classes = [], rooms = [];
    grades.forEach((g, gi) => {
      for (let k = 1; k <= 5; k++) {
        const rid = "r" + (gi + 1) + "0" + k;
        rooms.push({ id: rid, name: String((gi + 1) * 100 + k), type: "כיתה", capacity: 40 });
        classes.push({ id: "c_" + gi + "_" + k, name: g + k, grade: g, homeRoom: rid, students: 29 + ((rnd() * 9) | 0) });
      }
    });
    [["120", 24], ["121", 24], ["220", 32], ["221", 32], ["320", 45], ["321", 45], ["420", 60]].forEach(([n, c]) => rooms.push({ id: "r" + n, name: n, type: "כיתה", capacity: c }));
    [["מעבדת ביולוגיה", 40], ["מעבדת כימיה", 32], ["מעבדת פיזיקה", 32], ["מעבדה רב-תחומית", 40]].forEach(([n, c], i) => rooms.push({ id: "lab" + i, name: n, type: "מעבדה", capacity: c }));
    ["מחשבים 1", "מחשבים 2"].forEach((n, i) => rooms.push({ id: "pc" + i, name: n, type: "מחשבים", capacity: 40 }));
    ["אולם ספורט", "מגרש", "חדר כושר"].forEach((n, i) => rooms.push({ id: "gym" + i, name: n, type: "ספורט" }));
    rooms.push({ id: "hall", name: "אולם תרבות", type: "אולם", capacity: 220 });
    rooms.push({ id: "lib", name: "ספרייה", type: "אולם", capacity: 50 });

    // sections: what needs teaching
    const reqs = [];
    const sections = []; // {subject, hours, grade, reqRef, gi}
    let rq = 0;
    function addReq(classIds, hours, groups, extra) {
      const r = Object.assign({ id: "q" + (++rq), classIds, hours, maxPerDay: 1, double: false, groups: groups.map(g => ({ subject: g[0], teacherId: null, roomType: g[1] || "כיתה" })) }, extra || {});
      reqs.push(r);
      r.groups.forEach((g, i) => sections.push({ subject: g.subject, hours, grade: (classes.find(c => c.id === classIds[0]) || {}).grade, req: r, gi: i, classIds }));
      return r;
    }
    grades.forEach((g, gi) => {
      const cls = classes.filter(c => c.grade === g).map(c => c.id);
      // math & english: grade-wide הקבצות
      const mathLevels = gi < 2 ? ["מתמטיקה 5", "מתמטיקה 5", "מתמטיקה 4", "מתמטיקה 4", "מתמטיקה 3", "מתמטיקה 3"] : ["מתמטיקה 5", "מתמטיקה 5", "מתמטיקה 4", "מתמטיקה 4", "מתמטיקה 3", "מתמטיקה 3"];
      addReq(cls, 5, mathLevels.map(s => [s]), { label: "הקבצות מתמטיקה " + g, maxPerDay: 2, double: true });
      addReq(cls, gi < 2 ? 4 : 5, ["אנגלית 5", "אנגלית 5", "אנגלית 4", "אנגלית 4", "אנגלית 3", "אנגלית 3"].map(s => [s]), { label: "הקבצות אנגלית " + g, maxPerDay: 2, double: true });
      if (gi >= 2) {
        const ma = addReq(cls, 5, [["ביולוגיה", "מעבדה"], ["כימיה", "מעבדה"], ["מדעי המחשב", "מחשבים"], ["תקשורת"], ["ספרות מורחב"], ["פיזיקה", "מעבדה"]], { label: "מגמות א׳ " + g, maxPerDay: 2, double: true });
        [38, 24, 30, 28, 18, 25].forEach((n, i) => { ma.groups[i].students = n; });
        const mb = addReq(cls, 5, [["ביולוגיה", "מעבדה"], ["פסיכולוגיה"], ["מדעי המחשב", "מחשבים"], ["היסטוריה מורחב"], ["אמנות"], ["כלכלה"]], { label: "מגמות ב׳ " + g, maxPerDay: 2, double: true });
        [26, 42, 28, 20, 22, 25].forEach((n, i) => { mb.groups[i].students = n; });
      }
      // phys ed pairs: boys / girls
      for (let k = 0; k < cls.length; k += 2) {
        const pair = cls.slice(k, k + 2);
        if (pair.length === 2) addReq(pair, 2, [["חנ\"ג בנים", "ספורט"], ["חנ\"ג בנות", "ספורט"]], { label: "חנ\"ג " + pair.map(id => classes.find(c => c.id === id).name).join("+") });
        else addReq(pair, 2, [["חנ\"ג", "ספורט"]]);
      }
      cls.forEach(cid => {
        const per = [];
        if (gi === 0) per.push(["לשון", 3], ["ספרות", 2], ["היסטוריה", 2], ["תנ\"ך", 3], ["גאוגרפיה", 2], ["מדעים", 3, "מעבדה"], ["מחשבים", 2, "מחשבים"], ["ערבית", 2], ["חינוך", 1]);
        if (gi === 1) per.push(["לשון", 3], ["ספרות", 2], ["היסטוריה", 2], ["תנ\"ך", 3], ["אזרחות", 2], ["ביולוגיה", 2, "מעבדה"], ["כימיה", 2, "מעבדה"], ["פיזיקה", 2, "מעבדה"], ["ערבית", 2], ["חינוך", 1]);
        if (gi === 2) per.push(["לשון", 2], ["ספרות", 2], ["היסטוריה", 2], ["תנ\"ך", 2], ["אזרחות", 2], ["חינוך", 1]);
        if (gi === 3) per.push(["ספרות", 2], ["היסטוריה", 2], ["תנ\"ך", 2], ["אזרחות", 2], ["חינוך", 1]);
        per.forEach(([s, h, rt]) => addReq([cid], h, [[s, rt || "כיתה"]]));
      });
    });

    // teachers by subject family
    const fam = s => s.replace(/ \d$/, "").replace(" מורחב", "").replace(/ (בנים|בנות)$/, "");
    const firsts = ["מיכל", "יוסי", "רונית", "אבי", "שירה", "דוד", "נועה", "איתי", "הדס", "עמית", "תמר", "גיל", "ליאת", "אורי", "יעל", "רועי", "מורן", "אלון", "דנה", "עידו", "קרן", "ניר", "שני", "אסף", "ענבל", "יואב", "סיגל", "עומר", "מירב", "חן", "אורית", "טל", "אפרת", "ברק", "ורד", "שגיא", "הילה", "זיו", "רינת", "אייל", "גלית", "תומר", "אסנת", "יובל", "לימור", "שחר", "דפנה", "נדב", "אביטל", "רז"];
    const lasts = ["כהן", "לוי", "מזרחי", "פרץ", "ביטון", "אברהם", "פרידמן", "שפירא", "אזולאי", "דהן", "גבאי", "חדד", "אוחיון", "יוסף", "גולן", "ברק", "שלום", "רוזן", "אדלר", "קפלן", "סגל", "וייס", "נחום", "עמר", "אלמוג", "הררי", "זילבר", "טל", "מלכה", "בן דוד"];
    const teachers = [];
    const usedNames = new Set();
    function newTeacher(subjects, gender) {
      let name;
      do { name = pick(firsts) + " " + pick(lasts); } while (usedNames.has(name));
      usedNames.add(name);
      const t = { id: "t" + (teachers.length + 1), name, subjects: subjects.slice(), off: [], load: 0 };
      teachers.push(t); return t;
    }
    const MAXLOAD = 24;
    // group sections by family; assign with locality (same grade first)
    const famMap = new Map();
    sections.forEach(sec => { const f = fam(sec.subject); let a = famMap.get(f); if (!a) famMap.set(f, a = []); a.push(sec); });
    famMap.forEach((secs, f) => {
      if (f === "חינוך") return;
      const pool = [];
      secs.forEach(sec => {
        // a teacher can't take two groups of the same req (simultaneous)
        let t = pool.find(t => t.load + sec.hours <= MAXLOAD && !sec.req.groups.some(g => g.teacherId === t.id) && (t.grades.has(sec.grade) || t.grades.size < 2));
        if (!t) { t = newTeacher([f]); t.grades = new Set(); pool.push(t); }
        t.grades.add(sec.grade);
        t.load += sec.hours;
        sec.req.groups[sec.gi].teacherId = t.id;
      });
    });
    // homeroom: pick a teacher already teaching the class with low load
    reqs.filter(r => r.groups[0].subject === "חינוך").forEach(r => {
      const cid = r.classIds[0];
      const cands = teachers.filter(t => !t.homeroom && reqs.some(q => q !== r && q.classIds.indexOf(cid) >= 0 && q.groups.some(g => g.teacherId === t.id)) && t.load <= MAXLOAD - 1);
      cands.sort((a, b) => a.load - b.load);
      const t = cands[0] || teachers.slice().sort((a, b) => a.load - b.load)[0];
      t.homeroom = cid; t.load += 1; if (t.subjects.indexOf("חינוך") < 0) t.subjects.push("חינוך");
      r.groups[0].teacherId = t.id;
      const c = classes.find(c => c.id === cid); c.educator = t.id;
    });
    // add a few part-time teachers with a second subject
    // days off: ~35% get one free day
    const inBlock = new Set(); reqs.forEach(r => { if (r.groups.length > 1 && r.hours >= 4) r.groups.forEach(g => inBlock.add(g.teacherId)); });
    teachers.forEach(t => {
      if (t.load <= 20 && !inBlock.has(t.id) && rnd() < 0.45) t.off.push(String((rnd() * 5) | 0));
      if (rnd() < 0.15) t.off.push("4-8");
    });
    teachers.forEach(t => { delete t.load; delete t.grades; delete t.homeroom; });
    return { config, teachers, classes, rooms, reqs };
  };

  // ---------- import helpers (Shahaf / Excel tables) ----------
  E.HEADER_ALIASES = {
    teacher: ["מורה", "שם מורה", "מורים", "שם המורה", "מורה מלמד", "teacher"],
    subject: ["מקצוע", "שם מקצוע", "נושא", "subject"],
    klass: ["כיתה", "כיתות", "שכבה/כיתה", "קבוצה", "class"],
    day: ["יום", "day"],
    period: ["שעה", "שעת לימוד", "period", "hour"],
    room: ["חדר", "שם חדר", "room"],
    hours: ["ש\"ש", "שש", "שעות", "שעות שבועיות", "מס שעות", "hours"],
    group: ["הקבצה", "רצועה", "מקבץ", "group", "block"],
  };
  E.detectColumns = function (headers) {
    const norm = s => String(s || "").replace(/["'״׳]/g, "").replace(/\s+/g, " ").trim().toLowerCase();
    const map = {};
    headers.forEach((h, i) => {
      const n = norm(h);
      for (const key in E.HEADER_ALIASES) {
        if (map[key] !== undefined) continue;
        if (E.HEADER_ALIASES[key].some(a => norm(a) === n)) { map[key] = i; return; }
      }
    });
    headers.forEach((h, i) => {
      const n = norm(h);
      for (const key in E.HEADER_ALIASES) {
        if (map[key] !== undefined) continue;
        if (Object.values(map).indexOf(i) >= 0) continue;
        if (E.HEADER_ALIASES[key].some(a => n.indexOf(norm(a)) >= 0)) { map[key] = i; return; }
      }
    });
    return map;
  };
  E.parseDay = function (v, days) {
    const s = String(v || "").replace(/["'״׳]/g, "").replace("יום", "").trim();
    if (/^\d+$/.test(s)) { const n = +s; return n >= 1 && n <= days.length ? n - 1 : -1; }
    const names = ["ראשון", "שני", "שלישי", "רביעי", "חמישי", "שישי"];
    let i = names.indexOf(s); if (i >= 0) return i < days.length ? i : -1;
    i = days.indexOf(s); if (i >= 0) return i;
    i = E.DAY_NAMES.indexOf(s); return i >= 0 && i < days.length ? i : -1;
  };

  // rows: array of objects {teacher, subject, klass, day?, period?, room?, hours?, group?}
  // Builds data (teachers/classes/rooms/reqs) and optional placements, merging into base data.
  E.importRows = function (base, rows, mode) {
    const data = JSON.parse(JSON.stringify(base));
    const cfg = data.config;
    const P = Math.max.apply(null, cfg.periods);
    const byName = (list, name) => list.find(x => x.name === name);
    const report = { teachers: 0, classes: 0, rooms: 0, reqs: 0, placed: 0, skipped: [] };
    const getTeacher = name => {
      name = String(name || "").trim(); if (!name) return null;
      let t = byName(data.teachers, name);
      if (!t) { t = { id: E.uid("t"), name, subjects: [], off: [] }; data.teachers.push(t); report.teachers++; }
      return t;
    };
    const getClass = name => {
      name = String(name || "").trim(); if (!name) return null;
      let c = byName(data.classes, name);
      if (!c) { c = { id: E.uid("c"), name, grade: name.replace(/\d+$/, "").trim() }; data.classes.push(c); report.classes++; }
      return c;
    };
    const getRoom = name => {
      name = String(name || "").trim(); if (!name) return null;
      let r = byName(data.rooms, name);
      if (!r) { r = { id: E.uid("r"), name, type: "כיתה" }; data.rooms.push(r); report.rooms++; }
      return r;
    };
    const placements = {};
    if (mode === "timetable") {
      // 0) adapt the week to the file: hour 0, Friday, more periods per day
      const norm = rows.map((row, i) => {
        let d = E.parseDay(row.day, cfg.days);
        if (d < 0) { const d6 = E.parseDay(row.day, ["א", "ב", "ג", "ד", "ה", "ו"]); if (d6 === 5) d = 5; }
        const pn = parseInt(String(row.period == null ? "" : row.period).replace(/[^\d]/g, ""), 10);
        return { i, d, pn, row };
      });
      if (norm.some(x => x.d === 5) && cfg.days.length === 5) { cfg.days = cfg.days.concat(["ו"]); cfg.periods = cfg.periods.concat([6]); report.configChanged = true; }
      if (norm.some(x => x.pn === 0) && (cfg.firstPeriod || 0) === 1) { cfg.firstPeriod = 0; cfg.periods = cfg.periods.map(n => n + 1); if (cfg.times) cfg.times.unshift(["", ""]); report.configChanged = true; }
      const fp0 = cfg.firstPeriod || 0;
      norm.forEach(x => { if (x.d >= 0 && x.pn >= 0) { const need = x.pn - fp0 + 1; if (need > cfg.periods[x.d] && need <= 14) { cfg.periods[x.d] = need; report.configChanged = true; } } });
      const P2 = Math.max.apply(null, cfg.periods);
      // 1) one entry per (slot, teacher, subject); classes of the same lesson are merged
      const entries = new Map();
      norm.forEach(x => {
        const p = x.pn - fp0;
        if (x.d < 0 || !(p >= 0 && p < P2) || isNaN(x.pn)) { report.skipped.push("שורה " + (x.i + 2) + ": יום/שעה לא מזוהים (" + (x.row.day || "") + " " + (x.row.period || "") + ")"); return; }
        const subject = String(x.row.subject || "").trim(), teacher = String(x.row.teacher || "").trim();
        if (!subject && !teacher) { report.skipped.push("שורה " + (x.i + 2) + ": חסרים מקצוע ומורה"); return; }
        const classNames = String(x.row.klass || "").split(/[,+;\/]/).map(v => v.trim()).filter(Boolean);
        const s = x.d * P2 + p;
        const key = s + "|" + (teacher ? "t:" + teacher + "|" + subject : "c:" + classNames.slice().sort().join(",") + "|" + subject);
        let e = entries.get(key);
        if (!e) entries.set(key, e = { s, subject: subject || "שיעור", teacher, classes: new Set(), room: "", group: "" });
        classNames.forEach(n => e.classes.add(n));
        if (!e.room && x.row.room) e.room = String(x.row.room).trim();
        if (!e.group && x.row.group) e.group = String(x.row.group).trim();
      });
      // 2) per slot: lessons that share a class run in parallel = one block (הקבצה / מגמה / בנים-בנות)
      const bySlot = new Map();
      entries.forEach(e => { let a = bySlot.get(e.s); if (!a) bySlot.set(e.s, a = []); a.push(e); });
      const blocks = new Map(); // signature -> {classes, groups, label, slots:[{s, rooms}]}
      bySlot.forEach((list, s) => {
        const parent = list.map((_, i) => i);
        const find = i => parent[i] === i ? i : (parent[i] = find(parent[i]));
        const owner = new Map();
        list.forEach((e, i) => {
          e.classes.forEach(c => { if (owner.has(c)) parent[find(i)] = find(owner.get(c)); else owner.set(c, i); });
          if (e.group) { const gk = "#g:" + e.group; if (owner.has(gk)) parent[find(i)] = find(owner.get(gk)); else owner.set(gk, i); }
        });
        const comps = new Map();
        list.forEach((e, i) => { const r = find(i); let a = comps.get(r); if (!a) comps.set(r, a = []); a.push(e); });
        comps.forEach(members => {
          members.sort((a, b) => (a.subject + a.teacher).localeCompare(b.subject + b.teacher));
          const classes = Array.from(new Set([].concat.apply([], members.map(m => Array.from(m.classes))))).sort();
          const sig = classes.join(",") + "||" + members.map(m => m.subject + "|" + m.teacher).join(";");
          let b = blocks.get(sig);
          if (!b) blocks.set(sig, b = { classes, groups: members.map(m => ({ subject: m.subject, teacher: m.teacher })), label: (members.find(m => m.group) || {}).group || "", slots: [] });
          b.slots.push({ s, rooms: members.map(m => m.room) });
        });
      });
      // 3) one requirement per recurring block; placements keep the exact slots and rooms
      blocks.forEach(b => {
        const roomTypeOf = gi => { const names = b.slots.map(x => x.rooms[gi]).filter(Boolean); if (!names.length) return "כיתה"; const r = byName(data.rooms, names[0]) || getRoom(names[0]); return r.type || "כיתה"; };
        const groups = b.groups.map((g, gi) => {
          const t = getTeacher(g.teacher); if (t && g.subject && t.subjects.indexOf(g.subject) < 0) t.subjects.push(g.subject);
          return { subject: g.subject, teacherId: t ? t.id : null, roomType: roomTypeOf(gi) };
        });
        const classIds = b.classes.map(n => getClass(n).id);
        const slots = b.slots.sort((a, c) => a.s - c.s);
        const perDay = {}; slots.forEach(x => { const d = Math.floor(x.s / P2); perDay[d] = (perDay[d] || 0) + 1; });
        const dbl = slots.some((x, k) => k && slots[k - 1].s === x.s - 1);
        const req = { id: E.uid("q"), classIds, hours: slots.length, maxPerDay: Math.max.apply(null, Object.values(perDay)), double: dbl, groups };
        if (b.label) req.label = b.label;
        else if (groups.length > 1) req.label = Array.from(new Set(groups.map(g => g.subject.replace(/ \d$/, "")))).slice(0, 3).join("/") + " – " + b.classes.join(",");
        data.reqs.push(req); report.reqs++;
        if (groups.length > 1) report.blocks = (report.blocks || 0) + 1;
        slots.forEach((x, k) => {
          placements[E.pidOf(req.id, k)] = { s: x.s, rooms: x.rooms.map(n => { const rm = n ? getRoom(n) : null; return rm ? rm.id : null; }), locked: false };
          report.placed++;
        });
      });
    } else {
      // requirements: teacher, subject, class(es), hours, optional group (rows with same group = one block)
      const blocks = new Map();
      rows.forEach((row, i) => {
        const hours = parseInt(row.hours, 10);
        if (!(hours > 0)) { report.skipped.push("שורה " + (i + 2) + ": חסר מספר שעות"); return; }
        const classNames = String(row.klass || "").split(/[,+;\/]/).map(s => s.trim()).filter(Boolean);
        const t = getTeacher(row.teacher);
        const subject = String(row.subject || "").trim() || "שיעור";
        if (t && t.subjects.indexOf(subject) < 0) t.subjects.push(subject);
        const g = { subject, teacherId: t ? t.id : null, roomType: "כיתה" };
        if (row.room) { const rm = getRoom(row.room); g.room = rm.id; g.roomType = rm.type; }
        const classIds = classNames.map(n => getClass(n).id);
        if (row.group) {
          let b = blocks.get(row.group);
          if (!b) { b = { id: E.uid("q"), label: String(row.group), classIds: [], hours, maxPerDay: 1, double: false, groups: [] }; blocks.set(row.group, b); data.reqs.push(b); report.reqs++; }
          classIds.forEach(id => { if (b.classIds.indexOf(id) < 0) b.classIds.push(id); });
          b.hours = Math.max(b.hours, hours);
          b.groups.push(g);
        } else {
          data.reqs.push({ id: E.uid("q"), classIds, hours, maxPerDay: hours >= 5 ? 2 : 1, double: false, groups: [g] }); report.reqs++;
        }
      });
    }
    return { data, placements, report };
  };

  // Timetable grids (one table per class: rows = periods, columns = days, cell = subject / teacher / room)
  // sheets: [{name, aoa}] -> {rows:[{day,period,klass,subject,teacher,room}], classes:[...]} or null
  E.gridToRows = function (sheets) {
    const dayTok = v => { const t = String(v == null ? "" : v).replace(/["'״׳]/g, "").replace(/יום/g, "").trim(); const names = ["ראשון", "שני", "שלישי", "רביעי", "חמישי", "שישי"]; let i = names.indexOf(t); if (i < 0) i = E.DAY_NAMES.indexOf(t); return i; };
    const out = [], classes = [];
    sheets.forEach(sh => {
      const aoa = sh.aoa || [];
      // a sheet can hold several class tables stacked vertically
      for (let r = 0; r < aoa.length; r++) {
        const row = aoa[r] || [];
        const dayCols = []; row.forEach((v, c) => { const d = dayTok(v); if (d >= 0) dayCols.push({ c, d }); });
        if (dayCols.length < 3) continue;
        // class name: a cell above mentioning "כיתה", else the sheet name
        let klass = "";
        for (let k = r - 1; k >= Math.max(0, r - 4) && !klass; k--) (aoa[k] || []).forEach(v => { const m = /כית(?:ה|ת)\s*[:\-]?\s*([^\s,]+)/.exec(String(v || "")); if (m && !klass) klass = m[1]; });
        if (!klass) (row.slice(0, Math.min.apply(null, dayCols.map(x => x.c)))).forEach(v => { const t = String(v || "").trim(); if (t && !/שעה|^\d+$/.test(t) && !klass) klass = t; });
        if (!klass) klass = String(sh.name || "").trim();
        let added = 0;
        for (let k = r + 1; k < aoa.length; k++) {
          const rr = aoa[k] || [];
          if (rr.filter(v => dayTok(v) >= 0).length >= 3) break; // next table
          const lead = rr.slice(0, Math.min.apply(null, dayCols.map(x => x.c))).map(v => String(v == null ? "" : v).trim()).find(v => /^\d{1,2}$/.test(v) || /^שעה\s*\d{1,2}/.test(v));
          if (lead == null) { if (rr.every(v => !String(v == null ? "" : v).trim())) { if (added) break; else continue; } else continue; }
          const period = parseInt(String(lead).replace(/[^\d]/g, ""), 10);
          dayCols.forEach(({ c, d }) => {
            E.parseCell(rr[c]).forEach(x => { out.push({ day: E.DAY_NAMES[d], period, klass, subject: x.subject, teacher: x.teacher, room: x.room }); added++; });
          });
        }
        if (added && classes.indexOf(klass) < 0) classes.push(klass);
      }
    });
    return out.length ? { rows: out, classes } : null;
  };
  // one cell -> lessons. Supports "מקצוע – מורה (חדר) | ..." and multi-line "מקצוע\nמורה\nחדר"
  E.parseCell = function (v) {
    const txt = String(v == null ? "" : v).replace(/\r/g, "").trim(); if (!txt) return [];
    const parts = txt.indexOf("|") >= 0 ? txt.split("|") : txt.split(/\n\s*\n/);
    const res = [];
    parts.map(x => x.trim()).filter(Boolean).forEach(part => {
      let subject = "", teacher = "", room = "";
      const pm = /\(([^)]+)\)\s*$/.exec(part); if (pm) { room = pm[1].trim(); part = part.slice(0, pm.index).trim(); }
      const lines = part.split("\n").map(x => x.trim()).filter(Boolean);
      if (lines.length >= 2) {
        subject = lines[0]; teacher = lines[1];
        if (!room && lines[2]) room = lines[2].replace(/^חדר\s*/, "");
      } else {
        const m = part.split(/\s+[–-]\s+/);
        subject = m[0].trim(); teacher = (m[1] || "").trim();
        if (m[2] && !room) room = m[2].trim();
      }
      res.push({ subject, teacher, room });
    });
    return res;
  };

  // flat export rows (for Excel / Shahaf)
  E.exportRows = function (M, placements) {
    const data = M.data, out = [];
    for (const pid in placements) {
      const pl = placements[pid]; const ri = M.reqIdx.get(E.reqOfPid(pid)); if (ri === undefined) continue;
      const r = M.reqs[ri].src; const { d, p } = E.slotDP(M, pl.s);
      (r.groups || []).forEach((g, gi) => {
        const t = data.teachers[M.tIdx.get(g.teacherId)];
        const rm = data.rooms[M.rIdx.get((pl.rooms || [])[gi])];
        out.push({
          "יום": M.cfg.days[d], "שעה": p + (M.cfg.firstPeriod || 0),
          "כיתה": (r.classIds || []).map(id => (data.classes[M.cIdx.get(id)] || {}).name).join(","),
          "מקצוע": g.subject, "מורה": t ? t.name : "", "חדר": rm ? rm.name : "", "הקבצה": r.label || "",
        });
      });
    }
    out.sort((a, b) => (M.cfg.days.indexOf(a["יום"]) - M.cfg.days.indexOf(b["יום"])) || (a["שעה"] - b["שעה"]) || a["כיתה"].localeCompare(b["כיתה"], "he"));
    return out;
  };

  return E;
}
