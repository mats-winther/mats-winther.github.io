/* relocationchess.js
 * Relocation Chess (Chess64) board with randomizer, legal-move checking and
 * Chess960-style castling. Load with: <script src="relocationchess.js"></script>
 * Author of the variant: Mats Winther. No external dependencies.
 */
(function () {
  'use strict';
  if (window.RelocationChess) { window.RelocationChess.open(); return; }

  /* ---------------------------------------------------------------- *
   *  Basic helpers
   * ---------------------------------------------------------------- */
  var FILES = 'abcdefgh';
  var GLYPH = { K: '\u265A', Q: '\u265B', R: '\u265C', B: '\u265D', N: '\u265E', P: '\u265F\uFE0E' };
  var KN = [[1,2],[2,1],[-1,2],[-2,1],[1,-2],[2,-1],[-1,-2],[-2,-1]];
  var KG = [[1,0],[-1,0],[0,1],[0,-1],[1,1],[1,-1],[-1,1],[-1,-1]];
  var DIAG = [[1,1],[1,-1],[-1,1],[-1,-1]];
  var ORTH = [[1,0],[-1,0],[0,1],[0,-1]];

  function sqName(i) { return FILES[i & 7] + ((i >> 3) + 1); }
  function opp(c) { return c === 'w' ? 'b' : 'w'; }
  function inB(r, f) { return r >= 0 && r < 8 && f >= 0 && f < 8; }

  /* ---------------------------------------------------------------- *
   *  Relocation Chess set-ups (the 8 possible arrays per side)
   * ---------------------------------------------------------------- */
  function bishopsOK(a) {
    var p = [];
    for (var i = 0; i < 8; i++) if (a[i] === 'B') p.push(i);
    return (p[0] + p[1]) % 2 === 1;            // different square colours
  }
  function relocationArrays() {
    var base = 'RNBQKBNR'.split(''), seen = {}, res = [];
    function add(a) {
      var s = a.join('');
      if (seen[s] || !bishopsOK(a)) return;
      seen[s] = true; res.push(a);
    }
    add(base.slice());                                     // standard array
    [3, 4].forEach(function (mover) {                      // queen (d) or king (e)
      for (var j = 1; j < 7; j++) {                        // anything but the rooks
        if (j === mover) continue;
        var a = base.slice(); var t = a[mover]; a[mover] = a[j]; a[j] = t;
        add(a);
      }
    });
    return res;                                            // 8 arrays -> 8 x 8 = 64 positions
  }
  var ARRAYS = relocationArrays();
  var STANDARD = 'RNBQKBNR'.split('');

  /* ---------------------------------------------------------------- *
   *  Position / rules engine
   *  board: array of 64, index = rank*8+file (a1 = 0), items like 'wK'
   * ---------------------------------------------------------------- */
  function makePosition(wRow, bRow, curtailed) {
    var b = new Array(64).fill(null);
    for (var f = 0; f < 8; f++) {
      b[f] = 'w' + wRow[f]; b[8 + f] = 'wP';
      b[48 + f] = 'bP';     b[56 + f] = 'b' + bRow[f];
    }
    var castle = { wK: true, wQ: true, bK: true, bQ: true };
    if (curtailed) {                                       // optional "curtailed castling"
      var wk = wRow.indexOf('K'), bk = bRow.indexOf('K');
      if (wk === 1 || wk === 6) castle.wK = castle.wQ = false;
      if (bk === 1 || bk === 6) castle.bK = castle.bQ = false;
    }
    return { b: b, turn: 'w', castle: castle, ep: -1 };
  }

  function attacked(b, sq, by) {
    var r = sq >> 3, f = sq & 7, i, d, rr, ff, p;
    var pr = by === 'w' ? r - 1 : r + 1;
    for (d = -1; d <= 1; d += 2)
      if (inB(pr, f + d) && b[pr * 8 + f + d] === by + 'P') return true;
    for (i = 0; i < 8; i++) {
      rr = r + KN[i][0]; ff = f + KN[i][1];
      if (inB(rr, ff) && b[rr * 8 + ff] === by + 'N') return true;
      rr = r + KG[i][0]; ff = f + KG[i][1];
      if (inB(rr, ff) && b[rr * 8 + ff] === by + 'K') return true;
    }
    var sets = [[ORTH, 'R'], [DIAG, 'B']];
    for (var s = 0; s < 2; s++) for (i = 0; i < 4; i++) {
      rr = r + sets[s][0][i][0]; ff = f + sets[s][0][i][1];
      while (inB(rr, ff)) {
        p = b[rr * 8 + ff];
        if (p) { if (p[0] === by && (p[1] === sets[s][1] || p[1] === 'Q')) return true; break; }
        rr += sets[s][0][i][0]; ff += sets[s][0][i][1];
      }
    }
    return false;
  }

  function inCheck(b, c) {
    var k = b.indexOf(c + 'K');
    return k >= 0 && attacked(b, k, opp(c));
  }

  function pseudo(pos, c) {
    var b = pos.b, out = [];
    for (var i = 0; i < 64; i++) {
      var p = b[i];
      if (!p || p[0] !== c) continue;
      var t = p[1], r = i >> 3, f = i & 7, k, rr, ff, q, to;
      if (t === 'P') {
        var d = c === 'w' ? 1 : -1, start = c === 'w' ? 1 : 6, last = c === 'w' ? 7 : 0;
        var r1 = r + d;
        var addP = function (from, to, cap) {
          if ((to >> 3) === last) ['Q', 'R', 'B', 'N'].forEach(function (pr) {
            out.push({ from: from, to: to, piece: p, capture: cap, promo: pr });
          });
          else out.push({ from: from, to: to, piece: p, capture: cap });
        };
        if (inB(r1, f) && !b[r1 * 8 + f]) {
          addP(i, r1 * 8 + f, null);
          if (r === start && !b[(r + 2 * d) * 8 + f])
            out.push({ from: i, to: (r + 2 * d) * 8 + f, piece: p, dbl: true });
        }
        for (var df = -1; df <= 1; df += 2) {
          if (!inB(r1, f + df)) continue;
          to = r1 * 8 + f + df; q = b[to];
          if (q && q[0] !== c) addP(i, to, q);
          else if (!q && to === pos.ep)
            out.push({ from: i, to: to, piece: p, capture: opp(c) + 'P', ep: true });
        }
      } else if (t === 'N' || t === 'K') {
        var offs = t === 'N' ? KN : KG;
        for (k = 0; k < 8; k++) {
          rr = r + offs[k][0]; ff = f + offs[k][1];
          if (!inB(rr, ff)) continue;
          to = rr * 8 + ff; q = b[to];
          if (!q || q[0] !== c) out.push({ from: i, to: to, piece: p, capture: q });
        }
      } else {
        var dirs = t === 'R' ? ORTH : t === 'B' ? DIAG : ORTH.concat(DIAG);
        for (k = 0; k < dirs.length; k++) {
          rr = r + dirs[k][0]; ff = f + dirs[k][1];
          while (inB(rr, ff)) {
            to = rr * 8 + ff; q = b[to];
            if (!q) out.push({ from: i, to: to, piece: p });
            else { if (q[0] !== c) out.push({ from: i, to: to, piece: p, capture: q }); break; }
            rr += dirs[k][0]; ff += dirs[k][1];
          }
        }
      }
    }
    return out;
  }

  /* Chess960-style castling: king ends on g/c, rook on f/d, wherever they started. */
  function castles(pos, c) {
    var b = pos.b, out = [], r = c === 'w' ? 0 : 7, o = opp(c);
    var kSq = b.indexOf(c + 'K');
    if (kSq < 0 || (kSq >> 3) !== r) return out;
    ['K', 'Q'].forEach(function (side) {
      if (!pos.castle[c + side]) return;
      var rookFrom = r * 8 + (side === 'K' ? 7 : 0);
      if (b[rookFrom] !== c + 'R') return;
      if (side === 'K' ? kSq > rookFrom : kSq < rookFrom) return;
      var kingTo = r * 8 + (side === 'K' ? 6 : 2);
      var rookTo = r * 8 + (side === 'K' ? 5 : 3);
      var ok = true, s;
      function chk(a, z) {
        for (s = Math.min(a, z); s <= Math.max(a, z); s++)
          if (s !== kSq && s !== rookFrom && b[s]) ok = false;
      }
      chk(kSq, kingTo); chk(rookFrom, rookTo);          // everything in between must be empty
      for (s = Math.min(kSq, kingTo); s <= Math.max(kSq, kingTo); s++)
        if (attacked(b, s, o)) ok = false;               // king's path (incl. start & end) safe
      if (ok) out.push({ from: kSq, to: rookFrom, castle: true, side: side,
                         piece: c + 'K', kingTo: kingTo, rookFrom: rookFrom, rookTo: rookTo });
    });
    return out;
  }

  function apply(pos, m) {
    var b = pos.b.slice(), c = pos.turn, ep = -1;
    var castle = { wK: pos.castle.wK, wQ: pos.castle.wQ, bK: pos.castle.bK, bQ: pos.castle.bQ };
    if (m.castle) {
      var king = b[m.from], rook = b[m.rookFrom];
      b[m.from] = null; b[m.rookFrom] = null;
      b[m.kingTo] = king; b[m.rookTo] = rook;
      castle[c + 'K'] = castle[c + 'Q'] = false;
    } else {
      b[m.from] = null;
      if (m.ep) b[m.to + (c === 'w' ? -8 : 8)] = null;
      b[m.to] = m.promo ? c + m.promo : m.piece;
      if (m.piece[1] === 'K') castle[c + 'K'] = castle[c + 'Q'] = false;
      if (m.dbl) ep = (m.from + m.to) / 2;
    }
    [[0, 'wQ'], [7, 'wK'], [56, 'bQ'], [63, 'bK']].forEach(function (x) {
      if (m.from === x[0] || m.to === x[0]) castle[x[1]] = false;
    });
    return { b: b, turn: opp(c), castle: castle, ep: ep };
  }

  function legal(pos) {
    var c = pos.turn, res = [];
    pseudo(pos, c).concat(castles(pos, c)).forEach(function (m) {
      if (!inCheck(apply(pos, m).b, c)) res.push(m);
    });
    return res;
  }

  function insufficient(b) {
    var n = [];
    b.forEach(function (p) { if (p && p[1] !== 'K') n.push(p[1]); });
    return n.length === 0 || (n.length === 1 && (n[0] === 'B' || n[0] === 'N'));
  }

  function toSAN(m, moves) {
    if (m.castle) return m.side === 'K' ? 'O-O' : 'O-O-O';
    var t = m.piece[1], s = '';
    if (t === 'P') {
      if (m.capture) s += FILES[m.from & 7] + 'x';
      s += sqName(m.to);
      if (m.promo) s += '=' + m.promo;
    } else {
      s += t;
      var o = moves.filter(function (x) {
        return !x.castle && x !== m && x.piece === m.piece && x.to === m.to && x.from !== m.from;
      });
      if (o.length) {
        var sf = o.some(function (x) { return (x.from & 7) === (m.from & 7); });
        var sr = o.some(function (x) { return (x.from >> 3) === (m.from >> 3); });
        if (!sf) s += FILES[m.from & 7];
        else if (!sr) s += (m.from >> 3) + 1;
        else s += sqName(m.from);
      }
      if (m.capture) s += 'x';
      s += sqName(m.to);
    }
    return s;
  }

  /* ---------------------------------------------------------------- *
   *  User interface
   * ---------------------------------------------------------------- */
  var win = null, launcher = null;
  var board, sqEl = [], statusEl, movesEl, setupEl, promoEl, curtailBox;
  var pos, startPos, hist = [], moves = [], sel = -1, flipped = false;
  var over = false, checked = false, pendingPromo = null;
  var setup = { w: STANDARD.slice(), b: STANDARD.slice() };

  function el(tag, cls, text) {
    var e = document.createElement(tag);
    if (cls) e.className = cls;
    if (text) e.textContent = text;
    return e;
  }

  function injectCSS() {
    var css =
      '.rc-win{--sz:min(52px,10.5vw);position:fixed;top:30px;left:30px;z-index:99999;background:#2b2b2b;color:#eee;' +
      'font:14px/1.35 Arial,sans-serif;border:1px solid #000;border-radius:6px;box-shadow:0 6px 24px rgba(0,0,0,.55);max-width:98vw}' +
      '.rc-title{cursor:move;padding:6px 10px;background:#444;display:flex;justify-content:space-between;align-items:center;' +
      'border-radius:6px 6px 0 0;user-select:none;touch-action:none;font-weight:bold}' +
      '.rc-x{cursor:pointer;background:none;border:0;color:#eee;font-size:18px}' +
      '.rc-body{display:flex;flex-wrap:wrap;gap:12px;padding:10px}' +
      '.rc-board{display:grid;grid-template-columns:repeat(8,var(--sz));grid-template-rows:repeat(8,var(--sz));border:2px solid #111}' +
      '.rc-sq{width:var(--sz);height:var(--sz);position:relative;display:flex;align-items:center;justify-content:center;' +
      'font-size:calc(var(--sz)*.76);line-height:1;cursor:pointer;user-select:none}' +
      '.rc-l{background:#f0d9b5}.rc-d{background:#b58863}' +
      '.rc-p{position:relative;z-index:1}' +
      '.rc-pw{color:#fff;text-shadow:0 0 2px #000,0 0 2px #000,0 0 3px #000}.rc-pb{color:#111}' +
      '.rc-sel{outline:3px solid #2f7de1;outline-offset:-3px}' +
      '.rc-last{box-shadow:inset 0 0 0 100px rgba(255,230,0,.35)}' +
      '.rc-chk{background-image:radial-gradient(circle,rgba(255,0,0,.85) 0,rgba(255,0,0,0) 70%)}' +
      '.rc-tgt::after{content:"";position:absolute;width:30%;height:30%;border-radius:50%;background:rgba(20,110,20,.55);z-index:2;pointer-events:none}' +
      '.rc-tgt.rc-cap::after{width:84%;height:84%;background:none;border:4px solid rgba(20,110,20,.6);box-sizing:border-box}' +
      '.rc-rk,.rc-fl{position:absolute;font-size:10px;color:rgba(0,0,0,.65);z-index:0;pointer-events:none;font-family:Arial,sans-serif}' +
      '.rc-rk{left:2px;top:1px}.rc-fl{right:2px;bottom:0}' +
      '.rc-side{width:250px;max-width:100%;display:flex;flex-direction:column;gap:8px}' +
      '.rc-btns{display:flex;flex-wrap:wrap;gap:6px}' +
      '.rc-btns button,.rc-promo button{padding:5px 9px;cursor:pointer;border:1px solid #777;background:#555;color:#fff;border-radius:4px}' +
      '.rc-btns button:hover,.rc-promo button:hover{background:#777}' +
      '.rc-status{font-weight:bold;min-height:1.3em}' +
      '.rc-setup{font:12px monospace;color:#bbb}' +
      '.rc-promo{display:none;gap:5px;align-items:center;flex-wrap:wrap}' +
      '.rc-promo button{font-size:22px;padding:2px 8px}' +
      '.rc-moves{background:#1e1e1e;border:1px solid #111;padding:6px;height:150px;overflow:auto;font-family:monospace;font-size:13px}' +
      '.rc-launch{position:fixed;right:14px;bottom:14px;z-index:99998;padding:8px 12px;background:#333;color:#fff;border:1px solid #000;' +
      'border-radius:6px;cursor:pointer;font:14px Arial,sans-serif}' +
      '.rc-small{font-size:12px;color:#ccc}';
    var st = document.createElement('style');
    st.textContent = css;
    document.head.appendChild(st);
  }

  function layout() {               // (re)order squares according to orientation
    board.innerHTML = '';
    for (var i = 0; i < 8; i++) for (var j = 0; j < 8; j++) {
      var r = flipped ? i : 7 - i, f = flipped ? 7 - j : j;
      var e = sqEl[r * 8 + f];
      e.querySelector('.rc-rk').textContent = j === 0 ? (r + 1) : '';
      e.querySelector('.rc-fl').textContent = i === 7 ? FILES[f] : '';
      board.appendChild(e);
    }
  }

  function buildUI() {
    injectCSS();
    win = el('div', 'rc-win');
    var title = el('div', 'rc-title');
    title.appendChild(el('span', '', 'Relocation Chess'));
    var x = el('button', 'rc-x', '\u00D7'); x.title = 'Close';
    x.onclick = function () { win.style.display = 'none'; };
    title.appendChild(x);
    win.appendChild(title);

    // dragging the window
    var drag = false, dx = 0, dy = 0;
    title.addEventListener('pointerdown', function (e) {
      if (e.target === x) return;
      var r = win.getBoundingClientRect(); dx = e.clientX - r.left; dy = e.clientY - r.top;
      drag = true; title.setPointerCapture(e.pointerId);
    });
    title.addEventListener('pointermove', function (e) {
      if (!drag) return;
      win.style.left = Math.max(0, e.clientX - dx) + 'px';
      win.style.top = Math.max(0, e.clientY - dy) + 'px';
    });
    title.addEventListener('pointerup', function () { drag = false; });

    var body = el('div', 'rc-body');
    board = el('div', 'rc-board');
    for (var s = 0; s < 64; s++) (function (sq) {
      var e = el('div', 'rc-sq');
      e.appendChild(el('span', 'rc-p'));
      e.appendChild(el('span', 'rc-rk'));
      e.appendChild(el('span', 'rc-fl'));
      e.addEventListener('click', function () { onSquare(sq); });
      e.addEventListener('dragstart', function (ev) {
        var p = pos.b[sq];
        if (over || pendingPromo || !p || p[0] !== pos.turn) { ev.preventDefault(); return; }
        try { ev.dataTransfer.setData('text/plain', sqName(sq)); } catch (err) {}
        select(sq);
      });
      e.addEventListener('dragover', function (ev) { ev.preventDefault(); });
      e.addEventListener('drop', function (ev) { ev.preventDefault(); if (sel >= 0 && sel !== sq) onSquare(sq); });
      sqEl[sq] = e;
    })(s);
    layout();
    body.appendChild(board);

    var side = el('div', 'rc-side');
    var btns = el('div', 'rc-btns');
    function btn(label, fn, tip) { var b = el('button', '', label); b.onclick = fn; if (tip) b.title = tip; btns.appendChild(b); }
    btn('Randomize', randomize, 'Random Relocation Chess position (each side independently)');
    btn('Standard', function () { newGame(STANDARD.slice(), STANDARD.slice()); });
    btn('Flip', function () { flipped = !flipped; layout(); render(); });
    btn('Undo', undo);
    side.appendChild(btns);

    var lab = el('label', 'rc-small');
    curtailBox = document.createElement('input'); curtailBox.type = 'checkbox';
    curtailBox.onchange = function () { newGame(setup.w, setup.b); };
    lab.appendChild(curtailBox);
    lab.appendChild(document.createTextNode(' Curtailed castling (no castling if king on b/g file; restarts game)'));
    side.appendChild(lab);

    statusEl = el('div', 'rc-status'); side.appendChild(statusEl);
    promoEl = el('div', 'rc-promo'); side.appendChild(promoEl);
    setupEl = el('div', 'rc-setup'); side.appendChild(setupEl);
    movesEl = el('div', 'rc-moves'); side.appendChild(movesEl);
    side.appendChild(el('div', 'rc-small',
      'Click or drag a piece, then its destination. To castle, click your king and then the rook ' +
      '(or the king\u2019s target square on c/g, if that is not an ordinary king move).'));
    body.appendChild(side);
    win.appendChild(body);
    document.body.appendChild(win);
  }

  /* ---- game control ---- */
  function newGame(wRow, bRow) {
    setup = { w: wRow.slice(), b: bRow.slice() };
    startPos = makePosition(wRow, bRow, curtailBox && curtailBox.checked);
    pos = startPos; hist = []; sel = -1; pendingPromo = null;
    update();
  }

  function randomize() {
    var pick = function () { return ARRAYS[Math.floor(Math.random() * ARRAYS.length)]; };
    newGame(pick(), pick());             // each side: 8 options -> 64 positions in all
  }

  function undo() {
    if (!hist.length) return;
    hist.pop();
    pos = hist.length ? hist[hist.length - 1].after : startPos;
    sel = -1; pendingPromo = null;
    update();
  }

  function update() {
    moves = legal(pos);
    checked = inCheck(pos.b, pos.turn);
    over = moves.length === 0 || insufficient(pos.b);
    render(); renderStatus(); renderMoves(); renderSetup();
    promoEl.style.display = 'none';
  }

  function select(sq) {
    sel = sq;
    render();
  }

  function movesFor(from, to) {
    return moves.filter(function (m) {
      if (m.from !== from) return false;
      if (m.to === to) return true;
      // alias: click the king's destination square to castle
      if (m.castle && m.kingTo === to && to !== from)
        return !moves.some(function (x) { return !x.castle && x.from === from && x.to === to; });
      return false;
    });
  }

  function onSquare(sq) {
    if (over || pendingPromo) return;
    if (sel >= 0 && sel !== sq) {
      var ms = movesFor(sel, sq);
      if (ms.length) {
        if (ms.length > 1 && ms[0].promo) { askPromotion(ms); return; }
        doMove(ms[0]); return;
      }
    }
    var p = pos.b[sq];
    if (p && p[0] === pos.turn && sq !== sel) select(sq);
    else select(-1);
  }

  function askPromotion(ms) {
    pendingPromo = ms;
    promoEl.innerHTML = '';
    promoEl.appendChild(el('span', '', 'Promote to: '));
    ms.forEach(function (m) {
      var b = el('button', '', GLYPH[m.promo]);
      b.title = m.promo;
      b.onclick = function () { pendingPromo = null; doMove(m); };
      promoEl.appendChild(b);
    });
    var c = el('button', '', 'Cancel'); c.style.fontSize = '13px';
    c.onclick = function () { pendingPromo = null; promoEl.style.display = 'none'; select(-1); };
    promoEl.appendChild(c);
    promoEl.style.display = 'flex';
  }

  function doMove(m) {
    var san = toSAN(m, moves);
    var after = apply(pos, m);
    var replies = legal(after), chk = inCheck(after.b, after.turn);
    if (chk) san += replies.length ? '+' : '#';
    hist.push({ m: m, san: san, before: pos, after: after });
    pos = after; sel = -1;
    update();
  }

  /* ---- rendering ---- */
  function render() {
    var tmap = {};
    if (sel >= 0) moves.forEach(function (m) {
      if (m.from === sel) tmap[m.to] = (m.castle || m.capture) ? 2 : 1;
    });
    var last = hist.length ? hist[hist.length - 1].m : null;
    var kSq = checked ? pos.b.indexOf(pos.turn + 'K') : -1;
    for (var sq = 0; sq < 64; sq++) {
      var e = sqEl[sq], p = pos.b[sq];
      var cls = 'rc-sq ' + ((((sq >> 3) + (sq & 7)) % 2 === 0) ? 'rc-d' : 'rc-l');
      if (sq === sel) cls += ' rc-sel';
      if (tmap[sq]) cls += ' rc-tgt' + (tmap[sq] === 2 ? ' rc-cap' : '');
      if (last && (sq === last.from || sq === (last.castle ? last.kingTo : last.to))) cls += ' rc-last';
      if (sq === kSq) cls += ' rc-chk';
      e.className = cls;
      var ps = e.firstChild;
      ps.textContent = p ? GLYPH[p[1]] : '';
      ps.className = 'rc-p' + (p ? (p[0] === 'w' ? ' rc-pw' : ' rc-pb') : '');
      e.draggable = !!p && p[0] === pos.turn && !over;
    }
  }

  function renderStatus() {
    var who = pos.turn === 'w' ? 'White' : 'Black';
    var t;
    if (moves.length === 0) t = checked ? 'Checkmate \u2013 ' + (pos.turn === 'w' ? 'Black' : 'White') + ' wins' : 'Stalemate \u2013 draw';
    else if (insufficient(pos.b)) t = 'Draw \u2013 insufficient material';
    else t = who + ' to move' + (checked ? ' (check)' : '');
    statusEl.textContent = t;
  }

  function renderMoves() {
    var s = '';
    hist.forEach(function (h, i) {
      if (i % 2 === 0) s += (i / 2 + 1) + '. ';
      s += h.san + ' ';
    });
    movesEl.textContent = s;
    movesEl.scrollTop = movesEl.scrollHeight;
  }

  function renderSetup() {
    setupEl.textContent = 'White: ' + setup.w.join(' ') + '   Black: ' + setup.b.join(' ');
  }

  /* ---- public API ---- */
  var api = {
    open: function () {
      if (!win) { buildUI(); newGame(STANDARD.slice(), STANDARD.slice()); }
      win.style.display = 'block';
      if (launcher) launcher.style.display = 'none';
    },
    randomize: function () { if (win) randomize(); },
    arrays: ARRAYS.map(function (a) { return a.join(''); })   // the 8 legal arrays per side
  };
  window.RelocationChess = api;
})();