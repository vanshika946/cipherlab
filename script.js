/* CipherLab – five classical ciphers, implemented by hand (no libraries).
   Section 1: helpers | 2: the ciphers | 3: visualisations | 4: UI (cards, workspaces, buttons) */

/* ================= 1. HELPERS ================= */
class Err extends Error {}                          // validation errors shown to the user
const mod = (n, m) => ((n % m) + m) % m;            // true modulo (JS % can be negative)
const letters = t => t.toUpperCase().replace(/[^A-Z]/g, ''); // keep only A–Z
const num = c => c.charCodeAt(0) - 65;              // A=0 ... Z=25
const chr = n => String.fromCharCode(65 + mod(n, 26));

/* ================= 2. THE CIPHERS ================= */

/* ---------- PLAYFAIR (5x5, I and J share a cell) ---------- */
function createPlayfairMatrix(key) {
  // keyword first, then the rest of the alphabet; duplicates skipped; J becomes I
  const seq = (letters(key) + 'ABCDEFGHIKLMNOPQRSTUVWXYZ').replace(/J/g, 'I');
  const m = [];
  for (const c of seq) if (!m.includes(c)) m.push(c);
  return m; // 25 letters, row-major
}
function preparePlayfairText(text) {
  // Classroom convention: HELLO -> HE LX LO, JAZZ -> JA ZX ZX
  const s = letters(text).replace(/J/g, 'I');
  const pairs = [];
  let i = 0;
  while (i < s.length) {
    const a = s[i], b = s[i + 1];
    const filler = a === 'X' ? 'Z' : 'X';           // filler is X (Z only if the letter itself is X)
    if (b === undefined) { pairs.push(a + filler); break; }   // odd letter at the end: pad
    if (a === b) { pairs.push(a + filler); i += 1; }          // same letters: insert filler between
    else { pairs.push(a + b); i += 2; }
  }
  return pairs;
}
function playfairPairs(m, pairs, dir) {             // dir = +1 encrypt, -1 decrypt
  return pairs.map(p => {
    const i = m.indexOf(p[0]), j = m.indexOf(p[1]);
    const r1 = Math.floor(i / 5), c1 = i % 5, r2 = Math.floor(j / 5), c2 = j % 5;
    if (r1 === r2) return m[r1 * 5 + mod(c1 + dir, 5)] + m[r2 * 5 + mod(c2 + dir, 5)]; // same row
    if (c1 === c2) return m[mod(r1 + dir, 5) * 5 + c1] + m[mod(r2 + dir, 5) * 5 + c2]; // same column
    return m[r1 * 5 + c2] + m[r2 * 5 + c1];                                              // rectangle
  });
}
function playfairEncrypt(text, key) {
  const m = createPlayfairMatrix(key), pairs = preparePlayfairText(text);
  if (!pairs.length) throw new Err('Playfair needs at least one letter (A–Z) in the text. Digits and symbols are ignored.');
  const outPairs = playfairPairs(m, pairs, 1);
  return { out: outPairs.join(''), viz: vizPlayfair(m, pairs, outPairs, 'Prepared pairs', 'Encrypted pairs') };
}
function playfairDecrypt(text, key) {
  const m = createPlayfairMatrix(key), s = letters(text).replace(/J/g, 'I');
  if (!s.length) throw new Err('Playfair needs at least one letter (A–Z) in the text.');
  if (s.length % 2) throw new Err('Playfair ciphertext must have an even number of letters.');
  const pairs = s.match(/../g);
  if (pairs.some(p => p[0] === p[1])) throw new Err('Invalid Playfair ciphertext: a pair never has two identical letters.');
  const outPairs = playfairPairs(m, pairs, -1);
  return { out: outPairs.join(''), viz: vizPlayfair(m, pairs, outPairs, 'Ciphertext pairs', 'Decrypted pairs') +
    '<p class="warn">The result may contain filler X/Z letters added during encryption (e.g. HELXLO). Remove them by reading the sense of the message.</p>' };
}

/* ---------- HILL (n x n key, n = 2, 3 or 4; C = K x P mod 26, column vectors) ---------- */
function modInverse(a, m) {                         // x such that a*x = 1 (mod m), or null
  a = mod(a, m);
  for (let x = 1; x < m; x++) if ((a * x) % m === 1) return x;
  return null;
}
function gcd(a, b) { return b === 0 ? a : gcd(b, a % b); }
function minorMatrix(rows, r, c) {                  // delete row r and column c
  return rows.filter((_, i) => i !== r).map(row => row.filter((_, j) => j !== c));
}
function determinant(rows) {                        // exact integer cofactor expansion along the first row (no floating point)
  if (rows.length === 1) return rows[0][0];
  return rows[0].reduce((sum, v, j) => sum + (j % 2 ? -1 : 1) * v * determinant(minorMatrix(rows, 0, j)), 0);
}
function matrixInverse(k) {                         // k = flat row-major key with n*n entries (already reduced mod 26)
  const n = Math.round(Math.sqrt(k.length));
  const rows = Array.from({ length: n }, (_, i) => k.slice(i * n, i * n + n));
  const detRaw = determinant(rows), det = mod(detRaw, 26);
  const detInv = modInverse(det, 26);
  if (detInv === null)                              // invertible only if gcd(det, 26) = 1
    throw new Err(`This key matrix cannot be inverted mod 26: det(K) = ${detRaw} ≡ ${det} (mod 26) and gcd(${det}, 26) = ${gcd(det, 26)}, but it must be 1. The determinant must be odd and not a multiple of 13. Change one or more entries.`);
  // inverse = det^-1 x adjugate; adjugate[i][j] = cofactor of element (j, i) = (-1)^(i+j) x det(minor(j, i))
  const m = [];
  for (let i = 0; i < n; i++)
    for (let j = 0; j < n; j++)
      m.push(mod(detInv * ((i + j) % 2 ? -1 : 1) * determinant(minorMatrix(rows, j, i)), 26));
  return { n, detRaw, det, detInv, m };
}
function hillApply(text, key, decrypt) {
  const k = key.map(v => {
    if (String(v).trim() === '' || !Number.isInteger(Number(v))) throw new Err('Every cell of the Hill key matrix must be a whole number.');
    return mod(Number(v), 26);
  });
  const n = Math.round(Math.sqrt(k.length));
  if (![2, 3, 4].includes(n) || n * n !== k.length) throw new Err('The Hill key matrix must be 2×2, 3×3 or 4×4.');
  const inv = matrixInverse(k);                     // also validates the key for encryption
  const use = decrypt ? inv.m : k;
  let s = letters(text);
  if (!s.length) throw new Err('Hill cipher needs at least one letter (A–Z) in the text.');
  let padded = 0;
  while (s.length % n) { s += 'X'; padded++; }      // pad with X until the length is a multiple of n
  let out = '', steps = [];
  for (let b = 0; b < s.length; b += n) {
    const block = s.slice(b, b + n), P = [...block].map(num);   // column vector of n numbers
    const lines = [`Block ${block}: vector = (${P.join(', ')})`];
    for (let r = 0; r < n; r++) {                   // row r of the matrix times the vector
      const terms = P.map((p, c) => `${use[r * n + c]}×${p}`).join(' + ');
      const sum = P.reduce((acc, p, c) => acc + use[r * n + c] * p, 0);
      const v = mod(sum, 26);
      out += chr(v);
      lines.push(`  row ${r + 1}: ${terms} = ${sum}, ${sum} mod 26 = ${v} = ${chr(v)}`);
    }
    steps.push(lines.join('\n'));
  }
  return { out, viz: vizHill(k, inv, use, decrypt, steps, padded) };
}
const hillEncrypt = (text, key) => hillApply(text, key, false);
const hillDecrypt = (text, key) => hillApply(text, key, true);

/* ---------- VIGENÈRE and OTP share the same arithmetic ---------- */
function shiftText(text, key, dir) {                // dir = +1 encrypt (P+K), -1 decrypt (C-K)
  const k = letters(key);
  let j = 0, out = '', rows = [];
  for (const ch of text) {
    if (/[a-z]/i.test(ch)) {
      const p = num(ch.toUpperCase()), kv = num(k[j % k.length]);   // key repeats (Vigenère only)
      const c = mod(p + dir * kv, 26);
      rows.push([ch.toUpperCase(), p, k[j % k.length], kv, chr(c), c]);
      out += chr(c); j++;
    } else out += ch;                               // spaces/punctuation stay in place
  }
  return { out, rows };
}
function checkKeyLetters(key) {
  if (!key.trim()) throw new Err('Enter a key.');
  if (/[^A-Za-z]/.test(key.trim())) throw new Err('The key may contain letters A–Z only (no spaces, digits or symbols).');
}
function vigenereEncrypt(text, key) { checkKeyLetters(key); const r = shiftText(text, key, 1);  return { out: r.out, viz: vizVigenere(r.rows, false) }; }
function vigenereDecrypt(text, key) { checkKeyLetters(key); const r = shiftText(text, key, -1); return { out: r.out, viz: vizVigenere(r.rows, true) }; }

function validateOtpKey(text, key) {
  checkKeyLetters(key);
  const need = letters(text).length, have = key.trim().length;
  if (have !== need) throw new Err(`Key length mismatch: the message has ${need} letters but the key has ${have}. A one-time pad key must be exactly as long as the message and never repeats.`);
}
function otpEncrypt(text, key) { validateOtpKey(text, key); const r = shiftText(text, key, 1);  return { out: r.out, viz: vizOtp(r.rows, false) }; }
function otpDecrypt(text, key) { validateOtpKey(text, key); const r = shiftText(text, key, -1); return { out: r.out, viz: vizOtp(r.rows, true) }; }
function generateOtpKey(length) {                   // random letters from the browser's random source
  let key = '';
  while (key.length < length) {
    const b = crypto.getRandomValues(new Uint8Array(1))[0];
    if (b < 234) key += chr(b % 26);                // 234 = 26*9, rejects values that would bias the result
  }
  return key;
}

/* ---------- RAIL FENCE ---------- */
function railPattern(length, rails) {               // rail number of each position: 0,1,2,1,0,1,2...
  const p = []; let rail = 0, d = 1;
  for (let i = 0; i < length; i++) {
    p.push(rail);
    if (rail === 0) d = 1; else if (rail === rails - 1) d = -1;   // bounce at top and bottom
    rail += d;
  }
  return p;
}
function railSetup(text, railsValue) {
  const s = text.replace(/\s/g, '').toUpperCase();  // spaces are removed
  const rails = Number(railsValue);
  if (!Number.isInteger(rails) || rails < 2) throw new Err('Number of rails must be a whole number, at least 2.');
  if (rails > s.length) throw new Err(`Number of rails (${rails}) cannot exceed the text length (${s.length}).`);
  const pat = railPattern(s.length, rails);
  // reading order: rail 0 left-to-right, then rail 1, ... (sort positions by rail, ties by position)
  const order = [...Array(s.length).keys()].sort((a, b) => pat[a] - pat[b] || a - b);
  return { s, rails, pat, order };
}
function railFenceEncrypt(text, railsValue) {
  const { s, rails, pat, order } = railSetup(text, railsValue);
  return { out: order.map(i => s[i]).join(''), viz: vizRails(s, rails, pat) };
}
function railFenceDecrypt(text, railsValue) {
  const { s, rails, pat, order } = railSetup(text, railsValue);
  const plain = [];
  order.forEach((pos, k) => { plain[pos] = s[k]; });  // k-th ciphertext letter goes to the k-th slot in reading order
  return { out: plain.join(''), viz: vizRails(plain.join(''), rails, pat) };
}

/* ================= 3. VISUALISATIONS ================= */
function vizPlayfair(m, pairs, outPairs, l1, l2) {
  const cells = m.map(c => `<span>${c === 'I' ? 'I/J' : c}</span>`).join('');
  const chips = a => a.map(p => `<span>${p}</span>`).join('');
  return `<h3>5×5 matrix</h3><div class="mx" style="grid-template-columns:repeat(5,44px)">${cells}</div>
    <h3>${l1}</h3><div class="pairs">${chips(pairs)}</div><h3>${l2}</h3><div class="pairs">${chips(outPairs)}</div>`;
}
function matrixBox(arr, n) {
  return `<div class="mx" style="grid-template-columns:repeat(${n},44px)">${arr.map(v => `<span>${v}</span>`).join('')}</div>`;
}
function vizHill(k, inv, use, decrypt, steps, padded) {
  const n = inv.n;
  return `<h3>Key matrix K (${n}×${n})</h3><div class="scroll">${matrixBox(k, n)}</div>
    <p class="calc">det(K) = ${inv.detRaw} ≡ ${inv.det} (mod 26)\ngcd(${inv.det}, 26) = 1, so K is invertible\ndet⁻¹ = ${inv.detInv} because ${inv.det} × ${inv.detInv} ≡ 1 (mod 26)</p>
    <h3>Inverse matrix K⁻¹ = det⁻¹ × adj(K) mod 26</h3><div class="scroll">${matrixBox(inv.m, n)}</div>
    <h3>${decrypt ? 'P = K⁻¹ × C' : 'C = K × P'} (mod 26), blocks of ${n} letters</h3>
    <p class="calc">${steps.join('\n\n')}${padded ? `\n\n(padded with ${padded} X to complete the last block)` : ''}</p>`;
}
function numTable(rows, decrypt) {
  const h = decrypt ? ['C', 'K', 'P'] : ['P', 'K', 'C'];
  const line = (name, idx) => `<tr><th>${name}</th>${rows.map(r => `<td>${r[idx]}</td>`).join('')}</tr>`;
  const src = decrypt ? [0, 1, 4, 5] : [0, 1, 4, 5];
  return `<div class="scroll"><table>
    ${line(h[0] + ' letter', 0)}${line(h[0] + ' number', 1)}${line('K letter', 2)}${line('K number', 3)}${line(h[2] + ' number', 5)}${line(h[2] + ' letter', 4)}</table></div>`;
}
function vizVigenere(rows, decrypt) {
  // 26x26 table: row = key letter, column = plaintext letter, cell = ciphertext letter
  // highlight cell (key row, plaintext column); when decrypting, the plaintext number is r[5]
  const hit = new Set(rows.map(r => `${r[3]},${decrypt ? r[5] : r[1]}`));
  let t = '<tr><th></th>' + [...Array(26).keys()].map(c => `<th>${chr(c)}</th>`).join('') + '</tr>';
  for (let r = 0; r < 26; r++) {
    t += `<tr><th>${chr(r)}</th>`;
    for (let c = 0; c < 26; c++) t += `<td class="${hit.has(r + ',' + c) ? 'hl' : ''}">${chr(r + c)}</td>`;
    t += '</tr>';
  }
  return `<h3>Numbers (A=0 … Z=25)</h3>${numTable(rows, decrypt)}
    <h3>Vigenère table (row = key letter, column = plaintext letter)</h3><div class="scroll"><table>${t}</table></div>`;
}
function vizOtp(rows, decrypt) {
  return `<p class="warn">Key accepted: it has exactly one letter per message letter, so nothing repeats.</p>
    <h3>Message and key, letter by letter</h3>${numTable(rows, decrypt)}`;
}
function vizRails(s, rails, pat) {
  let t = '';
  for (let r = 0; r < rails; r++)
    t += `<tr><th>${r + 1}</th>${[...s].map((ch, i) => `<td class="${pat[i] === r ? 'hl' : ''}">${pat[i] === r ? ch : ''}</td>`).join('')}</tr>`;
  return `<h3>Zig-zag pattern</h3><div class="scroll"><table>${t}</table></div><p>Ciphertext = read each rail from left to right, top rail first.</p>`;
}

/* ================= 4. UI ================= */
const CIPHERS = {
  playfair: { name: 'Playfair', sym: 'PF', tag: 'Digraph substitution', short: 'Encrypts letters in pairs using a 5×5 keyword grid.',
    desc: 'Playfair encrypts two letters at a time using a 5×5 grid built from a keyword. I and J share one cell.',
    fields: [{ id: 'key', type: 'text', label: 'Keyword', def: 'MONARCHY' }], enc: playfairEncrypt, dec: playfairDecrypt,
    how: `<ol><li>Write the keyword into the grid, skipping repeated letters, then the rest of the alphabet (I/J together).</li>
      <li>Split the text into pairs. Identical letters get a filler X between them (HELLO → HE LX LO). A lone last letter gets a filler too.</li>
      <li>Same row: take the letter to the right. Same column: take the letter below (both wrap around).</li>
      <li>Otherwise form a rectangle: each letter is replaced by the one in its own row, in the other letter's column.</li>
      <li>Decryption goes left/up instead, with the same rectangle rule.</li></ol>` },
  hill: { name: 'Hill', sym: 'H', tag: 'Matrix cipher', short: 'Multiplies blocks of letters by an n×n key matrix mod 26.',
    desc: 'Hill turns letters into numbers (A=0 … Z=25) and multiplies each block of n letters by an n×n key matrix (2×2, 3×3 or 4×4), modulo 26: C = K × P.',
    fields: [{ id: 'key', type: 'matrix', label: 'Key matrix size and entries' }], enc: hillEncrypt, dec: hillDecrypt,
    how: `<ol><li>Choose the size n. Split the text into blocks of n letters (pad the last block with X) and turn each block into a column vector P.</li>
      <li>Compute C = K × P (mod 26): each ciphertext number is one row of K times P, reduced mod 26.</li>
      <li>To decrypt you need K⁻¹ = det(K)⁻¹ × adj(K) (mod 26), where adj is the adjugate (transposed cofactors).</li>
      <li>K works only if gcd(det(K), 26) = 1, otherwise no inverse exists mod 26.</li>
      <li>Example: K = [9 4; 5 7], ME = (12, 4) → (9×12 + 4×4, 5×12 + 7×4) mod 26 = (20, 10) → UK.</li></ol>` },
  vigenere: { name: 'Vigenère', sym: 'V', tag: 'Polyalphabetic', short: 'A repeating keyword shifts each letter by a different amount.',
    desc: 'Vigenère shifts each letter by the matching letter of a repeating keyword, so one plaintext letter can encrypt to many different letters.',
    fields: [{ id: 'key', type: 'text', label: 'Key', def: 'LEMON' }], enc: vigenereEncrypt, dec: vigenereDecrypt,
    how: `<ol><li>Convert letters to numbers, A=0 … Z=25.</li><li>Repeat the key across the letters of the message (spaces and punctuation are skipped).</li>
      <li>Encrypt: C = (P + K) mod 26. Decrypt: P = (C − K) mod 26.</li><li>The table shows the ciphertext letter at the crossing of key row and plaintext column.</li></ol>` },
  otp: { name: 'One-Time Pad', sym: 'OTP', tag: 'Perfect secrecy', short: 'Vigenère arithmetic with a random key as long as the message.',
    desc: 'The one-time pad uses the same arithmetic as Vigenère, but the key is as long as the message, never repeats, and is used only once.',
    fields: [{ id: 'key', type: 'text', label: 'Key (same number of letters as the message)', def: '' }], enc: otpEncrypt, dec: otpDecrypt, gen: true,
    how: `<ol><li>Encrypt: C = (P + K) mod 26. Decrypt: P = (C − K) mod 26.</li>
      <li>A true OTP key is <b>random</b>, <b>secret</b>, <b>exactly as long as the message</b>, and <b>never reused</b>.</li>
      <li>Reuse or a repeating key breaks its perfect secrecy, so CipherLab rejects keys of the wrong length.</li></ol>` },
  rail: { name: 'Rail Fence', sym: 'RF', tag: 'Transposition', short: 'Writes text in a zig-zag over rails, then reads row by row.',
    desc: 'Rail Fence does not change letters; it rearranges them. The text is written in a zig-zag over several rails and read off rail by rail.',
    fields: [{ id: 'rails', type: 'number', label: 'Number of rails', def: 3 }], enc: railFenceEncrypt, dec: railFenceDecrypt,
    how: `<ol><li>Remove spaces and write the letters diagonally down to the last rail, then diagonally back up, and repeat.</li>
      <li>Read the ciphertext along rail 1, then rail 2, and so on.</li>
      <li>To decrypt, compute the same zig-zag positions, fill them rail by rail with the ciphertext, then read along the zig-zag.</li>
      <li>Example: WEAREDISCOVEREDFLEEATONCE with 3 rails → WECRLTEERDSOEEFEAOCAIVDEN.</li></ol>` }
};
const $ = s => document.querySelector(s);

function buildCards() {
  if (!$('#cards').children.length)                 // cards are written in index.html; build them only if missing
  $('#cards').innerHTML = Object.entries(CIPHERS).map(([id, c]) =>
    `<button class="card" onclick="openWorkspace('${id}')"><div class="sym">${c.sym}</div><h3>${c.name}</h3><small>${c.tag}</small><p>${c.short}</p></button>`).join('');
  $('#tabs').innerHTML = Object.entries(CIPHERS).map(([id, c]) => `<button id="tab-${id}" onclick="openWorkspace('${id}')">${c.name}</button>`).join('');
}
function showDashboard() {
  $('#dashboard').hidden = false; $('#workspace').hidden = true; $('#tabs').hidden = true;
}
let hillN = 2;                                      // current Hill matrix size
const HILL_DEFAULTS = {                             // valid (invertible) starter keys
  2: [9, 4, 5, 7],
  3: [6, 24, 1, 13, 16, 10, 20, 17, 15],
  4: [1, 17, 24, 21, 19, 1, 16, 12, 5, 23, 1, 20, 3, 0, 18, 19]
};
function matrixInputsHtml() {
  return `<div class="mx mxk" style="grid-template-columns:repeat(${hillN},minmax(0,56px))">${HILL_DEFAULTS[hillN].map((v, i) =>
    `<input id="k${i}" type="number" step="1" value="${v}" aria-label="Row ${Math.floor(i / hillN) + 1}, column ${i % hillN + 1}">`).join('')}</div>`;
}
function setHillSize(n) {                           // rebuild the matrix inputs when the size changes
  hillN = n;
  $('#hillMatrix').innerHTML = matrixInputsHtml();
  document.querySelectorAll('.seg button').forEach(b => { const on = Number(b.dataset.n) === n; b.classList.toggle('on', on); b.setAttribute('aria-pressed', on); });
  $('#err').hidden = true;
}
function fieldHtml(f) {
  if (f.type === 'matrix')
    return `<label>${f.label}</label>
      <div class="seg" role="group" aria-label="Matrix size">${[2, 3, 4].map(n =>
        `<button type="button" data-n="${n}" class="${n === hillN ? 'on' : ''}" aria-pressed="${n === hillN}" onclick="setHillSize(${n})">${n}×${n}</button>`).join('')}</div>
      <div id="hillMatrix">${matrixInputsHtml()}</div>`;
  const extra = f.type === 'number' ? 'type="number" min="2" step="1"' : 'type="text" autocomplete="off" spellcheck="false"';
  return `<label for="${f.id}">${f.label}</label><input id="${f.id}" ${extra} value="${f.def}">`;
}
function openWorkspace(id) {
  const c = CIPHERS[id];
  if (id === 'hill') hillN = 2;                     // Clear / reopen resets the Hill size
  $('#dashboard').hidden = true; $('#tabs').hidden = false; $('#workspace').hidden = false;
  document.querySelectorAll('.tabs button').forEach(b => b.classList.toggle('on', b.id === 'tab-' + id));
  $('#workspace').innerHTML = `<div class="ws">
    <div class="panel"><h2>${c.name} cipher</h2><p>${c.desc}</p>
      <label for="input">Text</label><textarea id="input" placeholder="Type or paste the message here"></textarea>
      ${c.fields.map(fieldHtml).join('')}
      ${c.gen ? `<p class="warn">A true one-time pad key is random, secret, as long as the message, and used only once.</p><button class="btn ghost" onclick="fillOtpKey()">Generate random key</button>` : ''}
      <div class="btns"><button class="btn" onclick="run('${id}','enc')">Encrypt</button><button class="btn alt" onclick="run('${id}','dec')">Decrypt</button>
        <button class="btn ghost" onclick="openWorkspace('${id}')">Clear</button></div>
      <div id="err" class="err" role="alert" hidden></div>
      <label>Output</label><div id="output" class="out" aria-live="polite"></div></div>
    <div class="panel"><div id="viz"><p>Run the cipher to see how it works, step by step.</p></div></div></div>
    <details><summary>How it works</summary>${c.how}</details>`;
}
function fillOtpKey() {                             // OTP helper: random key matching the message
  const n = letters($('#input').value).length;
  if (!n) { showErr('Type the message first so the key can match its length.'); return; }
  $('#key').value = generateOtpKey(n); $('#err').hidden = true;
}
function showErr(msg) { $('#err').textContent = msg; $('#err').hidden = false; }
function run(id, mode) {
  const c = CIPHERS[id];
  $('#err').hidden = true;
  try {
    const text = $('#input').value;
    if (!text.trim()) throw new Err('Enter the text to ' + (mode === 'enc' ? 'encrypt.' : 'decrypt.'));
    let key;
    const f = c.fields[0];
    if (f.type === 'matrix') key = [...Array(hillN * hillN).keys()].map(i => $('#k' + i).value);
    else {
      key = $('#' + f.id).value;
      if (f.type === 'text' && !letters(key).length) throw new Err('Enter a key with at least one letter (A–Z).');
    }
    const r = c[mode](text, key);
    $('#output').textContent = r.out; $('#viz').innerHTML = r.viz;
  } catch (e) {
    if (!(e instanceof Err)) throw e;
    showErr(e.message); $('#output').textContent = '';
  }
}
buildCards();

// Make the functions used by inline onclick="..." handlers explicitly global
Object.assign(window, { openWorkspace, showDashboard, run, fillOtpKey, setHillSize });
