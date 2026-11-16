// A fast, dependency-free drop-in for marked 18.1.3 (default options, GFM on).
// Written from the CommonMark 0.31.2 and GFM 0.29 specifications, verified
// case by case against marked's own output on the competition practice set.
// parse(markdown) returns exactly the HTML marked.parse(markdown) returns.
//
// Layout: a line-oriented block parser builds a small block tree, then an
// inline parser (delimiter stack, CommonMark appendix A) renders each leaf.
// No regular expressions in the hot paths; everything is charCodeAt/indexOf
// scanning and array-joined string building.

const CC_SPACE = 32;
const CC_TAB = 9;
const CC_NL = 10;
const CC_CR = 13;
const CC_LT = 60;
const CC_GT = 62;
const CC_AMP = 38;
const CC_QUOT = 34;
const CC_APOS = 39;
const CC_BACKSLASH = 92;

// Document-wide state, reset per parse(): an <a> tag whose href value
// contains a backslash-newline suppresses all later GFM autolinks
// (marked quirk -- the tag leaves its tokenizer inside a link).
let gfmSuppressed = false;

// An <a ... href="...\<newline>..."> tag (href value contains a
// backslash followed by a newline) triggers the suppression.
// An inline "<a " open tag (literal space after a/A, case-insensitive)
// puts marked's inline lexer in "inLink" state, suppressing all later
// GFM autolinks until a "</a>" resets it. A bare "<a>", "<a/>", or
// "<a\t..." does not trigger it; an "<a ...>" that forms an HTML block
// never reaches the inline parser, so it does not trigger it either.
function isGfmSuppressingTag(tag) {
  if (tag.length < 3 || tag.charCodeAt(0) !== CC_LT) return false;
  const c1 = tag.charCodeAt(1);
  if (c1 !== 97 && c1 !== 65) return false; // 'a' / 'A'
  return tag.charCodeAt(2) === CC_SPACE;
}
const CC_BACKTICK = 96;
const CC_STAR = 42;
const CC_UNDER = 95;
const CC_TILDE = 126;
const CC_LBRACK = 91;
const CC_RBRACK = 93;
const CC_LPAREN = 40;
const CC_RPAREN = 41;
const CC_BANG = 33;
const CC_HASH = 35;
const CC_DASH = 45;
const CC_PLUS = 43;
const CC_DOT = 46;
const CC_SLASH = 47;
const CC_COLON = 58;
const CC_SEMI = 59;
const CC_EQ = 61;
const CC_PIPE = 124;

// ---- character classes ----------------------------------------------------

function isSpace(c) {
  return c === CC_SPACE || c === CC_TAB || c === CC_NL || c === 11 || c === 12 || c === CC_CR;
}
// Unicode whitespace, as used by the flanking rules for emphasis.
function isSpaceOrNl(c) {
  return isUnicodeWhitespace(c);
}
function isAsciiPunct(c) {
  return (c >= 33 && c <= 47) || (c >= 58 && c <= 64) || (c >= 91 && c <= 96) || (c >= 123 && c <= 126);
}
const PUNCT_RE = /[\p{P}\p{S}]/u;
// A punctuation character (Unicode P or S category). `c` is a code point.
function isPunct(c) {
  if (c < 128) return isAsciiPunct(c);
  return PUNCT_RE.test(String.fromCodePoint(c));
}
function isAlnum(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
}
function isDigit(c) {
  return c >= 48 && c <= 57;
}
function isHex(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 70) || (c >= 97 && c <= 102);
}
function isWordChar(c) {
  return isAlnum(c) || c === CC_UNDER;
}
function isUnicodeWhitespace(c) {
  // The whitespace characters CommonMark treats as space for parsing purposes.
  return c === CC_SPACE || c === CC_TAB || c === CC_NL || c === 11 || c === 12 || c === CC_CR ||
    c === 0x85 || c === 0xa0 || c === 0x1680 || (c >= 0x2000 && c <= 0x200a) ||
    c === 0x2028 || c === 0x2029 || c === 0x202f || c === 0x205f || c === 0x3000;
}

// ---- HTML escaping --------------------------------------------------------
// marked escapes & < > " ' in text and code, except that an & that begins a
// valid character reference (&word+; or &#digits; / &#xhex;) is left as-is
// (named references are passed through verbatim; numeric ones are decoded
// first, by decodeEntities, so by the time text is escaped only named
// references remain). The same escape serves hrefs (after encodeURI) and
// titles and alt text.

// Parse an entity or numeric character reference at s[i] === '&'.
// Returns {ch, end, named} or null. Named references pass through verbatim
// (&word;); numeric ones are decoded (0 / surrogate / >0x10FFFF become
// U+FFFD; >7 decimal or >6 hex digits are not references at all).
function parseEntity(s, i) {
  let j = i + 1;
  if (s.charCodeAt(j) === CC_HASH) {
    j++;
    let hex = false;
    if (s.charCodeAt(j) === 120 || s.charCodeAt(j) === 88) { hex = true; j++; }
    const ds = j;
    if (hex) { while (j < s.length && isHex(s.charCodeAt(j))) j++; }
    else { while (j < s.length && isDigit(s.charCodeAt(j))) j++; }
    const digits = j - ds;
    if (digits === 0 || (hex && digits > 6) || (!hex && digits > 7) || s.charCodeAt(j) !== CC_SEMI) return null;
    const n = parseInt(s.slice(ds, j), hex ? 16 : 10);
    const ch = (n === 0 || n > 0x10ffff || (n >= 0xd800 && n <= 0xdfff)) ? '\uFFFD' : String.fromCodePoint(n);
    return { ch, end: j + 1, named: false };
  }
  const ds = j;
  while (j < s.length && isWordChar(s.charCodeAt(j))) j++;
  if (j === ds || s.charCodeAt(j) !== CC_SEMI) return null;
  return { ch: s.slice(i, j + 1), end: j + 1, named: true };
}

// Decode numeric character references in `s` (from..to); returns the string
// with &#...; replaced. Numeric refs out of range, zero or surrogates become
// U+FFFD; refs with >7 decimal or >6 hex digits are not references at all.
function decodeNumericEntities(s) {
  if (s.indexOf('&#') < 0) return s;
  let out = '';
  let i = 0;
  let start = 0;
  for (;;) {
    const amp = s.indexOf('&#', i);
    if (amp < 0) break;
    let j = amp + 2;
    let hex = false;
    if (s.charCodeAt(j) === 120 || s.charCodeAt(j) === 88) { hex = true; j++; }
    const ds = j;
    if (hex) { while (j < s.length && isHex(s.charCodeAt(j))) j++; }
    else { while (j < s.length && isDigit(s.charCodeAt(j))) j++; }
    const digits = j - ds;
    if (digits > 0 && ((hex && digits <= 6) || (!hex && digits <= 7)) && s.charCodeAt(j) === CC_SEMI) {
      const n = parseInt(s.slice(ds, j), hex ? 16 : 10);
      const ch = (n === 0 || n > 0x10ffff || (n >= 0xd800 && n <= 0xdfff)) ? '\uFFFD' : String.fromCodePoint(n);
      out += s.slice(start, amp) + ch;
      i = j + 1;
      start = i;
    } else {
      i = amp + 2;
    }
  }
  return start === 0 ? s : out + s.slice(start);
}

// Escape text, leaving valid named/numeric references alone. `s` may still
// hold numeric references (they are decoded by callers that need it); here a
// numeric-looking reference is also left alone, matching marked.
function escapeText(s) {
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === CC_AMP) {
      // valid reference? &word+; or &#digits; or &#xhex;
      let j = i + 1;
      if (s.charCodeAt(j) === CC_HASH) {
        j++;
        if (s.charCodeAt(j) === 120 || s.charCodeAt(j) === 88) {
          j++;
          const ds = j;
          while (j < s.length && isHex(s.charCodeAt(j))) j++;
          if (j > ds && j - ds <= 6 && s.charCodeAt(j) === CC_SEMI) { i = j; continue; }
        } else {
          const ds = j;
          while (j < s.length && isDigit(s.charCodeAt(j))) j++;
          if (j > ds && j - ds <= 7 && s.charCodeAt(j) === CC_SEMI) { i = j; continue; }
        }
      } else {
        const ds = j;
        while (j < s.length && isWordChar(s.charCodeAt(j))) j++;
        if (j > ds && s.charCodeAt(j) === CC_SEMI) { i = j; continue; }
      }
      out += s.slice(start, i) + '&amp;';
      start = i + 1;
    } else if (c === CC_LT) {
      out += s.slice(start, i) + '&lt;';
      start = i + 1;
    } else if (c === CC_GT) {
      out += s.slice(start, i) + '&gt;';
      start = i + 1;
    } else if (c === CC_QUOT) {
      out += s.slice(start, i) + '&quot;';
      start = i + 1;
    } else if (c === CC_APOS) {
      out += s.slice(start, i) + '&#39;';
      start = i + 1;
    }
  }
  return start === 0 ? s : out + s.slice(start);
}

// encodeURI, then escape & and ' (the HTML escape above handles both, and
// leaves &word; references alone). encodeURI already percent-encodes " < >
// space and non-ASCII, and leaves % alone.
function escapeHref(s) {
  // encodeURI, but an existing % is left alone (marked does not re-encode
  // percent sequences, so %25 from encodeURI is turned back into %)
  return escapeText(encodeURI(decodeNumericEntities(s)).replace(/%25/g, '%'));
}

// Unescape backslash escapes (\punct -> punct) in a string.
function unescapeBackslashes(s) {
  if (s.indexOf('\\') < 0) return s;
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    if (s.charCodeAt(i) === CC_BACKSLASH && i + 1 < s.length && isAsciiPunct(s.charCodeAt(i + 1))) {
      out += s.slice(start, i) + s[i + 1];
      i++;
      start = i + 1;
    }
  }
  return start === 0 ? s : out + s.slice(start);
}

// ---- line helpers (tab-aware columns) -------------------------------------
// A tab advances the column to the next multiple of 4. When a parser consumes
// columns of indentation that end inside a tab, the tab is partially consumed
// and is replaced by spaces filling to its tab stop.

// Columns of leading whitespace in line `s`, and the index of the first
// non-whitespace character. `base` is the absolute column of s[0] (tab
// stops are computed from absolute columns).
function leadingWhitespace(s, base) {
  let col = base || 0;
  let i = 0;
  while (i < s.length) {
    const c = s.charCodeAt(i);
    if (c === CC_SPACE) { col++; i++; }
    else if (c === CC_TAB) { col += 4 - (col % 4); i++; }
    else break;
  }
  return { col, idx: i };
}

// The string of `s` starting at absolute column `col`. `base` is the
// absolute column of s[0]. A tab straddling `col` is replaced by spaces
// filling to its tab stop. Inside a container (base > 0), a tab that
// begins the sliced string is also expanded to spaces filling to its
// tab stop (marked expands it when the container indent is stripped);
// at the top level a leading tab stays a literal tab.
function sliceFromColumn(s, col, base) {
  let c = base || 0;
  let i = 0;
  while (i < s.length && c < col) {
    const ch = s.charCodeAt(i);
    if (ch === CC_SPACE) { c++; i++; }
    else if (ch === CC_TAB) {
      const next = c + 4 - (c % 4);
      if (next <= col) { c = next; i++; }
      else return ' '.repeat(next - col) + s.slice(i + 1);
    } else break;
  }
  if ((base || 0) > 0 && c >= col) {
    let out = '';
    while (i < s.length) {
      const ch = s.charCodeAt(i);
      if (ch === CC_TAB) {
        const next = c + 4 - (c % 4);
        out += ' '.repeat(next - c);
        c = next; i++;
      } else if (ch === CC_SPACE) {
        out += ' ';
        c++; i++;
      } else break;
    }
    if (out) return out + s.slice(i);
  }
  return s.slice(i);
}

// Fenced-code content indent: marked strips up to `n` leading
// whitespace CHARACTERS (a tab counts as one and is removed whole,
// even when it straddles the indent boundary), not columns. Used for
// top-level fenced code; inside a container the column-based
// sliceFromColumn (which expands a remaining tab to spaces) still
// applies.
function stripFenceIndent(s, n) {
  let i = 0;
  while (i < s.length && i < n) {
    const ch = s.charCodeAt(i);
    if (ch === CC_SPACE || ch === CC_TAB) i++;
    else break;
  }
  return s.slice(i);
}

// A paragraph continuation line inside a LIST ITEM whose remainder is
// indented 4+ columns loses one indent unit (4 columns) -- the indented
// code indent. Inside a blockquote (or at the top level) the remainder
// keeps all its spaces: marked never strips a quote continuation.
function stripParaIndent(s, base, inItem) {
  if (!inItem) return s;
  const lw = leadingWhitespace(s, base);
  if (lw.col - (base || 0) < 4) return s;
  return sliceFromColumn(s, (base || 0) + 4, base);
}
// True when the block has a list-item ancestor (its continuation lines
// are indented relative to the item's content).
function hasItemAncestor(b) {
  for (let p = b ? b.parent : null; p; p = p.parent) {
    if (p.t === 'item') return true;
    if (p.t === 'doc') return false;
  }
  return false;
}

// The string of `s` starting at absolute column `target`, beginning the
// scan at character index `startIdx` whose absolute column is `startCol`
// (used to skip a list marker, which is not whitespace).
function sliceFromColumnAt(s, startIdx, startCol, target) {
  let c = startCol;
  let i = startIdx;
  while (i < s.length && c < target) {
    const ch = s.charCodeAt(i);
    if (ch === CC_SPACE) { c++; i++; }
    else if (ch === CC_TAB) {
      const next = c + 4 - (c % 4);
      if (next <= target) { c = next; i++; }
      else return ' '.repeat(next - target) + s.slice(i + 1);
    } else break;
  }
  return s.slice(i);
}

// The column of index `i` in `s` (tabs expand to tab stops).
function columnAt(s, i) {
  let col = 0;
  for (let k = 0; k < i; k++) {
    const c = s.charCodeAt(k);
    if (c === CC_TAB) col += 4 - (col % 4);
    else col++;
  }
  return col;
}

// Skip up to `max` columns of spaces/tabs starting at index `i` in `s`.
// Returns {idx, col, used} where used is the columns skipped.
function skipIndent(s, i, max) {
  let col = 0;
  let idx = i;
  while (idx < s.length && col < max) {
    const c = s.charCodeAt(idx);
    if (c === CC_SPACE) { col++; idx++; }
    else if (c === CC_TAB) {
      const next = col + 4 - (col % 4);
      if (next > max) break;
      col = next; idx++;
    } else break;
  }
  return { idx, col, used: col };
}

// Count trailing spaces (space/tab) at the end of `s`.
function trailingWhitespaceLen(s) {
  let n = 0;
  for (let i = s.length - 1; i >= 0; i--) {
    const c = s.charCodeAt(i);
    if (c === CC_SPACE || c === CC_TAB) n++;
    else break;
  }
  return n;
}

// ---- link labels, destinations, titles (shared by defs and inline links) --

// Normalize a link label for lookup: collapse whitespace to single spaces,
// trim, case-fold.
function normalizeLabel(s) {
  let out = '';
  let lastSpace = true; // trims leading whitespace too
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (isSpace(c)) {
      if (!lastSpace) { out += ' '; lastSpace = true; }
    } else {
      out += s[i];
      lastSpace = false;
    }
  }
  if (lastSpace && out.length > 0) out = out.slice(0, -1);
  // full Unicode case folding for the characters that fold to more than
  // one character (toLowerCase alone maps them to a single character)
  return out.toLowerCase()
    .replace(/\u00df/g, 'ss').replace(/\u1e9e/g, 'ss')
    .replace(/\u0130/g, 'i')
    .replace(/\ufb00/g, 'ff').replace(/\ufb01/g, 'fi').replace(/\ufb02/g, 'fl')
    .replace(/\ufb03/g, 'ffi').replace(/\ufb04/g, 'ffl')
    .replace(/\ufb05/g, 'st').replace(/\ufb06/g, 'st');
}

// Parse a link label starting at s[i] === '['. Returns {label, end} where
// end is the index just past the closing ']', or null. A label holds no
// unescaped '[' (marked rejects nested brackets in labels); backslash
// escapes are allowed and newlines may appear. At most 999 characters.
// ---- marked's masked-source computation (for the last-possible
// emphasis closer). marked masks a paragraph's inline source before
// computing where an emphasis closer may be: code spans, links and
// raw HTML are replaced by same-length "[aaa...]" runs (blockSkip),
// escaped punctuation is replaced by "+" and backticks inside a code
// span's content are replaced by "+" (anyPunctuationOutsideCode).
// A dangling backtick inside a link label can pair with a later
// backtick in this masked source, swallowing intervening * / _ / ~
// delimiters -- so an emphasis whose closer falls inside such a
// masked span has no valid closer and stays literal.
const RE_ANY_PUNCT_OUTSIDE_CODE = /(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\([\p{P}\p{S}])/gu;
const RE_BLOCK_SKIP = /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)|(?<!`)()(?<b>`+)[^`]+\k<b>(?!`)|<(?! )[^<>]*?>/g;
function maskInlineSource(text) {
  let t = text.replace(RE_ANY_PUNCT_OUTSIDE_CODE, (n, s, r) => {
    if (r) return '+'.repeat(n.length);
    if (s) return s + n.slice(s.length, -s.length).replace(/`/g, '+') + s;
    return n;
  });
  t = t.replace(RE_BLOCK_SKIP, (n) => '[' + 'a'.repeat(Math.max(0, n.length - 2)) + ']');
  return t;
}
// Validate the backtick runs in a link label (text.slice(start, end),
// end = index of the closing ]). Mirrors marked's label regex `re`:
// a backtick run is allowed only when it is part of a complete
// `...` code span (a later backtick run with non-backtick content
// between; the two runs need not have the same length) or when it is
// a run of 2+ backticks immediately before the closing ]. A lone
// single backtick makes the label invalid, so no link forms and the
// code span may instead pair across the ].
function labelBackticksValid(s, start, end) {
  let i = start;
  while (i < end) {
    const c = s.charCodeAt(i);
    if (c === CC_BACKSLASH) { i += 2; continue; }
    if (c === CC_BACKTICK) {
      let j = i;
      while (j < end && s.charCodeAt(j) === CC_BACKTICK) j++;
      const runLen = j - i;
      // a later backtick run with non-backtick content between?
      let p = j;
      while (p < end && s.charCodeAt(p) !== CC_BACKTICK) p++;
      if (p < end && p > j) {
        let e = p;
        while (e < end && s.charCodeAt(e) === CC_BACKTICK) e++;
        i = e;
        continue;
      }
      // no closer: valid only as 2+ backticks right before the ]
      if (runLen >= 2 && j === end) { i = j; continue; }
      return false;
    }
    i++;
  }
  return true;
}

function parseLinkLabel(s, i) {
  if (s.charCodeAt(i) !== CC_LBRACK) return null;
  let j = i + 1;
  let len = 0;
  while (j < s.length) {
    const c = s.charCodeAt(j);
    if (c === CC_BACKSLASH && j + 1 < s.length && isAsciiPunct(s.charCodeAt(j + 1))) { j += 2; len += 2; continue; }
    if (c === CC_LBRACK) return null; // unescaped [ is not allowed
    if (c === CC_RBRACK) {
      if (len === 0 || len > 999) return null;
      return { label: s.slice(i + 1, j), end: j + 1 };
    }
    j++; len++;
    if (len > 999) return null;
  }
  return null;
}

// Skip spaces, tabs and newlines (but not across a blank line) from `i`.
// Returns the new index, or -1 if a blank line is crossed.
function skipLinkWhitespace(s, i) {
  let j = i;
  let newlines = 0;
  while (j < s.length) {
    const c = s.charCodeAt(j);
    if (c === CC_SPACE || c === CC_TAB) { j++; continue; }
    if (c === CC_NL) {
      newlines++;
      if (newlines > 1) return -1;
      j++;
      continue;
    }
    break;
  }
  return j;
}

// Parse a link destination at s[i]. Returns {dest, end} or null.
// <...> form: no unescaped < or newline inside; bare form: no spaces or
// control characters, balanced parens allowed, backslash escapes kept.
function parseLinkDestination(s, i) {
  if (i >= s.length) return null;
  if (s.charCodeAt(i) === CC_LT) {
    let j = i + 1;
    while (j < s.length) {
      const c = s.charCodeAt(j);
      if (c === CC_LT || c === CC_NL) return null;
      if (c === CC_BACKSLASH && j + 1 < s.length && isAsciiPunct(s.charCodeAt(j + 1))) { j += 2; continue; }
      if (c === CC_GT) return { dest: s.slice(i + 1, j), end: j + 1 };
      j++;
    }
    return null;
  }
  let depth = 0;
  let j = i;
  while (j < s.length) {
    const c = s.charCodeAt(j);
    if (c === CC_SPACE || c === CC_TAB || c === CC_NL || c < 32) break;
    if (c === CC_BACKSLASH && j + 1 < s.length && isAsciiPunct(s.charCodeAt(j + 1))) { j += 2; continue; }
    if (c === CC_LPAREN) { depth++; j++; continue; }
    if (c === CC_RPAREN) {
      if (depth === 0) break;
      depth--; j++; continue;
    }
    j++;
  }
  if (j === i) return null;
  return { dest: s.slice(i, j), end: j };
}

// Parse a link title at s[i]. Returns {title, end} or null. Titles may be
// "..." or '...' or (...), may span lines but not blank lines.
function parseLinkTitle(s, i) {
  if (i >= s.length) return null;
  const c = s.charCodeAt(i);
  let close;
  if (c === CC_QUOT) close = CC_QUOT;
  else if (c === CC_APOS) close = CC_APOS;
  else if (c === CC_LPAREN) close = CC_RPAREN;
  else return null;
  let j = i + 1;
  while (j < s.length) {
    const ch = s.charCodeAt(j);
    if (ch === CC_NL) {
      // a blank line ends the title: the next line must have content
      let k = j + 1;
      while (k < s.length && (s.charCodeAt(k) === CC_SPACE || s.charCodeAt(k) === CC_TAB)) k++;
      if (k >= s.length || s.charCodeAt(k) === CC_NL) return null;
      j++;
      continue;
    }
    if (ch === CC_BACKSLASH && j + 1 < s.length && isAsciiPunct(s.charCodeAt(j + 1))) { j += 2; continue; }
    if (close === CC_RPAREN && ch === CC_LPAREN) return null; // no ( inside (title)
    if (ch === close) return { title: s.slice(i + 1, j), end: j + 1 };
    j++;
  }
  return null;
}

// Try to parse link reference definitions from the start of `text` (a
// paragraph's joined lines). Returns {defs: [[label, dest, title]...],
// rest: string} where rest is the paragraph text after the definitions
// ('' when the paragraph was only definitions). When `collect` is given,
// definitions are added to it (label -> {dest, title}); the first
// definition of a label wins.
function stripLinkDefinitions(text, collect) {
  let i = 0;
  const defs = [];
  for (;;) {
    // up to 3 spaces of indent
    let j = i;
    let sp = 0;
    while (j < text.length && text.charCodeAt(j) === CC_SPACE && sp < 3) { j++; sp++; }
    if (j >= text.length || text.charCodeAt(j) !== CC_LBRACK) break;
    const lab = parseLinkLabel(text, j);
    if (!lab) break;
    let k = lab.end;
    if (text.charCodeAt(k) !== CC_COLON) break;
    k++;
    // optional whitespace (may span one line, not a blank line)
    k = skipLinkWhitespace(text, k);
    if (k < 0) break;
    const dest = parseLinkDestination(text, k);
    if (!dest) break;
    k = dest.end;
    // A title must be separated from the destination by whitespace. It
    // may sit on the same line, or on the next line when the destination
    // is alone on its line. After the title (or destination) only
    // whitespace may follow to the end of that line; a bad title on the
    // next line leaves a title-less definition behind.
    let title = '';
    let k3;
    // spaces/tabs on the destination's line
    let k2 = k;
    while (k2 < text.length && (text.charCodeAt(k2) === CC_SPACE || text.charCodeAt(k2) === CC_TAB)) k2++;
    const cc = k2 < text.length ? text.charCodeAt(k2) : -1;
    if (cc === CC_QUOT || cc === CC_APOS || cc === CC_LPAREN) {
      // title on the same line -- needs whitespace before it
      if (k2 === k) break;
      const t = parseLinkTitle(text, k2);
      if (!t) break;
      title = t.title;
      k3 = t.end;
      while (k3 < text.length && (text.charCodeAt(k3) === CC_SPACE || text.charCodeAt(k3) === CC_TAB)) k3++;
      if (k3 < text.length && text.charCodeAt(k3) !== CC_NL) break;
    } else if (cc === CC_NL || k2 >= text.length) {
      // destination alone on its line: a title may follow on the next line
      let k5 = cc === CC_NL ? k2 + 1 : k2;
      while (k5 < text.length && (text.charCodeAt(k5) === CC_SPACE || text.charCodeAt(k5) === CC_TAB)) k5++;
      const c5 = k5 < text.length ? text.charCodeAt(k5) : -1;
      if (c5 === CC_QUOT || c5 === CC_APOS || c5 === CC_LPAREN) {
        const t = parseLinkTitle(text, k5);
        if (t) {
          let k6 = t.end;
          while (k6 < text.length && (text.charCodeAt(k6) === CC_SPACE || text.charCodeAt(k6) === CC_TAB)) k6++;
          if (k6 >= text.length || text.charCodeAt(k6) === CC_NL) {
            title = t.title;
            k3 = k6;
          } else {
            k3 = k2; // bad title on the next line: no title at all
          }
        } else {
          k3 = k2;
        }
      } else {
        k3 = k2;
      }
    } else {
      break; // trailing content after the destination
    }
    // a definition! consume through the end of this line -- but only when
    // the label is non-empty after normalization (a whitespace-only label
    // is not a definition at all)
    const norm = normalizeLabel(lab.label);
    if (norm.length === 0) break;
    defs.push([norm, unescapeBackslashes(dest.dest), unescapeBackslashes(title)]);
    if (collect && !collect.has(norm)) {
      collect.set(norm, { dest: unescapeBackslashes(dest.dest), title: unescapeBackslashes(title) });
    }
    i = k3 < text.length ? k3 + 1 : k3;
    if (i >= text.length) { i = text.length; break; }
  }
  return { defs, rest: text.slice(i) };
}

// ---- block parsing --------------------------------------------------------
// A line-oriented CommonMark block parser. Containers (blockquote, list,
// item) are kept open on a stack; leaves (paragraph, heading, code, html,
// table) consume lines until they close. Link reference definitions are
// stripped from paragraphs when they close (or when a paragraph turns into
// a setext heading or a table).

const HTML_BLOCK_TAGS = new Set([
  'address', 'article', 'aside', 'base', 'basefont', 'blockquote', 'body',
  'caption', 'center', 'col', 'colgroup', 'dd', 'details', 'dialog', 'dir',
  'div', 'dl', 'dt', 'fieldset', 'figcaption', 'figure', 'footer', 'form',
  'frame', 'frameset', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'head', 'header',
  'hr', 'html', 'iframe', 'legend', 'li', 'link', 'main', 'menu', 'menuitem',
  'nav', 'noframes', 'ol', 'optgroup', 'option', 'p', 'param', 'search',
  'section', 'summary', 'table', 'tbody', 'td', 'tfoot', 'th', 'thead',
  'title', 'tr', 'track', 'ul',
]);

function isContainer(b) {
  return b.t === 'doc' || b.t === 'quote' || b.t === 'list' || b.t === 'item';
}

// Is `s` (already de-indented to <=3 spaces) an HTML block start? Returns
// the block type (1-7) or 0.
function htmlBlockType(s) {
  if (s.charCodeAt(0) !== CC_LT) return 0;
  const c1 = s.charCodeAt(1);
  if (c1 === 33) { // !
    if (s[2] === '-' && s[3] === '-') return 2;
    if (s.slice(2, 9).toUpperCase() === '[CDATA[') return 5;
    if (s.length > 2 && ((s.charCodeAt(2) >= 65 && s.charCodeAt(2) <= 90) || (s.charCodeAt(2) >= 97 && s.charCodeAt(2) <= 122))) return 4;
    return 0;
  }
  if (c1 === 63) return 3; // ?
  if (c1 === 47) { // / close tag
    let j = 2;
    while (j < s.length && isAlnum(s.charCodeAt(j))) j++;
    if (j === 2) return 0;
    const name = s.slice(2, j).toLowerCase();
    const after = s.charCodeAt(j);
    if (after !== CC_SPACE && after !== CC_TAB && after !== CC_GT && j !== s.length) return 0;
    if (HTML_BLOCK_TAGS.has(name)) return 6;
    // type 7: a complete closing tag followed only by whitespace
    // (validated as a tag: no attributes on a closing tag)
    return isType7(s) ? 7 : 0;
  }
  // open tag
  if ((c1 >= 65 && c1 <= 90) || (c1 >= 97 && c1 <= 122)) {
    let j = 1;
    while (j < s.length && (isAlnum(s.charCodeAt(j)) || s.charCodeAt(j) === CC_DASH)) j++;
    const name = s.slice(1, j).toLowerCase();
    const after = s.charCodeAt(j);
    if (after !== CC_SPACE && after !== CC_TAB && after !== CC_GT && after !== CC_SLASH && j !== s.length) return 0;
    if (name === 'script' || name === 'pre' || name === 'style' || name === 'textarea') {
      // type 1 needs the tag name followed by space, tab, > or EOL
      if (after === CC_SPACE || after === CC_TAB || after === CC_GT || j === s.length) return 1;
      return 0;
    }
    if (HTML_BLOCK_TAGS.has(name)) return 6;
    // type 7: a complete open tag followed only by whitespace
    // (validated as a tag: attribute names and separation matter)
    return isType7(s) ? 7 : 0;
  }
  return 0;
}

// Is `s` a complete open/close tag followed only by whitespace? Used for
// HTML block type 7; parseHtmlTag validates the tag's attributes.
function isType7(s) {
  const tag = parseHtmlTag(s, 0);
  if (!tag) return false;
  // only a plain open or close tag counts (not a comment, PI, declaration)
  const c1 = tag.tag.charCodeAt(1);
  if (c1 === 33 || c1 === 63) return false;
  for (let k = tag.end; k < s.length; k++) {
    const cc = s.charCodeAt(k);
    if (cc !== CC_SPACE && cc !== CC_TAB) return false;
  }
  return true;
}

// Index just past the '>' that closes the HTML tag whose name ends at `j`
// (a '>' inside a quoted attribute value does not close the tag), or -1
// when the tag is not complete on this line.
function tagEnd(s, j) {
  while (j < s.length) {
    const c = s.charCodeAt(j);
    if (c === CC_QUOT || c === CC_APOS) {
      const q = c;
      j++;
      while (j < s.length && s.charCodeAt(j) !== q) j++;
      if (j >= s.length) return -1;
      j++;
      continue;
    }
    if (c === CC_GT) return j + 1;
    j++;
  }
  return -1;
}

// Does line `s` satisfy the end condition of HTML block type `ty`?
// (Checked against the raw line, case-insensitively.)
function htmlBlockEnds(ty, s) {
  const low = s.toLowerCase();
  switch (ty) {
    case 1: return low.indexOf('</script') >= 0 || low.indexOf('</pre') >= 0 || low.indexOf('</style') >= 0 || low.indexOf('</textarea') >= 0;
    case 2: return low.indexOf('-->') >= 0;
    case 3: return low.indexOf('?>') >= 0;
    case 4: return low.indexOf('>') >= 0;
    case 5: return low.indexOf(']]>') >= 0;
    default: return false; // 6 and 7 end at blank lines
  }
}

// Is `s` a thematic break (after <=3 spaces of indent)?
function isThematicBreak(s) {
  const c = s.charCodeAt(0);
  if (c !== CC_STAR && c !== CC_DASH && c !== CC_UNDER) return false;
  let n = 0;
  for (let i = 0; i < s.length; i++) {
    const ch = s.charCodeAt(i);
    if (ch === c) n++;
    else if (ch !== CC_SPACE && ch !== CC_TAB) return false;
  }
  return n >= 3;
}

// Is `s` a setext heading underline? Returns 1 for =, 2 for -, else 0.
function setextLevel(s) {
  // a setext underline is one run of = or - with only leading/trailing
  // whitespace (no internal spaces: "= =" and "--- -" are not underlines)
  let i = 0;
  while (i < s.length && (s.charCodeAt(i) === CC_SPACE || s.charCodeAt(i) === CC_TAB)) i++;
  if (i >= s.length) return 0;
  const c = s.charCodeAt(i);
  if (c !== CC_EQ && c !== CC_DASH) return 0;
  let n = 0;
  while (i < s.length && s.charCodeAt(i) === c) { i++; n++; }
  while (i < s.length && (s.charCodeAt(i) === CC_SPACE || s.charCodeAt(i) === CC_TAB)) i++;
  if (i !== s.length || n === 0) return 0;
  return c === CC_EQ ? 1 : 2;
}

// Parse an ATX heading at `s` (de-indented). Returns {level, text} or null.
function parseAtx(s) {
  if (s.charCodeAt(0) !== CC_HASH) return null;
  let n = 0;
  while (n < s.length && s.charCodeAt(n) === CC_HASH) n++;
  if (n > 6) return null;
  if (n < s.length && s.charCodeAt(n) !== CC_SPACE && s.charCodeAt(n) !== CC_TAB) return null;
  let text = s.slice(n);
  // strip leading/trailing spaces/tabs
  let a = 0;
  while (a < text.length && (text.charCodeAt(a) === CC_SPACE || text.charCodeAt(a) === CC_TAB)) a++;
  let b = text.length;
  while (b > a && (text.charCodeAt(b - 1) === CC_SPACE || text.charCodeAt(b - 1) === CC_TAB)) b--;
  // strip a closing sequence of #s preceded by space/tab (the whole
  // content may be just the closing sequence, leaving an empty heading)
  let c = b;
  while (c > a && text.charCodeAt(c - 1) === CC_HASH) c--;
  if (c < b && c > 0 && (text.charCodeAt(c - 1) === CC_SPACE || text.charCodeAt(c - 1) === CC_TAB)) {
    b = c;
    while (b > a && (text.charCodeAt(b - 1) === CC_SPACE || text.charCodeAt(b - 1) === CC_TAB)) b--;
  }
  return { level: n, text: text.slice(a, b) };
}

// Parse a fenced code start at `s` (de-indented). Returns
// {char, len, info} or null. Backtick fences: info must not contain `.
function parseFence(s) {
  const c = s.charCodeAt(0);
  if (c !== CC_BACKTICK && c !== CC_TILDE) return null;
  let n = 0;
  while (n < s.length && s.charCodeAt(n) === c) n++;
  if (n < 3) return null;
  const info = s.slice(n).trim();
  if (c === CC_BACKTICK && info.indexOf('`') >= 0) return null;
  return { char: c === CC_BACKTICK ? '`' : '~', len: n, info };
}

// Is `s` a closing fence for a block opened with `char`/`len`?
function isClosingFence(s, char, len) {
  if (s.charCodeAt(0) !== char.charCodeAt(0)) return false;
  let n = 0;
  while (n < s.length && s.charCodeAt(n) === char.charCodeAt(0)) n++;
  if (n < len) return false;
  for (let i = n; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c !== CC_SPACE && c !== CC_TAB) return false;
  }
  return true;
}

// Parse a list marker at `s` (de-indented, i.e. after <=3 spaces).
// `base` is the absolute column of s[0]. Returns
// {bullet, ordered, start, delim, markerLen, contentIndent} or null.
// contentIndent is relative columns from the marker start to the content.
function parseListMarker(s, base) {
  const c0 = s.charCodeAt(0);
  let markerLen, bullet, ordered, start = 0, delim = '';
  if (c0 === CC_DASH || c0 === CC_PLUS || c0 === CC_STAR) {
    bullet = true; ordered = false; markerLen = 1;
  } else if (isDigit(c0)) {
    let j = 0;
    while (j < s.length && isDigit(s.charCodeAt(j))) j++;
    if (j > 9) return null;
    const d = s.charCodeAt(j);
    if (d !== CC_DOT && d !== CC_RPAREN) return null;
    bullet = false; ordered = true; delim = d === CC_DOT ? '.' : ')';
    start = parseInt(s.slice(0, j), 10);
    markerLen = j + 1;
  } else return null;
  // whitespace after the marker (tabs expand from the marker's column,
  // which is `base` + markerLen in absolute columns)
  let col = (base || 0) + markerLen;
  let i = markerLen;
  let ws = 0;
  while (i < s.length) {
    const c = s.charCodeAt(i);
    if (c === CC_SPACE) { ws++; col++; i++; }
    else if (c === CC_TAB) { const nx = col + 4 - (col % 4); ws += nx - col; col = nx; i++; }
    else break;
  }
  if (ws === 0) {
    if (i >= s.length) {
      // empty item: content indent is marker + 1
      return { bullet, ordered, start, delim, markerLen, contentIndent: markerLen + 1, empty: true };
    }
    return null;
  }
  // an empty item (marker + spaces, then end of line) also has content
  // indent marker + 1, so a following indented line is its content
  if (i >= s.length) {
    return { bullet, ordered, start, delim, markerLen, contentIndent: markerLen + 1, empty: true };
  }
  const contentIndent = ws >= 5 ? markerLen + 1 : markerLen + ws;
  return { bullet, ordered, start, delim, markerLen, contentIndent, empty: false };
}

// Split a table row into cells, code-span and escape aware. `s` is the raw
// row line. Returns the cell strings (untrimmed).
function splitTableRow(s) {
  const cells = [];
  let cur = '';
  let i = 0;
  // strip one leading | and one trailing | (the row's edges)
  let a = 0;
  while (a < s.length && (s.charCodeAt(a) === CC_SPACE || s.charCodeAt(a) === CC_TAB)) a++;
  let b = s.length;
  while (b > a && (s.charCodeAt(b - 1) === CC_SPACE || s.charCodeAt(b - 1) === CC_TAB)) b--;
  if (s.charCodeAt(a) === CC_PIPE) a++;
  if (b > a && s.charCodeAt(b - 1) === CC_PIPE) b--;
  for (i = a; i < b; i++) {
    const c = s.charCodeAt(i);
    if (c === CC_BACKSLASH && i + 1 < b && s.charCodeAt(i + 1) === CC_PIPE) {
      // an escaped pipe is a literal pipe (the backslash is consumed
      // at the table level, so it also vanishes inside code spans)
      cur += '|';
      i++;
      continue;
    }
    // a pipe splits the row unless escaped; code spans do NOT protect
    // it (marked splits on every unescaped pipe, even inside backticks)
    if (c === CC_PIPE) {
      cells.push(cur);
      cur = '';
      continue;
    }
    cur += s[i];
  }
  cells.push(cur);
  return cells;
}

// Is `line` a valid table delimiter row for a header with `headerCells`
// cells? Returns the alignments array ('' | 'left' | 'center' | 'right')
// or null.
function tableAlignments(headerCells, line) {
  const cells = splitTableRow(line);
  if (cells.length !== headerCells.length) return null;
  const aligns = [];
  for (const cell of cells) {
    const t = cell.trim();
    if (!/^:?-+:?$/.test(t)) return null;
    if (t[0] === ':' && t[t.length - 1] === ':') aligns.push('center');
    else if (t[t.length - 1] === ':') aligns.push('right');
    else if (t[0] === ':') aligns.push('left');
    else aligns.push('');
  }
  return aligns;
}

// The block parser: returns {root, refs}.
function parseBlocks(src) {
  // a trailing newline leaves an empty string after the last split; it is
  // not a line (a real blank line still shows up as an earlier element)
  const srcEndsWithNl = src.length > 0 && src.charCodeAt(src.length - 1) === 10;
  const lines = src.split('\n');
  if (lines.length > 1 && lines[lines.length - 1] === '') lines.pop();
  const refs = new Map();
  const root = { t: 'doc', children: [], parent: null };
  const stack = [root];
  let blankPending = false;
  let blankScope = null;
  // a type 1-5 HTML block that closes by its end condition: whether the
  // following line is blank is decided when that line is processed (its
  // container markers must be matched first -- a ">" line is blank for
  // the quote's content but the raw line is not empty)
  let pendingHtmlBlank = null;

  const tip = () => stack[stack.length - 1];
  const parentContainer = () => {
    for (let i = stack.length - 1; i >= 0; i--) {
      if (isContainer(stack[i])) return stack[i];
    }
    return root;
  };
  const addChild = (b) => {
    let p = parentContainer();
    // a list can only hold items; if the parent is a list it is left over
    // from a closed item -- close it so the block lands in the list's
    // parent instead (items are added to lists directly, never here)
    if (p.t === 'list') {
      closeBlocks(stack.indexOf(p));
      p = parentContainer();
    }
    b.parent = p;
    p.children.push(b);
    return b;
  };
  const openBlock = (b) => {
    addChild(b);
    stack.push(b);
    return b;
  };

  // Finalize a block being closed. Returns false when the block should be
  // dropped from its parent (an empty paragraph).
  function finalize(b) {
    if (b.t === 'para') {
      const text = b.lines.join('\n');
      const stripped = stripLinkDefinitions(text, refs);
      if (stripped.rest.length === 0) return false;
      b.text = stripped.rest;
      return true;
    }
    if (b.t === 'code') {
      if (b.fenced) {
        // exactly one trailing blank line is dropped (the one before the
        // closing fence); blank lines inside the fence are kept
        if (b.lines.length > 0 && b.lines[b.lines.length - 1] === '') b.lines.pop();
      } else {
        while (b.lines.length > 0 && b.lines[b.lines.length - 1] === '') b.lines.pop();
      }
    }
    return true;
  }
  function closeBlocks(from, eof) {
    for (let i = stack.length - 1; i >= from; i--) {
      const b = stack[i];
      // an HTML block whose container ends mid-parse (a new list item, a
      // closing quote) renders without a trailing newline; at EOF it keeps
      // one -- unless the source itself has no trailing newline. Type 1-5
      // blocks keep theirs unless a blank line follows (handled where
      // they close by their end condition).
      if (!eof && b.t === 'html' && (b.htype === 6 || b.htype === 7)) b.endedAtBlank = true;
      if (eof && b.t === 'html' && !srcEndsWithNl) b.noTrailingNl = true;
      if (!finalize(b)) {
        const p = b.parent;
        const idx = p.children.indexOf(b);
        if (idx >= 0) p.children.splice(idx, 1);
      }
    }
    stack.length = from;
  }
  function closeLeaf() {
    if (stack.length > 1 && !isContainer(tip())) closeBlocks(stack.length - 1);
  }

  // Looseness: called when a new block is created in phase 2.
  function noteBlockStart(block) {
    if (!blankPending) return;
    if (block.t === 'item') {
      const list = block.parent;
      // the blank line loosens the list when it falls inside the list
      // itself or inside any item of the list (even nested in a sublist
      // within that item, e.g. after the last nested item). The walk
      // only crosses list/item nodes: a blank line inside a blockquote
      // does not loosen the enclosing list.
      if (list.children.length > 1) {
        let s = blankScope;
        while (s && (s.t === 'list' || s.t === 'item')) {
          if (s === list || (s.t === 'item' && s.parent === list)) { list.tight = false; break; }
          s = s.parent;
        }
      }
      return;
    }
    // any other block: find the nearest enclosing item (the block itself
    // is already among its children, so > 1 means it had one before).
    // The blank line loosens the list when it falls inside that item,
    // even inside a nested list within it.
    let p = block.parent;
    while (p && p.t !== 'item' && p.t !== 'doc') p = p.parent;
    if (p && p.t === 'item' && p.children.length > 1) {
      let s = blankScope;
      while (s && s !== p) s = s.parent;
      if (s === p) p.parent.tight = false;
    }
  }

  // Match open containers against `line`. Returns {rest, lazy} where rest is
  // the line's remainder after the matched containers (with a partially
  // consumed tab replaced by spaces). `lazy` means the line continues an
  // open paragraph without its container markers.
  function matchContainers(line) {
    let idx = 0;
    let col = 0;
    let sp = 0; // virtual spaces from a partially consumed tab
    // stack[0] is root; containers are stack[1..k] while they are containers
    let k = 1;
    while (k < stack.length && isContainer(stack[k])) {
      const c = stack[k];
      if (c.t === 'quote') {
        // skip up to 3 columns of spaces, then '>', then one optional space
        let i2 = idx, c2 = col;
        while (i2 < line.length && c2 - col < 3) {
          const ch = line.charCodeAt(i2);
          if (ch === CC_SPACE) { i2++; c2++; }
          else if (ch === CC_TAB) {
            const nx = c2 + 4 - (c2 % 4);
            if (nx - col > 3) break;
            i2++; c2 = nx;
          } else break;
        }
        if (i2 >= line.length || line.charCodeAt(i2) !== CC_GT) break;
        i2++; c2++;
        // the whitespace run after '>' is expanded with J semantics:
        // tab stops count from the marker length (not the absolute
        // column), so a tab after "> " in a nested quote expands the
        // same as in a single quote. The marker consumes one column
        // of the expanded run; the rest is virtual content indent.
        const markerLen = c2 - col;
        let j = i2, t = markerLen, exp = 0;
        while (j < line.length) {
          const ch = line.charCodeAt(j);
          if (ch === CC_SPACE) { exp++; t++; j++; }
          else if (ch === CC_TAB) { const r = 4 - (t % 4); exp += r; t += r; j++; }
          else break;
        }
        if (j > i2) {
          sp = Math.max(0, exp - 1);
          let c3 = c2;
          for (let q = i2; q < j; q++) {
            if (line.charCodeAt(q) === CC_SPACE) c3++;
            else c3 += 4 - (c3 % 4);
          }
          idx = j; col = c3;
        } else {
          idx = i2; col = c2;
          sp = 0;
        }
        k++;
        continue;
      }
      if (c.t === 'item') {
        // blank remainder matches the item
        let j = idx;
        let blank = true;
        while (j < line.length) {
          const ch = line.charCodeAt(j);
          if (ch !== CC_SPACE && ch !== CC_TAB) { blank = false; break; }
          j++;
        }
        if (blank) { k++; continue; }
        // measure leading whitespace columns from idx, including any
        // virtual spaces left by a partially consumed tab in an outer
        // container (they occupy columns col-sp .. col-1)
        let i2 = idx, c2 = col - sp, w = sp;
        while (i2 < line.length) {
          const ch = line.charCodeAt(i2);
          if (ch === CC_SPACE) { i2++; c2++; w++; }
          else if (ch === CC_TAB) { const nx = c2 + 4 - (c2 % 4); i2++; w += nx - c2; c2 = nx; }
          else break;
        }
        if (w < c.contentIndent) break;
        // consume exactly contentIndent columns (partial tab -> spaces),
        // counting the virtual spaces from an outer container first
        const inSp = sp;
        let need = c.contentIndent;
        let i3 = idx, c3 = col;
        sp = 0;
        if (inSp >= need) {
          // the whole indent is covered by virtual spaces
          sp = inSp - need;
          need = 0;
        } else {
          need -= inSp;
          while (need > 0 && i3 < line.length) {
            const ch = line.charCodeAt(i3);
            if (ch === CC_SPACE) { i3++; c3++; need--; }
            else if (ch === CC_TAB) {
              const nx = c3 + 4 - (c3 % 4);
              const w2 = nx - c3;
              if (w2 <= need) { i3++; c3 = nx; need -= w2; }
              else { sp = w2 - need; i3++; c3 = nx; need = 0; }
            } else break;
          }
        }
        idx = i3; col = c3;
        k++;
        continue;
      }
      // list: transparent
      k++;
    }
    const matched = k; // containers stack[1..matched-1] matched
    const rest = ' '.repeat(sp) + line.slice(idx);
    // absolute column of rest[0]: the virtual spaces fill the remainder of
    // a partially consumed tab that ends at column `col`
    const base = col - sp;
    if (matched < stack.length && isContainer(stack[matched])) {
      // a container failed to match
      const t = tip();
      // a fenced code block keeps consuming lines when the failed
      // container is a list item -- but only when the line is indented
      // enough to belong to the block: marked drops a code line that is
      // below the item's content indent unless the fence itself is
      // outdented (fence indent < content indent), in which case the
      // line must be at least fence-1. A missing ">" ends a blockquote
      // and the code block inside it.
      if (t && t.t === 'code' && t.fenced && stack[matched].t !== 'quote') {
        // absolute indent of this line's first non-ws char
        let li = 0;
        for (let q = 0; q < line.length; q++) {
          const cq = line.charCodeAt(q);
          if (cq === CC_SPACE) li++;
          else if (cq === CC_TAB) li += 4 - (li % 4);
          else break;
        }
        // nearest item ancestor of the code block
        let ci = -1;
        for (let p = t.parent; p; p = p.parent) {
          if (p.t === 'item') { ci = p.contentIndent; break; }
          if (p.t === 'doc') break;
        }
        // a line that starts a new list item at an outer level ends
        // the code block instead: the item belongs to the outer list,
        // not to the code block's item
        const dm = deindent3(rest, base);
        if (parseListMarker(dm.s, dm.base) !== null) {
          // fall through to closeBlocks below
        } else if (ci < 0 || t.lines.length > 0 || li >= ci || (t.fenceAbs < ci && li >= t.fenceAbs - 1)) return { rest, lazy: false, base };
      }
      if (t && t.t === 'para' && rest.trim() !== '') {
        // lazy continuation -- unless the line starts a block that can
        // interrupt a paragraph (heading, fence, HTML 1-6, hr, quote,
        // or a list item); then the paragraph closes instead. Here a
        // container has failed to match, so the paragraph's container is
        // being closed and ANY list marker starts a new list at the
        // outer level (the start-at-1 rule only limits interrupting an
        // open paragraph from inside its own container).
        const d = deindent3(rest, base);
        const s = d.s;
        const interrupts = parseAtx(s) !== null ||
          parseFence(s) !== null ||
          (htmlBlockType(s) > 0 && htmlBlockType(s) !== 7) ||
          isThematicBreak(s) ||
          s.charCodeAt(0) === CC_GT ||
          parseListMarker(s, d.base) !== null;
        if (!interrupts) return { rest, lazy: true, base };
      }
      closeBlocks(matched);
      return { rest, lazy: false, base };
    }
    return { rest, lazy: false, base };
  }

  // The remainder after up to 3 columns of leading whitespace (for block
  // start detection). `base` is the absolute column of s[0]. Returns
  // {s, indent, base} where s is the de-indented string and base is the
  // absolute column of s[0].
  function deindent3(s, base) {
    let i = 0;
    let col = base || 0;
    while (i < s.length && col - (base || 0) < 3) {
      const c = s.charCodeAt(i);
      if (c === CC_SPACE) { i++; col++; }
      else if (c === CC_TAB) {
        const nx = col + 4 - (col % 4);
        if (nx - (base || 0) > 3) break;
        i++; col = nx;
      } else break;
    }
    return { s: s.slice(i), indent: col - (base || 0), base: col };
  }

  // Try to convert an open paragraph with an incoming setext/table line.
  // `rest` is the incoming line (de-indented). Returns true when the line
  // was consumed by the conversion.
  function trySetextOrTable(para, rest) {
    const raw = para.lines.join('\n');
    const stripped = stripLinkDefinitions(raw, null);
    const remaining = stripped.rest;
    const remLines = remaining.length === 0 ? [] : remaining.split('\n');
    const lvl = setextLevel(rest);
    if (lvl > 0 && remLines.length >= 1) {
      // setext heading from the remaining lines; the heading text is the
      // paragraph text with leading/trailing whitespace stripped
      const idx = stack.indexOf(para);
      closeBlocks(idx);
      // drop the paragraph from its parent; the heading replaces it
      const pp = para.parent;
      const pi = pp.children.indexOf(para);
      if (pi >= 0) pp.children.splice(pi, 1);
      const h = { t: 'heading', level: lvl, text: remaining.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '') };
      addChild(h);
      // register the definitions that were stripped
      stripLinkDefinitions(raw, refs);
      return true;
    }
    if (remLines.length === 1) {
      const headerCells = splitTableRow(remLines[0]);
      const aligns = tableAlignments(headerCells, rest);
      if (aligns) {
        const idx = stack.indexOf(para);
        closeBlocks(idx);
        // drop the paragraph from its parent; the table replaces it
        const pp = para.parent;
        const pi = pp.children.indexOf(para);
        if (pi >= 0) pp.children.splice(pi, 1);
        const tb = { t: 'table', aligns, header: remLines[0], rows: [] };
        addChild(tb);
        stack.push(tb);
        stripLinkDefinitions(raw, refs);
        return true;
      }
    }
    return false;
  }

  // Phase 2: open blocks from `rest` (the line remainder). `canInterrupt`
  // is false while a paragraph is open (indented code and type-7 HTML
  // cannot interrupt). `base` is the absolute column of rest[0].
  // Returns true when the line is fully consumed.
  function phase2(rest, canInterrupt, base, ln) {
    base = base || 0;
    for (;;) {
      const d = deindent3(rest, base);
      const s = d.s;
      if (s === '') return true; // blank (should not normally reach here)
      // blockquote
      if (s.charCodeAt(0) === CC_GT) {
        let i = 1;
        let nb = d.base + 1;
        if (i < s.length && s.charCodeAt(i) === CC_SPACE) { i++; nb++; }
        else if (i < s.length && s.charCodeAt(i) === CC_TAB) {
          // only one column of the tab is consumed; the rest stays as spaces
          const w = 4 - (nb % 4);
          rest = ' '.repeat(w - 1) + s.slice(i + 1);
          base = nb + 1;
          const q = { t: 'quote', children: [] };
          openBlock(q);
          noteBlockStart(q);
          continue;
        }
        const q = { t: 'quote', children: [] };
        openBlock(q);
        noteBlockStart(q);
        rest = s.slice(i);
        base = nb;
        continue;
      }
      // thematic break (before list: "* * *" is an hr, not a list item)
      if (isThematicBreak(s)) {
        addChild({ t: 'hr' });
        return true;
      }
      // list item
      const lm = parseListMarker(s, d.base);
      if (lm) {
        const markerMatches = (l) => (lm.bullet && l.bullet && l.marker === s[0]) ||
          (lm.ordered && l.ordered && l.delim === lm.delim);
        let list = null;
        // a list continues across blank lines (going loose); only the
        // marker type decides whether the item joins the previous list
        const pc = parentContainer();
        if (pc.t === 'list') {
          // the innermost container is itself a list (its last item was
          // just closed); the item joins it when the marker matches,
          // otherwise the list is closed so the new one is a sibling
          if (markerMatches(pc)) list = pc;
          else closeBlocks(stack.indexOf(pc));
        }
        if (!list) {
          const p2 = parentContainer();
          const prev = p2.children;
          const last = prev.length > 0 ? prev[prev.length - 1] : null;
          if (last && last.t === 'list' && markerMatches(last)) list = last;
        }
        // a list item can interrupt a paragraph; an ordered list only when
        // it starts at 1 (checked by the caller via canInterrupt for the
        // paragraph case -- handled in the leaf section)
        if (!list) {
          list = { t: 'list', bullet: lm.bullet, ordered: lm.ordered, start: lm.start, delim: lm.delim, marker: lm.bullet ? s[0] : '', tight: true, children: [] };
          openBlock(list);
          noteBlockStart(list);
        }
        // contentIndent is stored in `rest` coordinates (columns from the
        // line remainder) so matchContainers can measure against it
        const item = { t: 'item', children: [], contentIndent: d.indent + lm.contentIndent };
        // the item is a child of the list; push it and make it the tip
        item.parent = list;
        list.children.push(item);
        stack.push(item);
        noteBlockStart(item);
        // content starts after the marker + whitespace (contentIndent
        // columns from the marker start, in `s` coordinates)
        rest = sliceFromColumnAt(s, lm.markerLen, d.base + lm.markerLen, d.base + lm.contentIndent);
        base = d.base + lm.contentIndent;
        if (rest === '') {
          // empty item: nothing more on this line
          return true;
        }
        continue;
      }
      // ATX heading
      const atx = parseAtx(s);
      if (atx) {
        addChild({ t: 'heading', level: atx.level, text: atx.text });
        return true;
      }
      // fenced code
      const fence = parseFence(s);
      if (fence) {
        const code = { t: 'code', fenced: true, fenceChar: fence.char, fenceLen: fence.len, fenceIndent: d.indent, fenceAbs: base + d.indent, info: fence.info, lines: [] };
        openBlock(code);
        noteBlockStart(code);
        return true;
      }
      // HTML block
      const ht = htmlBlockType(s);
      if (ht > 0 && (canInterrupt || ht !== 7)) {
        const hb = { t: 'html', lines: [rest], htype: ht };
        openBlock(hb);
        noteBlockStart(hb);
        if (ht < 6 && htmlBlockEnds(ht, rest)) {
          // whether the following line is blank is decided when it is
          // processed (container markers must be matched first)
          pendingHtmlBlank = hb;
          closeBlocks(stack.length - 1);
        }
        return true;
      }
      // indented code (cannot interrupt a paragraph)
      if (canInterrupt) {
        const lw = leadingWhitespace(rest, base);
        if (lw.col >= base + 4) {
          const code = { t: 'code', fenced: false, lines: [sliceFromColumn(rest, base + 4, base)] };
          openBlock(code);
          noteBlockStart(code);
          return true;
        }
      }
      // paragraph
      const p = { t: 'para', lines: [rest] };
      openBlock(p);
      noteBlockStart(p);
      return true;
    }
  }

  for (let ln = 0; ln < lines.length; ln++) {
    const line = lines[ln];
    const m = matchContainers(line);
    if (m.lazy) {
      const t = tip();
      // a lazy continuation (no container markers on the line) loses
      // 4 columns of leading whitespace when it has 4+ -- the
      // indented code indent -- in any container, quote or item
      // (cm-238: "> foo\n    - bar" -> "- bar")
      let content = stripParaIndent(m.rest, m.base, true);
      // a lazy setext underline inside a blockquote is indented by 4
      // spaces (marked's blockquote tokenizer does this so the line is not
      // re-parsed as a heading when the quote content is re-lexed)
      if (t.t === 'para' && setextLevel(m.rest) > 0) {
        let anc = t.parent;
        while (anc) {
          if (anc.t === 'quote') { content = '    ' + m.rest; break; }
          anc = anc.parent;
        }
      }
      t.lines.push(content);
      blankPending = false;
      blankScope = null;
      continue;
    }
    const rest = m.rest;
    const base = m.base || 0;
    const leaf = stack.length > 1 && !isContainer(tip()) ? tip() : null;

    // blank line? A whitespace-only remainder inside a blockquote (a
    // ">" marker was consumed, leaving spaces) is paragraph content,
    // not a blank line -- ">  " continues the paragraph with " " while
    // a top-level "   " or a bare-spaces line in a list item ends it.
    if (rest.trim() === '') {
      if (leaf && leaf.t === 'para' && rest !== '') {
        let anc = leaf.parent;
        let inQuote = false;
        while (anc) {
          if (anc.t === 'quote') { inQuote = true; break; }
          anc = anc.parent;
        }
        if (inQuote) {
          leaf.lines.push(stripParaIndent(rest, base, hasItemAncestor(leaf)));
          blankPending = false;
          blankScope = null;
          continue;
        }
      }
      // a truly blank line after a type 1-5 HTML block that closed by
      // its end condition: the block renders without a trailing newline
      // (only a truly empty remainder counts -- a spaces/tabs-only line
      // does not, per fix 66)
      if (pendingHtmlBlank) { if (rest === '') pendingHtmlBlank.endedAtBlank = true; pendingHtmlBlank = null; }
      if (leaf) {
        if (leaf.t === 'code') {
          // a whitespace-only line keeps its spaces minus the code
          // indent (fenced: the fence indent; indented: 4 columns)
          // a tilde fence strips no indent from its lines (marked
          // quirk) but still expands a leading tab inside a container;
          // a backtick fence strips the fence indent
          if (leaf.fenced) { leaf.lines.push(leaf.fenceChar === '~' ? sliceFromColumn(rest, base, base) : (base === 0 ? stripFenceIndent(rest, leaf.fenceIndent) : sliceFromColumn(rest, base + leaf.fenceIndent, base))); continue; }
          leaf.lines.push(sliceFromColumn(rest, base + 4, base));
          continue;
        }
        if (leaf.t === 'html') {
          if (leaf.htype === 7 || leaf.htype === 6) {
            // an HTML block that ends at a blank line renders without a
            // trailing newline -- except inside a list item, where the
            // blank line is a separator and the item text keeps the \n
            if (!leaf.parent || leaf.parent.t !== 'item') leaf.endedAtBlank = true;
            closeLeaf();
          }
          else { leaf.lines.push(''); continue; }
        }
        if (leaf.t === 'para') { closeLeaf(); }
        else if (leaf.t === 'table') {
          // a line that is exactly one tab inside a table is a row of
          // empty cells (marked quirk); any other whitespace-only line
          // (spaces, two tabs, empty) ends the table
          if (rest === '\t') { leaf.rows.push(rest); continue; }
          closeLeaf();
        }
      }
      // an empty list item followed by a blank line is closed: a later
      // indented line is a separate paragraph, not the item's content
      if (stack.length > 1 && tip().t === 'item' && tip().children.length === 0) {
        closeBlocks(stack.length - 1);
      }
      if (!blankPending) {
        blankPending = true;
        blankScope = parentContainer();
      }
      continue;
    }
    // blankPending stays set until a new block is created in phase 2, so
    // noteBlockStart can loosen the enclosing list; it is cleared after
    // phase 2 below

    // a non-blank line: the pending HTML block did not end at a blank
    pendingHtmlBlank = null;

    // leaves that consume the line
    if (leaf) {
      if (leaf.t === 'code' && leaf.fenced) {
        const d = deindent3(rest, base);
        if (isClosingFence(d.s, leaf.fenceChar, leaf.fenceLen)) { closeLeaf(); continue; }
        // a tilde fence strips no indent from its lines (marked
        // quirk) but still expands a leading tab inside a container;
        // a backtick fence strips the fence indent
        leaf.lines.push(leaf.fenceChar === '~' ? sliceFromColumn(rest, base, base) : (base === 0 ? stripFenceIndent(rest, leaf.fenceIndent) : sliceFromColumn(rest, base + leaf.fenceIndent, base)));
        continue;
      }
      if (leaf.t === 'code' && !leaf.fenced) {
        const lw = leadingWhitespace(rest, base);
        if (lw.col >= base + 4) { leaf.lines.push(sliceFromColumn(rest, base + 4, base)); continue; }
        closeLeaf();
        // fall through to phase 2
      } else if (leaf.t === 'html') {
        leaf.lines.push(rest);
        if (leaf.htype < 6 && htmlBlockEnds(leaf.htype, rest)) {
          // whether the following line is blank is decided when it is
          // processed (container markers must be matched first)
          pendingHtmlBlank = leaf;
          closeLeaf();
        }
        continue;
      } else if (leaf.t === 'table') {
        // a table row, unless the line starts another block
        const d = deindent3(rest, base);
        const s = d.s;
        const startsBlock = s.charCodeAt(0) === CC_HASH && parseAtx(s) ||
          parseFence(s) !== null ||
          (htmlBlockType(s) > 0 && htmlBlockType(s) !== 7) ||
          isThematicBreak(s) ||
          s.charCodeAt(0) === CC_GT ||
          parseListMarker(s, d.base) !== null;
        if (startsBlock) {
          closeLeaf();
          // fall through to phase 2
        } else {
          leaf.rows.push(rest);
          continue;
        }
      } else if (leaf.t === 'para') {
        const d = deindent3(rest, base);
        // setext heading or table? Only when the line looks like an
        // underline (all = or -) or a delimiter row (only - : | and space),
        // and only at <=3 spaces of indent (a 4-space indent is a plain
        // continuation line, not an underline -- deindent3 leaves a
        // leading space behind when the indent was 4+)
        const indented4 = d.s.length > 0 && (d.s.charCodeAt(0) === CC_SPACE || d.s.charCodeAt(0) === CC_TAB);
        if (!indented4 && (setextLevel(d.s) > 0 || /^[:\-|\s]+$/.test(d.s))) {
          if (trySetextOrTable(leaf, d.s)) continue;
        }
        // interrupting blocks?
        const s = d.s;
        const interrupts = parseAtx(s) !== null ||
          parseFence(s) !== null ||
          (htmlBlockType(s) > 0 && htmlBlockType(s) !== 7) ||
          isThematicBreak(s) ||
          s.charCodeAt(0) === CC_GT ||
          (() => {
            const lm = parseListMarker(s, d.base);
            if (!lm) return false;
            // an empty list item cannot interrupt a paragraph
            if (lm.empty) return false;
            // an ordered list can interrupt a paragraph only when it
            // starts at 1 -- except when the paragraph is inside a list
            // item, where any ordered list starts a nested list
            if (lm.ordered && lm.start !== 1) {
              let p = leaf.parent;
              while (p && p.t !== 'doc') {
                if (p.t === 'item') return true;
                p = p.parent;
              }
              return false;
            }
            return true;
          })();
        if (interrupts) {
          closeLeaf();
          phase2(rest, true, base, ln);
          blankPending = false;
          blankScope = null;
          continue;
        }
        // a continuation inside a list item loses 4 columns of leading
        // whitespace when it has 4+ (the indented code indent); inside
        // a blockquote it keeps all its spaces
        leaf.lines.push(stripParaIndent(rest, base, hasItemAncestor(leaf)));
        continue;
      }
    }
    // no leaf consumes it: phase 2
    phase2(rest, true, base, ln);
    blankPending = false;
    blankScope = null;
  }

  closeBlocks(1, true);
  return { root, refs };
}

// ---- inline parsing -------------------------------------------------------
// A flat atom list is built by scanning the inline text once; links are
// resolved as their closing bracket is met, then emphasis is processed over
// the list (delimiters never match across a link boundary), then the atoms
// are rendered to HTML.

// Escape &, <, >, ", ' unconditionally (code content, literal text).
function escapePlain(s) {
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === CC_AMP) { out += s.slice(start, i) + '&amp;'; start = i + 1; }
    else if (c === CC_LT) { out += s.slice(start, i) + '&lt;'; start = i + 1; }
    else if (c === CC_GT) { out += s.slice(start, i) + '&gt;'; start = i + 1; }
    else if (c === CC_QUOT) { out += s.slice(start, i) + '&quot;'; start = i + 1; }
    else if (c === CC_APOS) { out += s.slice(start, i) + '&#39;'; start = i + 1; }
  }
  return start === 0 ? s : out + s.slice(start);
}

function isEmailLocalChar(c) {
  return isAlnum(c) || c === CC_DOT || c === CC_UNDER || c === CC_DASH || c === 43; // + . _ -
}
function isDomainChar(c) {
  return isAlnum(c) || c === CC_DASH;
}

// Scan an email address starting at `i` (the local part's first char).
// Returns {email, end} or null. The domain must contain a dot, and every
// label must start and end with an alphanumeric. `allowUnder` (optional)
// is called with the position of a "_" right after the domain and returns
// true when that "_" is a closing emphasis delimiter (so the address
// still counts, e.g. inside __...__).
function scanEmail(text, i, allowUnder) {
  const n = text.length;
  let j = i;
  while (j < n && isEmailLocalChar(text.charCodeAt(j))) j++;
  if (j === i) return null;
  if (j >= n || text.charCodeAt(j) !== 64) return null; // @
  let k = j + 1;
  // domain: labels separated by dots, at least one dot
  let labels = 0;
  let lastDot = -1;
  while (k < n) {
    const c = text.charCodeAt(k);
    if (isAlnum(c)) { k++; continue; }
    if (c === CC_DASH) {
      // hyphen must not start or end a label
      if (k === j + 1 || k + 1 >= n || !isAlnum(text.charCodeAt(k + 1))) return null;
      k++;
      continue;
    }
    if (c === CC_DOT) {
      // a dot right after @ is invalid; a dot not followed by an alnum
      // is trailing punctuation -- the domain ends before it
      if (k === j + 1) return null;
      if (k + 1 >= n || !isAlnum(text.charCodeAt(k + 1))) break;
      labels++;
      lastDot = k;
      k++;
      continue;
    }
    break;
  }
  if (labels < 1) return null;
  // the last label must end with an alnum (the loop guarantees the char
  // before the stop is alnum, unless it stopped on a dot/hyphen)
  const last = text.charCodeAt(k - 1);
  if (!isAlnum(last)) return null;
  // a "_" right after the domain invalidates the address (it is a local
  // char, so the token is not a standalone email) -- unless it is a
  // closing emphasis delimiter, in which case the address still counts
  if (k < n && text.charCodeAt(k) === CC_UNDER && !(allowUnder && allowUnder(k))) return null;
  return { email: text.slice(i, k), end: k };
}

// Scan a www/http(s) URL starting at `i` (just past the "www." or "://").
// Returns the end index after trailing-punctuation stripping, or -1 when
// there is nothing after the prefix.
function scanUrl(text, i, inLabel) {
  const n = text.length;
  let j = i;
  while (j < n) {
    const c = text.charCodeAt(j);
    if (c === CC_SPACE || c === CC_TAB || c === CC_NL || c === CC_CR || c === CC_LT || c < 32) break;
    // inside a link label, a "]" closes the label -- the URL ends
    // there instead of swallowing the label's closing bracket
    if (inLabel && c === CC_RBRACK) break;
    // an "&" that begins an entity reference (&word; / &#...; / &#x...;)
    // ends the URL -- the entity is literal text, not part of the link
    if (c === 38) {
      let k = j + 1;
      if (k < n && text.charCodeAt(k) === 35) {
        k++;
        if (k < n && (text.charCodeAt(k) === 120 || text.charCodeAt(k) === 88)) k++;
        while (k < n && isAlnum(text.charCodeAt(k))) k++;
      } else {
        while (k < n && isAlnum(text.charCodeAt(k))) k++;
      }
      if (k > j + 1 && k < n && text.charCodeAt(k) === CC_SEMI) break;
    }
    j++;
  }
  if (j === i) return -1;
  let end = j;
  // a "(" must be part of a "(...)" group closed before the URL ends
  // (marked's backpedal); an unclosed "(" truncates the URL before it
  {
    let k = i;
    while (k < end) {
      if (text.charCodeAt(k) === CC_LPAREN) {
        let r = k + 1;
        while (r < end && text.charCodeAt(r) !== CC_RPAREN) r++;
        if (r >= end) { end = k; break; }
        k = r + 1;
      } else k++;
    }
  }
  for (;;) {
    let changed = false;
    while (end > i) {
      const c = text.charCodeAt(end - 1);
      if (c === 63 || c === 33 || c === CC_DOT || c === 44 || c === CC_COLON || c === CC_SEMI || c === CC_STAR || c === CC_UNDER || c === CC_TILDE) { end--; changed = true; }
      else break;
    }
    while (end > i && text.charCodeAt(end - 1) === CC_RPAREN) {
      // a trailing ")" is kept only when it closes an "(" that is
      // still open just before it (marked's backpedal treats "(...)"
      // as a balanced unit); an unmatched trailing ")" is stripped
      let depth = 0;
      for (let k = i; k < end - 1; k++) {
        if (text.charCodeAt(k) === CC_LPAREN) depth++;
        else if (text.charCodeAt(k) === CC_RPAREN && depth > 0) depth--;
      }
      if (depth > 0) break;
      end--; changed = true;
    }
    if (!changed) break;
  }
  return end === i ? -1 : end;
}

// Parse an HTML tag starting at text[i] === '<'. Returns {tag, end} or null.
function parseHtmlTag(text, i) {
  const n = text.length;
  if (text.charCodeAt(i) !== CC_LT) return null;
  let j = i + 1;
  // comment (the first --> ends it, so <!--> is an empty comment)
  if (text.startsWith('<!--', i)) {
    const e = text.indexOf('-->', i + 2);
    if (e < 0) return null;
    return { tag: text.slice(i, e + 3), end: e + 3 };
  }
  // processing instruction
  if (text.charCodeAt(j) === 63) {
    const e = text.indexOf('?>', j + 1);
    if (e < 0) return null;
    return { tag: text.slice(i, e + 2), end: e + 2 };
  }
  // declaration / CDATA
  if (text.charCodeAt(j) === 33) {
    if (text.startsWith('<![CDATA[', i)) {
      const e = text.indexOf(']]>', i + 9);
      if (e < 0) return null;
      return { tag: text.slice(i, e + 3), end: e + 3 };
    }
    if (j + 1 < n && ((text.charCodeAt(j + 1) >= 65 && text.charCodeAt(j + 1) <= 90) || (text.charCodeAt(j + 1) >= 97 && text.charCodeAt(j + 1) <= 122))) {
      const e = text.indexOf('>', j + 1);
      if (e < 0) return null;
      return { tag: text.slice(i, e + 1), end: e + 1 };
    }
    return null;
  }
  // close tag
  let close = false;
  if (text.charCodeAt(j) === 47) { close = true; j++; }
  if (j >= n || !((text.charCodeAt(j) >= 65 && text.charCodeAt(j) <= 90) || (text.charCodeAt(j) >= 97 && text.charCodeAt(j) <= 122))) return null;
  // tag names are letters, digits and hyphens (custom elements)
  while (j < n && (isAlnum(text.charCodeAt(j)) || text.charCodeAt(j) === CC_DASH)) j++;
  if (close) {
    while (j < n && (text.charCodeAt(j) === CC_SPACE || text.charCodeAt(j) === CC_TAB || text.charCodeAt(j) === CC_NL)) j++;
    if (j >= n || text.charCodeAt(j) !== CC_GT) return null;
    return { tag: text.slice(i, j + 1), end: j + 1 };
  }
  // open tag: attributes, each separated from the previous by whitespace
  let seenAttr = false;
  for (;;) {
    let skippedWs = false;
    while (j < n && (text.charCodeAt(j) === CC_SPACE || text.charCodeAt(j) === CC_TAB || text.charCodeAt(j) === CC_NL)) { j++; skippedWs = true; }
    if (j >= n) return null;
    const c = text.charCodeAt(j);
    if (c === CC_GT) return { tag: text.slice(i, j + 1), end: j + 1 };
    if (c === 47) {
      if (text.charCodeAt(j + 1) === CC_GT) return { tag: text.slice(i, j + 2), end: j + 2 };
      return null;
    }
    // an attribute needs whitespace before it (including the first,
    // which must be separated from the tag name)
    if (!skippedWs) return null;
    // attribute name
    if (!((c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === CC_UNDER || c === CC_COLON)) return null;
    j++;
    while (j < n) {
      const a = text.charCodeAt(j);
      if (isAlnum(a) || a === CC_UNDER || a === CC_COLON || a === CC_DOT || a === CC_DASH) j++;
      else break;
    }
    // optional whitespace then optional = value; the whitespace is only
    // consumed when an = follows, so it still separates attributes when
    // the attribute has no value
    let k = j;
    while (k < n && (text.charCodeAt(k) === CC_SPACE || text.charCodeAt(k) === CC_TAB || text.charCodeAt(k) === CC_NL)) k++;
    if (k < n && text.charCodeAt(k) === CC_EQ) {
      j = k;
      j++;
      while (j < n && (text.charCodeAt(j) === CC_SPACE || text.charCodeAt(j) === CC_TAB || text.charCodeAt(j) === CC_NL)) j++;
      if (j >= n) return null;
      const q = text.charCodeAt(j);
      if (q === CC_QUOT || q === CC_APOS) {
        j++;
        while (j < n && text.charCodeAt(j) !== q) j++;
        if (j >= n) return null;
        j++;
      } else {
        if (q === CC_SPACE || q === CC_TAB || q === CC_NL || q === CC_GT || q === CC_QUOT || q === CC_APOS || q === CC_EQ || q === CC_LT || q === CC_BACKTICK) return null;
        while (j < n) {
          const a = text.charCodeAt(j);
          if (a === CC_SPACE || a === CC_TAB || a === CC_NL || a === CC_GT || a === CC_QUOT || a === CC_APOS || a === CC_EQ || a === CC_LT || a === CC_BACKTICK) break;
          j++;
        }
      }
    }
    seenAttr = true;
  }
}

// Parse an autolink <...> starting at text[i] === '<'. Returns
// {href, text, end} or null.
function parseAutolink(text, i) {
  const n = text.length;
  // scheme: [A-Za-z][A-Za-z0-9+.-]{1,31}:
  let j = i + 1;
  if (j >= n || !((text.charCodeAt(j) >= 65 && text.charCodeAt(j) <= 90) || (text.charCodeAt(j) >= 97 && text.charCodeAt(j) <= 122))) return null;
  j++;
  let sl = 1;
  while (j < n && (isAlnum(text.charCodeAt(j)) || text.charCodeAt(j) === 43 || text.charCodeAt(j) === CC_DOT || text.charCodeAt(j) === CC_DASH)) { j++; sl++; }
  if (sl >= 2 && sl <= 32 && j < n && text.charCodeAt(j) === CC_COLON) {
    let k = j + 1;
    while (k < n) {
      const c = text.charCodeAt(k);
      if (c === CC_SPACE || c === CC_TAB || c === CC_NL || c === CC_LT || c < 32) break;
      if (c === CC_GT) {
        const inner = text.slice(i + 1, k);
        return { href: inner, text: inner, end: k + 1 };
      }
      k++;
    }
    return null;
  }
  // email: <local@domain>
  const em = scanEmail(text, i + 1);
  if (em && text.charCodeAt(em.end) === CC_GT) {
    return { href: 'mailto:' + em.email, text: em.email, end: em.end + 1 };
  }
  return null;
}

// Plain-text rendering of atoms (for image alt text): text and code as-is,
// delimiters and link markers contribute nothing.
function plainTextOf(atoms) {
  let out = '';
  for (const a of atoms) {
    if (a.k === 't' || a.k === 'code') out += a.s;
    else if (a.k === 'br' || a.k === 'nl') out += '\n';
    // an image's children were spliced out when it resolved; its alt
    // text is the only record of them
    else if (a.k === 'lo' && a.img) out += a.alt || '';
  }
  return out;
}

// Scan inline text into a flat atom list. Links are resolved inline; the
// result is then run through emphasis processing and rendered.
function scanInline(text, refs) {
  const atoms = [];
  const n = text.length;
  let i = 0;
  let ts = 0; // start of the current plain-text run
  // unmatched [ / ![ openers: while one is open, no autolink is formed
  // (a link's text is plain text, not a nested link) -- unless the
  // label already contains a real (non-image, non-autolink) link, in
  // which case it can never resolve and the autolink is allowed
  let openLabels = 0;
  const labelHasLink = () => {
    for (let k = atoms.length - 1; k >= 0; k--) {
      const a = atoms[k];
      if (a.k === 'd' && a.ch === '[' && a.active) {
        for (let q = k + 1; q < atoms.length; q++) {
          if (atoms[q].k === 'lo' && !atoms[q].auto && !atoms[q].img) return true;
        }
        return false;
      }
    }
    return false;
  };
  const pushText = (s, lit) => {
    if (!s) return;
    const last = atoms[atoms.length - 1];
    if (last && last.k === 't' && last.lit === lit) last.s += s;
    else atoms.push({ k: 't', s, lit: !!lit });
  };
  const flushText = (end) => { if (end > ts) pushText(text.slice(ts, end)); };

  // Resolve a link whose ] is at text[i]. Returns the new index (just past
  // the link suffix) or -1 when no link forms.
  const tryLink = (closePos) => {
    // find the nearest active [ delimiter
    let oi = -1;
    for (let k = atoms.length - 1; k >= 0; k--) {
      const a = atoms[k];
      if (a.k === 'd' && a.ch === '[') { if (a.active) oi = k; break; }
      if (a.k === 'd' && a.ch === ']') break; // unreachable in practice
    }
    if (oi < 0) return -1;
    // the [ is consumed either way (link formed or literal text)
    openLabels--;
    const open = atoms[oi];
    // a label with an invalid backtick run (a lone single backtick,
    // per marked's label regex) cannot form a link at all
    if (open.pos !== undefined && !labelBackticksValid(text, open.pos, closePos)) return -1;
    let pos = closePos + 1;
    let href = null;
    let title = null;
    let end = -1;
    // inline link: (dest "title")
    if (pos < n && text.charCodeAt(pos) === CC_LPAREN) {
      // empty destination: [link]() -- only with no whitespace inside
      if (pos + 1 < n && text.charCodeAt(pos + 1) === CC_RPAREN) {
        href = '';
        end = pos + 2;
      } else {
        const r = skipLinkWhitespace(text, pos + 1);
        if (r > 0) {
          const d = parseLinkDestination(text, r);
          if (d) {
            const t = skipLinkWhitespace(text, d.end);
            if (t > 0) {
              const ti = parseLinkTitle(text, t);
              if (ti) {
                const e = skipLinkWhitespace(text, ti.end);
                if (e > 0 && text.charCodeAt(e) === CC_RPAREN) {
                  href = unescapeBackslashes(d.dest);
                  title = unescapeBackslashes(ti.title);
                  end = e + 1;
                }
              } else if (text.charCodeAt(t) === CC_RPAREN) {
                href = unescapeBackslashes(d.dest);
                end = t + 1;
              }
            }
          }
        }
      }
    }
    // reference link: [label], [] (collapsed), or shortcut
    if (href === null) {
      let label = null;
      let lend = -1;
      if (pos < n && text.charCodeAt(pos) === CC_LBRACK) {
        const lb = parseLinkLabel(text, pos);
        if (lb) { label = lb.label; lend = lb.end; }
        else if (pos + 1 < n && text.charCodeAt(pos + 1) === CC_RBRACK) {
          label = text.slice(open.pos, closePos);
          lend = pos + 2;
        }
      }
      if (label === null) {
        label = text.slice(open.pos, closePos);
        lend = closePos + 1;
      }
      if (label !== null) {
        const key = normalizeLabel(label);
        if (key.length > 0 && key.length <= 999) {
          const ref = refs.get(key);
          if (ref) {
            href = ref.dest;
            title = ref.title;
            end = lend;
          }
        }
      }
    }
    if (href === null) {
      // failure: the [ is literal text; restore a leading ! if present
      open.active = false;
      open.ch = '[';
      // convert the [ delimiter atom into literal text, inserting ! first
      const idx = atoms.indexOf(open);
      atoms[idx] = { k: 't', s: open.img ? '![' : '[', lit: false };
      return -1;
    }
    // success: turn the [ atom into the link opener, append the closer
    const children = atoms.slice(oi + 1);
    // a link's text may not contain another bracket link (an image may:
    // its inner links only feed the alt text). Autolinks may nest inside
    // a link's text, so they do not block it.
    if (!open.img) {
      for (const a of children) {
        if (a.k === 'lo' && !a.img && !a.auto) {
          open.active = false;
          open.ch = '[';
          const idx = atoms.indexOf(open);
          atoms[idx] = { k: 't', s: '[', lit: false };
          return -1;
        }
      }
    }
    // a GFM autolink inside a label that resolves is literal text
    // (marked suppresses it); one in a label that never resolves stays
    // a link. Demote the GFM autolinks here: a GFM autolink is lo,t,lc
    // consecutively, so remove the lo and its matching lc. Angle-bracket
    // autolinks are NOT demoted -- they nest inside the link.
    if (!open.img) {
      const drop = new Set();
      for (let k = oi + 1; k < atoms.length; k++) {
        const a = atoms[k];
        if (a.k === 'lo' && a.gfm) {
          drop.add(k);
          for (let q = k + 1; q < atoms.length; q++) {
            if (atoms[q].k === 'lc') { drop.add(q); break; }
            if (atoms[q].k === 'lo') break;
          }
        }
      }
      if (drop.size > 0) {
        let w = oi + 1;
        for (let r = oi + 1; r < atoms.length; r++) {
          if (!drop.has(r)) atoms[w++] = atoms[r];
        }
        atoms.length = w;
      }
    }
    const alt = plainTextOf(children);
    open.k = 'lo';
    open.href = href;
    open.title = title;
    open.alt = alt;
    if (open.img) {
      // an image renders only its <img> tag; its text becomes the alt
      // attribute and is not rendered as content
      atoms.splice(oi + 1, children.length);
    }
    atoms.push({ k: 'lc', img: open.img });
    return end;
  };

  while (i < n) {
    const c = text.charCodeAt(i);
    // ---- newline: hard break (backslash or two trailing spaces) or soft
    if (c === CC_NL) {
      flushText(i);
      // count the unescaped backslashes at the end of the current text run
      let bs = 0;
      for (let j = i - 1; j >= ts && text.charCodeAt(j) === CC_BACKSLASH; j--) bs++;
      let hard = false;
      if (bs % 2 === 1) {
        // backslash before the newline: drop it from the text run
        const last = atoms[atoms.length - 1];
        if (last && last.k === 't' && !last.lit && last.s.endsWith('\\')) last.s = last.s.slice(0, -1);
        atoms.push({ k: 'br' });
        hard = true;
      } else {
        let j = i - 1;
        let sp = 0;
        while (j >= ts && text.charCodeAt(j) === CC_SPACE) { sp++; j--; }
        if (sp >= 2) {
          // a hard break: all trailing spaces are dropped, not just two
          const last = atoms[atoms.length - 1];
          if (last && last.k === 't' && !last.lit) last.s = last.s.slice(0, last.s.length - sp);
          atoms.push({ k: 'br' });
          hard = true;
        } else {
          atoms.push({ k: 'nl' });
        }
      }
      i++;
      // after a hard break the next line's leading whitespace is stripped
      if (hard) {
        while (i < n && (text.charCodeAt(i) === CC_SPACE || text.charCodeAt(i) === CC_TAB)) i++;
      }
      ts = i;
      continue;
    }
    // ---- code span
    if (c === CC_BACKTICK) {
      let j = i;
      while (j < n && text.charCodeAt(j) === CC_BACKTICK) j++;
      const len = j - i;
      // a code span may not span past the closing ] of the innermost
      // open link label (marked tokenizes a link's label separately,
      // so a backtick run inside it can only close inside the label)
      let labelClose = -1;
      if (openLabels > 0) {
        for (let q = atoms.length - 1; q >= 0; q--) {
          const a = atoms[q];
          if (a.k === 'd' && a.ch === '[' && a.active && a.pos !== undefined) {
            let depth = 1;
            for (let p = a.pos; p < n; p++) {
              const pc = text.charCodeAt(p);
              if (pc === CC_BACKSLASH) { p++; continue; }
              if (pc === 91) depth++;
              else if (pc === 93) { depth--; if (depth === 0) { labelClose = p; break; } }
            }
            // bound the closer search to the label only when the label
            // is valid (a link will form); an invalid label cannot form
            // a link, so the code span may pair across its ]. The
            // label must also close ahead of this backtick: a ] behind
            // us (e.g. one swallowed by an autolink URL) means this
            // backtick is not inside the label at all.
            if (labelClose >= 0 && labelClose <= i) labelClose = -1;
            if (labelClose >= 0 && !labelBackticksValid(text, a.pos, labelClose)) labelClose = -1;
            break;
          }
        }
      }
      let k = j;
      let found = -1;
      for (;;) {
        k = text.indexOf('`', k);
        if (k < 0 || (labelClose >= 0 && k >= labelClose)) break;
        let e = k;
        while (e < n && text.charCodeAt(e) === CC_BACKTICK) e++;
        if (e - k === len) { found = k; break; }
        k = e;
      }
      // no matching closer: the whole opening run is literal text
      if (found < 0) { i = j; continue; }
      flushText(i);
      // newlines become spaces first; then one leading and one trailing
      // space are stripped when both are present and the content is not
      // all spaces
      let content = text.slice(j, found).replace(/\n/g, ' ');
      if (content.length >= 2 && content.charCodeAt(0) === CC_SPACE && content.charCodeAt(content.length - 1) === CC_SPACE && /[^ ]/.test(content)) {
        content = content.slice(1, -1);
      }
      atoms.push({ k: 'code', s: content });
      i = found + len;
      ts = i;
      continue;
    }
    // ---- backslash escape
    if (c === CC_BACKSLASH) {
      if (i + 1 < n) {
        const d = text.charCodeAt(i + 1);
        if (isAsciiPunct(d)) {
          flushText(i);
          pushText(String.fromCharCode(d), true);
          i += 2;
          ts = i;
          continue;
        }
        if (d === CC_NL) { i++; continue; } // handled by the newline branch
      }
      i++;
      continue;
    }
    // ---- emphasis / strikethrough delimiters
    if (c === CC_STAR || c === CC_UNDER || c === CC_TILDE) {
      let j = i;
      while (j < n && text.charCodeAt(j) === c) j++;
      const len = j - i;
      // code point of the character just before the run (astral-aware)
      let prev = 0;
      if (i > 0) {
        const pc = text.charCodeAt(i - 1);
        if (pc >= 0xDC00 && pc <= 0xDFFF && i - 2 >= 0 && text.charCodeAt(i - 2) >= 0xD800 && text.charCodeAt(i - 2) <= 0xDBFF) {
          prev = text.codePointAt(i - 2);
        } else prev = pc;
      }
      const next = j >= n ? 0 : text.codePointAt(j);
      const prevWs = i === 0 || isSpaceOrNl(prev);
      const nextWs = j >= n || isSpaceOrNl(next);
      const leftFlank = !nextWs && (!isPunct(next) || prevWs || isPunct(prev));
      const rightFlank = !prevWs && (!isPunct(prev) || nextWs || isPunct(next));
      let canOpen, canClose;
      if (c === CC_UNDER) {
        canOpen = leftFlank && (!rightFlank || isPunct(prev));
        canClose = rightFlank && (!leftFlank || isPunct(next));
      } else {
        canOpen = leftFlank;
        canClose = rightFlank;
      }
      flushText(i);
      atoms.push({ k: 'd', ch: String.fromCharCode(c), n: len, open: canOpen, close: canClose, active: true, pos: i });
      i = j;
      ts = i;
      continue;
    }
    // ---- image opener
    if (c === CC_BANG && i + 1 < n && text.charCodeAt(i + 1) === CC_LBRACK) {
      flushText(i);
      atoms.push({ k: 'd', ch: '[', n: 0, open: false, close: false, active: true, img: true, pos: i + 2 });
      openLabels++;
      i += 2;
      ts = i;
      continue;
    }
    // ---- link opener
    if (c === CC_LBRACK) {
      flushText(i);
      atoms.push({ k: 'd', ch: '[', n: 0, open: false, close: false, active: true, img: false, pos: i + 1 });
      openLabels++;
      i++;
      ts = i;
      continue;
    }
    // ---- link closer
    if (c === CC_RBRACK) {
      // flush the pending text run first: it is the link's text
      flushText(i);
      ts = i;
      const end = tryLink(i);
      if (end >= 0) {
        i = end;
        ts = i;
        continue;
      }
      i++;
      continue;
    }
    // ---- < : autolink, raw HTML, or entity. Angle-bracket autolinks
    // are recognized inside link labels too (they may nest in a link);
    // only bare GFM autolinks are suppressed there.
    if (c === CC_LT) {
      const al = parseAutolink(text, i);
      if (al) {
        flushText(i);
        atoms.push({ k: 'lo', href: al.href, title: null, alt: '', img: false, auto: true });
        atoms.push({ k: 't', s: al.text, lit: false });
        atoms.push({ k: 'lc', img: false });
        i = al.end;
        ts = i;
        continue;
      }
      const tag = parseHtmlTag(text, i);
      if (tag) {
        // an <a href="...\<newline>..."> tag suppresses all later GFM
        // autolinks in the document (marked quirk); a </a> parsed
        // inline resets the suppression again
        if (isGfmSuppressingTag(tag.tag)) gfmSuppressed = true;
        else if (tag.tag.length >= 4 && tag.tag.charCodeAt(0) === CC_LT && tag.tag.charCodeAt(1) === 47 &&
          (tag.tag.charCodeAt(2) === 97 || tag.tag.charCodeAt(2) === 65)) {
          const c3 = tag.tag.charCodeAt(3);
          if (c3 === CC_GT || c3 === CC_SPACE || c3 === CC_TAB || c3 === CC_NL) gfmSuppressed = false;
        }
        flushText(i);
        atoms.push({ k: 'html', s: tag.tag });
        i = tag.end;
        ts = i;
        continue;
      }
      i++;
      continue;
    }
    // ---- entity / numeric reference
    if (c === CC_AMP) {
      const ent = parseEntity(text, i);
      if (ent) {
        flushText(i);
        // a decoded numeric character is escaped plainly; a named
        // reference is left for the entity-aware escape to pass through
        pushText(ent.ch, !ent.named);
        i = ent.end;
        ts = i;
        continue;
      }
      i++;
      continue;
    }
    // ---- www. autolink
    if (c === 119 && !gfmSuppressed && text.startsWith('www.', i)) {
      const prev = i === 0 ? 0 : text.charCodeAt(i - 1);
      if (i === 0 || isSpaceOrNl(prev) || prev === CC_STAR || prev === CC_UNDER || prev === CC_TILDE || prev === CC_LPAREN) {
        const end = scanUrl(text, i + 4, openLabels > 0 && !labelHasLink());
        if (end > 0) {
          flushText(i);
          const url = text.slice(i, end);
          atoms.push({ k: 'lo', href: 'http://' + url, title: null, alt: '', img: false, auto: true, gfm: true });
          atoms.push({ k: 't', s: url, lit: false });
          atoms.push({ k: 'lc', img: false });
          i = end;
          ts = i;
          continue;
        }
      }
      i++;
      continue;
    }
    // ---- http(s):// autolink (case-insensitive scheme, no boundary rule)
    if ((c === 104 || c === 72) && !gfmSuppressed) {
      let j = i + 1;
      while (j < n && ((text.charCodeAt(j) >= 65 && text.charCodeAt(j) <= 90) || (text.charCodeAt(j) >= 97 && text.charCodeAt(j) <= 122))) j++;
      const scheme = text.slice(i, j).toLowerCase();
      if ((scheme === 'http' || scheme === 'https') && j + 2 < n && text.charCodeAt(j) === CC_COLON && text.charCodeAt(j + 1) === 47 && text.charCodeAt(j + 2) === 47) {
        const end = scanUrl(text, j + 3, openLabels > 0 && !labelHasLink());
        if (end > 0) {
          flushText(i);
          const url = text.slice(i, end);
          atoms.push({ k: 'lo', href: url, title: null, alt: '', img: false, auto: true, gfm: true });
          atoms.push({ k: 't', s: url, lit: false });
          atoms.push({ k: 'lc', img: false });
          i = end;
          ts = i;
          continue;
        }
      }
      i++;
      continue;
    }
    // ---- mailto: / xmpp: autolinks
    if (c === 109 && !gfmSuppressed && text.startsWith('mailto:', i)) {
      const prev = i === 0 ? 0 : text.charCodeAt(i - 1);
      if (i === 0 || !(isAlnum(prev) || prev === 43 || prev === CC_DOT || prev === CC_DASH)) {
        const em = scanEmail(text, i + 7);
        if (em) {
          flushText(i);
          const url = 'mailto:' + em.email;
          atoms.push({ k: 'lo', href: url, title: null, alt: '', img: false, auto: true, gfm: true });
          atoms.push({ k: 't', s: url, lit: false });
          atoms.push({ k: 'lc', img: false });
          i = em.end;
          ts = i;
          continue;
        }
      }
      i++;
      continue;
    }
    if (c === 120 && !gfmSuppressed && text.startsWith('xmpp:', i)) {
      const prev = i === 0 ? 0 : text.charCodeAt(i - 1);
      if (i === 0 || !(isAlnum(prev) || prev === 43 || prev === CC_DOT || prev === CC_DASH)) {
        const em = scanEmail(text, i + 5);
        if (em) {
          let end = em.end;
          if (text.charCodeAt(end) === 47) {
            let k = end + 1;
            while (k < n) {
              const ch = text.charCodeAt(k);
              if (ch === CC_SPACE || ch === CC_TAB || ch === CC_NL || ch === CC_LT || ch === 47) break;
              k++;
            }
            if (k > end + 1) end = k;
          }
          flushText(i);
          const url = text.slice(i, end);
          atoms.push({ k: 'lo', href: url, title: null, alt: '', img: false, auto: true, gfm: true });
          atoms.push({ k: 't', s: url, lit: false });
          atoms.push({ k: 'lc', img: false });
          i = end;
          ts = i;
          continue;
        }
      }
      i++;
      continue;
    }
    // ---- email autolink
    if (c === 64 && !gfmSuppressed) {
      // scan the local part back through the raw text (not bounded by
      // the current text run: a "_" inside the address was already
      // emitted as an emphasis delimiter and must be rewound). Stop
      // at a "_" that opens emphasis (e.g. the "__" of a strong) --
      // it is not part of the address.
      let ls = i - 1;
      while (ls >= 0 && isEmailLocalChar(text.charCodeAt(ls))) {
        if (text.charCodeAt(ls) === CC_UNDER) {
          // the last "_" delimiter at or before this position
          let opensEm = false;
          for (let q = atoms.length - 1; q >= 0; q--) {
            const a = atoms[q];
            if (a.k === 'd' && a.ch === '_' && a.pos !== undefined && a.pos <= ls) {
              opensEm = a.open && ls < a.pos + a.n;
              break;
            }
          }
          if (opensEm) break;
        }
        ls--;
      }
      ls++;
      // a local part starting with a backslash-escaped char is not an
      // email (e.g. "foo\+@bar" -- the "+" is escaped, so no autolink)
      if (ls < i) {
        let bs = 0;
        for (let b = ls - 1; b >= 0 && text.charCodeAt(b) === CC_BACKSLASH; b--) bs++;
        if (bs % 2 === 1) { i++; continue; }
      }
      if (ls < i) {
        // a "_" right after the domain is a closing emphasis delimiter
        // (not part of the address) when it can close and some "_"
        // opener is still open in the atoms list
        const allowUnder = (k) => {
          let re = k;
          while (re < text.length && text.charCodeAt(re) === CC_UNDER) re++;
          const prev = k > 0 ? text.charCodeAt(k - 1) : 0;
          const next = re < text.length ? text.codePointAt(re) : 0;
          const prevWs = k === 0 || isSpaceOrNl(prev);
          const nextWs = re >= text.length || isSpaceOrNl(next);
          const leftFlank = !nextWs && (!isPunct(next) || prevWs || isPunct(prev));
          const rightFlank = !prevWs && (!isPunct(prev) || nextWs || isPunct(next));
          const canClose = rightFlank && (!leftFlank || isPunct(next));
          if (!canClose) return false;
          for (let q = atoms.length - 1; q >= 0; q--) {
            const a = atoms[q];
            if (a.k === 'd' && a.ch === '_' && a.open && a.active) return true;
          }
          return false;
        };
        const em = scanEmail(text, ls, allowUnder);
        if (em) {
          if (ls < ts) {
            // rewind atoms emitted for the local-part span [ls, ts):
            // text atoms and "_" delimiter atoms (the only delimiter
            // that is also an email local char). Stop at a link boundary.
            let need = ts - ls;
            while (need > 0 && atoms.length > 0) {
              const a = atoms[atoms.length - 1];
              if (a.k === 'lo' || a.k === 'lc') break;
              const len = a.k === 't' ? a.s.length : (a.k === 'd' ? a.n : 0);
              atoms.pop();
              need -= len;
            }
            ts = ls;
          }
          flushText(ls);
          atoms.push({ k: 'lo', href: 'mailto:' + em.email, title: null, alt: '', img: false, auto: true, gfm: true });
          atoms.push({ k: 't', s: em.email, lit: false });
          atoms.push({ k: 'lc', img: false });
          i = em.end;
          ts = i;
          continue;
        }
      }
      i++;
      continue;
    }
    i++;
  }
  flushText(n);
  return atoms;
}

// ---- emphasis processing --------------------------------------------------
// Walk the delimiter atoms in order; each closer looks backwards for the
// nearest opener with the same character that can match it. Delimiters
// never match across a link boundary (depth is tracked through lo/lc).
function processEmphasis(atoms, masked) {
  // depth of every delimiter (number of enclosing links)
  const depth = new Map();
  let d = 0;
  for (const a of atoms) {
    if (a.k === 'lo') d++;
    else if (a.k === 'lc') d--;
    else if (a.k === 'd' && (a.ch === '*' || a.ch === '_' || a.ch === '~')) depth.set(a, d);
  }
  const delims = atoms.filter(a => a.k === 'd' && (a.ch === '*' || a.ch === '_' || a.ch === '~'));
  for (const closer of delims) {
    if (!closer.active || closer.n === 0 || !closer.close) continue;
    // marked's masked-source limit: a closer whose position falls
    // inside a masked code span / link / html region (the masked
    // source no longer holds the delimiter char there) can never
    // close an emphasis. The masking preserves length, so positions
    // align with the original text. Applies only outside links: a
    // link label is tokenized in its own nested parse with its own
    // masked source, so delimiters inside a label are not governed
    // by the outer limit.
    if (masked && depth.get(closer) === 0 && closer.pos !== undefined && masked[closer.pos] !== closer.ch) continue;
    while (closer.n > 0 && closer.close) {
      const ci = atoms.indexOf(closer);
      if (ci < 0) break;
      const cd = depth.get(closer);
      // search backwards for the nearest opener that can match
      let opener = null;
      let use = 0;
      let kind = null;
      let dd = cd;
      // emphasis depth relative to the closer: an opener inside an
      // already-formed emphasis cannot match a closer outside it
      let ed = 0;
      // index of the first (nearest the opener) inner strong close
      // tag seen while searching backwards
      let firstStrongClose = -1;
      // whether the search passed an inner emphasis formed by a
      // single delimiter of the same char whose closer could both
      // open and close; a single closer that passed one may not match
      // a multi-delimiter opener (it would steal a delimiter from a
      // strong), but it may still match a single-delimiter opener
      let passedBothEm = false;
      // deferred single-delimiter opener: a multi-delimiter closer
      // prefers a multi-delimiter opener (strong) over a nearer
      // single opener (em), because marked processes the earlier
      // ** opener first and it claims the ** closer for a strong.
      // Save the nearest single opener and keep searching; use it
      // only if no multi opener turns up.
      let singleCandidate = null;
      for (let k = ci - 1; k >= 0; k--) {
        const a = atoms[k];
        if (a.k === 'em' || a.k === 'strong' || a.k === 'del') {
          if (a.open) ed--;
          else {
            ed++;
            if (closer.n === 1 && a.both && a.use === 1 && a.ch === closer.ch) passedBothEm = true;
            // record the first inner strong (scanning backwards, the
            // last one recorded is the earliest in the document)
            if (a.k === 'strong') firstStrongClose = k;
          }
          if (ed < 0) break; // left the closer's emphasis context
          continue;
        }
        if (ed !== 0) continue; // inside a different emphasis
        if (a.k === 'lc') { dd++; continue; }
        if (a.k === 'lo') {
          if (dd === cd) break; // the closer sits inside this link
          dd--;
          continue;
        }
        if (a.k !== 'd' || a.ch !== closer.ch || !a.active || a.n === 0 || !a.open) continue;
        if (dd !== cd) continue;
        // odd-match rule (spec rule 9): if one of the two delimiters can
        // both open and close, their lengths must not sum to a multiple
        // of 3 -- unless both lengths are themselves multiples of 3
        const oneCanBoth = (a.open && a.close) || (closer.open && closer.close);
        const sum = a.n + closer.n;
        if (oneCanBoth && sum % 3 === 0 && !(a.n % 3 === 0 && closer.n % 3 === 0)) continue;
        // a single closer that passed a both-open-close inner em may
        // not match a multi-delimiter opener (it would steal a
        // delimiter from a strong); keep looking for an earlier opener
        if (passedBothEm && a.n >= 2) continue;
        // a single * closer may not match an opener past the first
        // inner strong when (a) the char right before that strong's
        // open tag is whitespace and (b) the text after the strong
        // is non-empty and either does not start with whitespace or
        // ends with whitespace (marked quirk: *a **b**c* and *foo
        // **bar**baz* stay literal, but *foo**bar**baz*, *a **b** c*
        // and *foo **bar*** form the em)
        if (closer.ch === '*' && closer.n === 1 && firstStrongClose >= 0) {
          // find the matching open tag of the first strong
          let depth = 0;
          let strongOpenIdx = -1;
          for (let q = firstStrongClose - 1; q >= 0; q--) {
            const aq = atoms[q];
            if (aq.k === 'em' || aq.k === 'strong' || aq.k === 'del') {
              if (aq.open) {
                if (depth === 0 && aq.k === 'strong') { strongOpenIdx = q; break; }
                depth--;
              } else depth++;
            }
          }
          // last text char before the strong's open tag
          let beforeCh = -1;
          if (strongOpenIdx >= 0) {
            for (let q = strongOpenIdx - 1; q >= 0; q--) {
              const aq = atoms[q];
              if ((aq.k === 't' || aq.k === 'code' || aq.k === 'html') && aq.s.length > 0) { beforeCh = aq.s.charCodeAt(aq.s.length - 1); break; }
              if (aq.k === 'nl') { beforeCh = CC_NL; break; }
              if (aq.k === 'd') { beforeCh = aq.ch.charCodeAt(0); break; }
              if (aq.k === 'br') { beforeCh = 65; break; }
            }
          }
          const beforeWs = beforeCh === CC_SPACE || beforeCh === CC_TAB || beforeCh === CC_NL || beforeCh === 13 || beforeCh === 12;
          // visible text after the strong: text, code spans, raw html
          // and leftover delimiters all count; tags do not
          let txt = '';
          for (let q = firstStrongClose + 1; q < ci; q++) {
            const aq = atoms[q];
            if (aq.k === 't' || aq.k === 'code' || aq.k === 'html') txt += aq.s;
            else if (aq.k === 'nl') txt += '\n';
            else if (aq.k === 'd') txt += aq.ch.repeat(aq.n);
          }
          const first = txt.charCodeAt(0);
          const last = txt.charCodeAt(txt.length - 1);
          const startsWs = first === CC_SPACE || first === CC_TAB || first === CC_NL || first === 13 || first === 12;
          const endsWs = last === CC_SPACE || last === CC_TAB || last === CC_NL || last === 13 || last === 12;
          if (beforeWs && txt.length > 0 && (!startsWs || endsWs)) break;
        }
        if (closer.ch === '~') {
          // strikethrough: only one or two tildes, and the opener and
          // closer must have exactly the same length
          if (a.n === closer.n && (a.n === 1 || a.n === 2)) {
            opener = a; use = a.n; kind = 'del'; break;
          }
          continue;
        }
        if (a.n >= 2 && closer.n >= 2) { opener = a; use = 2; kind = 'strong'; }
        else if (a.n >= 1 && closer.n >= 1) {
          // a closer with exactly 2 delimiters forming an em with a
          // single opener is deferred: it would leave only 1
          // delimiter, not enough for a farther multi opener's
          // strong, and marked's earlier ** opener claims the **
          // closer for a strong first. With 3+ delimiters there is
          // enough for both, so the nearer em forms first.
          if (closer.n === 2 && a.n === 1) {
            if (!singleCandidate) singleCandidate = { a, use: 1, kind: 'em' };
            continue;
          }
          opener = a; use = 1; kind = 'em';
        }
        else continue;
        break;
      }
      if (!opener && singleCandidate) {
        opener = singleCandidate.a; use = singleCandidate.use; kind = singleCandidate.kind;
      }
      if (!opener) break;
      // apply the match: the tag goes after the opener's remaining run and
      // before the closer's remaining run, so nesting comes out right.
      // Record whether the closer could both open and close, and how
      // many delimiters the match used.
      const both = closer.open && closer.close;
      const cIdx = atoms.indexOf(closer);
      if (closer.n - use === 0) atoms.splice(cIdx, 1, { k: kind, open: false, both, use, ch: closer.ch });
      else {
        closer.n -= use;
        // A strong's leftover closer delimiter goes INSIDE the strong
        // only for a 3-delimiter run whose strong contains a same-char
        // inner em followed immediately by a non-space char (marked's
        // emStrong: that em's closer is matched via the odd-match
        // branch, raising the count so the strong consumes the whole
        // run). A 4-delimiter run (e.g. ____ closing two nested
        // strongs) must leave its leftover outside so it can still
        // match the outer opener.
        let leftoverInside = false;
        // closer.n was already reduced by `use`; the run length
        // before this match is closer.n + use
        if (kind === 'strong' && closer.n + use === 3 && use === 2) {
          let lastEmClose = -1;
          for (let q = cIdx - 1; q >= 0; q--) {
            const aq = atoms[q];
            if (aq === opener) break;
            if (aq.k === 'em' && !aq.open && aq.ch === closer.ch) { lastEmClose = q; break; }
          }
          if (lastEmClose >= 0) {
            for (let q = lastEmClose + 1; q < cIdx; q++) {
              const aq = atoms[q];
              if ((aq.k === 't' || aq.k === 'code' || aq.k === 'html') && aq.s.length > 0) {
                const ch0 = aq.s.charCodeAt(0);
                leftoverInside = !(ch0 === CC_SPACE || ch0 === CC_TAB || ch0 === CC_NL || ch0 === 13 || ch0 === 12);
                break;
              }
              if (aq.k === 'nl') { leftoverInside = false; break; }
              if (aq.k === 'd') { leftoverInside = true; break; }
              if (aq.k === 'br') { leftoverInside = true; break; }
            }
          }
        }
        if (leftoverInside) atoms.splice(cIdx + 1, 0, { k: kind, open: false, both, use, ch: closer.ch });
        else atoms.splice(cIdx, 0, { k: kind, open: false, both, use, ch: closer.ch });
      }
      const oIdx = atoms.indexOf(opener);
      if (opener.n - use === 0) atoms.splice(oIdx, 1, { k: kind, open: true });
      else { opener.n -= use; atoms.splice(oIdx + 1, 0, { k: kind, open: true }); }
      if (opener.n === 0) opener.active = false;
      if (closer.n === 0) { closer.active = false; break; }
    }
  }
}

// Render an atom list to HTML.
function renderAtoms(atoms) {
  let out = '';
  for (const a of atoms) {
    switch (a.k) {
      case 't':
        out += a.lit ? escapePlain(a.s) : escapeText(a.s);
        break;
      case 'code':
        out += '<code>' + escapePlain(a.s) + '</code>';
        break;
      case 'html':
        out += a.s;
        break;
      case 'br':
        out += '<br>';
        break;
      case 'nl':
        out += '\n';
        break;
      case 'd':
        // a leftover [ delimiter (never closed, or its ] was taken by an
        // inner link) renders as a literal bracket
        if (a.ch === '[') out += '[';
        else out += escapePlain(a.ch.repeat(a.n));
        break;
      case 'lo': {
        const href = escapeHref(a.href);
        if (a.img) {
          out += '<img src="' + href + '" alt="' + escapeText(a.alt || '') + '"';
          if (a.title) out += ' title="' + escapeText(a.title) + '"';
          out += '>';
        } else {
          out += '<a href="' + href + '"';
          if (a.title) out += ' title="' + escapeText(a.title) + '"';
          out += '>';
        }
        break;
      }
      case 'lc':
        if (!a.img) out += '</a>';
        break;
      case 'em':
        out += a.open ? '<em>' : '</em>';
        break;
      case 'strong':
        out += a.open ? '<strong>' : '</strong>';
        break;
      case 'del':
        out += a.open ? '<del>' : '</del>';
        break;
    }
  }
  return out;
}

// Render inline content (a paragraph's text, a heading's text, a cell's
// text, ...).
function renderInline(text, refs) {
  if (!text) return '';
  const atoms = scanInline(text, refs);
  processEmphasis(atoms, maskInlineSource(text));
  return renderAtoms(atoms);
}

// ---- block rendering ------------------------------------------------------
function renderBlock(b, refs) {
  switch (b.t) {
    case 'para':
      return '<p>' + renderInline(b.text, refs) + '</p>\n';
    case 'heading':
      return '<h' + b.level + '>' + renderInline(b.text, refs) + '</h' + b.level + '>\n';
    case 'hr':
      return '<hr>\n';
    case 'code': {
      // the info string's first word, with backslash escapes removed
      const info = b.fenced && b.info ? unescapeBackslashes(b.info.split(/\s+/)[0]) : null;
      let s = '<pre><code';
      if (info) s += ' class="language-' + escapeText(info) + '"';
      // every line contributes its text plus a newline
      let content = '';
      for (const l of b.lines) content += l + '\n';
      s += '>' + escapePlain(content) + '</code></pre>\n';
      return s;
    }
    case 'quote':
      return '<blockquote>\n' + renderBlocks(b.children, refs) + '</blockquote>\n';
    case 'html':
      // a block that ended at a blank line, or at EOF when the source
      // has no trailing newline, renders its lines joined with no
      // trailing newline; otherwise a trailing newline is added
      return (b.endedAtBlank || b.noTrailingNl) ? b.lines.join('\n') : b.lines.join('\n') + '\n';
    case 'list': {
      const tag = b.ordered ? 'ol' : 'ul';
      let open = '<' + tag;
      if (b.ordered && b.start !== 1) open += ' start="' + b.start + '"';
      open += '>\n';
      return open + b.children.map(it => renderItem(it, b.tight, refs)).join('') + '</' + tag + '>\n';
    }
    case 'table': {
      const headCells = splitTableRow(b.header);
      const aligns = b.aligns;
      const renderCell = (cell, tag, align) => {
        let s = '<' + tag;
        if (align) s += ' align="' + align + '"';
        return s + '>' + renderInline(cell, refs) + '</' + tag + '>\n';
      };
      let s = '<table>\n<thead>\n<tr>\n' + headCells.map((c, i) => renderCell(c.trim(), 'th', aligns[i])).join('') + '</tr>\n</thead>\n';
      if (b.rows.length > 0) {
        s += '<tbody>';
        for (const row of b.rows) {
          const cells = splitTableRow(row);
          s += '<tr>\n';
          for (let i = 0; i < headCells.length; i++) {
            s += renderCell(i < cells.length ? cells[i].trim() : '', 'td', aligns[i]);
          }
          s += '</tr>\n';
        }
        s += '</tbody>';
      }
      return s + '</table>\n';
    }
  }
  return '';
}

function renderBlocks(blocks, refs) {
  let out = '';
  for (const b of blocks) out += renderBlock(b, refs);
  return out;
}

// A list item: a leading "[ ] " / "[x] " / "[X] " on its first paragraph
// is a task checkbox, and the marker is stripped from the text.
function renderItem(item, tight, refs) {
  let s = '<li>';
  let first = true;
  for (const b of item.children) {
    if (first && b.t === 'para') {
      const m = /^\[( |x|X)\] /.exec(b.text);
      if (m) {
        const box = '<input' + (m[1] === ' ' ? '' : ' checked=""') + ' disabled="" type="checkbox">';
        // tight: the checkbox sits directly in the <li>; loose: it opens
        // the paragraph. Either way a space follows the checkbox.
        if (tight) s += box + ' ' + renderInline(b.text.slice(4), refs);
        else s += '<p>' + box + ' ' + renderInline(b.text.slice(4), refs) + '</p>\n';
        first = false;
        continue;
      }
    }
    first = false;
    if (b.t === 'para' && tight) s += renderInline(b.text, refs);
    else s += renderBlock(b, refs);
  }
  return s + '</li>\n';
}

// ---- entry point ----------------------------------------------------------
export function parse(markdown) {
  if (markdown === '') return '';
  gfmSuppressed = false;
  const src = markdown.replace(/\r\n?/g, '\n');
  const { root, refs } = parseBlocks(src);
  return renderBlocks(root.children, refs);
}

export default parse;
