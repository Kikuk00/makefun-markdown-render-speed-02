// parse.js — a fast, dependency-free Markdown renderer.
//
// parse(markdown) returns exactly the HTML that marked 18.1.3 renders with
// its default options (GFM on, breaks off, pedantic off, async off).
// Written from the CommonMark 0.31.2 + GFM 0.29 rules and from marked's
// documented behaviour, as a single-pass implementation: a line scanner for
// blocks, a character scanner for inline content, and a small renderer.
// No token-tree pass is skipped, but no work is repeated: link references
// are collected during the block pass and inline content is tokenised once
// the whole block pass has finished, so definitions may appear after use.
//
// Nothing is cached between calls: every parse() call builds fresh state,
// so rendering one case can never leak into the next.

'use strict';

// ---------------------------------------------------------------------------
// Small character helpers
// ---------------------------------------------------------------------------

const CODE_LT = 60; // <
const CODE_GT = 62; // >
const CODE_AMP = 38; // &
const CODE_QUOT = 34; // "
const CODE_APOS = 39; // '
const CODE_BACKSLASH = 92; // \
const CODE_BACKTICK = 96; // `
const CODE_TILDE = 126; // ~
const CODE_STAR = 42; // *
const CODE_UNDER = 95; // _
const CODE_LBRACK = 91; // [
const CODE_RBRACK = 93; // ]
const CODE_LPAREN = 40; // (
const CODE_RPAREN = 41; // )
const CODE_LT_BRACE = 123; // {
const CODE_NEWLINE = 10; // \n
const CODE_SPACE = 32; // space
const CODE_TAB = 9; // \t
const CODE_CR = 13; // \r

/** Is the code unit an ASCII whitespace character (space, tab, newline, CR, FF, VT)? */
function isWs(code) {
  return code === CODE_SPACE || code === CODE_TAB || code === CODE_NEWLINE || code === CODE_CR || code === 12 || code === 11;
}

/** Is the code unit a space or a tab? */
function isSpaceOrTab(code) {
  return code === CODE_SPACE || code === CODE_TAB;
}

/** Unicode punctuation or symbol class, used for flanking and escapes. */
const RE_PUNCT = /[\p{P}\p{S}]/u;
/** A single character that counts as punctuation-or-space but is not * or _ . */
const RE_PUNCT_SPACE = /^((?![*_])[\s\p{P}\p{S}])/u;
/** A single alphanumeric character (Unicode letter or number). */
const RE_ALNUM = /[\p{L}\p{N}]/u;

/** Test whether the single character `ch` is Unicode punctuation/symbol. */
function isPunct(ch) {
  return RE_PUNCT.test(ch);
}

/** Test whether the single character `ch` is punctuation/space and not * or _. */
function isPunctSpace(ch) {
  return ch !== '' && RE_PUNCT_SPACE.test(ch);
}

/** ASCII punctuation, the set a backslash can escape. */
function isAsciiPunct(code) {
  return (code >= 33 && code <= 47) || (code >= 58 && code <= 64) ||
    (code >= 91 && code <= 96) || (code >= 123 && code <= 126);
}

/** Remove trailing occurrences of the character `ch` from `s`. */
function rtrimChar(s, ch) {
  let n = s.length;
  while (n > 0 && s.charCodeAt(n - 1) === ch) n--;
  return s.slice(0, n);
}

// ---------------------------------------------------------------------------
// Escaping and entity handling
// ---------------------------------------------------------------------------

const HTML_ESCAPES = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };

/**
 * Escape a string for HTML. With `encode`, every & < > " ' is escaped.
 * Without it, an & that already begins a character reference (&name;,
 * &#123; or &#x1f;) is left alone, and so are < > " ' handled the same way
 * marked does: < > " ' are always escaped, & only when it is not part of
 * a reference. Returns the input unchanged when nothing needs escaping.
 */
function escapeHtml(s, encode) {
  let out = null;
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    let rep = null;
    if (c === CODE_LT) rep = '&lt;';
    else if (c === CODE_GT) rep = '&gt;';
    else if (c === CODE_QUOT) rep = '&quot;';
    else if (c === CODE_APOS) rep = '&#39;';
    else if (c === CODE_AMP) {
      if (encode) rep = '&amp;';
      else if (!isEntityStart(s, i)) rep = '&amp;';
    }
    if (rep !== null) {
      if (out === null) out = '';
      out += s.slice(start, i) + rep;
      start = i + 1;
    }
  }
  if (out === null) return s;
  return out + s.slice(start);
}

/** Does a character reference start at `s[i]` (which is &)? */
function isEntityStart(s, i) {
  // &#123; or &#x1f; or &name;
  let j = i + 1;
  if (j < s.length && s.charCodeAt(j) === 35) { // #
    j++;
    if (j < s.length && (s.charCodeAt(j) === 120 || s.charCodeAt(j) === 88)) { // x X
      j++;
      const st = j;
      while (j < s.length && isHexDigit(s.charCodeAt(j))) j++;
      return j > st && j - st <= 6 && j < s.length && s.charCodeAt(j) === 59;
    }
    const st = j;
    while (j < s.length && s.charCodeAt(j) >= 48 && s.charCodeAt(j) <= 57) j++;
    return j > st && j - st <= 7 && j < s.length && s.charCodeAt(j) === 59;
  }
  let k = j;
  while (k < s.length) {
    const c = s.charCodeAt(k);
    if ((c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) || c === 95) k++;
    else break;
  }
  return k > j && k < s.length && s.charCodeAt(k) === 59;
}

function isHexDigit(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 70) || (c >= 97 && c <= 102);
}

const RE_NUMERIC_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

/**
 * Decode numeric character references (&#65; &#x41;) in a string, turning
 * a bare & into &amp; at the same time, exactly when the string holds at
 * least one numeric reference. Named references are left untouched.
 */
function decodeNumericEntities(s) {
  if (s.indexOf('&#') === -1) return s;
  RE_NUMERIC_REF.lastIndex = 0;
  return s.replace(RE_NUMERIC_REF, (whole, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec !== undefined ? parseInt(dec, 10) : parseInt(hex, 16);
    if (code === 0 || code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF)) return '\uFFFD';
    if (code === 38) return '&amp;';
    return String.fromCodePoint(code);
  });
}

// ---------------------------------------------------------------------------
// Link-label and URL helpers
// ---------------------------------------------------------------------------

/** Collapse a link label for lookup: trim, one space per whitespace run, case-fold. */
function normalizeLabel(s) {
  return s.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

/** Backslash-escaped punctuation loses its backslash: \* becomes *. */
const RE_BACKSLASH_PUNCT = /\\([\p{P}\p{S}])/gu;
function unescapePunct(s) {
  if (s.indexOf('\\') === -1) return s;
  RE_BACKSLASH_PUNCT.lastIndex = 0;
  return s.replace(RE_BACKSLASH_PUNCT, '$1');
}

/** encodeURI a link destination, keeping % as %, or null when it cannot be encoded. */
function encodeHref(s) {
  try {
    return encodeURI(s).replace(/%25/g, '%');
  } catch {
    return null;
  }
}

/** Expand tabs in `s` to spaces, tab stops every 4 columns starting at `col`. */
function expandTabs(s, col) {
  let out = '';
  let c = col;
  for (let i = 0; i < s.length; i++) {
    if (s.charCodeAt(i) === CODE_TAB) {
      const n = 4 - (c % 4);
      out += '    '.slice(0, n);
      c += n;
    } else {
      out += s[i];
      c++;
    }
  }
  return out;
}

/** Drop trailing blank lines, keeping the last one or two lines untouched. */
function trimBlankTail(s) {
  const lines = s.split('\n');
  let t = lines.length - 1;
  while (t >= 0 && /^[ \t]*$/.test(lines[t])) t--;
  if (lines.length - t <= 2) return s;
  return lines.slice(0, t + 1).join('\n');
}

/** Count unescaped parentheses in `s`: -1 when balanced, -2 when an opener is unclosed, else the index of the extra closer. */
function parenBalance(s) {
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c === CODE_BACKSLASH) { i++; continue; }
    if (c === CODE_LPAREN) depth++;
    else if (c === CODE_RPAREN) {
      depth--;
      if (depth < 0) return i;
    }
  }
  return depth > 0 ? -2 : -1;
}

// ---------------------------------------------------------------------------
// Inline parsing
// ---------------------------------------------------------------------------
//
// The inline pass walks one string (a paragraph, heading, table cell, ...)
// and produces a flat list of small tokens, tried in this order at each
// position: escape, raw HTML tag, link, reference link, emphasis, code span,
// hard break, strikethrough, autolink, extended autolink, then plain text.
// Link labels are tokenised recursively, with the parser state saved and
// restored around them, so a link cannot contain another link.

/** Match an escape: backslash followed by ASCII punctuation. */
function matchEscape(src, pos) {
  if (src.charCodeAt(pos) === CODE_BACKSLASH && pos + 1 < src.length && isAsciiPunct(src.charCodeAt(pos + 1))) {
    return { raw: src.slice(pos, pos + 2), text: src[pos + 1], end: pos + 2 };
  }
  return null;
}

/** Match a code span starting at `pos` (which holds a backtick). Returns its end index or -1. */
function matchCodeSpan(src, pos) {
  let k = 0;
  while (pos + k < src.length && src.charCodeAt(pos + k) === CODE_BACKTICK) k++;
  if (k === 0) return -1;
  // Find the next backtick run of exactly k backticks, after at least one content char.
  let j = pos + k + 1;
  while (j < src.length) {
    if (src.charCodeAt(j) !== CODE_BACKTICK) { j++; continue; }
    let m = 0;
    while (j + m < src.length && src.charCodeAt(j + m) === CODE_BACKTICK) m++;
    if (m === k) return j + m;
    j += m;
  }
  return -1;
}

/** The text of a code span: newlines become spaces, one space is trimmed off each end when both ends have one. */
function codeSpanText(src, start, end) {
  let s = src.slice(start, end);
  if (s.indexOf('\n') !== -1) s = s.replace(/\n/g, ' ');
  if (s.length >= 2 && s.charCodeAt(0) === CODE_SPACE && s.charCodeAt(s.length - 1) === CODE_SPACE && /[^ ]/.test(s)) {
    s = s.slice(1, -1);
  }
  return s;
}

// Inline HTML tag, autolink and extended-autolink patterns (sticky: they
// anchor at the scan position through lastIndex).
const RE_INLINE_TAG = /<!--(?:-?>|[\s\S]*?-->)|<\/[a-zA-Z][a-zA-Z0-9-]*\s*>|<[a-zA-Z][a-zA-Z0-9-]*(?:\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?)*\s*\/?>|<\?[\s\S]*?\?>|<![a-zA-Z]+\s[\s\S]*?>|<!\[CDATA\[[\s\S]*?\]\]>/y;
const RE_AUTOLINK = /<((?:[a-zA-Z][a-zA-Z0-9+.-]{1,31}):[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/y;
const RE_URL_SCHEME = /^(?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\/\//;
const RE_URL = /(?:mailto:[a-zA-Z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])|xmpp:[a-zA-Z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])(?:\/[A-Za-z0-9@.]+)?|((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\/\/|www\.)(?:[a-zA-Z0-9-]+\.?)+[^\s<]*|[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-]))/y;
const RE_BACKPEDAL = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;

/** Trim trailing punctuation off an extended autolink, the way the backpedal rule does. */
function backpedal(s) {
  let cur = s;
  for (;;) {
    RE_BACKPEDAL.lastIndex = 0;
    const m = RE_BACKPEDAL.exec(cur);
    const next = m ? m[0] : '';
    if (next === cur) return cur;
    cur = next;
  }
}

/** Is there a hard break (two spaces, or a backslash, before a newline) at `pos`? Returns its end index or -1. */
function matchBr(src, pos) {
  let i = pos;
  if (src.charCodeAt(i) === CODE_BACKSLASH) i++;
  else {
    let n = 0;
    while (i < src.length && src.charCodeAt(i) === CODE_SPACE) { i++; n++; }
    if (n < 2) return -1;
  }
  if (i >= src.length || src.charCodeAt(i) !== CODE_NEWLINE) return -1;
  // The break only counts when non-whitespace follows it somewhere.
  let j = i + 1;
  while (j < src.length && isWs(src.charCodeAt(j))) j++;
  if (j >= src.length) return -1;
  i++;
  while (i < src.length && isSpaceOrTab(src.charCodeAt(i))) i++;
  return i;
}

// ---------------------------------------------------------------------------
// Emphasis and strikethrough delimiter matching
// ---------------------------------------------------------------------------
//
// A delimiter run can open emphasis when the character after it is
// punctuation, or there is no character before it, or the character before
// it is punctuation. The search for a closer then walks forward with the
// right-delimiter pattern, applying the odd-match rule (a run that can both
// open and close is skipped when the two run lengths add to a multiple of
// three) and the "leftover" accounting for runs of different lengths.

const RE_EM_L_DELIM = /(?:\*+(?:((?!\*)(?!~)[\p{P}\p{S}])|([^\s*]))?)|(?:_+(?:((?!_)(?!~)[\p{P}\p{S}])|([^\s_]))?)/yu;
const RE_EM_R_DELIM_AST = /^[^_*]*?__[^_*]*?\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\*)(?!~)[\p{P}\p{S}](\*+)(?=[\s]|$)|(?:[^\s\p{P}\p{S}]|~)(\*+)(?!\*)(?=(?!~)[\s\p{P}\p{S}]|$)|(?!\*)(?!~)[\s\p{P}\p{S}](\*+)(?=(?:[^\s\p{P}\p{S}]|~))|[\s](\*+)(?!\*)(?=(?!~)[\p{P}\p{S}])|(?!\*)(?!~)[\p{P}\p{S}](\*+)(?!\*)(?=(?!~)[\p{P}\p{S}])|(?:[^\s\p{P}\p{S}]|~)(\*+)(?=(?:[^\s\p{P}\p{S}]|~))/gu;
const RE_EM_R_DELIM_UND = /^[^_*]*?\*\*[^_*]*?_[^_*]*?(?=\*\*)|[^_]+(?=[^_])|(?!_)[\p{P}\p{S}](_+)(?=[\s]|$)|[^\s\p{P}\p{S}](_+)(?!_)(?=[\s\p{P}\p{S}]|$)|(?!_)[\s\p{P}\p{S}](_+)(?=[^\s\p{P}\p{S}])|[\s](_+)(?!_)(?=[\p{P}\p{S}])|(?!_)[\p{P}\p{S}](_+)(?!_)(?=[\p{P}\p{S}])/gu;
const RE_EM_R_ALT1_AST = /[^_*]*?__[^_*]*?\*[^_*]*?(?=__)/y;
const RE_EM_R_ALT1_UND = /[^_*]*?\*\*[^_*]*?_[^_*]*?(?=\*\*)/y;
const RE_DEL_L_DELIM = /~~?(?:((?!~)[\p{P}\p{S}])|([^\s~]))/yu;
const RE_DEL_R_DELIM = /^[^~]+(?=[^~])|(?!~)[\p{P}\p{S}](~~?)(?=[\s]|$)|[^\s\p{P}\p{S}](~~?)(?!~)(?=[\s\p{P}\p{S}]|$)|(?!~)[\s\p{P}\p{S}](~~?)(?=[^\s\p{P}\p{S}])|[\s](~~?)(?!~)(?=[\p{P}\p{S}])|(?!~)[\p{P}\p{S}](~~?)(?!~)(?=[\p{P}\p{S}])|[^\s\p{P}\p{S}](~~?)(?=[^\s\p{P}\p{S}])/gu;

/** The code point ending just before index `i` ("" at the start). */
function codePointBefore(src, i) {
  if (i <= 0) return '';
  const lo = src.charCodeAt(i - 1);
  if (lo >= 0xDC00 && lo <= 0xDFFF && i >= 2) {
    const hi = src.charCodeAt(i - 2);
    if (hi >= 0xD800 && hi <= 0xDBFF) return src.slice(i - 2, i);
  }
  return src[i - 1];
}

/** Length of a string in code points. */
function codePointLength(s) {
  let n = 0;
  for (const _ch of s) n++;
  return n;
}

/**
 * Try to read * or _ emphasis starting at `pos`. `prev` is the last code
 * unit of the preceding text token ("" when there is none). Returns the
 * token ({type, raw, text}) or null.
 */
function tryEmStrong(src, masked, pos, prev, ctx, bound) {
  RE_EM_L_DELIM.lastIndex = pos;
  const s = RE_EM_L_DELIM.exec(src);
  if (!s || (!s[1] && !s[2] && !s[3] && !s[4])) return null;
  const delim = src[pos];
  const samePrev = prev === delim;
  // Start of the delimiter run (the scan may begin mid-run).
  let l = pos;
  while (l > 0 && src[l - 1] === delim) l--;
  const beforeRun = codePointBefore(src, l);
  const beforeIsPunct = beforeRun === '*' || beforeRun === '_' || isPunctSpace(beforeRun);
  let n = prev;
  if (l < pos) n = beforeRun;
  const u = l < pos ? beforeIsPunct : isPunctSpace(n);
  if (s[4] && RE_ALNUM.test(n)) return null;
  const d = s[1] || s[3] || '';
  // Left-flanking gate: bail only when followed by punctuation, preceded by
  // a non-punctuation character, and that character is not punctuation.
  if (d && n && !u) return null;
  {
    // Length of the opening run, in code points (the match is the run plus one following char).
    const k = codePointLength(s[0]) - 1;
    const canBoth = beforeRun !== '' && beforeRun.trim() !== '' && (d !== '' || (delim === '*' && !beforeIsPunct));
    let m = k;
    let f = 0;
    const y = (pos - l) + k;
    const R = delim === '*' ? RE_EM_R_DELIM_AST : RE_EM_R_DELIM_UND;
    const alt1 = delim === '*' ? RE_EM_R_ALT1_AST : RE_EM_R_ALT1_UND;
    // The closer search stops at the last position where a closer for this
    // delimiter can occur (the mask bound). No closer can follow the opener
    // run's end when that bound is before it.
    const v = bound[delim];
    const Q = pos + k;
    if (v < Q) return null;
    let scan = pos + k;
    // The first alternative of the closer pattern only applies at the scan
    // start: it keeps a closer from being read across a __ or ** span.
    // The closer search runs on the masked string.
    alt1.lastIndex = scan;
    const a1 = alt1.exec(masked);
    if (a1) scan = alt1.lastIndex;
    R.lastIndex = scan;
    let match;
    while ((match = R.exec(masked)) !== null) {
      if (match.index > v) break;
      const g = match[1] || match[2] || match[3] || match[4] || match[5] || match[6] || '';
      if (!g) continue;
      let b = codePointLength(g);
      if (match[3] || match[4]) { m += b; continue; }
      if (match[5] || match[6] || canBoth) {
        if (samePrev && (match[5] || match[6])) break;
        if (y % 3 !== 0 && (y + b) % 3 === 0) { f += b; continue; }
      }
      m -= b;
      if (m > 0) continue;
      b = Math.min(b, b + m + f);
      const firstLen = [...match[0]][0].length;
      const raw = src.slice(pos, pos + k + (match.index - (pos + k)) + firstLen + b);
      if (Math.min(k, b) % 2 === 1) {
        const inner = raw.slice(1, -1);
        return { type: 'em', raw, text: inner, _inner: inner };
      }
      const inner = raw.slice(2, -2);
      return { type: 'strong', raw, text: inner, _inner: inner };
    }
  }
  return null;
}

/**
 * Try to read ~~ strikethrough starting at `pos`. Same shape as emphasis,
 * with its own delimiter rules. Returns the token or null.
 */
function tryDel(src, masked, pos, prev, ctx, bound) {
  RE_DEL_L_DELIM.lastIndex = pos;
  const s = RE_DEL_L_DELIM.exec(src);
  if (!s) return null;
  // It can open when the character after the run is not punctuation, or
  // there is no character before it, or the character before it is
  // punctuation-or-space.
  if (s[1] && prev && !isPunctSpace(prev)) return null;
  const runLen = codePointLength(s[0]) - 1; // the ~~ or ~ run (match is run plus one char)
  let p = runLen;
  // The closer search stops at the last position where a ~ closer can occur.
  const v = bound['~'];
  const Q = pos + runLen;
  if (v < Q) return null;
  let scan = pos + runLen;
  RE_DEL_R_DELIM.lastIndex = scan;
  let match;
  while ((match = RE_DEL_R_DELIM.exec(masked)) !== null) {
    if (match.index > v) break;
    const g = match[1] || match[2] || match[3] || match[4] || match[5] || match[6] || '';
    if (!g) continue;
    const b = codePointLength(g);
    if (b !== runLen) continue;
    if (match[3] || match[4]) { p += b; continue; }
    p -= b;
    if (p > 0) continue;
    const bb = Math.min(b, b + p);
    const firstLen = [...match[0]][0].length;
    const raw = src.slice(pos, pos + runLen + (match.index - (pos + runLen)) + firstLen + bb);
    const inner = raw.slice(runLen, -runLen);
    return { type: 'del', raw, text: inner, _inner: inner };
  }
  return null;
}

// ---------------------------------------------------------------------------
// Link labels and destinations
// ---------------------------------------------------------------------------

/**
 * Scan a bracketed group starting at `j` (src[j] is '['). Level 1 groups
 * may hold one more level of brackets; level 2 groups may not. Returns the
 * index just past the closing ']' or -1.
 */
function scanBracketGroup(src, j, level) {
  let k = j + 1;
  const len = src.length;
  while (k < len) {
    const c = src.charCodeAt(k);
    if (c === CODE_BACKSLASH) { k += 2; continue; }
    if (c === CODE_RBRACK) return k + 1;
    if (c === CODE_LBRACK) {
      if (level === 2) return -1;
      const inner = scanBracketGroup(src, k, 2);
      if (inner === -1) return -1;
      k = inner;
      continue;
    }
    k++;
  }
  return -1;
}

/**
 * Scan a link label (the [...] of an inline or reference link) starting
 * just after its '['. Nested bracket groups and code spans are consumed as
 * units; a bare ']' ends the label. Returns {end, label} with end the index
 * of the closing ']', or null.
 */
function scanLabelRe(src, i) {
  let j = i;
  const len = src.length;
  while (j < len) {
    const c = src.charCodeAt(j);
    if (c === CODE_BACKSLASH) { j += 2; continue; }
    if (c === CODE_LBRACK) {
      const g = scanBracketGroup(src, j, 1);
      if (g === -1) return null;
      j = g;
      continue;
    }
    if (c === CODE_BACKTICK) {
      // The `` ``+(?=\]) `` alternative is tried before the code span:
      // the label pattern is lazy, so a run of two or more backticks
      // right before ']' closes the label there, not inside a code span.
      let m = 0;
      while (j + m < len && src.charCodeAt(j + m) === CODE_BACKTICK) m++;
      if (m >= 2 && j + m < len && src.charCodeAt(j + m) === CODE_RBRACK) { j += m; continue; }
      const cs = matchLabelCodeSpan(src, j);
      if (cs !== -1) { j = cs; continue; }
      return null;
    }
    if (c === CODE_RBRACK) return { end: j, label: src.slice(i, j) };
    j++;
  }
  return null;
}

/**
 * Scan a reference label (the [...] of a shortcut or collapsed reference,
 * or the second [...] of a full reference). No nesting, and a newline is
 * allowed only when the next line is not blank. Returns {end, text} with
 * end the index of the closing ']', or null.
 */
function scanLabelLe(src, i) {
  const len = src.length;
  if (i >= len) return null;
  let k = i;
  while (k < len && isWs(src.charCodeAt(k))) k++;
  if (k < len && src.charCodeAt(k) === CODE_RBRACK) return null;
  let j = i;
  while (j < len) {
    const c = src.charCodeAt(j);
    if (c === CODE_BACKSLASH) { j += 2; continue; }
    if (c === CODE_LBRACK || c === CODE_RBRACK) break;
    if (c === CODE_NEWLINE) {
      let m = j + 1;
      while (m < len && isSpaceOrTab(src.charCodeAt(m))) m++;
      if (m >= len || src.charCodeAt(m) === CODE_NEWLINE) break;
      j++;
      continue;
    }
    j++;
  }
  if (j < len && src.charCodeAt(j) === CODE_RBRACK) return { end: j, text: src.slice(i, j) };
  return null;
}

/**
 * Does the label hold a '<' that begins a tag or autolink reaching past the
 * label's end? Such a label can never be a link.
 */
function labelHasOpenTag(src, label, offset) {
  if (label.indexOf('<') === -1) return false;
  for (let s = 0; s < label.length; s++) {
    if (label.charCodeAt(s) === CODE_BACKSLASH) { s++; continue; }
    if (label.charCodeAt(s) === CODE_BACKTICK) {
      const cs = matchCodeSpan(label, s);
      if (cs !== -1) { s = cs - 1; continue; }
    }
    if (label.charCodeAt(s) !== CODE_LT) continue;
    const rest = src.slice(offset + s);
    const tagLen = matchInlineTag(rest, 0);
    const auto = tagLen === -1 ? matchAutolink(rest, 0) : null;
    const hit = tagLen !== -1 ? tagLen : (auto ? auto.end : -1);
    if (hit !== -1) {
      if (hit > label.length - s) return true;
      s += hit - 1;
    }
  }
  return false;
}

/** Match an inline HTML tag at `pos`; returns its end index or -1. */
function matchInlineTag(src, pos) {
  RE_INLINE_TAG.lastIndex = pos;
  const m = RE_INLINE_TAG.exec(src);
  return m ? RE_INLINE_TAG.lastIndex : -1;
}

/** Match an autolink <...> at `pos`; returns {end, text, href} or null. */
function matchAutolink(src, pos) {
  RE_AUTOLINK.lastIndex = pos;
  const m = RE_AUTOLINK.exec(src);
  if (!m) return null;
  const text = m[1];
  return { end: RE_AUTOLINK.lastIndex, text, href: m[2] === '@' ? 'mailto:' + text : text };
}

/** Is the code unit an email-address character? */
function isEmailCharCode(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) ||
    c === 46 || c === 33 || c === 35 || c === 36 || c === 37 || c === 38 || c === 39 ||
    c === 42 || c === 43 || c === 47 || c === 61 || c === 63 || c === 94 || c === 95 ||
    c === 96 || c === 123 || c === 124 || c === 125 || c === 126 || c === 45;
}

/** Does an email address (word characters then @) start at `j`? */
function isEmailStartAt(src, j) {
  let k = j;
  while (k < src.length && isEmailCharCode(src.charCodeAt(k))) k++;
  return k > j && k < src.length && src.charCodeAt(k) === 64;
}

/** Is the code unit an ASCII letter or digit? */
function isAlnumCode(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
}

/** Does a URL scheme (http://, https://, ftp://) start at `j`, any case? */
function isProtocolAt(src, j) {
  const c = src.charCodeAt(j);
  if (c === 104 || c === 72) {
    return src.slice(j + 1, j + 7).toLowerCase() === 'ttp://' ||
      src.slice(j + 1, j + 8).toLowerCase() === 'ttps://';
  }
  if (c === 102 || c === 70) return src.slice(j + 1, j + 6).toLowerCase() === 'tp://';
  return false;
}

/** Does `src` hold two or more spaces then a newline starting at `j`? */
function hasHardBreakSpaces(src, j) {
  let k = j;
  let n = 0;
  while (k < src.length && src.charCodeAt(k) === CODE_SPACE) { k++; n++; }
  return n >= 2 && k < src.length && src.charCodeAt(k) === CODE_NEWLINE;
}

/**
 * Where does the plain-text run starting at `pos` end? Text stops before
 * a backslash, a tag start, a link start, a code span, emphasis, a
 * strikethrough, an underscore at a word boundary, a URL scheme, a www.
 * start or an email address, and before a hard break, leaving the break's
 * spaces for the break tokeniser.
 */
function scanTextEnd(src, pos) {
  const len = src.length;
  if (pos >= len) return pos;
  const c0 = src.charCodeAt(pos);
  // A lone non-alphanumeric character right before mailto: or xmpp: is its own token.
  if (!isAlnumCode(c0) && (src.startsWith('mailto:', pos + 1) || src.startsWith('xmpp:', pos + 1))) return pos + 1;
  let i = pos;
  if (c0 === CODE_BACKTICK || c0 === CODE_TILDE) {
    while (i < len && src.charCodeAt(i) === c0) i++;
  } else {
    i++;
  }
  for (let j = i; j <= len; j++) {
    if (j === len) return len;
    const c = src.charCodeAt(j);
    if (c === CODE_BACKSLASH || c === CODE_LT || c === 33 || c === CODE_LBRACK ||
      c === CODE_BACKTICK || c === CODE_STAR || c === CODE_TILDE || c === CODE_UNDER) return j;
    if (c === CODE_SPACE && hasHardBreakSpaces(src, j)) return j;
    // A protocol, www. or mailto:/xmpp: can only start at its first letter.
    if (c === 104 || c === 72 || c === 102 || c === 70) {
      if (isProtocolAt(src, j)) return j;
    }
    if (c === 119 && src.startsWith('www.', j)) {
      const prev = j === 0 ? '' : src[j - 1];
      if (j === 0 || prev === ' ' || prev === '\t' || prev === '\n' || prev === '\r' || prev === '*' || prev === '_' || prev === '~' || prev === '(') return j;
    }
    // An email address can only start at the first email character of a run.
    if (isEmailCharCode(c) && (j === i || !isEmailCharCode(src.charCodeAt(j - 1)))) {
      if (isEmailStartAt(src, j)) return j;
    }
    if (c !== CODE_SPACE && hasHardBreakSpaces(src, j + 1)) return j + 1;
    if (!isAlnumCode(c)) {
      const n1 = j + 1 < len ? src.charCodeAt(j + 1) : 0;
      if ((n1 === 109 || n1 === 120) && (src.startsWith('mailto:', j + 1) || src.startsWith('xmpp:', j + 1))) return j + 1;
      if (!isEmailCharCode(c) && isEmailCharCode(n1) && isEmailStartAt(src, j + 1)) return j + 1;
    }
  }
  return len;
}

// ---------------------------------------------------------------------------
// Links
// ---------------------------------------------------------------------------

/** Skip spaces, tabs and newlines starting at `j`. */
function skipBlank(src, j) {
  while (j < src.length) {
    const c = src.charCodeAt(j);
    if (c === CODE_SPACE || c === CODE_TAB || c === CODE_NEWLINE) j++;
    else break;
  }
  return j;
}

/**
 * Try to read a link title at `k` (after the destination). The title must
 * follow a separator of spaces/tabs, optionally spanning one newline, and
 * be double-quoted, single-quoted or parenthesised. Returns {title, end}
 * with end just past the closing quote, or null.
 */
function tryTitle(src, k) {
  const len = src.length;
  let m = k;
  if (m < len && isSpaceOrTab(src.charCodeAt(m))) {
    while (m < len && isSpaceOrTab(src.charCodeAt(m))) m++;
    if (m < len && src.charCodeAt(m) === CODE_NEWLINE) {
      m++;
      while (m < len && isSpaceOrTab(src.charCodeAt(m))) m++;
    }
  } else if (m < len && src.charCodeAt(m) === CODE_NEWLINE) {
    m++;
    while (m < len && isSpaceOrTab(src.charCodeAt(m))) m++;
  } else {
    return null;
  }
  if (m >= len) return null;
  const q = src.charCodeAt(m);
  if (q === CODE_QUOT) {
    let j = m + 1;
    while (j < len) {
      const c = src.charCodeAt(j);
      if (c === CODE_BACKSLASH) { j += 2; continue; }
      if (c === CODE_QUOT) return { title: src.slice(m + 1, j), end: j + 1 };
      j++;
    }
    return null;
  }
  if (q === CODE_APOS) {
    let j = m + 1;
    while (j < len) {
      const c = src.charCodeAt(j);
      if (c === CODE_BACKSLASH) { j += 2; continue; }
      if (c === CODE_APOS) return { title: src.slice(m + 1, j), end: j + 1 };
      if (c === CODE_NEWLINE) {
        if (j + 1 < len && src.charCodeAt(j + 1) === CODE_NEWLINE) return null;
        j++;
        continue;
      }
      j++;
    }
    return null;
  }
  if (q === CODE_LPAREN) {
    let j = m + 1;
    while (j < len) {
      const c = src.charCodeAt(j);
      if (c === CODE_BACKSLASH) { j += 2; continue; }
      if (c === CODE_RPAREN) return { title: src.slice(m + 1, j), end: j + 1 };
      if (c === CODE_LPAREN) return null;
      j++;
    }
    return null;
  }
  return null;
}

/**
 * Build a link or image token from its parts, tokenising the label text
 * with the parser state saved around it: a link inside the label stops the
 * outer link from forming at all.
 */
function buildLink(kind, raw, href, title, labelText, ctx, parenPossible) {
  const savedInLink = ctx.inLink;
  const savedEmitted = ctx.linkEmitted;
  const savedRawBlock = ctx.inRawBlock;
  ctx.inLink = true;
  ctx.linkEmitted = false;
  const inner = inlineTokens(labelText, ctx, parenPossible && labelText.indexOf(')') !== -1);
  const emittedInside = ctx.linkEmitted;
  ctx.linkEmitted = savedEmitted;
  ctx.inLink = savedInLink;
  if (kind === 'link') {
    if (emittedInside) {
      ctx.inRawBlock = savedRawBlock;
      return null;
    }
    ctx.linkEmitted = true;
  }
  return { type: kind, raw, href, title, text: labelText, tokens: inner };
}

/**
 * Try to read an inline link or image starting at `pos`. Returns
 * {token, end} or null.
 */
function tryLink(src, pos, ctx, parenPossible) {
  if (!parenPossible) return null;
  const len = src.length;
  let i = pos;
  let kind = 'link';
  if (src.charCodeAt(i) === 33) { // !
    kind = 'image';
    i++;
    if (i >= len || src.charCodeAt(i) !== CODE_LBRACK) return null;
  } else if (src.charCodeAt(i) !== CODE_LBRACK) {
    return null;
  }
  const lab = scanLabelRe(src, i + 1);
  if (!lab) return null;
  let j = lab.end + 1;
  if (j >= len || src.charCodeAt(j) !== CODE_LPAREN) return null;
  if (labelHasOpenTag(src, lab.label, i + 1)) return null;
  j++;
  j = skipBlank(src, j);
  const destStart = j;
  // Destination in angle brackets: <...> first, then a bare run, then
  // empty before ')'. When the bracketed form matches but the rest of the
  // link does not follow, the bare form is tried from the same spot.
  if (j < len && src.charCodeAt(j) === CODE_LT) {
    let k = j + 1;
    let closed = -1;
    while (k < len) {
      const c = src.charCodeAt(k);
      if (c === CODE_BACKSLASH) { k += 2; continue; }
      if (c === CODE_GT) { closed = k; break; }
      if (c === CODE_LT || c === CODE_NEWLINE) break;
      k++;
    }
    if (closed !== -1) {
      const href = src.slice(j, closed + 1);
      const tail = parseDestTail(src, closed + 1);
      if (tail) {
        return finishLink(src, pos, kind, lab.label, href, tail.title, tail.endPos, destStart, ctx, parenPossible);
      }
    }
  }
  // Bare destination: a run of characters that are not space, tab,
  // newline or a control character.
  let e1 = j;
  while (e1 < len) {
    const c = src.charCodeAt(e1);
    if (c === CODE_SPACE || c === CODE_TAB || c === CODE_NEWLINE || c < 0x20) break;
    e1++;
  }
  if (e1 === j) {
    if (j < len && src.charCodeAt(j) === CODE_RPAREN) {
      return finishLink(src, pos, kind, lab.label, '', null, j + 1, destStart, ctx, parenPossible);
    }
    return null;
  }
  const run = src.slice(j, e1);
  const tail = parseDestTail(src, e1);
  if (tail) {
    return finishLink(src, pos, kind, lab.label, run, tail.title, tail.endPos, destStart, ctx, parenPossible);
  }
  const lastParen = run.lastIndexOf(')');
  if (lastParen === -1) return null;
  return finishLink(src, pos, kind, lab.label, run.slice(0, lastParen), null, j + lastParen + 1, destStart, ctx, parenPossible);
}

/**
 * After a destination, read an optional title and the closing ')'. The
 * title is tried first; without one, spaces and then ')' must follow.
 * Returns {title, endPos} or null.
 */
function parseDestTail(src, hrefEnd) {
  const len = src.length;
  const t = tryTitle(src, hrefEnd);
  if (t) {
    const m = skipBlank(src, t.end);
    if (m < len && src.charCodeAt(m) === CODE_RPAREN) return { title: t.title, endPos: m + 1 };
  }
  const m = skipBlank(src, hrefEnd);
  if (m < len && src.charCodeAt(m) === CODE_RPAREN) return { title: null, endPos: m + 1 };
  return null;
}

/** Apply the destination checks and build the token, or null. */
function finishLink(src, pos, kind, label, href, title, endPos, hrefStart, ctx, parenPossible) {
  const s = href.trim();
  if (s.charCodeAt(0) === CODE_LT) {
    if (s.charCodeAt(s.length - 1) !== CODE_GT) return null;
    const stripped = rtrimChar(s.slice(0, -1), CODE_BACKSLASH);
    if ((s.length - stripped.length) % 2 === 0) return null;
  } else if (s !== '') {
    const bal = parenBalance(href);
    if (bal === -2) return null;
    if (bal > -1) {
      href = href.slice(0, bal);
      title = null;
      endPos = hrefStart + bal + 1;
    }
  }
  const raw = src.slice(pos, endPos);
  const noClose = rtrimChar(raw.slice(0, -1), CODE_BACKSLASH);
  if ((raw.length - noClose.length) % 2 === 0) return null;
  let dest = href.trim();
  if (dest.charCodeAt(0) === CODE_LT) dest = dest.slice(1, -1);
  const labelText = label.replace(/\\([\[\]])/g, '$1');
  const token = buildLink(kind, raw, dest ? unescapePunct(dest) : dest,
    title ? unescapePunct(title) : (title === '' ? '' : title), labelText, ctx, parenPossible);
  return token ? { token, end: endPos } : null;
}

/**
 * Try to read a reference link starting at `pos`. Returns {token, end} for
 * a link, or {text, end} for the single-character fallback when the
 * reference is undefined, or null.
 */
function tryReflink(src, pos, ctx, parenPossible) {
  const len = src.length;
  let i = pos;
  let kind = 'link';
  if (src.charCodeAt(i) === 33) {
    kind = 'image';
    i++;
    if (i >= len || src.charCodeAt(i) !== CODE_LBRACK) return null;
  } else if (src.charCodeAt(i) !== CODE_LBRACK) {
    return null;
  }
  // Full reference: [label][ref]
  const lab = scanLabelRe(src, i + 1);
  if (lab) {
    const after = lab.end + 1;
    if (after < len && src.charCodeAt(after) === CODE_LBRACK) {
      const ref = scanLabelLe(src, after + 1);
      if (ref) {
        const end = ref.end + 1;
        if (labelHasOpenTag(src, lab.label, i + 1)) return null;
        const key = normalizeLabel(ref.text || lab.label);
        const def = ctx.links[key];
        if (!def) {
          const ch = src[pos];
          return { text: { type: 'text', raw: ch, text: ch }, end: pos + 1 };
        }
        const labelText = lab.label.replace(/\\([\[\]])/g, '$1');
        const token = buildLink(kind, src.slice(pos, end), def.href, def.title, labelText, ctx, parenPossible);
        if (!token) return null;
        return { token, end };
      }
    }
  }
  // Shortcut or collapsed reference: [ref] or [ref][]
  const ref = scanLabelLe(src, i + 1);
  if (!ref) return null;
  let end = ref.end + 1;
  if (end + 1 < len && src.charCodeAt(end) === CODE_LBRACK && src.charCodeAt(end + 1) === CODE_RBRACK) end += 2;
  if (labelHasOpenTag(src, ref.text, i + 1)) return null;
  const key = normalizeLabel(ref.text);
  const def = ctx.links[key];
  if (!def) {
    const ch = src[pos];
    return { text: { type: 'text', raw: ch, text: ch }, end: pos + 1 };
  }
  const labelText = ref.text.replace(/\\([\[\]])/g, '$1');
  const token = buildLink(kind, src.slice(pos, end), def.href, def.title, labelText, ctx, parenPossible);
  if (!token) return null;
  return { token, end };
}

// ---------------------------------------------------------------------------
// The inline loop
// ---------------------------------------------------------------------------

/**
 * Tokenise one inline string. `ctx` carries the link definitions and the
 * in-link / in-raw-block state; `parenPossible` says whether a link
 * destination may follow (the string holds a ')').
 */
function inlineTokens(src, ctx, parenPossible) {
  const tokens = [];
  const len = src.length;
  let pos = 0;
  let prev = '';
  let prevWasText = false;
  // The masked string (escapes, code spans, links and tags neutralised)
  // is what the closer search runs on; the bound is its last possible
  // closer for each delimiter. When the string holds no emphasis or
  // strikethrough delimiter there is nothing to close, so the mask is
  // skipped entirely.
  const hasDelim = src.indexOf('*') !== -1 || src.indexOf('_') !== -1 || src.indexOf('~') !== -1;
  const masked = hasDelim ? maskInline(src, ctx.links) : src;
  const bound = hasDelim ? computeCloserBound(masked) : { '*': -1, '_': -1, '~': -1 };
  while (pos < len) {
    if (!prevWasText) prev = '';
    prevWasText = false;
    const before = pos;

    const esc = matchEscape(src, pos);
    if (esc) {
      tokens.push({ type: 'escape', raw: esc.raw, text: esc.text });
      pos = esc.end;
      continue;
    }

    const tagEnd = matchInlineTag(src, pos);
    if (tagEnd !== -1) {
      const raw = src.slice(pos, tagEnd);
      if (!ctx.inLink && /^<a /i.test(raw)) ctx.inLink = true;
      else if (ctx.inLink && /^<\/a>/i.test(raw)) ctx.inLink = false;
      if (!ctx.inRawBlock && /^<(pre|code|kbd|script)(\s|>)/i.test(raw)) ctx.inRawBlock = true;
      else if (ctx.inRawBlock && /^<\/(pre|code|kbd|script)(\s|>)/i.test(raw)) ctx.inRawBlock = false;
      tokens.push({ type: 'html', raw, inLink: ctx.inLink, inRawBlock: ctx.inRawBlock, block: false, text: raw });
      pos = tagEnd;
      continue;
    }

    if (parenPossible) {
      const link = tryLink(src, pos, ctx, parenPossible);
      if (link) {
        tokens.push(link.token);
        pos = link.end;
        continue;
      }
    }

    const ref = tryReflink(src, pos, ctx, parenPossible);
    if (ref) {
      if (ref.token) {
        tokens.push(ref.token);
        pos = ref.end;
      } else {
        const last = tokens.length ? tokens[tokens.length - 1] : null;
        if (last && last.type === 'text') {
          last.raw += ref.text.raw;
          last.text += ref.text.text;
        } else {
          tokens.push(ref.text);
        }
        pos = ref.end;
      }
      continue;
    }

    const em = tryEmStrong(src, masked, pos, prev, ctx, bound);
    if (em) {
      em.tokens = inlineTokens(em._inner, ctx, parenPossible && em._inner.indexOf(')') !== -1);
      delete em._inner;
      tokens.push(em);
      pos += em.raw.length;
      continue;
    }

    const csEnd = src.charCodeAt(pos) === CODE_BACKTICK ? matchCodeSpan(src, pos) : -1;
    if (csEnd !== -1) {
      let k = 0;
      while (src.charCodeAt(pos + k) === CODE_BACKTICK) k++;
      const raw = src.slice(pos, csEnd);
      tokens.push({ type: 'codespan', raw, text: codeSpanText(src, pos + k, csEnd - k) });
      pos = csEnd;
      continue;
    }

    const brEnd = matchBr(src, pos);
    if (brEnd !== -1) {
      tokens.push({ type: 'br', raw: src.slice(pos, brEnd) });
      pos = brEnd;
      continue;
    }

    const del = tryDel(src, masked, pos, prev, ctx, bound);
    if (del) {
      del.tokens = inlineTokens(del._inner, ctx, parenPossible && del._inner.indexOf(')') !== -1);
      delete del._inner;
      tokens.push(del);
      pos += del.raw.length;
      continue;
    }

    const auto = matchAutolink(src, pos);
    if (auto) {
      tokens.push({
        type: 'link', raw: src.slice(pos, auto.end), text: auto.text, href: auto.href,
        autolink: true, tokens: [{ type: 'text', raw: auto.text, text: auto.text }],
      });
      pos = auto.end;
      continue;
    }

    if (!ctx.inLink) {
      RE_URL.lastIndex = pos;
      const um = RE_URL.exec(src);
      if (um) {
        let text = backpedal(um[0]);
        let href;
        if (um[2] === '@') {
          href = 'mailto:' + text;
        } else if (um[1] === 'www.') {
          href = 'http://' + text;
        } else {
          href = text;
        }
        tokens.push({
          type: 'link', raw: text, text, href,
          autolink: true, tokens: [{ type: 'text', raw: text, text }],
        });
        pos += text.length;
        continue;
      }
    }

    const textEnd = scanTextEnd(src, pos);
    const raw = src.slice(pos, textEnd);
    const inRaw = ctx.inRawBlock;
    const tok = { type: 'text', raw, text: inRaw ? raw : decodeNumericEntities(raw), escaped: inRaw };
    const last = tokens.length ? tokens[tokens.length - 1] : null;
    if (last && last.type === 'text') {
      last.raw += tok.raw;
      last.text += tok.text;
    } else {
      tokens.push(tok);
    }
    if (raw.charCodeAt(raw.length - 1) !== CODE_UNDER) prev = raw[raw.length - 1];
    prevWasText = true;
    pos = textEnd;

    if (pos === before) throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
  }
  return tokens;
}

// ---------------------------------------------------------------------------
// Block parsing
// ---------------------------------------------------------------------------
//
// Blocks are read line by line from the current position, in the order
// marked tries them: blank lines, indented code, fenced code, ATX heading,
// thematic break, blockquote, list, HTML block, link definition, table,
// setext heading, paragraph, then a single text line. Link definitions are
// collected as they are found, and inline content is queued and tokenised
// only after the whole block pass, so a definition may appear after its
// first use.

/** Index of the newline ending the line that starts at `pos` (or the end). */
function lineEnd(src, pos) {
  const i = src.indexOf('\n', pos);
  return i === -1 ? src.length : i;
}

/** Start of the line after the one starting at `pos`. */
function nextLineStart(src, pos) {
  const e = lineEnd(src, pos);
  return e < src.length ? e + 1 : src.length;
}

/** Is the line blank (only spaces and tabs)? */
function isBlankLine(line) {
  for (let i = 0; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c !== CODE_SPACE && c !== CODE_TAB) return false;
  }
  return true;
}

/** Position of the first character that is not a space, or -1. */
function firstNonSpace(line) {
  for (let i = 0; i < line.length; i++) {
    if (line.charCodeAt(i) !== CODE_SPACE) return i;
  }
  return -1;
}

/** Expand the leading whitespace of a line, tab stops from column 0. */
function expandLeadingWs(line) {
  let i = 0;
  while (i < line.length && isSpaceOrTab(line.charCodeAt(i))) i++;
  if (i === 0) return line;
  return expandTabs(line.slice(0, i), 0) + line.slice(i);
}

/** Count leading spaces (at most `max`). */
function leadingSpaces(line, max) {
  let n = 0;
  while (n < line.length && n < max && line.charCodeAt(n) === CODE_SPACE) n++;
  return n;
}

// The block tags of HTML block type 6.
const BLOCK_TAGS = new Set(('address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h1|h2|h3|h4|h5|h6|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul').split('|'));

/** Does the line start a thematic break (three or more of -, _ or *)? */
function isHrLine(line) {
  let i = leadingSpaces(line, 3);
  if (i > 3) return false;
  if (i >= line.length) return false;
  const ch = line.charCodeAt(i);
  if (ch !== 45 && ch !== 95 && ch !== CODE_STAR) return false;
  let n = 0;
  for (; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c === ch) n++;
    else if (c === CODE_SPACE || c === CODE_TAB) continue;
    else return false;
  }
  return n >= 3;
}

/** Does the line start an ATX heading (up to three spaces, 1-6 #, then space or end)? */
function isAtxHeadingLine(line) {
  let i = leadingSpaces(line, 3);
  if (i > 3) return false;
  let n = 0;
  while (i < line.length && line.charCodeAt(i) === 35 && n < 6) { i++; n++; }
  if (n === 0) return false;
  if (i >= line.length) return true;
  const c = line.charCodeAt(i);
  return c === CODE_SPACE || c === CODE_TAB || c === CODE_NEWLINE;
}

/** Does the line open a fence (three or more backticks with no backtick after, or three or more tildes)? */
function isFenceLine(line) {
  let i = leadingSpaces(line, 3);
  if (i > 3) return false;
  if (i >= line.length) return false;
  const ch = line.charCodeAt(i);
  if (ch !== CODE_BACKTICK && ch !== CODE_TILDE) return false;
  let n = 0;
  while (i < line.length && line.charCodeAt(i) === ch) { i++; n++; }
  if (n < 3) return false;
  if (ch === CODE_BACKTICK) return line.indexOf('`', i) === -1;
  return true;
}

/** Does the line start a list item (any bullet, or "1." / "1)") followed by space and content? */
function isListStartLine(line) {
  let i = leadingSpaces(line, 3);
  if (i > 3) return false;
  if (i >= line.length) return false;
  const c = line.charCodeAt(i);
  if (c === CODE_STAR || c === 43 || c === 45) {
    i++;
  } else if (c >= 48 && c <= 57) {
    let n = 0;
    while (i < line.length && line.charCodeAt(i) >= 48 && line.charCodeAt(i) <= 57 && n < 9) { i++; n++; }
    if (n === 0 || n > 9) return false;
    if (i >= line.length || (line.charCodeAt(i) !== 46 && line.charCodeAt(i) !== 41)) return false;
    i++;
  } else {
    return false;
  }
  if (i >= line.length) return false;
  const s = line.charCodeAt(i);
  if (s !== CODE_SPACE && s !== CODE_TAB) return false;
  let j = i;
  while (j < line.length && isSpaceOrTab(line.charCodeAt(j))) j++;
  return j < line.length;
}

/** Does the line start a bullet (any marker) with no content requirement, as setext content forbids? */
function isBulletLine(line) {
  let i = leadingSpaces(line, 3);
  if (i > 3 || i >= line.length) return false;
  const c = line.charCodeAt(i);
  if (c === CODE_STAR || c === 43 || c === 45) return true;
  if (c >= 48 && c <= 57) {
    let n = 0;
    while (i < line.length && line.charCodeAt(i) >= 48 && line.charCodeAt(i) <= 57 && n < 9) { i++; n++; }
    if (n === 0) return false;
    return i < line.length && (line.charCodeAt(i) === 46 || line.charCodeAt(i) === 41);
  }
  return false;
}

/** Does the line look like a table delimiter row (cells of dashes with optional colons)? */
function isTableDelimiterLine(line) {
  let i = leadingSpaces(line, 3);
  if (i > 3) return false;
  const rest = line.slice(i);
  if (rest.indexOf(':') === -1 && rest.indexOf('|') === -1) return false;
  return /^(?:\| *)?:?-+:? *(?:\| *:?-+:? *)*(?:\| *)?$/.test(rest);
}

/** Does the line begin an HTML block (the block-start test)? */
function isHtmlBlockStart(line) {
  let i = leadingSpaces(line, 3);
  if (i > 3 || i >= line.length) return false;
  if (line.charCodeAt(i) !== CODE_LT) return false;
  const rest = line.slice(i);
  const lower = rest.toLowerCase();
  if (lower.startsWith('<!--') || lower.startsWith('<?') || lower.startsWith('<![cdata[')) return true;
  if (lower.startsWith('<!') && lower.length > 2) {
    const c = lower.charCodeAt(2);
    if (c >= 65 && c <= 90) return true;
  }
  if (/^<(script|pre|style|textarea)(?:[\s>]|$)/.test(lower)) return true;
  // A block tag, open or close, followed by space, end, or /> or >.
  let j = 1;
  let closing = false;
  if (rest.charCodeAt(j) === 47) { closing = true; j++; }
  let k = j;
  while (k < rest.length) {
    const c = rest.charCodeAt(k);
    if ((c >= 97 && c <= 122) || (c >= 65 && c <= 90) || (c >= 48 && c <= 57) || c === 45) k++;
    else break;
  }
  if (k === j) return false;
  const name = rest.slice(j, k).toLowerCase();
  if (!BLOCK_TAGS.has(name)) return false;
  if (k >= rest.length) return true;
  const c = rest.charCodeAt(k);
  if (c === CODE_SPACE || c === CODE_TAB) return true;
  if (c === 47) return k + 1 < rest.length && rest.charCodeAt(k + 1) === CODE_GT;
  return c === CODE_GT;
}

/**
 * Is `line` a paragraph continuation (not blank, and not starting a block
 * that interrupts a paragraph)? `next` is the following line, needed to
 * recognise a table start.
 */
/**
 * Can `line` continue a paragraph? The continuation lookahead is
 * (?!hr|heading|blockquote|fences|list|html|table|[ \t]+\n): a line of only
 * spaces or tabs blocks only when a newline follows it (so a trailing
 * spaces-only line at the end of input is a continuation), and an ordered
 * list only interrupts a paragraph when it starts with 1.
 */
function isParagraphContinuation(line, next, followedByNewline) {
  if (isBlankLine(line) && followedByNewline) return false;
  if (isHrLine(line)) return false;
  if (isAtxHeadingLine(line)) return false;
  if (/^ {0,3}>/.test(line)) return false;
  if (isFenceLine(line)) return false;
  if (isListStartLinePara(line)) return false;
  if (isHtmlBlockStart(line)) return false;
  if (next !== null && next !== undefined && isTableStart(line, next)) return false;
  return true;
}

/** The paragraph rule's list test: a bullet, or an ordered item starting with 1. */
function isListStartLinePara(line) {
  let i = leadingSpaces(line, 3);
  if (i > 3 || i >= line.length) return false;
  const c = line.charCodeAt(i);
  if (c === CODE_STAR || c === 43 || c === 45) {
    i++;
  } else if (c === 49) { // '1'
    i++;
    if (i >= line.length || (line.charCodeAt(i) !== 46 && line.charCodeAt(i) !== 41)) return false;
    i++;
  } else {
    return false;
  }
  if (i >= line.length) return false;
  const s = line.charCodeAt(i);
  if (s !== CODE_SPACE && s !== CODE_TAB) return false;
  let j = i;
  while (j < line.length && isSpaceOrTab(line.charCodeAt(j))) j++;
  return j < line.length;
}

/** Do `header` and `delim` begin a table (a header line and a delimiter row)? */
function isTableStart(header, delim) {
  let i = 0;
  while (i < header.length && header.charCodeAt(i) === CODE_SPACE) i++;
  if (i >= header.length) return false;
  return isTableDelimiterLine(delim);
}

// ---------------------------------------------------------------------------
// Single-purpose block tokenisers
// ---------------------------------------------------------------------------

/** Blank lines. Returns {token, end} or null. */
/** Match marked's space rule /^ *(?:\n|$)+/: spaces, then newlines or end of input. */
function tokenizeSpace(src, pos) {
  // marked's newline rule: /^(?:[ \t]*(?:\n|$))+/ — one or more lines of
  // only spaces and tabs, each ended by a newline (or the end of input).
  const len = src.length;
  let p = pos;
  let matched = false;
  while (p < len) {
    let q = p;
    while (q < len && (src.charCodeAt(q) === CODE_SPACE || src.charCodeAt(q) === CODE_TAB)) q++;
    if (q < len && src.charCodeAt(q) === CODE_NEWLINE) {
      p = q + 1;
      matched = true;
      continue;
    }
    if (q >= len && q > p) {
      p = q;
      matched = true;
      continue;
    }
    break;
  }
  if (!matched) return null;
  return { token: { type: 'space', raw: src.slice(pos, p) }, end: p };
}

/** Indented code. Returns {token, end} or null. */
function tokenizeCode(src, pos) {
  const len = src.length;
  const e0 = lineEnd(src, pos);
  const first = src.slice(pos, e0);
  if (!isIndentedCodeLine(first)) return null;
  let p = pos;
  let end = e0 < len ? e0 + 1 : len;
  // Consume code lines, allowing blank lines between them.
  for (;;) {
    let q = end;
    // Skip blank lines, remembering where they started.
    while (q < len) {
      const e = lineEnd(src, q);
      if (!isBlankLine(src.slice(q, e))) break;
      q = e < len ? e + 1 : len;
    }
    if (q >= len) break;
    const e = lineEnd(src, q);
    if (!isIndentedCodeLine(src.slice(q, e))) break;
    end = e < len ? e + 1 : len;
  }
  let raw = trimBlankTail(src.slice(pos, end));
  const text = raw.replace(/^(?: {0,3}\t| {1,4})/gm, '');
  return { token: { type: 'code', raw, codeBlockStyle: 'indented', text }, end };
}

/** Is the line an indented code line (four spaces, or up to three spaces and a tab, then content)? */
function isIndentedCodeLine(line) {
  let n = 0;
  while (n < line.length && line.charCodeAt(n) === CODE_SPACE) n++;
  if (n >= 4) return n < line.length;
  if (n < line.length && line.charCodeAt(n) === CODE_TAB) return n + 1 < line.length;
  return false;
}

/** Fenced code. Returns {token, end} or null. */
function tokenizeFences(src, pos) {
  const len = src.length;
  const e0 = lineEnd(src, pos);
  const line = src.slice(pos, e0);
  let i = leadingSpaces(line, 3);
  if (i > 3 || i >= line.length) return null;
  const ch = line.charCodeAt(i);
  if (ch !== CODE_BACKTICK && ch !== CODE_TILDE) return null;
  let run = 0;
  while (i + run < line.length && line.charCodeAt(i + run) === ch) run++;
  if (run < 3) return null;
  const info = line.slice(i + run);
  if (ch === CODE_BACKTICK && info.indexOf('`') !== -1) return null;
  const afterOpen = e0 < len ? e0 + 1 : len;
  // Find the closing fence: the same character, at least as long, alone on its line.
  let closeStart = -1;
  let closeEnd = -1;
  let p = afterOpen;
  while (p < len) {
    const e = lineEnd(src, p);
    const l = src.slice(p, e);
    let k = leadingSpaces(l, 3);
    if (k <= 3 && k < l.length && l.charCodeAt(k) === ch) {
      let m = 0;
      while (k + m < l.length && l.charCodeAt(k + m) === ch) m++;
      if (m >= run) {
        let r = k + m;
        while (r < l.length && l.charCodeAt(r) === CODE_SPACE) r++;
        if (r === l.length) {
          closeStart = p;
          closeEnd = e;
          break;
        }
      }
    }
    p = e < len ? e + 1 : len;
  }
  let content;
  let end;
  if (closeStart !== -1) {
    content = src.slice(afterOpen, closeStart);
    if (content.charCodeAt(content.length - 1) === CODE_NEWLINE) content = content.slice(0, -1);
    end = closeEnd;
  } else {
    content = src.slice(afterOpen);
    if (content.charCodeAt(content.length - 1) === CODE_NEWLINE) content = content.slice(0, -1);
    end = len;
  }
  // A backtick fence with a leading indent dedents its content lines by that indent.
  if (ch === CODE_BACKTICK && i > 0) {
    const indent = line.slice(0, i);
    content = content.split('\n').map((l) => {
      const m = /^\s+/.exec(l);
      if (!m) return l;
      return l.slice(Math.min(m[0].length, indent.length));
    }).join('\n');
  }
  const lang = info ? unescapePunct(info.trim()) : info;
  return { token: { type: 'code', raw: src.slice(pos, end), lang, text: content }, end };
}

/** ATX heading. Returns {token, end} or null. */
function tokenizeHeading(src, pos, ctx) {
  const len = src.length;
  const e0 = lineEnd(src, pos);
  const line = src.slice(pos, e0);
  let i = leadingSpaces(line, 3);
  if (i > 3) return null;
  let depth = 0;
  while (i < line.length && line.charCodeAt(i) === 35 && depth < 6) { i++; depth++; }
  if (depth === 0) return null;
  if (i < line.length && !isWs(line.charCodeAt(i))) return null;
  let text = line.slice(i).trim();
  if (text.charCodeAt(text.length - 1) === 35) {
    const stripped = rtrimChar(text, 35);
    if (stripped === '' || stripped.charCodeAt(stripped.length - 1) === CODE_SPACE || stripped.charCodeAt(stripped.length - 1) === CODE_TAB) {
      text = stripped.trim();
    }
  }
  let end = e0;
  while (end < len && src.charCodeAt(end) === CODE_NEWLINE) end++;
  const token = { type: 'heading', raw: line, depth, text, tokens: [] };
  ctx.inlineQueue.push({ src: text, tokens: token.tokens });
  return { token, end };
}

/** Thematic break. Returns {token, end} or null. */
function tokenizeHr(src, pos) {
  const len = src.length;
  const e0 = lineEnd(src, pos);
  const line = src.slice(pos, e0);
  if (!isHrLine(line)) return null;
  let end = e0;
  while (end < len && src.charCodeAt(end) === CODE_NEWLINE) end++;
  return { token: { type: 'hr', raw: line }, end };
}

/** HTML block. Returns {token, end} or null. */
function tokenizeHtml(src, pos) {
  const len = src.length;
  const e0 = lineEnd(src, pos);
  const line = src.slice(pos, e0);
  let i = leadingSpaces(line, 3);
  if (i > 3 || i >= line.length || line.charCodeAt(i) !== CODE_LT) return null;
  const rest = line.slice(i);
  const lower = rest.toLowerCase();
  let end = -1;
  let pre = false;
  // Type 1: script, pre, style, textarea until the matching close tag.
  const type1 = /^<(script|pre|style|textarea)(?:[\s>]|$)/.exec(lower);
  if (type1) {
    const name = type1[1];
    pre = name === 'pre' || name === 'script' || name === 'style';
    const closeRe = new RegExp('</' + name + '>', 'gi');
    closeRe.lastIndex = pos + i;
    const m = closeRe.exec(src);
    if (m) {
      let e = closeRe.lastIndex;
      while (e < len && src.charCodeAt(e) !== CODE_NEWLINE) e++;
      while (e < len && src.charCodeAt(e) === CODE_NEWLINE) e++;
      end = e;
    } else {
      end = len;
    }
  } else if (lower.startsWith('<!--')) {
    const idx = src.indexOf('-->', pos + i + 4);
    if (idx === -1) end = len;
    else {
      let e = idx + 3;
      while (e < len && src.charCodeAt(e) !== CODE_NEWLINE) e++;
      while (e < len && src.charCodeAt(e) === CODE_NEWLINE) e++;
      end = e;
    }
  } else if (lower.startsWith('<?')) {
    const idx = src.indexOf('?>', pos + i + 2);
    if (idx === -1) end = len;
    else {
      let e = idx + 2;
      while (e < len && src.charCodeAt(e) !== CODE_NEWLINE) e++;
      while (e < len && src.charCodeAt(e) === CODE_NEWLINE) e++;
      end = e;
    }
  } else if (lower.startsWith('<!') && rest.length > 2 && rest.charCodeAt(2) >= 65 && rest.charCodeAt(2) <= 90) {
    const idx = src.indexOf('>', pos + i + 2);
    if (idx === -1) end = len;
    else {
      let e = idx + 1;
      while (e < len && src.charCodeAt(e) !== CODE_NEWLINE) e++;
      while (e < len && src.charCodeAt(e) === CODE_NEWLINE) e++;
      end = e;
    }
  } else if (lower.startsWith('<![cdata[')) {
    const idx = src.indexOf(']]>', pos + i + 9);
    if (idx === -1) end = len;
    else {
      let e = idx + 3;
      while (e < len && src.charCodeAt(e) !== CODE_NEWLINE) e++;
      while (e < len && src.charCodeAt(e) === CODE_NEWLINE) e++;
      end = e;
    }
  } else {
    // Types 6 and 7 run until a blank line or the end.
    let isBlock = false;
    let j = 1;
    if (rest.charCodeAt(j) === 47) j++;
    let k = j;
    while (k < rest.length) {
      const c = rest.charCodeAt(k);
      if ((c >= 97 && c <= 122) || (c >= 65 && c <= 90) || (c >= 48 && c <= 57) || c === 45) k++;
      else break;
    }
    if (k > j) {
      const name = rest.slice(j, k).toLowerCase();
      if (BLOCK_TAGS.has(name)) {
        const after = rest.charCodeAt(k);
        if (k >= rest.length || after === CODE_SPACE || after === CODE_TAB || after === CODE_GT || (after === 47 && rest.charCodeAt(k + 1) === CODE_GT)) {
          isBlock = true;
        }
      } else if (name !== 'script' && name !== 'pre' && name !== 'style' && name !== 'textarea') {
        // Type 7: a complete tag alone on its line. The block rule's
        // attribute pattern forbids newlines, so the tag must be single-line.
        const tagEnd = matchInlineTag(src, pos + i);
        if (tagEnd !== -1) {
          const tagText = src.slice(pos + i, tagEnd);
          let r = tagEnd;
          let onlySpaces = true;
          while (r < len && src.charCodeAt(r) !== CODE_NEWLINE) {
            if (!isSpaceOrTab(src.charCodeAt(r))) { onlySpaces = false; break; }
            r++;
          }
          if (onlySpaces && tagText.charCodeAt(tagText.length - 1) === CODE_GT &&
            tagText.indexOf('\n') === -1) isBlock = true;
        }
      }
    }
    if (!isBlock) return null;
    // Until the first blank line.
    let p = e0 < len ? e0 + 1 : len;
    end = len;
    while (p < len) {
      const e = lineEnd(src, p);
      if (isBlankLine(src.slice(p, e))) {
        end = e < len ? e + 1 : len;
        break;
      }
      p = e < len ? e + 1 : len;
    }
  }
  const raw = trimBlankTail(src.slice(pos, end));
  return { token: { type: 'html', block: true, raw, pre, text: raw }, end };
}

/** Link reference definition. Returns {token, end} or null. */
function tokenizeDef(src, pos) {
  const len = src.length;
  let i = leadingSpaces(src.slice(pos, lineEnd(src, pos)), 3);
  if (i > 3) return null;
  let p = pos + i;
  if (p >= len || src.charCodeAt(p) !== CODE_LBRACK) return null;
  const lab = scanLabelLe(src, p + 1);
  if (!lab) return null;
  let q = lab.end + 1;
  if (q >= len || src.charCodeAt(q) !== 58) return null; // :
  q++;
  while (q < len && src.charCodeAt(q) === CODE_SPACE) q++;
  if (q < len && src.charCodeAt(q) === CODE_NEWLINE) {
    q++;
    while (q < len && isSpaceOrTab(src.charCodeAt(q))) q++;
  }
  // Destination.
  let destRaw;
  let dest;
  let angle = false;
  if (q < len && src.charCodeAt(q) === CODE_LT) {
    const gt = src.indexOf('>', q + 1);
    const nl = src.indexOf('\n', q);
    if (gt === -1 || (nl !== -1 && gt > nl)) return null;
    destRaw = src.slice(q, gt + 1);
    dest = src.slice(q + 1, gt);
    angle = true;
    q = gt + 1;
  } else {
    if (q >= len || src.charCodeAt(q) === CODE_LT || isWs(src.charCodeAt(q))) return null;
    let r = q;
    while (r < len && !isWs(src.charCodeAt(r))) r++;
    destRaw = src.slice(q, r);
    dest = destRaw;
    q = r;
  }
  if (!angle && parenBalance(destRaw) !== -1) return null;
  // Optional title.
  let title;
  let saveQ = q;
  let sep = -1;
  if (q < len && src.charCodeAt(q) === CODE_SPACE) {
    let m = q;
    while (m < len && src.charCodeAt(m) === CODE_SPACE) m++;
    if (m < len && src.charCodeAt(m) === CODE_NEWLINE) {
      m++;
      while (m < len && isSpaceOrTab(src.charCodeAt(m))) m++;
    }
    sep = m;
  } else {
    let m = q;
    while (m < len && src.charCodeAt(m) === CODE_SPACE) m++;
    if (m < len && src.charCodeAt(m) === CODE_NEWLINE) {
      m++;
      while (m < len && isSpaceOrTab(src.charCodeAt(m))) m++;
      sep = m;
    }
  }
  if (sep !== -1) {
    const tt = scanTitleForm(src, sep);
    if (tt) {
      title = tt.title;
      q = tt.end;
    }
  }
  while (q < len && src.charCodeAt(q) === CODE_SPACE) q++;
  let end = q;
  while (end < len && src.charCodeAt(end) === CODE_NEWLINE) end++;
  // After the destination and optional title only spaces and newlines may
  // follow. If a title was found but other text follows on its line, the
  // title group is dropped (it is optional) and the definition ends at the
  // destination.
  if (end === q && q < len) {
    if (title === undefined) return null;
    title = undefined;
    q = saveQ;
    while (q < len && src.charCodeAt(q) === CODE_SPACE) q++;
    end = q;
    while (end < len && src.charCodeAt(end) === CODE_NEWLINE) end++;
    if (end === q && q < len) return null;
  }
  const raw = rtrimChar(src.slice(pos, end), CODE_NEWLINE);
  return {
    token: {
      type: 'def',
      tag: normalizeLabel(lab.text),
      raw,
      href: unescapePunct(dest),
      title: title === undefined ? undefined : unescapePunct(title),
    },
    end,
  };
}

/** Read a "..." / '...' / (...) title starting at `p`; returns {title, end} or null. */
function scanTitleForm(src, p) {
  const len = src.length;
  if (p >= len) return null;
  const q = src.charCodeAt(p);
  if (q === CODE_QUOT) {
    let j = p + 1;
    while (j < len) {
      const c = src.charCodeAt(j);
      if (c === CODE_BACKSLASH) { j += 2; continue; }
      if (c === CODE_QUOT) return { title: src.slice(p + 1, j), end: j + 1 };
      j++;
    }
    return null;
  }
  if (q === CODE_APOS) {
    let j = p + 1;
    while (j < len) {
      const c = src.charCodeAt(j);
      if (c === CODE_BACKSLASH) { j += 2; continue; }
      if (c === CODE_APOS) return { title: src.slice(p + 1, j), end: j + 1 };
      if (c === CODE_NEWLINE) {
        if (j + 1 < len && src.charCodeAt(j + 1) === CODE_NEWLINE) return null;
        j++;
        continue;
      }
      j++;
    }
    return null;
  }
  if (q === CODE_LPAREN) {
    let j = p + 1;
    while (j < len) {
      const c = src.charCodeAt(j);
      if (c === CODE_BACKSLASH) { j += 2; continue; }
      if (c === CODE_RPAREN) return { title: src.slice(p + 1, j), end: j + 1 };
      if (c === CODE_LPAREN) return null;
      j++;
    }
    return null;
  }
  return null;
}

// ---------------------------------------------------------------------------
// Table, setext heading, paragraph, text
// ---------------------------------------------------------------------------

const RE_FIND_PIPE = /\|/g;

/** Split a table row on unescaped pipes, dropping empty edge cells. */
function splitTableRow(s, count) {
  RE_FIND_PIPE.lastIndex = 0;
  const t = s.replace(RE_FIND_PIPE, (ch, off, str) => {
    let odd = false;
    let p = off;
    while (--p >= 0 && str.charCodeAt(p) === CODE_BACKSLASH) odd = !odd;
    return odd ? '|' : ' |';
  });
  const cells = t.split(' |');
  if (cells.length > 0 && cells[0].trim() === '') cells.shift();
  if (cells.length > 0 && cells[cells.length - 1].trim() === '') cells.pop();
  if (count !== undefined) {
    if (cells.length > count) cells.length = count;
    else while (cells.length < count) cells.push('');
  }
  for (let k = 0; k < cells.length; k++) cells[k] = cells[k].trim().replace(/\\\|/g, '|');
  return cells;
}

/** Alignment of each cell of a delimiter row. */
function parseTableDelimiter(delimLine) {
  const i = leadingSpaces(delimLine, 3);
  const rest = delimLine.slice(i).replace(/^\||\| *$/g, '');
  return rest.split('|').map((cell) => {
    if (/^ *-+: *$/.test(cell)) return 'right';
    if (/^ *:-+: *$/.test(cell)) return 'center';
    if (/^ *:-+ *$/.test(cell)) return 'left';
    return null;
  });
}

/** Does the line start a list item in the loose sense (a bullet and a space or tab)? */
function isListLineLoose(line) {
  let i = leadingSpaces(line, 3);
  if (i > 3 || i >= line.length) return false;
  const c = line.charCodeAt(i);
  if (c === CODE_STAR || c === 43 || c === 45) {
    i++;
  } else if (c >= 48 && c <= 57) {
    let n = 0;
    while (i < line.length && line.charCodeAt(i) >= 48 && line.charCodeAt(i) <= 57 && n < 9) { i++; n++; }
    if (n === 0) return false;
    if (i >= line.length || (line.charCodeAt(i) !== 46 && line.charCodeAt(i) !== 41)) return false;
    i++;
  } else {
    return false;
  }
  return i < line.length && isSpaceOrTab(line.charCodeAt(i));
}

/** GFM table. Returns {token, end} or null. */
function tokenizeTable(src, pos, ctx) {
  const len = src.length;
  const e0 = lineEnd(src, pos);
  const headerLine = src.slice(pos, e0);
  let i = 0;
  while (i < headerLine.length && headerLine.charCodeAt(i) === CODE_SPACE) i++;
  if (i >= headerLine.length) return null;
  const headerText = headerLine.slice(i);
  const dStart = e0 < len ? e0 + 1 : len;
  if (dStart >= len) return null;
  const dEnd = lineEnd(src, dStart);
  const delimLine = src.slice(dStart, dEnd);
  if (!isTableDelimiterLine(delimLine)) return null;
  const headerCells = splitTableRow(headerText);
  const align = parseTableDelimiter(delimLine);
  if (headerCells.length !== align.length) return null;
  const rows = [];
  let p = dEnd < len ? dEnd + 1 : len;
  while (p < len) {
    const e = lineEnd(src, p);
    const l = src.slice(p, e);
    // The body-row stop for a blank line is ` *\n`: spaces only, and a newline follows.
    if (/^ *$/.test(l) && e < len) break;
    if (isHrLine(l) || isAtxHeadingLine(l) || /^ {0,3}>/.test(l) || isIndentedCodeLine(l) ||
      isFenceLine(l) || isListLineLoose(l) || isHtmlBlockStart(l)) break;
    rows.push(l);
    p = e < len ? e + 1 : len;
  }
  let end = p;
  while (end < len && src.charCodeAt(end) === CODE_NEWLINE) end++;
  const raw = rtrimChar(src.slice(pos, end), CODE_NEWLINE);
  const token = { type: 'table', raw, header: [], align, rows: [] };
  for (let k = 0; k < headerCells.length; k++) {
    const cell = { text: headerCells[k], tokens: [], header: true, align: align[k] };
    ctx.inlineQueue.push({ src: headerCells[k], tokens: cell.tokens });
    token.header.push(cell);
  }
  for (const row of rows) {
    const cells = splitTableRow(row, headerCells.length);
    token.rows.push(cells.map((c, k) => {
      const cell = { text: c, tokens: [], header: false, align: align[k] };
      ctx.inlineQueue.push({ src: c, tokens: cell.tokens });
      return cell;
    }));
  }
  return { token, end };
}

/** Does the line look like a table delimiter row in the setext sense (pipes and dashes)? */
function isGeTableLine(line) {
  const i = leadingSpaces(line, 3);
  if (i > 3) return false;
  return /^\|?(?:[:\- ]*\|)+[:\- ]*$/.test(line.slice(i));
}

/** Is the line exactly an HTML tag (the setext lookahead's html test)? */
function isHtmlTagLine(line) {
  const i = leadingSpaces(line, 3);
  if (i > 3 || i >= line.length || line.charCodeAt(i) !== CODE_LT) return false;
  const gt = line.indexOf('>', i + 1);
  return gt !== -1 && gt === line.length - 1 && gt > i + 1;
}

/** Does the line open a fence with no info check (the setext lookahead's fences test)? */
function isFenceLineLoose(line) {
  const i = leadingSpaces(line, 3);
  if (i > 3 || i >= line.length) return false;
  const ch = line.charCodeAt(i);
  if (ch !== CODE_BACKTICK && ch !== CODE_TILDE) return false;
  let n = 0;
  while (i + n < line.length && line.charCodeAt(i + n) === ch) n++;
  return n >= 3;
}

/** Can the line start a setext heading's content? */
function isLheadingFirstLine(line) {
  if (isBlankLine(line)) return false;
  if (isBulletLine(line)) return false;
  if (isIndentedCodeLine(line)) return false;
  if (isFenceLineLoose(line)) return false;
  if (/^ {0,3}>/.test(line)) return false;
  if (isAtxHeadingLine(line)) return false;
  if (isHtmlTagLine(line)) return false;
  if (isGeTableLine(line)) return false;
  return true;
}

/** Can the line continue a setext heading's content? */
function isLheadingContentLine(line) {
  if (isBlankLine(line)) return false;
  if (isBulletLine(line)) return false;
  if (isFenceLineLoose(line)) return false;
  if (/^ {0,3}>/.test(line)) return false;
  if (isAtxHeadingLine(line)) return false;
  if (isHrLine(line)) return false;
  if (isHtmlTagLine(line)) return false;
  if (isGeTableLine(line)) return false;
  return true;
}

/** Do `first` and `second` form a setext heading (content line, underline line)? */
function isLheadingPair(first, second) {
  if (!isLheadingFirstLine(first)) return false;
  return /^ {0,3}(=+|-+)[ \t]*$/.test(second);
}

/** Setext heading. Returns {token, end} or null. */
function tokenizeLheading(src, pos, ctx) {
  const len = src.length;
  const e0 = lineEnd(src, pos);
  const first = src.slice(pos, e0);
  if (!isLheadingFirstLine(first)) return null;
  const lines = [first];
  let p = e0 < len ? e0 + 1 : len;
  for (;;) {
    if (p < len) {
      const e = lineEnd(src, p);
      const ul = src.slice(p, e);
      const m = /^ {0,3}(=+|-+)[ \t]*$/.exec(ul);
      if (m) {
        const depth = ul.charAt(leadingSpaces(ul, 3)) === '=' ? 1 : 2;
        const text = lines.join('\n').trim();
        let end = e;
        while (end < len && src.charCodeAt(end) === CODE_NEWLINE) end++;
        const token = { type: 'heading', raw: src.slice(pos, e), depth, text, tokens: [] };
        ctx.inlineQueue.push({ src: text, tokens: token.tokens });
        return { token, end };
      }
    }
    if (p >= len) return null;
    const e = lineEnd(src, p);
    const l = src.slice(p, e);
    if (!isLheadingContentLine(l)) return null;
    lines.push(l);
    p = e < len ? e + 1 : len;
  }
}

/** Paragraph. Returns {token, end} or null. */
function tokenizeParagraph(src, pos, ctx) {
  const len = src.length;
  const e0 = lineEnd(src, pos);
  const first = src.slice(pos, e0);
  if (first.length === 0) return null;
  const lines = [first];
  let end = e0;
  let p = e0 < len ? e0 + 1 : len;
  while (p < len) {
    const e = lineEnd(src, p);
    const l = src.slice(p, e);
    const nextStart = e < len ? e + 1 : len;
    const next = nextStart < len ? src.slice(nextStart, lineEnd(src, nextStart)) : null;
    if (!isParagraphContinuation(l, next, e < len)) break;
    lines.push(l);
    end = e;
    p = nextStart;
  }
  const text = lines.join('\n');
  const token = { type: 'paragraph', raw: text, text, tokens: [] };
  ctx.inlineQueue.push({ src: text, tokens: token.tokens });
  return { token, end };
}

/** A single text line (used inside list items, where paragraphs do not apply). */
function tokenizeText(src, pos, ctx) {
  const e0 = lineEnd(src, pos);
  const line = src.slice(pos, e0);
  const token = { type: 'text', raw: line, text: line, tokens: [] };
  ctx.inlineQueue.push({ src: line, tokens: token.tokens });
  return { token, end: e0 };
}

// ---------------------------------------------------------------------------
// Blockquote
// ---------------------------------------------------------------------------

/** The content of a quote line after its marker (null when there is no marker). */
function quoteContent(line) {
  const i = leadingSpaces(line, 3);
  if (i > 3 || i >= line.length || line.charCodeAt(i) !== CODE_GT) return null;
  let j = i + 1;
  if (j < line.length && isSpaceOrTab(line.charCodeAt(j))) j++;
  return line.slice(j);
}

/** Strip quote markers from a chunk, expanding tabs after markers and indenting setext underlines. */
function stripQuoteMarkers(h) {
  return h
    .replace(/^( {0,3}>)([ \t]+)/gm, (g, b, m) => b + expandTabs(m, b.length))
    .replace(/\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g, '\n    $1')
    .replace(/^ {0,3}>[ \t]?/gm, '');
}

/** Blockquote. Returns {token, end} or null. */
function tokenizeBlockquote(src, pos, ctx) {
  const len = src.length;
  let p = pos;
  let matchEnd = pos;
  while (p < len) {
    const e = lineEnd(src, p);
    const line = src.slice(p, e);
    if (!/^ {0,3}>/.test(line)) break;
    let next = e < len ? e + 1 : len;
    const after = quoteContent(line);
    if (after !== null && after.trim() !== '') {
      let q = next;
      while (q < len) {
        const e2 = lineEnd(src, q);
        const l2 = src.slice(q, e2);
        const n2 = e2 < len ? e2 + 1 : len;
        const nextLine = n2 < len ? src.slice(n2, lineEnd(src, n2)) : null;
        if (!isParagraphContinuation(l2, nextLine, e2 < len)) break;
        q = n2;
      }
      next = q;
    }
    matchEnd = next;
    p = next;
  }
  if (matchEnd === pos) return null;
  let lines = rtrimChar(src.slice(pos, matchEnd), CODE_NEWLINE).split('\n');
  let s = '';
  let r = '';
  const tokens = [];
  while (lines.length > 0) {
    let i = false;
    const chunk = [];
    let p2 = 0;
    for (; p2 < lines.length; p2++) {
      if (/^ {0,3}>/.test(lines[p2])) { chunk.push(lines[p2]); i = true; }
      else if (!i) chunk.push(lines[p2]);
      else break;
    }
    lines = lines.slice(p2);
    const h = chunk.join('\n');
    const u = stripQuoteMarkers(h);
    s = s ? s + '\n' + h : h;
    r = r ? r + '\n' + u : u;
    const savedTop = ctx.top;
    ctx.top = true;
    blockTokens(u, tokens, true, ctx);
    ctx.top = savedTop;
    if (lines.length === 0) break;
    const k = tokens.length ? tokens[tokens.length - 1] : null;
    if (k && (k.type === 'code' || k.type === 'heading' || k.type === 'hr' || k.type === 'html' || k.type === 'table')) break;
    if (k && k.type === 'blockquote') {
      const b = lines.join('\n');
      const m = k.raw + '\n' + b.replace(/^ {0,3}>[ \t]?/gm, '');
      const f = tokenizeBlockquote(m, 0, ctx);
      if (!f) break;
      tokens[tokens.length - 1] = f.token;
      const y = m.substring(f.token.raw.length).replace(/^\n/, '');
      const R = y ? y.split('\n').length : 0;
      const A = R ? lines.slice(0, -R) : lines;
      if (A.length > 0) s = s + '\n' + A.join('\n');
      r = r.substring(0, r.length - k.text.length) + f.token.text;
      lines = lines.slice(A.length);
      if (lines.length > 0 && /^ {0,3}>/.test(lines[0])) continue;
      break;
    } else if (k && k.type === 'list') {
      const b = k.raw + '\n' + lines.join('\n');
      const mTok = tokenizeList(b, 0, ctx);
      if (!mTok) break;
      tokens[tokens.length - 1] = mTok.token;
      const f = mTok.token.raw.length > k.raw.length
        ? b.slice(k.raw.length + 1, mTok.token.raw.length).split('\n').length : 0;
      if (f > 0) {
        const y = lines.slice(0, f).join('\n');
        s = s + '\n' + y;
        r = r + '\n' + y;
      }
      lines = lines.slice(f);
      continue;
    }
  }
  return { token: { type: 'blockquote', raw: s, tokens, text: r }, end: pos + s.length };
}

// ---------------------------------------------------------------------------
// List
// ---------------------------------------------------------------------------

/**
 * Match a list item's bullet on a line. `spec` is null for any bullet, a
 * single character for an unordered list's bullet, or '.' / ')' for an
 * ordered list's delimiter. Returns {bulletLen, bulletText, rest} or null.
 */
function matchBullet(line, spec) {
  let i = 0;
  while (i < line.length && line.charCodeAt(i) === CODE_SPACE && i < 3) i++;
  if (i >= line.length) return null;
  const c = line.charCodeAt(i);
  let bulletText;
  let j;
  if (c === CODE_STAR || c === 43 || c === 45) {
    if (spec && spec !== String.fromCharCode(c)) return null;
    bulletText = String.fromCharCode(c);
    j = i + 1;
  } else if (c >= 48 && c <= 57) {
    let n = 0;
    let k = i;
    while (k < line.length && line.charCodeAt(k) >= 48 && line.charCodeAt(k) <= 57 && n < 9) { k++; n++; }
    if (n === 0) return null;
    if (k >= line.length || (line.charCodeAt(k) !== 46 && line.charCodeAt(k) !== 41)) return null;
    const delim = String.fromCharCode(line.charCodeAt(k));
    if (spec && spec !== delim) return null;
    bulletText = line.slice(i, k + 1);
    j = k + 1;
  } else {
    return null;
  }
  if (j >= line.length) return { bulletLen: j, bulletText, rest: '' };
  const s = line.charCodeAt(j);
  if (s !== CODE_SPACE && s !== CODE_TAB) return null;
  return { bulletLen: j, bulletText, rest: line.slice(j) };
}

/** Expand the leading whitespace of `s`, tab stops starting at column `col`. */
function expandLeadingWsOf(s, col) {
  const m = /^[ \t]+/.exec(s);
  if (!m) return s;
  return expandTabs(m[0], col) + s.slice(m[0].length);
}

/** Leading spaces of `line`, or -1 when there are more than `max`. */
function lineIndentAtMost(line, max) {
  let n = 0;
  while (n < line.length && line.charCodeAt(n) === CODE_SPACE) n++;
  return n <= max ? n : -1;
}

/** The indent a list break-test regex allows: R-1, clamped to 0..3 (marked's D helper). */
function regexIndent(R) {
  return Math.max(0, Math.min(3, R - 1));
}

/** Does the line open a fence at an indent of at most `max`? */
function isFenceBeginAt(line, R) {
  const max = regexIndent(R);
  const i = lineIndentAtMost(line, max);
  if (i === -1 || i >= line.length) return false;
  const ch = line.charCodeAt(i);
  if (ch !== CODE_BACKTICK && ch !== CODE_TILDE) return false;
  let n = 0;
  while (i + n < line.length && line.charCodeAt(i + n) === ch) n++;
  return n >= 3;
}

/** Does the line open an ATX heading at an indent of at most `max`? */
function isHeadingBeginAt(line, R) {
  const max = regexIndent(R);
  const i = lineIndentAtMost(line, max);
  if (i === -1 || i >= line.length) return false;
  let n = 0;
  let j = i;
  while (j < line.length && line.charCodeAt(j) === 35 && n < 6) { j++; n++; }
  if (n === 0) return false;
  if (j >= line.length) return true;
  return isWs(line.charCodeAt(j));
}

/** Does the line start an HTML block at an indent of at most `max`? */
function isHtmlBeginAt(line, R) {
  const max = regexIndent(R);
  const i = lineIndentAtMost(line, max);
  if (i === -1 || i >= line.length || line.charCodeAt(i) !== CODE_LT) return false;
  return isHtmlBlockStart(line.slice(i));
}

/** Does the line start a blockquote at an indent of at most `max`? */
function isBlockquoteBeginAt(line, R) {
  const max = regexIndent(R);
  const i = lineIndentAtMost(line, max);
  if (i === -1 || i >= line.length) return false;
  return line.charCodeAt(i) === CODE_GT;
}

/** Does the line start any list item at an indent of at most `max`? */
function isNextBulletAt(line, R) {
  const max = regexIndent(R);
  const i = lineIndentAtMost(line, max);
  if (i === -1 || i >= line.length) return false;
  return matchBullet(line.slice(i), null) !== null;
}

/** Is the line a thematic break at an indent of at most `max`? */
function isHrAt(line, R) {
  const max = regexIndent(R);
  const i = lineIndentAtMost(line, max);
  if (i === -1) return false;
  return isHrLine(line.slice(i));
}

/** Is the item's text a task item ([ ] / [x] / [X] and content)? */
function isListTask(text) {
  if (text.length < 4) return false;
  const a = text.charCodeAt(0);
  const b = text.charCodeAt(1);
  const c = text.charCodeAt(2);
  if (a !== CODE_LBRACK || c !== CODE_RBRACK) return false;
  if (b !== CODE_SPACE && b !== 120 && b !== 88) return false;
  let i = 3;
  while (i < text.length && isSpaceOrTab(text.charCodeAt(i))) i++;
  return i > 3 && i < text.length && !isWs(text.charCodeAt(i));
}

/** List. Returns {token, end} or null. */
function tokenizeList(src, pos, ctx) {
  const len = src.length;
  const e0 = lineEnd(src, pos);
  const firstLine = src.slice(pos, e0);
  const first = matchBullet(firstLine, null);
  if (!first) return null;
  const ordered = first.bulletText.length > 1;
  const spec = ordered ? first.bulletText.slice(-1) : first.bulletText;
  const items = [];
  let loose = false;
  let p = false;
  let e = pos;
  const startPos = pos;
  while (e < len) {
    const le = lineEnd(src, e);
    const line = src.slice(e, le);
    const m = matchBullet(line, spec);
    if (!m || isHrLine(line)) break;
    const k = e - startPos;
    e = le < len ? le + 1 : len;
    const g = m.rest;
    const b = m.bulletLen;
    const content = expandLeadingWsOf(g, b);
    const fEnd = lineEnd(src, e);
    const f = e < len ? src.slice(e, fEnd) : '';
    const y = content.trim() === '';
    let R;
    let d;
    if (y) {
      R = b + 1;
      d = '';
    } else {
      R = firstNonSpace(content);
      if (R === -1) R = content.length;
      if (R > 4) R = 1;
      d = content.slice(R);
      R += b;
    }
    let u = false;
    if (y && isBlankLine(f)) {
      e = fEnd < len ? fEnd + 1 : len;
      u = true;
    }
    if (!u) {
      let mm = content;
      let yy = y;
      while (e < len) {
        const uEnd = lineEnd(src, e);
        const U = src.slice(e, uEnd);
        const Z = expandLeadingWs(U);
        if (isFenceBeginAt(U, R) || isHeadingBeginAt(U, R) || isHtmlBeginAt(U, R) ||
          isBlockquoteBeginAt(U, R) || isNextBulletAt(U, R) || isHrAt(U, R)) break;
        if (firstNonSpace(Z) >= R || !U.trim()) {
          d += '\n' + Z.slice(R);
        } else {
          if (yy || firstNonSpace(mm.replace(/\t/g, '    ')) >= 4 ||
            isFenceBeginAt(mm, R) || isHeadingBeginAt(mm, R) || isHtmlBeginAt(mm, R) || isHrAt(mm, R)) break;
          let qe;
          if (/^ {0,3}(?:=+|-+) *$/.test(U) && isLheadingPair(mm, U)) {
            qe = '    ' + Z.replace(/^ {0,3}/, '');
          } else {
            qe = U;
          }
          d += '\n' + qe;
        }
        yy = !U.trim();
        e = uEnd < len ? uEnd + 1 : len;
        mm = Z.slice(R);
      }
    }
    const A = src.slice(startPos + k, e);
    if (!loose) {
      if (p) loose = true;
      else if (/\n[ \t]*\n[ \t]*$/.test(A)) p = true;
    }
    items.push({ type: 'list_item', raw: A, task: isListTask(d), loose: false, text: d, tokens: [] });
  }
  const last = items.length ? items[items.length - 1] : null;
  if (!last) return null;
  last.raw = last.raw.trimEnd();
  last.text = last.text.trimEnd();
  const raw = src.slice(startPos, e).trimEnd();
  const token = {
    type: 'list', raw, ordered,
    start: ordered ? parseInt(first.bulletText.slice(0, -1), 10) : '',
    loose, items,
  };
  for (const item of items) {
    ctx.top = false;
    item.tokens = blockTokens(item.text, [], false, ctx);
    if (!loose) {
      const spaces = item.tokens.filter((t) => t.type === 'space');
      if (spaces.length > 0 && spaces.some((t) => /\n.*\n/.test(t.raw))) loose = true;
    }
  }
  token.loose = loose;
  for (const item of items) {
    const d0 = item.tokens[0];
    if (item.task && d0 && (d0.type === 'text' || d0.type === 'paragraph')) {
      item.text = item.text.replace(/^\[[ xX]\][ \t]+/, '');
      d0.raw = d0.raw.replace(/^\[[ xX]\][ \t]+/, '');
      d0.text = d0.text.replace(/^\[[ xX]\][ \t]+/, '');
      for (let g = ctx.inlineQueue.length - 1; g >= 0; g--) {
        if (/^\[[ xX]\][ \t]+\S/.test(ctx.inlineQueue[g].src)) {
          ctx.inlineQueue[g].src = ctx.inlineQueue[g].src.replace(/^\[[ xX]\][ \t]+/, '');
          break;
        }
      }
      const ck = /\[[ xX]\]/.exec(item.raw);
      if (ck) {
        const g = { type: 'checkbox', raw: ck[0] + ' ', checked: ck[0] !== '[ ]' };
        item.checked = g.checked;
        if (loose) {
          const t0 = item.tokens[0];
          if (t0 && (t0.type === 'paragraph' || t0.type === 'text') && 'tokens' in t0 && t0.tokens) {
            t0.raw = g.raw + t0.raw;
            t0.text = g.raw + t0.text;
            t0.tokens.unshift(g);
          } else {
            item.tokens.unshift({ type: 'paragraph', raw: g.raw, text: g.raw, tokens: [g] });
          }
        } else {
          item.tokens.unshift(g);
        }
      }
    } else if (item.task) {
      item.task = false;
    }
  }
  if (loose) {
    for (const item of items) {
      item.loose = true;
      for (const t of item.tokens) if (t.type === 'text') t.type = 'paragraph';
    }
  }
  return { token, end: startPos + raw.length };
}

// ---------------------------------------------------------------------------
// Main block loop
// ---------------------------------------------------------------------------

/**
 * Tokenise `src` into `tokens`. `n` is the paragraph-merge flag: when true,
 * the first paragraph tokenised here merges into a preceding paragraph token
 * (this happens for the inner lex of a blockquote). After any paragraph it
 * becomes false. `ctx.top` gates the paragraph rule: it is false inside list
 * items, so they get text tokens instead.
 */
function blockTokens(src, tokens, n, ctx) {
  const len = src.length;
  let pos = 0;
  let shortest = Infinity;
  while (pos < len) {
    const remaining = len - pos;
    if (remaining < shortest) shortest = remaining;
    else throw new Error('Infinite loop on byte: ' + src.charCodeAt(pos));
    let r;
    if ((r = tokenizeSpace(src, pos))) {
      pos = r.end;
      const prev = tokens.length ? tokens[tokens.length - 1] : undefined;
      if (r.token.raw.length === 1 && prev !== undefined) prev.raw += '\n';
      else tokens.push(r.token);
      continue;
    }
    if ((r = tokenizeCode(src, pos))) {
      pos = r.end;
      const prev = tokens.length ? tokens[tokens.length - 1] : undefined;
      if (prev && (prev.type === 'paragraph' || prev.type === 'text')) {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + r.token.raw;
        prev.text += '\n' + r.token.text;
        ctx.inlineQueue[ctx.inlineQueue.length - 1].src = prev.text;
      } else {
        tokens.push(r.token);
      }
      continue;
    }
    if ((r = tokenizeFences(src, pos, ctx))) {
      pos = r.end;
      tokens.push(r.token);
      continue;
    }
    if ((r = tokenizeHeading(src, pos, ctx))) {
      pos = r.end;
      tokens.push(r.token);
      continue;
    }
    if ((r = tokenizeHr(src, pos))) {
      pos = r.end;
      tokens.push(r.token);
      continue;
    }
    if ((r = tokenizeBlockquote(src, pos, ctx))) {
      pos = r.end;
      tokens.push(r.token);
      continue;
    }
    if ((r = tokenizeList(src, pos, ctx))) {
      pos = r.end;
      tokens.push(r.token);
      continue;
    }
    if ((r = tokenizeHtml(src, pos))) {
      pos = r.end;
      tokens.push(r.token);
      continue;
    }
    if ((r = tokenizeDef(src, pos, ctx))) {
      pos = r.end;
      const prev = tokens.length ? tokens[tokens.length - 1] : undefined;
      if (prev && (prev.type === 'paragraph' || prev.type === 'text')) {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + r.token.raw;
        prev.text += '\n' + r.token.raw;
        ctx.inlineQueue[ctx.inlineQueue.length - 1].src = prev.text;
      } else {
        if (!(r.token.tag in ctx.links)) {
          ctx.links[r.token.tag] = { href: r.token.href, title: r.token.title };
        }
        tokens.push(r.token);
      }
      continue;
    }
    if ((r = tokenizeTable(src, pos, ctx))) {
      pos = r.end;
      tokens.push(r.token);
      continue;
    }
    if ((r = tokenizeLheading(src, pos, ctx))) {
      pos = r.end;
      tokens.push(r.token);
      continue;
    }
    if (ctx.top) {
      r = tokenizeParagraph(src, pos, ctx);
      if (r) {
        pos = r.end;
        const prev = tokens.length ? tokens[tokens.length - 1] : undefined;
        if (n && prev && prev.type === 'paragraph') {
          prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + r.token.raw;
          prev.text += '\n' + r.token.text;
          ctx.inlineQueue.pop();
          ctx.inlineQueue[ctx.inlineQueue.length - 1].src = prev.text;
        } else {
          tokens.push(r.token);
        }
        n = false;
        continue;
      }
    }
    r = tokenizeText(src, pos, ctx);
    pos = r.end;
    const prev = tokens.length ? tokens[tokens.length - 1] : undefined;
    if (prev && prev.type === 'text') {
      prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + r.token.raw;
      prev.text += '\n' + r.token.text;
      ctx.inlineQueue.pop();
      ctx.inlineQueue[ctx.inlineQueue.length - 1].src = prev.text;
    } else {
      tokens.push(r.token);
    }
  }
  ctx.top = true;
  return tokens;
}

// ---------------------------------------------------------------------------
// Renderer
// ---------------------------------------------------------------------------

/** Render a block-level text token the way the renderer does. */
function renderTextToken(t) {
  if ('tokens' in t && t.tokens) return renderInline(t.tokens, false);
  if ('escaped' in t && t.escaped) return t.text;
  return escapeHtml(t.text);
}

/** Render an inline link token. */
function renderLink(t) {
  const text = t.autolink ? escapeHtml(t.text, true) : renderInline(t.tokens, false);
  const href = encodeHref(t.href);
  if (href === null) return text;
  let out = '<a href="' + escapeHtml(href, t.autolink) + '"';
  if (t.title) out += ' title="' + escapeHtml(t.title) + '"';
  return out + '>' + text + '</a>';
}

/** Render an inline image token. */
function renderImage(t) {
  const text = t.tokens ? renderInline(t.tokens, true) : t.text;
  const href = encodeHref(t.href);
  if (href === null) return escapeHtml(text);
  let out = '<img src="' + escapeHtml(href) + '" alt="' + escapeHtml(text) + '"';
  if (t.title) out += ' title="' + escapeHtml(t.title) + '"';
  return out + '>';
}

/**
 * Render inline tokens. `textMode` renders plain text (the text renderer:
 * strong/em/del/link/image recurse into their tokens, codespan and html give
 * their text, br gives nothing, checkbox gives its raw).
 */
function renderInline(tokens, textMode) {
  let out = '';
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    switch (t.type) {
      case 'escape':
        // An escape token renders its (single) character through the escaper.
        out += textMode ? t.text : escapeHtml(t.text);
        break;
      case 'html':
        out += t.text;
        break;
      case 'link':
        out += textMode
          ? (t.tokens ? renderInline(t.tokens, true) : t.text)
          : renderLink(t);
        break;
      case 'image':
        out += textMode
          ? (t.tokens ? renderInline(t.tokens, true) : t.text)
          : renderImage(t);
        break;
      case 'checkbox':
        out += textMode ? t.raw : '<input ' + (t.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
        break;
      case 'strong':
        out += textMode
          ? (t.tokens ? renderInline(t.tokens, true) : t.text)
          : '<strong>' + renderInline(t.tokens, false) + '</strong>';
        break;
      case 'em':
        out += textMode
          ? (t.tokens ? renderInline(t.tokens, true) : t.text)
          : '<em>' + renderInline(t.tokens, false) + '</em>';
        break;
      case 'codespan':
        out += textMode ? t.text : '<code>' + escapeHtml(t.text, true) + '</code>';
        break;
      case 'br':
        if (!textMode) out += '<br>';
        break;
      case 'del':
        out += textMode
          ? (t.tokens ? renderInline(t.tokens, true) : t.text)
          : '<del>' + renderInline(t.tokens, false) + '</del>';
        break;
      case 'text':
      default:
        out += textMode ? t.text : renderTextToken(t);
        break;
    }
  }
  return out;
}

/** Render block tokens to HTML. */
function renderTokens(tokens) {
  let out = '';
  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    switch (t.type) {
      case 'space':
      case 'def':
        break;
      case 'hr':
        out += '<hr>\n';
        break;
      case 'heading':
        out += '<h' + t.depth + '>' + renderInline(t.tokens, false) + '</h' + t.depth + '>\n';
        break;
      case 'code': {
        const lang = t.lang ? t.lang.match(/^\S*/)[0] : '';
        const body = escapeHtml(t.text ? t.text.replace(/\n$/, '') + '\n' : '', true);
        out += lang
          ? '<pre><code class="language-' + escapeHtml(lang) + '">' + body + '</code></pre>\n'
          : '<pre><code>' + body + '</code></pre>\n';
        break;
      }
      case 'table': {
        let head = '';
        for (let k = 0; k < t.header.length; k++) {
          const c = t.header[k];
          head += (c.align ? '<th align="' + c.align + '">' : '<th>') +
            renderInline(c.tokens, false) + '</th>\n';
        }
        let body = '';
        for (let r = 0; r < t.rows.length; r++) {
          let row = '';
          for (let k = 0; k < t.rows[r].length; k++) {
            const c = t.rows[r][k];
            row += (c.align ? '<td align="' + c.align + '">' : '<td>') +
              renderInline(c.tokens, false) + '</td>\n';
          }
          body += '<tr>\n' + row + '</tr>\n';
        }
        if (body) body = '<tbody>' + body + '</tbody>';
        out += '<table>\n<thead>\n<tr>\n' + head + '</tr>\n</thead>\n' + body + '</table>\n';
        break;
      }
      case 'blockquote':
        out += '<blockquote>\n' + renderTokens(t.tokens) + '</blockquote>\n';
        break;
      case 'list': {
        let items = '';
        for (let k = 0; k < t.items.length; k++) {
          items += '<li>' + renderTokens(t.items[k].tokens) + '</li>\n';
        }
        const tag = t.ordered ? 'ol' : 'ul';
        const start = t.ordered && t.start !== 1 ? ' start="' + t.start + '"' : '';
        out += '<' + tag + start + '>\n' + items + '</' + tag + '>\n';
        break;
      }
      case 'checkbox':
        out += '<input ' + (t.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
        break;
      case 'html':
        out += t.text;
        break;
      case 'paragraph':
        out += '<p>' + renderInline(t.tokens, false) + '</p>\n';
        break;
      case 'text':
        out += renderTextToken(t);
        break;
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// Entry point
// ---------------------------------------------------------------------------

/**
 * Render Markdown to HTML, matching marked 18.1.3 with its defaults.
 * Fresh state per call; nothing is cached between calls.
 */
export function parse(markdown) {
  const src = String(markdown).replace(/\r\n|\r/g, '\n');
  const ctx = {
    links: Object.create(null),
    inlineQueue: [],
    top: true,
    inLink: false,
    inRawBlock: false,
    linkEmitted: false,
  };
  const tokens = [];
  blockTokens(src, tokens, false, ctx);
  for (let i = 0; i < ctx.inlineQueue.length; i++) {
    const q = ctx.inlineQueue[i];
    ctx.inRawBlock = false;
    // The top-level paren flag is always true here (marked restores it after
    // each inline pass), so parenPossible is just whether this string has a ).
    const toks = inlineTokens(q.src, ctx, q.src.indexOf(')') !== -1);
    for (let k = 0; k < toks.length; k++) q.tokens.push(toks[k]);
  }
  return renderTokens(tokens);
}

// ---------------------------------------------------------------------------
// Emphasis closer bound (the "mask")
// ---------------------------------------------------------------------------

/**
 * For a masked inline string, the last index of a run of each delimiter
 * (*, _, ~) that can close emphasis or strikethrough: the character before
 * the run must not be whitespace. The string is already masked, so a run
 * inside a code span, a link, a tag or an escape is simply not there.
 * Returns {'*': i, '_': i, '~': i} with -1 when there is no such run.
 */
function computeCloserBound(src) {
  const bound = { '*': -1, '_': -1, '~': -1 };
  const len = src.length;
  let i = 0;
  while (i < len) {
    const c = src.charCodeAt(i);
    if (c === CODE_STAR || c === CODE_UNDER || c === CODE_TILDE) {
      const delim = src[i];
      let j = i + 1;
      while (j < len && src.charCodeAt(j) === c) j++;
      const before = i === 0 ? CODE_NEWLINE : src.charCodeAt(i - 1);
      if (before !== CODE_SPACE && before !== CODE_TAB && before !== CODE_NEWLINE &&
        before !== CODE_CR && before !== 12) {
        bound[delim] = i;
      }
      i = j;
      continue;
    }
    i++;
  }
  return bound;
}

// ---------------------------------------------------------------------------
// Inline mask (for the emphasis closer search)
// ---------------------------------------------------------------------------

/**
 * Whether a string contains a link (an inline link or a reference link
 * whose reference is known). Used by the reflink mask: a reference link
 * whose label itself holds a link is masked only in its reference part.
 */
function linkInText(text, links) {
  if (!text.includes('[')) return false;
  const len = text.length;
  for (let i = 0; i < len; i++) {
    if (text.charCodeAt(i) !== CODE_LBRACK) continue;
    const bang = i > 0 && text.charCodeAt(i - 1) === 33;
    if (bang) continue;
    // Inline link [label](dest).
    const lab = scanLabelRe(text, i + 1);
    if (lab) {
      const after = lab.end + 1;
      if (after < len && text.charCodeAt(after) === CODE_LPAREN) return true;
      if (after < len && text.charCodeAt(after) === CODE_LBRACK) {
        const ref = scanLabelLe(text, after + 1);
        if (ref) {
          const key = normalizeLabel(ref.text || lab.label);
          if (links[key] !== undefined) return true;
        }
      }
      // Shortcut reference [ref]: the label itself is the reference.
      if (links[normalizeLabel(lab.label)] !== undefined) return true;
      continue;
    }
    // Shortcut reference [ref].
    const ref = scanLabelLe(text, i + 1);
    if (ref) {
      const key = normalizeLabel(ref.text);
      if (links[key] !== undefined) return true;
    }
  }
  return false;
}

/**
 * Mask reference links whose reference is known, length-preserving: the
 * whole match becomes `[aaa...]`, except that a full reference link whose
 * label itself holds a link is masked only in its reference part (and any
 * reference links inside the label are masked in turn). Reference links
 * whose reference is not known are left alone.
 */
function maskReflinks(src, links) {
  const len = src.length;
  const out = new Array(len);
  for (let i = 0; i < len; i++) out[i] = src[i];
  let i = 0;
  while (i < len) {
    let start = i;
    let bang = false;
    if (src.charCodeAt(i) === 33 && i + 1 < len && src.charCodeAt(i + 1) === CODE_LBRACK) {
      bang = true;
      start = i + 1;
    } else if (src.charCodeAt(i) !== CODE_LBRACK) {
      i++;
      continue;
    }
    // Full reference link [label][ref].
    const lab = scanLabelRe(src, start + 1);
    if (lab) {
      const after = lab.end + 1;
      if (after < len && src.charCodeAt(after) === CODE_LBRACK) {
        const ref = scanLabelLe(src, after + 1);
        if (ref) {
          const end = ref.end + 1;
          const key = normalizeLabel(ref.text || lab.label);
          if (links[key] !== undefined) {
            if (!bang && lab.label.includes('[') && linkInText(lab.label, links)) {
              const maskedLabel = maskReflinks(lab.label, links);
              for (let k = 0; k < maskedLabel.length; k++) out[start + 1 + k] = maskedLabel[k];
              for (let k = after; k < end; k++) out[k] = 'a';
              out[after] = '[';
              out[end - 1] = ']';
            } else {
              for (let k = start; k < end; k++) out[k] = 'a';
              out[start] = '[';
              out[end - 1] = ']';
            }
            i = end;
            continue;
          }
        }
      }
    }
    // Shortcut or collapsed reference [ref] or [ref][].
    const ref = scanLabelLe(src, start + 1);
    if (ref) {
      let end = ref.end + 1;
      if (end + 1 < len && src.charCodeAt(end) === CODE_LBRACK && src.charCodeAt(end + 1) === CODE_RBRACK) end += 2;
      if (end < len && src.charCodeAt(end) === CODE_LPAREN) { i++; continue; }
      const key = normalizeLabel(ref.text);
      if (links[key] !== undefined) {
        for (let k = start; k < end; k++) out[k] = 'a';
        out[start] = '[';
        out[end - 1] = ']';
        i = end;
        continue;
      }
    }
    i++;
  }
  return out.join('');
}

/**
 * A code span as the label pattern reads it: a backtick run, content with
 * no backticks, then a backtick run of any length. Returns the index just
 * past the closing run, or -1. Unlike a real code span, the closing run
 * need not match the opening run, and the content may hold no backticks.
 */
function matchLabelCodeSpan(src, j) {
  const len = src.length;
  let m = 0;
  while (j + m < len && src.charCodeAt(j + m) === CODE_BACKTICK) m++;
  let k = j + m;
  while (k < len && src.charCodeAt(k) !== CODE_BACKTICK) k++;
  if (k >= len) return -1;
  let n = 0;
  while (k + n < len && src.charCodeAt(k + n) === CODE_BACKTICK) n++;
  return k + n;
}
/**
 * A code span as the block-skip pattern reads it: a backtick run, content
 * of one or more non-backtick characters, then a run of the same length
 * not followed by a backtick. Returns the index just past the closing run,
 * or -1.
 */
function matchBlockSkipCodeSpan(src, i) {
  const len = src.length;
  let runLen = 0;
  while (i + runLen < len && src.charCodeAt(i + runLen) === CODE_BACKTICK) runLen++;
  let k = i + runLen;
  const contentStart = k;
  while (k < len && src.charCodeAt(k) !== CODE_BACKTICK) k++;
  if (k === contentStart) return -1;
  let closeLen = 0;
  while (k + closeLen < len && src.charCodeAt(k + closeLen) === CODE_BACKTICK) closeLen++;
  if (closeLen !== runLen) return -1;
  return k + closeLen;
}

/**
 * Scan a link label for the block-skip mask, starting just after '['. The
 * label may hold code spans (as the block-skip pattern reads them) and
 * escapes but no nested brackets; a backtick that does not open a code
 * span ends it. Returns the index of the closing ']' or -1.
 */
function scanBlockSkipLabelEnd(src, i) {
  const len = src.length;
  let j = i;
  while (j < len) {
    const c = src.charCodeAt(j);
    if (c === CODE_BACKSLASH) { j += 2; continue; }
    if (c === CODE_BACKTICK) {
      const cs = matchBlockSkipCodeSpan(src, j);
      if (cs !== -1) { j = cs; continue; }
      return -1;
    }
    if (c === CODE_LBRACK) return -1;
    if (c === CODE_RBRACK) return j;
    j++;
  }
  return -1;
}

/**
 * The first mask phase (anyPunctuationOutsideCode): an escape (backslash
 * plus punctuation) becomes `++`, and a code span keeps its backtick runs
 * while any backtick inside its content becomes `+`. A backtick run that
 * opens no code span is left as it is. Length-preserving.
 */
function maskOt(src) {
  const len = src.length;
  const out = new Array(len);
  for (let i = 0; i < len; i++) out[i] = src[i];
  let i = 0;
  while (i < len) {
    const c = src.charCodeAt(i);
    if (c === CODE_BACKSLASH && i + 1 < len && isPunct(src[i + 1])) {
      out[i] = '+';
      out[i + 1] = '+';
      i += 2;
      continue;
    }
    if (c === CODE_BACKTICK) {
      const cs = matchCodeSpan(src, i);
      if (cs !== -1) {
        let runLen = 0;
        while (i + runLen < len && src.charCodeAt(i + runLen) === CODE_BACKTICK) runLen++;
        for (let k = i + runLen; k < cs - runLen; k++) {
          if (src.charCodeAt(k) === CODE_BACKTICK) out[k] = '+';
        }
        i = cs;
        continue;
      }
      let k = i + 1;
      while (k < len && src.charCodeAt(k) === CODE_BACKTICK) k++;
      i = k;
      continue;
    }
    i++;
  }
  return out.join('');
}

/**
 * The second mask phase (blockSkip), run on the result of the first: an
 * inline link, a code span or an HTML tag (or an autolink) becomes
 * `[aaa...]`, length-preserving. A link's destination is a run of
 * characters that are not parentheses (so it may hold a title and spaces)
 * or balanced parentheses, followed at once by ')'.
 */
function maskBlockSkip(src) {
  const len = src.length;
  const out = new Array(len);
  for (let i = 0; i < len; i++) out[i] = src[i];
  let i = 0;
  while (i < len) {
    const c = src.charCodeAt(i);
    if (c === CODE_BACKTICK) {
      const cs = matchBlockSkipCodeSpan(src, i);
      if (cs !== -1) {
        out[i] = '[';
        for (let k = i + 1; k < cs - 1; k++) out[k] = 'a';
        out[cs - 1] = ']';
        i = cs;
        continue;
      }
      // A run that opens no code span is consumed whole: the block-skip
      // pattern will not start a code span on a backtick that follows one.
      let k = i + 1;
      while (k < len && src.charCodeAt(k) === CODE_BACKTICK) k++;
      i = k;
      continue;
    }
    if (c === CODE_LT) {
      const tagEnd = matchInlineTag(src, i);
      if (tagEnd !== -1) {
        out[i] = '[';
        for (let k = i + 1; k < tagEnd - 1; k++) out[k] = 'a';
        out[tagEnd - 1] = ']';
        i = tagEnd;
        continue;
      }
      const al = matchAutolink(src, i);
      if (al) {
        out[i] = '[';
        for (let k = i + 1; k < al.end - 1; k++) out[k] = 'a';
        out[al.end - 1] = ']';
        i = al.end;
        continue;
      }
      i++;
      continue;
    }
    if (c === CODE_LBRACK || (c === 33 && i + 1 < len && src.charCodeAt(i + 1) === CODE_LBRACK)) {
      const start = c === 33 ? i + 1 : i;
      const labEnd = scanBlockSkipLabelEnd(src, start + 1);
      if (labEnd !== -1) {
        const j = labEnd + 1;
        if (j < len && src.charCodeAt(j) === CODE_LPAREN) {
          let k = j + 1;
          let ok = true;
          while (k < len) {
            const ch = src.charCodeAt(k);
            if (ch === CODE_BACKSLASH) { k += 2; continue; }
            if (ch === CODE_LPAREN) {
              let depth = 1;
              k++;
              while (k < len && depth > 0) {
                const ch2 = src.charCodeAt(k);
                if (ch2 === CODE_BACKSLASH) { k += 2; continue; }
                if (ch2 === CODE_LPAREN) depth++;
                else if (ch2 === CODE_RPAREN) depth--;
                k++;
              }
              if (depth !== 0) { ok = false; break; }
              continue;
            }
            if (ch === CODE_RPAREN) break;
            k++;
          }
          if (ok && k < len && src.charCodeAt(k) === CODE_RPAREN) {
            out[i] = '[';
            for (let m = i + 1; m < k; m++) out[m] = 'a';
            out[k] = ']';
            i = k + 1;
            continue;
          }
        }
      }
      i++;
      continue;
    }
    i++;
  }
  return out.join('');
}

/**
 * The masked form of an inline string: escapes become `++`, code spans,
 * inline links and HTML tags become `[aaa...]`, all length-preserving, so
 * indexes in the masked string line up with the original. A delimiter
 * inside one of those constructs can never close emphasis, so the closer
 * search runs on this string instead of the original.
 */
/**
 * The masked form of an inline string, in marked's order: reference links
 * whose reference is known first, then escapes and code spans (inner
 * backticks neutralised), then inline links, code spans and HTML tags.
 * Every phase is length-preserving, so indices line up with the original.
 */
function maskInline(src, links) {
  // Nothing to mask when the string holds no backtick, bracket, angle
  // bracket or backslash: no code span, link, tag or escape can hide a
  // closer, so the mask is the string itself.
  if (src.indexOf('`') === -1 && src.indexOf('[') === -1 && src.indexOf('<') === -1 && src.indexOf('\\') === -1) return src;
  if (links && src.indexOf('[') !== -1) src = maskReflinks(src, links);
  src = maskOt(src);
  src = maskBlockSkip(src);
  return src;
}
