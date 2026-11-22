// mend: one patch tool for every AI edit format.
//
// Applies an edit (unified diff, SEARCH/REPLACE blocks, V4A patch, or JSON
// edits) to a tree of text files, as SPEC.md says. Node 22, standard library
// alone. When MAKEFUN_ENV_URL is set, the file hands the trial over to the
// kit's runner instead of running the CLI.

import { readFileSync, writeFileSync, mkdirSync, unlinkSync, existsSync, statSync } from 'node:fs';
import { dirname, join } from 'node:path';
import { runTrial } from './runner.ts';

// ---------------------------------------------------------------------------
// Small helpers

type Br = '\n' | '\r\n';

/** A file as mend works on it: its lines, its line break, whether it ends with one. */
interface WorkFile {
  br: Br;
  lines: string[];
  eol: boolean;
}

/** Split a file's text into its line break, its lines, and whether it ends with a break. */
function parseFile(text: string): WorkFile {
  const firstLF = text.indexOf('\n');
  const br: Br = firstLF > 0 && text[firstLF - 1] === '\r' ? '\r\n' : '\n';
  const eol = text.length > 0 && text.endsWith(br);
  let lines: string[];
  if (text === '') {
    lines = [];
  } else {
    lines = text.split(br);
    if (eol) lines.pop();
  }
  return { br, lines, eol };
}

/** Render a file back to text. A file of no lines is written empty. */
function renderFile(f: WorkFile): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.eol ? f.br : '');
}

/** A patch's lines: split at \n, one trailing \r removed, no empty piece after a final \n. */
function patchLines(text: string): string[] {
  const parts = text.split('\n');
  if (parts.length > 0 && parts[parts.length - 1] === '') parts.pop();
  return parts.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

/** Remove trailing spaces and tabs. */
function rtrimWS(s: string): string {
  return s.replace(/[ \t]+$/, '');
}

/** The leading spaces and tabs of a line. */
function leadingWS(s: string): string {
  const m = /^[ \t]*/.exec(s);
  return m ? m[0] : '';
}

/** A path is safe when it is not empty, does not start with /, holds no \, and none of its
 *  /-separated segments is empty, . or ... */
function isSafePath(p: string): boolean {
  if (p === '') return false;
  if (p.startsWith('/')) return false;
  if (p.includes('\\')) return false;
  const segs = p.split('/');
  for (const s of segs) {
    if (s === '' || s === '.' || s === '..') return false;
  }
  return true;
}

/** Compare two strings by their UTF-8 bytes. */
function byteCompare(a: string, b: string): number {
  return Buffer.compare(Buffer.from(a, 'utf8'), Buffer.from(b, 'utf8'));
}

/** A parse fault: the patch cannot be read in its format at patch line n (1-based). */
class ParseFault extends Error {
  line: number;
  constructor(line: number) {
    super(`parse ${line}`);
    this.line = line;
  }
}

// ---------------------------------------------------------------------------
// Matching (SPEC section 5)

function normLine(s: string, tier: number): string {
  if (tier === 0) return s;
  if (tier === 1) return rtrimWS(s);
  return s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
}

/**
 * Find O in F at the first tier where it occurs at least once, considering only
 * positions >= minPos. Returns the tier and every occurrence position at it, or null.
 */
function findOccurrences(
  F: string[],
  O: string[],
  strict: boolean,
  minPos: number,
): { tier: number; positions: number[] } | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const On = O.map((s) => normLine(s, t));
    const Fn = F.map((s) => normLine(s, t));
    const pos: number[] = [];
    for (let i = minPos; i + O.length <= F.length; i++) {
      let ok = true;
      for (let j = 0; j < O.length; j++) {
        if (Fn[i + j] !== On[j]) {
          ok = false;
          break;
        }
      }
      if (ok) pos.push(i);
    }
    if (pos.length > 0) return { tier: t, positions: pos };
  }
  return null;
}

/**
 * Replace O (found at pos, at tier) by N in the file's lines. contextNtoO maps an
 * index of N that is a context line to the index of O it corresponds to; such a line
 * is written as the file's own matched line. Every other line of N is re-indented
 * at tier 2. Returns the new lines (the file's eol is untouched by this helper).
 */
function replaceLines(
  F: string[],
  pos: number,
  O: string[],
  N: string[],
  tier: number,
  contextNtoO: Map<number, number>,
): string[] {
  const fIndent = leadingWS(F[pos]);
  const pIndent = leadingWS(O[0]);
  const repl: string[] = [];
  for (let i = 0; i < N.length; i++) {
    const oi = contextNtoO.get(i);
    if (oi !== undefined) {
      repl.push(F[pos + oi]);
    } else {
      let line = N[i];
      if (tier === 2 && line !== '' && line.trim() !== '' && line.startsWith(pIndent)) {
        line = fIndent + line.slice(pIndent.length);
      }
      repl.push(line);
    }
  }
  return [...F.slice(0, pos), ...repl, ...F.slice(pos + O.length)];
}

// ---------------------------------------------------------------------------
// The tree

type EditFailure = { ok: false; code: string; path: string };
type EditResult = { ok: true } | EditFailure;

function fail(code: string, path: string): EditFailure {
  return { ok: false, code, path };
}

/** The working tree: what is on disk before the patch, and what edits left so far. */
class Tree {
  /** Original text of every path ever touched (null = did not exist). */
  orig: Map<string, string | null> = new Map();
  /** Current state: a path is here exactly when the file exists in the working tree. */
  cur: Map<string, WorkFile> = new Map();
  /** Successful moves, in order, for the R output lines. */
  moves: Array<{ old: string; nw: string }> = [];

  /** Load a path from disk on first touch. */
  touch(p: string): void {
    if (this.orig.has(p)) return;
    let text: string | null = null;
    try {
      const st = statSync(p);
      if (st.isFile()) text = readFileSync(p, 'utf8');
    } catch {
      text = null;
    }
    this.orig.set(p, text);
    if (text !== null) this.cur.set(p, parseFile(text));
  }

  /** Current file, or null when it does not exist in the working tree. */
  get(p: string): WorkFile | null {
    this.touch(p);
    return this.cur.get(p) ?? null;
  }

  exists(p: string): boolean {
    return this.get(p) !== null;
  }

  set(p: string, f: WorkFile): void {
    this.touch(p);
    this.cur.set(p, f);
  }

  delete(p: string): void {
    this.touch(p);
    this.cur.delete(p);
  }

  /** Change lines for the exit-0 output, in byte order of the paths (R lines sort by new). */
  changeLines(): { key: string; line: string }[] {
    const out: { key: string; line: string }[] = [];
    const paths = new Set<string>([...this.orig.keys(), ...this.cur.keys()]);
    const isMove: Map<string, { old: string; nw: string }> = new Map();
    for (const m of this.moves) {
      const o = this.orig.get(m.old);
      const nOrig = this.orig.get(m.nw);
      const nCur = this.cur.get(m.nw);
      if (o !== null && o !== undefined && !this.cur.has(m.old) && (nOrig === null || nOrig === undefined) && nCur !== undefined) {
        isMove.set(m.nw, m);
      }
    }
    for (const p of paths) {
      const o = this.orig.get(p);
      const c = this.cur.get(p);
      const oText = o === undefined ? null : o;
      const cText = c === undefined ? null : renderFile(c);
      if (oText === null && cText !== null) {
        const m = isMove.get(p);
        if (m) out.push({ key: p, line: `R ${m.old} -> ${m.nw}` });
        else out.push({ key: p, line: `A ${p}` });
      } else if (oText !== null && cText === null) {
        // A path deleted by a move is covered by its R line, not by a D line.
        let covered = false;
        for (const m of this.moves) {
          if (m.old === p && isMove.has(m.nw)) {
            covered = true;
            break;
          }
        }
        if (!covered) out.push({ key: p, line: `D ${p}` });
      } else if (oText !== null && cText !== null && oText !== cText) {
        out.push({ key: p, line: `M ${p}` });
      }
    }
    out.sort((a, b) => byteCompare(a.key, b.key));
    return out;
  }

  /** Write every change to disk. */
  writeAll(): void {
    const paths = new Set<string>([...this.orig.keys(), ...this.cur.keys()]);
    for (const p of paths) {
      const o = this.orig.get(p);
      const c = this.cur.get(p);
      const oText = o === undefined ? null : o;
      const cText = c === undefined ? null : renderFile(c);
      if (cText !== null && oText !== cText) {
        mkdirSync(dirname(p) === '' ? '.' : dirname(p), { recursive: true });
        writeFileSync(p, cText, 'utf8');
      } else if (cText === null && oText !== null) {
        unlinkSync(p);
      }
    }
  }
}

interface Ctx {
  tree: Tree;
  strict: boolean;
}

interface Edit {
  /** Every path the edit names, in patch order (for the safety check). */
  paths: string[];
  apply(ctx: Ctx): EditResult;
}

/** Check every path an edit names for safety, before anything else about it. */
function unsafePath(e: Edit): string | null {
  for (const p of e.paths) {
    if (!isSafePath(p)) return p;
  }
  return null;
}

// ---------------------------------------------------------------------------
// Unified diffs (SPEC section 6)

interface HunkBodyLine {
  type: ' ' | '-' | '+' | '\\';
  text: string;
}

interface Hunk {
  a: number;
  body: HunkBodyLine[];
}

interface UniSection {
  oldPath: string | null; // null means /dev/null (no file)
  newPath: string | null;
  creation: boolean;
  deletion: boolean;
  hunks: Hunk[];
}

const DIFF_GIT_RE = /^diff --git a\/(\S+) b\/(\S+)$/;
const HUNK_RE = /^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/;

/** Path text after `--- ` or `+++ `: up to the first tab, surrounding spaces removed,
 *  a leading a/ or b/ removed. */
function uniPath(line: string): string {
  let p = line.slice(4).split('\t')[0].trim();
  if (p.startsWith('a/') || p.startsWith('b/')) p = p.slice(2);
  return p;
}

/** Parse a unified patch into its sections (one edit each). Throws ParseFault. */
function parseUnified(lines: string[]): UniSection[] {
  const sections: UniSection[] = [];
  let cur: UniSection | null = null;
  let curHasPair = false;
  let curInHeader = false; // true while the current section has no hunk yet
  let i = 0;
  const n = lines.length;
  while (i < n) {
    const line = lines[i];
    if (line.startsWith('diff --git ')) {
      const m = DIFF_GIT_RE.exec(line);
      if (!m) throw new ParseFault(i + 1);
      cur = { oldPath: m[1], newPath: m[2], creation: false, deletion: false, hunks: [] };
      sections.push(cur);
      curHasPair = false;
      curInHeader = true;
      i++;
      continue;
    }
    if (line.startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ ')) {
      const rawOld = line.slice(4).split('\t')[0].trim();
      const rawNew = lines[i + 1].slice(4).split('\t')[0].trim();
      if (cur !== null && curInHeader && !curHasPair) {
        cur.oldPath = rawOld === '/dev/null' ? null : uniPath(line);
        cur.newPath = rawNew === '/dev/null' ? null : uniPath(lines[i + 1]);
        curHasPair = true;
      } else {
        cur = {
          oldPath: rawOld === '/dev/null' ? null : uniPath(line),
          newPath: rawNew === '/dev/null' ? null : uniPath(lines[i + 1]),
          creation: false,
          deletion: false,
          hunks: [],
        };
        sections.push(cur);
        curHasPair = true;
        curInHeader = true;
      }
      i += 2;
      continue;
    }
    if (line.startsWith('--- ')) {
      if (cur !== null && curInHeader) throw new ParseFault(i + 2);
      i++;
      continue;
    }
    if (line.startsWith('@@')) {
      if (cur === null) throw new ParseFault(i + 1);
      const m = HUNK_RE.exec(line);
      if (!m) throw new ParseFault(i + 1);
      const a = parseInt(m[1], 10);
      i++;
      // Collect the body.
      const body: HunkBodyLine[] = [];
      while (i < n) {
        const bl = lines[i];
        if (bl.startsWith('--- ') && i + 1 < n && lines[i + 1].startsWith('+++ ')) break;
        if (bl === '' || bl.startsWith(' ') || bl.startsWith('-') || bl.startsWith('+') || bl.startsWith('\\')) {
          if (bl === '') body.push({ type: ' ', text: '' });
          else body.push({ type: bl[0] as ' ' | '-' | '+' | '\\', text: bl.slice(1) });
          i++;
        } else {
          break;
        }
      }
      // Empty lines at the end of a body are not part of it.
      while (body.length > 0 && body[body.length - 1].type === ' ' && body[body.length - 1].text === '') {
        body.pop();
      }
      cur.hunks.push({ a, body });
      curInHeader = false;
      continue;
    }
    if (cur !== null && curInHeader) {
      if (line.startsWith('rename from ')) {
        if (!curHasPair) cur.oldPath = line.slice('rename from '.length).trim();
      } else if (line.startsWith('rename to ')) {
        if (!curHasPair) cur.newPath = line.slice('rename to '.length).trim();
      } else if (line.startsWith('new file mode')) {
        cur.creation = true;
      } else if (line.startsWith('deleted file mode')) {
        cur.deletion = true;
      }
      i++;
      continue;
    }
    // Outside bodies, lines that are not part of a section header are ignored.
    i++;
  }
  return sections;
}

/** Build O, N and the context map of a hunk body. */
function hunkON(body: HunkBodyLine[]): { O: string[]; N: string[]; ctx: Map<number, number> } {
  const O: string[] = [];
  const N: string[] = [];
  const ctx = new Map<number, number>();
  for (const bl of body) {
    if (bl.type === ' ') {
      ctx.set(N.length, O.length);
      O.push(bl.text);
      N.push(bl.text);
    } else if (bl.type === '-') {
      O.push(bl.text);
    } else if (bl.type === '+') {
      N.push(bl.text);
    }
  }
  return { O, N, ctx };
}

/** Whether a \ line follows the hunk's last context or + line. */
function hunkEndsNoNewline(body: HunkBodyLine[]): boolean {
  for (let k = body.length - 1; k >= 0; k--) {
    if (body[k].type === ' ' || body[k].type === '+') {
      return k + 1 < body.length && body[k + 1].type === '\\';
    }
  }
  return false;
}

/** Apply one unified section to the tree. The section changes nothing on failure. */
function applyUnifiedSection(s: UniSection, ctx: Ctx): EditResult {
  const tree = ctx.tree;
  const oldP = s.oldPath;
  const newP = s.newPath;
  const isCreation = s.creation || oldP === null;
  const isDeletion = s.deletion || newP === null;
  if (isCreation) {
    if (newP === null) return fail('unsafe', '');
    if (tree.exists(newP)) return fail('exists', newP);
    const plus: string[] = [];
    let noEol = false;
    for (const h of s.hunks) {
      for (let k = 0; k < h.body.length; k++) {
        if (h.body[k].type === '+') plus.push(h.body[k].text);
      }
    }
    // A created file ends with a line break unless a \ line follows its last + line.
    const allPlus: Array<{ h: Hunk; idx: number }> = [];
    for (const h of s.hunks) {
      h.body.forEach((bl, idx) => {
        if (bl.type === '+') allPlus.push({ h, idx });
      });
    }
    if (allPlus.length > 0) {
      const last = allPlus[allPlus.length - 1];
      if (last.idx + 1 < last.h.body.length && last.h.body[last.idx + 1].type === '\\') noEol = true;
    }
    tree.set(newP, { br: '\n', lines: plus, eol: plus.length > 0 && !noEol });
    return { ok: true };
  }
  if (isDeletion) {
    if (oldP === null) return fail('unsafe', '');
    if (!tree.exists(oldP)) return fail('missing', oldP);
    tree.delete(oldP);
    return { ok: true };
  }
  if (oldP === null || newP === null) return fail('unsafe', oldP ?? newP ?? '');
  const isMove = oldP !== newP;
  if (!tree.exists(oldP)) return fail('missing', oldP);
  if (isMove && tree.exists(newP)) return fail('exists', newP);
  const file = tree.get(oldP) as WorkFile;
  let lines = [...file.lines];
  let eol = file.eol;
  let d = 0;
  for (const h of s.hunks) {
    const { O, N, ctx: ctxMap } = hunkON(h.body);
    if (O.length === 0) {
      const pos = Math.max(0, Math.min(h.a + d, lines.length));
      const atEnd = pos === lines.length;
      lines = [...lines.slice(0, pos), ...N, ...lines.slice(pos)];
      if (atEnd) eol = !hunkEndsNoNewline(h.body);
      d += N.length;
      continue;
    }
    const found = findOccurrences(lines, O, ctx.strict, 0);
    if (found === null) return fail('no-match', oldP);
    const target = h.a - 1 + d;
    let best = found.positions[0];
    let bestDist = Math.abs(best - target);
    for (const p of found.positions) {
      const dist = Math.abs(p - target);
      if (dist < bestDist) {
        best = p;
        bestDist = dist;
      }
    }
    const runsToEnd = best + O.length === lines.length;
    lines = replaceLines(lines, best, O, N, found.tier, ctxMap);
    if (runsToEnd) eol = !hunkEndsNoNewline(h.body);
    d += N.length - O.length;
  }
  const out: WorkFile = { br: file.br, lines, eol };
  if (isMove) {
    tree.delete(oldP);
    tree.set(newP, out);
    tree.moves.push({ old: oldP, nw: newP });
  } else {
    tree.set(oldP, out);
  }
  return { ok: true };
}

function unifiedEdits(lines: string[]): Edit[] {
  const sections = parseUnified(lines);
  return sections.map((s) => {
    const paths: string[] = [];
    if (s.oldPath !== null) paths.push(s.oldPath);
    if (s.newPath !== null && s.newPath !== s.oldPath) paths.push(s.newPath);
    return {
      paths,
      apply: (ctx: Ctx) => applyUnifiedSection(s, ctx),
    };
  });
}

// ---------------------------------------------------------------------------
// SEARCH/REPLACE blocks (SPEC section 7)

interface SRBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
  searchLine: number; // 1-based line of the <<<<<<< SEARCH line
}

function isSearchMarker(line: string): boolean {
  return rtrimWS(line) === '<<<<<<< SEARCH';
}

/** Parse SEARCH/REPLACE blocks. Throws ParseFault. */
function parseSearchReplace(lines: string[]): SRBlock[] {
  const blocks: SRBlock[] = [];
  let prevPath: string | null = null;
  let prevReplaceEnd = -1; // 0-based index of the previous block's >>>>>>> REPLACE line
  let i = 0;
  const n = lines.length;
  while (i < n) {
    if (!isSearchMarker(lines[i])) {
      i++;
      continue;
    }
    const searchIdx = i;
    // The path: nearest line before the SEARCH line and after the previous block's
    // REPLACE line (or the start) that is not blank and does not start with ```.
    let path: string | null = null;
    for (let j = i - 1; j > prevReplaceEnd; j--) {
      const t = lines[j].trim();
      if (t === '') continue;
      if (t.startsWith('```')) continue;
      path = t;
      break;
    }
    if (path === null) {
      if (prevPath !== null) path = prevPath;
      else throw new ParseFault(searchIdx + 1);
    }
    let eq = -1;
    for (let j = i + 1; j < n; j++) {
      if (rtrimWS(lines[j]) === '=======') {
        eq = j;
        break;
      }
    }
    if (eq === -1) throw new ParseFault(searchIdx + 1);
    let rep = -1;
    for (let j = eq + 1; j < n; j++) {
      if (rtrimWS(lines[j]) === '>>>>>>> REPLACE') {
        rep = j;
        break;
      }
    }
    if (rep === -1) throw new ParseFault(searchIdx + 1);
    blocks.push({
      path,
      oldLines: lines.slice(i + 1, eq),
      newLines: lines.slice(eq + 1, rep),
      searchLine: searchIdx + 1,
    });
    prevPath = path;
    prevReplaceEnd = rep;
    i = rep + 1;
  }
  return blocks;
}

function applySRBlock(b: SRBlock, ctx: Ctx): EditResult {
  const tree = ctx.tree;
  if (b.oldLines.length === 0) {
    if (tree.exists(b.path)) return fail('exists', b.path);
    tree.set(b.path, { br: '\n', lines: [...b.newLines], eol: b.newLines.length > 0 });
    return { ok: true };
  }
  const file = tree.get(b.path);
  if (file === null) return fail('missing', b.path);
  const found = findOccurrences(file.lines, b.oldLines, ctx.strict, 0);
  if (found === null) return fail('no-match', b.path);
  if (found.positions.length > 1) return fail('ambiguous', b.path);
  const lines = replaceLines(file.lines, found.positions[0], b.oldLines, b.newLines, found.tier, new Map());
  tree.set(b.path, { br: file.br, lines, eol: file.eol });
  return { ok: true };
}

function searchReplaceEdits(lines: string[]): Edit[] {
  const blocks = parseSearchReplace(lines);
  return blocks.map((b) => ({
    paths: [b.path],
    apply: (ctx: Ctx) => applySRBlock(b, ctx),
  }));
}

// ---------------------------------------------------------------------------
// V4A patches (SPEC section 8)

type V4ASection =
  | { kind: 'add'; path: string; lines: string[] }
  | { kind: 'delete'; path: string }
  | { kind: 'update'; path: string; moveTo: string | null; chunks: V4AChunk[]; updateLine: number };

interface V4AChunk {
  anchor: string | null;
  eof: boolean;
  body: HunkBodyLine[];
}

const ADD_PREFIX = '*** Add File: ';
const DELETE_PREFIX = '*** Delete File: ';
const UPDATE_PREFIX = '*** Update File: ';
const MOVE_PREFIX = '*** Move to: ';

/** Parse a V4A patch into its sections. Throws ParseFault. */
function parseV4A(lines: string[]): V4ASection[] {
  const n = lines.length;
  let firstNonBlank = -1;
  let lastNonBlank = -1;
  for (let i = 0; i < n; i++) {
    if (lines[i].trim() !== '') {
      if (firstNonBlank === -1) firstNonBlank = i;
      lastNonBlank = i;
    }
  }
  if (firstNonBlank === -1) throw new ParseFault(1);
  if (lines[firstNonBlank].trim() !== '*** Begin Patch') throw new ParseFault(firstNonBlank + 1);
  if (lines[lastNonBlank].trim() !== '*** End Patch') throw new ParseFault(n + 1);
  const sections: V4ASection[] = [];
  let i = firstNonBlank + 1;
  while (i <= lastNonBlank) {
    const line = lines[i];
    if (line.trim() === '') {
      i++;
      continue;
    }
    if (line.trim() === '*** End Patch') break;
    if (line.startsWith(ADD_PREFIX) || line.startsWith(DELETE_PREFIX) || line.startsWith(UPDATE_PREFIX)) {
      const isAdd = line.startsWith(ADD_PREFIX);
      const isDelete = line.startsWith(DELETE_PREFIX);
      const prefix = isAdd ? ADD_PREFIX : isDelete ? DELETE_PREFIX : UPDATE_PREFIX;
      const path = line.slice(prefix.length).trim();
      const headerLine = i + 1;
      i++;
      // Collect the section's lines, up to the next section header or *** End Patch.
      const raw: Array<{ text: string; line: number }> = [];
      while (i <= lastNonBlank) {
        const l = lines[i];
        if (l.trim() === '*** End Patch') break;
        if (l.startsWith(ADD_PREFIX) || l.startsWith(DELETE_PREFIX) || l.startsWith(UPDATE_PREFIX)) break;
        raw.push({ text: l, line: i + 1 });
        i++;
      }
      // Blank lines at the end of a section are not part of it.
      while (raw.length > 0 && raw[raw.length - 1].text.trim() === '') raw.pop();
      if (isAdd) {
        const fileLines: string[] = [];
        for (const r of raw) {
          if (r.text.startsWith('+')) fileLines.push(r.text.slice(1));
          else if (r.text === '') fileLines.push('');
          else throw new ParseFault(r.line);
        }
        sections.push({ kind: 'add', path, lines: fileLines });
      } else if (isDelete) {
        if (raw.length > 0) throw new ParseFault(raw[0].line);
        sections.push({ kind: 'delete', path });
      } else {
        let moveTo: string | null = null;
        let idx = 0;
        if (idx < raw.length && raw[idx].text.startsWith(MOVE_PREFIX)) {
          moveTo = raw[idx].text.slice(MOVE_PREFIX.length).trim();
          idx++;
        }
        const chunks: V4AChunk[] = [];
        while (idx < raw.length) {
          let anchor: string | null = null;
          let eof = false;
          if (raw[idx].text.startsWith('@@')) {
            const a = raw[idx].text.slice(2).trim();
            anchor = a === '' ? null : a;
            idx++;
          } else if (chunks.length > 0) {
            throw new ParseFault(raw[idx].line);
          }
          const body: HunkBodyLine[] = [];
          while (idx < raw.length) {
            const r = raw[idx];
            if (r.text.startsWith('@@')) break;
            if (r.text.trim() === '*** End of File') {
              eof = true;
              idx++;
              break;
            }
            if (r.text === '' || r.text.startsWith(' ') || r.text.startsWith('-') || r.text.startsWith('+')) {
              if (r.text === '') body.push({ type: ' ', text: '' });
              else body.push({ type: r.text[0] as ' ' | '-' | '+', text: r.text.slice(1) });
              idx++;
            } else {
              throw new ParseFault(r.line);
            }
          }
          chunks.push({ anchor, eof, body });
        }
        if (chunks.length === 0 && moveTo === null) throw new ParseFault(headerLine);
        sections.push({ kind: 'update', path, moveTo, chunks, updateLine: headerLine });
      }
      continue;
    }
    throw new ParseFault(i + 1);
  }
  return sections;
}

/** Find the first line at or after cursor equal to anchor, at the first tier with one. */
function findAnchor(F: string[], anchor: string, strict: boolean, cursor: number): number | null {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) {
    const a = normLine(anchor, t);
    for (let i = cursor; i < F.length; i++) {
      if (normLine(F[i], t) === a) return i;
    }
  }
  return null;
}

function applyV4ASection(s: V4ASection, ctx: Ctx): EditResult {
  const tree = ctx.tree;
  if (s.kind === 'add') {
    if (tree.exists(s.path)) return fail('exists', s.path);
    tree.set(s.path, { br: '\n', lines: [...s.lines], eol: s.lines.length > 0 });
    return { ok: true };
  }
  if (s.kind === 'delete') {
    if (!tree.exists(s.path)) return fail('missing', s.path);
    tree.delete(s.path);
    return { ok: true };
  }
  // update
  if (!tree.exists(s.path)) return fail('missing', s.path);
  if (s.moveTo !== null && tree.exists(s.moveTo)) return fail('exists', s.moveTo);
  const file = tree.get(s.path) as WorkFile;
  let lines = [...file.lines];
  let cursor = 0;
  for (const ch of s.chunks) {
    if (ch.anchor !== null) {
      const ai = findAnchor(lines, ch.anchor, ctx.strict, cursor);
      if (ai === null) return fail('no-match', s.path);
      cursor = ai + 1;
    }
    const { O, N, ctx: ctxMap } = hunkON(ch.body);
    if (O.length === 0) {
      const pos = ch.eof ? lines.length : cursor;
      lines = [...lines.slice(0, pos), ...N, ...lines.slice(pos)];
      cursor = pos + N.length;
      continue;
    }
    const found = findOccurrences(lines, O, ctx.strict, cursor);
    if (found === null) return fail('no-match', s.path);
    let pos: number | null = null;
    for (const p of found.positions) {
      if (ch.eof) {
        if (p + O.length === lines.length) {
          pos = p;
          break;
        }
      } else {
        pos = p;
        break;
      }
    }
    if (pos === null) return fail('no-match', s.path);
    lines = replaceLines(lines, pos, O, N, found.tier, ctxMap);
    cursor = pos + N.length;
  }
  const out: WorkFile = { br: file.br, lines, eol: file.eol };
  if (s.moveTo !== null) {
    tree.delete(s.path);
    tree.set(s.moveTo, out);
    tree.moves.push({ old: s.path, nw: s.moveTo });
  } else {
    tree.set(s.path, out);
  }
  return { ok: true };
}

function v4aEdits(lines: string[]): Edit[] {
  const sections = parseV4A(lines);
  return sections.map((s) => {
    const paths: string[] = [s.path];
    if (s.kind === 'update' && s.moveTo !== null && s.moveTo !== s.path) paths.push(s.moveTo);
    return {
      paths,
      apply: (ctx: Ctx) => applyV4ASection(s, ctx),
    };
  });
}

// ---------------------------------------------------------------------------
// JSON edits (SPEC section 9)

type JsonEdit =
  | { kind: 'create'; path: string; fileText: string }
  | { kind: 'str_replace'; path: string; oldStr: string; newStr: string }
  | { kind: 'insert'; path: string; insertLine: number; newStr: string };

function isRecord(v: unknown): v is Record<string, unknown> {
  return typeof v === 'object' && v !== null && !Array.isArray(v);
}

/** Validate one edit object; returns it, or null when it is not a valid edit object. */
function asJsonEdit(v: unknown): JsonEdit | null {
  if (!isRecord(v)) return null;
  const path = v['path'];
  const command = v['command'];
  if (typeof path !== 'string' || typeof command !== 'string') return null;
  if (command === 'create') {
    if (typeof v['file_text'] !== 'string') return null;
    return { kind: 'create', path, fileText: v['file_text'] };
  }
  if (command === 'str_replace') {
    if (typeof v['old_str'] !== 'string' || v['old_str'] === '') return null;
    if (v['new_str'] === undefined) return { kind: 'str_replace', path, oldStr: v['old_str'], newStr: '' };
    if (typeof v['new_str'] !== 'string') return null;
    return { kind: 'str_replace', path, oldStr: v['old_str'], newStr: v['new_str'] };
  }
  if (command === 'insert') {
    if (typeof v['insert_line'] !== 'number' || !Number.isInteger(v['insert_line'])) return null;
    if (typeof v['new_str'] !== 'string') return null;
    return { kind: 'insert', path, insertLine: v['insert_line'], newStr: v['new_str'] };
  }
  return null;
}

/** Count occurrences of needle in haystack, positions may overlap. */
function countOccurrences(haystack: string, needle: string): number {
  let count = 0;
  let idx = haystack.indexOf(needle, 0);
  while (idx !== -1) {
    count++;
    idx = haystack.indexOf(needle, idx + 1);
  }
  return count;
}

function applyJsonEdit(e: JsonEdit, ctx: Ctx): EditResult {
  const tree = ctx.tree;
  if (e.kind === 'create') {
    if (tree.exists(e.path)) return fail('exists', e.path);
    tree.set(e.path, parseFile(e.fileText));
    return { ok: true };
  }
  if (e.kind === 'str_replace') {
    const file = tree.get(e.path);
    if (file === null) return fail('missing', e.path);
    const text = renderFile(file);
    let result: string;
    if (file.br === '\r\n') {
      const t = text.replace(/\r\n/g, '\n');
      const o = e.oldStr.replace(/\r\n/g, '\n');
      const nw = e.newStr.replace(/\r\n/g, '\n');
      const c = countOccurrences(t, o);
      if (c === 0) return fail('no-match', e.path);
      if (c > 1) return fail('ambiguous', e.path);
      result = t.replace(o, nw).replace(/\n/g, '\r\n');
    } else {
      const c = countOccurrences(text, e.oldStr);
      if (c === 0) return fail('no-match', e.path);
      if (c > 1) return fail('ambiguous', e.path);
      result = text.replace(e.oldStr, e.newStr);
    }
    tree.set(e.path, parseFile(result));
    return { ok: true };
  }
  // insert
  const file = tree.get(e.path);
  if (file === null) return fail('missing', e.path);
  if (e.insertLine < 0 || e.insertLine > file.lines.length) return fail('no-match', e.path);
  const ins = patchLines(e.newStr);
  const lines = [...file.lines.slice(0, e.insertLine), ...ins, ...file.lines.slice(e.insertLine)];
  tree.set(e.path, { br: file.br, lines, eol: file.eol });
  return { ok: true };
}

/** Parse a JSON patch (array form or JSON Lines). Throws ParseFault. */
function parseJson(text: string, lines: string[]): JsonEdit[] {
  // The line where the array starts, for array-form faults: the first non-blank line.
  let firstNonBlank = -1;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].trim() !== '') {
      firstNonBlank = i;
      break;
    }
  }
  if (firstNonBlank === -1) return [];
  const first = lines[firstNonBlank];
  const firstChar = first[first.search(/\S/)];
  if (firstChar === '[') {
    let parsed: unknown;
    try {
      parsed = JSON.parse(text);
    } catch {
      throw new ParseFault(firstNonBlank + 1);
    }
    if (!Array.isArray(parsed)) throw new ParseFault(firstNonBlank + 1);
    const edits: JsonEdit[] = [];
    for (const el of parsed) {
      const ed = asJsonEdit(el);
      if (ed === null) throw new ParseFault(firstNonBlank + 1);
      edits.push(ed);
    }
    return edits;
  }
  // JSON Lines: one edit object a line, blank lines ignored.
  const edits: JsonEdit[] = [];
  for (let i = 0; i < lines.length; i++) {
    const l = lines[i];
    if (l.trim() === '') continue;
    let parsed: unknown;
    try {
      parsed = JSON.parse(l);
    } catch {
      throw new ParseFault(i + 1);
    }
    const ed = asJsonEdit(parsed);
    if (ed === null) throw new ParseFault(i + 1);
    edits.push(ed);
  }
  return edits;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const edits = parseJson(text, lines);
  return edits.map((e) => ({
    paths: [e.path],
    apply: (ctx: Ctx) => applyJsonEdit(e, ctx),
  }));
}

// ---------------------------------------------------------------------------
// Format detection (SPEC section 4)

function detectFormat(lines: string[]): string | null {
  let firstNonBlank = -1;
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].trim() !== '') {
      firstNonBlank = i;
      break;
    }
  }
  if (firstNonBlank === -1) return null;
  const first = lines[firstNonBlank];
  if (first.trim() === '*** Begin Patch') return 'v4a';
  const firstNonWS = first[first.search(/\S/)];
  if (firstNonWS === '[' || firstNonWS === '{') return 'json';
  for (const l of lines) {
    if (rtrimWS(l) === '<<<<<<< SEARCH') return 'search-replace';
  }
  for (let i = 0; i < lines.length; i++) {
    if (lines[i].startsWith('diff --git ')) return 'unified';
    if (lines[i].startsWith('--- ') && i + 1 < lines.length && lines[i + 1].startsWith('+++ ')) return 'unified';
  }
  return null;
}

// ---------------------------------------------------------------------------
// Driver

function out(line: string): void {
  process.stdout.write(line + '\n');
}

function exit2(msg: string): number {
  out(msg);
  return 2;
}

/** Parse the command line. Returns the options, or null on a usage error. */
function parseArgs(args: string[]): { format: string; check: boolean; strict: boolean; patch: string | null } | null {
  let format = 'auto';
  let check = false;
  let strict = false;
  let seenFormat = false;
  let seenCheck = false;
  let seenStrict = false;
  const positionals: string[] = [];
  let endOpts = false;
  for (const a of args) {
    if (!endOpts && a === '--') {
      endOpts = true;
      continue;
    }
    if (!endOpts && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=')) {
        const v = a.slice('--format='.length);
        if (seenFormat) return null;
        if (v !== 'unified' && v !== 'search-replace' && v !== 'v4a' && v !== 'json' && v !== 'auto') return null;
        seenFormat = true;
        format = v;
      } else if (a === '--check') {
        if (seenCheck) return null;
        seenCheck = true;
        check = true;
      } else if (a === '--strict') {
        if (seenStrict) return null;
        seenStrict = true;
        strict = true;
      } else {
        return null;
      }
    } else {
      positionals.push(a);
    }
  }
  if (positionals.length > 1) return null;
  return { format, check, strict, patch: positionals.length === 1 ? positionals[0] : null };
}

function runCli(args: string[]): number {
  const opts = parseArgs(args);
  if (opts === null) return exit2('error: usage');
  // Read the patch.
  let patchText: string;
  if (opts.patch === null || opts.patch === '-') {
    try {
      patchText = readFileSync(0, 'utf8');
    } catch {
      return exit2('error: no-patch');
    }
  } else {
    try {
      patchText = readFileSync(opts.patch, 'utf8');
    } catch {
      return exit2('error: no-patch');
    }
  }
  const lines = patchLines(patchText);
  const format = opts.format === 'auto' ? detectFormat(lines) : opts.format;
  if (format === null) return exit2('error: format');
  let edits: Edit[];
  try {
    if (format === 'unified') edits = unifiedEdits(lines);
    else if (format === 'search-replace') edits = searchReplaceEdits(lines);
    else if (format === 'v4a') edits = v4aEdits(lines);
    else edits = jsonEdits(patchText, lines);
  } catch (err) {
    if (err instanceof ParseFault) return exit2(`error: parse ${err.line}`);
    throw err;
  }
  if (edits.length === 0) return exit2('error: parse 1');
  const tree = new Tree();
  const ctx: Ctx = { tree, strict: opts.strict };
  const failures: EditFailure[] = [];
  for (const e of edits) {
    const unsafe = unsafePath(e);
    if (unsafe !== null) {
      failures.push(fail('unsafe', unsafe));
      continue;
    }
    const r = e.apply(ctx);
    if (!r.ok) failures.push(r);
  }
  if (failures.length > 0) {
    for (const f of failures) out(`error: ${f.code} ${f.path}`);
    out(`failed: ${failures.length} of ${edits.length} edits`);
    return 1;
  }
  const changes = tree.changeLines();
  if (!opts.check) tree.writeAll();
  for (const c of changes) out(c.line);
  out(changes.length === 1 ? 'ok: 1 file' : `ok: ${changes.length} files`);
  return 0;
}

const envUrl = process.env.MAKEFUN_ENV_URL;
if (envUrl) {
  runTrial(envUrl).then(
    () => undefined,
    (err: unknown) => {
      process.stderr.write(String(err) + '\n');
      process.exitCode = 1;
    },
  );
} else {
  process.exitCode = runCli(process.argv.slice(2));
}


