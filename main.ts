// main.ts is mend, the CLI SPEC.md specifies. Node 22, the standard library alone; run it as `node main.ts [options] [PATCH]`.
//
// It does all of SPEC.md: the command line (section 1), the output and exit codes (section 2), safe paths and file
// lines (section 3), format detection (section 4), line matching at three tiers (section 5), unified diffs
// (section 6), SEARCH/REPLACE blocks (section 7), V4A patches (section 8), JSON edits (section 9) and order and
// atomicity (section 10). Its last lines hand a trial over to runner.ts when MAKEFUN_ENV_URL is set: keep that
// hand-over and runner.ts as they are.

import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

/** What the format readers share: --strict, and the moves successful edits record (for `R` output lines). */
interface Ctx {
  strict: boolean;
  moves: Array<{ old: string; nw: string }>;
}

/** The tree as the edits leave it: changed paths in `now` (null: deleted), the rest read from disk. */
class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

/** A file as lines: its own line break, and whether it ends with one (SPEC section 3). */
interface FileState {
  lines: string[];
  br: '\r\n' | '\n';
  final: boolean;
}

function splitFile(text: string): FileState {
  if (text === '') return { lines: [], br: '\n', final: false };
  const nl = text.indexOf('\n');
  const br: '\r\n' | '\n' = nl > 0 && text[nl - 1] === '\r' ? '\r\n' : '\n';
  const lines = text.split(br);
  const final = text.endsWith(br);
  if (final) lines.pop();
  return { lines, br, final };
}

function joinFile(f: FileState): string {
  if (f.lines.length === 0) return '';
  return f.lines.join(f.br) + (f.final ? f.br : '');
}

/** Section 5: matching lines. */
const stripTrail = (s: string): string => s.replace(/[ \t]+$/, '');
const stripBoth = (s: string): string => s.replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
const leadWs = (s: string): string => /^[ \t]*/.exec(s)![0];

function lineEq(a: string, b: string, tier: number): boolean {
  if (tier === 0) return a === b;
  if (tier === 1) return stripTrail(a) === stripTrail(b);
  return stripBoth(a) === stripBoth(b);
}

/** Positions i >= `from` where O matches the file's lines at `tier`; when `eof`, only ones ending at the last line. */
function occurrences(o: string[], file: string[], tier: number, from = 0, eof = false): number[] {
  const out: number[] = [];
  if (o.length === 0) return out;
  for (let i = from; i + o.length <= file.length; i++) {
    if (eof && i + o.length !== file.length) continue;
    let ok = true;
    for (let k = 0; k < o.length; k++) {
      if (!lineEq(o[k], file[i + k], tier)) {
        ok = false;
        break;
      }
    }
    if (ok) out.push(i);
  }
  return out;
}

/** The first tier (0, 1, 2; with --strict only 0) at which O occurs at least once, or -1. */
function findTier(o: string[], file: string[], strict: boolean, from = 0, eof = false): number {
  const tiers = strict ? [0] : [0, 1, 2];
  for (const t of tiers) if (occurrences(o, file, t, from, eof).length > 0) return t;
  return -1;
}

/**
 * A replacement: O the old lines, N the new lines, and nSrc[j] the index into O of N[j] when N[j] is a context
 * line (written as the file's own matched line), else -1.
 */
interface Repl {
  o: string[];
  n: string[];
  nSrc: number[];
}

/** The lines that replace file[at .. at+o.length]: context lines from the file, the rest re-indented at tier 2. */
function replacement(file: string[], at: number, r: Repl, tier: number): string[] {
  if (r.o.length === 0) return [...r.n];
  const f = tier === 2 ? leadWs(file[at]) : '';
  const p = tier === 2 ? leadWs(r.o[0]) : '';
  return r.n.map((l, j) => {
    const s = r.nSrc[j];
    if (s !== -1) return file[at + s];
    if (tier === 2 && l !== '' && !/^[ \t]+$/.test(l) && l.startsWith(p)) return f + l.slice(p.length);
    return l;
  });
}

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

/** Section 6: unified diffs. */

const HUNK_RE = /^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@/;

interface Hunk {
  a: number;
  body: string[];
}

interface UniSection {
  diffOld: string | null;
  diffNew: string | null;
  headOld: string | null;
  hasHeadOld: boolean;
  headNew: string | null;
  hasHeadNew: boolean;
  renameFrom: string | null;
  renameTo: string | null;
  newFile: boolean;
  deletedFile: boolean;
  hunks: Hunk[];
}

/** The path after `--- `/`+++ `: up to the first tab, surrounding spaces removed, a/ or b/ stripped; null is /dev/null. */
function uniPath(raw: string): string | null {
  const p = raw.split('\t')[0].trim();
  if (p === '/dev/null') return null;
  return p.replace(/^[ab]\//, '');
}

function newUniSection(): UniSection {
  return {
    diffOld: null, diffNew: null,
    headOld: null, hasHeadOld: false,
    headNew: null, hasHeadNew: false,
    renameFrom: null, renameTo: null,
    newFile: false, deletedFile: false,
    hunks: [],
  };
}

function parseUnified(lines: string[]): UniSection[] {
  const sections: UniSection[] = [];
  let cur: UniSection | null = null;
  let inHeader = false;
  const headerLine = (l: string): void => {
    if (cur === null) return;
    if (l.startsWith('--- ')) {
      cur.headOld = uniPath(l.slice(4));
      cur.hasHeadOld = true;
    } else if (l.startsWith('+++ ')) {
      cur.headNew = uniPath(l.slice(4));
      cur.hasHeadNew = true;
    } else if (l.startsWith('rename from ')) cur.renameFrom = l.slice(12).trim();
    else if (l.startsWith('rename to ')) cur.renameTo = l.slice(10).trim();
    else if (l.startsWith('new file mode')) cur.newFile = true;
    else if (l.startsWith('deleted file mode')) cur.deletedFile = true;
  };
  let i = 0;
  while (i < lines.length) {
    const l = lines[i]!;
    if (l.startsWith('diff --git ') || l === 'diff --git') {
      const m = /^diff --git a\/(\S+) b\/(\S+)\s*$/.exec(l);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      cur = newUniSection();
      cur.diffOld = m[1]!;
      cur.diffNew = m[2]!;
      sections.push(cur);
      inHeader = true;
      i++;
      continue;
    }
    if (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      if (cur === null || !inHeader) {
        cur = newUniSection();
        sections.push(cur);
        inHeader = true;
      }
      headerLine(l);
      headerLine(lines[i + 1]!);
      i += 2;
      continue;
    }
    if (l.startsWith('@@')) {
      const m = HUNK_RE.exec(l);
      if (!m || cur === null) throw new Exit2(`error: parse ${i + 1}`);
      inHeader = false;
      const body: string[] = [];
      let j = i + 1;
      while (j < lines.length) {
        const b = lines[j]!;
        if (b.startsWith('diff --git ') || b === 'diff --git') break;
        if (b.startsWith('--- ') && (lines[j + 1] ?? '').startsWith('+++ ')) break;
        if (b === '' || b[0] === ' ' || b[0] === '-' || b[0] === '+' || b[0] === '\\') {
          body.push(b);
          j++;
        } else break;
      }
      while (body.length > 0 && body[body.length - 1] === '') body.pop();
      cur.hunks.push({ a: Number(m[1]), body });
      i = j;
      continue;
    }
    if (cur !== null && inHeader) {
      if (l.startsWith('--- ')) throw new Exit2(`error: parse ${i + 2}`);
      headerLine(l);
      i++;
      continue;
    }
    i++;
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections;
}

/** A hunk's body as a replacement, and whether a `\` line follows its last context or `+` line. */
function hunkRepl(body: string[]): { r: Repl; noBreak: boolean } {
  const o: string[] = [];
  const n: string[] = [];
  const nSrc: number[] = [];
  for (const b of body) {
    if (b === '' || b[0] === ' ') {
      const t = b === '' ? '' : b.slice(1);
      o.push(t);
      n.push(t);
      nSrc.push(o.length - 1);
    } else if (b[0] === '-') o.push(b.slice(1));
    else if (b[0] === '+') {
      n.push(b.slice(1));
      nSrc.push(-1);
    }
  }
  let lastCtxPlus = -1;
  for (let k = 0; k < body.length; k++) {
    const b = body[k]!;
    if (b === '' || b[0] === ' ' || b[0] === '+') lastCtxPlus = k;
  }
  const noBreak = lastCtxPlus >= 0 && lastCtxPlus + 1 < body.length && body[lastCtxPlus + 1]![0] === '\\';
  return { r: { o, n, nSrc }, noBreak };
}

/** Apply a section's hunks in order to a file's state; `path` names the file a failure concerns. */
function applyHunks(state: FileState, hunks: Hunk[], strict: boolean, path: string): FileState {
  let lines = [...state.lines];
  let final = state.final;
  let d = 0;
  for (const h of hunks) {
    const { r, noBreak } = hunkRepl(h.body);
    if (r.o.length > 0) {
      const tier = findTier(r.o, lines, strict);
      if (tier < 0) throw new Fail('no-match', path);
      const occs = occurrences(r.o, lines, tier);
      const target = h.a - 1 + d;
      let best = occs[0]!;
      for (const p of occs) if (Math.abs(p - target) < Math.abs(best - target)) best = p;
      const atEnd = best + r.o.length === lines.length;
      const repl = replacement(lines, best, r, tier);
      lines = [...lines.slice(0, best), ...repl, ...lines.slice(best + r.o.length)];
      if (atEnd) final = !noBreak;
    } else {
      const at = Math.max(0, Math.min(h.a + d, lines.length));
      lines = [...lines.slice(0, at), ...r.n, ...lines.slice(at)];
      if (at === lines.length) final = !noBreak;
    }
    d += r.n.length - r.o.length;
  }
  return { lines, br: state.br, final };
}

/** Whether a `\` line follows the last `+` line of a creation's hunks (so the created file ends bare). */
function createdEndsBare(hunks: Hunk[]): boolean {
  for (let hi = hunks.length - 1; hi >= 0; hi--) {
    const body = hunks[hi]!.body;
    for (let k = body.length - 1; k >= 0; k--) {
      if (body[k]![0] === '+') return k + 1 < body.length && body[k + 1]![0] === '\\';
    }
  }
  return false;
}

function unifiedEdits(lines: string[], ctx: Ctx): Edit[] {
  const sections = parseUnified(lines);
  return sections.map((s) => {
    const oldP = s.hasHeadOld ? s.headOld : (s.renameFrom ?? s.diffOld);
    const newP = s.hasHeadNew ? s.headNew : (s.renameTo ?? s.diffNew);
    return (tree: Tree): void => {
      if (oldP === null || s.newFile) {
        const p = newP ?? oldP ?? '';
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        const ls: string[] = [];
        for (const h of s.hunks) for (const b of h.body) if (b[0] === '+') ls.push(b.slice(1));
        tree.now.set(p, ls.length === 0 ? '' : ls.join('\n') + (createdEndsBare(s.hunks) ? '' : '\n'));
        return;
      }
      if (newP === null || s.deletedFile) {
        const p = oldP;
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
        return;
      }
      const op = oldP;
      const np = newP;
      if (!safe(op)) throw new Fail('unsafe', op);
      if (!safe(np)) throw new Fail('unsafe', np);
      if (op !== np) {
        if (tree.get(op) === null) throw new Fail('missing', op);
        if (tree.get(np) !== null) throw new Fail('exists', np);
        const out = applyHunks(splitFile(tree.get(op)!), s.hunks, ctx.strict, op);
        tree.now.set(op, null);
        tree.now.set(np, joinFile(out));
        ctx.moves.push({ old: op, nw: np });
        return;
      }
      if (tree.get(op) === null) throw new Fail('missing', op);
      const out = applyHunks(splitFile(tree.get(op)!), s.hunks, ctx.strict, op);
      tree.now.set(op, joinFile(out));
    };
  });
}

/** Section 7: SEARCH/REPLACE blocks. */

interface SRBlock {
  path: string;
  oldLines: string[];
  newLines: string[];
}

function parseSearchReplace(lines: string[]): SRBlock[] {
  const blocks: SRBlock[] = [];
  let prevReplaceEnd = 0;
  let prevPath: string | null = null;
  let i = 0;
  while (i < lines.length) {
    if (lines[i]!.trimEnd() === '<<<<<<< SEARCH') {
      let path: string | null = null;
      for (let j = i - 1; j >= prevReplaceEnd; j--) {
        const t = lines[j]!.trim();
        if (t === '' || t.startsWith('```')) continue;
        path = t;
        break;
      }
      if (path === null) {
        if (prevPath === null) throw new Exit2(`error: parse ${i + 1}`);
        path = prevPath;
      }
      let k = i + 1;
      while (k < lines.length && lines[k]!.trimEnd() !== '=======') k++;
      if (k >= lines.length) throw new Exit2(`error: parse ${i + 1}`);
      let m = k + 1;
      while (m < lines.length && lines[m]!.trimEnd() !== '>>>>>>> REPLACE') m++;
      if (m >= lines.length) throw new Exit2(`error: parse ${i + 1}`);
      blocks.push({ path, oldLines: lines.slice(i + 1, k), newLines: lines.slice(k + 1, m) });
      prevPath = path;
      prevReplaceEnd = m + 1;
      i = m + 1;
      continue;
    }
    i++;
  }
  if (blocks.length === 0) throw new Exit2('error: parse 1');
  return blocks;
}

function searchReplaceEdits(lines: string[], ctx: Ctx): Edit[] {
  const blocks = parseSearchReplace(lines);
  return blocks.map((b) => (tree: Tree): void => {
    if (!safe(b.path)) throw new Fail('unsafe', b.path);
    if (b.oldLines.length === 0) {
      if (tree.get(b.path) !== null) throw new Fail('exists', b.path);
      tree.now.set(b.path, b.newLines.length === 0 ? '' : b.newLines.join('\n') + '\n');
      return;
    }
    const before = tree.get(b.path);
    if (before === null) throw new Fail('missing', b.path);
    const st = splitFile(before);
    const tier = findTier(b.oldLines, st.lines, ctx.strict);
    if (tier < 0) throw new Fail('no-match', b.path);
    const occs = occurrences(b.oldLines, st.lines, tier);
    if (occs.length > 1) throw new Fail('ambiguous', b.path);
    const at = occs[0]!;
    const r: Repl = { o: b.oldLines, n: b.newLines, nSrc: b.newLines.map(() => -1) };
    const repl = replacement(st.lines, at, r, tier);
    const out = [...st.lines.slice(0, at), ...repl, ...st.lines.slice(at + b.oldLines.length)];
    tree.now.set(b.path, joinFile({ lines: out, br: st.br, final: st.final }));
  });
}

/** Section 8: V4A patches. */

interface VChunk {
  anchor: string | null;
  eof: boolean;
  body: string[];
}

interface VSection {
  kind: 'add' | 'delete' | 'update';
  path: string;
  moveTo: string | null;
  lines: string[];
  chunks: VChunk[];
}

function v4aHeaderKind(l: string): 'add' | 'delete' | 'update' | null {
  if (l.startsWith('*** Add File: ')) return 'add';
  if (l.startsWith('*** Delete File: ')) return 'delete';
  if (l.startsWith('*** Update File: ')) return 'update';
  return null;
}

function parseV4a(lines: string[]): VSection[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  if (lines[first]!.trim() !== '*** Begin Patch') throw new Exit2(`error: parse ${first + 1}`);
  let last = lines.length - 1;
  while (last >= 0 && blank(lines[last]!)) last--;
  if (lines[last]!.trim() !== '*** End Patch') throw new Exit2(`error: parse ${lines.length + 1}`);
  const sections: VSection[] = [];
  let i = first + 1;
  while (i < last) {
    const l = lines[i]!;
    if (blank(l)) {
      i++;
      continue;
    }
    const kind = v4aHeaderKind(l);
    if (kind === null) throw new Exit2(`error: parse ${i + 1}`);
    const prefix = kind === 'add' ? '*** Add File: ' : kind === 'delete' ? '*** Delete File: ' : '*** Update File: ';
    const path = l.slice(prefix.length).trim();
    const headerLine = i + 1;
    const content: number[] = [];
    let j = i + 1;
    while (j < last) {
      if (v4aHeaderKind(lines[j]!) !== null) break;
      content.push(j);
      j++;
    }
    while (content.length > 0 && blank(lines[content[content.length - 1]!]!)) content.pop();
    const sec: VSection = { kind, path, moveTo: null, lines: [], chunks: [] };
    if (kind === 'add') {
      for (const ci of content) {
        const cl = lines[ci]!;
        if (cl.startsWith('+')) sec.lines.push(cl.slice(1));
        else if (cl === '') sec.lines.push('');
        else throw new Exit2(`error: parse ${ci + 1}`);
      }
    } else if (kind === 'delete') {
      if (content.length > 0) throw new Exit2(`error: parse ${content[0]! + 1}`);
    } else {
      let k = 0;
      if (k < content.length && lines[content[k]!]!.startsWith('*** Move to: ')) {
        sec.moveTo = lines[content[k]!]!.slice('*** Move to: '.length).trim();
        k++;
      }
      let cur: VChunk | null = null;
      const pushChunk = (): void => {
        if (cur !== null) {
          sec.chunks.push(cur);
          cur = null;
        }
      };
      for (; k < content.length; k++) {
        const ci = content[k]!;
        const cl = lines[ci]!;
        if (cl === '' || cl[0] === ' ' || cl[0] === '-' || cl[0] === '+') {
          if (cur === null) {
            if (sec.chunks.length === 0) cur = { anchor: null, eof: false, body: [] };
            else throw new Exit2(`error: parse ${ci + 1}`);
          }
          cur.body.push(cl);
        } else if (cl.startsWith('@@')) {
          pushChunk();
          const anchor = cl.slice(2).trim();
          cur = { anchor: anchor === '' ? null : anchor, eof: false, body: [] };
        } else if (cl.trim() === '*** End of File') {
          if (cur !== null) {
            cur.eof = true;
            pushChunk();
          }
        } else {
          throw new Exit2(`error: parse ${ci + 1}`);
        }
      }
      pushChunk();
      if (sec.chunks.length === 0 && sec.moveTo === null) throw new Exit2(`error: parse ${headerLine}`);
    }
    sections.push(sec);
    i = j;
  }
  if (sections.length === 0) throw new Exit2('error: parse 1');
  return sections;
}

/** A V4A chunk's body as a replacement (context lines carry the file's own text). */
function chunkRepl(body: string[]): Repl {
  const o: string[] = [];
  const n: string[] = [];
  const nSrc: number[] = [];
  for (const b of body) {
    if (b === '' || b[0] === ' ') {
      const t = b === '' ? '' : b.slice(1);
      o.push(t);
      n.push(t);
      nSrc.push(o.length - 1);
    } else if (b[0] === '-') o.push(b.slice(1));
    else if (b[0] === '+') {
      n.push(b.slice(1));
      nSrc.push(-1);
    }
  }
  return { o, n, nSrc };
}

function v4aEdits(lines: string[], ctx: Ctx): Edit[] {
  const sections = parseV4a(lines);
  return sections.map((s) => (tree: Tree): void => {
    if (s.kind === 'add') {
      if (!safe(s.path)) throw new Fail('unsafe', s.path);
      if (tree.get(s.path) !== null) throw new Fail('exists', s.path);
      tree.now.set(s.path, s.lines.length === 0 ? '' : s.lines.join('\n') + '\n');
      return;
    }
    if (s.kind === 'delete') {
      if (!safe(s.path)) throw new Fail('unsafe', s.path);
      if (tree.get(s.path) === null) throw new Fail('missing', s.path);
      tree.now.set(s.path, null);
      return;
    }
    if (!safe(s.path)) throw new Fail('unsafe', s.path);
    if (s.moveTo !== null && !safe(s.moveTo)) throw new Fail('unsafe', s.moveTo);
    const before = tree.get(s.path);
    if (before === null) throw new Fail('missing', s.path);
    if (s.moveTo !== null && tree.get(s.moveTo) !== null) throw new Fail('exists', s.moveTo);
    const st = splitFile(before);
    let curLines = [...st.lines];
    let cursor = 0;
    for (const ch of s.chunks) {
      if (ch.anchor !== null) {
        const anchor = ch.anchor;
        let found = -1;
        const tiers = ctx.strict ? [0] : [0, 1, 2];
        for (const t of tiers) {
          for (let k = cursor; k < curLines.length; k++) {
            if (lineEq(anchor, curLines[k], t)) {
              found = k;
              break;
            }
          }
          if (found >= 0) break;
        }
        if (found < 0) throw new Fail('no-match', s.path);
        cursor = found + 1;
      }
      const r = chunkRepl(ch.body);
      if (r.o.length > 0) {
        const tier = findTier(r.o, curLines, ctx.strict, cursor, ch.eof);
        if (tier < 0) throw new Fail('no-match', s.path);
        const at = occurrences(r.o, curLines, tier, cursor, ch.eof)[0]!;
        const repl = replacement(curLines, at, r, tier);
        curLines = [...curLines.slice(0, at), ...repl, ...curLines.slice(at + r.o.length)];
        cursor = at + r.n.length;
      } else {
        const at = ch.eof ? curLines.length : Math.min(cursor, curLines.length);
        curLines = [...curLines.slice(0, at), ...r.n, ...curLines.slice(at)];
        cursor = at + r.n.length;
      }
    }
    const out = joinFile({ lines: curLines, br: st.br, final: st.final });
    if (s.moveTo !== null) {
      tree.now.set(s.path, null);
      tree.now.set(s.moveTo, out);
      ctx.moves.push({ old: s.path, nw: s.moveTo });
    } else {
      tree.now.set(s.path, out);
    }
  });
}

function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };
  const ctx: Ctx = { strict, moves: [] };
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'unified') edits = unifiedEdits(lines, ctx);
    else if (kind === 'search-replace') edits = searchReplaceEdits(lines, ctx);
    else edits = v4aEdits(lines, ctx);
    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }
  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };
  // The changed paths, in byte order of the path: a successful move is one `R` line (SPEC section 2), sorted by
  // its new path, and it replaces that pair's `D` and `A` lines.
  const changed: Array<{ key: string; line: string }> = [];
  const rOld = new Set<string>();
  const rNew = new Set<string>();
  for (const mv of ctx.moves) {
    if (tree.original(mv.old) !== null && tree.get(mv.old) === null && tree.original(mv.nw) === null && tree.get(mv.nw) !== null) {
      changed.push({ key: mv.nw, line: `R ${mv.old} -> ${mv.nw}` });
      rOld.add(mv.old);
      rNew.add(mv.nw);
    }
  }
  for (const p of [...tree.now.keys()].sort((a, b) => Buffer.compare(Buffer.from(a), Buffer.from(b)))) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;
    if (now === null && rOld.has(p)) continue;
    if (was === null && rNew.has(p)) continue;
    changed.push({ key: p, line: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
  }
  changed.sort((a, b) => Buffer.compare(Buffer.from(a.key), Buffer.from(b.key)));
  const rows = changed.map((c) => c.line);
  if (!check) {
    for (const p of [...tree.now.keys()]) {
      const now = tree.now.get(p)!;
      if (now === null) rmSync(p, { force: true });
      else {
        mkdirSync(dirname(p), { recursive: true });
        writeFileSync(p, now);
      }
    }
  }
  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}


const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  // A trial: the kit's runner reads the checks from the env and runs this file on each one, without this variable.
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}
