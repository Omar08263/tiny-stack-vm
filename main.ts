// Tiny stack VM: one program answering every instance of a set.
// Implements the ISA in program/generator/subject/ISA.md exactly:
// 32-bit wrapping arithmetic, signed/unsigned division, shifts masked
// to 5 bits, PUSH8 sign extension, EXIT low byte, all ten traps with
// their codes, step and output limits, IN returning -1 at end of input.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

function run(p, q) {
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256);
  const o = new Uint8Array(65536);
  let s = 0, c = 0, n = p.length, ol = 0, ip = 0, pc = 0, st = 0;
  const T = (e) => [o.slice(0, ol), e];
  for (;;) {
    if (st === 1e6) return T(10);
    if (pc < 0 || pc >= n) return T(9);
    const op = p[pc];
    const B = (op >= 0x10 && op <= 0x1e) || op === 0x20 || op === 0x21 || op === 0x22;
    if (!(op < 8 || B || (op >= 0x30 && op <= 0x34) ||
      op === 0x40 || op === 0x41 || (op >= 0x50 && op <= 0x53))) return T(5);
    const im = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    if (pc + im >= n) return T(9);
    st++;
    const nx = pc + 1 + im;
    const po = op === 7 ? 3 : op === 5 || op === 6 || op === 0x41 ||
      (B && op !== 0x17 && op !== 0x1b) ? 2 :
      op === 3 || op === 4 || op === 0x17 || op === 0x1b || op === 0x31 ||
      op === 0x32 || op === 0x40 || op === 0x50 || op === 0x51 || op === 0x53 ? 1 : 0;
    const pu = op === 1 || op === 2 || op === 0x52 || op === 0x40 ||
      B ? 1 : op === 4 ? 2 : op === 6 || op === 7 ? 3 : 0;
    if (s < po) return T(2);
    if (s - po + pu > 256) return T(3);
    pc = nx;
    if (op === 0) return T(0);
    if (op === 1) { D[s++] = (p[nx - 1] << 24) >> 24; continue; }
    if (op === 2) { D[s++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); continue; }
    if (op === 3) { s--; continue; }
    if (op === 4) { D[s] = D[s - 1]; s++; continue; }
    if (op === 5) { const t = D[s - 1]; D[s - 1] = D[s - 2]; D[s - 2] = t; continue; }
    if (op === 6) { D[s] = D[s - 2]; s++; continue; }
    if (op === 7) { const a = D[s - 3]; D[s - 3] = D[s - 2]; D[s - 2] = D[s - 1]; D[s - 1] = a; continue; }
    if (op === 0x17) { D[s - 1] = -D[s - 1] | 0; continue; }
    if (op === 0x1b) { D[s - 1] = ~D[s - 1]; continue; }
    if (B) {
      const b = D[s - 1], a = D[s - 2];
      let r;
      if (op === 0x10) r = (a + b) | 0;
      else if (op === 0x11) r = (a - b) | 0;
      else if (op === 0x12) r = Math.imul(a, b);
      else if (op === 0x13) { if (!b) return T(4); r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
      else if (op === 0x14) { if (!b) return T(4); r = b === -1 ? 0 : (a % b) | 0; }
      else if (op === 0x15) { if (!b) return T(4); r = Math.floor((a >>> 0) / (b >>> 0)) | 0; }
      else if (op === 0x16) { if (!b) return T(4); r = ((a >>> 0) % (b >>> 0)) | 0; }
      else if (op === 0x18) r = a & b;
      else if (op === 0x19) r = a | b;
      else if (op === 0x1a) r = a ^ b;
      else if (op === 0x1c) r = a << (b & 31);
      else if (op === 0x1d) r = a >> (b & 31);
      else if (op === 0x1e) r = (a >>> (b & 31)) | 0;
      else if (op === 0x20) r = a === b ? 1 : 0;
      else if (op === 0x21) r = a < b ? 1 : 0;
      else r = (a >>> 0) < (b >>> 0) ? 1 : 0;
      s -= 2; D[s++] = r; continue;
    }
    if (op >= 0x30 && op <= 0x32) {
      const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
      if (op === 0x30 || (op === 0x31) === (D[--s] === 0)) pc = nx + rel;
      continue;
    }
    if (op === 0x33) {
      if (c === 64) return T(7);
      C[c++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8); continue;
    }
    if (op === 0x34) {
      if (!c) return T(8);
      pc = C[--c]; continue;
    }
    if (op === 0x40) {
      const a = D[s - 1];
      if (a < 0 || a > 255) return T(6);
      D[s - 1] = M[a]; continue;
    }
    if (op === 0x41) {
      const a = D[s - 1];
      if (a < 0 || a > 255) return T(6);
      s -= 2; M[a] = D[s]; continue;
    }
    if (op === 0x50) {
      const t = String(D[s - 1]);
      if (ol + t.length > 65536) return T(11);
      s--;
      for (let i = 0; i < t.length; i++) o[ol++] = t.charCodeAt(i);
      continue;
    }
    if (op === 0x51) {
      if (ol + 1 > 65536) return T(11);
      o[ol++] = D[--s] & 255; continue;
    }
    if (op === 0x52) { D[s++] = ip < q.length ? q[ip++] : -1; continue; }
    return T(D[--s] & 255);
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const O = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";
for (const id of readdirSync(I).sort()) {
  const r = run(readFileSync(join(I, id, "program.bin")), readFileSync(join(I, id, "input.bin")));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, "stdout.bin"), r[0]);
  writeFileSync(join(O, id, "exit.txt"), r[1] + "\n");
}
