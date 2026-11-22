// A tiny stack VM for make.fun's tiny stack ISA in one small file. It mirrors
// the reference semantics exactly: the per-step check order, wrapping 32-bit
// arithmetic, and the step and output limits.
import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
const IN = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";
// Runs one program to its end; returns [output bytes, exit code]. A trap ends
// the run at once with the trap's code, keeping the output already written.
function exec(P, Q) {
 const n = P.length;
 const S = new Int32Array(256); // data stack
 const C = new Int32Array(64); // return addresses
 const M = new Int32Array(256); // memory words, zeroed
 const out = []; // output bytes; its length is the output meter
 let sp = 0, cp = 0, pc = 0, steps = 0, ip = 0;
 for (;;) {
  if (steps === 1000000) return [out, 10];
  if (pc < 0 || pc >= n) return [out, 9];
  const o = P[pc];
  if (!((o < 8) || (o >= 16 && o <= 30) || (o >= 32 && o <= 34) ||
   (o >= 48 && o <= 52) || (o >= 64 && o <= 65) || (o >= 80 && o <= 83)))
   return [out, 5]; // a byte the ISA does not name
  const imm = o === 1 ? 1 : o === 2 ? 4 : o >= 48 && o <= 51 ? 2 : 0;
  if (pc + imm >= n) return [out, 9]; // the immediate is cut off by the end
  steps++;
  // Stack needs first: too few values traps 2, over 256 traps 3.
  let pops = 0, pushes = 0;
  if (o < 8) {
   pops = "00011223".charCodeAt(o) - 48;
   pushes = "01102333".charCodeAt(o) - 48;
  } else if (o <= 34) {
   pops = o === 23 || o === 27 ? 1 : 2; // NEG and NOT take one, the rest two
   pushes = 1;
  } else if (o === 49 || o === 50 || o === 80 || o === 81 || o === 83) pops = 1;
  else if (o === 64) { pops = 1; pushes = 1; }
  else if (o === 65) pops = 2;
  else if (o === 82) pushes = 1;
  if (sp < pops) return [out, 2];
  if (sp - pops + pushes > 256) return [out, 3];
  const next = pc + 1 + imm;
  pc = next;
  const off = imm === 2 ? ((P[next - 2] | (P[next - 1] << 8)) << 16) >> 16 : 0;
  switch (o) {
   case 0: return [out, 0]; // HALT
   case 1: S[sp++] = (P[next - 1] << 24) >> 24; break; // PUSH8, sign-extended
   case 2: // PUSH32, little-endian
    S[sp++] = P[next - 4] | (P[next - 3] << 8) | (P[next - 2] << 16) | (P[next - 1] << 24); break;
   case 3: sp--; break; // POP
   case 4: S[sp] = S[sp - 1]; sp++; break; // DUP
   case 5: { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; break; } // SWAP
   case 6: S[sp] = S[sp - 2]; sp++; break; // OVER
   case 7: { // ROT: ( a b c -- b c a )
    const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; break; }
   case 23: S[sp - 1] = -S[sp - 1]; break; // NEG; the store wraps -(-2^31)
   case 27: S[sp - 1] = ~S[sp - 1]; break; // NOT
   case 16: case 17: case 18: case 19: case 20: case 21: case 22:
   case 24: case 25: case 26: case 28: case 29: case 30:
   case 32: case 33: case 34: { // two-operand arithmetic and compares
    const b = S[sp - 1], a = S[sp - 2];
    let r;
    if (o === 16) r = a + b;
    else if (o === 17) r = a - b;
    else if (o === 18) r = Math.imul(a, b); // MUL, exact low 32 bits
    else if (o === 19) { if (b === 0) return [out, 4]; r = (a / b) | 0; } // DIV, toward zero
    else if (o === 20) { if (b === 0) return [out, 4]; r = a % b; } // MOD, sign of a
    else if (o === 21) { if (b === 0) return [out, 4]; r = Math.floor((a >>> 0) / (b >>> 0)); } // DIVU
    else if (o === 22) { if (b === 0) return [out, 4]; r = (a >>> 0) % (b >>> 0); } // MODU
    else if (o === 24) r = a & b;
    else if (o === 25) r = a | b;
    else if (o === 26) r = a ^ b;
    else if (o === 28) r = a << b; // SHL; JS masks the count to 5 bits itself
    else if (o === 29) r = a >> b; // SHR, arithmetic
    else if (o === 30) r = a >>> b; // SHRU, logical; the store wraps to signed
    else if (o === 32) r = a === b ? 1 : 0;
    else if (o === 33) r = a < b ? 1 : 0;
    else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU, unsigned
    S[sp - 2] = r; sp--; break;
   }
   case 48: pc = next + off; break; // JMP
   case 49: if (S[--sp] === 0) pc = next + off; break; // JZ
   case 50: if (S[--sp] !== 0) pc = next + off; break; // JNZ
   case 51: // CALL, to the unsigned absolute address
    if (cp === 64) return [out, 7];
    C[cp++] = next; pc = off & 65535; break;
   case 52: // RET
    if (cp === 0) return [out, 8];
    pc = C[--cp]; break;
   case 64: { // LOAD
    const a = S[sp - 1];
    if (a < 0 || a > 255) return [out, 6];
    S[sp - 1] = M[a]; break;
   }
   case 65: { // STORE: ( v addr -- )
    const a = S[sp - 1];
    if (a < 0 || a > 255) return [out, 6];
    M[a] = S[sp - 2]; sp -= 2; break;
   }
   case 80: { // PRINT; one that would cross the output limit writes nothing
    const s = String(S[sp - 1]);
    if (out.length + s.length > 65536) return [out, 11];
    sp--;
    for (let i = 0; i < s.length; i++) out.push(s.charCodeAt(i));
    break;
   }
   case 81: // PUTC
    if (out.length === 65536) return [out, 11];
    out.push(S[--sp] & 255); break;
   case 82: S[sp++] = ip < Q.length ? Q[ip++] : -1; break; // IN; -1 past the end
   case 83: return [out, S[sp - 1] & 255]; // EXIT, the low byte of the value
  }
 }
}
for (const id of readdirSync(IN).sort()) {
 let prog;
 try {
  prog = readFileSync(join(IN, id, "program.bin"));
 } catch {
  continue;
 }
 let inp = Buffer.alloc(0);
 try {
  inp = readFileSync(join(IN, id, "input.bin"));
 } catch {}
 const [bytes, code] = exec(prog, inp);
 mkdirSync(join(OUT, id), { recursive: true });
 writeFileSync(join(OUT, id, "stdout.bin"), Buffer.from(bytes));
 writeFileSync(join(OUT, id, "exit.txt"), String(code) + "\n");
}
