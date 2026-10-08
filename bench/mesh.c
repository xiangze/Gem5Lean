// 同じ wave プログラムを、uint32_t 配列で持つ 4x4 同期メッシュ (レジスタ方式) で実行する参照実装
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#define R 4
#define C 4
typedef struct { uint32_t pc, x[32], out[4], mir[4], dmem[1024]; int halted; } Core;  // dir: 0N 1S 2E 3W
static uint32_t imem[16];
static int32_t sx(uint32_t v, int b){ return (int32_t)(v << (32-b)) >> (32-b); }
static void step(Core *c) {
  if (c->halted) return;
  uint32_t in = imem[(c->pc >> 2) & 15], op = in & 0x7f, rd = (in>>7)&31, f3 = (in>>12)&7,
           rs1 = (in>>15)&31, rs2 = (in>>20)&31, f7 = in>>25;
  uint32_t a = c->x[rs1], b = c->x[rs2], npc = c->pc + 4, wb = 0; int w = 0;
  switch (op) {
    case 0x0B: if (f7 & 1) c->out[f3&3] = a; else { wb = c->mir[f3&3]; w = 1; } break;
    case 0x13: wb = a + sx(in>>20,12); w = 1; break;                       // addi
    case 0x33: wb = (f7==0x20) ? a - b : a + b; w = 1; break;              // add/sub
    case 0x63: { int32_t im = sx(((in>>31)<<12)|(((in>>7)&1)<<11)|(((in>>25)&63)<<5)|(((in>>8)&15)<<1),13);
                 if ((f3==1) ? a!=b : a==b) npc = c->pc + im; } break;      // beq/bne
    case 0x23: c->dmem[((a + sx(((in>>25)<<5)|((in>>7)&31),12))>>2)&1023] = b; break;
    default: c->halted = 1; return;
  }
  if (w && rd) c->x[rd] = wb;
  c->pc = npc;
}
int main(int argc, char **argv) {
  long iters = argc > 1 ? atol(argv[1]) : 1000;
  FILE *f = fopen("bench/wave.hex", "r"); for (int i = 0; i < 10; i++) fscanf(f, "%x", &imem[i]); fclose(f);
  static Core g[R][C]; memset(g, 0, sizeof g);
  for (int r = 0; r < R; r++) for (int c = 0; c < C; c++) { g[r][c].x[10] = (r==0&&c==0); g[r][c].x[11] = iters; }
  struct timespec t0, t1; clock_gettime(CLOCK_MONOTONIC, &t0);
  long cycles = 0, instrs = 0; int live = 1;
  while (live) {
    // ミラー = 前サイクル末の隣接出力 (端は 0)
    for (int r = 0; r < R; r++) for (int c = 0; c < C; c++) {
      Core *k = &g[r][c];
      k->mir[0] = r > 0     ? g[r-1][c].out[1] : 0;
      k->mir[1] = r < R-1   ? g[r+1][c].out[0] : 0;
      k->mir[2] = c < C-1   ? g[r][c+1].out[3] : 0;
      k->mir[3] = c > 0     ? g[r][c-1].out[2] : 0;
    }
    live = 0;
    for (int r = 0; r < R; r++) for (int c = 0; c < C; c++) { if (!g[r][c].halted) { step(&g[r][c]); instrs++; live = 1; } }
    cycles++;
  }
  clock_gettime(CLOCK_MONOTONIC, &t1);
  double ms = (t1.tv_sec - t0.tv_sec) * 1e3 + (t1.tv_nsec - t0.tv_nsec) / 1e6;
  printf("[C] iters=%ld cycles=%ld instrs=%ld time_ms=%.1f Minstr_per_s=%.1f dmem(3,3)=%u\n",
         iters, cycles, instrs, ms, instrs / ms / 1e3, g[3][3].dmem[0x100>>2]);
  return 0;
}
