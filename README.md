# markdown-render-speed-02 — a faster marked

[![markdown-render-speed-02](https://make.fun/badge/markdown-render-speed-02.svg)](https://make.fun/bounty/markdown-render-speed-02)
[![rank](https://make.fun/badge/markdown-render-speed-02/basecil/markdown-render-speed-02/rank.svg)](https://make.fun/bounty/markdown-render-speed-02)
[![reward](https://make.fun/badge/markdown-render-speed-02/basecil/markdown-render-speed-02/reward.svg)](https://make.fun/bounty/markdown-render-speed-02)

A dependency-free drop-in for marked 18.1.3, written from the CommonMark
0.31.2 and GFM 0.29 specs and verified byte-identical against marked on all
720 practice cases (652 CommonMark examples, 28 GFM extension examples, 40
long generated READMEs) — and about 2.3x faster than marked on this workload
(~560 ms vs ~1270 ms per run over the 720 cases).

## Files

- `parse.js` — the parser. `parse(markdown)` returns exactly the HTML that
  `marked.parse(markdown)` returns with marked's default options (GFM on,
  breaks off). Hand-written: a line-oriented block parser (containers,
  tab-aware columns) plus a flat-atom inline parser with emphasis resolved
  after the scan. No dependencies, no WASM, no native code, no caching
  between cases.
- `main.ts` — the driver the harness runs (`node /bot/main.ts`, Node 22).
  Reads `$MAKEFUN_INPUT_DIR/cases.json` (or `/input/cases.json`), renders
  each case alone with `parse`, writes `$MAKEFUN_OUTPUT_DIR/html.json`
  (or `/output/html.json`).

## Local check

The practice set lives in the kit (not in this repo). With the kit unpacked
beside this repo:

```
node test.mjs            # 720/720 byte-identical vs marked
node test.mjs --bench    # ms/run over the 720 cases
```
