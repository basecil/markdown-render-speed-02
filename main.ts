// Driver for the markdown-render-speed-02 entry.
//
// The harness runs `node /bot/main.ts` on Node 22. It reads every case from
// $MAKEFUN_INPUT_DIR/cases.json (falling back to /input/cases.json): a JSON
// array of {id, markdown}. Each case is rendered alone with parse() from
// ./parse.js, and the HTML strings are written, in the cases' order, to
// $MAKEFUN_OUTPUT_DIR/html.json (falling back to /output/html.json).
// Nothing is cached from one case to the next; parse() is a pure function
// of the markdown string it is given.

import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { join } from 'node:path';
import { parse } from './parse.js';

const inputDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outputDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

const cases = JSON.parse(readFileSync(join(inputDir, 'cases.json'), 'utf8')) as { id: string; markdown: string }[];
const html = new Array<string>(cases.length);
for (let i = 0; i < cases.length; i++) html[i] = parse(cases[i].markdown);
mkdirSync(outputDir, { recursive: true });
writeFileSync(join(outputDir, 'html.json'), JSON.stringify(html));
