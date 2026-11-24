import { join } from 'node:path';
import { pathToFileURL } from 'node:url';
import fc from 'fast-check';

fc.configureGlobal({ numRuns: 1000 });

export async function load(file: string): Promise<Record<string, any>> {
  const work = process.env.BENCH_WORK;
  if (work === undefined) {
    throw new Error('BENCH_WORK names the workspace to test');
  }
  return import(pathToFileURL(join(work, file)).href);
}
