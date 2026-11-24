import { test } from 'node:test';
import fc from 'fast-check';
import { load } from './load.ts';

const { zip } = await load('zip.ts');

test('property', () => {
  fc.assert(
    fc.property(fc.array(fc.integer()), fc.array(fc.string()), (a, b) => {
      const rows: unknown[][] = zip(a, b);
      if (rows.length !== Math.max(a.length, b.length)) return false;
      return rows.every((row, i) => row.length === 2 && row[0] === a[i] && row[1] === b[i]);
    })
  );
});
