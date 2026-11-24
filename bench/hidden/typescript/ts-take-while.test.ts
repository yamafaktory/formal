import { test } from 'node:test';
import fc from 'fast-check';
import { load } from './load.ts';

const { takeWhile } = await load('takeWhile.ts');

test('property', () => {
  fc.assert(
    fc.property(fc.array(fc.integer({ min: -10, max: 10 })), fc.integer({ min: -10, max: 10 }), (arr, limit) => {
      const p = (x: number) => x < limit;
      let end = 0;
      while (end < arr.length && p(arr[end])) end++;
      return JSON.stringify(takeWhile(arr, p)) === JSON.stringify(arr.slice(0, end));
    })
  );
});
