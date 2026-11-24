import { test } from 'node:test';
import fc from 'fast-check';
import { load } from './load.ts';

const { windowed } = await load('windowed.ts');

test('property', () => {
  fc.assert(
    fc.property(
      fc.array(fc.integer(), { maxLength: 20 }),
      fc.integer({ min: 1, max: 8 }),
      fc.integer({ min: 1, max: 8 }),
      (arr, size, step) => {
        const expected: number[][] = [];
        for (let i = 0; i + size <= arr.length; i += step) {
          expected.push(arr.slice(i, i + size));
        }
        return JSON.stringify(windowed(arr, size, step)) === JSON.stringify(expected);
      }
    )
  );
});
