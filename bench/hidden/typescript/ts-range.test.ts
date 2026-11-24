import { test } from 'node:test';
import fc from 'fast-check';
import { load } from './load.ts';

const { range } = await load('range.ts');
const bound = fc.integer({ min: -60, max: 60 });
const step = fc.integer({ min: -7, max: 7 }).filter(step => step !== 0);

test('property', () => {
  fc.assert(
    fc.property(bound, bound, step, (start, end, step) => {
      const expected: number[] = [];
      for (let value = start; step > 0 ? value < end : value > end; value += step) {
        expected.push(value);
      }
      return JSON.stringify(range(start, end, step)) === JSON.stringify(expected);
    })
  );
});
