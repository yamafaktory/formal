import { test } from 'node:test';
import fc from 'fast-check';
import { load } from './load.ts';

const { clamp } = await load('clamp.ts');
const finite = fc.double({ noNaN: true, noDefaultInfinity: true });

test('property', () => {
  fc.assert(
    fc.property(finite, finite, finite, (value, x, y) => {
      const [minimum, maximum] = x <= y ? [x, y] : [y, x];
      const expected = value < minimum ? minimum : value > maximum ? maximum : value;
      return clamp(value, minimum, maximum) === expected;
    })
  );
});
