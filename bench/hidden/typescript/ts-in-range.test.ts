import { test } from 'node:test';
import fc from 'fast-check';
import { load } from './load.ts';

const { inRange } = await load('inRange.ts');
const small = fc.integer({ min: -20, max: 20 });
const finite = fc.double({ noNaN: true, noDefaultInfinity: true });

for (const [name, number] of [['integers', small], ['doubles', finite]] as const) {
  test(name, () => {
    fc.assert(
      fc.property(number, number, number, (value, x, y) => {
        fc.pre(x !== y);
        const [minimum, maximum] = x < y ? [x, y] : [y, x];
        return inRange(value, minimum, maximum) === (minimum <= value && value < maximum);
      })
    );
  });
}

test('bounds', () => {
  fc.assert(
    fc.property(small, small, (x, y) => {
      fc.pre(x !== y);
      const [minimum, maximum] = x < y ? [x, y] : [y, x];
      return inRange(minimum, minimum, maximum) && !inRange(maximum, minimum, maximum);
    })
  );
});
