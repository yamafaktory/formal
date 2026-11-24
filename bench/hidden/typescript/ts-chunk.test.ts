import { test } from 'node:test';
import fc from 'fast-check';
import { load } from './load.ts';

const { chunk } = await load('chunk.ts');

test('property', () => {
  fc.assert(
    fc.property(fc.array(fc.integer()), fc.integer({ min: 1, max: 12 }), (arr, size) => {
      const chunks: number[][] = chunk(arr, size);
      if (JSON.stringify(chunks.flat()) !== JSON.stringify(arr)) return false;
      return chunks.every((part, index) =>
        index < chunks.length - 1 ? part.length === size : part.length >= 1 && part.length <= size
      );
    })
  );
});
