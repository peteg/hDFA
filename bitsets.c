/*
 * Cheap and cheerful bitsets.
 *
 * (C) 2010 Peter Gammie, peteg42 at gmail dot com
 * Begun April 2010.
 */

#include <assert.h>
#include <stdlib.h>
#include <stdint.h>

#include "bitsets.h"

struct BitSet {
  unsigned int size;
  uint8_t *bits;
};

#define BIT_BYTE(x) ((x) / 8)
#define BIT_BIT(x)  ((x) % 8)

struct BitSet *
BitSet_init(unsigned int size)
{
  struct BitSet *bs;

  bs = (struct BitSet *)malloc(sizeof(struct BitSet));
  bs->size = size;
  bs->bits = (uint8_t *)calloc((size + 7) / 8, sizeof(uint8_t));

  return bs;
}

void
BitSet_free(struct BitSet *bs)
{
  free(bs->bits);
  free(bs);
}

void
BitSet_realloc(struct BitSet *bs, unsigned int newSize)
{
  unsigned int i = bs->size;

  bs->size = newSize;
  bs->bits = (uint8_t *)realloc(bs->bits, (newSize + 7 / 8));

  /* Clear the new bits. */
  while(i < newSize) {
    BitSet_clear(bs, i);
    i++;
  }
}

unsigned int
BitSet_size(const struct BitSet *bs)
{
  return bs->size;
}

void
BitSet_set(struct BitSet *bs, unsigned int bitPos)
{
  assert(bitPos < bs->size);

  bs->bits[BIT_BYTE(bitPos)] |= (1 << BIT_BIT(bitPos));
}

void
BitSet_clear(struct BitSet *bs, unsigned int bitPos)
{
  assert(bitPos < bs->size);

  bs->bits[BIT_BYTE(bitPos)] &= ~(1 << BIT_BIT(bitPos));
}

bool
BitSet_isSet(const struct BitSet *bs, unsigned int bitPos)
{
  assert(bitPos < bs->size);

  return !! (bs->bits[BIT_BYTE(bitPos)] & (1 << BIT_BIT(bitPos)));
}
