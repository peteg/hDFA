/*
 * Cheap and cheerful bitsets.
 *
 * (C) 2010 Peter Gammie, peteg42 at gmail dot com
 * Begun April 2010.
 */

#ifndef _BITSET_H_
#define _BITSET_H_

#include <stdbool.h>

struct BitSet;

struct BitSet *BitSet_init(unsigned int size);
void BitSet_free(struct BitSet *bs);

void BitSet_realloc(struct BitSet *bs, unsigned int newSize);

unsigned int BitSet_size(const struct BitSet *bs);

void BitSet_set(struct BitSet *bs, unsigned int bitPos);
void BitSet_clear(struct BitSet *bs, unsigned int bitPos);
bool BitSet_isSet(const struct BitSet *bs, unsigned int bitPos);

#endif /* _BITSET_H_ */
