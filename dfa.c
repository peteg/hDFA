/*
 * Representation of DFAs and algorithms on them.
 *
 * Ported to C by Peter Gammie, peteg42 at gmail dot com
 * This port (C) 2010 Peter Gammie.
 *
 * Original code (JFlex.DFA from http://www.jflex.de/):
 *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 * JFlex 1.4.3                                                             *
 * Copyright (C) 1998-2009  Gerwin Klein <lsf@jflex.de>                    *
 * All rights reserved.                                                    *
 *                                                                         *
 * This program is free software; you can redistribute it and/or modify    *
 * it under the terms of the GNU General Public License. See the file      *
 * COPYRIGHT for more information.                                         *
 *                                                                         *
 * This program is distributed in the hope that it will be useful,         *
 * but WITHOUT ANY WARRANTY; without even the implied warranty of          *
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the           *
 * GNU General Public License for more details.                            *
 *                                                                         *
 * You should have received a copy of the GNU General Public License along *
 * with this program; if not, write to the Free Software Foundation, Inc., *
 * 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA                 *
 *                                                                         *
 * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *
 *

Explicit-state representation: use an adjacency matrix. Assume that
the input alphabet has been made dense enough by other means. This is
a perfect hashing problem, but as we've got pointers we could also try
to sort the alphabet.

We have no use for actions, just a distinction between two types of
states. (The initial partition is based on a single bit.)

 */

#include <assert.h>

#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

#include <string.h>

#include "bitsets.h"
#include "dfa.h"

/* **************************************** */

/* The default number of states. */
#define DEFAULT_NUM_STATES 10

/* The default number of input symbols. */
#define DEFAULT_ALPHABET_SIZE 5

/* End-of-list sentinel. */
#define END_OF_LIST (-1)

#define FIXME_MISC_SENTINEL (-1)

/* **************************************** */

struct DFA {
  /* Debugging output. */
  bool debug;

  /* Initial transitions: can be labelled. */
  int *initial;

  /* The transition table (adjacency matrix). We use NO_TARGET as a sentinel. */
  int *table;

  /* How many states are actually present? */
  unsigned int numStates;

  /* How many input symbols? */
  unsigned int numSymbols;

  /* Mark each state as satisfying or not satisfying the bit. */
  struct BitSet *satBit;
};

/* Grease the 2D-array wheels. */

#define ARRAY_2D_PRIM(array, width, x, y) (*((array) + (x) * (width) + (y)))
#define TRANS(dfa, s, x) (ARRAY_2D_PRIM(dfa->table, dfa->numSymbols, s, x))

#define MAX(a, b) ((a) > (b) ? (a) : (b))

void
DFA_dumpState(struct DFA *dfa)
{
  printf("Initially:\n");
  for(unsigned int x = 0; x < dfa->numSymbols; x++) {
    if(dfa->initial[x] >= 0) {
      printf(" -%d-> %d\n", x, dfa->initial[x]);
    }
  }

  for(unsigned int s = 0; s < dfa->numStates; s++) {
    printf("State %d", s);
    if(BitSet_isSet(dfa->satBit, s)) {
      printf("[S]");
    }
    printf("\n");

    for(unsigned int x = 0; x < dfa->numSymbols; x++) {
      int t = TRANS(dfa, s, x);

      if(t >= 0) {
        printf("  -%d-> %d\n", x, t);
      }
    }
  }
}

struct DFA *
DFA_init(bool debug)
{
  struct DFA *dfa = (struct DFA *)malloc(sizeof(struct DFA));
  unsigned int numStates = DEFAULT_NUM_STATES;
  unsigned int numSymbols = DEFAULT_ALPHABET_SIZE;

  dfa->debug = debug;
  dfa->initial = (int *)malloc(numSymbols * sizeof(int));
  dfa->table = (int *)malloc(numStates * numSymbols * sizeof(int));
  dfa->numStates = 0;
  dfa->numSymbols = numSymbols;
  dfa->satBit = BitSet_init(numStates);

  for(unsigned int x = 0; x < numSymbols; x++) {
    dfa->initial[x] = NO_TARGET;
  }

  for(unsigned int s = 0; s < numStates; s++) {
    for(unsigned int x = 0; x < numSymbols; x++) {
      TRANS(dfa, s, x) = NO_TARGET;
    }
  }

  return dfa;
}

void
DFA_free(struct DFA *dfa)
{
  free(dfa->initial);
  free(dfa->table);
  BitSet_free(dfa->satBit);
  free(dfa);
}

static void
DFA_ensureCapacity(struct DFA *dfa, state_t newMaxNumStates, unsigned int newMaxNumSymbols) {
  unsigned int maxNumStates = BitSet_size(dfa->satBit);
  unsigned int numSymbols = dfa->numSymbols;

  if(newMaxNumStates < maxNumStates
     && newMaxNumSymbols < numSymbols) {
    return;
  }

  unsigned int oldMaxNumStates = maxNumStates;
  while(maxNumStates <= newMaxNumStates) {
    maxNumStates *= 2;
  }

  unsigned int oldMaxNumSymbols = numSymbols;
  while(numSymbols <= newMaxNumSymbols) {
    numSymbols *= 2;
  }

  if(dfa->debug) {
      printf("ensureCapacity, resizing from %d -> %d states (%d req), %d -> %d syms (%d req)\nOld table:\n",
             oldMaxNumStates, maxNumStates, newMaxNumStates,
             oldMaxNumSymbols, numSymbols, newMaxNumSymbols);
      DFA_dumpState(dfa);
    }

  dfa->initial = (int *)realloc(dfa->initial, numSymbols * sizeof(int));
  dfa->table = (int *)realloc(dfa->table, numSymbols * maxNumStates * sizeof(int));
  dfa->numSymbols = numSymbols;
  BitSet_realloc(dfa->satBit, maxNumStates);

  /* FIXME this is a bit tricky: shuffle things around in the table.
     Need to ensure we copy before we trash.
   */
  for(int x = oldMaxNumSymbols; x < numSymbols; x++) {
    dfa->initial[x] = NO_TARGET;
  }

  for(int s = maxNumStates - 1; s >= 0; s--) {
    for(int x = numSymbols - 1; x >= 0; x--) {
      ARRAY_2D_PRIM(dfa->table, numSymbols, s, x)
        = (s < dfa->numStates && x < oldMaxNumSymbols)
        ? ARRAY_2D_PRIM(dfa->table, oldMaxNumSymbols, s, x)
        : NO_TARGET;
    }
  }

  if(dfa->debug) {
    printf("ensureCapacity, after:\n");
    DFA_dumpState(dfa);
  }
}

void
DFA_addInitialTransition(struct DFA *dfa, label_t label, state_t end)
{
  DFA_ensureCapacity(dfa, end, label);
  /* FIXME where does this go? */
  dfa->numStates = MAX(dfa->numStates, end + 1);
  dfa->initial[label] = end;
}

void
DFA_addTransition(struct DFA *dfa, state_t start, label_t label, state_t end)
{
  DFA_ensureCapacity(dfa, MAX(start, end), label);
  /* FIXME where does this go? */
  dfa->numStates = MAX(dfa->numStates, MAX(start, end) + 1);
  TRANS(dfa, start, label) = end;
}

void
DFA_setSatBit(struct DFA *dfa, state_t state)
{
  DFA_ensureCapacity(dfa, state, 0);

  BitSet_set(dfa->satBit, state);
}

unsigned int
DFA_numStates(struct DFA *dfa)
{
  return dfa->numStates;
}

unsigned int
DFA_numSymbols(struct DFA *dfa)
{
  return dfa->numSymbols;
}

int
DFA_initialTransition(struct DFA *dfa, label_t label)
{
  return (label < dfa->numSymbols)
    ? dfa->initial[label]
    : NO_TARGET;
}

int
DFA_transition(struct DFA *dfa, state_t start, label_t label)
{
  return (start < dfa->numStates && label < dfa->numSymbols)
    ? TRANS(dfa, start, label)
    : NO_TARGET;
}

bool
DFA_satBit(struct DFA *dfa, state_t state)
{
  return (state < dfa->numStates)
    ? BitSet_isSet(dfa->satBit, state)
    : false;
}

/* **************************************** */
/* Render the automaton in DOT format. */

void
DFA_toDot(struct DFA *dfa, void (label_fn)(label_t, char[LABEL_LEN]), FILE *file)
{
  if(dfa->debug) {
    printf("DFA_toDot\n");
  }

  fprintf(file, "digraph DFA {\n");
  fprintf(file, "\trankdir = LR\n\tnode [shape=\"circle\"]\n");

  for(unsigned int i = 0; i < dfa->numStates; i++) {
    if(BitSet_isSet(dfa->satBit, i)) {
      fprintf(file, "\t%d [shape=\"doublecircle\"]\n", i);
    }
  }

  for(unsigned int x = 0; x < dfa->numSymbols; x++) {
    int end;

    /* Ignore all transitions to the error state. */
    if((end = dfa->initial[x]) >= 0) {
      fprintf(file, "\tinit%d[label=\"\" width=\"0.01\"];\n", x);

      char buffer[LABEL_LEN];
      label_fn(x, buffer);
      fprintf(file, "\tinit%d -> %d [label=\"%s\"]\n", x, end, buffer);
    }
  }

  for(unsigned int s = 0; s < dfa->numStates; s++) {
    for(unsigned int x = 0; x < dfa->numSymbols; x++) {
      int end;

      /* Ignore all transitions to the error state. */
      if((end = TRANS(dfa, s, x)) >= 0) {
        char buffer[LABEL_LEN];
        label_fn(x, buffer);
        fprintf(file, "\t%d -> %d [label=\"%s\"]\n", s, end, buffer);
      }
    }
  }

  fprintf(file, "}\n");
}

int
DFA_writeDotToFile(struct DFA *dfa, void (label_fn)(label_t, char[LABEL_LEN]), char *file)
{
  FILE *f;
  bool ret = -1;

  if((f = fopen(file, "w")) != NULL) {
    DFA_toDot(dfa, label_fn, f);
    fclose(f);

    ret = 0;
  }

  return ret;
}

/* **************************************** */

/*
 * Implementation of Hopcroft's O(n log n) minimization algorithm, follows
 * description by D. Gries.
 *
 * Time: O(n log n)
 * Space: O(c n), size < 4*(5*c*n + 13*n + 3*c) bytes
 *
 */

static void
DFA_printInvDelta(struct DFA *dfa, int *inv_delta, int *inv_delta_set)
{
  unsigned int numInput = dfa->numSymbols;

  printf("Inverse of transition table:\n");

  for(unsigned int s = 0; s < dfa->numStates + 1; s++) {
    printf("State [%d]\n", s - 1);

    for(unsigned int c = 0; c < numInput; c++) {
      if(inv_delta_set[ARRAY_2D_PRIM(inv_delta, numInput, s, c)] != NO_TARGET) {
        printf("With <%d> in {", c);
        int t = ARRAY_2D_PRIM(inv_delta, numInput, s, c);

        while(inv_delta_set[t] != END_OF_LIST) {
          printf("%d", inv_delta_set[t] - 1);
          t++;
          if(inv_delta_set[t] != END_OF_LIST) {
            printf(",");
          }
        }

        printf("}\n");
      }
    }
  }
}

static void
DFA_printBlocks(struct DFA *dfa, unsigned int *block, unsigned int *b_f, unsigned int *b_b, unsigned int last)
{
  unsigned int i;
  const unsigned int n = dfa->numStates + 1;

  printf(">> DFA_printBlocks\n");

  printf("block[0..n-1], s->b:  ");
  for(i = 0; i < n; i++) {
    unsigned int b = block[i];

    printf(" %2d", b > 0 ? b - n : (-1));
  }
  printf("\nblock[n..2n-1], bsize:");
  for(; i < 2 * n; i++) {
    printf(" %2d", block[i]);
  }
  printf("\n");

/*   Out.dump("b_forward : "+toString(b_f)); */
/*   Out.dump("b_backward: "+toString(b_b)); */
  printf("lastBlock: %d\n", last - n);

  for(int i = n; i <= last; i++) {
    printf("Block %d (size %d): {", i - n, block[i]);
    unsigned int s = b_f[i];

    while(s != i) {
      printf("%d", s - 1);
      int t = s;
      s = b_f[s];

      /* FIXME errors interleaved, oops. */
      if (s != i) {
        printf(",");
        if(block[s] != i) {
          printf("consistency error for state %d (block %d)", s - 1, block[s]);
        }
      }

      if (b_b[s] != t) {
        printf("consistency error for b_back in state %d (back = %d, should be = %d)", s - 1, b_b[s], t);
      }
    }
    printf("}\n");
  }
}

static void
DFA_printL(struct DFA *dfa, unsigned int *l_f, unsigned int *l_b, unsigned int anchor)
{
  unsigned int bc = l_f[anchor];

  printf("L = {");
  while (bc != anchor) {
    int b = bc / dfa->numSymbols;
    int c = bc % dfa->numSymbols;
    printf("(%d, %d)", b, c);
    int old_bc = bc;
    bc = l_f[bc];
    if(bc != anchor) {
      printf(", ");
    }
    // FIXME this is badly interleaved.
    if(l_b[bc] != old_bc) {
      printf("consistency error for (%d, %d)\n", b, c);
    }
  }
  printf("}\n");
}

void
DFA_minimize(struct DFA *dfa)
{
  if(dfa->debug) {
    printf("%d states before minimization\n", dfa->numStates);
  }

  if(dfa->numStates == 0) {
    if(dfa->debug) {
      printf("no states, already done!\n");
    }
    return;
  }

  // the algorithm needs the DFA to be total, so we add an error state 0,
  // and translate the rest of the states by +1
  const unsigned int n = dfa->numStates + 1;
  const unsigned int numInput = dfa->numSymbols;

  // block information:
  // [0..n-1] stores which block a state belongs to,
  // [n..2*n-1] stores how many elements each block has
  unsigned int *block = (unsigned int *)calloc(2 * n, sizeof(unsigned int));

  // implements a doubly linked list of states (these are the actual blocks)
  unsigned int *b_forward  = (unsigned int *)malloc(2 * n * sizeof(unsigned int));
  unsigned int *b_backward = (unsigned int *)malloc(2 * n * sizeof(unsigned int));

  // the last of the blocks currently in use (in [n..2*n-1])
  // (end of list marker, points to the last used block)
  unsigned int lastBlock = n;  // at first we start with one empty block
  const unsigned int b0 = n;   // the first block

  // the circular doubly linked list L of pairs (B_i, c)
  // (B_i, c) in L iff l_forward[(B_i-n)*numInput+c] > 0 // numeric value of block 0 = n!
  unsigned int *l_forward = (unsigned int *)malloc(n * (numInput + 1) * sizeof(unsigned int));
  unsigned int *l_backward = (unsigned int *)malloc(n * (numInput + 1) * sizeof(unsigned int));
  const unsigned int anchorL = n * numInput; // list anchor

  // inverse of the transition table
  // if t = inv_delta[s][c] then { inv_delta_set[t], inv_delta_set[t+1], .. inv_delta_set[k] }
  // is the set of states, with inv_delta_set[k] = -1 and inv_delta_set[j] >= 0 for t <= j < k
// FIXME note signed
  int *inv_delta = (int *)malloc(n * numInput * sizeof(int));/* new int[n][numInput]; */
  int *inv_delta_set = (int *)malloc(2 * n * numInput * sizeof(int));

  // twin stores two things:
  // twin[0]..twin[numSplit-1] is the list of blocks that have been split
  // twin[B_i] is the twin of block B_i
  unsigned int *twin = (unsigned int *)malloc(2 * n * sizeof(unsigned int));
  unsigned int numSplit;

  // SD[B_i] is the the number of states s in B_i with delta(s,a) in B_j
  // if SD[B_i] == block[B_i], there is no need to split
  int *SD = (int *)malloc(2 * n * sizeof(int)); // [only SD[n..2*n-1] is used]

  // for fixed (B_j,a), the D[0]..D[numD-1] are the inv_delta(B_j,a)
  unsigned int *D = (unsigned int *)malloc(n * sizeof(unsigned int));
  unsigned int numD;

  // initialize inverse of transition table
// FIXME note signed
  unsigned int lastDelta = 0;
  unsigned int *inv_lists = (unsigned int *)malloc(n * sizeof(unsigned int)); // holds a set of lists of states
  int *inv_list_last = (int *)malloc(n * sizeof(int)); // the last element

  for(unsigned int c = 0; c < numInput; c++) {
    // clear "head" and "last element" pointers
    for(unsigned int s = 0; s < n; s++) {
      inv_list_last[s] = END_OF_LIST;
      ARRAY_2D_PRIM(inv_delta, numInput, s, c) = NO_TARGET;
/*       inv_delta[s][c] = -1; */
    }

    // the error state has a transition for each character into itself
    ARRAY_2D_PRIM(inv_delta, numInput, 0, c) = 0;
/*     inv_delta[0][c] = 0; */
    inv_list_last[0] = 0;

    // accumulate states of inverse delta into lists (inv_delta serves as head of list)
    for(unsigned int s = 1; s < n; s++) {
      unsigned int t = TRANS(dfa, s - 1, c) + 1;

      if(inv_list_last[t] == END_OF_LIST) { // if there are no elements in the list yet
        ARRAY_2D_PRIM(inv_delta, numInput, t, c) = s;  // mark t as first and last element
/*         inv_delta[t][c] = s;  // mark t as first and last element */
        inv_list_last[t] = s;
      } else {
        inv_lists[inv_list_last[t]] = s; // link t into chain
        inv_list_last[t] = s; // and mark as last element
      }
    }

    // now move them to inv_delta_set in sequential order,
    // and update inv_delta accordingly
    for(int s = 0; s < n; s++) {
      int i = ARRAY_2D_PRIM(inv_delta, numInput, s, c);
/*         int i = inv_delta[s][c]; */
      ARRAY_2D_PRIM(inv_delta, numInput, s, c) = lastDelta;
/*         inv_delta[s][c] = lastDelta; */
      int j = inv_list_last[s];
      bool go_on = (i != -1);

      while(go_on) {
        go_on = (i != j);
        inv_delta_set[lastDelta++] = i;
        i = inv_lists[i];
      }
      inv_delta_set[lastDelta++] = -1;
    }
  } // of initialize inv_delta

  if(dfa->debug) {
    DFA_printInvDelta(dfa, inv_delta, inv_delta_set);
  }

  // initialize blocks

  if(dfa->debug) {
    printf("\n>>> initialising blocks\n");
  }

  // make b0 = {0}  where 0 = the additional error state
  b_forward[b0]  = 0;
  b_backward[b0] = 0;
  b_forward[0]   = b0;
  b_backward[0]  = b0;
  block[0]  = b0;
  block[b0] = 1;

  if(dfa->debug) {
    DFA_printBlocks(dfa, block, b_forward, b_backward, lastBlock);
  }

  for(int s = 1; s < n; s++) {
    if(dfa->debug) {
      printf(" Checking state [%d]\n", s - 1);
    }

    // search the blocks if it fits in somewhere
    // (fit in = same pushback behavior, same finalness, same lookahead behavior, same action)
    unsigned int b = b0 + 1; // no state can be equivalent to the error state
    bool found = false;

    while(!found && b <= lastBlock) {
      // get some state out of the current block
      int t = b_forward[b];

      if(dfa->debug) {
        printf("  picking state [%d]\n", t - 1);
      }

      // check if s could be equivalent with t
      found = (BitSet_isSet(dfa->satBit, s - 1))
        ? BitSet_isSet(dfa->satBit, t - 1)
        : ! (BitSet_isSet(dfa->satBit, t - 1));

      if(found) { // found -> add state s to block b
        if(dfa->debug) {
          printf("Found! Adding to block %d\n", b - b0);
        }

        // update block information
        block[s] = b;
        block[b]++;

        // chain in the new element
        int last = b_backward[b];
        b_forward[last] = s;
        b_forward[s] = b;
        b_backward[b] = s;
        b_backward[s] = last;
      }

      b++;
    }

    if(!found) { // fits in nowhere -> create new block
      if(dfa->debug) {
        printf("Not found, lastBlock = %d\n", lastBlock);
      }

      // update block information
      block[s] = b;
      block[b]++;

      // chain in the new element
      b_forward[b] = s;
      b_forward[s] = b;
      b_backward[b] = s;
      b_backward[s] = b;

      lastBlock++;
    }
  } // of initialize blocks

  if(dfa->debug) {
    DFA_printBlocks(dfa, block, b_forward, b_backward, lastBlock);
  }

  // initialize worklist L

  // first, find the largest block B_max, then, all other (B_i,c) go into the list
  unsigned int B_max = b0;
  unsigned int B_i;

  for(B_i = b0 + 1; B_i <= lastBlock; B_i++) {
    if(block[B_max] < block[B_i]) {
      B_max = B_i;
    }
  }

  // L = empty
  l_forward[anchorL] = anchorL;
  l_backward[anchorL] = anchorL;

  // set up the first list element
  B_i = (B_max == b0) ? b0 + 1 : b0; // there must be at least two blocks

  unsigned int index = (B_i - b0) * numInput;  // (B_i, 0)

  while(index < (B_i + 1 - b0) * numInput) {
    unsigned int last = l_backward[anchorL];
    l_forward[last]     = index;
    l_forward[index]    = anchorL;
    l_backward[index]   = last;
    l_backward[anchorL] = index;
    index++;
  }

  // now do the rest of L
  for(; B_i <= lastBlock; B_i++) {
    if(B_i != B_max) {
      index = (B_i - b0) * numInput;
      while (index < (B_i + 1 - b0) * numInput) {
        unsigned int last = l_backward[anchorL];
        l_forward[last]     = index;
        l_forward[index]    = anchorL;
        l_backward[index]   = last;
        l_backward[anchorL] = index;
        index++;
      }
    }
  }
  // end of setup L

  // start of "real" algorithm

  unsigned int step = 1;
  if(dfa->debug) {
    printf("\n>> start of real alg: max_steps = %d\n", n * numInput);
  }

  // while L not empty
  while(l_forward[anchorL] != anchorL) {
    if(dfa->debug) {
      printf("\nstep: %d\n", step++);
      DFA_printL(dfa, l_forward, l_backward, anchorL);
    }

    // pick and delete (B_j, a) in L:

    // pick
    int B_j_a = l_forward[anchorL];
    // delete
    l_forward[anchorL] = l_forward[B_j_a];
    l_backward[l_forward[anchorL]] = anchorL;
    l_forward[B_j_a] = 0;
    // take B_j_a = (B_j-b0)*numInput+c apart into (B_j, a)
    unsigned int B_j = b0 + B_j_a / numInput;
    unsigned int a   = B_j_a % numInput;

    if(dfa->debug) {
      DFA_printL(dfa, l_forward, l_backward, anchorL);
      printf("picked (%d, %d)\n", B_j - n, a);
      // DFA_printL(dfa, l_forward, l_backward, anchorL);
    }

    // determine splittings of all blocks wrt (B_j, a)
    // i.e. D = inv_delta(B_j,a)
    numD = 0;
    unsigned int s = b_forward[B_j];

    while(s != B_j) {
      if(dfa->debug) {
        printf("splitting wrt. state %d\n", s - 1);
      }

      int t = ARRAY_2D_PRIM(inv_delta, numInput, s, a);
/*         int t = inv_delta[s][a]; */
      if(dfa->debug) {
        printf("inv_delta chunk %d\n", t);
      }

      while(inv_delta_set[t] != NO_TARGET) {
        if(dfa->debug) {
          printf("D += state %d\n", inv_delta_set[t] - 1);
        }
        D[numD++] = inv_delta_set[t++];
      }
      s = b_forward[s];
    }

    // clear the twin list
    numSplit = 0;

    if(dfa->debug) {
      printf("splitting blocks according to D\n");
    }

    // clear SD and twins (only those B_i that occur in D)
    for(unsigned int indexD = 0; indexD < numD; indexD++) { // for each s in D
      s = D[indexD];
      B_i = block[s];
      SD[B_i] = FIXME_MISC_SENTINEL;
      twin[B_i] = 0;
    }

    // count how many states of each B_i occurring in D go with a into B_j
    // Actually we only check, if *all* t in B_i go with a into B_j.
    // In this case SD[B_i] == block[B_i] will hold.
    for(unsigned int indexD = 0; indexD < numD; indexD++) { // for each s in D
      s = D[indexD];
      B_i = block[s];

      // only count, if we haven't checked this block already
      if (SD[B_i] < 0) {
        SD[B_i] = 0;
        unsigned int t = b_forward[B_i];
        while(t != B_i
              && (t != 0 || block[0] == B_j)
              && (t == 0 || block[TRANS(dfa, t - 1, a) + 1] == B_j)) {
          SD[B_i]++;
          t = b_forward[t];
        }
      }
    }

    // split each block according to D
    for(unsigned int indexD = 0; indexD < numD; indexD++) { // for each s in D
      s = D[indexD];
      B_i = block[s];

      if(dfa->debug) {
        printf("checking if block %d must be split because of state %d\n", B_i - b0 , s - 1);
      }

      if(SD[B_i] != block[B_i]) {
        unsigned int B_k = twin[B_i];

        if(dfa->debug) {
          printf("state %d must be moved\n", s - 1);
        }

        if(B_k == 0) {
          // no twin for B_i yet -> generate new block B_k, make it B_i's twin
          B_k = ++lastBlock;

          if(dfa->debug) {
            printf("creating block %d\n", B_k - n);
            DFA_printBlocks(dfa, block, b_forward, b_backward, lastBlock - 1);
          }

          b_forward[B_k] = B_k;
          b_backward[B_k] = B_k;

          twin[B_i] = B_k;

          // mark B_i as split
          twin[numSplit++] = B_i;
        }
        // move s from B_i to B_k

        // remove s from B_i
        b_forward[b_backward[s]] = b_forward[s];
        b_backward[b_forward[s]] = b_backward[s];

        // add s to B_k
        unsigned int last = b_backward[B_k];
        b_forward[last] = s;
        b_forward[s] = B_k;
        b_backward[s] = last;
        b_backward[B_k] = s;

        block[s] = B_k;
        block[B_k]++;
        block[B_i]--;

        SD[B_i]--;  // there is now one state less in B_i that goes with a into B_j

        if(dfa->debug) {
          DFA_printBlocks(dfa, block, b_forward, b_backward, lastBlock);
          printf("finished move\n");
        }
      }
    } // of block splitting

    if(dfa->debug) {
      DFA_printBlocks(dfa, block, b_forward, b_backward, lastBlock);
      printf("updating L\n");
    }

    // update L
    for(unsigned int indexTwin = 0; indexTwin < numSplit; indexTwin++) {
      B_i = twin[indexTwin];
      unsigned int B_k = twin[B_i];
      for(unsigned int c = 0; c < numInput; c++) {
        int B_i_c = (B_i - b0) * numInput + c;
        int B_k_c = (B_k - b0) * numInput + c;

        if(l_forward[B_i_c] > 0) {
          // (B_i,c) already in L --> put (B_k,c) in L
          unsigned int last = l_backward[anchorL];

          l_backward[anchorL] = B_k_c;
          l_forward[last] = B_k_c;
          l_backward[B_k_c] = last;
          l_forward[B_k_c] = anchorL;
        } else {
          // put the smaller block in L
          if (block[B_i] <= block[B_k]) {
            unsigned int last = l_backward[anchorL];

            l_backward[anchorL] = B_i_c;
            l_forward[last] = B_i_c;
            l_backward[B_i_c] = last;
            l_forward[B_i_c] = anchorL;
          } else {
            unsigned int last = l_backward[anchorL];

            l_backward[anchorL] = B_k_c;
            l_forward[last] = B_k_c;
            l_backward[B_k_c] = last;
            l_forward[B_k_c] = anchorL;
          }
        }
      }
    }
  }

  if(dfa->debug) {
    printf("\n>> Result\n");
    DFA_printBlocks(dfa, block, b_forward, b_backward, lastBlock);
  }

  // Clean up
  free(inv_list_last);
  free(inv_lists);
  free(D);
  free(SD);
  free(twin);
  free(inv_delta_set);
  free(inv_delta);
  free(l_backward);
  free(l_forward);

  // transform the transition table

  // trans[i] is the state j that will replace state i, i.e.
  // states i and j are equivalent
  int *trans = (int *)malloc(dfa->numStates * sizeof(int));

  // kill[i] is true iff state i is redundant and can be removed
  struct BitSet *kill = BitSet_init(dfa->numStates);

  // move[i] is the amount line i has to be moved in the transition table
  // (because states j < i have been removed)
  int *move = (int *)malloc(dfa->numStates * sizeof(int));

  // fill arrays trans[] and kill[] (in O(n))
  for(unsigned int b = b0 + 1; b <= lastBlock; b++) { // b0 contains the error state
    // get the state with smallest value in current block
    unsigned int s = b_forward[b];
    unsigned int min_s = s; // there are no empty blocks!
    for(; s != b; s = b_forward[s]) {
      if(min_s > s) {
        min_s = s;
      }
    }

    // now fill trans[] and kill[] for this block
    // (and translate states back to partial DFA)
    min_s--;
    for(s = b_forward[b] - 1; s != b - 1; s = b_forward[s + 1] - 1) {
      trans[s] = min_s;
      if(s != min_s) {
        BitSet_set(kill, s);
        if(dfa->debug) {
          printf("Killing state %d\n", s);
        }
      }
    }
  }

  // fill array move[] (in O(n))
  unsigned int amount = 0;
  for(unsigned int i = 0; i < dfa->numStates; i++) {
    if(BitSet_isSet(kill, i)) {
      amount++;
    } else {
      move[i] = amount;
    }
  }

  unsigned int i, j;
  // j is the index in the new transition table
  // the transition table is transformed in place (in O(c n))
  for(i = 0, j = 0; i < dfa->numStates; i++) {
    // we only copy lines that have not been removed
    if(! BitSet_isSet(kill, i)) {
      // translate the target states
      for(unsigned int c = 0; c < numInput; c++) {
        if( TRANS(dfa, i, c) >= 0 ) {
          TRANS(dfa, j, c) = trans[ TRANS(dfa, i, c) ];
          TRANS(dfa, j, c) -= move[ TRANS(dfa, j, c) ];
        } else {
          TRANS(dfa, j, c) = TRANS(dfa, i, c);
        }
      }

      /* FIXME yuck */
      if(BitSet_isSet(dfa->satBit, i)) {
        BitSet_set(dfa->satBit, j);
      } else {
        BitSet_clear(dfa->satBit, j);
      }

      j++;
    }
  }

  /* Clear the remaining satBits. */
  for(unsigned int k = j; k < dfa->numStates; k++) {
    BitSet_clear(dfa->satBit, k);
  }

  /* FIXME adjust the initial states. */
  for(unsigned int x = 0; x < dfa->numSymbols; x++) {
    if(dfa->initial[x] >= 0) {
      dfa->initial[x]  = trans[ dfa->initial[x] ];
      dfa->initial[x] -=  move[ dfa->initial[x] ];
    }
  }

  dfa->numStates = j;

  // FIXME and the rest
  free(move);
  free(trans);
  BitSet_free(kill);

  free(b_backward);
  free(b_forward);
  free(block);

  if(dfa->debug) {
    printf("%d states in minimized DFA\n", dfa->numStates);
  }
}
