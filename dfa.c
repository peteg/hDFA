/*
 * Representation of DFAs and algorithms on them.
 *
 * (C) Peter Gammie 2010-2012, peteg42 at gmail dot com
 * Original minimisation algorithm implementation in C++ (C) Antti Valmari 2011

Adjacency-list representation.

We have no use for actions, just a distinction between two types of
states. (The initial partition is based on a single bit.)

This representation does not ensure that the finite automaton is
deterministic. We assume it is in a few places, hopefully signposted.

 */

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>

#include "bitsets.h"
#include "dfa.h"
#include "qsort.h"

#define DEFAULT_NUM_STATES 128
#define DEFAULT_NUM_TRANS 128

#define MAX(a, b) ((a) > (b) ? (a) : (b))

struct DFA {
  bool debug;
  unsigned int
    max_mm, // allocated memory for this many transitions
    nn,     // number of states
    mm,     // number of transitions
    ll,     // number of labels
    q0,     // initial state
    *T,     // tails of transitions
    *L,     // labels of transitions
    *H;     // heads of transitions
  struct BitSet *isFinal; // record the final states - O(1) lookups.
};

static inline
void malloc_unsigned_int(unsigned int **a, size_t width)
{
  if((*a = (unsigned int *)calloc(width, sizeof(unsigned int))) == NULL) {
    perror("malloc_unsigned_int()");
    abort();
  }
}

struct DFA *
DFA_initialize(bool debug, state_t initial, unsigned int numStates, unsigned int numTrans)
{
  struct DFA * dfa = (struct DFA *)malloc(sizeof(struct DFA));

  dfa->debug = debug;

  dfa->max_mm = numTrans;
  dfa->nn = initial + 1;
  dfa->mm = 0;
  dfa->ll = 0;
  dfa->q0 = initial;

  malloc_unsigned_int(&dfa->T, dfa->max_mm);
  malloc_unsigned_int(&dfa->L, dfa->max_mm);
  malloc_unsigned_int(&dfa->H, dfa->max_mm);

  dfa->isFinal = BitSet_init(numStates);

  /* fprintf(stderr, "DFA_init(%p, bs = %p)\n", dfa, dfa->isFinal); */

  return dfa;
}

struct DFA *
DFA_init(bool debug, state_t initial)
{
  return DFA_initialize(debug, initial, DEFAULT_NUM_STATES, DEFAULT_NUM_TRANS);
}

void
DFA_free(struct DFA *dfa)
{
  free(dfa->T);
  free(dfa->L);
  free(dfa->H);
  BitSet_free(dfa->isFinal);
  free(dfa);
}

void
DFA_addTransition(struct DFA *dfa, state_t start, label_t label, state_t end)
{
  /* fprintf(stderr, "DFA_addTransition(%p, %p, %d, %d)\n", dfa, dfa->isFinal, dfa->mm, BitSet_size(dfa->isFinal)); */

  if(dfa->mm == dfa->max_mm) {
    unsigned int new_max_mm = 2 * dfa->max_mm;

    /* fprintf(stderr, "Resizing transitions: %d -> %d\n", dfa->max_mm, new_max_mm); */

    dfa->max_mm = new_max_mm;

    dfa->T = realloc(dfa->T, new_max_mm * sizeof(unsigned int));
    dfa->L = realloc(dfa->L, new_max_mm * sizeof(unsigned int));
    dfa->H = realloc(dfa->H, new_max_mm * sizeof(unsigned int));
  }

  dfa->nn = MAX(dfa->nn, MAX(start, end) + 1);
  dfa->ll = MAX(dfa->ll, label);

  unsigned int mm = dfa->mm++;

  dfa->T[mm] = start;
  dfa->L[mm] = label;
  dfa->H[mm] = end;

  /* fprintf(stderr, "DFA_addTransition end (%p, %p, %d, %d)\n", dfa, dfa->isFinal, dfa->mm, BitSet_size(dfa->isFinal)); */
}

state_t
DFA_getInitialState(struct DFA *dfa)
{
  return dfa->q0;
}

void
DFA_setInitialState(struct DFA *dfa, state_t initial)
{
  dfa->q0 = initial;
}

void
DFA_setFinal(struct DFA *dfa, state_t state)
{
  /* fprintf(stderr, "DFA_setFinal(%p, %d, %d)\n", dfa, BitSet_size(dfa->isFinal), state); */

  if(state >= BitSet_size(dfa->isFinal)) {
    unsigned int max_states = BitSet_size(dfa->isFinal);
    while(max_states <= state) {
      max_states *= 2;
    }

    BitSet_realloc(dfa->isFinal, max_states);
  }

  dfa->nn = MAX(dfa->nn, state + 1);
  BitSet_set(dfa->isFinal, state);
}

unsigned int
DFA_numStates(struct DFA *dfa)
{
  return dfa->nn;
}

unsigned int
DFA_numTransitions(struct DFA *dfa)
{
  return dfa->mm;
}

unsigned int
DFA_numSymbols(struct DFA *dfa)
{
  return dfa->ll;
}

bool
DFA_isFinal(struct DFA *dfa, state_t state)
{
  return (state < dfa->nn)
    ? BitSet_isSet(dfa->isFinal, state)
    : false;
}

bool
DFA_debugging(struct DFA *dfa)
{
  return dfa->debug;
}

/* Get the ith transition. */
unsigned int
DFA_transition_start(struct DFA *dfa, unsigned int i)
{

  return dfa->T[i];
}

unsigned int
DFA_transition_end(struct DFA *dfa, unsigned int i)
{
  return dfa->H[i];
}

unsigned int
DFA_transition_label(struct DFA *dfa, unsigned int i)
{
  return dfa->L[i];
}

/* **************************************** */

/* Load and store the automaton in Antti's format. */

struct DFA *
DFA_load(FILE *file)
{
  struct DFA *dfa;
  unsigned int numTrans, numStates, numFinal;
  state_t q0;

  /* Read sizes and reserve most memory */
  fscanf(file, "%u%u%u%u", &numStates, &numTrans, &q0, &numFinal);
  dfa = DFA_initialize(false, q0, numStates, numTrans);

  /* Read transitions */
  for(unsigned int t = 0; t < numTrans; ++t) {
    state_t t, h;
    label_t l;

    scanf("%u%u%u", &t, &l, &h);
    /* printf("trans: %u %u %u\n", t, l, h); */
    DFA_addTransition(dfa, t, l, h);
  }

  /* Read final states */
  for(unsigned int i = 0; i < numFinal; ++i) {
    state_t f;
    scanf("%u\n", &f);
    /* printf("final: %u\n", f); */
    DFA_setFinal(dfa, f);
  }

  return dfa;
}

struct DFA *
DFA_loadFromFile(char *file)
{
  FILE *f;
  struct DFA *dfa = NULL;

  if((f = fopen(file, "w")) != NULL) {
    dfa = DFA_load(f);
    fclose(f);
  }

  return dfa;
}

void
DFA_dump(struct DFA *dfa, FILE *file)
{
  unsigned int ff = 0;

  for(unsigned int i = 0; i < BitSet_size(dfa->isFinal); i++) {
    if(BitSet_isSet(dfa->isFinal, i)) {
      ff++;
    }
  }

  fprintf(file, "%u %u %u %u\n", dfa->nn, dfa->mm, dfa->q0, ff);

  for(unsigned int i = 0; i < dfa->mm; i++) {
    fprintf(file, "%u %u %u\n", dfa->T[i], dfa->L[i], dfa->H[i]);
  }
  for(unsigned int i = 0; i < BitSet_size(dfa->isFinal); i++) {
    if(BitSet_isSet(dfa->isFinal, i)) {
      fprintf(file, "%u\n", i);
    }
  }
}

int
DFA_dumpToFile(struct DFA *dfa, char *file)
{
  FILE *f;
  bool ret = -1;

  if((f = fopen(file, "w")) != NULL) {
    DFA_dump(dfa, f);
    fclose(f);

    ret = 0;
  }

  return ret;
}

/* **************************************** */

/* Render the automaton in DOT format. FIXME This encodes our
   non-standard notion of "initial transitions". */

void
DFA_toDot(struct DFA *dfa, void (label_fn)(label_t, char[LABEL_LEN]), FILE *file)
{
  if(dfa->debug) {
    printf("DFA_toDot\n");
  }

  fprintf(file, "digraph DFA {\n");
  fprintf(file, "\trankdir = LR\n\tnode [shape=\"circle\"]\n");

  /* Node lines for the final states. */
  for(unsigned int i = 0; i < BitSet_size(dfa->isFinal); i++) {
    if(BitSet_isSet(dfa->isFinal, i)) {
      fprintf(file, "\t%d [shape=\"doublecircle\"]\n", i);
    }
  }

  for(unsigned int i = 0; i < dfa->mm; i++) {
    unsigned int
      t = dfa->T[i],
      l = dfa->L[i],
      h = dfa->H[i];
    char buffer[LABEL_LEN];

    label_fn(l, buffer);
    if(t == dfa->q0) {
      fprintf(file, "\tinit%d[label=\"\" width=\"0.01\"];\n", i);
      fprintf(file, "\tinit%d -> %d [label=\"%s\"]\n", i, h, buffer);
    } else {
      fprintf(file, "\t%d -> %d [label=\"%s\"]\n", t, h, buffer);
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

/* Render the automaton in Berkeley's KISS2 format. */

#define INIT_STATE "init"

void
DFA_toKISS2(struct DFA *dfa, FILE *file)
{
  if(dfa->debug) {
    printf("struct DFA *oKISS2\n");
  }

  fprintf(file, "# Generated by hDFA.\n");

  /* How many bits do we need to represent the labels? (always at least 1) */
  unsigned int sym_bits = 1;
  while((1 << sym_bits) < dfa->ll + 1) sym_bits++;

  /* fprintf(stderr, "hDFA: syms: %d sym_bits: %d\n", sym, sym_bits); */

  fprintf(file, ".i %d\n", sym_bits); /* number of inputs */
  fprintf(file, ".o 1\n"); /* one output */
  fprintf(file, ".p %d\n", dfa->mm); /* number of transitions */
  fprintf(file, ".s %d\n", dfa->nn); /* number of states */
  fprintf(file, ".r " INIT_STATE "\n"); /* reset (initial) state */

  fprintf(file, "# Transitions\n");
  for(unsigned int x = 0; x < dfa->mm; x++) {
    unsigned int t = dfa->T[x];
    unsigned int l = dfa->L[x];
    unsigned int h = dfa->H[x];

    for(unsigned int i = 0; i < sym_bits; i++) {
      fprintf(file, (l & (1 << i)) ? "1" : "0");
    }
    if(t == dfa->q0) {
      fprintf(file, " " INIT_STATE " st%d %c\n",
              h, BitSet_isSet(dfa->isFinal, h) ? '1' : '0');
    } else {
      fprintf(file, " st%d st%d %c\n",
              t, h, BitSet_isSet(dfa->isFinal, h) ? '1' : '0');
    }
  }
  fprintf(file, ".e\n");
}

int
DFA_writeKISS2ToFile(struct DFA *dfa, char *file)
{
  FILE *f;
  bool ret = -1;

  if((f = fopen(file, "w")) != NULL) {
    DFA_toKISS2(dfa, f);
    fclose(f);

    ret = 0;
  }

  return ret;
}

/* **************************************** */

/*
 * This minimization routine is derived from the C++ code by Antti
 * Valmari, "Fast brief practical DFA minimization", Information
 * Processing Letters 112(6): 213-217 (2012). Please cite this if
 * appropriate.
 *
 * C version by Peter Gammie, October 2011, March 2012.
 */

/*

FIXME Antti's concern about the sorting algorithm: qsort behaves
poorly if there are a lot of identical keys.

 */

typedef struct partition {
  unsigned int z, *E, *L, *S, *F, *P;
} *partition_t;

static void
partition_init(partition_t *p_t, unsigned int n)
{
  partition_t p;

  if((p = (partition_t)malloc(sizeof(struct partition))) == NULL) {
    perror("partition_init()");
    abort();
  }
  *p_t = p;

  p->z = n ? 1 : 0;
  malloc_unsigned_int(&p->E, n);
  malloc_unsigned_int(&p->L, n);
  malloc_unsigned_int(&p->S, n);
  malloc_unsigned_int(&p->F, n);
  malloc_unsigned_int(&p->P, n);

  for(unsigned int i = 0; i < n; ++i) {
    p->E[i] = p->L[i] = i;
    p->S[i] = 0;
  }

  if(p->z) {
    p->F[0] = 0;
    p->P[0] = n;
  }
}

static void
partition_free(partition_t *p_t)
{
  free((*p_t)->E);
  free((*p_t)->L);
  free((*p_t)->S);
  free((*p_t)->F);
  free((*p_t)->P);

  free(*p_t);
  *p_t = NULL;
}

/* Algorithm state */
typedef struct min_alg_state {
  partition_t
    B,                     // blocks (consist of states)
    C;                     // cords (consist of transitions)
  unsigned int *M, *W, w;  // temporary worksets
  unsigned int *A, *F;     // Adjacent transitions
  unsigned int rr;         // number of reached states
} *min_alg_state_t;

static void
partition_mark(const struct DFA *dfa, min_alg_state_t tw, partition_t p, unsigned int e)
{
  unsigned int
    s = p->S[e],
    i = p->L[e],
    j = p->F[s] + tw->M[s];

  p->E[i] = p->E[j];
  p->L[p->E[i]] = i;

  p->E[j] = e;
  p->L[e] = j;

  if(!tw->M[s]++) {
    tw->W[tw->w++] = s;
  }
}

static void
partition_split(min_alg_state_t tw, partition_t p)
{
  while(tw->w) {
    unsigned int
      s = tw->W[--tw->w],
      j = p->F[s] + tw->M[s];

    if(j == p->P[s]){
      tw->M[s] = 0;
      continue;
    }

    if(tw->M[s] <= p->P[s] - j) {
      p->F[p->z] = p->F[s];
      p->P[p->z] = p->F[s] = j;
    } else {
      p->P[p->z] = p->P[s];
      p->F[p->z] = p->P[s] = j;
    }

    for(unsigned int i = p->F[p->z]; i < p->P[p->z]; ++i) {
      p->S[p->E[i]] = p->z;
    }

    tw->M[s] = tw->M[p->z++] = 0;
  }
}

static int
cmp(void *d, const void *i, const void *j)
{
  struct DFA *dfa = (struct DFA *)d;

  unsigned int
    m = dfa->L[*(unsigned int *)i],
    n = dfa->L[*(unsigned int *)j];

  return m < n ? -1 : (m == n ? 0 : 1);
}

static void
make_adjacent(const struct DFA *dfa, min_alg_state_t tw, unsigned int K[])
{
  for(unsigned int q = 0;  q <= dfa->nn; ++q) { tw->F[q] = 0; }
  for(unsigned int t = 0;  t < dfa->mm;  ++t) { tw->F[K[t]]++; }
  for(unsigned int q = 0;  q < dfa->nn;  ++q) { tw->F[q+1] += tw->F[q]; }
  for(unsigned int t = dfa->mm; t--; )        { tw->A[--tw->F[K[t]]] = t; }
}

static inline void
reach(const struct DFA *dfa, min_alg_state_t tw, unsigned int q)
{
  unsigned int i = tw->B->L[q];

  if(i >= tw->rr) {
    tw->B->E[i] = tw->B->E[tw->rr];
    tw->B->L[tw->B->E[i]] = i;
    tw->B->E[tw->rr] = q;
    tw->B->L[q] = tw->rr++;
  }
}

static void
rem_unreachable(struct DFA *dfa, min_alg_state_t tw, unsigned int T[], unsigned int H[])
{
  make_adjacent(dfa, tw, T);

  for(unsigned int i = 0; i < tw->rr; i++) {
    for(unsigned int j = tw->F[tw->B->E[i]]; j < tw->F[tw->B->E[i] + 1]; j++) {
      reach(dfa, tw, H[tw->A[j]]);
    }
  }

  unsigned int j = 0;
  for(unsigned int t = 0; t < dfa->mm; t++) {
    if(tw->B->L[T[t]] < tw->rr) {
      /* *NOTE* The parameters point to the dfa arrays, so this is OK. */
      dfa->H[j] = dfa->H[t];
      dfa->L[j] = dfa->L[t];
      dfa->T[j] = dfa->T[t];
      j++;
    }
  }

  dfa->mm = j;
  tw->B->P[0] = tw->rr;
  tw->rr = 0;
}

/* Minimize a DFA.
 *
 * The algorithm discards states that are not reachable from the
 * initial state or backwards reachable from a final state. Sometimes
 * we want to retain the latter; setting @preserve_unreachable_states@
 * does so.
 */
void
DFA_minimize(struct DFA *dfa, bool preserve_unreachable_states)
{
  min_alg_state_t tw;
  unsigned int ff = 0;

  if(dfa->debug) {
    printf("DFA_minimize()\n");
    DFA_dump(dfa, stdout);
  }

  /* Following a suggestion by Antti Valmari, we preserve states that
   * cannot reach a final state by adding self-transitions with a new
   * label to all final states, and then making all states final. */
  unsigned int final_label = 0;

  if(preserve_unreachable_states) {
    for(unsigned int i = 0; i < dfa->mm; i++) {
      final_label = MAX(final_label, dfa->L[i] + 1);
    }
    for(unsigned int q = 0; q < BitSet_size(dfa->isFinal); q++) {
      if(BitSet_isSet(dfa->isFinal, q)) {
        DFA_addTransition(dfa, q, final_label, q);
      }
    }
    for(unsigned int q = 0; q < BitSet_size(dfa->isFinal); q++) {
      BitSet_set(dfa->isFinal, q);
    }
  }

  /* Antti Valmari's original algorithm. */

  tw = (min_alg_state_t)malloc(sizeof(struct min_alg_state));
  tw->w = 0;
  tw->rr = 0;

  malloc_unsigned_int(&tw->A, dfa->mm);
  malloc_unsigned_int(&tw->F, dfa->nn + 1);

  partition_init(&tw->B, dfa->nn);
  partition_t B = tw->B;

  /* Remove states that cannot be reached
     from the initial state, and from which
     final states cannot be reached */
  reach(dfa, tw, dfa->q0);
  rem_unreachable(dfa, tw, dfa->T, dfa->H);

  /* Process the final states. */
  for(unsigned int q = 0; q < BitSet_size(dfa->isFinal); q++) {
    if(BitSet_isSet(dfa->isFinal, q)) {
      /* printf("Final state %d\n", q); */
      if(B->L[q] < B->P[0]) {
        reach(dfa, tw, q);
      }
    }
  }

  ff = tw->rr;
  rem_unreachable(dfa, tw, dfa->H, dfa->T);

  /* Make initial partition */
  malloc_unsigned_int(&tw->W, dfa->mm);
  malloc_unsigned_int(&tw->M, dfa->mm);

  tw->M[0] = ff;
  if(ff) {
    tw->W[tw->w++] = 0;
    partition_split(tw, B);
  }

  /* Make transition partition */
  partition_init(&tw->C, dfa->mm);
  partition_t C = tw->C;

  if(dfa->mm) {
    dfa_qsort_r(C->E, dfa->mm, sizeof(C->E[0]), dfa, cmp);

    C->z = tw->M[0] = 0;

    unsigned int a = dfa->L[C->E[0]];
    for(unsigned int i = 0; i < dfa->mm; i++) {
      unsigned int t = C->E[i];
      if(dfa->L[t] != a) {
        a = dfa->L[t]; C->P[C->z++] = i;
        C->F[C->z] = i; tw->M[C->z] = 0; }
      C->S[t] = C->z; C->L[t] = i; }
    C->P[C->z++] = dfa->mm;
  }

  /* Split blocks and cords */
  make_adjacent(dfa, tw, dfa->H);
  unsigned int b = 1;
  for(unsigned int c = 0; c < C->z; ) {
    for(unsigned int i = C->F[c]; i < C->P[c]; i++) {
      partition_mark(dfa, tw, B, dfa->T[C->E[i]]);
    }
    partition_split(tw, B);
    c++;

    while(b < B->z) {
      for(unsigned int i = B->F[b]; i < B->P[b]; i++) {
        for(unsigned int j = tw->F[B->E[i]]; j < tw->F[B->E[i] + 1]; j++) {
          partition_mark(dfa, tw, C, tw->A[j]);
        }
      }
      partition_split(tw, C);
      b++;
    }
  }

  /* Update the DFA / print out the result */

  /* Count the numbers of transitions in the result. */
  unsigned int mo = 0;

  for(unsigned int t = 0; t < dfa->mm; t++) {
    if(dfa->L[t] != final_label && B->L[dfa->T[t]] == B->F[B->S[dfa->T[t]]]) {
      mo++;
    }
  }

  /* Print the result FIXME take care of preserve_unreachable_states */
/*
  Count the number of final states in the result.
  unsigned int fo = 0;
  if(preserve_unreachable_states) {
    FIXME
  } else {
    for(unsigned int b = 0; b < B->z; b++) {
      if(B->F[b] < ff) {
        fo++;
      }
    }
  }

  printf("DFA_minimize() print result.\n");
  printf("%u %u %u %u\n", B->z, mo, B->S[dfa->q0], fo);
  for(unsigned int t = 0; t < dfa->mm; t++) {
    if(B->L[dfa->T[t]] == B->F[B->S[dfa->T[t]]]) {
      printf("%u %u %u\n", B->S[dfa->T[t]], dfa->L[t], B->S[dfa->H[t]]);
    }
  }
  for(unsigned int b = 0; b < B->z; b++) {
    if(B->F[b] < ff) {
      printf("%u\n", b);
    }
  }
 */

  /* Update the DFA */

  /* FIXME Arguable if we should realloc the original arrays or create
   * new ones; new ones may mean less memory fragmentation, just
   * maybe. */
  unsigned int *T1, *L1, *H1;
  struct BitSet *isFinal1;

  malloc_unsigned_int(&T1, mo);
  malloc_unsigned_int(&L1, mo);
  malloc_unsigned_int(&H1, mo);
  isFinal1 = BitSet_init(B->z); /* FIXME perhaps too many if preserve_unreachable_states */

  unsigned int i = 0;
  for(unsigned int t = 0; t < dfa->mm; t++) {
    if(B->L[dfa->T[t]] == B->F[B->S[dfa->T[t]]]) {
      unsigned int
        tail = B->S[dfa->T[t]],
        label = dfa->L[t],
        head = B->S[dfa->H[t]];

      if(preserve_unreachable_states && label == final_label) {
        BitSet_set(isFinal1, tail);
      } else {
        T1[i] = tail;
        L1[i] = label;
        H1[i] = head;
        i++;
      }
    }
  }
  if(!preserve_unreachable_states) {
    for(unsigned int b = 0; b < B->z; b++) {
      if(B->F[b] < ff) {
        BitSet_set(isFinal1, b);
      }
    }
  }

  free(dfa->T);
  free(dfa->L);
  free(dfa->H);
  BitSet_free(dfa->isFinal);

  dfa->max_mm = mo;
  dfa->nn = B->z;
  dfa->mm = mo;
  dfa->q0 = B->S[dfa->q0];
  dfa->T = T1;
  dfa->L = L1;
  dfa->H = H1;
  dfa->isFinal = isFinal1;

  /* Clean up FIXME and the rest. */
  free(tw->W);
  free(tw->M);
  free(tw->A);
  free(tw->F);
  partition_free(&tw->B);
  partition_free(&tw->C);
  free(tw);
}
