/*
 * Representation of DFAs and algorithms on them.
 *
 * (C) Peter Gammie 2010-2012, peteg42 at gmail dot com
 */

#ifndef _DFA_H_
#define _DFA_H_

#include <stdbool.h>
#include <stdio.h>

struct DFA;

/* Maximum length of a label. FIXME share with Haskell land. */
#define LABEL_LEN 201

/* Signals the lack of an edge in the adjacency matrix. */
#define NO_TARGET (-1)

typedef unsigned int state_t;
typedef unsigned int label_t;

struct DFA *DFA_init(bool, state_t initial);
struct DFA *DFA_initialize(bool debug, state_t initial, unsigned int numStates, unsigned int numTrans);
void DFA_free(struct DFA *dfa);

state_t DFA_getInitialState(struct DFA *dfa);
void DFA_setInitialState(struct DFA *dfa, state_t initial);

void DFA_addTransition(struct DFA *dfa, state_t start, label_t label, state_t end);

void DFA_setFinal(struct DFA *dfa, state_t state);

unsigned int DFA_numStates(struct DFA *dfa);
unsigned int DFA_numSymbols(struct DFA *dfa);
unsigned int DFA_numTransitions(struct DFA *dfa);

unsigned int DFA_transition_start(struct DFA *dfa, unsigned int i);
unsigned int DFA_transition_end(struct DFA *dfa, unsigned int i);
unsigned int DFA_transition_label(struct DFA *dfa, unsigned int i);

/* FIXME returns false on invalid states. */
bool DFA_isFinal(struct DFA *dfa, state_t state);

void DFA_toDot(struct DFA *dfa, void (label_fn)(label_t, char[LABEL_LEN]), FILE *file);
/* FIXME returns (-1)/errno if anything goes wrong. */
int DFA_writeDotToFile(struct DFA *dfa, void (label_fn)(label_t, char[LABEL_LEN]), char *file);

void DFA_toKISS2(struct DFA *dfa, FILE *file);
/* FIXME returns (-1)/errno if anything goes wrong. */
int DFA_writeKISS2ToFile(struct DFA *dfa, char *file);

void DFA_minimize(struct DFA *dfa, bool preserve_unreachable_states);

bool DFA_debugging(struct DFA *dfa);

struct DFA *DFA_load(FILE *file);
void DFA_dump(struct DFA *dfa, FILE *file);

#endif /* _DFA_H_ */
