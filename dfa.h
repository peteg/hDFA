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
 */

#ifndef _DFA_H_
#define _DFA_H_

#include <stdbool.h>
#include <stdio.h>

struct DFA;

/* Maximum length of a label. */
#define LABEL_LEN 80

/* Signals the lack of an edge in the adjacency matrix. */
#define NO_TARGET (-1)

typedef unsigned int state_t;
typedef unsigned int label_t;

struct DFA *DFA_init(bool);
void DFA_free(struct DFA *dfa);

void DFA_addInitialTransition(struct DFA *dfa, label_t label, state_t end);
void DFA_addTransition(struct DFA *dfa, state_t start, label_t label, state_t end);

void DFA_setSatBit(struct DFA *dfa, state_t state);

unsigned int DFA_numStates(struct DFA *dfa);
unsigned int DFA_numSymbols(struct DFA *dfa);

/* FIXME returns NO_TARGET if there is no target state.
 * This interface sucks, we'd prefer a fold/iterate sort of thing. */
int DFA_initialTransition(struct DFA *dfa, label_t label);
int DFA_transition(struct DFA *dfa, state_t start, label_t label);

/* FIXME returns false on invalid states. */
bool DFA_satBit(struct DFA *dfa, state_t state);

void DFA_toDot(struct DFA *dfa, void (label_fn)(label_t, char[LABEL_LEN]), FILE *file);
/* FIXME returns (-1)/errno if anything goes wrong. */
int DFA_writeDotToFile(struct DFA *dfa, void (label_fn)(label_t, char[LABEL_LEN]), char *file);

void DFA_minimize(struct DFA *dfa);

#endif /* _DFA_H_ */
