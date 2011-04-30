/*
 * Test harness for the DFA code.
 *
 * (C) 2010 Peter Gammie, peteg42 at gmail dot com
 */

#include <stdlib.h>
#include <stdio.h>

#include "dfa.h"

void
test_graph(char *filename)
{
  FILE *f;
  struct DFA *dfa;

  if((f = fopen(filename, "r")) == NULL) {
    return;
  }

  dfa = DFA_init();

  state_t s, t;
  label_t l;

  while(fscanf(f, "%u\n", &s) == 1) {
    printf("%u sat\n", s);
    DFA_setSatBit(dfa, s);
  }

  // FIXME error handling.
  fscanf(f, "--\n");

  while(fscanf(f, "%u %u %u\n", &s, &l, &t) == 3) {
    printf("%u -%u-> %d\n", s, l, t);
    DFA_addTransition(dfa, s, l, t);
  }

  // FIXME error handling.
  fscanf(f, "==\n");

  // FIXME also slurp in the final graph.

  DFA_writeDot(dfa, stdout);
  DFA_minimize(dfa);
  DFA_writeDot(dfa, stdout);

  DFA_free(dfa);
  fclose(f);
}

int
main(int argc, char *argv[])
{
  for(unsigned int i = 1; i < argc; i++) {
    test_graph(argv[i]);
  }

  return EXIT_SUCCESS;
}
