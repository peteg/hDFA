/* Driver for the automata format used by Antti. */

#include "dfa.h"

int
main(int argc, char *argv[])
{
  struct DFA *dfa = DFA_load(stdin);
  DFA_minimize(dfa);
  DFA_dump(dfa, stdout);

  return 0;
}
