module T where

import qualified Data.DFA as DFA

-- Smoke test: the basic functionality works.
ok_simple =
  do dfa <- DFA.initialize
     mapM_ (DFA.addInitialTransition dfa) i
     mapM_ (DFA.addTransition dfa) g
     DFA.minimize dfa
     DFA.finished dfa
  where
    i = [ (0, 1) ]
    g = [ (0, 0, 1), (0, 1, 0), (1, 0, 0), (1, 1, 0) ]
