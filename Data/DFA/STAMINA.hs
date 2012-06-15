-- | An interface to the Berkeley/Colorado STAMINA tool.
--
-- STAMINA minimizes the number of states in an under-specified finite
-- state automata. This problem is NP-complete in general (unlike the
-- problem solved by Hopcroft's algorithm and its modern
-- descendants.).
--
-- It is part of Berkeley's SIS distribution: <http://embedded.eecs.berkeley.edu/pubs/downloads/sis/index.htm>
module Data.DFA.STAMINA
       (
         minimize
       ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude
import Control.Monad ( unless, when )

import System.Process ( readProcess )
import System.Directory ( removeFile )
import System.IO ( openTempFile )

import Data.DFA ( DFA )
import qualified Data.DFA as DFA
import qualified Data.DFA.KISS2 as KISS2

-------------------------------------------------------------------

-- | Minimize an automaton using STAMINA.
--
-- The first argument is the path to STAMINA.
--
-- FIXME This creates a new DFA (it really shouldn't). It inherits the
-- debugging setting from the argument @DFA@.
minimize :: FilePath -> DFA -> IO DFA
minimize stamina dfa =
  do debugging <- DFA.debugging dfa
     (tmpfile, _) <- openTempFile "/tmp" "hDFA_stamina.kiss2"
     when debugging $ putStrLn $ "STAMINA.minimize: tmpfile: " ++ tmpfile
     KISS2.writeToFile dfa tmpfile
     kiss2 <- readProcess stamina [tmpfile] ""
     -- unless debugging $ removeFile tmpfile
     KISS2.read debugging kiss2
