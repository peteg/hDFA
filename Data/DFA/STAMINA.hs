{- Berkeley/Colorado STAMINA interface.
 - Copyright   :  (C)opyright 2011-2012 peteg42 at gmail dot com
 - License     :  BSD (see LICENCE for details)

STAMINA minimizes under-specified finite state automata.

It is part of Berkeley's SIS distribution:

http://embedded.eecs.berkeley.edu/pubs/downloads/sis/index.htm

 -}
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
-- The first argument is the path to STMAINA.
--
-- FIXME Creates a new DFA (it really shouldn't). Inherits debugging
-- setting from the argument DFA.
minimize :: FilePath -> DFA -> IO DFA
minimize stamina dfa =
  do debugging <- DFA.debugging dfa
     (tmpfile, _) <- openTempFile "/tmp" "hDFA_stamina.kiss2"
     when debugging $ putStrLn $ "STAMINA.minimize: tmpfile: " ++ tmpfile
     KISS2.writeToFile dfa tmpfile
     kiss2 <- readProcess stamina [tmpfile] ""
     -- unless debugging $ removeFile tmpfile
     KISS2.read debugging kiss2
