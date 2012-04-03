{- Berkeley KISS2 format operations.
 - Copyright   :  (C)opyright 2011-2012 peteg42 at gmail dot com
 - License     :  BSD (see LICENCE for details)
 -}
module Data.DFA.KISS2
       (
         read
       , writeToFile
       ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( lex, read )
import Control.Monad ( when )
import Data.List ( foldl' )
import Foreign.C

-- import Data.Map ( Map )
import qualified Data.Map as Map

import Data.DFA ( DFA, State )
import qualified Data.DFA as DFA

-------------------------------------------------------------------

cToNum :: (Num i, Integral e) => e -> i
cToNum  = fromIntegral . toInteger

-- | The initial state.
q0 :: State
q0 = 0

-- | Read a @DFA@ from KISS2 format.
--
-- A very sloppy and incomplete parser. Assumes there is a single
-- output.
read :: Bool -> String -> IO DFA
read debug ls =
  do let s = foldl' lex_states (Map.empty, initial_state) (lines ls)
     dfa <- DFA.initialize debug q0
     _ <- mapM_ (lex_trans dfa s) (lines ls)
     return dfa
  where
    initial_state = error "KISS2.read: no initial state."

    -- FIXME not especially robust.
    state_name st out = st ++ "_" ++ out

    -- This needs to be the inverse of what writeKISS2ToFile does.
    -- lex_inputs = cToNum . length . takeWhile (== '0') -- one-hot
    lex_inputs is = sum [ 2 ^ x | (i, x) <- zip is [(0::Int) .. ], i == '1' ]

    lex_out out = out == "1"

    -- Build a map of states, and find the initial state.
    lex_states s@(sm, _) l = case l of
      '0':_ -> lex_states_trans s l
      '1':_ -> lex_states_trans s l
        -- The reset/initial state is unique.
      '.':'r':rest -> case words rest of
        [st] -> (sm, st)
        _ -> error $ "readKISS2: malformed reset line: '" ++ l ++ "'"
        -- Ignore everything else.
      _ -> s

    -- Ignore "from" states: assume the graph is connected.
    -- It may be that the initial state has no incoming edges.
    -- (+1) to account for the initial state
    lex_states_trans s = lex_states_trans2 s . words
    lex_states_trans2 (sm, is) [_inputs, _from, to, out] =
      let t = state_name to out
          sm' = case t `Map.lookup` sm of
            Nothing -> Map.insert t (cToNum (Map.size sm + 1)) sm
            Just {} -> sm
       in sm' `seq` is `seq` (sm', is)
    lex_states_trans2 _s l = error $ "readKISS2: failed to lex: '" ++ unwords l ++ "'"

    -- Add the transitions to the DFA.
    lex_trans dfa s l = case l of
      '0':_ -> lex_trans1 dfa s l
      '1':_ -> lex_trans1 dfa s l
      _ -> return ()

    lex_trans1 dfa s = lex_trans2 dfa s . words
    lex_trans2 dfa (sm, is) [inputs, from, to, out] =
      do let sym = lex_inputs inputs
             Just t = state_name to out `Map.lookup` sm
         -- Treat all outgoing transitions from the reset state as
         -- initial transitions.
         when (from == is) $ DFA.addTransition dfa (q0, sym, t)
         when (lex_out out) $ DFA.setFinal dfa t
         -- Add transitions from both "from" states.
         -- FIXME in general "out" is not just boolean.
         let add_trans o =
               case state_name from o `Map.lookup` sm of
                 Nothing -> return ()
                 Just f -> DFA.addTransition dfa (f, sym, t)
         add_trans "0"
         add_trans "1"
    lex_trans2 _dfa _sm l = error $ "readKISS2: failed to lex: '" ++ unwords l ++ "'"

-- | Write @DFA@ to a file with the given @FilePath@ in Berkeley KISS2 format.
writeToFile :: DFA -> FilePath -> IO ()
writeToFile dfa fname =
  throwErrnoPathIfMinus1_ "KISS2.writetoFile" fname $
    withCString fname (writeKISS2ToFile' dfa)

foreign import ccall unsafe "dfa.h DFA_writeKISS2ToFile"
         writeKISS2ToFile' :: DFA -> CString -> IO CInt
