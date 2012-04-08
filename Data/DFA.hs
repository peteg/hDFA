-- |
-- Representation of DFAs and some simple algorithms on them.
--
-- (C) Peter Gammie 2010-2012, peteg42 at gmail dot com
module Data.DFA
       (
         DFA
       , Label
       , State

         -- * Initialisation
       , initialize
       , finished

         -- * Construction
       , addTransition
       , setFinal
       , minimize

         -- * Traversal
       , foldTransitions

         -- * Inspection
       , getInitialState
       , numStates
       , numSymbols
       , isFinal
       , debugging

       , loadFromFile
       , dumpToFile
       ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude
import Control.Monad	( foldM )

import Foreign
import Foreign.C

-------------------------------------------------------------------

-- | The type of DFAs is abstract: it is a pointer to a C @struct@.
newtype DFA = DFA (Ptr DFA)

-- | Labels are represented using C @unsigned int@s.
type Label = CUInt
-- | States are represented using C @unsigned int@s.
type State = CUInt

{- FIXME
cToNum :: (Num i, Integral e) => e -> i
cToNum  = fromIntegral . toInteger
-}

-- | Create a new @DFA@.
initialize :: Bool -- ^ Debugging?
           -> State -- ^ Initial state
           -> IO DFA
initialize debug initial = dfa_init (fromBool debug) initial

-- | Add a transition from the given @State@ on the given @Label@ to
-- the given @State@ to @DFA@.
addTransition :: DFA -> (State, Label, State) -> IO ()
addTransition dfa (t, l, h) = addTransition' dfa t l h

-- | Is the debugging flag set?
debugging :: DFA -> IO Bool
debugging = fmap toBool . debugging'

-- | Load a @DFA@ from a file in FIXME format.
loadFromFile :: FilePath -> IO DFA
loadFromFile fname = fmap DFA $ throwErrnoPathIfNull "Data.DFA.loadFromFile" fname $
    withCString fname loadFromFile'

-- | Dump a @DFA@ to a file in FIXME format.
dumpToFile :: DFA -> FilePath -> IO ()
dumpToFile dfa fname = throwErrnoPathIfMinus1_ "Data.DFA.dumpToFile" fname $
    withCString fname (dumpToFile' dfa)

-- | Reduce the @DFA@ using Hopcroft's algorithm.
minimize :: DFA
         -> Bool -- ^ Preserve states that cannot reach final states.
         -> IO ()
minimize dfa = minimize' dfa . fromBool

-------------------------------------------------------------------

-- Traversal combinators.

-- | Is the state @s@ final?
isFinal :: DFA -> State -> IO Bool
isFinal dfa = fmap toBool . isFinal' dfa

-- | Traverse the transitions of @DFA@ by invoking the given function
-- on each of them.
--
-- DFAs aren't functorial (they're monomorphic), so we cannot use
-- @Traversable@.
foldTransitions :: DFA -> ((State, Label, State, Bool) -> b -> IO b) -> b -> IO b
foldTransitions dfa f b0 =
  do trans <- numTransitions dfa
     foldM g b0 [ 0 .. trans - 1 ]
  where
    g b i =
      do t <- transition_start dfa i
         l <- transition_label dfa i
         h <- transition_end dfa i
         hf <- isFinal dfa h
         f (t, l, h, hf) b

-------------------------------------------------------------------

-- | Create a new @DFA@.
foreign import ccall unsafe "dfa.h DFA_init" dfa_init :: Int -> State -> IO DFA

-- | Get the initial state.
foreign import ccall unsafe "dfa.h DFA_getInitialState"
        getInitialState :: DFA -> IO State

-- foreign import ccall unsafe "dfa.h DFA_setInitialState" setInitialState :: DFA -> State -> IO ()

-- | Garbage-collect a @DFA@.
foreign import ccall unsafe "dfa.h DFA_free" finished :: DFA -> IO ()

-- | Returns the number of states that are actually present in @DFA@.
foreign import ccall unsafe "dfa.h DFA_numStates"  numStates :: DFA -> IO CUInt

-- | Returns the number of symbols that are actually present in @DFA@.
foreign import ccall unsafe "dfa.h DFA_numSymbols" numSymbols :: DFA -> IO CUInt

-- | Returns the number of transitions that are actually present in @DFA@.
foreign import ccall unsafe "dfa.h DFA_numTransitions" numTransitions :: DFA -> IO CUInt

foreign import ccall unsafe "dfa.h DFA_transition_start"
        transition_start :: DFA -> CUInt -> IO State
foreign import ccall unsafe "dfa.h DFA_transition_label"
        transition_label :: DFA -> CUInt -> IO Label
foreign import ccall unsafe "dfa.h DFA_transition_end"
        transition_end :: DFA -> CUInt -> IO State

foreign import ccall unsafe "dfa.h DFA_isFinal"
        isFinal' :: DFA -> State -> IO CInt {- FIXME Bool -}

foreign import ccall unsafe "dfa.h DFA_addTransition"
         addTransition' :: DFA -> State -> Label -> State -> IO ()

-- | Set the final bit associated with @State@.
--
-- The minimization algorithm will distinguish states with different
-- bits (that are otherwise bisimilar).
foreign import ccall unsafe "dfa.h DFA_setFinal"
         setFinal :: DFA -> State -> IO ()

foreign import ccall unsafe "dfa.h DFA_minimize"
         minimize' :: DFA -> CInt {- FIXME Bool -} -> IO ()

-- | Is the debugging flag set?
foreign import ccall unsafe "dfa.h DFA_debugging"
         debugging' :: DFA -> IO CInt -- FIXME actually CBool

-- | Dump the DFA to a file in FIXME format.
foreign import ccall unsafe "dfa.h DFA_dumpToFile"
         dumpToFile' :: DFA -> CString -> IO CInt

-- | Load a DFA from a file in FIXME format.
foreign import ccall unsafe "dfa.h DFA_loadFromFile"
         loadFromFile' :: CString -> IO (Ptr DFA)
