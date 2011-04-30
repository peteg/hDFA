-- |
-- Representation of DFAs and some simple algorithms on them.

{-
 - Ported to C by Peter Gammie, peteg42 at gmail dot com
 - This port (C) 2010-2011 Peter Gammie.
 - Original code (JFlex.DFA from http://www.jflex.de/):
 -
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
 -
 -}
module Data.DFA
       (
         DFA
       , Label
       , State

         -- * Initialisation
       , initialize
       , finished

         -- * Construction
       , addInitialTransition
       , addTransition
       , setSatBit
       , minimize

         -- * Traversal
       , foldInitialTransitions
       , foldTransitions

         -- * Inspection
       , numStates
       , numSymbols
       , writeDotToFile
       ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

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

cToNum :: (Num i, Integral e) => e -> i
cToNum  = fromIntegral . toInteger

-- | Add an initial transition for the given @Label@ to the given
-- @State@ to @DFA@.
addInitialTransition :: DFA -> (Label, State) -> IO ()
addInitialTransition dfa (l, t) = addInitialTransition' dfa l t

-- | Add a transition from the given @State@ on the given @Label@ to
-- the given @State@ to @DFA@.
addTransition :: DFA -> (State, Label, State) -> IO ()
addTransition dfa (s, l, t) = addTransition' dfa s l t

-- | Write @DFA@ to a file with the given @FilePath@, using the given
-- labelling function.
writeDotToFile :: DFA -> FilePath -> (Label -> String) -> IO ()
writeDotToFile dfa fname labelFn =
  do labelFunPtr <- mkLabelFunPtr labelFn'
     throwErrnoPathIfMinus1_ "writeDotToFile" fname $
       withCString fname (writeDotToFile' dfa labelFunPtr)
  where
   labelFn' l buf =
     pokeArray0 (castCharToCChar '\0') buf (map castCharToCChar (take 79 (labelFn l))) -- FIXME constant, char casts

foreign import ccall "wrapper" mkLabelFunPtr :: (Label -> Ptr CChar -> IO ()) -> IO (FunPtr (Label -> Ptr CChar -> IO ()))

-------------------------------------------------------------------

-- Traversal combinators.

-- We'd hope to do this more efficiently in C land, maybe.

-- | Traverse the initial transitions of @DFA@ by invoking the given
-- function on each of them.
--
-- DFAs aren't functorial (they're monomorphic), so we cannot use
-- @Traversable@.
foldInitialTransitions :: DFA -> ((Label, State, Bool) -> b -> IO b) -> b -> IO b
foldInitialTransitions dfa f b0 =
  do syms <- numSymbols dfa
     foldM g b0 [ 0 .. syms - 1 ]
  where
    g b l =
      do s <- initialTransition dfa l
         if s >= 0
           then do let s' = cToNum s
                   sb <- fmap toBool (satBit dfa s')
                   f (l, s', sb) b
           else return b

-- | Traverse the transitions of @DFA@ by invoking the given function
-- on each of them.
--
-- DFAs aren't functorial (they're monomorphic), so we cannot use
-- @Traversable@.
foldTransitions :: DFA -> ((State, Label, State, Bool) -> b -> IO b) -> b -> IO b
foldTransitions dfa f b0 =
  do states <- numStates  dfa
     syms   <- numSymbols dfa
     foldM g b0 [ (i, j) | i <- [ 0 .. states - 1 ], j <- [ 0 .. syms - 1 ] ]
  where
    g b (s, l) =
      do t <- transition dfa s l
         if t >= 0
           then do let s' = cToNum s
                       t' = cToNum t
                   tb <- fmap toBool (satBit dfa t')
                   f (s', l, t', tb) b
           else return b

-------------------------------------------------------------------

-- | Create a new @DFA@.
foreign import ccall unsafe "dfa.h DFA_init" initialize :: IO DFA

-- | Garbage-collect a @DFA@.
foreign import ccall unsafe "dfa.h DFA_free" finished :: DFA -> IO ()

-- | Returns the number of states that are actually present in @DFA@.
foreign import ccall unsafe "dfa.h DFA_numStates"  numStates :: DFA -> IO CUInt

-- | Returns the number of symbols that are actually present in @DFA@.
foreign import ccall unsafe "dfa.h DFA_numSymbols" numSymbols :: DFA -> IO CUInt

foreign import ccall unsafe "dfa.h DFA_initialTransition"
        initialTransition :: DFA -> Label -> IO CInt
foreign import ccall unsafe "dfa.h DFA_transition"
        transition :: DFA -> State -> Label -> IO CInt
foreign import ccall unsafe "dfa.h DFA_satBit"
        satBit :: DFA -> State -> IO CInt -- FIXME actually CBool

foreign import ccall unsafe "dfa.h DFA_addInitialTransition"
         addInitialTransition' :: DFA -> Label -> State -> IO ()
foreign import ccall unsafe "dfa.h DFA_addTransition"
         addTransition' :: DFA -> State -> Label -> State -> IO ()

-- | Set the bit associated with @State@. Used to indicate finality,
-- acceptance, etc. The minimization algorithm will distinguish states
-- with different bits (that are otherwise bisimilar).
foreign import ccall unsafe "dfa.h DFA_setSatBit"
         setSatBit :: DFA -> State -> IO ()

-- | Reduce the @DFA@ using Hopcroft's algorithm.
foreign import ccall unsafe "dfa.h DFA_minimize"
         minimize :: DFA -> IO ()

-- Note this can call back into Haskell land.
foreign import ccall safe "dfa.h DFA_writeDotToFile"
         writeDotToFile' :: DFA -> FunPtr (Label -> Ptr CChar -> IO ()) -> CString -> IO CInt
