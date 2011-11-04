{- graphviz DOT format operations.
 - Copyright   :  (C)opyright 2011 peteg42 at gmail dot com
 - License     :  GPL (see COPYING for details)
 -}
module Data.DFA.DOT
       (
         writeToFile
       ) where

-------------------------------------------------------------------
-- Dependencies.
-------------------------------------------------------------------

import Prelude hiding ( lex, read )

import Foreign
import Foreign.C

import Data.DFA ( DFA, Label )
-- import qualified Data.DFA as DFA

-------------------------------------------------------------------

-- | Write @DFA@ to a file with the given @FilePath@ in graphviz DOT
-- format, using the given labelling function.
writeToFile :: DFA -> FilePath -> (Label -> String) -> IO ()
writeToFile dfa fname labelFn =
  do labelFunPtr <- mkLabelFunPtr labelFn'
     throwErrnoPathIfMinus1_ "writeDotToFile" fname $
       withCString fname (writeDotToFile' dfa labelFunPtr)
  where
   labelFn' l buf =
     pokeArray0 (castCharToCChar '\0') buf (map castCharToCChar (take 79 (labelFn l))) -- FIXME constant, char casts

foreign import ccall "wrapper" mkLabelFunPtr :: (Label -> Ptr CChar -> IO ()) -> IO (FunPtr (Label -> Ptr CChar -> IO ()))

-- Note this can call back into Haskell land.
foreign import ccall safe "dfa.h DFA_writeDotToFile"
         writeDotToFile' :: DFA -> FunPtr (Label -> Ptr CChar -> IO ()) -> CString -> IO CInt
