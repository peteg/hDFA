-- | graphviz DOT format operations.
--
-- Support here is rudimentary. It is probably better to build it on
-- top of one of the existing libraries on Hackage.
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
     throwErrnoPathIfMinus1_ "DOT.writeToFile" fname $
       withCString fname (writeDotToFile' dfa labelFunPtr)
  where
    f c = castCharToCChar (if c == '\n' then ' ' else c)
    labelFn' l buf =
      pokeArray0 (castCharToCChar '\0') buf (map f (take 200 (labelFn l))) -- FIXME constant, char casts

foreign import ccall "wrapper"
         mkLabelFunPtr :: (Label -> Ptr CChar -> IO ()) -> IO (FunPtr (Label -> Ptr CChar -> IO ()))

-- Note this can call back into Haskell land.
foreign import ccall safe "dfa.h DFA_writeDotToFile"
         writeDotToFile' :: DFA -> FunPtr (Label -> Ptr CChar -> IO ()) -> CString -> IO CInt
