module Control.ST.StringBuffer

import Control.ST

%access public export

interface StringBufferIO (m : Type -> Type) where
  StrBuffer : Type
  newStringBuffer : (len : Int) -> ST m Var [add StrBuffer]
  addToStringBuffer : (sb : Var) -> String -> ST m () [sb ::: StrBuffer]
  getStringFromBuffer : (sb : Var) -> ST m String [remove sb StrBuffer]

StringBufferIO IO where
  StrBuffer = State StringBuffer

  newStringBuffer len = do sb <- lift $ newStringBuffer len
                           new sb

  addToStringBuffer var str = do sb <- read var
                                 lift $ addToStringBuffer sb str

  getStringFromBuffer var = do sb <- read var
                               str <- lift $ getStringFromBuffer sb 
                               delete var
                               pure str

