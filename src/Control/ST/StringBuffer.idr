module Control.ST.StringBuffer

import Control.ST

%access public export

data Dummy : (Type -> Type) -> Type where
  MkDummy : Dummy m

interface StringBufferIO (m : Type -> Type) where
  StrBuffer : Dummy m -> Type
  newStringBuffer : (len : Int) -> ST m Var [add (StrBuffer MkDummy)]
  addToStringBuffer : (sb : Var) -> String -> ST m () [sb ::: StrBuffer MkDummy]
  getStringFromBuffer : (sb : Var) -> ST m String [remove sb (StrBuffer MkDummy)]

StringBufferIO IO where
  StrBuffer _ = State StringBuffer

  newStringBuffer len = do sb <- lift $ newStringBuffer len
                           new sb

  addToStringBuffer var str = do sb <- read var
                                 lift $ addToStringBuffer sb str

  getStringFromBuffer var = do sb <- read var
                               str <- lift $ getStringFromBuffer sb 
                               delete var
                               pure str

