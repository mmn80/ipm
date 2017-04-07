module Control.ST.Error

import Control.ST
import Control.ST.Symbol

%access public export
%default total

record Error where
  constructor MkError
  errCode : Sym
  errMsg  : String

data Result : (r : Type) -> Type where
  Ok  : (resOk : r) -> Result r
  Err : (resErr : Error) -> Result r

Functor Result where
  map f (Ok resOk)   = Ok (f resOk)
  map f (Err resErr) = Err resErr

result : (err : Lazy (Error -> a)) -> (ok : Lazy (r -> a)) -> (r : Result r) -> a
result err ok (Err e) = (Force err) e
result err ok (Ok r)  = (Force ok) r

%error_reduce
addIfOk : Type -> Action (Result Var)
addIfOk ty = Add (result (const []) (\var => [var ::: ty]))

%inline
err : (e : Error) -> STrans m (Result r) (out_fn (Err e)) out_fn
err e = pure (Err e)
