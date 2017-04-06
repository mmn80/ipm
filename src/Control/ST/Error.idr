module Control.ST.Error

import Control.ST

%access public export
%default total

ErrorTypeCode : Type
ErrorTypeCode = Int

ErrorCode : Type
ErrorCode = Int

interface Error (e : Type) where
  errString : e -> String
  errElim : e -> (ErrorTypeCode -> ErrorCode -> r) -> r

data SomeError : Type where
  MkErr : Error e => e -> SomeError

%inline
errToString : SomeError -> String
errToString (MkErr e) = errString e

%inline
caseErr : SomeError -> (ErrorTypeCode -> ErrorCode -> r) -> r
caseErr (MkErr e) = errElim e

data Result r = Ok r | Err SomeError

Functor Result where
  map f (Ok r)  = Ok (f r)
  map f (Err e) = Err e

result : (err : Lazy (SomeError -> a)) -> (ok : Lazy (r -> a)) -> (r : Result r) -> a
result err ok (Err e) = (Force err) e
result err ok (Ok r)  = (Force ok) r

%error_reduce
addIfOk : Type -> Action (Result Var)
addIfOk ty = Add (result (const []) (\var => [var ::: ty]))

%inline
error : Error err => (e : err) -> STrans m (Result r) (out_fn (Err $ MkErr e)) out_fn
error e = pure (Err $ MkErr e)

%inline
err : (e : SomeError) -> STrans m (Result r) (out_fn (Err e)) out_fn
err e = pure (Err e)
