module Control.ST.Error

import public Data.List
import Control.ST

%access public export
%default total

data SomeError : (es : List Type) -> Type where
  SomeErr : (err : e) -> SomeError (e::es)
  Skip    : (rs : SomeError es) -> SomeError (e::es)

data Result : (es : List Type) -> (r : Type) -> Type where
  Ok  : (res : r) -> Result es r
  Err : (err : SomeError es) -> Result es r

Functor (Result es) where
  map f (Ok  res) = Ok (f res)
  map f (Err err) = Err err

result : (ek : Lazy (SomeError es -> a)) -> (rk : Lazy (r -> a)) -> Result es r -> a
result ek rk (Ok  res) = (Force rk) res
result ek rk (Err err) = (Force ek) err

%error_reduce
addIfOk : Type -> Action (Result es Var)
addIfOk ty = Add (result (const []) (\var => [var ::: ty]))

errCast : (err : SomeError [e]) -> (pf : Elem e es) -> SomeError es
errCast (SomeErr err) Here = SomeErr err
errCast err (There later) = Skip (errCast err later)

%inline
err : (err : SomeError [e]) -> {auto pf : Elem e es} ->
      STrans m (Result es r) (out_fn $ Err $ errCast err pf) out_fn
err {pf} er = pure (Err $ errCast er pf)

%inline
serr : (err : e) -> Result [e] r
serr err = Err (SomeErr err)
