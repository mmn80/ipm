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

-- Casting errors

data SubList : List Type -> List Type -> Type where
  SeNil  : SubList [] []
  SeSkip : SubList xs ys -> SubList xs (y :: ys)
  SeIn   : (el : Elem x ys) -> SubList xs (dropElem ys el) -> SubList (x :: xs) ys

errCast1 : (err : SomeError [e]) -> (pf : Elem e xs) -> SomeError xs
errCast1 (SomeErr err) Here          = SomeErr err
errCast1 err           (There later) = Skip (errCast1 err later)

errCast : (err : SomeError xs) -> (pf : SubList xs ys) -> SomeError ys
errCast se            (SeSkip pfs)             = Skip (errCast se pfs) 
errCast (SomeErr err) (SeIn Here pfi)          = SomeErr err
errCast (Skip rs)     (SeIn Here pfi)          = Skip (errCast rs pfi)
errCast (SomeErr err) (SeIn (There later) pfi) = Skip (errCast1 (SomeErr err) later)
errCast (Skip rs)     (SeIn (There later) pfi) = errCast' (errCast rs pfi)
  where
    errExt : SomeError (dropElem xs el) -> SomeError xs
    errExt {el = Here}          err           = Skip err 
    errExt {el = (There later)} (SomeErr err) = SomeErr err
    errExt {el = (There later)} (Skip rs)     = Skip (errExt rs) 

    errCast' : SomeError (y :: dropElem xs el) -> SomeError (y::xs)
    errCast' (SomeErr err) = SomeErr err
    errCast' (Skip rs)     = Skip (errExt rs)

-- Utilities to reduce verbosity when using error bubbling patterns like:
-- Ok r <- apiCall args | Err e -> err e

%inline
err : (err : SomeError [e]) -> {auto pf : Elem e es} ->
      STrans m (Result es r) (out_fn $ Err $ errCast1 err pf) out_fn
err {pf} er = pure (Err $ errCast1 er pf)

%inline
err' : (err : SomeError xs) -> {auto pf : SubList xs ys} ->
      STrans m (Result ys r) (out_fn $ Err $ errCast err pf) out_fn
err' {pf} err = pure (Err $ errCast err pf)

%inline
serr : (err : e) -> Result [e] r
serr err = Err (SomeErr err)
