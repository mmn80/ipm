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
  SeSkip : (sl : SubList xs ys) -> SubList xs (y :: ys)
  SeIn   : (el : Elem x ys) -> (sl : SubList xs (dropElem ys el)) ->
           SubList (x :: xs) ys

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

-- Reducing verbosity when using error bubbling patterns like:
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

-- Handling errors

data ErrHandlers : (es : List Type) -> (r : Type) -> Type where
  Nil  : ErrHandlers [] r
  (::) : (fn : e -> r) -> ErrHandlers es r -> ErrHandlers (e::es) r

listDiff : (pf : SubList xs ys) -> List Type 
listDiff SeNil = []
listDiff (SeSkip sl) = listDiff sl
listDiff (SeIn {x} el sl) = x :: listDiff sl

subListEq : SubList xs xs
subListEq {xs = []}       = SeNil
subListEq {xs = (x::xs')} = SeIn Here (subListEq {xs=xs'})

errElim : (err : SomeError es) -> (fns : ErrHandlers hs r) -> (df : r) ->
          {pf : SubList hs es} -> Result (listDiff pf) r
--errElim (SomeErr err) (fn :: fns) = fn err
--errElim (Skip rs)     (fn :: fns) = errElim rs fns
errElim err [] df = Ok df
errElim (SomeErr err) fns df {pf=(SeSkip sl)} = Ok df
errElim (Skip rs) fns df {pf=(SeSkip sl)} = errElim rs fns df {pf=sl}
errElim (SomeErr err) (fn::fns) df {pf=(SeIn Here sl)} = Ok (fn err)
errElim (Skip rs) (fn::fns) df {pf=(SeIn Here sl)} =
  case errElim rs fns df {pf=sl} of
    Ok  res => Ok res
    Err err => Err $ errCast err (SeSkip subListEq)
errElim (SomeErr err) (fn::fns) df {pf=(SeIn (There later) sl)} =
  case errElim (SomeErr err) fns df {pf=sl} of
    Ok res   => Ok res
    Err err' => Err $ errCast err' (SeSkip subListEq)
errElim (Skip rs) fns df {pf=(SeIn (There later) sl)} = ?e2

catch : (err : SomeError es) -> (fns : ErrHandlers hs r) -> (df : r) ->
        {auto pf : SubList hs es} ->
        STrans m (Result (listDiff pf) r) (out_fn $ errElim err fns df) out_fn
catch err fns df = pure (errElim err fns df)
