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

%inline
resErr : (err : e) -> STrans m (Result [e] r) (out_fn $ Err $ SomeErr err) out_fn
resErr err = pure $ Err (SomeErr err)

-- Casting errors

data SubList : List Type -> List Type -> Type where
  SuNil  : SubList [] []
  SuSkip : (sl : SubList xs ys) -> SubList xs (y :: ys)
  SuIn   : (el : Elem x ys) -> (sl : SubList xs (dropElem ys el)) ->
           SubList (x :: xs) ys

errCast1 : (err : SomeError [e]) -> (pf : Elem e xs) -> SomeError xs
errCast1 (SomeErr err) Here          = SomeErr err
errCast1 err           (There later) = Skip (errCast1 err later)

errCast : (err : SomeError xs) -> (pf : SubList xs ys) -> SomeError ys
errCast se            (SuSkip pfs)             = Skip (errCast se pfs) 
errCast (SomeErr err) (SuIn Here pfi)          = SomeErr err
errCast (Skip rs)     (SuIn Here pfi)          = Skip (errCast rs pfi)
errCast (SomeErr err) (SuIn (There later) pfi) = Skip (errCast1 (SomeErr err) later)
errCast (Skip rs)     (SuIn (There later) pfi) = errCast' (errCast rs pfi)
  where
    errExt : SomeError (dropElem xs el) -> SomeError xs
    errExt {el = Here}          err           = Skip err 
    errExt {el = (There later)} (SomeErr err) = SomeErr err
    errExt {el = (There later)} (Skip rs)     = Skip (errExt rs) 

    errCast' : SomeError (y :: dropElem xs el) -> SomeError (y::xs)
    errCast' (SomeErr err) = SomeErr err
    errCast' (Skip rs)     = Skip (errExt rs)

%inline
err1 : (err : SomeError [e]) -> {auto pf : Elem e es} ->
      STrans m (Result es r) (out_fn $ Err $ errCast1 err pf) out_fn
err1 {pf} er = pure (Err $ errCast1 er pf)

%inline
err : (err : SomeError xs) -> {auto pf : SubList xs ys} ->
      STrans m (Result ys r) (out_fn $ Err $ errCast err pf) out_fn
err {pf} err = pure (Err $ errCast err pf)

-- Handling errors

namespace ErrHandlers
  data ErrHandlers : (es : List Type) -> (r : Type) -> Type where
    Nil  : ErrHandlers [] r
    (::) : (fn : e -> r) -> ErrHandlers es r -> ErrHandlers (e::es) r

listDiff : (pf : SubList xs ys) -> List Type 
listDiff SuNil           = []
listDiff (SuSkip {y} sl) = y :: listDiff sl
listDiff (SuIn el sl)    = listDiff sl

subListEq : SubList xs xs
subListEq {xs = []}       = SuNil
subListEq {xs = (x::xs')} = SuIn Here (subListEq {xs=xs'})

dropErr : (err : SomeError es) -> (pos : Elem e es) ->
          Maybe $ SomeError (dropElem es pos)
dropErr (SomeErr err) _         = Nothing
dropErr (Skip rs)  Here         = Just rs 
dropErr (Skip rs) (There later) = Skip <$> dropErr rs later

errElim : (err : SomeError es) -> (fns : ErrHandlers hs r) -> (df : r) ->
          (pf : SubList hs es) -> Result (listDiff pf) r
errElim err           []  df pf          = Ok df
errElim (SomeErr err) fns df (SuSkip sl) = Ok df
errElim (Skip rs)     fns df (SuSkip sl) =
  case errElim rs fns df sl of
    Ok  res  => Ok res
    Err err' => Err $ errCast err' (SuSkip subListEq)
errElim (SomeErr err) (fn::fns) df (SuIn Here sl) = Ok (fn err)
errElim (Skip rs)     (fn::fns) df (SuIn Here sl) = errElim rs fns df sl
errElim (SomeErr err) (fn::fns) df (SuIn (There later) sl) =
  errElim (SomeErr err) fns df sl
errElim (Skip rs) (fn::fns) df (SuIn (There later) sl) =
  case dropErr rs later of
    Just err => errElim (Skip err) fns df sl
    Nothing  => Ok df

catch : (err : SomeError es) -> (df : r) -> (fns : ErrHandlers hs r) ->
        {auto pf : SubList hs es} ->
        STrans m (Result (listDiff pf) r) (out_fn $ errElim err fns df pf) out_fn
catch err df fns {pf} = pure (errElim err fns df pf)
