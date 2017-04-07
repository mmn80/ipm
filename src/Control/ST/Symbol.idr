module Control.ST.Symbol

import Control.ST

%access public export
%default total

export
data Sym : Type where
  TopSym : (idx : Int) -> Sym
  SubSym : (scope : Sym) -> (idx : Int) -> Sym

export
subSym : (scope : Sym) -> (idx : Int) -> Sym
subSym = SubSym

Eq Sym where
  (TopSym x)     == (TopSym y)     = x == y
  (SubSym s1 i1) == (SubSym s2 i2) = (s1 == s2) && (i1 == i2)
  _ == _ = False

symElim : Sym -> List (Sym, Lazy r) -> Lazy r -> r
symElim s lst def = case lookup s lst of
                         Just r  => r
                         Nothing => def

interface SymbolIO (m : Type -> Type) where
  SymTable   : Type
  symbolInit : ST m Var [add SymTable]
  symbolFree : (tbl : Var) -> ST m () [remove tbl SymTable]
  genSym     : (tbl : Var) -> ST m Sym [tbl ::: SymTable]

SymbolIO IO where
  SymTable = State Int

  symbolInit = new 0

  genSym tbl = do x <- read tbl
                  write tbl (x + 1)
                  pure (TopSym $ x + 1)

  symbolFree tbl = delete tbl
