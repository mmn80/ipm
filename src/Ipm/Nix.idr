module Ipm.Nix

import Data.Fin
import Data.Vect
import Data.HVect

%default total
%access public export

Name : Type
Name = String

Path : Type
Path = String

mutual
  NixVar : Type
  NixVar = (Name, NixType)

  data NixType = TString | TInt | TPath | TBool
               | TFun NixVar NixType
               | TList (Vect n NixType)
               | TSet (Vect n NixVar)
               | TDerivation (Vect n NixVar)

dropElem : (xs : Vect (S n) a) -> (p : Elem x xs) -> Vect n a
dropElem (x :: ys) Here = ys
dropElem {n=S k} (x :: ys) (There p) = x :: dropElem ys p

data SubVect : Vect n t -> Vect m t -> Type where
  SvNil  : SubVect [] []
  SvSkip : SubVect xs ys -> SubVect xs (y :: ys)
  SvIn   : (el : Elem x ys) -> SubVect xs (dropElem ys el) -> SubVect (x :: xs) ys

data SubType : NixType -> NixType -> Type where
  SubEq : SubType t t
  SubTList : SubVect ts ts' -> SubType (TList ts) (TList ts')
  SubTSet : SubVect vs vs' -> SubType (TSet vs) (TSet vs')
  SubTFun : n = n' -> SubType a' a -> SubType t t' ->
            SubType (TFun (n, a) t) (TFun (n', a') t')

mutual
  using (G : Vect n NixVar)
    data HasVar : (i : Fin n) -> Vect n NixVar -> NixVar -> Type where
      Stop : HasVar FZ (v :: G) v
      Pop  : HasVar k G v -> HasVar (FS k) (u :: G) v

    namespace ExprList
      data ExprList : Vect n NixType -> Type where
        Nil : ExprList []
        (::) : Expr G t -> ExprList ts -> ExprList (t::ts)

    namespace ExprSet 
      data ExprSet : Vect n NixVar -> Vect m NixVar -> Type where
        Nil : ExprSet G []
        (::) : (fld : (Name, Expr G t)) -> ExprSet G ts ->
               ExprSet ((fst fld, t)::G) ((fst fld, t)::ts)

    data Pattern : NixVar -> Type where
      PatVar : (v : NixVar) -> (def : Maybe (Expr G (snd v))) -> Pattern v

    data Expr : Vect n NixVar -> NixType -> Type where
      EAssert : Expr G TBool -> Expr G t -> Expr G t
      EComment : String -> Expr G t -> Expr G t

      EString : String -> Expr G TString
      EInt : Int -> Expr G TInt
      EPath : String -> Expr G TPath
      EBool : Bool -> Expr G TBool
      EList : ExprList ts -> Expr G (TList ts)

      EVar : {-(set : Maybe Name) -> -}HasVar i G v -> Expr G (snd v)
      EApp : Expr G (TFun v t) -> Expr G u -> {auto p : SubType (snd v) u} -> Expr G t
      EFun : Pattern a -> Expr (a::G) t -> Expr G (TFun a t)
      ELet : (v : Name) -> Expr G u -> Expr ((v, u)::G) t -> Expr G t

      ESet : {-(rec : Bool) -> -}ExprSet (vs++G) vs -> Expr G (TSet vs)
      EWith : Expr G (TSet vs) -> Expr (vs++G) t -> Expr G t
      EOpDot : Expr G (TSet vs) -> (atp : Vect m Name) -> (def : Expr G t) -> Expr G t
      EOpAttrExists : Expr G (TSet vs) -> (atp : Vect m Name) -> Expr G TBool

      EIf : Expr G TBool -> Lazy (Expr G t) -> Lazy (Expr G t) -> Expr G t

      EOpListConcat : Expr G (TList vs) -> Expr G (TList vs') ->
                      Expr G (TList (vs++vs'))
      EOpStrConcat : Expr G TString -> Expr G TString -> Expr G TString
      EOpPathConcat : Expr G TPath -> Expr G TPath -> Expr G TPath
      EOpBoolNeg : Expr G TBool -> Expr G TBool
      EOpSetMerge : Expr G (TSet vs) -> Expr G (TSet vs') -> Expr G (TSet (vs++vs'))
      EOpEq : Expr G t -> Expr G t -> Expr G TBool
      EOpNEq : Expr G t -> Expr G t -> Expr G TBool
      EOpAnd : Expr G TBool -> Expr G TBool -> Expr G TBool
      EOpOr : Expr G TBool -> Expr G TBool -> Expr G TBool
      EOpImplies : Expr G TBool -> Expr G TBool -> Expr G TBool

      EDerivation : (system : String) ->
                    (name : String) ->
                    (builder : Either Path (Expr G (TDerivation vs))) ->
                    (args : List String) ->
                    (outputs : List String) ->
                    (attrs : Expr G (TSet vs)) ->
                    Expr G (TDerivation vs)

record Derivation (vs : Vect n Type) where
  constructor MkDerivation
  system : String
  name : String
  builder : Either Path (Derivation vs)
  args : List String
  outputs : List String
  attrs : HVect vs

mutual
  nixVarsToIdris : (vs : Vect n NixVar) -> Vect n Type
  nixVarsToIdris vs = assert_total $ (\(n, t) => (Name, NixTypeToIdris t)) <$> vs

  NixTypeToIdris : NixType -> Type
  NixTypeToIdris TString = String
  NixTypeToIdris TInt = Int
  NixTypeToIdris TPath = Path
  NixTypeToIdris TBool = Bool
  NixTypeToIdris (TFun (n, a) t) = NixTypeToIdris a -> NixTypeToIdris t
  NixTypeToIdris (TList ts) = HVect (assert_total $ NixTypeToIdris <$> ts)
  NixTypeToIdris (TSet vs) = HVect (nixVarsToIdris vs)
  NixTypeToIdris (TDerivation vs) = Derivation (nixVarsToIdris vs)

using (G : Vect n NixVar)
  data Env : Vect n NixVar -> Type where
    Nil  : Env Nil
    (::) : (p : (Name, NixTypeToIdris t)) -> Env G -> Env ((fst p, t) :: G)

  lookup : HasVar i G (_, t) -> Env G -> (Name, NixTypeToIdris t)
  lookup Stop    (x :: xs) = x
  lookup (Pop k) (x :: xs) = lookup k xs

  interp : Env G -> Expr G t -> NixTypeToIdris t



