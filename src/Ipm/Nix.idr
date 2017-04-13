module Ipm.Nix

%default total
%access public export

Name : Type
Name = String

Path : Type
Path = String

data NixType = NixString | NixInt | NixPath | NixBool | NixList | NixSet | NixRef
             | NixFun NixType | NixDerivation

mutual
  data Pattern : Type where
    PatName : Name -> (def : Maybe (Expr t)) -> Pattern
    PatSet : List Pattern -> (allowExtra : Bool) -> Pattern

  namespace ExprList
    data ExprList : Type where
      Nil : ExprList
      (::) : Expr t -> ExprList -> ExprList

  namespace AttrList
    data AttrList : Type where
      Nil : AttrList
      (::) : (Name, Expr t) -> AttrList -> AttrList

  data Expr : NixType -> Type where
    EString : String -> Expr NixString
    EInt : Int -> Expr NixInt
    EPath : String -> Expr NixPath
    EBool : Bool -> Expr NixBool
    ENull : Expr t
    EList : ExprList -> Expr NixList
    ESet : (rec : Bool) -> (attrs : AttrList) -> Expr NixSet
    ERef : (set : Maybe Name) -> (attr : Name) -> Expr NixRef
    EFun : (args : Pattern) -> (body : Expr t) -> Expr (NixFun t)
    EIf : (cond : Expr NixBool) -> (tr : Expr NixBool) -> (fl : Expr t) -> Expr t
    EAssert : (cond : Expr NixBool) -> (ok : Expr t) -> Expr t
    EWith : (set : Expr NixSet) -> (expr : Expr t) -> Expr t
    EComment : (comment : String) -> (expr : Expr t) -> Expr t
    EOpApp : (fun : Either Name (Expr (NixFun t))) -> (arg : Expr a) -> Expr t
    EOpDot : (set : Expr NixSet) -> (attrPath : List Name) -> (def : Expr t) -> Expr t
    EOpAttrExists : (set : Expr NixSet) -> (attrPath : List Name) -> Expr NixBool
    EOpListConcat : (lst1 : Expr NixList) -> (lst2 : Expr NixList) -> Expr NixList
    EOpStrConcat : (str1 : Expr NixString) -> (str2 : Expr NixString) -> Expr NixString
    EOpPathConcat : (p1 : Expr NixPath) -> (p2 : Expr NixPath) -> Expr NixPath
    EOpBoolNeg : (bool : Expr NixBool) -> Expr NixBool
    EOpSetMerge : (set1 : Expr NixSet) -> (set2 : Expr NixSet) -> Expr NixSet
    EOpEq : (e1 : Expr t) -> (e2 : Expr t) -> Expr NixBool
    EOpNEq : (e1 : Expr t) -> (e2 : Expr t) -> Expr NixBool
    EOpAnd : (bool1 : Expr NixBool) -> (bool2 : Expr NixBool) -> Expr NixBool
    EOpOr : (bool1 : Expr NixBool) -> (bool2 : Expr NixBool) -> Expr NixBool
    EOpImplies : (bool1 : Expr NixBool) -> (bool2 : Expr NixBool) -> Expr NixBool
    EDerivation : (system : String) ->
                  (name : String) ->
                  (builder : Either Path (Expr NixDerivation)) ->
                  (args : List String) ->
                  (outputs : List String) ->
                  (attrs : Expr NixSet) ->
                  Expr NixDerivation

 runNix : Expr NixDerivation -> IO ()
 runNix expr = putStrLn "Nix"
