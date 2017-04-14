module Ipm.Nix

%default total
%access public export

Name : Type
Name = String

Path : Type
Path = String

data NixType = TString | TInt | TPath | TBool | TRef | TDerivation | TAny
             | TList (List NixType) | TSet (List NixType)
             | TFun NixType

mutual
  namespace ExprList
    data ExprList : List NixType -> Type where
      Nil : ExprList []
      (::) : Expr t -> ExprList ts -> ExprList (t::ts)

  namespace AttrList
    data AttrList : List NixType -> Type where
      Nil : AttrList []
      (::) : (Name, Expr t) -> AttrList ts -> AttrList (t::ts)

  data Pattern : Type where
    PatName : Name -> (def : Maybe (Expr t)) -> Pattern
    PatSet : List Pattern -> (allowExtra : Bool) -> Pattern

  data Expr : NixType -> Type where
    EImport : (path : Path) -> Expr TAny
    EAssert : (cond : Expr TBool) -> (ok : Expr t) -> Expr t
    EComment : (comment : String) -> (expr : Expr t) -> Expr t

    EString : String -> Expr TString
    EInt : Int -> Expr TInt
    EPath : String -> Expr TPath
    EBool : Bool -> Expr TBool
    ENull : Expr TAny
    EList : ExprList ts -> Expr (TList ts)

    ERef : (set : Maybe Name) -> (attr : Name) -> Expr TRef
    EFun : (args : Pattern) -> (body : Expr t) -> Expr (TFun t)
    ELet : (var : Name) -> (expr : Expr t) -> (body : Expr b) -> Expr b
    ESet : (rec : Bool) -> (attrs : AttrList ts) -> Expr (TSet ts)
    EWith : (set : Expr (TSet ts)) -> (expr : Expr t) -> Expr t
    EOpDot : (set : Expr (TSet ts)) -> (atp : List Name) -> (def : Expr t) -> Expr t
    EOpAttrExists : (set : Expr (TSet ts)) -> (atp : List Name) -> Expr TBool

    EIf : (cond : Expr TBool) -> (tr : Expr t) -> (fl : Expr t) -> Expr t
    EOpApp : (fun : Either Name (Expr (TFun t))) -> (arg : Expr a) -> Expr t
    EOpListConcat : (lst1 : Expr (TList ts)) -> (lst2 : Expr (TList ts')) ->
                    Expr (TList (ts++ts'))
    EOpStrConcat : (str1 : Expr TString) -> (str2 : Expr TString) -> Expr TString
    EOpPathConcat : (p1 : Expr TPath) -> (p2 : Expr TPath) -> Expr TPath
    EOpBoolNeg : (bool : Expr TBool) -> Expr TBool
    EOpSetMerge : (set1 : Expr (TSet ts)) -> (set2 : Expr (TSet ts')) ->
                  Expr (TSet (ts++ts'))
    EOpEq : (e1 : Expr t) -> (e2 : Expr t) -> Expr TBool
    EOpNEq : (e1 : Expr t) -> (e2 : Expr t) -> Expr TBool
    EOpAnd : (bool1 : Expr TBool) -> (bool2 : Expr TBool) -> Expr TBool
    EOpOr : (bool1 : Expr TBool) -> (bool2 : Expr TBool) -> Expr TBool
    EOpImplies : (bool1 : Expr TBool) -> (bool2 : Expr TBool) -> Expr TBool

    EDerivation : (system : String) ->
                  (name : String) ->
                  (builder : Either Path (Expr TDerivation)) ->
                  (args : List String) ->
                  (outputs : List String) ->
                  (attrs : Expr (TSet ts)) ->
                  Expr TDerivation

mutual
  Set : Type
  Set = List (String, Variant)

  record Derivation where
    constructor MkDerivation
    system : String
    name : String
    builder : Either Path Derivation
    args : List String
    outputs : List String
    attrs : Set

  data Variant = VStr String | VInt Int | VPath Path | VBool Bool
               | VList (List Variant) | VSet Set | VRef Variant | VNull
               | VFun (Variant -> Variant)
               | VDerivation Derivation

namespace HList
  data HList : List Type -> Type where
    Nil : HList []
    (::) : (x : t) -> HList ts -> HList (t::ts)

NixTypeToIdris : NixType -> Type
NixTypeToIdris TAny = Variant
NixTypeToIdris TString = String
NixTypeToIdris TInt = Int
NixTypeToIdris TPath = Path
NixTypeToIdris TBool = Bool
NixTypeToIdris (TList ts) = HList (assert_total $ NixTypeToIdris <$> ts)
NixTypeToIdris (TSet ts) = HList (assert_total $ (\t => (Name, NixTypeToIdris t)) <$> ts)
NixTypeToIdris TRef = Variant
NixTypeToIdris (TFun r) = Variant -> NixTypeToIdris r
NixTypeToIdris TDerivation = Derivation

mutual
  evalList : ExprList ts -> HList (NixTypeToIdris <$> ts)
  evalList [] = []
  evalList (x :: xs) = evalExpr x :: evalList xs

  evalExpr : Expr t -> NixTypeToIdris t
  evalExpr (EString x) = x
  evalExpr (EInt x) = x
  evalExpr (EPath x) = x
  evalExpr (EBool x) = x
  evalExpr ENull = VNull
  evalExpr (EList lst) = evalList lst
  evalExpr (ESet rec attrs) = ?r_8
  evalExpr (ERef set attr) = ?r_9
  evalExpr (ELet var expr body) = ?r_10
  evalExpr (EFun args body) = ?r_11
  evalExpr (EIf cond tr fl) = if evalExpr cond then evalExpr tr else evalExpr fl
  evalExpr (EAssert cond ok) = ?r_13
  evalExpr (EWith set expr) = ?r_14
  evalExpr (EComment comment expr) = ?r_15
  evalExpr (EOpApp fun arg) = ?r_16
  evalExpr (EOpDot set attrPath def) = ?r_17
  evalExpr (EOpAttrExists set attrPath) = ?r_18
  evalExpr (EOpListConcat lst1 lst2) = ?r_19
  evalExpr (EOpStrConcat str1 str2) = ?r_20
  evalExpr (EOpPathConcat p1 p2) = ?r_21
  evalExpr (EOpBoolNeg bool) = ?r_22
  evalExpr (EOpSetMerge set1 set2) = ?r_23
  evalExpr (EOpEq e1 e2) = ?r_24
  evalExpr (EOpNEq e1 e2) = ?r_25
  evalExpr (EOpAnd bool1 bool2) = ?r_26
  evalExpr (EOpOr bool1 bool2) = ?r_27
  evalExpr (EOpImplies bool1 bool2) = ?r_28
  evalExpr (EDerivation system name builder args outputs attrs) = ?r_29
  evalExpr (EImport path) = VNull -- impossible

processImports : Expr t -> IO (Expr t)
processImports (EImport path) = pure ENull
processImports expr = pure expr

runNix : Expr TDerivation -> IO Derivation
runNix expr = do
  e <- processImports expr
  pure $ evalExpr e
