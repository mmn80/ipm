module Ipm.Record

import Data.Vect

%access public export
%default total

Name : Type
Name = String

data Field : Name -> Type -> Type where
  Fld : (n : Name) -> (t : Type) -> Field n t

FieldTy : Type
FieldTy = (Name, Type)

namespace Record
  data Record : (fs : List FieldTy) -> Type where
    Nil : Record []
    (::) : (Field n t, t) -> Record fs -> Record ((n, t) :: fs)

fieldMerge : List FieldTy -> List FieldTy -> List FieldTy
fieldMerge xs ys = go xs (sortBy (\(n, _), (n', _) => compare n n') ys)
  where
    go : List FieldTy -> List FieldTy -> List FieldTy
    go [] fs = fs
    go fs [] = fs
    go ((n, t) :: fs) ((n', t') :: fs') =
      if n == n' then (n, t') :: go fs fs'
      else if n < n' then (n, t) :: (n', t') :: go fs fs'
      else (n', t') :: go fs ((n, t) :: fs')

merge : Record fs -> Record fs' -> Record (fieldMerge fs fs')
merge r r' = ?rhs

testRec : (flds : List FieldTy ** Record flds)
testRec = (_ ** [(Fld "age"   _, 666),
                 (Fld "name"  _, "Bender"),
                 (Fld "parts" _, [(Fld "head" _, 5),
                                  (Fld "ass"  _, "shiny metal")])])

testFn : (flds : List FieldTy ** Record flds) -> (flds' : List FieldTy ** Record flds')
testFn (_ ** [(Fld "age" _, age), (Fld "name"  _, name),
              (Fld "parts" _, (Fld "head" _, head) (Record.::) parts)
             ])
     = (_ ** [(Fld "result" _, name)])
testFn _ = (_ ** [(Fld "error" _, "Type Error!")])
