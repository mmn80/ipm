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

testRec : Record [("age"  , Int),
                  ("name" , String),
                  ("parts", Record [("ass", String), ("head", Int)])]
testRec = [(Fld "age"   _, 666),
           (Fld "name"  _, "Bender Bending Rodriguez"),
           (Fld "parts" _, [(Fld "ass"  _, "shiny metal"),
                            (Fld "head" _, 42)])]

testFn : Record [("age", t_age),
                 ("name", t_name),
                 ("parts", Record (("ass", t_ass) :: parts))] ->
         Record [("result", t_name)]
testFn [(Fld "age" _, age),
        (Fld "name"  _, name),
        (Fld "parts" _, (Fld "ass" _, ass) :: parts)
       ]
     = [(Fld "result" _, name)]

testApp : Record [("result", String)]
testApp = testFn testRec
