module Ipm.Record

import Data.Vect

%access public export
%default total

Name : Type
Name = String

data Field : Name -> Type where
  Fld : (n : Name) -> Field n

FieldTy : Type
FieldTy = (Name, Type)

namespace Record
  data Record : (fs : List FieldTy) -> Type where
    Nil : Record []
    (::) : (Field n, t) -> Record fs -> Record ((n, t) :: fs)

  head : Record (f::fs) -> Record [f]
  head (x :: _) = [x]

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
testRec = [(Fld "age"  , 666),
           (Fld "name" , "Bender Bending Rodriguez"),
           (Fld "parts", [(Fld "ass" , "shiny metal"),
                          (Fld "head", 42)])]

testFn : Record (("age", t_age)
              :: ("name", t_name)
              :: ("parts", Record (("ass", t_ass) :: parts))
              :: other) ->
         Record (("result", t_name) :: parts)
testFn ((Fld "age"  , age)
     :: (Fld "name" , name)
     :: (Fld "parts", (Fld "ass", ass) :: parts)
     :: other)
     = (Fld "result", name) :: parts

testApp : Record [("result", String)]
testApp = head (testFn testRec)
