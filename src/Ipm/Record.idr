module Ipm.Record

import Data.Vect

%access public export
%default total
%language ElabReflection

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

name2Str : TTName -> Elab ()
name2Str name = do
  let n = case name of
            UN str => str
            _ => "WRONG"
  fill $ RConstant (Str n)
  solve

term    syntax {fld} ":." [ty]  = (%runElab (name2Str `{{fld}}), ty)
term    syntax {fld} ":=" [val] = (Fld (%runElab (name2Str `{{fld}})), val)
pattern syntax {fld} "~"  [val] = (Fld (%runElab (name2Str `{{fld}})), val)

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

bender : Record [age :. Int, name :. String, bend :. (Int -> Int),
                (parts :. Record [ass :. String, head :. Int])]
bender = [age := 666, name := "Bender Bending Rodriguez", bend := (+1),
         (parts := [ass := "shiny metal", head := 42])]

testFn : Record ((age :. t_age)
              :: (name :. t_name)
              :: (bend :. t_age -> t_age)
              :: (parts :. Record ((ass :. t_ass) :: otherParts))
              :: other) ->
         Record ((result :. t_name) :: (newAge :. t_age) :: otherParts)
testFn ((age ~ age)
     :: (name ~ name)
     :: (bend ~ bend)
     :: (parts ~ ((ass ~ ass) :: otherParts))
     :: other)
     = (result := name) :: (newAge := bend age) :: otherParts

testApp : Record [result :. String]
testApp = head (testFn bender)
