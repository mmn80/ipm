module Ipm.Interfaces

--import Control.ST
--import Control.ST.File

%language ElabReflection

interface Script (a : Type) (b : Type) (c : Type) | a, b where
  merge : a -> b -> c

autoScript : (a : TTName) -> (b : TTName) -> (c : TTName) -> Elab ()
autoScript a b c = do
  as <- scrapADT a
  bs <- scrapADT b
  cs <- scrapADT c
  fail $ [NamePart a, TextPart " := "] ++ concatMap
       (\(cn, cargs, craw) => [SubReport ([NamePart cn, TextPart " : "] ++ concatMap
         (\fa => [NamePart (name fa), TextPart " : ",
                 RawPart (type fa), TextPart " -> "]) cargs ++
                 [RawPart craw])]) as
  --let implName = 
  --addImplementation `Script implName
  --fill `(() : ())
  --solve
 where
  err : TTName -> Elab ()
  err n = fail [NamePart n, TextPart "is not a type constructor."]

  scrapADT : (dn : TTName) -> Elab (List (TTName, List FunArg, Raw))
  scrapADT dn = do
    MkDatatype n ar r cons <- lookupDatatypeExact dn
    pure $ map (\(cn, cargs, craw) => (cn, mapMaybe
                 (\carg => case carg of
                            CtorField funarg => Just funarg
                            _ => Nothing) cargs, craw)) cons


data Ins : Type where
  MkIns : (in1 : String) -> Ins

data A : Type where
  MkA : (astr : const String ()) -> (ain : Ins) -> A

data B : Type where
  MkB : (bstr : String) -> (ain : Ins) -> B

data C : Type where
  MkC : (astr : String) -> (bstr : String) -> (ain : Ins) -> C

--deriveScript : ()
--deriveScript = %runElab (autoScript `{{A}} `{{B}} `{{C}})

--Script A B C where
--  merge (MkA astr aint) (MkB bstr aint') = MkC astr bstr aint'
