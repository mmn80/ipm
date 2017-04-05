module Control.ST.File

import Control.ST
import Control.ST.StringBuffer

%access public export
%default total

-- A nicer type then Either

data Result : (res : Type) -> Type where
  Ok  : (resOk  : res)       -> Result res
  Err : (resErr : FileError) -> Result res

Functor Result where
  map f (Ok r)  = Ok (f r)
  map f (Err e) = Err e

result : (err : Lazy (FileError -> b)) -> (ok : Lazy (a -> b)) -> (r : Result a) -> b
result err ok (Err x) = (Force err) x
result err ok (Ok x)  = (Force ok) x

%error_reduce
addIfOk : Type -> Action (Result Var)
addIfOk ty = Add (result (const []) (\var => [var ::: ty]))

-- API constraints functions

isModeReadable : Mode -> Bool
isModeReadable Append        = False
isModeReadable WriteTruncate = False
isModeReadable _             = True

isModeWriteable : Mode -> Bool
isModeWriteable Read = False
isModeWriteable _    = True

-- API

interface FileIO (m : Type -> Type) where
  File      : (mode : Mode) -> Type
  fileOpen  : String -> (mode : Mode) ->
              ST m (Result Var) [addIfOk (File mode)]
  fileClose : (f : Var) ->
              ST m () [remove f (File mode)]
  fileSize  : (f : Var) ->
              ST m (Result Int) [f ::: File mode]
  fileEOF   : (f : Var) ->
              ST m (Result Bool) [f ::: File mode]
  fileRead  : (f : Var) -> (len : Int) -> {auto pf : isModeReadable mode = True} ->
              ST m (Result String) [f ::: File mode]
  fileWrite : (f : Var) -> (str : String) -> {auto pf : isModeWriteable mode = True} ->
              ST m (Result ()) [f ::: File mode]

-- Implementation for IO

data FileHandle : (hnd : Type) -> (mode : Mode) -> Type where
  MkFile : hnd -> FileHandle hnd mode

FileIO IO where
  File mode = State (FileHandle Prelude.File.File mode)

  fileOpen path mode = do Right h <- lift $ openFile path mode
                                  | Left e => pure (Err e)
                          var <- new $ MkFile h
                          pure (Ok var)

  fileClose f = do MkFile h <- read f
                   lift $ closeFile h
                   delete f

  fileSize f = do MkFile h <- read f
                  Right sz <- lift $ fileSize h | Left e => pure (Err e)
                  pure (Ok sz)

  fileEOF f = do MkFile h <- read f
                 pure $ Ok !(lift $ fEOF h)

  fileRead f len = do MkFile h <- read f
                      Right str <- lift $ fGetChars h len
                                | Left e => pure (Err e)
                      pure (Ok str)

  fileWrite f str = do MkFile h <- read f
                       Right () <- lift $ fPutStr h str
                                | Left e => pure (Err e)
                       pure (Ok ())

-- Example generic function

readFile : (FileIO m, StringBufferIO m) => (path : String) -> ST m (Result String) []
readFile path = with ST do
  Ok f <- call $ fileOpen path Read | Err e => pure (Err e)
  Ok sz <- call $ fileSize f | Err e => do fileClose f; pure (Err e)
  sb <- call $ newStringBuffer (sz + 1)
  r <- readFile' f sz sb
  str <- call $ getStringFromBuffer sb
  call $ fileClose f
  pure $ map (const str) r
 where
  readFile' : (FileIO m, StringBufferIO m) => (f : Var) -> Int -> (sb : Var) ->
              ST m (Result ()) [f ::: (File {m=m} Read), sb ::: StrBuffer {m=m}]
  readFile' f sz sb = with ST do
    Ok x <- call $ fileEOF f | Err e => pure (Err e)
    if not x && sz > 0
      then do Ok l <- call $ fileRead f 1024000 | Err e => pure (Err e)
              call $ addToStringBuffer sb l
              assert_total $ readFile' f (sz - 1024000) sb
      else pure (Ok ())
