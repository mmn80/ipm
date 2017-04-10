module Control.ST.File

import Control.ST
import Control.ST.ImplicitCall
import Control.ST.Error
import Control.ST.StringBuffer

%access public export
%default total

-- API constraints functions

isModeReadable : Mode -> Bool
isModeReadable Append        = False
isModeReadable WriteTruncate = False
isModeReadable _             = True

isModeWriteable : Mode -> Bool
isModeWriteable Read = False
isModeWriteable _    = True

-- API

namespace FileIO
  Res : Type -> Type
  Res r = Result [FileError] r

interface FileIO (m : Type -> Type) where
  File : (mode : Mode) -> Type

  fileOpen  : String -> (mode : Mode) ->
              ST m (Res Var) [addIfOk (File mode)]
  fileClose : (f : Var) ->
              ST m () [remove f (File mode)]
  fileSize  : (f : Var) ->
              ST m (Res Int) [f ::: File mode]
  fileEOF   : (f : Var) ->
              ST m (Res Bool) [f ::: File mode]
  fileRead  : (f : Var) -> (len : Int) ->
              {auto pf : isModeReadable mode = True} ->
              ST m (Res String) [f ::: File mode]
  fileWrite : (f : Var) -> (str : String) ->
              {auto pf : isModeWriteable mode = True} ->
              ST m (Res ()) [f ::: File mode]

-- FileIO implementation for IO

data FileHandle : (hnd : Type) -> (mode : Mode) -> Type where
  MkFile : hnd -> FileHandle hnd mode

FileIO IO where
  File mode = State (FileHandle Prelude.File.File mode)

  fileOpen path mode = do Right h <- lift $ openFile path mode
                                  | Left e => resErr e
                          var <- new $ MkFile h
                          pure (Ok var)

  fileClose f = do MkFile h <- read f
                   lift $ closeFile h
                   delete f

  fileSize f = do MkFile h <- read f
                  Right sz <- lift $ fileSize h
                           | Left e => resErr e
                  pure (Ok sz)

  fileEOF f = do MkFile h <- read f
                 pure $ Ok !(lift $ fEOF h)

  fileRead f len = do MkFile h <- read f
                      Right str <- lift $ fGetChars h len
                                | Left e => resErr e
                      pure (Ok str)

  fileWrite f str = do MkFile h <- read f
                       Right () <- lift $ fPutStr h str
                                | Left e => resErr e
                       pure (Ok ())

-- Example generic function

readFile : (FileIO m, StringBufferIO m) => (path : String) ->
           ST m (Result [FileError] String) []
readFile path = with ST do
  Ok f <- fileOpen path Read | Err e => err1 e
  Ok sz <- fileSize f        | Err e => do fileClose f; err1 e
  sb <- newStringBuffer (sz + 1)
  r <- readFile' f sz sb
  str <- getStringFromBuffer sb
  fileClose f
  pure $ const str <$> r
 where
  readFile' : (FileIO m, StringBufferIO m) => (f : Var) -> Int -> (sb : Var) ->
              ST m (Result [FileError] ())
              [f ::: File {m=m} Read, sb ::: StrBuffer {m=m}]
  readFile' f sz sb = with ST do
    Ok x <- fileEOF f | Err e => err e
    if not x && sz > 0
      then do Ok l <- fileRead f 1024000 | Err e => err e
              addToStringBuffer sb l
              assert_total $ readFile' f (sz - 1024000) sb
      else pure $ Ok ()
