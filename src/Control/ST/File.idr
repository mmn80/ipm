module Control.ST.File

import Control.ST
import Control.ST.StringBuffer

%access public export

isModeReadable : Mode -> Bool
isModeReadable Append        = False
isModeReadable WriteTruncate = False
isModeReadable _             = True

isModeWriteable : Mode -> Bool
isModeWriteable Read = False
isModeWriteable _    = True

interface FileIO (m : Type -> Type) where
  File : Dummy m -> (mode : Mode) -> Type
  fileOpen  : String -> (mode : Mode) ->
              ST m (Either FileError Var) [addIfRight (File MkDummy mode)]
  fileClose : (file : Var) -> ST m () [remove file (File MkDummy mode)]
  fileSize  : (file : Var) -> ST m (Either FileError Int) [file ::: File MkDummy mode]
  fileEOF   : (file : Var) -> ST m (Either FileError Bool) [file ::: File MkDummy mode]
  fileRead  : (file : Var) -> (len : Int) -> {auto pf : isModeReadable mode = True} ->
              ST m (Either FileError String) [file ::: File MkDummy mode]
  fileWrite : (file : Var) -> (str : String) -> {auto pf : isModeWriteable mode = True} ->
              ST m (Either FileError ()) [file ::: File MkDummy mode]

-- Implementation for IO

data FileHandle : (hnd : Type) -> (mode : Mode) -> Type where
  MkFile : hnd -> FileHandle hnd mode

FileIO IO where
  File _ mode = State (FileHandle Prelude.File.File mode)

  fileOpen path mode = do Right h <- lift $ openFile path mode
                                  | Left err => pure (Left err)
                          var <- new $ MkFile h
                          pure (Right var)

  fileClose f = do MkFile h <- read f
                   lift $ closeFile h
                   delete f

  fileSize f = do MkFile h <- read f
                  Right sz <- lift $ fileSize h | Left err => pure (Left err)
                  pure (Right sz)

  fileEOF f = do MkFile h <- read f
                 pure $ Right !(lift $ fEOF h)

  fileRead f len = do MkFile h <- read f
                      Right str <- lift $ fGetChars h len
                                | Left err => pure (Left err)
                      pure (Right str)

  fileWrite f str = do MkFile h <- read f
                       Right () <- lift $ fPutStr h str
                                | Left err => pure (Left err)
                       pure (Right ())

R : Type
R = State $ FileHandle File Read

W : Type
W = State $ FileHandle File WriteTruncate

A : Type
A = State $ FileHandle File Append

RW : Type
RW = State $ FileHandle File ReadWrite

RWPlus : Type
RWPlus = State $ FileHandle File ReadWriteTruncate

APlus : Type
APlus = State $ FileHandle File ReadAppend

readFile : (FileIO m, StringBufferIO m) => (path : String) ->
           ST m (Either FileError String) []
readFile path = with ST do
  Right f <- call $ fileOpen path Read | Left e => pure (Left e)
  Right max <- call $ fileSize f | Left e => do fileClose f; pure (Left e)
  sb <- call $ newStringBuffer (max + 1)
  r <- readFile' f max sb
  str <- call $ getStringFromBuffer sb
  call $ fileClose f
  pure $ map (const str) r
 where
  readFile' : (FileIO m, StringBufferIO m) => (f : Var) -> Int -> (sb : Var) ->
              ST m (Either FileError ()) [f ::: (File (the (Dummy m) MkDummy) Read)
                                       , sb ::: StrBuffer (the (Dummy m) MkDummy)]
  readFile' f max sb = with ST do
    Right x <- call $ fileEOF f | Left e => pure (Left e)
    if not x && max > 0
      then do Right l <- call $ fileRead f 1024000 | Left e => pure (Left e)
              call $ addToStringBuffer sb l
              assert_total $ readFile' f (max - 1024000) sb
      else pure (Right ())
