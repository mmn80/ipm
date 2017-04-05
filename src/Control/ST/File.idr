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
  File : (mode : Mode) -> Type
  fileOpen  : String -> (mode : Mode) ->
              ST m (Either FileError Var) [addIfRight (File mode)]
  fileClose : (f : Var) ->
              ST m () [remove f (File mode)]
  fileSize  : (f : Var) ->
              ST m (Either FileError Int) [f ::: File mode]
  fileEOF   : (f : Var) ->
              ST m (Either FileError Bool) [f ::: File mode]
  fileRead  : (f : Var) -> (len : Int) -> {auto pf : isModeReadable mode = True} ->
              ST m (Either FileError String) [f ::: File mode]
  fileWrite : (f : Var) -> (str : String) -> {auto pf : isModeWriteable mode = True} ->
              ST m (Either FileError ()) [f ::: File mode]

-- Implementation for IO

data FileHandle : (hnd : Type) -> (mode : Mode) -> Type where
  MkFile : hnd -> FileHandle hnd mode

FileIO IO where
  File mode = State (FileHandle Prelude.File.File mode)

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
              ST m (Either FileError ())
              [f ::: (File {m=m} Read), sb ::: StrBuffer {m=m}]
  readFile' f max sb = with ST do
    Right x <- call $ fileEOF f | Left e => pure (Left e)
    if not x && max > 0
      then do Right l <- call $ fileRead f 1024000 | Left e => pure (Left e)
              call $ addToStringBuffer sb l
              assert_total $ readFile' f (max - 1024000) sb
      else pure (Right ())
