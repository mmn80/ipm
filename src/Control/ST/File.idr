module Control.ST.File

import Control.ST
import Control.ST.Symbol
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

FIO : Type
FIO = State Sym

interface SymbolIO m => FileIO (m : Type -> Type) where
  fileIOinit  : (tbl : Var) -> ST m Var [add FIO, tbl ::: SymTable {m=m}]
  fileIOclose : (s : Var) -> ST m () [remove s FIO]

  File : (mode : Mode) -> Type

  fileOpen  : (s : Var) -> String -> (mode : Mode) ->
              ST m (Result Var) [addIfOk (File mode), s ::: FIO]
  fileClose : (s : Var) -> (f : Var) ->
              ST m () [remove f (File mode), s ::: FIO]
  fileSize  : (s : Var) -> (f : Var) ->
              ST m (Result Int) [f ::: File mode, s ::: FIO]
  fileEOF   : (s : Var) -> (f : Var) ->
              ST m (Result Bool) [f ::: File mode, s ::: FIO]
  fileRead  : (s : Var) -> (f : Var) -> (len : Int) ->
              {auto pf : isModeReadable mode = True} ->
              ST m (Result String) [f ::: File mode, s ::: FIO]
  fileWrite : (s : Var) -> (f : Var) -> (str : String) ->
              {auto pf : isModeWriteable mode = True} ->
              ST m (Result ()) [f ::: File mode, s ::: FIO]

-- FileIO implementation for IO

errGenericFileError : Sym -> Sym
errGenericFileError sym = subSym sym 0

errFileReadError : Sym -> Sym
errFileReadError sym = subSym sym 1

errFileWriteError : Sym -> Sym
errFileWriteError sym = subSym sym 2

errFileNotFound : Sym -> Sym
errFileNotFound sym = subSym sym 3

errPermissionDenied : Sym -> Sym
errPermissionDenied sym = subSym sym 4

fileErrorConv : (s : Sym) -> (err : FileError) -> Error
fileErrorConv s err = MkError (e2s s err) (show err)
  where
    e2s : Sym -> FileError -> Sym
    e2s sym (GenericFileError x) = errGenericFileError sym
    e2s sym FileReadError        = errFileReadError sym
    e2s sym FileWriteError       = errFileWriteError sym
    e2s sym FileNotFound         = errFileNotFound sym
    e2s sym PermissionDenied     = errPermissionDenied sym

private
error : (s : Sym) -> (err : FileError) ->
        STrans m (Result r) (out_fn (Err $ fileErrorConv s err)) out_fn
error s err = pure (Err $ fileErrorConv s err)

data FileHandle : (hnd : Type) -> (mode : Mode) -> Type where
  MkFile : hnd -> FileHandle hnd mode

FileIO IO where
  File mode = State (FileHandle Prelude.File.File mode)

  fileIOinit tbl = do s <- genSym tbl --new !(genSym tbl) ...> INTERNAL ERROR
                      new s

  fileIOclose s = delete s

  fileOpen s path mode = do Right h <- lift $ openFile path mode
                                    | Left e => error !(read s) e
                            var <- new $ MkFile h
                            pure (Ok var)

  fileClose s f = do MkFile h <- read f
                     lift $ closeFile h
                     delete f

  fileSize s f = do MkFile h <- read f
                    Right sz <- lift $ fileSize h | Left e => error !(read s) e
                    pure (Ok sz)

  fileEOF s f = do MkFile h <- read f
                   pure $ Ok !(lift $ fEOF h)

  fileRead s f len = do MkFile h <- read f
                        Right str <- lift $ fGetChars h len
                                  | Left e => error !(read s) e
                        pure (Ok str)

  fileWrite s f str = do MkFile h <- read f
                         Right () <- lift $ fPutStr h str
                                  | Left e => error !(read s) e
                         pure (Ok ())

-- Example generic function

readFile : (FileIO m, StringBufferIO m) => (s : Var) -> (path : String) ->
           ST m (Result String) [s ::: FIO]
readFile s path = with ST do
  Ok f <- call $ fileOpen s path Read | Err e => err e
  Ok sz <- call $ fileSize s f | Err e => do fileClose s f; err1 s e
  sb <- call $ newStringBuffer (sz + 1)
  r <- readFile' s f sz sb
  str <- call $ getStringFromBuffer sb
  call $ fileClose s f
  pure $ map (const str) r
 where
  readFile' : (FileIO m, StringBufferIO m) =>
              (s : Var) -> (f : Var) -> Int -> (sb : Var) ->
              ST m (Result ()) [f  ::: File {m=m} Read,
                                s  ::: FIO,
                                sb ::: StrBuffer {m=m}]
  readFile' s f sz sb = with ST do
    Ok x <- call $ fileEOF s f | Err e => err e
    if not x && sz > 0
      then do Ok l <- call $ fileRead s f 1024000 | Err e => err e
              call $ addToStringBuffer sb l
              assert_total $ readFile' s f (sz - 1024000) sb
      else pure (Ok ())

  err1 : (FileIO m) => (s : Var) -> Error -> ST m (Result r) [s ::: FIO]
  err1 s e = do sym <- read s
                symElim (errCode e) [(errFileNotFound sym, (pure $ Err e))]
                                     (pure $ Err e)

