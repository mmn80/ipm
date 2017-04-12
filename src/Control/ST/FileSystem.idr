module Control.ST.FileSystem

import System
import Control.ST
import Control.ST.Error

%default total
%access public export

NodeId : Type
NodeId = Int

export
record NodeInfo where
  constructor MkNodeInfo
  parent : NodeId
  name : String
  isDir : Bool
  symLink : Maybe NodeId

export
record FileSystem where
  constructor MkFS
  currentId : NodeId
  table : List (NodeId, NodeInfo)
  root : NodeId
  cwd : NodeId

export
root : NodeInfo
root = MkNodeInfo 0 "root" True Nothing

export
addDir : String -> FileSystem -> FileSystem
addDir n fs =
  let node = MkNodeInfo (cwd fs) n True Nothing
      nid = (currentId fs) + 1
  in record { currentId = nid, table $= (::) (nid, node) } fs

data DirectoryError = GenericDirectoryError String | DirectoryAccessError

namespace Dir
  Res : Type -> Type
  Res r = Result [DirectoryError] r

  export
  fsDef : FileSystem
  fsDef = MkFS 0 [(0, root)] 0 0

interface Directory (m : Type -> Type) where
  FS : FileSystem -> Type
  fsInit  : ST m (Res Var) [addIfOk (FS Dir.fsDef)]
  fsClose : (v : Var) -> ST m () [remove v (FS fs)]
  mkDir : (v : Var) -> (n : String) -> ST m (Res ())
          [v ::: FS fs :-> result (const $ FS fs) (const $ FS $ addDir n fs)]

data FState : (fs : FileSystem) -> Type where
  MkFState : (fs : FileSystem) -> FState fs

Directory IO where
  FS fs = State (FState fs)

  fsInit = do var <- new $ MkFState fsDef
              pure (Ok var)
 
  fsClose var = delete var

  mkDir var n = do r <- lift $ system ("mkdir " ++ n)
                   if r == -1
                     then resErr $ GenericDirectoryError "mkdir failed"
                     else do MkFState fs <- read var
                             write var (MkFState $ addDir n fs)
                             pure (Ok ())
