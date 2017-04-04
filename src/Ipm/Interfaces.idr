module Ipm.Interfaces

import Control.ST
import Control.ST.File

data PartialOrdering = LT | EQ | GT | NC

interface Eq ty => ParOrd ty where
  compare : ty -> ty -> PartialOrdering

Ord ty => ParOrd ty where
  compare x y = case Prelude.Interfaces.compare x y of
                  LT => LT
                  EQ => EQ
                  GT => GT

