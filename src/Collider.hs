{-#LANGUAGE UndecidableInstances#-}
module Collider where

import Geometry
import HList
import Game

data Collider = Collider [PhysShape]
                deriving(Eq,Ord,Show)

instance Updateable Collider where
  init = Collider []

instance (TypeIxable (HList this) Collider) => Component Collider this entities 
