{-#LANGUAGE UndecidableInstances#-}
{-#LANGUAGE TemplateHaskell#-}
{-#LANGUAGE TupleSections#-}
module Moveable where

import Prelude hiding ((.),id)
import Game
import Geometry
import Linear hiding (translation,angle)
import Control.Lens hiding (translation)
import HList
import Control.Wire
import Control.Lens

data Movement = Movement {
  _vel :: V2 Double,
  _accel :: V2 Double,
  _aVel :: Double,
  _aAccel :: Double
}
makeClassy 'Movement

instance Updateable Movement where
  init = Movement 0 0 0 0

instance (TypeIxable (HList this) Movement) => HasMovement (HList this) where
  movement = tIx

instance (TypeIxable (HList this) Transform ,
          TypeIxable (HList this) Movement) =>
           Component Movement this entities where
  wire _ = never . w
    where w = mkGen  ( \ds _ -> do
                let dt :: Double
                    dt = realToFrac $ dtime ds
                (v,a) <- liftA2 (,) (use vel) (use accel)
                translation .= dt *^ v + (1/2) * dt * dt *^ a
                vel .= dt *^ a
                (av,aa) <- liftA2 (,) (use aVel) (use aAccel)
                angle .= dt * av + (1/2) * dt * dt * aa
                aVel .= dt * aa
                return (Right (),w)
             )


