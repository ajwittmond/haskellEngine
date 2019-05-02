{-#LANGUAGE Arrows#-}
{-#LANGUAGE TemplateHaskell#-}
{-#LANGUAGE FlexibleContexts#-}
{-#LANGUAGE UndecidableInstances#-}
{-#LANGUAGE DataKinds#-}
{-#LANGUAGE FlexibleInstances#-}
{-#LANGUAGE TupleSections#-}
module Sprite where
import Prelude hiding (id , (.))
import Graphics.Gloss
import Control.Wire
import Codec.Picture
import Data.Vector.Storable as SV
import Data.Vector as V
import Control.Lens hiding (Contains)
import Data.Map
import Data.Proxy
import HList
import Game
import Geometry
import Linear
import GHC.Float

data Animation = Animation { _frames::(V.Vector Picture), _fps:: Float}
makeLenses 'Animation

animate :: (Monad m, HasTime t s)=> Animation -> Wire s e m Float Picture
animate (Animation frames fps) = proc rate -> do
  frame   <-  floor <$> arr (uncurry (*)) . (pure fps * timeF &&& id) -< rate
  returnA -< frames V.! frame

display :: (Monad m) => Animation -> Int -> Wire s e m a Picture
display (Animation frame _) i = pure $ frame V.! i

loadAnimation:: String -> Int -> Int -> Float -> IO (Either String Animation)
loadAnimation file xtiles ytiles fps = do
  picture <- readImage file
  case (convertRGBA8 <$> picture) of
    Right (Image w h dat) -> do
      let  (ptr,_) = SV.unsafeToForeignPtr0 dat
           bitmap    = bitmapDataOfForeignPtr w h
                          (BitmapFormat TopToBottom PxRGBA)
                          ptr True
           dim@(w',h')   = (w `div` xtiles,h `div` ytiles)
      return $ Right $ Animation
        (V.fromList [BitmapSection (Rectangle (x,y) dim) bitmap |x <- [0,w'..w], y <- [0,h'..h] ])
        fps
    Left a -> return $ Left a

class HasPicture a where
  picture :: Lens' a Picture

data Sprite  = Sprite {
  _animations::(Map String Animation),
  _currentAnimation::String
}
makeClassy 'Sprite

instance (TypeIxable (HList ls) Picture) => HasPicture (HList ls) where
  picture = tIxp (Proxy :: Proxy Picture) 

instance Updateable Picture where
  init = Blank

instance (TypeIxable (HList this) Picture) => Component Picture this entities 

data TransformedSprite = TransformedSprite

instance Updateable TransformedSprite where
  init  = TransformedSprite

transformPicture :: Transform -> Picture -> Picture
transformPicture _ Blank = Blank
transformPicture (Transform (V2 x y) (V2 w h) o) p =
  Translate (double2Float x) (double2Float y)
            (Rotate (double2Float o)
                    (Scale (double2Float w ) (double2Float h ) p) )

instance (TypeIxable (HList this) TransformedSprite,
          TypeIxable (HList this) Transform,
          TypeIxable (HList this) Picture) =>
          Component TransformedSprite this entities where
  wire _ = never . mkGen_
           (const $ Right <$> 
             (((tIx .=) =<< liftA2 transformPicture (use tIx) (use tIx))))

