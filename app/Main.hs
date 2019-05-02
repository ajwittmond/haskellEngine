module Main where

import Lib
import HList
import Graphics.Gloss.Interface.IO.Game
import Game
import Session
import Data.Maybe
import Control.Wire.Unsafe.Event


main :: IO ()
main = playIO (InWindow "game" (1280,720) (0,0))
              black
              60
              (clockSession_,gameWire game,game,NoEvent,NoEvent)
              toPicture
              propogateEvents
              update
  where
    toPicture (_,_,g,evt,_) =
      return $ Pictures $ extractFromGame g
    propogateEvents evt (s,g,gm,eOut,eIn) =
      return (s,g,gm,eOut,mergeL eIn (Event [(0,Gloss evt)]))
    update _ (s,g,gm,eOut,eIn) = do
      (ds,s') <- stepSession s
      (v,g') <- stepWire g ds (Right (mergeL eOut eIn))
      case v of
        Right (gm',eOut') -> return (s',g',gm',eOut',eIn)
        _               -> error "game impeding"
