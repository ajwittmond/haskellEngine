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
              (clockSession_,gameWire game,NoEvent,NoEvent)
              toPicture
              propogateEvents
              update
  where
    toPicture (_,_,evt,_) =
      case evt of
        (Event events) ->
            return $ Pictures $ (flip mapMaybe) events $ \ c ->
              case c of
                (_,Picture p) -> Just p
                _           -> Nothing
        NoEvent        -> return Blank
    propogateEvents evt (s,g,eOut,eIn) =
      return (s,g,eOut,mergeL eIn (Event [(0,Gloss evt)]))
    update _ (s,g,eOut,eIn) = do
      (ds,s') <- stepSession s
      (v,g') <- stepWire g ds (Right (mergeL eOut eIn))
      case v of
        Right (_,eOut') -> return (s',g',eOut',eIn)
        _               -> error "game impeding"
