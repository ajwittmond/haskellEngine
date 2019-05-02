module Run where

import Prelude hiding (id,(.))
import HList
import Component
import Control.Monad.State.Strict
import qualified Data.IntMap.Strict as M
import Control.Wire
import Data.Either
import Data.Maybe
import Control.Wire.Unsafe.Event

data ApplyGameUpdate entities = AGU (Timed NominalDiffTime ())
                                    (Game entities)
                                    (Event NominalDiffTime (GEvent entities))
instance ApplyAB
              (ApplyGameUpdate entities)
              (M.IntMap (HList x,GameWire x entities))
              (State (Event NominalDiffTime (GEvent entities))
                     (M.IntMap (HList x,GameWire x entities))) where
  applyAB (AGU ds g evt) mp = do
    M.mapMaybe id <$> mapM (\(a,w)-> do
        let ((e,w'),a') = runState (stepWire w ds (Right (g,evt))) a
        case e of
          Right evt -> do
            modify (mergeL evt)
            return $ Just (a', w')
          otherwise -> -- impeding wires are considered dead and removed
            return Nothing
      ) mp

gameWire ::(Monad m,
            HMapM (State (Event NominalDiffTime (GEvent entities)))
                          HList HList
                          (ApplyGameUpdate entities)
                          ( Mapify Game entities entities )
                          ( Mapify Game entities entities ),
             SameLength'  ( Mapify Game entities entities )
                          ( Mapify Game entities entities )) 
           => Game entities
           -> Wire (Timed NominalDiffTime ())
                   NominalDiffTime
                   m
                   (GameEvent entities)
                   (Game entities,GameEvent entities)
gameWire game@Game{_entities = ent} = mkGen $ \ds evt -> do
  let (ent',evt) = runState (hmapM (AGU ds game evt) ent) NoEvent
  let game' = game{_entities = ent'}
  return (Right (game,evt), gameWire game')
