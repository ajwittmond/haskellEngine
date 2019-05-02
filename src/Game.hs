{-#LANGUAGE TemplateHaskell#-}
{-#LANGUAGE TypeOperators#-}
{-#LANGUAGE UndecidableInstances#-}
{-#LANGUAGE ScopedTypeVariables#-}
module Game(
  Game(..),
  GEvent(..),
  Entity(..),
  GameWire,
  GEvent'(..),
  GameEvent,
  Mapify,
  Updateable(..),
  Component(..),
  module W,
  module HList,
  newGame,
  gameWire,
  extractFromGame
)where

import Prelude hiding ((.),id,init)
import HList
import Control.Wire as W
import Graphics.Gloss.Interface.IO.Interact as G
import Control.Lens
import qualified Data.IntMap.Strict as M
import Control.Monad.State.Strict
import Control.Monad.ST.Strict
import Control.Wire.Unsafe.Event
import Data.Proxy
import Data.Maybe

-- | Class representing game events
data GEvent' g (a :: [[*]]) =
  Gloss G.Event |
  Create (g a -> g a) 


type GameWire' g thisEntity entities =
               Wire  (Timed NominalDiffTime ())
                      NominalDiffTime
                      (State (HList thisEntity))
                      (g entities,W.Event NominalDiffTime (GEvent' g entities))
                      (W.Event NominalDiffTime (GEvent' g entities))



-- | This is a game entity consisting of a @HList@
-- of components and an id
data EntityData (a :: [*]) = EntityData {
  _index::Int,
  _typeIndex::Int,
  _components::(HList a)
}
makeLenses 'EntityData

newtype Entities g x entities = Entities (Int,M.IntMap (HList x,GameWire' g x entities))

instance Semigroup (Entities g x entities) where
  (Entities (i,m)) <> (Entities (i',m')) = (Entities (i',m'))

instance Monoid (Entities g x entities) where
  mempty = Entities (0,mempty)

type family Mapify g entities lst  where
  Mapify g entities (x ': xs) = Entities g x entities ': Mapify g entities xs
  Mapify _ _ '[] = '[]


-- | This is the object representing the current game state.
-- Contains all of the current entities public data as well as
-- TODO: The current state of the (abstract) input devices
data Game (entities :: [[*]]) = Game{
  _entities :: HList (Mapify Game entities entities)
}
makeLenses 'Game

-- | constructor for a game
newGame :: (Monoid (HList (Mapify Game entities entities))) => Game entities
newGame = Game mempty

-- | Game events
type GEvent entities = GEvent' Game entities

type GameEvent entities = W.Event NominalDiffTime (GEvent entities)

-- | The concrete(ish) type of wire that it used for the game
type GameWire this entities = GameWire' Game this entities


data ApplyGameUpdate entities = AGU (Timed NominalDiffTime ())
                                    (Game entities)
                                    (W.Event NominalDiffTime (GEvent entities))
instance ApplyAB
              (ApplyGameUpdate entities)
              (Entities Game x entities)
              (State (W.Event NominalDiffTime (GEvent entities))
                     (Entities Game x entities)) where
  applyAB (AGU ds g evt) (Entities (i,mp) ) = do
    (Entities.(i,)) <$> M.mapMaybe id <$> mapM (\(a,w)-> do
        let ((e,w'),a') = runState (stepWire w ds (Right (g,evt))) a
        case e of
          Right evt -> do
            modify (mergeL evt)
            return $ Just (a', w')
          otherwise -> -- impeding wires are considered dead and removed
            return Nothing
      ) mp

gameWire ::(Monad m,
            HMapM (State (W.Event NominalDiffTime (GEvent entities)))
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

class Updateable a where
  init :: a
  update :: a -> a -> a
  update _ a = a

class (Updateable a,TypeIxable (HList thisEntity) a) =>
       Component a (thisEntity :: [*]) (entities :: [[*]])  where
  wire :: Proxy a -> GameWire thisEntity entities
  wire _ = never

instance Updateable (HList '[]) where
  init = HNil

instance (Updateable x, Updateable (HList xs)) => Updateable (HList (x ': xs)) where
  init = init .*. init

instance (TypeIxable (HList (x ': xs)) (HList (x ': xs)),
          Component x  (x ': xs) entities,
          Component (HList xs) (x ': xs) entities)
         => Component (HList (x ': xs)) (x ': xs) entities where
  wire _ = liftA2 mergeL (wire (Proxy :: Proxy x)) (wire (Proxy :: Proxy (HList xs)))

data ToWire (this :: [*]) (entities :: [[*]]) = ToWire


-- | Allows validity of entities to be verified before the actual game is concrete.
-- This could also be used for reification. 
class (Component (HList this) this entities,
       TypeIxable (HList (Mapify Game entities entities))
                  (Entities Game this entities))
      => Entity this entities where
    create :: (HList this -> HList this) -> (Game entities -> Game entities)
    create f =
        let e = f init
            w = wire (Proxy :: Proxy (HList this))
        in entities.tIxp (Proxy :: Proxy (Entities Game this entities))  %~ \(Entities (i,mp)) ->
               Entities (i+1,M.insert (i+1) (e,w) mp)

data Extract = Extract
class ApplyExtract a (b::[*]) (c :: Bool) where
  extract :: Proxy c -> HList b -> Maybe a

instance (TypeIxable (HList b) a) => ApplyExtract a b 'True where
  extract _ hs = Just $ hs ^. tIx

instance ApplyExtract a b 'False where
  extract _ hs = Nothing

instance (ApplyExtract a b (HList.Contains b a))
          => ApplyAB Extract ([a],Entities Game b entities) [a] where
  applyAB _ (ls,Entities (_,mp)) =
    foldl (\l (e,_) -> maybe l (:l) $ extract (Proxy :: Proxy (HList.Contains b a)) e) ls mp

extractFromGame :: forall a entities . (HFoldl HList Extract (Mapify Game entities entities) [a] [a])
                    => Game entities -> [a]
extractFromGame g = hFoldl Extract ([] :: [a]) (g^.entities)
