-- |
-- Module:     Control.Wire.Unsafe.Event
-- Copyright:  (c) 2013 Ertugrul Soeylemez
-- License:    BSD3
-- Maintainer: Ertugrul Soeylemez <es@ertes.de>
{-#LANGUAGE TupleSections#-}
module Control.Wire.Unsafe.Event
    ( -- * Events
      Event(..),

      -- * Helper functions
      event,
      merge,
      occurred,
      onEventM
    )
    where

import Control.DeepSeq
import Control.Monad
import Control.Wire.Core
import Data.Semigroup
import Data.Typeable


-- | Denotes a stream of values, each together with time of occurrence.
-- Since 'Event' is commonly used for functional reactive programming it
-- does not define most of the usual instances to protect continuous
-- time and discrete event occurrence semantics.

data Event s a = Event [(s,a)] | NoEvent  deriving (Typeable)

instance Functor (Event s) where
    fmap f = event NoEvent (Event . fmap (\(s,a) -> (s,f a)))

instance (Ord s, Semigroup a) => Monoid (Event s a) where
    mempty = NoEvent
    mappend = (<>)

instance (NFData a,NFData s) => NFData (Event s a) where
    rnf (Event x) = rnf x
    rnf NoEvent   = ()

instance (Ord s, Semigroup a) => Semigroup (Event s a) where
    (<>) = merge (<>)


-- | Fold the given event.

event :: b -> ([(s,a)] -> b) -> Event s a -> b
event _ j (Event x) = j x
event n _ NoEvent   = n



-- | Merge two events using the given function when both occur at the
-- same time.

merge ::(Ord s) => (a -> a -> a) -> Event s a -> Event s a -> Event s a
merge _ NoEvent NoEvent     = NoEvent
merge _ (Event x) NoEvent   = Event x
merge _ NoEvent (Event y)   = Event y
merge f (Event x) (Event y) = Event $ mergeL f x y
  where
    mergeL :: (Ord s) => (b -> b -> b) -> [(s,b)] -> [(s,b)] -> [(s,b)]
    mergeL f ((s,b):ls) ((s',b'):ls')
        | s == s' = (s,f b b') : mergeL f ls ls'
        | s < s'  = (s,b) : mergeL f ls ((s',b'):ls')
        | s > s'  = (s',b') : mergeL f ((s,b):ls) ls'
    mergeL _ [] l = l
    mergeL _ l [] = l


-- | Did the given event occur?

occurred :: Event s a -> Bool
occurred = event False (const True)


-- | Each time the given event occurs, perform the given action with the
-- value the event carries.  The resulting event carries the result of
-- the action.
--
-- * Depends: now.

onEventM :: (Monad m) => (a -> m b) -> Wire s e m (Event s a) (Event s b)
onEventM c = mkGen_ $ liftM Right . event (return NoEvent) (liftM Event . mapM (\(s,x) -> (s,) <$> c x ))
