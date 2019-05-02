-- |
-- Module:     Control.Wire.Event
-- Copyright:  (c) 2013 Ertugrul Soeylemez
-- License:    BSD3
-- Maintainer: Ertugrul Soeylemez <es@ertes.de>
{-#LANGUAGE TupleSections#-}
module Control.Wire.Event
    ( -- * Events
      Event,

      -- * Time-based
      at,
      never,
      now,
      periodic,
      periodicList,

      -- * Signal analysis
      became,
      noLonger,
      edge,
      whenChanged,

      -- * Modifiers
      (<&),
      (&>),
      dropE,
      dropWhileE,
      filterE,
      merge,
      mergeL,
      mergeR,
      notYet,
      once,
      takeE,
      takeWhileE,

      -- * Scans
      accumE,
      accum1E,
      iterateE,
      -- ** Special scans
      maximumE,
      minimumE,
      productE,
      sumE
    )
    where

import Control.Applicative
import Control.Arrow
import Control.Monad.Fix
import Control.Wire.Core
import Control.Wire.Session
import Control.Wire.Unsafe.Event
import Data.Fixed
import Data.Bool
import Data.List


-- | Merge events with the leftmost event taking precedence.  Equivalent
-- to using the monoid interface with 'First'.  Infixl 5.
--
-- * Depends: now on both.
--
-- * Inhibits: when any of the two wires inhibit.

(<&) :: (Ord t,Monad m) => Wire s e m a (Event t b) -> Wire s e m a (Event t b) -> Wire s e m a (Event t b)
(<&) = liftA2 (merge const)

infixl 5 <&


-- | Merge events with the rightmost event taking precedence.
-- Equivalent to using the monoid interface with 'Last'.  Infixl 5.
--
-- * Depends: now on both.
--
-- * Inhibits: when any of the two wires inhibit.

(&>) :: (Ord t,Monad m) => Wire s e m a (Event t b) -> Wire s e m a (Event t b) -> Wire s e m a (Event t b)
(&>) = liftA2 (merge (const id))

infixl 5 &>


-- | Left scan for events.  Each time an event occurs, apply the given
-- function.
--
-- * Depends: now.

accumE ::
    (b -> a -> b)  -- ^ Fold function
    -> b           -- ^ Initial value.
    -> Wire s e m (Event s' a) (Event s' b)
accumE f = loop
    where
    loop x' =
        mkSFN $
            event (NoEvent, loop x')
                  (\y -> let (s,ys)  = unzip y
                             (x,xs) = mapAccumL (\x y -> let a = f x y in (a,a) ) x' ys
                         in (Event $ zip s xs, loop x)
                  )


-- | Left scan for events with no initial value.  Each time an event
-- occurs, apply the given function.  The first event is produced
-- unchanged.
--
-- * Depends: now.

accum1E ::
    (a -> a -> a)  -- ^ Fold function
    -> Wire s e m (Event s' a) (Event s' a)
accum1E f = initial
    where 
    initial = 
        mkSFN $ event (NoEvent, initial) (\ls ->
                 let ((_,x),xs) = mapAccumL (\(s,x) (s',x')->
                                               let a = f x x' in ((s',a),(s',a))
                                            ) (head ls) ls
                 in  (Event xs, accumE f x)
            )


-- | At the given point in time.
--
-- * Depends: now when occurring.

at ::
    (HasTime t s)
    => t  -- ^ Time of occurrence.
    -> Wire s e m a (Event t a)
at t' =
    mkSF $ \ds x ->
        let t = t' - dtime ds
        in if t <= 0
             then (Event [(t,x)], never)
             else (NoEvent, at t)


-- | Occurs each time the predicate becomes true for the input signal,
-- for example each time a given threshold is reached.
--
-- * Depends: now.

became :: (Monoid t) => (a -> Bool) ->  Wire s e m a (Event t a)
became p = off
    where
    off = mkSFN $ \x -> if p x then (Event [(mempty,x)], on) else (NoEvent, off)
    on = mkSFN $ \x -> (NoEvent, if p x then on else off)


-- | Forget the first given number of occurrences.
--
-- * Depends: now.

dropE :: Int -> Wire s e m (Event t a) (Event t a)
dropE n | n <= 0 = mkId
dropE n = mkSFN $ \evt ->
  case evt of
    NoEvent -> (NoEvent, dropE n)
    (Event lst) ->
      let count m [] = (m,[])
          count m (x:xs)  = if m == n then (m,xs) else count (m+1) xs
          (m,ls) = count 0 lst
      in  (if null ls then NoEvent else Event ls,dropE m)


-- | Forget all initial occurrences until the given predicate becomes
-- false.
--
-- * Depends: now.

dropWhileE :: (a -> Bool) -> Wire s e m (Event t a) (Event t a)
dropWhileE p = mkSFN $ \evt->
  case evt of
    NoEvent  -> (NoEvent, dropWhileE p)
    Event ls ->
      let ls' = dropWhile (p . snd) ls
      in  if null ls
          then (NoEvent, dropWhileE p)
          else (Event ls', mkId)


-- | Forget all occurrences for which the given predicate is false.
--
-- * Depends: now.

filterE :: (a -> Bool) -> Wire s e m (Event t a) (Event t a)
filterE p =
    mkSF_ $ \mev ->
        case mev of
          Event x ->
            let ls' = filter (p . snd) x
            in  if null ls' then NoEvent else Event ls'
          _ -> NoEvent


-- | On each occurrence, apply the function the event carries.
--
-- * Depends: now.

iterateE :: a -> Wire s e m (Event t (a -> a)) (Event t a)
iterateE = accumE (\x f -> f x)


-- | Maximum of all events.
--
-- * Depends: now.

maximumE :: (Ord a) => Wire s e m (Event t a) (Event t a)
maximumE = accum1E max


-- | Minimum of all events.
--
-- * Depends: now.

minimumE :: (Ord a) => Wire s e m (Event t a) (Event t a)
minimumE = accum1E min


-- | Left-biased event merge.

mergeL :: (Ord t) => Event t a -> Event t a -> Event t a
mergeL = merge const


-- | Right-biased event merge.

mergeR :: (Ord t) => Event t a -> Event t a -> Event t a
mergeR = merge (const id)


-- | Never occurs.

never :: Wire s e m a (Event t b)
never = mkConst (Right NoEvent)


-- | Occurs each time the predicate becomes false for the input signal,
-- for example each time a given threshold is no longer exceeded.
--
-- * Depends: now.

noLonger :: (Monoid t) => (a -> Bool) -> Wire s e m a (Event t a)
noLonger p = off
    where
    off = mkSFN $ \x -> if p x then (NoEvent, off) else (Event [(mempty,x)], on)
    on = mkSFN $ \x -> (NoEvent, if p x then off else on)


-- | Events occur first when the predicate is false then when it is
-- true, and then this pattern repeats.
--
-- * Depends: now.

edge :: (Monoid t) => (a -> Bool) -> Wire s e m a (Event t a)
edge p = off
    where
    off = mkSFN $ \x -> if p x then (Event [(mempty,x)], on) else (NoEvent, off)
    on = mkSFN $ \x -> if p x then (NoEvent, on) else (Event [(mempty,x)], off)

-- | Event occurs with value immediately and when the value changes
--
-- * Depends: Now
whenChanged ::(Eq a,Monoid s,Monoid t) => Wire s e m a (Event t a)
whenChanged = mkPure $ \_ x -> (Right $ Event [(mempty,x)], check x)
    where
    check x = mkPure $ \_ x' -> bool (Right $ Event [(mempty,x')], check x') (Right NoEvent, check x) (x' == x)

-- | Forget the first occurrence.
--
-- * Depends: now.

notYet :: Wire s e m (Event t a) (Event t a)
notYet =
    mkSFN $ event (NoEvent, notYet) (const (NoEvent, mkId))


-- | Occurs once immediately.
--
-- * Depends: now when occurring.

now :: (Monoid t) => Wire s e m a (Event t a)
now = mkSFN $ \x -> (Event [(mempty,x)], never)


-- | Forget all occurrences except the first.
--
-- * Depends: now when occurring.

once :: Wire s e m (Event t a) (Event t a)
once =
    mkSFN $ \mev ->
        (mev, if occurred mev then never else once)


-- | Periodic occurrence with the given time period.  First occurrence
-- is now.
--
-- * Depends: now when occurring.

periodic :: (HasTime t s) => t -> Wire s e m a (Event t a)
periodic int | int <= 0 = error "periodic: Non-positive interval"
periodic int = mkSFN $ \x -> (Event [(0,x)], loop int)
    where
    loop 0 = loop int
    loop t' =
        mkSF $ \ds x ->
            let t = t' - dtime ds
            in if t <= 0
                 then (Event [(t,x)], loop (mod' t int))
                 else (NoEvent, loop t)


-- | Periodic occurrence with the given time period.  First occurrence
-- is now.  The event values are picked one by one from the given list.
-- When the list is exhausted, the event does not occur again.

periodicList :: (HasTime t s) => t -> [b] -> Wire s e m a (Event t b)
periodicList int _ | int <= 0 = error "periodic: Non-positive interval"
periodicList _ [] = never
periodicList int (x:xs) = mkSFN $ \_ -> (Event [(0,x)], loop int xs)
    where
    loop _ [] = never
    loop 0 xs = loop int xs
    loop t' xs0@(x:xs) =
        mkSF $ \ds _ ->
            let t = t' - dtime ds
            in if t <= 0
                 then (Event [(t,x)], loop (mod' t int) xs)
                 else (NoEvent, loop t xs0)


-- | Product of all events.
--
-- * Depends: now.

productE :: (Num a) => Wire s e m (Event t a) (Event t a)
productE = accumE (*) 1


-- | Sum of all events.
--
-- * Depends: now.

sumE :: (Num a) => Wire s e m (Event t a) (Event t a)
sumE = accumE (+) 0


-- | Forget all but the first given number of occurrences.
--
-- * Depends: now.

takeE :: Int -> Wire s e m (Event t a) (Event t a)
takeE n | n <= 0 = never
takeE n =
    fix $ \again ->
    mkSFN $ \mev ->
       case mev of
         NoEvent -> (NoEvent,again)
         Event ls ->
           let ls'  =  take n ls
           in  (Event ls', takeE (n - length ls))


-- | Forget all but the initial occurrences for which the given
-- predicate is true.
--
-- * Depends: now.

takeWhileE :: (a -> Bool) -> Wire s e m (Event t a) (Event t a)
takeWhileE p =
    fix $ \again ->
    mkSFN $ \mev ->
        case mev of
          Event x  ->
            let (x',xs') = span (p . snd) x
            in  (if null x' then NoEvent else Event x',
                 if null xs' then takeWhileE p else never)
          _ -> (mev, again)
