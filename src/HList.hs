{-#LANGUAGE TemplateHaskell, TypeFamilies, FlexibleInstances, FlexibleContexts,
            UndecidableInstances, DataKinds, PolyKinds, ScopedTypeVariables,
            FunctionalDependencies, RankNTypes, TypeOperators #-}
{- This module consists of reimplementatins and modifications of things from the HList package (https://hackage.haskell.org/package/HList) .
   I was having difficulty getting it to work with my dependencies when I started this project.  It has since been updated to
   work with modern GHC
-}
module HList where

import Control.Lens hiding (Contains)
import Data.Typeable
import Control.DeepSeq
import Control.Applicative
import Text.Read
import Text.ParserCombinators.ReadP

type family TEq a b :: Bool where
  TEq a a = 'True
  TEq a b = 'False

data family Id a

newtype EntityId = EntityId (TypeRep,Int) deriving (Show)

idType :: EntityId -> TypeRep
idType (EntityId (t,_)) = t

idVal :: EntityId -> Int
idVal (EntityId (_,i)) = i

instance Eq EntityId where
  (EntityId (t1,v1)) == (EntityId (t2,v2)) =
    (t1 == t2) && ((v1 == v2) || (v1<0 || v2<0))

instance Ord EntityId where
  compare (EntityId (t1,v1)) (EntityId (t2,v2)) =
         compare t1 t2 <>
             if (v1<0 || v2<0)
                then EQ
                else compare v1 v2

instance NFData EntityId where
  rnf d@(EntityId val) = d `seq` rnf val


data Signal c = Signal{_target::Maybe EntityId,_payload::c}
makeLenses ''Signal

instance Functor Signal where
  fmap f s@(Signal _ p) = s{_payload= f p}

instance Applicative Signal where
  pure = Signal Nothing
  (Signal r f) <*> (Signal r' a) = Signal (r <|> r') (f a)

sigify :: [a] -> [Signal a]
sigify = map $ Signal Nothing

instance (Show a) => Show (Signal a) where
  show (Signal x y) = "(Signal " ++ show x ++" "++show y++")"

class Headable (r :: [*] -> *)  (ls :: [*]) a | r ls -> a where
  headH :: r ls -> a

class Tailable (r :: [*] -> *) (l :: [*]) (ls :: [*]) | r l -> ls where
  tailH :: r l -> r ls

class TypeIxable b a where
  tIx :: Lens' b a
  tIxp :: Proxy a -> Lens' b a
  tIxp = const tIx

class Nilable (r :: [*] -> *) where
  nil' :: r '[]

class Consable (r :: [*] -> *) l ls a | r a l -> ls where
  cons' :: a -> r l -> r ls
  (.*.) :: a -> r l -> r ls
  (.*.) = cons'

infixr 6 `cons'`
infixr 6 .*.

class HBuild' (r :: [*] -> * ) (l :: [*]) o where
  hBuild' :: r l -> o

instance HBuild' r l (r l) where
  hBuild' = id

instance (Consable r l ls a,HBuild' r ls x) => HBuild' r l ( a -> x) where
  hBuild' lst x = hBuild' (cons' x lst)

class TypeIxable' (r :: [*] -> * ) (l :: [*]) a (e :: Bool) (f :: Bool) where
  tIx' :: Proxy e -> Proxy f -> Lens' (r l) a

instance (Headable r (b ': l) h, TypeIxable' r (b ': l) a (TEq a h) (TEq a (r (b ': l))))
          =>TypeIxable (r (b ': l)) a where
  tIx = tIx' (Proxy :: Proxy (TEq a h)) (Proxy :: Proxy (TEq a (r (b ': l))))

instance (Consable r l ls a, Headable r ls a, Tailable r ls l , TypeIxable (r l) a) => TypeIxable' r ls a 'False 'False where
  tIx' _ _ f lst  = cons' (headH lst) <$> tIx f (tailH lst)

instance (Consable r l ls a, Headable r ls a, Tailable r ls l ) => TypeIxable' r ls a 'True 'False where
  tIx' _ _ f lst  = (.*. tailH lst ) <$> f (headH lst) 

-- HLists contain themselves
instance TypeIxable' r ls (r ls) 'False 'True where
  tIx' _ _ = id

data family HList (l::[*])

data instance HList '[] = HNil
data instance HList (x ': xs) = x `HCons` HList xs


hBuild :: (HBuild' HList '[] o) => o
hBuild = hBuild' HNil

hEnd :: HList l -> HList l
hEnd = id

infixr 8 `HCons`

instance Headable HList (a ': b) a where
  headH (HCons x l) = x

instance Tailable HList (a ': b) b where
  tailH (HCons x l) = l

instance Nilable HList where
  nil' = HNil

instance Consable HList l (a ': l) a where
  cons' = HCons

instance Show (HList '[]) where
  show HNil = "HNil"

instance (Show a,Show (HList b)) => Show (HList (a ': b)) where
  show (HCons x l) = "(HCons "++show x++" "++show l++")"

instance Eq (HList '[]) where
  HNil == HNil = True

instance (Eq x,Eq (HList xs)) => Eq (HList (x ': xs)) where
  (HCons a as) == (HCons a' as') = a == a' && as == as'

instance Ord (HList '[]) where
  compare = const . const EQ

instance (Ord x, Ord (HList xs)) => Ord (HList (x ': xs)) where
  compare (HCons a as) (HCons a' as') = compare a a' <> compare as as'

instance Semigroup (HList '[]) where
  (<>) = const $ const HNil

instance (Semigroup x, Semigroup (HList xs)) => Semigroup (HList (x ': xs)) where
  (a `HCons` as) <> (b `HCons` bs) = ( a <> b ) `HCons` ( as <> bs )

instance Monoid (HList '[]) where
  mempty = HNil

instance (Monoid x, Monoid (HList xs)) => Monoid (HList ( x ': xs )) where
  mempty =  mempty `HCons` mempty

instance (Read x, Read (HList xs)) => Read (HList (x ': xs)) where
  readPrec = do
    x <- readPrec
    lift $ do
      skipSpaces
      string ".*."
    xs <- readPrec
    return $ x .*. xs

type family HLift (r :: [*] -> *) (a :: *) where
     HLift HList a = a

type family HUnLift (r :: [*] -> *) (a :: *) where
     HUnLift HList a = a

class SameLength' (es1 :: [k]) (es2 :: [m])
instance (es2 ~ '[]) => SameLength' '[] es2
instance (SameLength' xs ys, es2 ~ (y ': ys)) => SameLength' (x ': xs) es2

class ApplyAB f a b | f a -> b where
  applyAB :: f -> a -> b

type family TMap f  ls where
  TMap f '[] = '[]
  TMap f (x ': xs) = f x ': TMap f xs

class HMap (r1 :: [*]-> *) (r2 :: [*]-> *) f (a::[*]) (b::[*]) | r1 r2 f a -> b where
  hmap ::(SameLength' a b) => f -> r1 a -> r2 b

class HFoldr (r :: [*] -> *) f (l :: [*]) v a | r l v f -> a where
  hFoldr :: f -> v -> r l -> a

class HFoldl (r :: [*] -> *) f (l :: [*]) v a | r l v f -> a where
  hFoldl :: f -> v ->  r l -> a

class HMapM m (r1 :: [*]-> *) (r2 :: [*]-> *) f (a::[*]) (b::[*]) | r1 r2 f a -> b where
  hmapM ::(SameLength' a b) => f -> r1 a -> m (r2 b)

instance ApplyAB (a -> b) a b where
  applyAB = ($)

instance (Nilable b) => HMap a b f '[] '[] where
  hmap _ _ = nil'

instance (Nilable b,Monad m) => HMapM m a b f '[] '[] where
  hmapM _ _ = return nil'

instance (ApplyAB f a b,
          HMap r1 r2 f l1 l2,
          SameLength' l1 l2,
          Headable r1 (e1 ': l1)  a ,
          Consable r2 l2 (e2 ': l2) b,
          Tailable r1 (e1 ': l1)  l1) => HMap r1 r2 f (e1 ': l1) (e2 ': l2) where
   hmap f lst = applyAB f (headH lst) `cons'` hmap f (tailH lst)

instance (Monad m,
          ApplyAB f a (m b),
          HMapM m r1 r2 f l1 l2,
          SameLength' l1 l2,
          Headable r1 (e1 ': l1)  a ,
          Consable r2 l2 (e2 ': l2) b,
          Tailable r1 (e1 ': l1)  l1) => HMapM m r1 r2 f (e1 ': l1) (e2 ': l2) where
   hmapM f lst =  cons' <$> applyAB f (headH lst) <*>  hmapM f (tailH lst)

instance (a ~ b) => HFoldl r f '[] a b where
  hFoldl _ = const

instance (ApplyAB f (b,h) a,
          Headable r l h,
          Tailable r l ls,
          HFoldr r f ls v b) => HFoldr r f l v a where
  hFoldr f v ls = applyAB f  (hFoldr f v (tailH ls),headH ls)

instance (a ~ b) => HFoldr r f '[] a b  where
  hFoldr _ = const

instance (zx ~ (v,h),
          ApplyAB f zx b,
          Headable r (e ': ls) h,
          Tailable r (e ': ls) ls,
          HFoldl r f ls b a) => HFoldl r f (e ': ls) v a where
  hFoldl f v ls = hFoldl f (applyAB f (v,headH ls)) (tailH ls)



class HWrap (r :: [*] -> *) (l :: [*]) a where
  hWrap :: a -> r l

class HWrapEq (eq :: Bool) (r :: [*] -> *) (l :: [*]) a where
  hWrapEq :: Proxy eq -> a -> r l

instance (Consable r ls (a ': ls) b,Monoid (r ls)) => HWrapEq 'True r (a ': ls) b where
  hWrapEq _ x = x .*.( mempty :: r ls)

instance (HWrap r ls a,Consable r ls (x ': ls )(HLift r x), Monoid (HLift r x)) => HWrapEq 'False r (x ': ls) a where
  hWrapEq _ x = (mempty :: HLift r x) .*. (hWrap x :: r ls)

instance (HWrapEq (TEq (HLift r a) b) r (a ': ls) b) => HWrap r (a ': ls) b where
  hWrap = hWrapEq (Proxy :: Proxy (TEq (HLift r a) b)) 

type family Contains (l::[*]) a where
  Contains (a ': ls) a = 'True
  Contains (b ': ls) a = Contains ls a
  Contains '[] a = 'False
