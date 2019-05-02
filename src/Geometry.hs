{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE Strict #-}
{-# LANGUAGE UndecidableInstances#-}
module Geometry(
  Transform(..),
  PhysShape(..),
  Manifold(..),
  Transformation(..),
  HasTransform(..),
  Point,
  collision,
  toBound,
  bound,
  radius,
  center,
  doTranslate,
  doRotate,
  doScale,
  position,
  orient,
  getPNs,
  trans,
  newLine,
  newCircle,
  newOBB,
  fillMul,
  angle,
  pos
) where

import Linear hiding (trace,translation,angle,scale,rotation)
import Data.List
import Control.Lens hiding (transform)
import Debug.Trace
import Data.Maybe (fromJust)
import Data.Ord (comparing)
import Game
import HList

type Point = V2 Double

transMat :: Point -> V3 (V3 Double)
transMat (V2 x y) = V3 (V3 1 0 x) (V3 0 1 y) (V3 0 0 1)

rotMat :: Double -> V3 (V3 Double)
rotMat o =
  let c = cos o
      s = sin o
  in V3 (V3 c (-s) 1) (V3 s c 1) (V3 0 0 1)

scaleMat :: Point -> V3 (V3 Double)
scaleMat (V2 w h) = V3 (V3 w 0 1) (V3 0 h 1) (V3 0 0 1)


data Transform = Transform {_translation::Point,_scale::Point,_orientation::Double} deriving (Show,Eq,Ord)
makeClassy ''Transform

pos :: (HasTransform a) => Lens' a Point
pos = translation

angle :: (HasTransform a) => Lens' a Double
angle = orientation

class Transformation a where
  convertTransform :: Transform -> a

instance Transformation (V2 (V3 Double)) where
  convertTransform (Transform (V2 x y) (V2 w h) o) =
    let c = cos o
        s = sin o
    in  V2 (V3 (c*w) (negate h*s) x) (V3 (s*w) (c*h) y)

instance Transformation (V4 (V4 Double)) where
  convertTransform (Transform (V2 x y) (V2 w h) o) =
    let c = cos o
        s = sin o
    in  V4 (V4 (c*w) (negate h*s) 0 x) (V4 (s*w) (c*h) 0 y) (V4 0 0 1 0) (V4 0 0 0 1)

fillMul :: V2 Double -> V2 (V3 Double) -> V2 Double
fillMul (V2 x y) mat = mat !* V3 x y 1

fillMulV :: V2 Double -> V2 (V3 Double) -> V2 Double
fillMulV (V2 x y) mat = mat !* V3 x y 0

fillMul3 :: V2 Double -> V3 (V3 Double) -> V2 Double
fillMul3 (V2 x y) mat = (mat !* V3 x y 1) ^. _xy

fillMulV3 :: V2 Double -> V3 (V3 Double) -> V2 Double
fillMulV3 (V2 x y) mat = (mat !* V3 x y 0) ^. _xy

data PhysShape = Line {_trans::Transform} |
                Circle {_trans::Transform} |
                OBB {_trans::Transform} |
                Polygon {_trans::Transform, _points::[Point]} |
                Box {_pos::Point, _dim::Point} deriving (Show,Eq,Ord)

newCircle :: V2 Double -> Double -> PhysShape
newCircle p r = Circle $ Transform p (pure r) 0

newOBB :: V2 Double -> V2 Double -> PhysShape
newOBB p d = OBB $ Transform p d 0

newLine :: Point -> Point -> PhysShape
newLine a b = Line $ Transform a (b-a) 0

trans :: Lens' PhysShape Transform
trans f (Line t) = Line <$> f t
trans f (Circle t) = Circle <$> f t
trans f (OBB t) = OBB <$> f t
trans f (Polygon t p) =  (`Polygon` p) <$> f t
trans f (Box p w) = (\(Transform p' w' _) -> Box (p'+ (w' ^/ 2)) w') <$> f (Transform (p+(w^/2)) w 0)

position :: Lens' PhysShape Point
position f (Box p w) = (\p' -> Box (p'-w^/2) w) <$> f (p + (w^/2))
position f (Line t@(Transform p _ _)) = (\p' -> Line t{_translation = p'}) <$> f p
position f (Circle t@(Transform p _ _)) = (\p' -> Circle t{_translation = p'}) <$> f p
position f (OBB t@(Transform p _ _)) = (\p' -> OBB t{_translation = p'}) <$> f p
position f (Polygon t@(Transform p _ _) ps) = (\p' -> Polygon t{_translation = p'} ps) <$> f p

orient :: Lens' PhysShape Double
orient f b@(Box p w) = const b <$> f 0
orient f (Line t@(Transform _ _ o)) = (\o' -> Line t{_orientation= o'}) <$> f o
orient f (Circle t@(Transform _ _ o)) = (\o' -> Circle t{_orientation = o'}) <$> f o
orient f (OBB t@(Transform _ _ o)) = (\o' -> OBB t{_orientation = o'}) <$> f o
orient f (Polygon t@(Transform _ _ o) ps) = (\o' -> Polygon t{_orientation = o'} ps) <$> f o

doTranslate :: V2 Double -> PhysShape -> PhysShape
doTranslate (V2 x y) (Line t@(Transform (V2 x1 y1) _ _)) = Line t{_translation=V2 (x+x1) (y+y1)}
doTranslate (V2 x y) (OBB t@(Transform (V2 x1 y1) _ _)) = OBB t{_translation=V2 (x+x1) (y+y1)}
doTranslate (V2 x y) (Polygon t@(Transform (V2 x1 y1) _ _) p) =Polygon t{_translation=V2 (x+x1) (y+y1)} p
doTranslate (V2 x y) (Circle t@(Transform (V2 x1 y1) _ _)) =Circle t{_translation=V2 (x+x1) (y+y1)}
doTranslate (V2 x y) (Box (V2 x1 y1) a) = Box (V2 (x+x1) (y+y1)) a

doRotate :: Double->PhysShape->PhysShape
doRotate r (Line t@(Transform _ _ o)) = Line t{_orientation=o+r}
doRotate r (OBB t@(Transform _ _ o)) =OBB t{_orientation=o+r}
doRotate r (Polygon t@(Transform _ _ o) p) = Polygon t{_orientation=o+r} p
doRotate r (Circle t@(Transform _ _ o)) = Circle t{_orientation=o+r}
doRotate _ b@(Box _ _) = b

doScale :: V2 Double -> PhysShape->PhysShape
doScale (V2 w h) (Line t@(Transform _ (V2 w1 h1) _)) = Line t{_scale=V2 (w*w1) (h*h1)}
doScale (V2 w h) (OBB t@(Transform _ (V2 w1 h1) _)) = OBB t{_scale=V2 (w*w1) (h*h1)}
doScale (V2 w h) (Polygon t@(Transform _ (V2 w1 h1) _) p) = Polygon t{_scale=V2 (w*w1) (h*h1)} p
doScale (V2 w h) (Circle t@(Transform _ (V2 w1 h1) _)) = Circle t{_scale=V2 (w*w1) (h*h1)}
doScale (V2 w h) b@(Box _ (V2 w1 h1)) = b{_dim=V2 (w*w1) (h*h1)}

radius (Circle (Transform _ (V2 w _) _)) = w/2
center (Circle (Transform c _ _)) = c

data Manifold = Manifold {points::[Point],normal::Point,transVec::Point,offset::Double} deriving (Show,Eq,Ord)
rev (Manifold p n t o) = Manifold p (-n) t (-o)

getBounds :: [Point] -> (Double, Double,Double,Double)
getBounds = foldl'
  (\(a,b,c,d) (V2 x y)->
          (min x a, min y b, max x c, max y d))
  (1/0,1/0,-1/0,-1/0)

squarePoints :: [V2 Double]
squarePoints  = [V2 0.5 0.5, V2 (-0.5) 0.5, V2 (-0.5) (-0.5) , V2 0.5 (-0.5)]

squareAxis :: [V2 Double]
squareAxis  = [V2 0 1, V2 1 0]

getPNs :: PhysShape -> ([Point],[Point])
getPNs (OBB t) = let mat =convertTransform t
                 in (map (`fillMul` mat) squarePoints, map (`fillMulV` mat) squareAxis)
getPNs  (Polygon t points) =
  let mat = convertTransform t
      p = map (`fillMul` mat) points
      toNorms :: Point -> [Point] -> [Point] -> [Point]
      toNorms first [x] a = perp (first-x) : a
      toNorms first (x:y:xs) a = toNorms first (y:xs) (perp (y-x):a)
  in (p,toNorms (head p) (tail p) [])
getPNs  (Line (Transform (V2 x y) (V2 w h) o)) =
  let c = cos o
      s = sin o
      rot = V2 (V2 c (-s)) (V2 s c)
      verts@[a,b] = [V2 (x-(w/2)) (y-(h/2)),V2 (x-(w/2)) (y-(h/2))]
      rotVerts@[ar,br] = map (rot !*) verts
  in if o == 0 then (verts,[(a-b),perp (a-b)]) else (rotVerts,[perp (ar-br)])
getPNs  (Box (V2 x y) (V2 w h)) =
  ([V2 x y ,V2 (x+w) y,V2 (x+w) (y+h),V2 x (y+h)],squareAxis)



--converts a physShape to a Box repesenting it bounds
toBound :: PhysShape -> PhysShape
toBound b@(Box x y) = b
toBound (Line (Transform t s o)) = Box (t - s/2) s
toBound (Circle (Transform t s@(V2 w h) o)) = Box (t - pure w/2) s
toBound b@(OBB t)
    |b ^. orient  == 0 = let (Transform tr sc _) = t
                          in Box (tr-(sc/2)) sc
    |otherwise =  let (minx, miny, maxx, maxy) = getBounds $ fst $ getPNs b
                  in Box (V2 minx miny) (V2 (maxx-minx) (maxy-miny))
toBound p@(Polygon t points) =
  let (minx, miny, maxx, maxy) = getBounds $ fst $ getPNs p
  in Box (V2 minx miny) (V2  (maxx-minx) (maxy-miny))


--bounding box test (runs in linear time for polygons)
bound :: PhysShape -> PhysShape -> Bool
bound (Box (V2 x1 y1) (V2 w1 h1)) (Box (V2 x2 y2) (V2 w2 h2)) =
  let lbound x1 w1 x2 w2 = x1+w1>=x2 && x2+w2>=x1
  in lbound x1 w1 x2 w2 && lbound y1 h1 y2 h2
bound a b = bound (toBound a) (toBound b)

boundManifold :: PhysShape -> PhysShape -> Maybe Manifold
boundManifold a@(Box (V2 x1 y1) (V2 w1 h1)) b@(Box (V2 x2 y2) (V2 w2 h2)) =
    let lbound x1 w1 x2 w2 = (x1+w1>=x2 && x2+w2>=x1)
        getManifold b1@(Box p1@(V2 x1 y1) d1@(V2 w1 h1)) b2@(Box p2@(V2 x2 y2) d2@(V2 w2 h2)) =
          let mid a b = (a+b)/2
              overlap a1 b1 a2 b2
                    | a1 > a2 && b1 < b2 = if (b1-a2) > (b2 -a1)                      -- 1 is in 2
                                             then  b2 - a1
                                             else a2 - b1
                    | a1 < a2 && b1 > b2 =  - overlap a2 b2 a1 b1   -- 2 is in 1
                    | a1 >=  a2 && b1 >= b2  = b2 - a1                            -- 1 is in front
                    | a1 <=  a2 && b1 <= b2  = a2 - b1                           -- 1 is behind
              xOverlap = overlap x1 (x1+w1) x2 (x2+w2)
              yOverlap = overlap y1 (y1+h1) y2 (y2+h2)
          in if abs xOverlap < abs yOverlap
             then
               let [a,b,c,d] = sort [x1,x1+w1,x2,x2+w2]
                   p
                    | y1<y2 = [(V2 b y1),(V2 c (y2+h2))]
                    | y1>=y2 =[(V2 b (y1+w1)),(V2 c y2)]
               in Manifold p (V2 1 0) (V2 1 0) xOverlap
             else
               let [a,b,c,d] = sort [y1,y1+h1,y2,y2+h2]
                   p
                    | x1<x2 = [(V2 x1 b),(V2 (x2+w2) c)]
                    | x1>=x2 = [(V2 (x1+w1) b),(V2 x2 c)]
               in Manifold p (V2 0 1) (V2 0 1) yOverlap
    in  if lbound x1 w1 x2 w2 && lbound y1 h1 y2 h2
        then Just $ getManifold a b
        else Nothing
boundManifold a b = boundManifold (toBound a) (toBound b)

--avoids square root
distSqrd :: Point -> Point -> Double
distSqrd (V2 x1 y1) (V2 x2 y2) = (x1-x2)^2 + (y1-y2)^2
{-# INLINE distSqrd #-}

epsilon = 0.0001
--runs a seperating axis or seperating hyperplane algorithm
doSat :: [Point] -> [Point] -> [Point] -> [Point] -> Maybe Manifold
doSat points1 axis1 points2 axis2 =
  --projects all the points onto the axis and returns the overlap and vector if applicable
  let overlap a@((a1,b1),p1) b@((a2,b2),p2)
        | a1 > b2 || b1<a2     = Nothing        --not overlapping
        | a1 >= a2 && b1 <= b2 = if (b1-a2) > (b2 -a1)                      -- 1 is in 2
                                 then  Just (b2 - a1,p1,p2)
                                 else  Just (a2 - b1,p1,p2)
        | a1 < a2 && b1 > b2 = (\(a,b,c) -> (negate a,b,c)) <$> overlap b a    -- 2 is in 1
        | a1 >=  a2 && b1 >= b2  = Just (b2 - a1,p1,p2)                            -- 1 is in front
        | a1 <=  a2 && b1 <= b2  = Just (a2 - b1,p1,p2)                           -- 1 is behind
      doAxis :: Point -> [Point]->[Point] ->Bool-> Maybe (Point,Bool,(Double,([Point],[Point]),([Point],[Point])))
      doAxis axis points1 points2 t =
        let vec = normalize axis
            start = ((1/0,-1/0),([],[]))
            fuzzySwap f a b p p' = case a-b of
              x | abs x < epsilon -> p':p
                | x `f` 0 -> p
                | otherwise -> [p']
            f = (\((a,b),(p1,p2)) v -> let x = v `dot` vec in
                 ((min a x, max b x),(fuzzySwap (<) a x p1 v, fuzzySwap (>) b x p2 v))
                )
            a = foldl' f start points1
            b = foldl' f start points2
        in   (vec,t,) <$>  overlap a b
      foldFunc t j v = (\a@(v1,t1,(f1,a1,b1)) b@(v2,t2,(f2,a2,b2)) ->
        if abs f2< abs f1 then b else a ) <$> j <*> doAxis v points1 points2 t
   in let getPoint (v,t,(d,(amin,amax),(bmin,bmax)))
            | t && d <0 =     bmin
            | t && d >=0 =    bmax
            | not t && d<0 =  amax
            | not t && d>=0 = amin
          toManifold a@(v,t,(d,p1,p2)) = Manifold (getPoint a) (v^* (negate $ signum d)) v d
          start = (Just (pure 0 ,True,(1/0,(pure 0,pure 0),(pure 0,pure 0))))
          res =  foldl' (foldFunc False) (foldl' (foldFunc True) start  axis1)   axis2
      in  toManifold <$> res

doSatCircle :: [Point] -> [Point] -> Point -> Double -> Maybe Manifold
doSatCircle points1 axis1 c r =
  --projects all the points onto the axis and returns the overlap and vector if applicable
  let overlap a@((a1,b1),(pa1,pb1)) b@((a2,b2),(pa2,pb2))
        | a1 > b2 || b1<a2     = Nothing        --not overlapping
        | a1 >= a2 && b1 <= b2 = if (b1-a2) > (b2 -a1)                      -- 1 is in 2
                                 then  Just (b2 - a1,(pa1,pb1),(pa2,pb2))
                                 else  Just (a2 - b1,(pa1,pb1),(pa2,pb2))
        | a1 < a2 && b1 > b2 = (\(a,b,c) -> (negate a,b,c)) <$> overlap b a    -- 2 is in 1
        | a1 >=  a2 && b1 >= b2  = Just (b2 - a1,(pa1,pb1),(pa2,pb2))                            -- 1 is in front
        | a1 <=  a2 && b1 <= b2  = Just (a2 - b1,(pa1,pb1),(pa2,pb2))                           -- 1 is behind
      doAxis :: Point -> [Point] ->Bool-> Maybe (Point,Bool,(Double,(Point,Point),(Point,Point)))
      doAxis axis points1 t =
        let vec = normalize axis
            sp = (pure 0, pure 0) ::(Point,Point)
            start = ((1/0,-1/0),sp)
            f = (\((a,b),(p1,p2)) v -> let x = v `dot` vec in
                ((min a x, max b x),(if a > x then v else p1, if b< x then v else p2))
                )
            a =  foldl' f start points1
            cp = c `dot` vec
            b =  ((cp-r,cp+r),(c- (vec ^* r),c+ (vec ^* r)))
        in  (vec,t,) <$>  overlap  a  b
      foldFunc t j v = (\a@(v1,t1,(f1,a1,b1)) b@(v2,t2,(f2,a2,b2)) ->
        if abs f2< abs f1 then b else a ) <$> j <*> doAxis v points1 t
   in let getPoints (v,t,(d,(amin,amax),(bmin,bmax)))
            |  d<0 =  (amax,bmin,v)
            |  d>=0 = (amin,bmax,-v)
          resolvePoint a@(v,t,(d,(amin,amax),(bmin,bmax))) =
            let (pa,pb,n) = getPoints a
                vp = perp v
                (Just (_,_,(_,(pmina,pmaxa),(pminb,pmaxb)))) = doAxis vp points1 True
                minp = min (pmina `dot` vp) (pminb `dot` vp)
                maxp = max (pmaxa `dot` vp) (pmaxb `dot` vp)
                c = (minp+maxp)/2
                pdist p =
                  let a = vp `dot` p
                  in if a<minp || a>maxp then Nothing else Just (abs (c-a),p)
                comp (Just (_,a)) Nothing = a
                comp Nothing (Just (_,a)) = a
                comp (Just (v1,a)) (Just (v2,b)) = if v1<v2 then a else b
              in Manifold [comp (pdist pa)  (pdist pb)] n n (negate $ abs d)
          toManifold a@(v,t,(d,p1,p2)) = resolvePoint a
          start = (Just (pure 0 ,True,(1/0,(pure 0,pure 0),(pure 0,pure 0))))
          res = (foldl' (foldFunc True) start (axis1++(map (c -) points1)))
      in toManifold <$> res

doSatUncurried :: ([Point] , [Point]) -> ([Point] ,[Point]) -> Maybe Manifold
doSatUncurried (points1, axis1) (points2, axis2) = doSat points1 axis1 points2 axis2

collision :: PhysShape -> PhysShape -> Maybe Manifold
collision a@(OBB (Transform tt1 ts1 o1)) b@(OBB (Transform tt2 ts2 o2))
    |otherwise =  doSatUncurried ( getPNs a) (getPNs b)

collision a@(OBB t) b@(Line s) = doSatUncurried (getPNs a) (getPNs b)
collision o@(Line s) l@(OBB t) = rev <$> collision l o

collision a@(OBB t)  (Circle (Transform c (V2 w _) _)) = uncurry doSatCircle (getPNs a) c (w/2)
collision c@(Circle s) o@(OBB t) = rev <$> collision o c

collision a@(OBB t) b@(Polygon s points) = doSatUncurried (getPNs a) (getPNs b)
collision p@(Polygon s points) o@(OBB t) = rev <$> collision o p

collision a@(OBB t) b@(Box p d) = doSatUncurried (getPNs a) (getPNs b)
collision b@(Box p d) o@(OBB t) = rev <$> collision o b

collision (Circle (Transform c (V2 w _) _)) p@(Polygon s points) = uncurry doSatCircle (getPNs p) c (w/2)
collision p@(Polygon s points) c@(Circle t) = rev <$> collision c p

collision (Circle (Transform c (V2 w _) _)) b@(Box p d) = uncurry doSatCircle (getPNs b) c (w/2)
collision b@(Box p d) c@(Circle s) = rev <$> collision c b

collision (Circle (Transform c (V2 w _) _)) l@(Line s) = uncurry doSatCircle (getPNs l) c (w/2)
collision l@(Line s) c@(Circle t) = rev <$> collision c l

collision (Circle (Transform c1 (V2 w1 _) _)) (Circle (Transform c2 (V2 w2 _) _)) =
  let d2 = (c1 - c2) `dot` (c1 - c2)
      rs = ((w1 + w2)/2) ^ 2
      collision = d2 < rs
      n = normalize (c2-c1)
  in if collision then
         Just $ Manifold [((c1+c2) ^/ 2)] n n $ negate (((w1 + w2)/2) - distance c1 c2 )
     else Nothing

--this is an inefficient implementation
collision a@(Line t) b@(Line s) = doSatUncurried (getPNs a) (getPNs b)

collision a@(Line t) b@(Box p d) = doSatUncurried (getPNs a) (getPNs b)
collision b@(Box p d) l@(Line t) = rev <$> collision l b

collision a@(Line t) b@(Polygon s points) = doSatUncurried (getPNs a) (getPNs b)
collision p@(Polygon t points) l@(Line s) = rev <$> collision l p

collision a@(Box p d) b@(Box p0 d0) = boundManifold a b

collision a@(Box p d) b@(Polygon s points) = doSatUncurried (getPNs a) (getPNs b)
collision poly@(Polygon s points) b@(Box p d) = rev <$> collision b poly

collision a@(Polygon t points1) b@(Polygon s points2) = doSatUncurried (getPNs a) (getPNs b)

instance Updateable Transform where
  init = Transform 0 0 0

instance (TypeIxable (HList this) Transform) => Component Transform this e

instance (TypeIxable (HList this) Transform) => HasTransform (HList this) where
  transform = tIx
