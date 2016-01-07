module Data.Simplify
  ( simplified
  , ddx
  , nddx
  , limitSimplify
  ) where

import Data.SAlgebra
import Data.List (sort, (\\))
import Prelude hiding ((+), (*))
import qualified Prelude as P
import Control.Monad.Writer
import Control.Monad.State
import Data.Functor (($>))
import Data.Coerce
import Data.Maybe (fromMaybe)
import Control.Arrow (first)
import Data.Ratio
import qualified Data.Map.Strict as M
import Data.Foldable (foldrM)

-- Filters and accumulates in a way analagous to mapAccumL
filterAccum :: (x -> acc -> (Bool, acc)) -> acc -> [x] -> ([x], acc)
filterAccum f s t = runState (filterM (state . f) t) s

-- Functor composition
infixr 9 <$<
(<$<) :: Functor f => (b -> c) -> (a -> f b) -> a -> f c
(<$<) g f x = g <$> f x

-- Removes the first element which satisfies a predicate, if it is present
remove :: (a -> Bool) -> [a] -> Maybe ([a],a)
remove p = sequence . filterAccum f Nothing where
  f x Nothing | p x = (False, Just x)
              | otherwise = (True, Nothing)
  f _ a = (True, a)

-- Combines the constant terms as a monoid
extractConst :: (Monoid a, Eq a) => [Expr a] -> [Expr a]
extractConst xs | a == mempty = l
                | otherwise = Const a : l where
  (l,a) = runWriter (filterM f xs)
  f (Const e) = tell e $> False
  f e = pure True

-- Returns the most frequent element, and the number of times that it occurs
mostFrequent :: Ord a => [a] -> (Int, a)
mostFrequent (x:xs) = execState (foldrM f (M.singleton x 1) xs) (1,x) where
  f :: Ord a => a -> M.Map a Int -> State (Int, a) (M.Map a Int)
  f e a = do
    (bc,_) <- get
    when (bc < c) (put (c,e))
    pure m
    where (c,m) = increment e a

-- Increments a numeric entry in a map, returns the updated value
increment :: (Num a, Integral a, Ord k) => k -> (M.Map k a) -> (a, M.Map k a)
increment k = first (maybe 1 succ) . M.insertLookupWithKey (const (P.+)) k 1

-- Tries to factorise a sum
factorise :: (Num a, Ord a, Integral a) => [Expr a] -> Either (Expr a) [Expr a]
factorise [] = Left (Const 0)
factorise xs = case mostFrequent (extractProd xs) of
  (1,_) -> Right xs
  (_,f) -> Left (extractFac f xs)

-- Tries to cancel out numbers which are the negation of each other
diff :: (Num a, Eq a, Integral a) => [Expr a] -> Either (Expr a) [Expr a]
diff xs = case remove p xs of
  (Just (ys, Prod (_:[SSum y]))) -> back (y\\ys) (ys\\y)
  _ -> Right xs
  where p (Prod (Const (-1):[SSum _])) = True
        p _ = False
        back []  []  = Left (Const 0)
        back xxs []  = Left (Prod (Const (-1) : [SSum xxs]))
        back []  yys = Right yys
        back xxs yys = Right (Prod (Const (-1) : [SSum xxs]) : yys)


extractFac :: (Num a, Ord a, Integral a) => Expr a -> [Expr a] -> Expr a
extractFac p xs = p * simplify (SSum e) + SSum r where
  (r,e) = filterAccum f [] xs
  f (Prod e) a = case remove (p==) e of
    Nothing       -> (True, a)
    (Just (es,_)) -> (False, Prod es : a)
  f e a | p == e = (False, Const 1 : a)
  f e a = (True, a)

-- Flattens a sum
extractSum :: [Expr a] -> [Expr a]
extractSum = concatMap f where
  f (SSum xs) = extractSum xs
  f e = [e]

-- Flattens a product
extractProd :: [Expr a] -> [Expr a]
extractProd = concatMap f where
  f (Prod xs) = extractProd xs
  f e = [e]

simplify :: (Integral a) => Expr a -> Expr a
-- Unsimplifyable
simplify e@(Var _)   = e
simplify e@(Const _) = e
-- Exponentation
simplify (_  :^: 0)        = Const 1
simplify (a  :^: 1)        = a
simplify ((c :^: b) :^: a) = c :^: (a P.* b)
simplify (Const a :^: b)   | b < 0 = Const 1 :/: Const (a ^ negate b)
                           | otherwise = Const (a ^ b)
-- Division
simplify (Const 0 :/: a      )          = Const 0
simplify (a       :/: Const 1)          = a
simplify (a       :/: b      ) | a == b = Const 1
simplify (a :/: b :^: c)       | a == b = a :^: succ c
simplify (a :^: b :/: c)       | a == c = a :^: pred b
simplify (a :^: b :/: c :^: d) | a == c = a :^: (b P.+ d)
-- Multiplication
simplify (Prod [])             = Const 1
simplify (Prod [e])            = e
simplify (Prod (Const 1 : xs)) = Prod xs
simplify (Prod (Const 0 : xs)) = Const 0
simplify (Prod xs) = Prod ((c extractConst . extractProd . sort . map simplify) xs) where
  c = coerce :: ([Expr (Product a)] -> [Expr (Product a)]) -> [Expr a] -> [Expr a]
-- Addition
simplify (SSum [])             = Const 0
simplify (SSum [e])            = e
simplify (SSum (Const 0 : xs)) = SSum xs
simplify (SSum xs) = either id SSum $ (factorise <=< sort <$< diff . c extractConst . extractSum . map simplify) xs where
  c = coerce :: ([Expr (Sum a)] -> [Expr (Sum a)]) -> [Expr a] -> [Expr a]
-- Catch-all
simplify (a :/: b)  = simplify a :/: simplify b
simplify (a :^: b)  = simplify a :^: b
simplify (Func f e) = Func f (simplify e)

derive :: Num a => Expr a -> Expr a
derive (Var c)   = Const 1
derive (Const c) = Const 0
derive (a :^: b) = Const b * (a :^: (b - 1))
derive (Prod (x:xs)) = x * derive (Prod xs) + Prod xs * derive x
derive (Prod []) = Const 0
derive (SSum xs) = SSum (map derive xs)
derive (a :/: b) = (b * derive a + Const (-1) * (a * derive b)) :/: b :^: 2
derive (Func f e) = d f e * derive e where
  d Cos e = Const (-1) * Func Sin e
  d Sin e = Func Cos e
  d Tan e = Const 1 :/: Func Cos e :^: 2
  d Exp e = Func Exp e
  d Log e = Const 1 :/: e

-- Repeatedly applies a function until it no longer changes its input
converge :: Eq a => (a -> a) -> a -> a
-- converge = until =<< (<*>) (==)
converge f x | x == y = y
             | otherwise = converge f y
             where y = f x

simplified :: (Integral a) => Expr a -> Expr a
simplified = converge simplify

-- Tries to simplify until it reaches its limit, n
limitSimplify :: (Integral a, Show a) => Int -> Expr a -> Either String (Expr a)
limitSimplify 0 e = Left ("Limit reached with:\n" ++ showExpr e ++ "\n" ++ showExpr (simplify e))
limitSimplify n e | e == s = Right s
                  | otherwise = limitSimplify (n-1) s where
                    s = simplify e

ddx :: (Integral a) => Expr a -> Expr a
ddx = simplified . derive

nddx :: (Integral a) => Int -> Expr a -> Expr a
nddx = flip ((!!) . iterate ddx)
