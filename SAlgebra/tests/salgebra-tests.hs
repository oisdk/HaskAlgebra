{-# LANGUAGE TemplateHaskell #-}

module Main where

import Test.QuickCheck
import qualified Test.QuickCheck.Property as P
import Data.SAlgebra
import Data.Simplify
import Data.Functor (($>))
import Data.Function (on)
import Control.Monad
import System.Exit
import Control.Exception
import Prelude hiding ((+), (*))
import Data.Coerce
import Control.Applicative hiding (Const)
import Data.Ratio

instance Arbitrary EFunc where
  arbitrary = arbitraryBoundedEnum

instance (Num a, Arbitrary a, Ord a, Show a) => Arbitrary (Expr a) where
  arbitrary = sized nExpr where
    nExpr n | n <= 0 = liftM Const arbitrary
            | otherwise = oneof [ liftM2 Func arbitrary nest
                                , liftM Const (suchThat arbitrary (1000>))
                                , liftM Var (pure <$> elements ['a'..'z'])
                                , liftM2 (:^:) nest arbitrary
                                , liftM2 (:/:) nest nest
                                , liftM Prod (listOf1 nest)
                                , liftM SSum (listOf1 nest)
                                ] where
                                  nest = nExpr (n `div` 8)
  shrink (Var _)    = []
  shrink (Func _ e) = [e]
  shrink (a :^: b)  = [a]
  shrink (Prod xs)  = xs
  shrink (a :/: b)  = [a,b]
  shrink (SSum xs)  = xs
  shrink (Const a)  = []

newtype ConstExpr a = ConstExpr { getConstExpr :: Expr a } deriving (Show, Eq)

instance (Num a, Arbitrary a, Ord a, Show a) => Arbitrary (ConstExpr a) where
  arbitrary = liftM ConstExpr (liftM2 subIn arbitrary arbitrary)
    
prop_ExampleNegate :: Property
prop_ExampleNegate = once (simplified (e + Const (-1) * e) == Const 0) where
  e = SSum $ map Const [0, 1, 1]
  
prop_NegateZero :: Expr Integer -> P.Property
prop_NegateZero = sSameResult (const (Const 0)) (\e -> e + (Const (-1) * e))

prop_SampleDeriv :: Property
prop_SampleDeriv = once (nddx 4 e == simplified (Const (-2520) * x :^: 3 + Const (-144))) where
  e :: Expr Int
  e = (Const (-3) * x :^: 7) + (Const (-6) * x :^: 4) + (Const 8 * x :^: 3) + (Const (-12) * x) + (Const 18)
  x = Var "x"

prop_Eval :: ConstExpr Integer -> P.Property
prop_Eval = P.ioProperty . catchZeroDenom  . P.liftBool . (liftA2 comp cEval (cEval . cSimp)) where
  cEval (ConstExpr e) = eval e
  cSimp (ConstExpr e) = ConstExpr (simplified e)
  comp (Right a) (Right b) = a == b
  comp _ _ = True

prop_ExampleAssociativeAdd :: P.Property
prop_ExampleAssociativeAdd = prop_AssociativeAdd (Var "c") (Var "a") c where
  c = Const (-1) * (Var "b") + Var "b"

prop_AssociativeAdd :: Expr Integer -> Expr Integer -> Expr Integer -> P.Property
prop_AssociativeAdd = sSameResult3 (\a b c -> (a + b) + c) (\a b c -> a + (b + c))

prop_CommuntitiveAdd :: Expr Integer -> Expr Integer -> P.Property
prop_CommuntitiveAdd = sSameResult2 (+) (flip (+))

prop_AssociativeMult :: Expr Integer -> Expr Integer -> Expr Integer -> P.Property
prop_AssociativeMult = sSameResult3 (\a b c -> (a * b) * c) (\a b c -> a * (b * c))

prop_CommuntitiveMult :: Expr Integer -> Expr Integer -> P.Property
prop_CommuntitiveMult = sSameResult2 (*) (flip (*))

sameResult :: Eq a => (b -> a) -> (b -> a) -> b -> Bool
sameResult = liftA2 (==)
 
catchZeroDenom :: P.Result -> IO P.Result
catchZeroDenom = P.protect g . evaluate where
  g e = case (fromException e :: Maybe ArithException) of
    Just RatioZeroDenominator -> P.rejected
    Just DivideByZero -> P.rejected
    _ -> P.exception (show e) e

sSameResult :: (Integral a, Show a) => (b -> Expr a) -> (b -> Expr a) -> b -> P.Property
sSameResult f g x = P.ioProperty (catchZeroDenom (sSameResult' f g x))
  
sSameResult' :: (Integral a, Show a) => (b -> Expr a) -> (b -> Expr a) -> b -> P.Result
sSameResult' = liftM2 (on comp (limitSimplify 10000)) where
  comp (Left s) _ = P.failed { P.reason = s }
  comp _ (Left s) = P.failed { P.reason = s }
  comp (Right a) (Right b) | a == b = P.succeeded
                           | otherwise = P.failed { P.reason = '\n' : showExpr a ++ "\n" ++ showExpr b ++ "\n" }

sSameResult2 :: (Integral a, Show a) => (b -> c -> Expr a) -> (b -> c -> Expr a) -> b -> c -> P.Property
sSameResult2 = liftM2 sSameResult

sSameResult3 :: (Integral a, Show a) => (b -> c -> d -> Expr a) -> (b -> c -> d -> Expr a) -> b -> c -> d -> P.Property
sSameResult3 = liftM2 sSameResult2

quickCheckExit :: Testable prop => prop -> IO Result
quickCheckExit = resultExit <=< quickCheckResult where
  resultExit r@(Success{}) = pure r
  resultExit r = exitFailure $> r

return []
runTests = $forAllProperties quickCheckExit

main = runTests
