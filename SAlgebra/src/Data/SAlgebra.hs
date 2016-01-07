module Data.SAlgebra
  ( Expr(..)
  , EFunc(..)
  , subIn
  , showExpr
  , (+), (*)
  , eval
  ) where

import Data.Monoid
import Data.List (intercalate)
import Data.Traversable (traverse)
import Data.Ratio
import Prelude hiding ((+), (*), (/), (^))
import qualified Prelude as P

infixl 5 :/:
infixr 6 :^:
infixl 3 +
infixl 4 *
infixl 5 /
infixr 6 ^

data Expr a = Var Char
            | Func EFunc (Expr a)
            | (Expr a) :^: a
            | (Expr a) :/: (Expr a)
            | Prod [Expr a]
            | SSum [Expr a]
            | Const a
            deriving (Eq, Ord)
            
(^) = (:^:)
(/) = (:/:)

eval :: Integral a => Expr a -> Either Char (Ratio a)
eval (Const a) = Right (a % 1)
eval (Var c) = Left c
eval (a :^: b) = (^^ b) <$> eval a
eval (a :/: b) = (P./) <$> eval a <*> eval b
eval (Prod xs) = product <$> traverse eval xs
eval (SSum xs) = sum <$> traverse eval xs
eval (Func f e) = Left 'f'

(*) :: Expr a -> Expr a -> Expr a
Prod xs * Prod ys = Prod (xs ++ ys)
e * Prod xs       = Prod (e:xs)
Prod xs * e       = Prod (e:xs)
a * b             = Prod [a,b]

(+) :: Expr a -> Expr a -> Expr a
SSum xs + SSum ys = SSum (xs ++ ys)
e + SSum xs       = SSum (e:xs)
SSum xs + e       = SSum (e:xs)
a + b             = SSum [a,b]

data EFunc = Cos | Sin | Tan | Exp | Log deriving (Eq, Show, Ord, Enum, Bounded)

subIn :: (Char -> a) -> Expr a -> Expr a
subIn f (Var c) = Const (f c)
subIn f (Func g e) = Func g (subIn f e)
subIn _ (Const c) = Const c
subIn f (a :^: b) = subIn f a ^ b
subIn f (a :/: b) = subIn f a / subIn f b
subIn f (Prod xs) = Prod (map (subIn f) xs)
subIn f (SSum xs) = SSum (map (subIn f) xs)

prec :: Expr a -> Int
prec (Func _ _) = 8
prec (Var   _ ) = 7
prec (Const _ ) = 7
prec (_ :^: _ ) = 5
prec (_ :/: _ ) = 4
prec (Prod  _ ) = 3
prec (SSum  _ ) = 2

condBr :: Show a => Int -> Expr a -> String
condBr n e | n > prec e = "(" ++ show e ++ ")"
           | otherwise = show e

instance Show a => Show (Expr a) where
  show (Func f e) = show f ++ "(" ++ show e ++ ")"
  show (Const a) = show a
  show (Var c) = [c]
  show e@(a :^: b) = condBr n a ++ "^" ++ show b where n = prec e
  show e@(a :/: b) = condBr n a ++ " / " ++ condBr n b where n = prec e
  show e@(Prod xs) = (intercalate " * " . map (condBr n)) xs where n = prec e
  show e@(SSum xs) = (intercalate " + " . map (condBr n)) xs where n = prec e
  
showExpr :: Show a => Expr a -> String
showExpr (Func f e) = show f ++ "(" ++ showExpr e ++ ")"
showExpr (Const a) = show a 
showExpr (Var c) = [c]
showExpr (a :^: b) = "(" ++ showExpr a ++ "^" ++ show b ++ ")"
showExpr (a :/: b) = "(" ++ showExpr a ++ " / " ++ showExpr b ++ ")"
showExpr (Prod xs) = "P((" ++ (intercalate ")(" . map showExpr) xs ++ "))"
showExpr (SSum xs) = "S((" ++ (intercalate ") + (" . map showExpr) xs ++ "))"


