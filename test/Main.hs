module Main where

import GHC.Generics

import Test.SmallCheck
import Test.SmallCheck.Series
import Test.Tasty
import Test.Tasty.SmallCheck

import Data.Int

import Diff

main :: IO ()
main = defaultMain $
    testGroup ""
    [testProperty "patch" $ \ a b -> Just (b :: [ABC]) == diff a b `patch` a]

data ABC = A | B | C deriving (Eq, Show, Generic, Different)
deriving instance Monad m => Serial m ABC
