{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}

module Diff (Different (..)) where

import Control.Monad (guard)
import Data.Function (on)
import Data.Void
import GHC.Generics
import Util ((∘∘))
import qualified Util.Enum as Util

import Data.Functor.Compose
import Data.Functor.Const
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.Int
import Data.List.NonEmpty (NonEmpty (..))
import Data.Proxy (Proxy (..))
import Data.Semigroup (Arg (..))
import Data.Monoid (Alt (..))
import Data.Version
import Data.Word
import Numeric.Natural (Natural)

class Different a where
    type Diff a
    type Diff a = Diff (Rep a ())

    diff :: a -> a -> Diff a
    default diff :: (Generic a, Different (Rep a ()), Diff a ~ Diff (Rep a ())) => a -> a -> Diff a
    diff = diff `on` (from :: a -> Rep a ())

    patch :: Diff a -> a -> Maybe a
    default patch :: (Generic a, Different (Rep a ()), Diff a ~ Diff (Rep a ())) => Diff a -> a -> Maybe a
    patch δ = fmap to . patch δ . (from :: a -> Rep a ())

    merge :: Proxy a -> Diff a -> Diff a -> Maybe (Diff a)
    default merge :: (Different (Rep a ()), Diff a ~ Diff (Rep a ())) => Proxy a -> Diff a -> Diff a -> Maybe (Diff a)
    merge _ = merge (Proxy :: Proxy (Rep a ()))

instance Different (V1 a) where
    type Diff (V1 a) = Void
    diff = \ case
    patch = \ case
    merge _ = \ case

instance Different (U1 a) where
    type Diff (U1 a) = ()
    diff U1 U1 = ()
    patch () = Just
    merge _ () () = Just ()

deriving newtype instance Different a => Different (Par1 a)
deriving newtype instance Different (f a) => Different (Rec1 f a)
deriving newtype instance Different c => Different (K1 i c a)
deriving newtype instance Different (f a) => Different (M1 i c f a)

instance (Different (f a), Eq (f a),
          Different (g a), Eq (g a)) => Different ((f :+: g) a) where
    type Diff ((f :+: g) a) = SumDiff (f a) (g a)
    diff (L1 a) (L1 b) = DiffL (diff a b)
    diff (R1 a) (R1 b) = DiffR (diff a b)
    diff (L1 a) (R1 b) = LR a b
    diff (R1 a) (L1 b) = RL a b
    patch (DiffL δ) (L1 a) = L1 <$> patch δ a
    patch (DiffR δ) (R1 a) = R1 <$> patch δ a
    patch (LR a b) (L1 a') | a == a' = Just (R1 b)
    patch (RL a b) (R1 a') | a == a' = Just (L1 b)
    patch _ _ = Nothing
    merge _ = mergeSumDiff

instance (Different (f a), Different (g a)) => Different ((f :*: g) a) where
    type Diff ((f :*: g) a) = (Diff (f a), Diff (g a))
    diff (a₁ :*: a₂) (b₁ :*: b₂) = (diff a₁ b₁, diff a₂ b₂)
    patch (δ₁, δ₂) (a₁ :*: a₂) = (:*:) <$> patch δ₁ a₁ <*> patch δ₂ a₂
    merge _ (δ₁₁, δ₁₂) (δ₂₁, δ₂₂) = (,) <$> merge (Proxy :: Proxy (f a)) δ₁₁ δ₂₁ <*> merge (Proxy :: Proxy (g a)) δ₁₂ δ₂₂

deriving newtype instance (Different (f (g a))) => Different ((f :.: g) a)

data SumDiff a b = DiffL (Diff a)
                 | DiffR (Diff b)
                 | LR a b
                 | RL b a

deriving instance (Eq a, Eq b, Eq (Diff a), Eq (Diff b)) => Eq (SumDiff a b)
deriving instance (Read a, Read b, Read (Diff a), Read (Diff b)) => Read (SumDiff a b)
deriving instance (Show a, Show b, Show (Diff a), Show (Diff b)) => Show (SumDiff a b)

------------------------

deriving instance Different Void
deriving instance Different Bool
deriving instance Different Ordering

instance Different Integer where
    type Diff Integer = Integer
    diff = flip (-)
    patch = Just ∘∘ (+)
    merge _ = Just ∘∘ (+)

instance Different Natural where
    type Diff Natural = Integer
    diff = flip (-) `on` fromIntegral
    patch δ a = fromIntegral b <$ guard (b >= 0)
      where b = fromIntegral a + δ
    merge _ = Just ∘∘ (+)

instance Different Int where
    type Diff Int = Int
    diff = flip (-)
    patch = Just ∘∘ (+)
    merge _ = Just ∘∘ (+)

instance Different Word where
    type Diff Word = Word
    diff = flip (-)
    patch = Just ∘∘ (+)
    merge _ = Just ∘∘ (+)

instance Different Int8 where
    type Diff Int8 = Int8
    diff = flip (-)
    patch = Just ∘∘ (+)
    merge _ = Just ∘∘ (+)

instance Different Word8 where
    type Diff Word8 = Word8
    diff = flip (-)
    patch = Just ∘∘ (+)
    merge _ = Just ∘∘ (+)

instance Different Int16 where
    type Diff Int16 = Int16
    diff = flip (-)
    patch = Just ∘∘ (+)
    merge _ = Just ∘∘ (+)

instance Different Word16 where
    type Diff Word16 = Word16
    diff = flip (-)
    patch = Just ∘∘ (+)
    merge _ = Just ∘∘ (+)

instance Different Int32 where
    type Diff Int32 = Int32
    diff = flip (-)
    patch = Just ∘∘ (+)
    merge _ = Just ∘∘ (+)

instance Different Word32 where
    type Diff Word32 = Word32
    diff = flip (-)
    patch = Just ∘∘ (+)
    merge _ = Just ∘∘ (+)

instance Different Int64 where
    type Diff Int64 = Int64
    diff = flip (-)
    patch = Just ∘∘ (+)
    merge _ = Just ∘∘ (+)

instance Different Word64 where
    type Diff Word64 = Word64
    diff = flip (-)
    patch = Just ∘∘ (+)
    merge _ = Just ∘∘ (+)

instance Different Char where
    type Diff Char = Int
    diff = flip (-) `on` fromEnum
    patch δ x = Util.toEnumMay . fromIntegral $ fromEnum x + δ
    merge _ _ _ = Nothing

deriving instance Different Version

deriving newtype instance Different a => Different (Identity a)
deriving instance (Eq a, Different a) => Different (Maybe a)
deriving instance (Eq a, Different a) => Different [a]
deriving instance (Eq a, Different a) => Different (NonEmpty a)

deriving instance (Eq a, Different a, Eq b, Different b) => Different (Either a b)

deriving instance Different ()
deriving instance (Different a, Different b) => Different (a, b)
deriving instance (Different a, Different b, Different c) => Different (a, b, c)
deriving instance (Different a, Different b, Different c, Different d) => Different (a, b, c, d)
deriving instance (Different a, Different b, Different c, Different d, Different e) => Different (a, b, c, d, e)
deriving instance (Different a, Different b, Different c, Different d, Different e, Different f) => Different (a, b, c, d, e, f)
deriving instance (Different a, Different b, Different c, Different d, Different e, Different f, Different g) => Different (a, b, c, d, e, f, g)

deriving newtype instance (Different (f a)) => Different (Alt f a)
deriving instance (Different a, Different b) => Different (Arg a b)

deriving instance Different (Proxy a)
deriving newtype instance Different a => Different (Const a b)

deriving newtype instance Different (f (g a)) => Different (Compose f g a)
deriving instance (Different (f a), Different (g a)) => Different (Product f g a)
deriving instance (Different (f a), Eq (f a), Different (g a), Eq (g a)) => Different (Sum f g a)

mergeSumDiff :: ∀ a b . (Different a, Different b) => SumDiff a b -> SumDiff a b -> Maybe (SumDiff a b)
mergeSumDiff = curry $ \ case
     (DiffL δ₁, DiffL δ₂) -> DiffL <$> merge (Proxy :: Proxy a) δ₁ δ₂
     (DiffR δ₁, DiffR δ₂) -> DiffR <$> merge (Proxy :: Proxy b) δ₁ δ₂
     (LR a b, DiffR δ) -> LR a <$> patch δ b
     (DiffR δ, LR a b) -> LR a <$> patch δ b
     (RL b a, DiffL δ) -> RL b <$> patch δ a
     (DiffL δ, RL b a) -> RL b <$> patch δ a
     _ -> Nothing
