{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DeriveAnyClass             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE RebindableSyntax           #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
-- |
-- Module      : Data.Array.Accelerate.System.Random.SFC
-- Copyright   : [2020] Trevor L. McDonell
-- License     : BSD3
--
-- Maintainer  : Trevor L. McDonell <trevor.mcdonell@gmail.com>
-- Stability   : experimental
-- Portability : non-portable (GHC extensions)
--
-- Small Fast Carry RNG from the PractRand library <http://pracrand.sourceforge.net>
--

module Data.Array.Accelerate.System.Random.SFC (

  Random, RandomT(..),
  runRandom, evalRandom, evalRandomT,
  RNG(random),

  RandomGen(create, createWith),
  SFC64, SFC32,
  XorShift32,

  Uniform(..),
) where

import Data.Array.Accelerate                                        as A
import Data.Array.Accelerate.Data.Complex                           as A
import Data.Array.Accelerate.Data.Either                            as A
import Data.Array.Accelerate.Data.Bits                              as A

import Control.Monad.Identity
import Control.Monad.State
import Language.Haskell.TH                                          hiding ( Exp )
import Prelude                                                      as P


type Random = RandomT Identity

newtype RandomT m t a = RandomT { runRandomT :: StateT t m a }
  deriving newtype (Functor, Applicative, Monad)

-- | Unwrap a random monad computation as a function, returning both the
-- generated value and the new generator state.
--
runRandom :: t -> Random t a -> (a, t)
runRandom gen r = runIdentity $ runStateT (runRandomT r) gen

-- | Evaluate a computation given the initial generator state and return
-- the final value, discarding the final state.
--
evalRandom :: t -> Random t a -> a
evalRandom gen = runIdentity . evalRandomT gen

-- | Evaluate a computation with the given initial generator state and
-- return the final value, discarding the final state.
--
evalRandomT :: (Monad m) => t -> RandomT m t a -> m a
evalRandomT gen r = evalStateT (runRandomT r) gen


-- | The class of types that can be used to generate random data with.
--
class RNG t where
  type Output t a

  -- | Generate random values. When generating an array the size of the array is
  -- determined by the generator state that was built using 'create' or
  -- 'createWith'.
  --
  random :: (Uniform a, Monad m) => RandomT m t (Output t a)

instance (Shape sh, RandomGen g) => RNG (Acc (Array sh g)) where
  type Output (Acc (Array sh g)) a = Acc (Array sh a)

  random = RandomT $ state (A.unzip . A.map uniform)

instance RandomGen g => RNG (Exp g) where
  type Output (Exp g) a = Exp a

  random = RandomT $ state (unlift . uniform)


first :: (Elt a, Elt b, Elt c) => (Exp a -> Exp b) -> Exp (a, c) -> Exp (b, c)
first f (T2 a b) = T2 (f a) b


-- * Pseudo-random number generators

-- | An interface to pseudo-random number generators.
--
class Elt g => RandomGen g where
  {-# MINIMAL create,createWith,(genWord32|genWord64) #-}

  -- | The type of the initial seed used while creating the PRNG.
  --
  type Seed g

  -- | Create a new generator state using default seeds (the array index).
  --
  -- You'll probably get better random numbers by using 'createWith' and
  -- seeding the initial state from a better source of entropy. For example,
  -- we can use the 'mwc-random-accelerate' package to generate the seed
  -- vector using the system's source of random numbers:
  --
  -- > gen <- createWith . use <$> MWC.randomArray MWC.uniform (Z :. 100)
  --
  create :: Shape sh => Exp sh -> Acc (Array sh g)

  -- | Create a new generator state using the given seed vector.
  --
  createWith
      :: Shape sh
      => Acc (Array sh (Seed g))
      -> Acc (Array sh g)

  -- | Generate a uniformly distributed 'Word32'.
  --
  genWord32 :: Exp g -> Exp (Word32, g)
  genWord32 = first A.fromIntegral . genWord64

  -- | Generate a uniformly distributed 'Word64'.
  --
  genWord64 :: Exp g -> Exp (Word64, g)
  genWord64 g =
      let T2 l32 g'  = genWord32 g
          T2 u32 g'' = genWord32 g'
      in  T2 ((A.fromIntegral u32 `unsafeShiftL` 32) .|. A.fromIntegral l32) g''


-- ** SFC64
--
-- The Small Fast Carry RNG (64-bit)
--
-- Stolen from PractRand v0.95.
--

data SFC a = SFC_ a a a a
  deriving (Generic, Elt)

pattern SFC :: Elt a => Exp a -> Exp a -> Exp a -> Exp a -> Exp (SFC a)
pattern SFC a b c counter = Pattern (a, b, c, counter)
{-# COMPLETE SFC #-}

type SFC64 = SFC Word64

instance RandomGen SFC64 where
  type Seed SFC64 = (Word64, Word64, Word64)

  create sh = A.map seedFast $ enumFromN sh 0
   where
    seedFast :: Exp Word64 -> Exp SFC64
    seedFast s = A.snd $ while
      (\(T2 i _) -> i A.< 8)
      (\(T2 i g) -> let T2 _ g' = genWord64 g in T2 (i + 1) g')
      (T2 (0 :: Exp Int) (SFC s s s 1))

  createWith = A.map (\(T3 a b c) -> seed a b c)
   where
    seed :: Exp Word64 -> Exp Word64 -> Exp Word64 -> Exp SFC64
    seed a b c = A.snd $ while
      (\(T2 i _) -> i A.< 18)
      (\(T2 i g) -> let T2 _ g' = genWord64 g in T2 (i + 1) g')
      (T2 (0 :: Exp Int) (SFC a b c 1))

  genWord64 (SFC a b c counter) =
    let tmp      = a + b + counter
        counter' = counter + 1
        a'       = b `xor` (b `unsafeShiftR` 11)
        b'       = c + (c `unsafeShiftL` 3)
        c' = ((c `unsafeShiftL` 24) .|. (c `unsafeShiftR` (64 - 24))) + tmp
    in  T2 tmp (SFC a' b' c' counter')


-- ** SFC32
--
-- Same as 'SFC64', but using 32-bit integers for its internal state.
--

type SFC32 = SFC Word32

instance RandomGen SFC32 where
  type Seed SFC32 = (Word32, Word32, Word32)

  create sh = A.map seedFast $ enumFromN sh 0
   where
    seedFast :: Exp Word64 -> Exp SFC32
    seedFast s = A.snd $ while
      (\(T2 i _) -> i A.< 8)
      (\(T2 i g) -> let T2 _ g' = genWord32 g in T2 (i + 1) g')
      (T2 (0 :: Exp Int) (SFC 0 (A.fromIntegral s) (A.fromIntegral $ s `unsafeShiftR` 32) 1))

  createWith = A.map (\(T3 a b c) -> seed a b c)
   where
    seed :: Exp Word32 -> Exp Word32 -> Exp Word32 -> Exp SFC32
    seed a b c = A.snd $ while
      (\(T2 i _) -> i A.< 15)
      (\(T2 i g) -> let T2 _ g' = genWord32 g in T2 (i + 1) g')
      (T2 (0 :: Exp Int) (SFC a b c 1))

  genWord32 (SFC a b c counter) =
    let tmp      = a + b + counter
        counter' = counter + 1
        a'       = b `xor` (b `unsafeShiftR` 9)
        b'       = c + (c `unsafeShiftL` 3)
        c' = ((c `unsafeShiftL` 21) .|. (c `unsafeShiftR` (32 - 21))) + tmp
    in  T2 tmp (SFC a' b' c' counter')


-- ** Xorshift
--
-- A 32-bit xorshift pseudo-random number generator. The implementation is
-- faster than the SFC family of PRNGs while using less memory, but the
-- generated numbers will be of much lower quality.

data XorShift a = XorShift_ a
  deriving (Generic, Elt)

pattern XorShift :: Elt a => Exp a -> Exp (XorShift a)
pattern XorShift state = Pattern state
{-# COMPLETE XorShift #-}

type XorShift32 = XorShift Word32

instance RandomGen XorShift32 where
  type Seed XorShift32 = Word32

  create sh = A.map XorShift $ enumFromN sh 0

  createWith = A.map XorShift

  genWord32 (XorShift state) =
    let state'    = state `xor` (state `unsafeShiftL` 13)
        state''   = state' `xor` (state' `unsafeShiftR` 17)
        nextState = state'' `xor` (state'' `unsafeShiftL` 5)
    in  T2 nextState (XorShift nextState)


-- * Distributions

-- | The class of types for which we can generate random variates. Integral
-- variates are generated in the full range, floating point variates are in
-- the range [0,1].
--
class Elt a => Uniform a where
  uniform :: RandomGen g => Exp g -> Exp (a, g)

-- TODO: Are redundant @A.fromIntegrals@ optimized away? For example:
--
--       > A.fromIntegral (A.fromIntegral (x :: Exp Word32) :: Exp Word16) :: Exp Word8
instance Uniform Bool   where uniform = first A.even . genWord32
-- TODO: How does Accelerate handle word sizes in PTX code? Can we always assume
--       the word size is 64 bits?
instance Uniform Int    where uniform = first A.fromIntegral . genWord64
instance Uniform Int8   where uniform = first A.fromIntegral . genWord32
instance Uniform Int16  where uniform = first A.fromIntegral . genWord32
instance Uniform Int32  where uniform = first A.fromIntegral . genWord32
instance Uniform Int64  where uniform = first A.fromIntegral . genWord64
-- TODO: Same as the above
instance Uniform Word   where uniform = first A.fromIntegral . genWord64
instance Uniform Word8  where uniform = first A.fromIntegral . genWord32
instance Uniform Word16 where uniform = first A.fromIntegral . genWord32
instance Uniform Word32 where uniform = genWord32
instance Uniform Word64 where uniform = genWord64

instance Uniform Half where
  uniform = first toFloating . uniform @Float

instance Uniform Float where
  uniform s =
    let cvt :: Exp Word32 -> Exp Float
        cvt v = A.fromIntegral v * (1 / A.fromIntegral (maxBound :: Exp Word32))
     in
     first cvt (genWord32 s)

instance Uniform Double where
  uniform s =
    let cvt :: Exp Word64 -> Exp Double
        cvt v = A.fromIntegral v * (1 / A.fromIntegral (maxBound :: Exp Word64))
     in
     first cvt (genWord64 s)

instance Uniform a => Uniform (Complex a) where
  uniform s0 =
    let T2 r s1 = uniform s0
        T2 c s2 = uniform s1
     in T2 (r ::+ c) s2

instance Uniform a => Uniform (Maybe a) where
  uniform s0 =
    let T2 c s1 = uniform @Bool s0
     in if c
           then T2 Nothing_ s1
           else first Just_ (uniform s1)

instance (Uniform a, Uniform b) => Uniform (Either a b) where
  uniform s0 =
    let T2 c s1 = uniform @Bool s0
     in if c
           then first Left_  (uniform s1)
           else first Right_ (uniform s1)

runQ $ do
  let
      tupT :: [TypeQ] -> TypeQ
      tupT [t] = t
      tupT tup =
        let n = P.length tup
         in foldl (\ts t -> [t| $ts $t |]) (tupleT n) tup


      mkTup :: Int -> Q [Dec]
      mkTup n =
        let
            xs          = [ mkName ('x':show i) | i <- [0 .. n-1] ]
            ss          = [ mkName ('s':show i) | i <- [0 .. n]   ]
            cst         = tupT (P.map (\x -> [t| Uniform $(varT x) |]) xs)
            res         = tupT (P.map varT xs)
            step x s s' = valD [p| T2 $(varP x) $(varP s') |] (normalB [| uniform $(varE s) |]) []
            steps       = P.zipWith3 step xs ss (P.tail ss)
            r           = [| T2 $(appsE (conE (mkName ('T':show n)) : P.map varE xs)) $(varE (last ss)) |]
         in
         [d| instance ($cst) => Uniform $res where
               uniform $(varP (P.head ss)) =
                 $(letE steps r)
           |]
  --
  concat <$> mapM mkTup [2..16]
