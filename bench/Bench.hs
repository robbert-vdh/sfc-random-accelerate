{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE NumericUnderscores #-}
{-# LANGUAGE TypeApplications #-}

import           Criterion.Main
import           Data.Array.Accelerate         as A
import qualified Data.Array.Accelerate.LLVM.Native
                                               as CPU
import qualified Data.Array.Accelerate.LLVM.PTX
                                               as PTX
import           Prelude                       as P
import qualified System.Random.MWC             as Rng

-- Convert a Word64 as generated by a PRNG directly to a @[0, 1]@ float value.
word64ToFloat :: Exp Word64 -> Exp Float
word64ToFloat n =
    A.fromIntegral n * (1 / A.fromIntegral (maxBound :: Exp Word64))

-- Convert a Word64 as generated by a PRNG to a @[0, 1]@ float value by first
-- casting to a Word32.
word64To32ToFloat :: Exp Word64 -> Exp Float
word64To32ToFloat n =
    A.fromIntegral n' * (1 / A.fromIntegral (maxBound :: Exp Word32))
    where n' = A.fromIntegral @Word64 @Word32 n

-- | Run the benchmark using the specified @run1@ implementation.
--
-- In this benchmark we'll compare 'word64ToFloat' to `word64To32ToFloat` by
-- producing an input vector of Word64 values, extrapolating some more values
-- from those, converting all values to floats using the functions defined
-- above, and then summing the results to a single floats. The extrapolation and
-- summing steps were added to reduce the data transfer overhead.
--
-- FIXME: I couldn't get this to type check with @Afunction@ and @AfunctionR@.
benchFor
    :: (  (Acc (Vector Word64) -> Acc (Scalar Float))
       -> (Vector Word64 -> Scalar Float)
       )
    -> String
    -> Benchmark
benchFor run1 name = bgroup name $ P.map
    (\n -> env (genData n) $ \xs -> bgroup ("input size " P.++ show n)
        $ P.map (\(f, fName) -> bench fName (nf f xs)) functions
    )
    [1_000_000, 10_000_000, 100_000_000]
  where
    !functions =
        [ (run1 $ dewit word64ToFloat    , "Word64 -> Float")
        , (run1 $ dewit word64To32ToFloat, "Word64 -> Word32 -> Float")
        ]

    -- | To somewhat reduce the overhead of data transfer we'll use 'generate'
    -- to produce some additional values, and then we'll sum the results to a
    -- single 'Float' value.
    dewit
        :: (Exp Word64 -> Exp Float)
        -> Acc (Vector Word64)
        -> Acc (Scalar Float)
    dewit f xs = A.sum . A.flatten . A.map f $ generate
        (I2 (size xs) (100 :: Exp Int))
        (\(I2 y x) -> (xs A.!! y) + (A.fromIntegral x))

    -- | Generate @n@ random 'Word64' values.
    genData :: Int -> IO (Vector Word64)
    genData n = Rng.createSystemRandom
        >>= \rng -> fromFunctionM (Z :. n) (const $ Rng.uniform rng)

main :: IO ()
main = defaultMain [benchFor CPU.runN "CPU", benchFor PTX.runN "GPU"]
