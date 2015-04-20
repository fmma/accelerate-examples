{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE TypeFamilies        #-}

module Test.Prelude.Sequencing (

  test_sequences

) where

import Prelude hiding ( zip, zipWith, fst, snd, map, fromIntegral, sum, product, replicate, (++) )
import qualified Prelude                                        as P
import Data.Label
import Data.Maybe
import Data.Typeable
import Test.QuickCheck hiding ( generate, collect )
import Test.Framework
import Test.Framework.Providers.QuickCheck2

import Config
import Test.Base
import QuickCheck.Arbitrary.Array
import Data.Array.Accelerate.Examples.Internal                  hiding ( Permute )
import Data.Array.Accelerate                                    as Acc
import Data.Array.Accelerate.Array.Sugar                        hiding ( shape )
import Data.Array.Accelerate.Smart                              ( Unfolded(..), PreArrayOp(..), PreAcc( ArrayOp ), PreSeq( SeqOp ), Acc(..), Seq(..) )
import qualified Data.Array.Accelerate.Array.Sugar              as Sugar

toSeq' :: (Shape sh, Elt a)
          => Acc (Array (sh :. Int) a)
          -> Seq [Array sh a]
toSeq' = toSeq (Any :. Split)

iota :: Int -> Acc (Vector Int)
iota n = generate (index1 (constant n)) unindex1

units :: Int -> Acc (Vector ())
units n = generate (index1 (constant n)) (const (constant ()))

idSequence :: (Shape sh, Elt a, Slice sh) => Acc (Array (sh :. Int) a) -> Acc (Array (sh :. Int) a)
idSequence xs = reshape (shape xs) $ collect
  $ fromSeq
  $ toSeq (Divide :. All) xs


idSequenceRef :: (Shape sh, Elt a) => (Array (sh :. Int) a) -> (Array (sh :. Int) a)
idSequenceRef = id

sumMaxSequence :: (Elt a, IsBounded a, IsNum a) => Acc (Vector a) -> Acc (Scalar a, Scalar a)
sumMaxSequence xs = collect $
  let xs' = toSeq' xs
  in lift ( foldSeq (+) 0 xs'
          , foldSeq max minBound xs')

sumMaxSequenceRef :: (Elt a, Ord a, Bounded a, Num a) => Vector a -> (Scalar a, Scalar a)
sumMaxSequenceRef xs = ( fromList Z . (:[]) . P.sum     . toList $ xs
                   , fromList Z . (:[]) . P.foldl (P.max) minBound . toList $ xs)

scatterSequence :: (Elt a, IsNum a) => Acc (Vector a, Vector (Int, a)) -> Acc (Vector a)
scatterSequence input = collect
  $ foldSeqFlatten f (afst input)
  $ toSeq' (asnd input)
  where
    f xs' upd =
      let (to, ys) = Acc.unzip upd
      in permute (+) xs' (index1 . (`mod` Acc.size (afst input)) . (to Acc.!)) ys

scatterSequenceRef :: (Elt a, IsNum a) => (Vector a, Vector (Int, a)) -> Vector a
scatterSequenceRef (vec, vec_upd) =
  let xs = toList vec
      n = P.length xs
      updates = toList vec_upd
      f xs' (i, x) = [ if j == i `P.mod` n then x P.+ y else y | (j, y) <- P.zip [0..] xs']
      ys = P.foldl f xs updates
  in fromList (Z :. n) ys

testSeqMap :: (Elt a, Elt b, Shape sh, Shape sh')
      => Backend 
      -> (Unfolded Seq (Array sh' b) -> PreArrayOp (Unfolded Seq) Exp (Array sh a))
      -> Exp sh'
      -> [Array sh' b]
      -> [Array sh  a]
testSeqMap backend op sh' = streamOut backend . Seq . SeqOp . op . Unfolded . streamIn sh'

testSeqMapRef :: (Elt a, Elt b, Shape sh, Shape sh')
      => Backend 
      -> (Acc (Array sh' b) -> PreArrayOp Acc Exp (Array sh a)) 
      -> [Array sh' b]  
      -> [Array sh  a]
testSeqMapRef backend op = P.map (run1 backend (Acc . ArrayOp . op))

testSeqZipWith :: (Elt a, Elt b, Elt c, Shape sh, Shape sh', Shape sh'')
      => Backend 
      -> (Unfolded Seq (Array sh' b) -> Unfolded Seq (Array sh'' c) -> PreArrayOp (Unfolded Seq) Exp (Array sh a))
      -> Exp sh'
      -> Exp sh''
      -> [Array sh'  b]
      -> [Array sh'' c]
      -> [Array sh  a]
testSeqZipWith backend op sh' sh'' xs ys = streamOut backend . Seq . SeqOp $ op (Unfolded (streamIn sh' xs)) (Unfolded (streamIn sh'' ys))

testSeqZipWithRef :: (Elt a, Elt b, Elt c, Shape sh, Shape sh', Shape sh'')
      => Backend 
      -> (Acc (Array sh' b) -> Acc (Array sh'' c) -> PreArrayOp Acc Exp (Array sh a)) 
      -> [Array sh' b]  
      -> [Array sh'' c]  
      -> [Array sh  a]
testSeqZipWithRef backend op = P.zipWith (run2 backend (\ x y -> Acc . ArrayOp $ op x y))

logsum :: (Elt a, IsFloating a) => Int -> Acc (Scalar a)
logsum n = collect
  $ foldSeq (+) 0.0
  $ mapS (log . fromIntegral . (+1))
  $ toSeq' (iota n)

logsumRef :: (Elt a, IsFloating a) => Int -> Scalar a
logsumRef n = fromList Z [P.sum [log (P.fromIntegral i) | i <- [1..n]]]


test_sequences :: Backend -> Config -> Test
test_sequences backend opt = testGroup "sequences"
  [ testGroup "id" $ catMaybes
    [ testIdSequence configInt8   (undefined :: Int8)
    , testIdSequence configInt16  (undefined :: Int16)
    , testIdSequence configInt32  (undefined :: Int32)
    , testIdSequence configInt64  (undefined :: Int64)
    , testIdSequence configWord8  (undefined :: Word8)
    , testIdSequence configWord16 (undefined :: Word16)
    , testIdSequence configWord32 (undefined :: Word32)
    , testIdSequence configWord64 (undefined :: Word64)
    , testIdSequence configFloat  (undefined :: Float)
    , testIdSequence configDouble (undefined :: Double)
    ]
  , testGroup "sum_max" $ catMaybes
    [ testSumMaxSequence configInt8   (undefined :: Int8)
    , testSumMaxSequence configInt16  (undefined :: Int16)
    , testSumMaxSequence configInt32  (undefined :: Int32)
    , testSumMaxSequence configInt64  (undefined :: Int64)
    , testSumMaxSequence configWord8  (undefined :: Word8)
    , testSumMaxSequence configWord16 (undefined :: Word16)
    , testSumMaxSequence configWord32 (undefined :: Word32)
    , testSumMaxSequence configWord64 (undefined :: Word64)
    ]
  , testGroup "scatter" $ catMaybes
    [ testScatterSequence configInt8   (undefined :: Int8)
    , testScatterSequence configInt16  (undefined :: Int16)
    , testScatterSequence configInt32  (undefined :: Int32)
    , testScatterSequence configInt64  (undefined :: Int64)
    , testScatterSequence configWord8  (undefined :: Word8)
    , testScatterSequence configWord16 (undefined :: Word16)
    , testScatterSequence configWord32 (undefined :: Word32)
    , testScatterSequence configWord64 (undefined :: Word64)
    , testScatterSequence configFloat  (undefined :: Float)
    , testScatterSequence configDouble (undefined :: Double)
    ]
  , testGroup "logsum" $ catMaybes
    [ testLogsum configFloat  (undefined :: Float)
    , testLogsum configDouble (undefined :: Double)
    ]
{-  , testGroup "mapReshape" $ catMaybes
    [ testMapReshape configInt8   (undefined :: Int)
    , testMapReshape configInt16  (undefined :: Int)
    , testMapReshape configInt32  (undefined :: Int)
    , testMapReshape configInt64  (undefined :: Int)
    ] -}
  , testGroup "mapFold1" $ catMaybes
    [ testMapFold1 configInt8   (undefined :: Int)
    , testMapFold1 configInt16  (undefined :: Int)
    , testMapFold1 configInt32  (undefined :: Int)
    , testMapFold1 configInt64  (undefined :: Int)
    ]
  , testGroup "mapFold" $ catMaybes
    [ testMapFold configInt8   (undefined :: Int)
    , testMapFold configInt16  (undefined :: Int)
    , testMapFold configInt32  (undefined :: Int)
    , testMapFold configInt64  (undefined :: Int)
    ] {- Not implemented in CUDA-backend yet.
  , testGroup "mapFold1Seg" $ catMaybes
    [ testMapFold1Seg configInt8   (undefined :: Int)
    , testMapFold1Seg configInt16  (undefined :: Int)
    , testMapFold1Seg configInt32  (undefined :: Int)
    , testMapFold1Seg configInt64  (undefined :: Int)
    ]
  , testGroup "mapFoldSeg" $ catMaybes
    [ testMapFoldSeg configInt8   (undefined :: Int)
    , testMapFoldSeg configInt16  (undefined :: Int)
    , testMapFoldSeg configInt32  (undefined :: Int)
    , testMapFoldSeg configInt64  (undefined :: Int)
    ] -}
  , testGroup "mapReplicate" $ catMaybes
    [ testMapReplicate configInt8   (undefined :: Int)
    , testMapReplicate configInt16  (undefined :: Int)
    , testMapReplicate configInt32  (undefined :: Int)
    , testMapReplicate configInt64  (undefined :: Int)
    ]
  , testGroup "mapSlice" $ catMaybes
    [ testMapSlice configInt8   (undefined :: Int)
    , testMapSlice configInt16  (undefined :: Int)
    , testMapSlice configInt32  (undefined :: Int)
    , testMapSlice configInt64  (undefined :: Int)
    ]
  , testGroup "mapPermute" $ catMaybes  
    [ testMapPermute configInt8   (undefined :: Int)
    , testMapPermute configInt16  (undefined :: Int)
    , testMapPermute configInt32  (undefined :: Int)
    , testMapPermute configInt64  (undefined :: Int)
    ]
  , testGroup "mapBackpermute" $ catMaybes  
    [ testMapBackpermute configInt8   (undefined :: Int)
    , testMapBackpermute configInt16  (undefined :: Int)
    , testMapBackpermute configInt32  (undefined :: Int)
    , testMapBackpermute configInt64  (undefined :: Int)
    ]
  ]
  where
    testIdSequence :: forall a. (Elt a, Similar a, IsNum a, Arbitrary a)
            => (Config :-> Bool)
            -> a
            -> Maybe Test
    testIdSequence ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testGroup (show (typeOf (undefined :: a)))
          [ testDim dim1
          , testDim dim2
          ]
      where
        testDim :: forall sh. (sh ~ FullShape sh, Slice sh, Shape sh, Eq sh, Arbitrary sh, Arbitrary (Array (sh :. Int) a)) => (sh :. Int) -> Test
        testDim sh = testProperty ("DIM" P.++ show (dim sh))
          ((\ xs -> run1 backend idSequence xs ~?= idSequenceRef xs) :: Array (sh :. Int) a -> Property)


    testSumMaxSequence :: forall a. (Elt a, Similar a, IsNum a, IsBounded a, Bounded a, Ord a, Arbitrary a)
            => (Config :-> Bool)
            -> a
            -> Maybe Test
    testSumMaxSequence ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testProperty (show (typeOf (undefined :: a)))
          ((\xs -> run1 backend sumMaxSequence xs ~?= sumMaxSequenceRef xs) :: Vector a -> Property)


    testScatterSequence :: forall a. (Elt a, Similar a, IsNum a, Arbitrary a)
            => (Config :-> Bool)
            -> a
            -> Maybe Test
    testScatterSequence ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testProperty (show (typeOf (undefined :: a)))
          ((\input -> run1 backend scatterSequence input ~?= scatterSequenceRef input) :: (Vector a, Vector (Int, a)) -> Property)


    testLogsum :: forall a. (Elt a, Similar a, IsFloating a, Arbitrary a)
               => (Config :-> Bool)
               -> a
               -> Maybe Test
    testLogsum ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testProperty (show (typeOf (undefined :: a)))
          (\ (NonNegative n) -> (run backend (logsum n) :: Scalar a) ~?= logsumRef n)
{-    
    testMapReshape :: forall e. (Elt e, Similar e, Arbitrary e)
                => (Config :-> Bool)
                -> e
                -> Maybe Test
    testMapReshape ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testProperty (show (typeOf (undefined :: e))) $
            forAll (choose (0,5))  $ \ a  ->
            forAll (choose (0,5))  $ \ b  ->
            forAll (choose (0,5))  $ \ c  ->
            let sh1 = Z :. a :. b :. c
                sh2 = Z :. c :. a * b
            in
            forAll (arbitraryArrays sh1) $ \ (arrs :: [Array (Z :. Int :. Int :. Int) e]) ->
              testSeqMap backend (Reshape (constant sh2)) (constant sh1) arrs ~?= testSeqMapRef backend (Reshape (constant sh2)) arrs
-}
    testMapFold :: forall e. (IsNum e, Elt e, Similar e, Arbitrary e)
                => (Config :-> Bool)
                -> e
                -> Maybe Test
    testMapFold ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testProperty (show (typeOf (undefined :: e))) $
            forAll (choose (0,5))  $ \ a  ->
            forAll (choose (0,5))  $ \ b  ->
            forAll (choose (0,5))  $ \ c  ->
            let sh1 = Z :. a :. b :. c
            in
            forAll (arbitraryArrays sh1) $ \ (arrs :: [Array (Z :. Int :. Int :. Int) e]) ->
              testSeqMap backend (Fold (+) (constant 0)) (constant sh1) arrs ~?= testSeqMapRef backend (Fold (+) (constant 0)) arrs


    testMapFold1 :: forall e. (IsNum e, Elt e, Similar e, Arbitrary e)
                => (Config :-> Bool)
                -> e
                -> Maybe Test
    testMapFold1 ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testProperty (show (typeOf (undefined :: e))) $
            forAll (choose (1,5))  $ \ a  ->
            forAll (choose (1,5))  $ \ b  ->
            forAll (choose (1,5))  $ \ c  ->
            let sh1 = Z :. a :. b :. c
            in
            forAll (arbitraryArrays sh1) $ \ (arrs :: [Array (Z :. Int :. Int :. Int) e]) ->
              testSeqMap backend (Fold1 (+)) (constant sh1) arrs ~?= testSeqMapRef backend (Fold1 (+)) arrs
    
    testMapFold1Seg :: forall e. (IsNum e, Elt e, Similar e, Arbitrary e)
                => (Config :-> Bool)
                -> e
                -> Maybe Test
    testMapFold1Seg ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testProperty (show (typeOf (undefined :: e))) $
            forAll (resize 10 arbitrarySegments1) $ \ (segs :: Segments Int) ->
            forAll (choose (1,3))  $ \ a  ->
            forAll (choose (1,3))  $ \ b  ->
            let 
              x = P.fromIntegral . P.sum $ Sugar.toList segs
              sh1 = Z :. a :. b :. x
            in
            forAll (arbitraryArrays sh1) $ \ (arrs :: [Array (Z :. Int :. Int :. Int) e]) ->
            let
              segss = P.replicate (P.length arrs) segs
            in 
              testSeqZipWith backend (Fold1Seg (+)) (constant sh1) (constant (Sugar.shape segs)) arrs segss
                ~?= testSeqZipWithRef backend (Fold1Seg (+)) arrs segss

    testMapFoldSeg :: forall e. (IsNum e, Elt e, Similar e, Arbitrary e)
                => (Config :-> Bool)
                -> e
                -> Maybe Test
    testMapFoldSeg ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testProperty (show (typeOf (undefined :: e))) $
            forAll (resize 10 arbitrarySegments1) $ \ (segs :: Segments Int) ->
            forAll (choose (1,3))  $ \ a  ->
            forAll (choose (1,3))  $ \ b  ->
            let 
              x = P.fromIntegral . P.sum $ Sugar.toList segs
              sh1 = Z :. a :. b :. x
            in
            forAll (arbitraryArrays sh1) $ \ (arrs :: [Array (Z :. Int :. Int :. Int) e]) ->
            let
              segss = P.replicate (P.length arrs) segs
            in 
              testSeqZipWith backend (FoldSeg (+) (constant 0)) (constant sh1) (constant (Sugar.shape segs)) arrs segss
                ~?= testSeqZipWithRef backend (FoldSeg (+) (constant 0)) arrs segss

    testMapReplicate :: forall e. (Elt e, Similar e, Arbitrary e)
                => (Config :-> Bool)
                -> e
                -> Maybe Test
    testMapReplicate ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testProperty (show (typeOf (undefined :: e))) $
            forAll (choose (0,5))  $ \ a  ->
            forAll (choose (0,5))  $ \ b  ->
            let sh1 = Z :. a :. b
                slix :: Z :. Int :. All :. Int :. All
                slix = Z :. 2 :. All :. 2 :. All
            in
            forAll (arbitraryArrays sh1) $ \ (arrs :: [Array (Z :. Int :. Int) e]) ->
              testSeqMap backend (Replicate (constant slix)) (constant sh1) arrs ~?= testSeqMapRef backend (Replicate (constant slix)) arrs

    testMapSlice :: forall e. (Elt e, Similar e, Arbitrary e)
                => (Config :-> Bool)
                -> e
                -> Maybe Test
    testMapSlice ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testProperty (show (typeOf (undefined :: e))) $
            forAll (choose (1,5))  $ \ a  ->
            forAll (choose (0,a-1))  $ \ i  ->
            forAll (choose (0,5))  $ \ b  ->
            forAll (choose (1,5))  $ \ c  ->
            forAll (choose (0,c-1))  $ \ j  ->
            let sh1 = Z :. a :. b :. c
                slix :: Z :. Int :. All :. Int
                slix = Z :. i :. All :. j
            in
            forAll (arbitraryArrays sh1) $ \ (arrs :: [Array (Z :. Int :. Int :. Int) e]) ->
              testSeqMap backend ((flip Slice) (constant slix)) (constant sh1) arrs ~?= testSeqMapRef backend ((flip Slice) (constant slix)) arrs

    testMapPermute :: forall e. (IsNum e, Elt e, Similar e, Arbitrary e)
                => (Config :-> Bool)
                -> e
                -> Maybe Test
    testMapPermute ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testProperty (show (typeOf (undefined :: e))) $
            forAll (choose (0,3))  $ \ a  ->
            forAll (choose (0,3))  $ \ b  ->
            let 
              sh1 = Z :. a :. b
              sh2 = Z :. b :. a
              f :: Exp (Z :. Int :. Int) -> Exp (Z :. Int :. Int)
              f ix = lift (Z :. Acc.indexHead ix :. (0 :: Int))
            in
            forAll (arbitraryArrays sh1) $ \ (defs :: [Array (Z :. Int :. Int) e]) ->
            forAll (arbitraryArrays sh2) $ \ (arrs :: [Array (Z :. Int :. Int) e]) ->
              testSeqZipWith backend (\ x -> Permute (+) x f) (constant sh1) (constant sh2) defs arrs
                ~?= testSeqZipWithRef backend (\ x -> Permute (+) x f) defs arrs


    testMapBackpermute :: forall e. (IsNum e, Elt e, Similar e, Arbitrary e)
                => (Config :-> Bool)
                -> e
                -> Maybe Test
    testMapBackpermute ok _
      | P.not (get ok opt)      = Nothing
      | otherwise               = Just $ testProperty (show (typeOf (undefined :: e))) $
            forAll (choose (0,3))  $ \ a  ->
            forAll (choose (0,3))  $ \ b  ->
            let 
              sh   = Z :. a :. b
              sh'  = Z :. b :. a
              f :: Exp (Z :. Int :. Int) {- sh' -} -> Exp (Z :. Int :. Int) {- sh -}
              f ix = lift (Z :. Acc.indexHead ix :. (0 :: Int))
            in
            forAll (arbitraryArrays sh) $ \ (arrs :: [Array (Z :. Int :. Int) e]) ->
              testSeqMap backend (Backpermute (constant sh') f) (constant sh) arrs
                ~?= testSeqMapRef backend (Backpermute (constant sh') f) arrs


arbitraryArrays :: (Shape sh, Elt e, Arbitrary e) => sh -> Gen [Array sh e]
arbitraryArrays sh = listOf (arbitraryArray sh)
