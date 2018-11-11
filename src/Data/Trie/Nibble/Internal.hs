{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

{-# LANGUAGE ScopedTypeVariables #-}

{-# OPTIONS_GHC -Wno-unused-imports #-}

module Data.Trie.Nibble.Internal
  ( Trie(..)
  , Key
  , null
  , size
  , member
  , lookup
  , findWithDefault
  , foldrWithKey
  , foldlWithKey
  , foldr'WithKey
  , foldl'WithKey
  , toListWithKey
  , toList'WithKey

  , empty
  , singleton
  , fromList

  , insert
  , insertWith
  , union
  , unionWith
  , unionWithKey
  )
  where

import Control.Arrow ((***))
import Control.Monad.ST
import Data.Bits
import Data.Functor.Classes
import Data.List (foldl')
import Data.Maybe
import Data.Primitive.SmallArray
import Data.Trie.Nibble.Internal.NatOps
import Data.Word
import GHC.Exts (inline)
import GHC.Prim
import GHC.Types
import Numeric.Natural
import Prelude hiding (null, lookup)
import Text.Show

import Debug.Trace

{-----------------------------------------------------------------------------
 - Types                                                                     -
 -----------------------------------------------------------------------------}

type Key = Natural

type Offset = Word
type Mask = Word16

data Trie a = Nil
              -- ^ An empty trie. Never a child of 'Node' or 'Full'.
            | Tip !Key a
              -- ^ @Tip k v@ is a tip containing the value @v@ at key ending in a bit-pattern @k@.
            | Node !Key !Offset !Mask !(SmallArray (Trie a))
              -- ^ @Node crumb offt mask arr@ is an up-to-16-ary node. All subtrees of this node refer to keys that contain the nibble-mask @crumb@ at offset
              -- @offt+1@. The nibble at offset @offt@ is used to index into bitmask @mask@ which indicates which subtrees are present in the @arr@ array.
              --
              -- All subtrees must have strictly smaller @offt@s.
            | Full !Key !Offset !(SmallArray (Trie a))
              -- ^ Same as 'Node' but @mask@ is assumed to be @0xFFFF@ and the nibble at offset @offt@ can be seen as an index into @arr@.
            deriving (Eq, Functor, Foldable, Traversable, Show)

{-----------------------------------------------------------------------------
 - Patterns                                                                  -
 -----------------------------------------------------------------------------}

-- | Abstraction over 'Node' and a 'Full'.
pattern NF :: Key -> Offset -> Mask -> SmallArray (Trie a) -> Trie a
pattern NF crumb offt mask arr <- (matchNF -> Just (crumb, offt, mask, arr))
  where NF crumb offt 0xFFFF arr = Full crumb offt arr
        NF crumb offt mask arr = Node crumb offt mask arr
{-# COMPLETE Nil, Tip, NF #-}

matchNF :: Trie a -> Maybe (Key, Offset, Mask, SmallArray (Trie a))
matchNF (Node crumb offt mask arr) = Just (crumb, offt, mask, arr)
matchNF (Full crumb offt arr) = Just (crumb, offt, 0xFFFF, arr)
matchNF _ = Nothing
{-# INLINE matchNF #-}

{-----------------------------------------------------------------------------
 - Analysis                                                                  -
 -----------------------------------------------------------------------------}

null :: Trie a -> Bool
null Nil = True
null _ = False
{-# INLINE null #-}

size :: Trie a -> Int
size = go 0 where go !n Nil = n
                  go !n (Tip _ _) = n + 1
                  go !n (Node _ _ _ arr) = goArr n arr 0 (sizeofSmallArray arr)
                  go !n (Full _ _ arr) = goArr n arr 0 0x10

                  goArr !n arr i j | i == j = n
                                   | otherwise = goArr (go n (indexSmallArray arr i)) arr (i + 1) j
{-# INLINABLE size #-}

-- todo: remove ShiftR
lookup :: Key -> Trie a -> Maybe a
lookup _ Nil = Nothing
lookup k (Tip crumb v)
  | crumb == k = Just v
  | otherwise = Nothing
lookup k (Node crumb offt mask arr)
  | nibbleShiftR k (offt + 1) == crumb
  , nib <- getNibble offt k
  , testBit mask (fromIntegral nib)
  , pos <- maskToPos mask (fromIntegral nib) = lookup (maskNibble offt k) (indexSmallArray arr pos)
  | otherwise = Nothing
lookup k (Full crumb offt arr)
  | nibbleShiftR k (offt + 1) == crumb
  , nib <- getNibble offt k = lookup (maskNibble offt k) (indexSmallArray arr (fromIntegral nib))
  | otherwise = Nothing
{-# INLINABLE lookup #-}

member :: Key -> Trie a -> Bool
member k t = isJust $ lookup k t
{-# INLINE member #-}

findWithDefault :: a -> Key -> Trie a -> a
findWithDefault def k t = fromMaybe def $ lookup k t
{-# INLINE findWithDefault #-}

foldr'WithKey :: (Key -> a -> b -> b) -> b -> Trie a -> b
foldr'WithKey _ z Nil = z
foldr'WithKey f z (Tip tcrumb tv) = f tcrumb tv z
foldr'WithKey f tz t = runST $ do mk <- newZeroMBNForNibble (logNibbleMaxKey t)
                                  go mk t tz
  where go _ Nil _ = error "foldl'WithKey: Nil cannot be a child"
        go mk (Tip crumb v) z = do uncheckedXorNibblesMBN mk 0 crumb
                                   k <- safeRenormFreezeMBN mk
                                   let !r = f k v z
                                   uncheckedXorNibblesMBN mk 0 crumb
                                   pure r

        go mk (Node crumb offt mask arr) z = do uncheckedXorNibblesMBN mk (offt + 1) crumb
                                                r <- goMask (popCount mask - 1) mask z
                                                uncheckedXorNibblesMBN mk (offt + 1) crumb
                                                pure r
          where goMask _ 0 gz = pure gz
                goMask !n m gz = do let nib = mostSignificantBit m
                                    uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                    gr <- go mk (indexSmallArray arr n) gz
                                    uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                    goMask (n - 1) (clearBit m nib) gr

        go mk (Full crumb offt arr) z = do uncheckedXorNibblesMBN mk (offt + 1) crumb
                                           r <- goArr 0xF z
                                           uncheckedXorNibblesMBN mk (offt + 1) crumb
                                           pure r
          where goArr (-1) gz = pure gz
                goArr !nib gz = do uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                   gr <- go mk (indexSmallArray arr nib) gz
                                   uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                   goArr (nib - 1) gr

foldlWithKey :: (b -> Key -> a -> b) -> b -> Trie a -> b
foldlWithKey f tz t = go 0 t tz where
  go _ Nil z = z
  go k (Tip crumb v) z = f z (k .|. crumb) v
  go k (Node crumb offt mask arr) z = goMask (popCount mask - 1) mask z
    where goMask _ 0 gz = gz
          goMask !n m gz | nib <- mostSignificantBit m
                         , newk <- k' .|. nibbleShiftL (fromIntegral nib) offt
                         = go newk (indexSmallArray arr n) $ goMask (n - 1) (clearBit m nib) gz
          k' = k .|. nibbleShiftL crumb (offt + 1)
  go k (Full crumb offt arr) z = goArr 0xF z
    where goArr (-1) gz = gz
          goArr !nib gz | newk <- k' .|. nibbleShiftL (fromIntegral nib) offt
                        = go newk (indexSmallArray arr nib) $ goArr (nib - 1) gz
          k' = k .|. nibbleShiftL crumb (offt + 1)
{-# INLINE foldlWithKey #-}

foldl'WithKey :: (b -> Key -> a -> b) -> b -> Trie a -> b
foldl'WithKey _ z Nil = z
foldl'WithKey f z (Tip tcrumb tv) = f z tcrumb tv
foldl'WithKey f tz t@(NF tcrumb tofft _ _) = runST $ do mk <- newZeroMBNForNibble (tofft + 1 + logNibble tcrumb)
                                                        go mk t tz
  where go _ Nil _ = error "foldl'WithKey: Nil cannot be a child"
        go mk (Tip crumb v) z = do uncheckedXorNibblesMBN mk 0 crumb
                                   k <- safeRenormFreezeMBN mk
                                   let !r = f z k v
                                   uncheckedXorNibblesMBN mk 0 crumb
                                   pure r

        go mk (Node crumb offt mask arr) z = do uncheckedXorNibblesMBN mk (offt + 1) crumb
                                                r <- goMask 0 mask z
                                                uncheckedXorNibblesMBN mk (offt + 1) crumb
                                                pure r
          where goMask _ 0 gz = pure gz
                goMask !n m gz = do let b = leastSignificant m
                                        nib = countTrailingZeros b
                                    uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                    gr <- go mk (indexSmallArray arr n) gz
                                    uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                    goMask (n + 1) (clearBit m nib) gr

        go mk (Full crumb offt arr) z = do uncheckedXorNibblesMBN mk (offt + 1) crumb
                                           r <- goArr 0 z
                                           uncheckedXorNibblesMBN mk (offt + 1) crumb
                                           pure r
          where goArr 0x10 gz = pure gz
                goArr !nib gz = do uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                   gr <- go mk (indexSmallArray arr nib) gz
                                   uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                   goArr (nib + 1) gr

foldrWithKey :: (Key -> a -> b -> b) -> b -> Trie a -> b
foldrWithKey f tz t = go 0 t tz where
  go _ Nil z = z
  go k (Tip crumb v) z = f (k .|. crumb) v z
  go k (Node crumb offt mask arr) z = goMask 0 mask z
    where goMask _ 0 gz = gz
          goMask !n m gz | b <- leastSignificant m
                         , nib <- countTrailingZeros b
                         , newk <- k' .|. nibbleShiftL (fromIntegral nib) offt
                         = go newk (indexSmallArray arr n) $ goMask (n + 1) (clearBit m nib) gz
          k' = k .|. nibbleShiftL crumb (offt + 1)
  go k (Full crumb offt arr) z = goArr 0 z
    where goArr 0x10 gz = gz
          goArr !nib gz | newk <- k' .|. nibbleShiftL (fromIntegral nib) offt
                        = go newk (indexSmallArray arr nib) $ goArr (nib + 1) gz
          k' = k .|. nibbleShiftL crumb (offt + 1)
{-# INLINE foldrWithKey #-}

toListWithKey :: Trie a -> [(Key, a)]
toListWithKey = foldrWithKey (\k v -> ((k, v):)) []
{-# INLINE toListWithKey #-}

toList'WithKey :: Trie a -> [(Key, a)]
toList'WithKey = foldr'WithKey (\k v -> ((k, v):)) []
{-# INLINE toList'WithKey #-}

{-
instance Show a => Show (Trie a) where
  showsPrec d t = showParen (d > 10) $ showString "fromList " .
                    liftShowsPrec (liftShowsPrec2 showKey (showListWith $ showKey 0) showsPrec showList)
                                  (liftShowList2  showKey (showListWith $ showKey 0) showsPrec showList) d (toListWithKey t)
    where showKey :: Int -> Key -> ShowS
          showKey _ k | k == 0 = showString "0"
                      | otherwise = showString "0x" . showString ["0123456789ABCDEF" !! fromIntegral (getNibble i k) | i <- [logNibble k, logNibble k - 1 .. 0]]
-}

{-----------------------------------------------------------------------------
 - Synthesis                                                                 -
 -----------------------------------------------------------------------------}

empty :: Trie a
empty = Nil
{-# INLINE empty #-}

singleton :: Key -> a -> Trie a
singleton = Tip
{-# INLINE singleton #-}

insert :: Key -> a -> Trie a -> Trie a
insert k v = inline insertWith (\x _ -> x) k v
{-# INLINE insert #-}

-- todo: remove maskNibble
insertWith :: (a -> a -> a) -> Key -> a -> Trie a -> Trie a
insertWith f key v = go key where
  go k Nil = Tip k v
  go k t@(Tip crumb tv)
    | k == crumb
    , newv <- f v tv = if newv *==* tv
                       then t
                       else Tip crumb newv
    | otherwise
    , offt <- logNibble $ k `xor` crumb
    , newcrumb <- nibbleShiftR crumb (offt + 1)
    , nib <- getNibble offt k
    , tNib <- getNibble offt crumb
    , newk <- maskNibble offt k
    , newt <- maskNode offt t
    = Node newcrumb offt (bit (fromIntegral nib) .|. bit (fromIntegral tNib)) (makePair nib (Tip newk v) tNib newt)
  go k t@(Node crumb offt mask arr)
    | nibbleShiftR k (offt + 1) == crumb
    , nib <- getNibble offt k
    , pos <- maskToPos mask (fromIntegral nib)
    , newk <- maskNibble offt k
    = if | testBit mask (fromIntegral nib)
         , child <- indexSmallArray arr pos
         , newchild <- go newk child -> if newchild *==* child
                                        then t
                                        else Node crumb offt mask (updateSmallArray arr pos newchild)
         | otherwise -> NF crumb offt (mask .|. bit (fromIntegral nib)) (insertSmallArray arr pos (Tip newk v))
  go k t@(Full crumb offt arr)
    | nibbleShiftR k (offt + 1) == crumb
    , nib <- getNibble offt k
    , newk <- maskNibble offt k
    , child <- indexSmallArray arr (fromIntegral nib)
    , newchild <- go newk child = if newchild *==* child
                                  then t
                                  else Full crumb offt (updateSmallArray arr (fromIntegral nib) newchild)
  go k t@(NF crumb offt _ _)
    | newofft <- logNibble $ nibbleShiftR k (offt + 1) `xor` crumb
    , newcrumb <- nibbleShiftR crumb (newofft + 1)
    , nib <- getNibble (newofft + offt + 1) k
    , tNib <- getNibble newofft crumb
    , newk <- maskNibble (newofft + offt + 1) k
    , newt <- maskNode newofft t
    = Node newcrumb (offt + newofft + 1) (bit (fromIntegral nib) .|. bit (fromIntegral tNib)) (makePair nib (Tip newk v) tNib newt)
{-# INLINE insertWith #-}

fromList :: [(Key, a)] -> Trie a
fromList = foldl' (\t (k, v) -> insert k v t) empty
{-# INLINE fromList #-}

{-----------------------------------------------------------------------------
 - Combinators                                                               -
 -----------------------------------------------------------------------------}

union :: Trie a -> Trie a -> Trie a
union l r = inline unionWithKey (\_ a _ -> a) l r

unionWith :: (a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWith f l r = inline unionWithKey (\_ a b -> f a b) l r

-- todo: efficient key comparison
unionWithKey :: (Key -> a -> a -> a) -> Trie a -> Trie a -> Trie a
unionWithKey _ Nil r = r
unionWithKey _ l Nil = l
unionWithKey f lt rt = runST $ do mk <- newZeroMBNForNibble (upperBound - 1)
                                  go mk upperBound lt upperBound rt
  where
    upperBound = 1 + (logNibbleMaxKey lt `max` logNibbleMaxKey rt)

    go mk lbnd l rbnd r
      | Just (nib, newlbnd) <- isProperSubTrie lbnd l rbnd r
      = case r of
        Node rcrumb rofft rmask rarr
          | pos <- maskToPos rmask (fromIntegral nib)
          -> if | testBit rmask (fromIntegral nib)
                , child <- indexSmallArray rarr pos
                -> do uncheckedXorNibblesMBN mk (rofft + 1) $ maskNibble rbnd rcrumb
                      uncheckedXorNibblesMBN mk rofft $ fromIntegral nib
                      newchild <- go mk newlbnd l upperBound child
                      uncheckedXorNibblesMBN mk (rofft + 1) $ maskNibble rbnd rcrumb
                      uncheckedXorNibblesMBN mk rofft $ fromIntegral nib
                      pure $ if newchild *==* child
                             then r
                             else Node (maskNibble rbnd rcrumb) rofft rmask (updateSmallArray rarr pos newchild)
                | otherwise
                , newchild <- maskNode newlbnd l
                -> do pure $ NF (maskNibble rbnd rcrumb) rofft
                                (rmask .|. bit (fromIntegral nib)) (insertSmallArray rarr pos newchild)
        Full rcrumb rofft rarr
          | child <- indexSmallArray rarr (fromIntegral nib)
          -> do uncheckedXorNibblesMBN mk (rofft + 1) $ maskNibble rbnd rcrumb
                uncheckedXorNibblesMBN mk rofft $ fromIntegral nib
                newchild <- go mk newlbnd l upperBound child
                uncheckedXorNibblesMBN mk (rofft + 1) $ maskNibble rbnd rcrumb
                uncheckedXorNibblesMBN mk rofft $ fromIntegral nib
                pure $ if newchild *==* child
                       then r
                       else Full (maskNibble rbnd rcrumb) rofft (updateSmallArray rarr (fromIntegral nib) newchild)
        _ -> error "isProperSubTrie cannot accept that"
      | Just (nib, newrbnd) <- isProperSubTrie rbnd r lbnd l
      = case l of
        Node lcrumb lofft lmask larr
          | pos <- maskToPos lmask (fromIntegral nib)
          -> if | testBit lmask (fromIntegral nib)
                , child <- indexSmallArray larr pos
                -> do uncheckedXorNibblesMBN mk (lofft + 1) $ maskNibble lbnd lcrumb
                      uncheckedXorNibblesMBN mk lofft $ fromIntegral nib
                      newchild <- go mk upperBound child newrbnd r
                      uncheckedXorNibblesMBN mk (lofft + 1) $ maskNibble lbnd lcrumb
                      uncheckedXorNibblesMBN mk lofft $ fromIntegral nib
                      pure $ if newchild *==* child
                             then l
                             else Node (maskNibble lbnd lcrumb) lofft lmask (updateSmallArray larr pos newchild)
                | otherwise
                , newchild <- maskNode newrbnd r
                -> do pure $ NF (maskNibble lbnd lcrumb) lofft
                                (lmask .|. bit (fromIntegral nib)) (insertSmallArray larr pos newchild)
        Full lcrumb lofft larr
          | child <- indexSmallArray larr (fromIntegral nib)
          -> do uncheckedXorNibblesMBN mk (lofft + 1) $ maskNibble lbnd lcrumb
                uncheckedXorNibblesMBN mk lofft $ fromIntegral nib
                newchild <- go mk upperBound child newrbnd r
                uncheckedXorNibblesMBN mk (lofft + 1) $ maskNibble lbnd lcrumb
                uncheckedXorNibblesMBN mk lofft $ fromIntegral nib
                pure $ if newchild *==* child
                       then l
                       else Full (maskNibble lbnd lcrumb) lofft (updateSmallArray larr (fromIntegral nib) newchild)
        _ -> error "isProperSubTrie cannot accept that"
      | Just (crumb, offt, lNib, newlbnd, rNib, newrbnd) <- isDisjointTrie (maskNode lbnd l) (maskNode rbnd r)
      , newl <- maskNode newlbnd l
      , newr <- maskNode newrbnd r
      = pure $ Node crumb offt (bit (fromIntegral lNib) .|. bit (fromIntegral rNib)) (makePair lNib newl rNib newr)
    go mk lbnd l@(Tip lcrumb lv) rbnd r@(Tip rcrumb rv)
      = do uncheckedXorNibblesMBN mk 0 $ maskNibble lbnd lcrumb
           k <- safeRenormFreezeMBN mk
           let newv = f k lv rv
           uncheckedXorNibblesMBN mk 0 $ maskNibble lbnd lcrumb
           pure $ if | newv *==* lv, logNibble lcrumb < lbnd -> l
                     | newv *==* rv, logNibble rcrumb < rbnd -> r
                     | otherwise -> Tip (maskNibble lbnd lcrumb) newv
    go mk lbnd l@(Node lcrumb offt lmask larr) rbnd r@(Node rcrumb _ rmask rarr)
      = do let mask = lmask .|. rmask
           uncheckedXorNibblesMBN mk (offt + 1) $ maskNibble lbnd lcrumb
           u <- if | lmask == rmask
                   -> do ma <- newSmallArray (popCount lmask) undefined
                         let fill !sl !sr _ 0 = pure (sl, sr)
                             fill !sl !sr !n !m | b <- leastSignificant m
                                                , nib <- countTrailingZeros b
                                                , lst <- indexSmallArray larr n
                                                , rst <- indexSmallArray rarr n
                                                = do uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                                     newt <- go mk upperBound lst upperBound rst
                                                     uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                                     writeSmallArray ma n newt
                                                     fill (sl && lst *==* newt) (sr && rst *==* newt)
                                                          (n + 1) (clearBit m nib)
                         (sharel, sharer) <- fill (logNibble lcrumb < lbnd) (logNibble rcrumb < rbnd) 0 lmask
                         if | sharel -> pure l
                            | sharer -> pure r
                            | otherwise -> do a <- unsafeFreezeSmallArray ma
                                              pure $ Node (maskNibble lbnd lcrumb) offt lmask a
                   | mask == lmask
                   -> do ma <- newSmallArray (popCount mask) undefined
                         let fill !sl _ 0 = pure sl
                             fill !sl !n !m | b <- leastSignificant m
                                            , nib <- countTrailingZeros b
                                            , lst <- indexSmallArray larr n
                                            = if rmask .&. b == 0
                                              then do writeSmallArray ma n lst
                                                      fill sl (n + 1) (clearBit m nib)
                                              else do let rst = indexSmallArray rarr $ maskToPos rmask $ fromIntegral nib
                                                      uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                                      newt <- go mk upperBound lst upperBound rst
                                                      uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                                      writeSmallArray ma n newt
                                                      fill (sl && lst *==* newt) (n + 1) (clearBit m nib)
                         sharel <- fill (logNibble lcrumb < lbnd) 0 mask
                         if sharel then pure l
                                   else do a <- unsafeFreezeSmallArray ma
                                           pure $ Node (maskNibble lbnd lcrumb) offt mask a
                   | mask == rmask
                   -> do ma <- newSmallArray (popCount mask) undefined
                         let fill !sr _ 0 = pure sr
                             fill !sr !n !m | b <- leastSignificant m
                                            , nib <- countTrailingZeros b
                                            , rst <- indexSmallArray rarr n
                                            = if lmask .&. b == 0
                                              then do writeSmallArray ma n rst
                                                      fill sr (n + 1) (clearBit m nib)
                                              else do let lst = indexSmallArray larr $ maskToPos lmask $ fromIntegral nib
                                                      uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                                      newt <- go mk upperBound lst upperBound rst
                                                      uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                                      writeSmallArray ma n newt
                                                      fill (sr && rst *==* newt) (n + 1) (clearBit m nib)
                         sharer <- fill (logNibble rcrumb < rbnd) 0 mask
                         if sharer then pure r
                                   else do a <- unsafeFreezeSmallArray ma
                                           pure $ Node (maskNibble lbnd lcrumb) offt mask a
                   | otherwise
                   -> do ma <- newSmallArray (popCount mask) undefined
                         let fill _ 0 = pure ()
                             fill !n !m | b <- leastSignificant m
                                        , nib <- countTrailingZeros b
                                        = if | lmask .&. b == 0
                                             -> do let rst = indexSmallArray rarr $ maskToPos rmask $ fromIntegral nib
                                                   writeSmallArray ma n rst
                                                   fill (n + 1) (clearBit m nib)
                                             | rmask .&. b == 0
                                             -> do let lst = indexSmallArray larr $ maskToPos lmask $ fromIntegral nib
                                                   writeSmallArray ma n lst
                                                   fill (n + 1) (clearBit m nib)
                                             | otherwise
                                             -> do let lst = indexSmallArray larr $ maskToPos lmask $ fromIntegral nib
                                                       rst = indexSmallArray rarr $ maskToPos rmask $ fromIntegral nib
                                                   uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                                   newt <- go mk upperBound lst upperBound rst
                                                   uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                                   writeSmallArray ma n newt
                                                   fill (n + 1) (clearBit m nib)
                         fill 0 mask
                         a <- unsafeFreezeSmallArray ma
                         pure $ NF (maskNibble lbnd lcrumb) offt mask a
           uncheckedXorNibblesMBN mk (offt + 1) $ maskNibble lbnd lcrumb
           pure u
    go mk lbnd (Node lcrumb offt lmask larr) rbnd r@(Full rcrumb _ rarr)
      = do ma <- newSmallArray 0x10 undefined
           let fill !sr 0x10 = pure sr
               fill !sr !nib | rst <- indexSmallArray rarr nib
                             = if lmask .&. bit nib == 0
                               then do writeSmallArray ma nib rst
                                       fill sr (nib + 1)
                                    else do let lst = indexSmallArray larr $ maskToPos lmask nib
                                            uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                            newt <- go mk upperBound lst upperBound rst
                                            uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                            writeSmallArray ma nib newt
                                            fill (sr && rst *==* newt) (nib + 1)
           sharer <- fill (logNibble rcrumb < rbnd) 0
           if sharer then pure r
                     else do a <- unsafeFreezeSmallArray ma
                             pure $ Full (maskNibble lbnd lcrumb) offt a
    go mk lbnd l@(Full lcrumb offt larr) _ (Node _ _ rmask rarr)
      = do ma <- newSmallArray 0x10 undefined
           let fill !sl 0x10 = pure sl
               fill !sl !nib | lst <- indexSmallArray larr nib
                             = if rmask .&. bit nib == 0
                               then do writeSmallArray ma nib lst
                                       fill sl (nib + 1)
                                    else do let rst = indexSmallArray rarr $ maskToPos rmask nib
                                            uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                            newt <- go mk upperBound lst upperBound rst
                                            uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                            writeSmallArray ma nib newt
                                            fill (sl && lst *==* newt) (nib + 1)
           sharel <- fill (logNibble lcrumb < lbnd) 0
           if sharel then pure l
                     else do a <- unsafeFreezeSmallArray ma
                             pure $ Full (maskNibble lbnd lcrumb) offt a
    go mk lbnd l@(Full lcrumb offt larr) rbnd r@(Full rcrumb _ rarr)
      = do ma <- newSmallArray 0x10 undefined
           let fill !sl !sr 0x10 = pure (sl, sr)
               fill !sl !sr !nib | lst <- indexSmallArray larr nib
                                 , rst <- indexSmallArray rarr nib
                                 = do uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                      newt <- go mk upperBound lst upperBound rst
                                      uncheckedXorNibblesMBN mk offt $ fromIntegral nib
                                      writeSmallArray ma nib newt
                                      fill (sl && lst *==* newt) (sr && rst *==* newt) (nib + 1)
           (sharel, sharer) <- fill (logNibble lcrumb < lbnd) (logNibble rcrumb < rbnd) 0
           if | sharel -> pure l
              | sharer -> pure r
              | otherwise -> do a <- unsafeFreezeSmallArray ma
                                pure $ Full (maskNibble lbnd lcrumb) offt a
    go _ _ _ _ _ = error "unionWithKey/go"

    isProperSubTrie :: Offset -> Trie a -> Offset -> Trie a -> Maybe (Word8, Offset)
    isProperSubTrie _ _ _ (Tip _ _) = Nothing
    isProperSubTrie lbnd (Tip lcrumb _) rbnd (NF rcrumb rofft _ _) = if nibbleShiftR (maskNibble lbnd lcrumb) (rofft + 1) == maskNibble rbnd rcrumb
                                                                     then Just (getNibble rofft lcrumb, rofft)
                                                                     else Nothing
    isProperSubTrie lbnd (NF lcrumb lofft _ _) rbnd (NF rcrumb rofft _ _) = if lofft < rofft && nibbleShiftR (maskNibble lbnd lcrumb) (rofft - lofft) == maskNibble rbnd rcrumb
                                                                            then Just (getNibble (rofft - lofft - 1) lcrumb, rofft - lofft - 1)
                                                                            else Nothing
    isProperSubTrie _ Nil _ _ = error "isProperSubTrie _ Nil _ _"
    isProperSubTrie _ _ _ Nil = error "isProperSubTrie _ _ _ Nil"
    {-# INLINE isProperSubTrie #-}

    isDisjointTrie :: Trie a -> Trie a -> Maybe (Key, Offset, Word8, Offset, Word8, Offset)
    isDisjointTrie (Tip lcrumb _) (Tip rcrumb _)
      | lcrumb /= rcrumb
      , offt <- logNibble $ lcrumb `xor` rcrumb
      , crumb <- nibbleShiftR lcrumb (offt + 1) = Just (crumb, offt, getNibble offt lcrumb, offt, getNibble offt rcrumb, offt)
      | otherwise = Nothing
    isDisjointTrie (Tip lcrumb _) (NF rcrumb rofft _ _)
      | offt <- logNibble $ nibbleShiftR lcrumb (rofft + 1) `xor` rcrumb
      , crumb <- nibbleShiftR rcrumb (offt + 1) = Just (crumb, offt + rofft + 1, getNibble (offt + rofft + 1) lcrumb, offt + rofft + 1, getNibble offt rcrumb, offt)
    isDisjointTrie (NF lcrumb lofft _ _) (Tip rcrumb _)
      | offt <- logNibble $ lcrumb `xor` nibbleShiftR rcrumb (lofft + 1)
      , crumb <- nibbleShiftR lcrumb (offt + 1) = Just (crumb, offt + lofft + 1, getNibble offt lcrumb, offt, getNibble (offt + lofft + 1) rcrumb, offt + lofft + 1)
    isDisjointTrie (NF lcrumb lofft _ _) (NF rcrumb rofft _ _) = case compare lofft rofft of
      LT | offt <- logNibble $ nibbleShiftR lcrumb (rofft - lofft) `xor` rcrumb
         , crumb <- nibbleShiftR rcrumb (offt + 1)
         -> Just (crumb, offt + rofft + 1, getNibble (offt + rofft - lofft) lcrumb, offt + rofft - lofft, getNibble offt rcrumb, offt)
      GT | offt <- logNibble $ lcrumb `xor` nibbleShiftR rcrumb (lofft - rofft)
         , crumb <- nibbleShiftR lcrumb (offt + 1)
         -> Just (crumb, offt + lofft + 1, getNibble offt lcrumb, offt, getNibble (offt + lofft - rofft) rcrumb, offt + lofft - rofft)
      EQ | lcrumb /= rcrumb
         , offt <- logNibble $ lcrumb `xor` rcrumb
         , crumb <- nibbleShiftR lcrumb (offt + 1)
         -> Just (crumb, offt + lofft + 1, getNibble offt lcrumb, offt, getNibble offt rcrumb, offt)
         | otherwise -> Nothing
    isDisjointTrie Nil _ = error "isDisjointTrie Nil _"
    isDisjointTrie _ Nil = error "isDisjointTrie _ Nil"
    {-# INLINE isDisjointTrie #-}
{-# INLINABLE unionWithKey #-}

{-----------------------------------------------------------------------------
 - Utilities                                                                 -
 -----------------------------------------------------------------------------}

(*==*) :: a -> a -> Bool
x *==* y = isTrue# (reallyUnsafePtrEquality# x y)


insertSmallArray :: SmallArray a -> Int -> a -> SmallArray a
insertSmallArray a pos v = runST $ do
  ma <- newSmallArray (sizeofSmallArray a + 1) undefined
  copySmallArray ma 0 a 0 pos
  writeSmallArray ma pos v
  copySmallArray ma (pos + 1) a pos (sizeofSmallArray a - pos)
  unsafeFreezeSmallArray ma

updateSmallArray :: SmallArray a -> Int -> a -> SmallArray a
updateSmallArray a pos v = runST $ do
  ma <- newSmallArray (sizeofSmallArray a) undefined
  copySmallArray ma 0 a 0 (sizeofSmallArray a)
  writeSmallArray ma pos v
  unsafeFreezeSmallArray ma


maskNode :: Offset -> Trie a -> Trie a
maskNode _ Nil = Nil
maskNode o (Tip crumb v) = Tip (maskNibble o crumb) v
maskNode o (Node crumb offt mask arr) = Node (maskNibble o crumb) offt mask arr
maskNode o (Full crumb offt arr) = Full (maskNibble o crumb) offt arr

makePair :: Ord b => b -> a -> b -> a -> SmallArray a
makePair lNib l rNib r = if lNib < rNib then makeArr l r else makeArr r l
  where makeArr x y = runST $ do ma <- newSmallArray 2 x
                                 writeSmallArray ma 1 y
                                 unsafeFreezeSmallArray ma

logNibbleMaxKey :: Trie a -> Offset
logNibbleMaxKey (Tip crumb _) = if crumb == 0 then 0 else logNibble crumb
logNibbleMaxKey (NF crumb offt _ _) = if crumb == 0 then offt else logNibble crumb + offt + 1
logNibbleMaxKey Nil = error "logNibbleMaxKey Nil"


nibbleShiftR :: Bits k => k -> Offset -> k
nibbleShiftR x offt = unsafeShiftR x (fromIntegral $ unsafeShiftL offt 2)

nibbleShiftL :: Bits k => k -> Offset -> k
nibbleShiftL x offt = unsafeShiftL x (fromIntegral $ unsafeShiftL offt 2)

maskToPos :: Mask -> Int -> Int
maskToPos mask b = popCount $ mask .&. (bit b - 1)

leastSignificant :: Mask -> Mask
leastSignificant x = x .&. negate x

mostSignificantBit :: Mask -> Int
mostSignificantBit x = wlog2 (fromIntegral x)
