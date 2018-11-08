{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Trie.Nibble.Internal
  ( Trie(..)
  , null
  , size
  , member
  , lookup
  , findWithDefault
  , toList

  , empty
  , singleton

  , fromList
  , insert
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
import Data.Trie.Nibble.NibbleQuery
import Data.Word
import GHC.Prim
import GHC.Types
import Prelude hiding (null, lookup)
import Text.Show

type Offset = Word
type Mask = Word16

data Trie k v = Nil
                -- ^ An empty trie. Never a child of 'Node' or 'Full'.
              | Tip !k v
                -- ^ @Tip k v@ is a tip containing the value @v@ at key ending in a bit-pattern @k@.
              | Node !k !Offset !Mask !(SmallArray (Trie k v))
                -- ^ @Node crumb offt mask arr@ is an up-to-16-ary node. All subtrees of this node refer to keys that contain the nibble-mask @crumb@ at offset
                -- @offt+1@. The nibble at offset @offt@ is used to index into bitmask @mask@ which indicates which subtrees are present in the @arr@ array.
                --
                -- All subtrees must have strictly smaller @offt@s.
              | Full !k !Offset !(SmallArray (Trie k v))
                -- ^ Same as 'Node' but @mask@ is assumed to be @0xFFFF@ and the nibble at offset @offt@ can be seen as an index into @arr@.
              deriving (Eq, Functor, Foldable, Traversable)

-- | Abstraction over 'Node' and a 'Full'.
pattern NF :: k -> Offset -> Mask -> SmallArray (Trie k v) -> Trie k v
pattern NF crumb offt mask arr <- (matchNF -> Just (crumb, offt, mask, arr))
  where NF crumb offt 0xFFFF arr = Full crumb offt arr
        NF crumb offt mask arr = Node crumb offt mask arr
{-# COMPLETE Nil, Tip, NF #-}

matchNF :: Trie k v -> Maybe (k, Offset, Mask, SmallArray (Trie k v))
matchNF (Node crumb offt mask arr) = Just (crumb, offt, mask, arr)
matchNF (Full crumb offt arr) = Just (crumb, offt, 0xFFFF, arr)
matchNF _ = Nothing


null :: Trie k v -> Bool
null Nil = False
null _ = True

size :: Trie k v -> Int
size = go 0 where go !n Nil = n
                  go !n (Tip _ _) = n + 1
                  go !n (Node _ _ _ arr) = goArr n arr 0 (sizeofSmallArray arr)
                  go !n (Full _ _ arr) = goArr n arr 0 0x10

                  goArr !n arr i j | i == j = n
                                   | otherwise = goArr (go n (indexSmallArray arr i)) arr (i + 1) j

lookup :: NibbleQuery k => k -> Trie k v -> Maybe v
lookup _ Nil = Nothing
lookup k (Tip crumb v) | crumb == k = Just v
                       | otherwise = Nothing
lookup k (Node crumb offt mask arr) | nibbleShiftR k (offt + 1) == crumb
                                    , nib <- getNibble offt k
                                    , testBit mask (fromIntegral nib)
                                    , pos <- maskToPos mask (fromIntegral nib) = lookup (nibbleMask offt k) (indexSmallArray arr pos)
                                    | otherwise = Nothing
lookup k (Full crumb offt arr) | nibbleShiftR k (offt + 1) == crumb
                               , nib <- getNibble offt k = lookup (nibbleMask offt k) (indexSmallArray arr (fromIntegral nib))
                               | otherwise = Nothing

member :: NibbleQuery k => k -> Trie k v -> Bool
member k t = isJust $ lookup k t

toList :: NibbleQuery k => Trie k v -> [(k, v)]
toList t = go zeroBits t [] where
  go _ Nil = id
  go k (Tip crumb v) = ((k .|. crumb, v):)
  go k (Node crumb offt mask arr) = goMask 0 mask
    where goMask _ 0 = id
          goMask !n m | b <- leastSignificant m
                      , nib <- countTrailingZeros b
                      , newk <- k' .|. nibbleShiftL (makeNibble (fromIntegral nib)) offt
                      = go newk (indexSmallArray arr n) . goMask (n + 1) (removeLeastSignificant m)
          k' = k .|. nibbleShiftL crumb (offt + 1)
  go k (Full crumb offt arr) = goArr 0
    where goArr 0x10 = id
          goArr !nib | newk <- k' .|. nibbleShiftL (makeNibble (fromIntegral nib)) offt
                     = go newk (indexSmallArray arr nib) . goArr (nib + 1)
          k' = k .|. nibbleShiftL crumb (offt + 1)

instance (NibbleQuery k, Show v) => Show (Trie k v) where
  showsPrec d t = showParen (d > 10) $ showString "fromList " .
                    liftShowsPrec (liftShowsPrec2 showKey (showListWith $ showKey 0) showsPrec showList)
                                  (liftShowList2  showKey (showListWith $ showKey 0) showsPrec showList) d (toList t)
    where showKey :: NibbleQuery k => Int -> k -> ShowS
          showKey _ k | k == zeroBits = showString "0"
                      | otherwise = showString "0x" . showString ["0123456789ABCDEF" !! fromIntegral (getNibble i k) | i <- [logNibble k, logNibble k - 1 .. 0]]

empty :: Trie k v
empty = Nil

singleton :: k -> v -> Trie k v
singleton = Tip

findWithDefault :: NibbleQuery k => v -> k -> Trie k v -> v
findWithDefault def k t = fromMaybe def $ lookup k t

-- todo: inline
insert :: NibbleQuery k => k -> v -> Trie k v -> Trie k v
insert k v t = union (singleton k v) t

fromList :: NibbleQuery k => [(k, v)] -> Trie k v
fromList = foldl' (\t (k, v) -> insert k v t) empty

union :: NibbleQuery k => Trie k v -> Trie k v -> Trie k v
union = unionWithKey (\_ x _ -> x)

unionWith :: NibbleQuery k => (v -> v -> v) -> Trie k v -> Trie k v -> Trie k v
unionWith f = unionWithKey (\_ -> f)

unionWithKey :: NibbleQuery k => (k -> v -> v -> v) -> Trie k v -> Trie k v -> Trie k v
unionWithKey f = go zeroBits where
  go _ l Nil = l
  go _ Nil r = r
  go k l r
    | Just (nib, o) <- isProperSubTrie l r
    , newl <- maskNode o l = case r of
      Node rcrumb rofft rmask rarr | pos <- maskToPos rmask (fromIntegral nib)
                                   -> if | testBit rmask (fromIntegral nib)
                                         , child <- indexSmallArray rarr pos
                                         , newk <- k .|. nibbleShiftL rcrumb (rofft + 1) .|. nibbleShiftL (makeNibble (fromIntegral nib)) rofft
                                         , newchild <- go newk newl child -> if newchild *==* child
                                                                             then r
                                                                             else Node rcrumb rofft rmask (updateSmallArray rarr pos newchild)
                                         | otherwise -> NF rcrumb rofft (rmask .|. bit (fromIntegral nib)) (insertSmallArray rarr pos newl)
      Full rcrumb rofft rarr | child <- indexSmallArray rarr (fromIntegral nib)
                             , newk <- k .|. nibbleShiftL rcrumb (rofft + 1) .|. nibbleShiftL (makeNibble (fromIntegral nib)) rofft
                             , newchild <- go newk newl child -> if newchild *==* child
                                                                 then r
                                                                 else Full rcrumb rofft (updateSmallArray rarr (fromIntegral nib) newchild)
      _ -> error "isProperSubTrie cannot accept that"
    | Just (nib, o) <- isProperSubTrie r l
    , newr <- maskNode o r = case l of
      Node lcrumb lofft lmask larr | pos <- maskToPos lmask (fromIntegral nib)
                                   -> if | testBit lmask (fromIntegral nib)
                                         , child <- indexSmallArray larr pos
                                         , newk <- k .|. nibbleShiftL lcrumb (lofft + 1) .|. nibbleShiftL (makeNibble (fromIntegral nib)) lofft
                                         , newchild <- go newk child newr -> if newchild *==* child
                                                                             then l
                                                                             else Node lcrumb lofft lmask (updateSmallArray larr pos newchild)
                                         | otherwise -> NF lcrumb lofft (lmask .|. bit (fromIntegral nib)) (insertSmallArray larr pos newr)
      Full lcrumb lofft larr | child <- indexSmallArray larr (fromIntegral nib)
                             , newk <- k .|. nibbleShiftL lcrumb (lofft + 1) .|. nibbleShiftL (makeNibble (fromIntegral nib)) lofft
                             , newchild <- go newk child newr -> if newchild *==* child
                                                                 then l
                                                                 else Full lcrumb lofft (updateSmallArray larr (fromIntegral nib) newchild)
      _ -> error "isProperSubTrie cannot accept that"
    | Just (crumb, offt, lNib, lo, rNib, ro) <- isDisjointTrie l r
    , newl <- maskNode lo l
    , newr <- maskNode ro r = Node crumb offt (bit (fromIntegral lNib) .|. bit (fromIntegral rNib)) (makePair lNib newl rNib newr)
  go k l@(Tip crumb lv) r@(Tip _ rv)
    | !newv <- f (k .|. crumb) lv rv = if | newv *==* lv -> l
                                          | newv *==* rv -> r
                                          | otherwise -> Tip crumb newv
  go k l@(Node crumb offt lmask larr) r@(Node _ _ rmask rarr)
    | lmask == rmask
    = runST $ do ma <- newSmallArray (popCount lmask) undefined
                 let fill _ 0 = pure (True, True)
                     fill !n m | b <- leastSignificant m
                               , nib <- countTrailingZeros b
                               , newk <- k' .|. nibbleShiftL (makeNibble (fromIntegral nib)) offt
                               , lt <- indexSmallArray larr n
                               , rt <- indexSmallArray rarr n
                               , newt <- go newk lt rt
                               = do writeSmallArray ma n newt
                                    ((lt *==* newt &&) *** (rt *==* newt &&)) <$> fill (n + 1) (removeLeastSignificant m)
                 (sharel, sharer) <- fill 0 lmask
                 if | sharel -> pure l
                    | sharer -> pure r
                    | otherwise -> Node crumb offt lmask <$> unsafeFreezeSmallArray ma
    | mask == lmask
    = runST $ do ma <- newSmallArray (popCount mask) undefined
                 let fill _ 0 = pure True
                     fill !n m | b <- leastSignificant m
                               , nib <- countTrailingZeros b
                               , newk <- k' .|. nibbleShiftL (makeNibble (fromIntegral nib)) offt
                               , lt <- indexSmallArray larr n
                               = if rmask .&. b == 0
                                 then do writeSmallArray ma n lt
                                         fill (n + 1) (removeLeastSignificant m)
                                 else do let rt = indexSmallArray rarr (maskToPos rmask (fromIntegral nib))
                                             newt = go newk lt rt
                                         writeSmallArray ma n newt
                                         (lt *==* newt &&) <$> fill (n + 1) (removeLeastSignificant m)
                 sharel <- fill 0 mask
                 if sharel then pure l
                           else Node crumb offt mask <$> unsafeFreezeSmallArray ma
    | mask == rmask
    = runST $ do ma <- newSmallArray (popCount mask) undefined
                 let fill _ 0 = pure True
                     fill !n m | b <- leastSignificant m
                               , nib <- countTrailingZeros b
                               , newk <- k' .|. nibbleShiftL (makeNibble (fromIntegral nib)) offt
                               , rt <- indexSmallArray rarr n
                               = if lmask .&. b == 0
                                 then do writeSmallArray ma n rt
                                         fill (n + 1) (removeLeastSignificant m)
                                 else do let lt = indexSmallArray larr (maskToPos lmask (fromIntegral nib))
                                             newt = go newk lt rt
                                         writeSmallArray ma n newt
                                         (rt *==* newt &&) <$> fill (n + 1) (removeLeastSignificant m)
                 sharer <- fill 0 mask
                 if sharer then pure r
                           else Node crumb offt mask <$> unsafeFreezeSmallArray ma
    | otherwise
    = runST $ do ma <- newSmallArray (popCount mask) undefined
                 let fill _ 0 = pure ()
                     fill !n m | b <- leastSignificant m
                               , nib <- countTrailingZeros b
                               , newk <- k' .|. nibbleShiftL (makeNibble (fromIntegral nib)) offt
                               = if | lmask .&. b == 0 -> do let rt = indexSmallArray rarr (maskToPos rmask (fromIntegral nib))
                                                             writeSmallArray ma n rt
                                                             fill (n + 1) (removeLeastSignificant m)
                                    | rmask .&. b == 0 -> do let lt = indexSmallArray larr (maskToPos lmask (fromIntegral nib))
                                                             writeSmallArray ma n lt
                                                             fill (n + 1) (removeLeastSignificant m)
                                    | otherwise -> do let lt = indexSmallArray larr (maskToPos lmask (fromIntegral nib))
                                                          rt = indexSmallArray rarr (maskToPos rmask (fromIntegral nib))
                                                          newt = go newk lt rt
                                                      writeSmallArray ma n newt
                                                      fill (n + 1) (removeLeastSignificant m)
                 fill 0 mask
                 NF crumb offt mask <$> unsafeFreezeSmallArray ma
    where k' = k .|. nibbleShiftL crumb (offt + 1)
          mask = lmask .|. rmask
  go k (Node crumb offt lmask larr) r@(Full _ _ rarr)
    = runST $ do ma <- newSmallArray 0x10 undefined
                 let fill 0x10 = pure True
                     fill !nib | newk <- k' .|. nibbleShiftL (makeNibble (fromIntegral nib)) offt
                               , rt <- indexSmallArray rarr nib
                               = if lmask .&. bit nib == 0
                                 then do writeSmallArray ma nib rt
                                         fill (nib + 1)
                                 else do let lt = indexSmallArray larr (maskToPos lmask nib)
                                             newt = go newk lt rt
                                         writeSmallArray ma nib newt
                                         (rt *==* newt &&) <$> fill (nib + 1)
                 sharer <- fill 0
                 if sharer then pure r
                           else Full crumb offt <$> unsafeFreezeSmallArray ma
    where k' = k .|. nibbleShiftL crumb (offt + 1)
  go k l@(Full crumb offt larr) (Node _ _ rmask rarr)
    = runST $ do ma <- newSmallArray 0x10 undefined
                 let fill 0x10 = pure True
                     fill !nib | newk <- k' .|. nibbleShiftL (makeNibble (fromIntegral nib)) offt
                               , lt <- indexSmallArray larr nib
                               = if rmask .&. bit nib == 0
                                 then do writeSmallArray ma nib lt
                                         fill (nib + 1)
                                 else do let rt = indexSmallArray rarr (maskToPos rmask nib)
                                             newt = go newk lt rt
                                         writeSmallArray ma nib newt
                                         (lt *==* newt &&) <$> fill (nib + 1)
                 sharel <- fill 0
                 if sharel then pure l
                           else Full crumb offt <$> unsafeFreezeSmallArray ma
    where k' = k .|. nibbleShiftL crumb (offt + 1)
  go k l@(Full crumb offt larr) r@(Full _ _ rarr)
    = runST $ do ma <- newSmallArray 0x10 undefined
                 let fill 0x10 = pure (True, True)
                     fill !nib | newk <- k' .|. nibbleShiftL (makeNibble (fromIntegral nib)) offt
                               , lt <- indexSmallArray larr nib
                               , rt <- indexSmallArray rarr nib
                               , newt <- go newk lt rt
                               = do writeSmallArray ma nib newt
                                    ((lt *==* newt &&) *** (rt *==* newt &&)) <$> fill (nib + 1)
                 (sharel, sharer) <- fill 0
                 if | sharel -> pure l
                    | sharer -> pure r
                    | otherwise -> Full crumb offt <$> unsafeFreezeSmallArray ma
    where k' = k .|. nibbleShiftL crumb (offt + 1)
  go _ (Node _ _ _ _) (Tip _ _) = error "isProperSubTrie and isDisjointTrie cannot miss that"
  go _ (Full _ _ _) (Tip _ _) = error "isProperSubTrie and isDisjointTrie cannot miss that"
  go _ (Tip _ _) (Node _ _ _ _) = error "isProperSubTrie and isDisjointTrie cannot miss that"
  go _ (Tip _ _) (Full _ _ _) = error "isProperSubTrie and isDisjointTrie cannot miss that"


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


isProperSubTrie :: NibbleQuery k => Trie k v -> Trie k v -> Maybe (Word8, Offset)
isProperSubTrie _ (Tip _ _) = Nothing
isProperSubTrie (Tip lcrumb _) (NF rcrumb rofft _ _) = if nibbleShiftR lcrumb (rofft + 1) == rcrumb
                                                       then Just (getNibble rofft lcrumb, rofft)
                                                       else Nothing
isProperSubTrie (NF lcrumb lofft _ _) (NF rcrumb rofft _ _) = if lofft < rofft && nibbleShiftR lcrumb (rofft - lofft) == rcrumb
                                                              then Just (getNibble (rofft - lofft - 1) lcrumb, rofft - lofft - 1)
                                                              else Nothing
isProperSubTrie Nil _ = error "isProperSubTrie Nil _"
isProperSubTrie _ Nil = error "isProperSubTrie _ Nil"

isDisjointTrie :: NibbleQuery k => Trie k v -> Trie k v -> Maybe (k, Offset, Word8, Offset, Word8, Offset)
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

maskNode :: NibbleQuery k => Offset -> Trie k v -> Trie k v
maskNode _ Nil = Nil
maskNode o (Tip crumb v) = Tip (nibbleMask o crumb) v
maskNode o (Node crumb offt mask arr) = Node (nibbleMask o crumb) offt mask arr
maskNode o (Full crumb offt arr) = Full (nibbleMask o crumb) offt arr

makePair :: Ord b => b -> a -> b -> a -> SmallArray a
makePair lNib l rNib r = if lNib < rNib then makeArr l r else makeArr r l
  where makeArr x y = runST $ do ma <- newSmallArray 2 x
                                 writeSmallArray ma 1 y
                                 unsafeFreezeSmallArray ma


nibbleShiftR :: Bits k => k -> Offset -> k
nibbleShiftR x offt = unsafeShiftR x (fromIntegral $ unsafeShiftL offt 2)

nibbleShiftL :: Bits k => k -> Offset -> k
nibbleShiftL x offt = unsafeShiftL x (fromIntegral $ unsafeShiftL offt 2)

maskToPos :: Mask -> Int -> Int
maskToPos mask b = popCount $ mask .&. (bit b - 1)

leastSignificant :: Mask -> Mask
leastSignificant x = x .&. negate x

removeLeastSignificant :: Mask -> Mask
removeLeastSignificant x = x .&. (x - 1)
