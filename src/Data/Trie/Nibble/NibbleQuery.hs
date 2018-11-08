{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE UnboxedTuples #-}

module Data.Trie.Nibble.NibbleQuery
  ( NibbleQuery(..)
  )
  where

#include "MachDeps.h"

import Data.Bits
import Data.Int
import Data.Word
import GHC.Integer.GMP.Internals
import GHC.Integer.Logarithms
import GHC.Prim
import GHC.Types
import GHC.Word
import GHC.Natural

-- | A class for efficient extraction of nibbles out of possibly large bit strings.
class Bits a => NibbleQuery a where
  -- | @getNibble i x@ extracts @i@th nibble out of the bit string @x@. For example:
  --
  -- > getNibble 3 0xDEADBEEF = 0xB
  getNibble :: Word -> a -> Word8
  -- | The default implementation performs a right-shift on @x@, which for an @N@-bit string might take @O(N)@.
  default getNibble :: Integral a => Word -> a -> Word8
  getNibble i x = fromIntegral $ 0xF .&. shiftR x (unsafeShiftL (fromIntegral i) 2)

  -- | @nibbleMask i x@ removes all nibbles of @x@ above @i@th. For example:
  --
  -- > nibbleMask 3 0xDEADBEEF = 0xEEF
  nibbleMask :: Word -> a -> a
  -- | The default implementation uses the 'Num' instance to construct a @0xF...F@ bitmask.
  default nibbleMask :: Num a => Word -> a -> a
  nibbleMask i x = x .&. (bit (unsafeShiftL (fromIntegral i) 2) - 1)

  -- | Return the index of the most significant nonzero nibble.
  logNibble :: a -> Word
  logNibble z = go 0 (shiftL z 4) where go !n x | x == zeroBits = n
                                                | otherwise = go (n + 1) (shiftL x 4)

  makeNibble :: Word8 -> a
  makeNibble x = d 
    where a = if testBit x 0 then bit 0 else zeroBits
          b = if testBit x 1 then setBit a 1 else a
          c = if testBit x 2 then setBit b 2 else b
          d = if testBit x 3 then setBit c 3 else c

logNibbleViaWord :: Integral a => a -> Word
logNibbleViaWord x = case fromIntegral x of W64# w -> W# (uncheckedShiftRL# (int2Word# (wordLog2# w)) 2#)

makeNibbleViaNum :: Num a => Word8 -> a
makeNibbleViaNum = fromIntegral

instance NibbleQuery Word8 where logNibble = logNibbleViaWord; makeNibble = makeNibbleViaNum
instance NibbleQuery Word16 where logNibble = logNibbleViaWord; makeNibble = makeNibbleViaNum
instance NibbleQuery Word32 where logNibble = logNibbleViaWord; makeNibble = makeNibbleViaNum
instance NibbleQuery Word64 where logNibble = logNibbleViaWord; makeNibble = makeNibbleViaNum
instance NibbleQuery Word where logNibble = logNibbleViaWord; makeNibble = makeNibbleViaNum

instance NibbleQuery Int8 where logNibble = logNibbleViaWord; makeNibble = makeNibbleViaNum
instance NibbleQuery Int16 where logNibble = logNibbleViaWord; makeNibble = makeNibbleViaNum
instance NibbleQuery Int32 where logNibble = logNibbleViaWord; makeNibble = makeNibbleViaNum
instance NibbleQuery Int64 where logNibble = logNibbleViaWord; makeNibble = makeNibbleViaNum
instance NibbleQuery Int where logNibble = logNibbleViaWord; makeNibble = makeNibbleViaNum

#if WORD_SIZE_IN_BITS == 64
#define GMP_LIMB_NIBBLES 16
#define GMP_LIMB_NIBBLES_LOG2 4
#define GMP_LIMB_BYTES 8
#define GMP_LIMB_BYTES_LOG2 3
#elif WORD_SIZE_IN_BITS == 32
#define GMP_LIMB_NIBBLES 8
#define GMP_LIMB_NIBBLES_LOG2 3
#define GMP_LIMB_BYTES 4
#define GMP_LIMB_BYTES_LOG2 2
#endif

{-
-- | @O(1)@ extraction from positive integers. For negative integers complexity is proportional to the trailing zero count, which averages to @O(1)@ but has a
-- worst case of @O(max(N, i))@ for negated powers of two.
instance NibbleQuery Integer where
  getNibble (W# i) n = case n of (S# x)      | isTrue# (i `geWord#` GMP_LIMB_NIBBLES##) -> if isTrue# (x >=# 0#) then 0 else 0xF
                                             | otherwise -> W8# (0xF## `and#` int2Word# (uncheckedIShiftRL# x (word2Int# (uncheckedShiftL# i 2#))))

                                 Jp# (BN# a) | isTrue# (byte >=# sizeofByteArray# a) -> 0
                                             | otherwise -> select (indexWord8Array# a byte)

                                 Jn# (BN# a) | isTrue# (byte >=# sizeofByteArray# a) -> 0xF
                                             | word <- uncheckedShiftRL# i GMP_LIMB_NIBBLES_LOG2#
                                             , allZeroCoarse 0# (word2Int# word) a
                                             , allZeroFine (word2Int# (uncheckedShiftL# word (GMP_LIMB_NIBBLES_LOG2# -# 1#))) byte a
                                                 -> select (narrow8Word# (int2Word# (negateInt# (indexInt8Array# a byte))))
                                             | otherwise -> select (narrow8Word# (not# (indexWord8Array# a byte)))

      where byte = word2Int# (uncheckedShiftRL# i 1#)

            allZeroCoarse f t a | isTrue# (f ==# t) = True
                                | otherwise = isTrue# (indexWordArray# a f `eqWord#` 0##) && allZeroCoarse (f +# 1#) t a

            allZeroFine f t a | isTrue# (f ==# t) = True
                              | otherwise = isTrue# (indexWord8Array# a f `eqWord#` 0##) && allZeroFine (f +# 1#) t a

            select x | isTrue# (i `and#` 0x1## `eqWord#` 0##) = W8# (0xF## `and#` x)
                     | otherwise = W8# (uncheckedShiftRL# x 4#)
-}

-- | @O(1)@ extraction.
instance NibbleQuery Natural where
  getNibble (W# i) (NatS# x) | isTrue# (i `geWord#` GMP_LIMB_NIBBLES##) = 0
                             | otherwise = W8# (0xF## `and#` uncheckedShiftRL# x (word2Int# (uncheckedShiftL# i 2#)))

  getNibble (W# i) (NatJ# (BN# a)) | isTrue# (byte >=# sizeofByteArray# a) = 0
                                   | otherwise = select (indexWord8Array# a byte)
                                   where byte = word2Int# (uncheckedShiftRL# i 1#)

                                         select x | isTrue# (i `and#` 0x1## `eqWord#` 0##) = W8# (0xF## `and#` x)
                                                  | otherwise = W8# (uncheckedShiftRL# x 4#)

  logNibble (NatS# x) = W# (uncheckedShiftRL# (int2Word# (wordLog2# x)) 2#)
  logNibble (NatJ# (BN# a)) = W# (coarse 0#)
    where bytes = sizeofByteArray# a

          coarse n | isTrue# (uncheckedIShiftL# (n +# 1#) GMP_LIMB_BYTES_LOG2# ># bytes) = error "logNibble invoked on malformed Natural"
                   | isTrue# (indexWordArray# a n `eqWord#` 0##) = coarse (n +# 1#)
                   | otherwise = fine (uncheckedIShiftL# n GMP_LIMB_BYTES_LOG2#)

          fine n | isTrue# (n >=# bytes) = error "logNibble invoked on malformed Natural"
                 | w <- indexWord8Array# a n = if | isTrue# (w `eqWord#` 0##) -> fine (n +# 1#)
                                                  | isTrue# (0xF## `and#` w `eqWord#` 0##) -> 0x1## `or#` int2Word# (uncheckedIShiftL# n 1#)
                                                  | otherwise -> int2Word# (uncheckedIShiftL# n 1#)

  makeNibble = makeNibbleViaNum
