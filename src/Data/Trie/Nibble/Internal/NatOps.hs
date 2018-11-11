{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UnboxedTuples #-}

module Data.Trie.Nibble.Internal.NatOps
  ( getNibble
  , maskNibble
  , logNibble
  , wlog2

  , MutBigNat
  , newZeroMBNForNibble
  , uncheckedXorNibblesMBN
  , unsafeRenormFreezeMBN
  , safeRenormFreezeMBN
  , unsafeFreezeMBN
  , safeFreezeMBN
  )
  where

#include "MachDeps.h"

import Control.Monad
import Control.Monad.Primitive
import Data.Bits
import Data.Primitive.ByteArray
import Data.Word
import GHC.Exts
import GHC.Integer.GMP.Internals
import GHC.Integer.Logarithms
import GHC.Natural
import GHC.ST

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

_shrinkMutableByteArray :: PrimMonad m => MutableByteArray (PrimState m) -> Int -> m ()
_shrinkMutableByteArray (MutableByteArray mba) (I# sz) = primitive_ $ shrinkMutableByteArray# mba sz

type MutBigNat = MutableByteArray

-- | Create a 'MutBigNat' with a given amount of limbs. The contents might be garbage.
newGarbageMBN :: Word -> ST s (MutBigNat s)
newGarbageMBN limbs = do let bytes = fromIntegral $ unsafeShiftL limbs GMP_LIMB_BYTES_LOG2
                         newByteArray bytes
{-# INLINE newGarbageMBN #-}

-- | Create a zero 'MugBigNat' with a given amount of limbs.
newZeroMBN :: Word -> ST s (MutBigNat s)
newZeroMBN limbs = do let bytes = fromIntegral $ unsafeShiftL limbs GMP_LIMB_BYTES_LOG2
                      ma <- newByteArray bytes
                      fillByteArray ma 0 bytes 0x00
                      return ma
{-# INLINE newZeroMBN #-}

-- | Create a zero 'MutBigNat' wide enough to fit a given nibble index.
newZeroMBNForNibble :: Word -> ST s (MutBigNat s)
newZeroMBNForNibble n = newZeroMBN $ unsafeShiftR (n + GMP_LIMB_NIBBLES) GMP_LIMB_NIBBLES_LOG2
{-# INLINE newZeroMBNForNibble #-}

-- | Freeze a 'MutBigNat' without copying or renormalization. The highest order limb must be nonzero.
unsafeFreezeMBN :: MutBigNat s -> ST s Natural
unsafeFreezeMBN ma = do ByteArray a <- unsafeFreezeByteArray ma
                        return (NatJ# (BN# a))
{-# INLINE unsafeFreezeMBN #-}

-- | Make a copy of a 'MutBigNat' and freeze it without renormalization. The highest order limb must be nonzero.
safeFreezeMBN :: MutBigNat s -> ST s Natural
safeFreezeMBN ma = do let bytes = sizeofMutableByteArray ma
                      ca <- newByteArray bytes
                      copyMutableByteArray ca 0 ma 0 bytes
                      unsafeFreezeMBN ca
{-# INLINE safeFreezeMBN #-}

-- | Renormalize and freeze a 'MutBigNat' without copying.
unsafeRenormFreezeMBN :: MutBigNat s -> ST s Natural
unsafeRenormFreezeMBN ma = let sz = unsafeShiftR (sizeofMutableByteArray ma) GMP_LIMB_BYTES_LOG2
                           in if | sz == 0 -> return (NatS# 0##)
                                 | sz == 1 -> do W# w <- readByteArray ma 0
                                                 return (NatS# w)
                                 | otherwise -> do limb :: Word <- readByteArray ma (sz - 1)
                                                   if limb == 0
                                                   then go (sz - 1)
                                                   else unsafeFreezeMBN ma
                           where go 1 = do W# w <- readByteArray ma 0
                                           return (NatS# w)
                                 go sz = do limb :: Word <- readByteArray ma (sz - 1)
                                            if limb == 0
                                            then go (sz - 1)
                                            else do _shrinkMutableByteArray ma (unsafeShiftL sz GMP_LIMB_BYTES_LOG2)
                                                    unsafeFreezeMBN ma
{-# INLINABLE unsafeRenormFreezeMBN #-}

-- | Make a copy of a 'MutBigNat', renormalize and freeze it.
safeRenormFreezeMBN :: MutBigNat s -> ST s Natural
safeRenormFreezeMBN ma = let sz = unsafeShiftR (sizeofMutableByteArray ma) GMP_LIMB_BYTES_LOG2
                         in if | sz == 0 -> return (NatS# 0##)
                               | sz == 1 -> do W# w <- readByteArray ma 0
                                               return (NatS# w)
                               | otherwise -> go sz
                           where go 1 = do W# w <- readByteArray ma 0
                                           return (NatS# w)
                                 go sz = do limb :: Word <- readByteArray ma (sz - 1)
                                            if limb == 0
                                            then go (sz - 1)
                                            else do let bytes = unsafeShiftL sz GMP_LIMB_BYTES_LOG2
                                                    ca <- newByteArray bytes
                                                    copyMutableByteArray ca 0 ma 0 bytes
                                                    unsafeFreezeMBN ca
{-# INLINABLE safeRenormFreezeMBN #-}

-- | @getNibble i n@ extracts the @i@'th nibble out of the number @n@.
--
-- > getNibble 0xDEADBEEF 3 = 0xB
getNibble :: Word -> Natural -> Word8
getNibble i (NatS# x) | i >= GMP_LIMB_NIBBLES = 0
                      | otherwise = fromIntegral $ 0xF .&. unsafeShiftR (W# x) (fromIntegral $ unsafeShiftL i 2)
getNibble i (NatJ# (BN# bn)) | byte >= sizeofByteArray a = 0
                             | otherwise = select (indexByteArray a byte)
                             where a = ByteArray bn
                                   byte = fromIntegral $ unsafeShiftR i 1
                                   select x | i .&. 1 == 0 = 0xF .&. x
                                            | otherwise = unsafeShiftR x 4
                                   {-# INLINE select #-}
{-# INLINABLE getNibble #-}

-- | @maskNibble i n@ removes all nibbles except the first @i@ from the number @n@.
--
-- > maskNibble 4 0xDEADBEEF = 0xBEEF
maskNibble :: Word -> Natural -> Natural
maskNibble i orig@(NatS# x)
  | i >= GMP_LIMB_NIBBLES = orig
  | otherwise 
  , W# r <- W# x .&. (unsafeShiftL 1 (fromIntegral $ unsafeShiftL i 2) - 1)
  = NatS# r
maskNibble i orig@(NatJ# (BN# bn))
  | byte >= sizeofByteArray a = orig
  | i == GMP_LIMB_NIBBLES
  , W# r <- indexByteArray a 0
  = NatS# r
  | i < GMP_LIMB_NIBBLES
  , W# r <- indexByteArray a 0 .&. (unsafeShiftL 1 (fromIntegral $ unsafeShiftL i 2) - 1)
  = NatS# r
  | otherwise
  , word <- min (unsafeShiftR (i + GMP_LIMB_NIBBLES - 1) GMP_LIMB_NIBBLES_LOG2)
                (unsafeShiftR (fromIntegral $ sizeofByteArray a) GMP_LIMB_BYTES_LOG2)
  = runST $ do ma <- newGarbageMBN word
               writeByteArray ma (fromIntegral $ word - 1) (0 :: Word)
               copyByteArray ma 0 a 0 byte
               when (i .&. 0x1 /= 0) $ writeByteArray ma byte (0xF .&. indexByteArray a byte :: Word8)
               unsafeRenormFreezeMBN ma
  where a = ByteArray bn
        byte = fromIntegral $ unsafeShiftR i 1
{-# INLINABLE maskNibble #-}

-- | @logNibble n@ finds the index of the most significant nonzero nibble.
--
-- > @logNibble 0x123DEAD = 6
logNibble :: Natural -> Word
logNibble (NatS# x) = fromIntegral $ unsafeShiftR (I# (wordLog2# x)) 2
logNibble (NatJ# (BN# bn)) = go bytes
  where a = ByteArray bn
        bytes = sizeofByteArray a

        go n | w :: Word8 <- indexByteArray a (n - 1)
             = if | w == 0 -> go (n - 1)
                  | w .&. 0xF0 == 0 -> fromIntegral $ unsafeShiftL (n - 1) 1
                  | otherwise -> fromIntegral $ 0x1 .|. unsafeShiftL (n - 1) 1
{-# INLINE logNibble #-}

wlog2 :: Word -> Int
wlog2 (W# x) = I# (wordLog2# x)
{-# INLINE wlog2 #-}

-- | Bitwise "XOR" a given natural number at a given nibble offset into a 'MutBigNat'. The 'MutBigNat' must have enough
-- limbs for the operation.
uncheckedXorNibblesMBN :: MutBigNat s -> Word -> Natural -> ST s ()
uncheckedXorNibblesMBN ma offt n
  | nibble == 0
  = case n of NatS# x -> do w <- readByteArray ma lofft
                            writeByteArray ma lofft (w `xor` W# x)
              NatJ# (BN# bn) -> let a = ByteArray bn
                                    limbs = unsafeShiftR (sizeofByteArray a) GMP_LIMB_BYTES_LOG2

                                    loop i | i == limbs = pure ()
                                    loop i = do w :: Word <- readByteArray ma (lofft + i)
                                                writeByteArray ma (lofft + i) (w `xor` indexByteArray a i)
                                                loop (i + 1)
                                in loop 0
  | otherwise
  , nibbleShift <- unsafeShiftL nibble 2
  , nibbleCoshift <- unsafeShiftL (GMP_LIMB_NIBBLES - nibble) 2
  = case n of NatS# x -> do w1 <- readByteArray ma lofft
                            writeByteArray ma lofft (w1 `xor` unsafeShiftL (W# x) nibbleShift)
                            when (unsafeShiftR (W# x) nibbleCoshift /= 0) $ do
                              w2 <- readByteArray ma (lofft + 1)
                              writeByteArray ma (lofft + 1) (w2 `xor` unsafeShiftR (W# x) nibbleCoshift)
              NatJ# (BN# bn) -> let a = ByteArray bn
                                    limbs = unsafeShiftR (sizeofByteArray a) GMP_LIMB_BYTES_LOG2

                                    loop i prev = do
                                      let !x = indexByteArray a i
                                      writeByteArray ma (lofft + i) (prev `xor` unsafeShiftL x nibbleShift)
                                      if | unsafeShiftR x nibbleCoshift /= 0
                                         -> do w <- readByteArray ma (lofft + i + 1)
                                               loop (i + 1) (w `xor` unsafeShiftR x nibbleCoshift)
                                         | i < limbs - 1
                                         -> do w <- readByteArray ma (lofft + i + 1)
                                               loop (i + 1) w
                                         | otherwise
                                         -> pure ()

                                in do w :: Word <- readByteArray ma lofft
                                      loop 0 w
  where nibble = fromIntegral $ offt .&. (GMP_LIMB_NIBBLES - 1)
        lofft = fromIntegral $ unsafeShiftR offt GMP_LIMB_NIBBLES_LOG2
{-# INLINABLE uncheckedXorNibblesMBN #-}
