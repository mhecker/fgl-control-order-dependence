{-# LANGUAGE GADTs #-}

module ReferenceCrypto where


import Crypto.Cipher.AES
import Data.ByteArray
import Crypto.Cipher.Types
import Data.Word

import Crypto.Error (CryptoFailable(..), CryptoError(..))


{-
runAES256 key msg =
  let packedKey = pack $ fmap fromIntegral $ key :: Bytes
      packedMsg = pack $ fmap fromIntegral $ msg :: Bytes
      
  in outputs
-}



data Key c a where
  Key :: (BlockCipher c, ByteArray a) => a -> Key c a

-- | Initialize a block cipher
initCipher :: (BlockCipher c, ByteArray a) => Key c a -> Either CryptoError c
initCipher (Key k) = case cipherInit k of
  CryptoFailed e -> Left e
  CryptoPassed a -> Right a

{-
encrypt :: (BlockCipher c, ByteArray a) => Key c a -> IV c -> a -> Either CryptoError a
encrypt secretKey initIV msg =
  case initCipher secretKey of
    Left e -> Left e
    Right c -> Right $ ctrCombine c initIV msg
-}

encrypt :: (BlockCipher c, ByteArray a) => Key c a -> a -> Either CryptoError a
encrypt secretKey msg =
  case initCipher secretKey of
    Left e -> Left e
    Right c -> Right $ ecbEncrypt c msg


runAES256 :: [Word8] -> [Word8] -> [Word8]
runAES256 key msg =
  let packedMsg = pack $ msg :: Bytes
      packedKey = pack $ key :: Bytes
      kkey = Key packedKey :: Key AES256 Bytes
  in case encrypt kkey packedMsg of
       Left e -> error (show e)
       Right result -> fmap (fromIntegral) $ unpack result


