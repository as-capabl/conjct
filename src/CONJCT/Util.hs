{-# LANGUAGE OverloadedStrings #-}

module
    CONJCT.Util
      (
        parseNonZeroVector,  
        unSuffix,
        wordsIdent,
        appToHead,
        bigCamel,
        smallCamel
      )
where

import Control.Monad (guard)
import Data.Vector (Vector)
import qualified Data.Vector.Generic as V
import qualified Data.HashMap.Strict as HM
import qualified Data.Aeson as J
import qualified Data.Aeson.Types as J
import Data.Text (Text)
import qualified Data.Text as T

parseNonZeroVector :: J.FromJSON a => J.Object -> Text -> J.Parser (Vector a)
parseNonZeroVector o name = o J..:? name J..!= V.empty

unSuffix :: Text -> Text -> Maybe Text
unSuffix srcSfx fileName = 
  do  
    let lTotal = T.length fileName
        lSrc = T.length srcSfx
        lName = lTotal - lSrc
    guard $ lName > 0
    let (nm, sfx) = T.splitAt lName fileName
    guard $ sfx == srcSfx
    return nm

wordsIdent :: Text -> [Text]
wordsIdent = T.split (elem `flip` ['.', ' ', '/', '\\'])

appToHead :: (Text -> Text) -> Text -> Text
appToHead f s = let (nmHead, nmTail) = T.splitAt 1 s in f nmHead <> nmTail

bigCamel :: [Text] -> Text
bigCamel ss = mconcat (appToHead T.toUpper <$> ss)

smallCamel :: [Text] -> Text
smallCamel [] = ""
smallCamel (s:ss) = appToHead T.toLower s <> mconcat (appToHead T.toUpper <$> ss)