{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RecordWildCards #-}

module
    CONJCT
where

import Data.Maybe (fromMaybe, catMaybes)
import GHC.Generics (Generic)
import Language.Haskell.TH
import qualified Data.Aeson as J
import qualified Data.Aeson.Types as J
import Data.Aeson ((.:))
import Control.Monad.Trans.Maybe
import Control.Monad.Reader
import Control.Monad.IO.Class
import Control.Monad.Fail (MonadFail)
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Text as T
import Data.Monoid (Endo(..), appEndo)
import qualified Data.Vector
import qualified Data.Vector.Generic as V
import qualified Data.HashMap.Strict as HM
import System.FilePath

import CONJCT.Util

type NameMap = Map Text Name
type JSONValue = J.Value
type Vector = Data.Vector.Vector
type Text = T.Text
type HashMap = HM.HashMap

type SCQ = ReaderT (IORef (Endo [Dec]), IORef NameMap) Q

liftQ :: Q a -> SCQ a
liftQ = lift

failQ :: String -> SCQ a
failQ = liftQ . fail

resultM :: MonadFail m => J.Result a -> m a
resultM (J.Error s) = fail s
resultM (J.Success x) = return x

putDec :: Dec -> SCQ ()
putDec dec =
  do
    (ioDecs, _) <- ask
    liftIO $ modifyIORef' ioDecs $ (<> Endo (dec:))

type SchemaFile = Text
type MemberName = Text
type IsRequired = Bool

data FieldInfo = FieldInfo {
    fldJSONName :: Text,
    fldHsName :: Name,
    fldType :: Type,
    fldFromJSON :: Name -> Exp,
    fldToJSON :: Name -> Exp
  }

type OnType ud = ud -> J.Object -> Maybe (SCQ Type)
type OnModule ud = ud -> SchemaFile -> Maybe (Name, SCQ ())
type OnMember ud = ud -> SchemaFile -> MemberName -> IsRequired -> J.Object -> Maybe (SCQ FieldInfo)

data SchemaSetting ud = SchemaSetting {
    schemaBaseDir :: Text,
    onType :: [OnType ud],
    onModule :: [OnModule ud],
    onMember :: [OnMember ud]
  }

class HasSchemaSetting a
  where
    getSchemaSetting :: a -> SchemaSetting a

newtype SimpleSchemaSetting = SimpleSchemaSetting (SchemaSetting SimpleSchemaSetting)

instance HasSchemaSetting SimpleSchemaSetting
  where
    getSchemaSetting (SimpleSchemaSetting x) = x

schemaSuffix :: Text
schemaSuffix = ".schema.json"

schemaSuffixLen :: Int
schemaSuffixLen = T.length schemaSuffix

unSuffix :: Text -> Maybe Text
unSuffix fileName = 
  do  
    let lTotal = T.length fileName
        lName = lTotal - schemaSuffixLen
    guard $ lName > 0
    let (nm, sfx) = T.splitAt lName fileName
    guard $ sfx == schemaSuffix
    return nm

tokenize :: Text -> [Text]
tokenize = T.splitOn "."

appToHead :: (Text -> Text) -> Text -> Text
appToHead f s = let (nmHead, nmTail) = T.splitAt 1 s in f nmHead <> nmTail

typeNameDefault :: Text -> Maybe Text
typeNameDefault fileName =
  do
    nm <- tokenize <$> unSuffix fileName
    return $ mconcat (appToHead T.toUpper <$> nm)

memberNameDefault :: Text -> Text -> Maybe Text
memberNameDefault fileName k =
  do
    sTy <- tokenize <$> unSuffix fileName
    let sMem = tokenize k
    case sTy ++ sMem
      of
        [] -> Nothing
        x:xs -> return $ mconcat (appToHead T.toLower x : (appToHead T.toUpper <$> xs))

onModuleDefault :: HasSchemaSetting a => OnModule a
onModuleDefault arg scFile =
  do
    nmText <- typeNameDefault scFile
    nm <- return $ mkName $ T.unpack nmText
    return (nm, decl nm)
  where
    stg = getSchemaSetting arg
    decl nm =
      do
        let scPath = T.unpack (schemaBaseDir stg) </> T.unpack scFile
        o <- liftIO (J.decodeFileStrict scPath) >>=
            maybe (fail $ "File read error:" ++ scPath) return
        vType <- maybe (fail $ "No type: " ++ T.unpack scFile) return $  HM.lookup "type" (o :: J.Object)
        t <- resultM $ J.fromJSON vType
        if  | (t :: Text) == "object" -> 
              do
                fields <- makeFields nm o
                let conFields = (\FieldInfo{..} -> (fldHsName, fieldBang, fldType)) <$> fields

                putDec $
                    DataD [] nm [] Nothing [
                        RecC nm conFields
                      ]
                      [
                        DerivClause (Just StockStrategy) [
                            ConT ''Eq,
                            ConT ''Show,
                            ConT ''Generic
                          ]
                      ]
                
                myO <- liftQ $ newName "o"
                putDec $
                    InstanceD Nothing [] (AppT (ConT ''J.FromJSON) (ConT nm)) [
                        FunD 'J.parseJSON [
                            Clause [] (NormalB $
                                VarE 'J.withObject `AppE` (LitE $ StringL $ nameBase nm) `AppE`
                                    LamE [VarP myO] (
                                        foldl
                                            (\x y -> VarE '(<*>) `AppE` x `AppE` y)
                                            (VarE 'pure `AppE` ConE nm)
                                            (($ myO) . fldFromJSON <$> fields)
                                      )
                              )
                                []
                        ]
                      ]
            | otherwise ->
              do
                x <- doOnType arg o
                putDec $ TySynD nm [] x

    makeFields nm o =
      do
        -- properties
        vProps <- 
            maybe (fail $ "No properties: " ++ T.unpack scFile) return $
                HM.lookup "properties" (o :: J.Object)
        props <- resultM $ J.fromJSON vProps

        -- required
        let reqList = fromMaybe V.empty $
                resultM . J.fromJSON @(Vector Text) =<< HM.lookup "required" o

        fields <- forM (HM.toList (props :: J.Object)) $ \(k, J.Object o) ->
          do
            let isReq = V.elem k reqList
            doOnMember arg scFile k isReq o
        return fields

    fieldBang = Bang NoSourceUnpackedness SourceStrict

findTop :: MonadFail m => Text -> [Maybe a] -> Either (m b) a
findTop s l = case catMaybes l
  of
    [] -> Left $ fail $ "No appropreate handler: " <> T.unpack s
    x:_ -> Right x


mkFieldInfo nMem t k op = FieldInfo {..}
  where
    fldType = t
    fldJSONName = k
    fldHsName = mkName $ T.unpack nMem
    fldFromJSON = \vn -> VarE op `AppE` VarE vn `AppE` LitE (StringL $ T.unpack k)
    fldToJSON = undefined

-- | For non-zero array members, omited value can be represented by empty array
onMember_nonzeroArray :: HasSchemaSetting a => OnMember a
onMember_nonzeroArray arg scFile k req o =
  do
    guard $ not req
    checkType o "array"
    minItems <- resultM . J.fromJSON =<< HM.lookup "minItems" o
    guard $ minItems > (0 :: Int)

    return $
      do
        t <- doOnType arg o
        nMem <- maybe (fail "memberName") return $ memberNameDefault scFile k
        return $ mkFieldInfo nMem t k 'parseNonZeroVector

onMember_opt :: HasSchemaSetting a => OnMember a
onMember_opt _ _ _ True o = Nothing
onMember_opt arg scFile k False o = Just $
  do
    t <- doOnType arg o
    nMem <- maybe (fail "memberName") return $ memberNameDefault scFile k
    return $ mkFieldInfo nMem (AppT (ConT ''Maybe) t) k '(J..:?)
    
onMember_default :: HasSchemaSetting a => OnMember a
onMember_default arg scFile k _ o = Just $
  do    
    t <- doOnType arg o
    nMem <- maybe (fail "memberName") return $ memberNameDefault scFile k
    return $ mkFieldInfo nMem t k '(J..:)

doOnMember :: HasSchemaSetting a => a -> SchemaFile -> MemberName -> IsRequired -> J.Object -> SCQ FieldInfo
doOnMember arg s n req o =
    either id id $
        findTop "onMember"
            [ onm arg s n req o | onm <- onMember (getSchemaSetting arg) ]

doOnType :: HasSchemaSetting a => a -> J.Object -> SCQ Type
doOnType arg o =
    either id id $ findTop "onType" [ ont arg o | ont <- onType (getSchemaSetting arg) ]

checkType :: J.Object -> Text -> Maybe ()
checkType o tCheck =
  do
    t <- resultM . J.fromJSON =<< HM.lookup "type" o
    guard $ t == tCheck


onType_array :: HasSchemaSetting a => OnType a
onType_array stg o =
  do
    checkType o "array"
    oItem <- resultM . J.fromJSON =<< HM.lookup "items" o

    return $
      do
        t <- doOnType stg oItem
        return $ AppT (ConT ''Vector) t

onType_int :: OnType ud
onType_int _ o =
  do
    checkType o "integer"
    return $ return (ConT ''Int)

onType_number :: OnType ud
onType_number _ o =
  do
    checkType o "number"
    return $ return (ConT ''Double)

onType_text :: OnType ud
onType_text _ o =
  do
    checkType o "string"
    return $ return (ConT ''Text)

onType_bool :: OnType ud
onType_bool _ o =
  do
    checkType o "boolean"
    return $ return (ConT ''Bool)

onType_dict :: HasSchemaSetting a => OnType a
onType_dict arg o =
  do
    checkType o "object"
    guard $ HM.lookup "properties" o == Nothing
    aprop <- resultM . J.fromJSON =<< HM.lookup "additionalProperties" o
    return $
      do
        t <- doOnType arg aprop
        return $ ConT ''HashMap `AppT` ConT ''Text `AppT` t


onType_ref :: HasSchemaSetting a => OnType a
onType_ref arg o =
  do
    s <- resultM . J.fromJSON =<< HM.lookup "$ref" o

    return $
      do
        n <- doOnModule arg s
        return $ ConT n

onType_allOf :: HasSchemaSetting a => OnType a
onType_allOf arg o =
  do
    x : _ <- resultM . J.fromJSON =<< HM.lookup "allOf" o
    xObj <- resultM $ J.fromJSON x

    return $
      do
        doOnType arg xObj
    


onType_fallback :: OnType a
onType_fallback _ _ = Just $ return (ConT ''JSONValue)
    

defaultSchemaSetting :: HasSchemaSetting a => Text -> SchemaSetting a
defaultSchemaSetting path = SchemaSetting {
    schemaBaseDir = path,
    onType = onTypeDefaultList,
    onModule = [onModuleDefault],
    onMember = onMemberDefaultList
  }

onTypeDefaultList :: HasSchemaSetting a => [OnType a]
onTypeDefaultList = [
    onType_array,
    onType_ref,
    onType_int,
    onType_number,
    onType_text,
    onType_bool,
    onType_dict,
    onType_allOf,
    onType_fallback
  ]

onMemberDefaultList :: HasSchemaSetting a => [OnMember a]
onMemberDefaultList = [
    onMember_nonzeroArray,
    onMember_opt,
    onMember_default
  ]

doOnModule :: HasSchemaSetting a => a -> SchemaFile -> SCQ Name
doOnModule arg s =
  do
    iom <- snd <$> ask
    prev <- Map.lookup s <$> liftIO (readIORef iom)
    case prev
      of
        Just n -> 
            return n
        Nothing ->
            either id execAndRegister $
                findTop "onModule" [ onm arg s | onm <-  onModule (getSchemaSetting arg) ]
  where
    execAndRegister (n, action) =
      do
        iom <- snd <$> ask
        liftIO $ modifyIORef' iom $ Map.insert s n
        action
        return n :: SCQ Name

fromSchema :: HasSchemaSetting a => a -> Text -> DecsQ
fromSchema stg scFile =
  do
    d <- liftIO $ newIORef $ Endo id
    m <- liftIO $ newIORef Map.empty
    runReaderT (doOnModule stg scFile) (d, m)
    dEndo <- liftIO $ readIORef d
    return $ appEndo dEndo []
