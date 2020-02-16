{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module
    CONJCT
where

import Data.Maybe (fromMaybe, catMaybes, isJust)
import GHC.Generics (Generic)
import Language.Haskell.TH
import qualified Data.Aeson as J
import Control.Monad.Reader
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

type NameMap = Map Text TypeName
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

lookupJM :: (J.FromJSON a, MonadFail m) => Text -> J.Object -> m a
lookupJM n o = 
  do
    v <- maybe (fail $ "No member named " ++ T.unpack n) return $ HM.lookup n o
    resultM $ J.fromJSON v

putDec :: Dec -> SCQ ()
putDec dec =
  do
    ioDecs <- asks fst
    liftIO $ modifyIORef' ioDecs $ (<> Endo (dec:))

type SchemaFile = Text
type MemberName = Text
type TypeName = Text
type IsRequired = Bool

data FieldInfoBasic = FieldInfoBasic {
    fldJSONName :: Text,
    fldHsName :: Name,
    fldType :: Type
  }

data FieldInfoFromJSON = FieldInfoFromJSON {
    fldFromJSON :: Name -> Exp
  }

data FieldInfoToJSON = FieldInfoToJSON {
    fldToJSON :: Name -> Exp
  }

data DefaultFieldInfo = DefaultFieldInfo {
    dfinfoBasic :: FieldInfoBasic,
    dfinfoFromJSON :: FieldInfoFromJSON,
    dfinfoToJSON :: FieldInfoToJSON
  }

type OnType a = a -> J.Object -> Maybe (SCQ Type)
type OnModule a = a -> RelatedModuleSummary a -> J.Object -> Maybe (SCQ ())
type OnMember a = a -> RelatedModuleSummary a -> MemberName -> J.Object -> Maybe (SCQ (RelatedFieldInfo a))
type OnMemberForDefaultFieldInfo a =
    a -> RelatedModuleSummary a -> MemberName -> J.Object -> Maybe (SCQ DefaultFieldInfo)

data SchemaSetting a = SchemaSetting {
    readModuleFile :: a -> Text -> SCQ (RelatedModuleSummary a, J.Object),
    typeNameOfModule :: a -> RelatedModuleSummary a -> SCQ TypeName,
    memberName :: a -> RelatedModuleSummary a -> Text -> SCQ MemberName,
    onType :: [OnType a],
    onModule :: [OnModule a],
    onMember :: [OnMember a]
  }

data ModuleSummary = ModuleSummary {
    msSchemaFile :: SchemaFile,
    msRequiredList :: Vector MemberName
  }

class HasSchemaSetting a
  where
    getSchemaSetting :: a -> SchemaSetting a
    type RelatedModuleSummary a :: *
    type RelatedModuleSummary a = ModuleSummary
    type RelatedFieldInfo a :: *
    type RelatedFieldInfo a = DefaultFieldInfo

callSchemaSetting :: HasSchemaSetting a => (SchemaSetting a -> a -> b) -> a -> b
callSchemaSetting f arg = f (getSchemaSetting arg) arg

newtype SimpleSchemaSetting = SimpleSchemaSetting (SchemaSetting SimpleSchemaSetting)

class HasModuleSummary a
  where
    getModuleSummary :: a -> ModuleSummary

instance HasSchemaSetting SimpleSchemaSetting
  where
    getSchemaSetting (SimpleSchemaSetting x) = x

instance HasModuleSummary ModuleSummary
  where
    getModuleSummary = id

class HasFieldInfoBasic a
  where
    getFieldInfoBasic :: a -> FieldInfoBasic

class HasFieldInfoFromJSON a
  where
    getFieldInfoFromJSON :: a -> FieldInfoFromJSON

class HasFieldInfoToJSON a
  where
    getFieldInfoToJSON :: a -> FieldInfoToJSON

instance HasFieldInfoBasic DefaultFieldInfo
  where
    getFieldInfoBasic = dfinfoBasic

instance HasFieldInfoFromJSON DefaultFieldInfo
  where
    getFieldInfoFromJSON = dfinfoFromJSON

instance HasFieldInfoToJSON DefaultFieldInfo
  where
    getFieldInfoToJSON = dfinfoToJSON


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

typeNameDefault :: HasModuleSummary ms => ms -> SCQ TypeName
typeNameDefault ms =
  do
    let ModuleSummary {..} = getModuleSummary ms
    maybe (fail $ "typeNameDefault: Could not generate a name for " ++ T.unpack msSchemaFile) return $
      do
        nm <- tokenize <$> unSuffix msSchemaFile
        return $ mconcat (appToHead T.toUpper <$> nm)

memberNameDefault :: (MonadFail m, HasModuleSummary ms) => ms -> Text -> m MemberName
memberNameDefault ms k = maybe (fail errMsg) return $
  do
    sTy <- tokenize <$> unSuffix msSchemaFile
    let sMem = tokenize k
    case sTy ++ sMem
      of
        [] -> Nothing
        x:xs -> return $ mconcat (appToHead T.toLower x : (appToHead T.toUpper <$> xs))
  where
    ModuleSummary{..} = getModuleSummary ms
    errMsg = "memberNameDefault: Could not generate a name for " ++ T.unpack k

onModule_object ::
    (   HasSchemaSetting a,
        HasFieldInfoBasic (RelatedFieldInfo a),
        HasFieldInfoFromJSON (RelatedFieldInfo a)) =>
    OnModule a
onModule_object arg ms o =
  do
    guard $ o `isType` "object"
    props <- lookupJM "properties" o
    return $
      do
        nm <- mkName . T.unpack <$> callSchemaSetting typeNameOfModule arg ms
        fields <- makeFields props
        myO <- liftQ $ newName "o"
        putDec $ makeDataDec nm fields
        putDec $ makeFromJSONDec nm myO fields
  where
    makeFields = mapM doMember' . HM.toList
    doMember' (k, J.Object oMem) = doOnMember arg ms k oMem
    doMember' (k, _) = fail $ "onModule_object: illegal member definition for " ++ T.unpack k

makeDataDec :: HasFieldInfoBasic field => Name -> [field] -> Dec
makeDataDec nm fields = DataD [] nm [] Nothing [RecC nm conFields] [deriveClause]
  where
    conFields = toConFields . getFieldInfoBasic <$> fields
    toConFields FieldInfoBasic{..} = (fldHsName, fieldBang, fldType)
    fieldBang = Bang NoSourceUnpackedness SourceStrict
    deriveClause = DerivClause Nothing [
        ConT ''Eq,
        ConT ''Show,
        ConT ''Generic
      ]

makeFromJSONDec :: HasFieldInfoFromJSON field => Name -> Name -> [field] -> Dec
makeFromJSONDec nm myO fields =
    InstanceD
        Nothing
        []
        (ConT ''J.FromJSON `AppT` ConT nm)
        [FunD 'J.parseJSON [ Clause [] (NormalB definition) []]]
  where
    definition =
        VarE 'J.withObject `AppE` (LitE $ StringL $ nameBase nm) `AppE`
            LamE [VarP myO] (
                foldl
                    (\x y -> VarE '(<*>) `AppE` x `AppE` y)
                    (VarE 'pure `AppE` ConE nm)
                    [ fj myO | fj <- fldFromJSON . getFieldInfoFromJSON <$> fields]
              )
    
onModule_knownType :: HasSchemaSetting a => OnModule a
onModule_knownType arg ms o = Just $
  do
    nm <- mkName . T.unpack <$> callSchemaSetting typeNameOfModule arg ms
    x <- doOnType arg o
    putDec $ TySynD nm [] x


isRequired :: HasModuleSummary a => a -> MemberName -> Bool
isRequired ms mn = V.elem mn (msRequiredList . getModuleSummary $ ms)

readModuleFileDefault :: Text -> a -> Text -> SCQ (ModuleSummary, J.Object)
readModuleFileDefault scBaseDir _ scFile =
  do
    let scPath = T.unpack scBaseDir </> T.unpack scFile
    mo <- liftIO (J.decodeFileStrict scPath)
    o <- maybe (fail $ "File read error:" ++ scPath) return mo

    let msSchemaFile = scFile
        msRequiredList = fromMaybe V.empty $ lookupJM "required" o
    return (ModuleSummary{..}, o)

findTop :: MonadFail m => Text -> [Maybe (m a)] -> m a
findTop s l = case catMaybes l
  of
    [] -> fail $ "No appropreate handler: " <> T.unpack s
    x:_ -> x

mkFieldInfo :: MemberName -> Type -> Text -> Name -> DefaultFieldInfo
mkFieldInfo hsName fldType fldJSONName op = DefaultFieldInfo {..}
  where
    fldHsName = mkName $ T.unpack hsName
    fldFromJSON = \vn -> VarE op `AppE` VarE vn `AppE` LitE (StringL $ T.unpack fldJSONName)
    fldToJSON = undefined
    dfinfoBasic = FieldInfoBasic {..}
    dfinfoFromJSON = FieldInfoFromJSON {..}
    dfinfoToJSON = FieldInfoToJSON {..}

-- | For non-zero array members, omited value can be represented by empty array
onMember_nonzeroArray ::
    (HasSchemaSetting a, HasModuleSummary (RelatedModuleSummary a)) =>
    OnMemberForDefaultFieldInfo a
onMember_nonzeroArray arg ms k o =
  do
    guard $ not (isRequired ms k)
    guard $ o `isType` "array"
    minItems <- lookupJM "minItems" o
    guard $ minItems > (0 :: Int)

    return $
      do
        t <- doOnType arg o
        nMem <- callSchemaSetting memberName arg ms k
        return $ mkFieldInfo nMem t k 'parseNonZeroVector

onMember_opt ::
    (HasSchemaSetting a, HasModuleSummary (RelatedModuleSummary a)) =>
    OnMemberForDefaultFieldInfo a
onMember_opt arg ms k o =
  do
    guard $ not (isRequired ms k)

    return $
      do
        t <- doOnType arg o
        nMem <- callSchemaSetting memberName arg ms k
        return $ mkFieldInfo nMem (AppT (ConT ''Maybe) t) k '(J..:?)
    
onMember_default ::
    (HasSchemaSetting a, HasModuleSummary (RelatedModuleSummary a)) =>
    OnMemberForDefaultFieldInfo a
onMember_default arg ms k o = Just $
  do
    t <- doOnType arg o
    nMem <- callSchemaSetting memberName arg ms k
    return $ mkFieldInfo nMem t k '(J..:)

doOnMember ::
    HasSchemaSetting a =>
    a -> RelatedModuleSummary a -> MemberName -> J.Object -> SCQ (RelatedFieldInfo a)
doOnMember arg ms n o =
    findTop "onMember"
        [ onm arg ms n o | onm <- onMember (getSchemaSetting arg) ]

doOnType :: HasSchemaSetting a => a -> J.Object -> SCQ Type
doOnType arg o =
    findTop "onType" [ ont arg o | ont <- onType (getSchemaSetting arg) ]

isType :: J.Object -> Text -> Bool
isType o tCheck = isJust $
  do
    t <- lookupJM "type" o
    guard $ t == tCheck

onType_array :: HasSchemaSetting a => OnType a
onType_array stg o =
  do
    guard $ o `isType` "array"
    oItem <- lookupJM "items" o
    return $ AppT (ConT ''Vector) <$> doOnType stg oItem

onType_int :: OnType a
onType_int _ o =
  do
    guard $ o `isType` "integer" :: Maybe ()
    return $ return (ConT ''Int)

onType_number :: OnType a
onType_number _ o =
  do
    guard $ o `isType` "number"
    return $ return (ConT ''Double)

onType_text :: OnType a
onType_text _ o =
  do
    guard $ o `isType` "string"
    return $ return (ConT ''Text)

onType_bool :: OnType a
onType_bool _ o =
  do
    guard $ o `isType` "boolean"
    return $ return (ConT ''Bool)

onType_dict :: HasSchemaSetting a => OnType a
onType_dict arg o =
  do
    guard $ o `isType` "object"
    guard $ not (HM.member "properties" o)
    aprop <- lookupJM "additionalProperties" o
    return $
      do
        t <- doOnType arg aprop
        return $ ConT ''HashMap `AppT` ConT ''Text `AppT` t


onType_ref :: HasSchemaSetting a => OnType a
onType_ref arg o =
  do
    s <- lookupJM "$ref" o
    return $ ConT <$> doOnModule arg s

-- |allOf keyword; apply only the first schema
onType_allOf :: HasSchemaSetting a => OnType a
onType_allOf arg o =
  do
    x : _ <- lookupJM "allOf" o
    return $ doOnType arg x

onType_fallback :: OnType a
onType_fallback _ _ = Just $ return (ConT ''JSONValue)
    

defaultSchemaSetting ::
    (HasSchemaSetting a, RelatedModuleSummary a ~ ModuleSummary, RelatedFieldInfo a ~ DefaultFieldInfo) =>
    Text -> SchemaSetting a
defaultSchemaSetting path = SchemaSetting {
    readModuleFile = readModuleFileDefault path,
    typeNameOfModule = \_ -> typeNameDefault,
    memberName = \_ -> memberNameDefault,
    onType = onTypeDefaultList,
    onModule = onModuleDefaultList,
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

onModuleDefaultList ::
    (HasSchemaSetting a, HasModuleSummary (RelatedModuleSummary a),
        HasFieldInfoBasic (RelatedFieldInfo a), HasFieldInfoFromJSON (RelatedFieldInfo a)) =>
    [OnModule a]
onModuleDefaultList = [
    onModule_object,
    onModule_knownType
  ]

onMemberDefaultList ::
    (HasSchemaSetting a, HasModuleSummary (RelatedModuleSummary a)) =>
    [OnMemberForDefaultFieldInfo a]
onMemberDefaultList = [
    onMember_nonzeroArray,
    onMember_opt,
    onMember_default
  ]

doOnModule :: HasSchemaSetting a => a -> SchemaFile -> SCQ Name
doOnModule arg scFile =
  do
    iom <- asks snd
    prev <- Map.lookup scFile <$> liftIO (readIORef iom)
    mkName . T.unpack <$> maybe newRegister return prev
  where
    newRegister =
      do
        (ms, o) <- callSchemaSetting readModuleFile arg scFile
        nm <- callSchemaSetting typeNameOfModule arg ms
        findTop "onModule" [ onm arg ms o | onm <- onModule (getSchemaSetting arg) ]
        iom <- asks snd
        liftIO $ modifyIORef' iom $ Map.insert scFile nm
        return nm

fromSchema :: HasSchemaSetting a => a -> Text -> DecsQ
fromSchema stg scFile =
  do
    d <- liftIO $ newIORef $ Endo id
    m <- liftIO $ newIORef Map.empty
    _ <- runReaderT (doOnModule stg scFile) (d, m)
    dEndo <- liftIO $ readIORef d
    return $ appEndo dEndo []
