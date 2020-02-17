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

import Data.Maybe (catMaybes, isJust)
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



isRequired :: HasModuleSummary a => a -> MemberName -> Bool
isRequired ms mn = V.elem mn (msRequiredList . getModuleSummary $ ms)

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


doOnMember ::
    HasSchemaSetting a =>
    a -> RelatedModuleSummary a -> MemberName -> J.Object -> SCQ (RelatedFieldInfo a)
doOnMember arg ms n o =
    findTop "onMember"
        [ onm arg ms n o | onm <- onMember (getSchemaSetting arg) ]

doOnMemberList ::
    (HasSchemaSetting a, Traversable t) =>
    a -> RelatedModuleSummary a -> t (MemberName, JSONValue) -> SCQ (t (RelatedFieldInfo a))
doOnMemberList arg ms = mapM doMember'
  where
    doMember' (k, J.Object o) = doOnMember arg ms k o
    doMember' (k, _) = fail $ "onModule_object: illegal member definition for " ++ T.unpack k

doOnType :: HasSchemaSetting a => a -> J.Object -> SCQ Type
doOnType arg o =
    findTop "onType" [ ont arg o | ont <- onType (getSchemaSetting arg) ]

isType :: J.Object -> Text -> Bool
isType o tCheck = isJust $
  do
    t <- lookupJM "type" o
    guard $ t == tCheck

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

fromSchema :: HasSchemaSetting a => a -> [Text] -> DecsQ
fromSchema stg files =
  do
    d <- liftIO $ newIORef $ Endo id
    m <- liftIO $ newIORef Map.empty
    forM_ files $ \file -> runReaderT (doOnModule stg file) (d, m)
    dEndo <- liftIO $ readIORef d
    return $ appEndo dEndo []
