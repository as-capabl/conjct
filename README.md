conjct
=================

Configurable JSON Schema Translator in Haskell

Description
-------------

A Template-Haskell library to translate from JSON schema to Haskell data types.

Status
---------
Experimental

Example
----------

```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}

module
    Data.GlTF.GlTF
where

import qualified Conjct
import qualified Data.Text as T
import Paths_gltf
import Control.Monad.IO.Class (liftIO)

do
    stg <- Conjct.defaultSchemaSetting . T.pack <$> liftIO getDataDir
    Conjct.fromSchema
        stg
        "glTF.schema.json" 
```

