module
    CONJCT.Util
      (
        parseNonZeroVector,  
      )
where

import Data.Vector (Vector)
import qualified Data.Vector.Generic as V
import qualified Data.HashMap.Strict as HM
import qualified Data.Aeson as J
import qualified Data.Aeson.Types as J
import Data.Text (Text)
import qualified Data.Text as T

parseNonZeroVector :: J.FromJSON a => J.Object -> Text -> J.Parser (Vector a)
parseNonZeroVector o name = o J..:? name J..!= V.empty
