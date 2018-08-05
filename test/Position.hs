{-# Language GADTs
  , LambdaCase
  , FlexibleContexts
  , ConstraintKinds
  , StandaloneDeriving
#-}
module Position (main) where

import Ethambda.System
import Ethambda.Position (position)

import qualified Data

main :: IO ()
main = mapM_ go Data.types
  where
  go t = do
    print t
    print $ position t
    putStrLn ""
