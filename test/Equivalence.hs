{-# Language GADTs
  , LambdaCase
  , FlexibleContexts
  , ConstraintKinds
  , StandaloneDeriving
#-}
module Equivalence where

import Ethambda.System
import Ethambda.Equivalence (equivalence)

import qualified Data

main :: IO ()
main = mapM_ go Data.types
  where
  go t = do
    print t
    print $ equivalence t
    putStrLn ""
