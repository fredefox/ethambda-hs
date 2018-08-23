module Equivalence (main) where

import Ethambda.Type
import Ethambda.Equivalence (equivalence)

import qualified Type as Data

main :: IO ()
main = mapM_ go Data.types
  where
  go t = do
    print t
    print $ equivalence t
    putStrLn ""
