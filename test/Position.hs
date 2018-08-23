module Position (main) where

import Ethambda.Type
import Ethambda.Position (position)

import qualified Type as Data

main :: IO ()
main = mapM_ go Data.types
  where
  go t = do
    print t
    print $ position t
    putStrLn ""
