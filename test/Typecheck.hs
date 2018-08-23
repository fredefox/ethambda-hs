module Typecheck (main) where

import Ethambda.Typecheck (typecheck)

import qualified Term as Data

main :: IO ()
main = mapM_ go Data.terms
  where
  go t = do
    print t
    typecheck t
    putStrLn ""
