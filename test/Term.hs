module Term (terms) where

import Ethambda.Term

-- "a -> a"
-- neg: a; pos: a
i :: Term Int
i = Fun $ Var 0

-- "a -> b -> a"
-- neg: a, b; pos: a
k :: Term Int
k = Fun $ Fun $ Var 1

-- "i -> b"
-- uninhabited
forget :: Term Int
forget = Fun $ Fun $ Var 0

terms :: [Term Int]
terms = [ i, k, forget ]
