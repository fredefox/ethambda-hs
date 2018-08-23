import qualified Equivalence as Equivalence
import qualified Position    as Position
import qualified Typecheck   as Typecheck

main :: IO ()
main
  =  Equivalence.main
  >> Position.main
  >> Typecheck.main
