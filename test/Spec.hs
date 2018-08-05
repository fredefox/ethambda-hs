import qualified Equivalence as Equivalence
import qualified Position    as Position

main :: IO ()
main
  =  Equivalence.main
  >> Position.main
