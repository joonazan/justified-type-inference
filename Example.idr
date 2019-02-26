import Infer
import LType
import Environment

implementation Show LType where
  show (TApp x y) = "(" ++ show x ++ " " ++ show y ++ ")"
  show (TVar x) = show x
  show (TConst x) = x

main : IO ()
main = putStrLn $ show $ typeOf empty
  (Lambda "x" (Lambda "y" (Variable "y")))
