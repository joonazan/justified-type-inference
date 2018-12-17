import Infer
import LType

implementation Show LType where
  show (x ~> y) = show x ++ " -> " ++ show y
  show (TVar x) = show x
  show (Primitive x) = x

main : IO ()
main = putStrLn $ show $ typeOf
  (\_ => Nothing)
  (Lambda "x" (Lambda "y" (Variable "y")))
