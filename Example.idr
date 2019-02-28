import Infer
import LType
import Environment

implementation Show LType where
  show (TApp x y) = "(" ++ show x ++ " " ++ show y ++ ")"
  show (TVar x) = show x
  show (TConst x) = x

main : JS_IO ()
main = putStrLn' $ show $ typeOf
  ( extend "int" ([], TConst "Int") $
    extend "string" ([], TConst "String") empty)
  (Let [("id", (Lambda "y" (Variable "y")))] (Variable "id"))
