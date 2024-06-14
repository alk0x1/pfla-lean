import Plfa.untyped.Term

open Term

def prettyPrint : Term → String
| var x       => x
| lam x t     => String.intercalate "" ["λ", x, ". ", prettyPrint t]
| app t1 t2   => "(" ++ prettyPrint t1 ++ " " ++ prettyPrint t2 ++ ")"

-- Example terms for testing
def id1 := lam "x" (var "x")
def const := lam "x" (lam "y" (var "x"))
def selfApp := lam "x" (app (var "x") (var "x"))
def doubleApp := lam "f" (lam "x" (app (var "f") (app (var "f") (var "x"))))
def applyArg := app (lam "x" (var "x")) (var "y")
def nestedLambda := lam "x" (lam "y" (lam "z" (app (var "x") (app (var "y") (var "z")))))
def complexApp := app (app (lam "x" (lam "y" (app (var "x") (var "y")))) (lam "z" (var "z"))) (var "w")
def churchTwo := lam "f" (lam "x" (app (var "f") (app (var "f") (var "x"))))
def churchAdd := lam "m" (lam "n" (lam "f" (lam "x" (app (app (var "m") (var "f")) (app (app (var "n") (var "f")) (var "x"))))))
def combineChurch := app (app churchAdd churchTwo) churchTwo

#eval prettyPrint id1
#eval prettyPrint const
#eval prettyPrint selfApp
#eval prettyPrint doubleApp
#eval prettyPrint applyArg
#eval prettyPrint nestedLambda
#eval prettyPrint complexApp
#eval prettyPrint churchTwo
#eval prettyPrint churchAdd
#eval prettyPrint combineChurch

def isFree (x : Identifier) : Term → Bool
| var y       => x = y
| lam y t     => x ≠ y ∧ isFree x t
| app t1 t2   => isFree x t1 ∨ isFree x t2

-- Example terms for testing isFree
def x := var "x"
def y := var "y"
def id2 := lam "x" (var "x")
def constx := lam "x" (lam "y" (var "x"))
def nested := lam "y" (lam "x" (app (var "x") (var "y")))
def appExample := app (lam "x" (var "x")) (var "y")

-- Testing isFree function
#eval isFree "x" x
#eval isFree "y" x
#eval isFree "x" y
#eval isFree "y" y
#eval isFree "x" id2
#eval isFree "y" id2
#eval isFree "x" const
#eval isFree "y" const
#eval isFree "x" nested
#eval isFree "y" nested
#eval isFree "x" appExample
#eval prettyPrint appExample
#eval isFree "y" appExample
