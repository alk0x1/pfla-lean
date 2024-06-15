import Plfa.untyped.Term
import Plfa.untyped.DeBruijin

---- Named Lambda Term
def prettyPrint : Term → String
| Term.var x       => x
| Term.lam x t     => String.intercalate "" ["λ", x, ". ", prettyPrint t]
| Term.app t1 t2   => "(" ++ prettyPrint t1 ++ " " ++ prettyPrint t2 ++ ")"

-- Example terms for testing
def id1 := Term.lam "x" (Term.var "x")
def constz := Term.lam "x" (Term.lam "y" (Term.var "x"))
def selfApp := Term.lam "x" (Term.app (Term.var "x") (Term.var "x"))
def doubleApp := Term.lam "f" (Term.lam "x" (Term.app (Term.var "f") (Term.app (Term.var "f") (Term.var "x"))))
def applyArg := Term.app (Term.lam "x" (Term.var "x")) (Term.var "y")
def nestedLambda := Term.lam "x" (Term.lam "y" (Term.lam "z" (Term.app (Term.var "x") (Term.app (Term.var "y") (Term.var "z")))))
def complexApp := Term.app (Term.app (Term.lam "x" (Term.lam "y" (Term.app (Term.var "x") (Term.var "y")))) (Term.lam "z" (Term.var "z"))) (Term.var "w")
def churchTwo := Term.lam "f" (Term.lam "x" (Term.app (Term.var "f") (Term.app (Term.var "f") (Term.var "x"))))
def churchAdd := Term.lam "m" (Term.lam "n" (Term.lam "f" (Term.lam "x" (Term.app (Term.app (Term.var "m") (Term.var "f")) (Term.app (Term.app (Term.var "n") (Term.var "f")) (Term.var "x"))))))
def combineChurch := Term.app (Term.app churchAdd churchTwo) churchTwo

#eval prettyPrint id1
#eval prettyPrint constz
#eval prettyPrint selfApp
#eval prettyPrint doubleApp
#eval prettyPrint applyArg
#eval prettyPrint nestedLambda
#eval prettyPrint complexApp
#eval prettyPrint churchTwo
#eval prettyPrint churchAdd
#eval prettyPrint combineChurch


---- DeBrujin Lambda Term


def prettyPrintDeBruijn : DeBruijnTerm → Nat → String
| DeBruijnTerm.var k, _     => k.repr
| DeBruijnTerm.lam t, c     => "λ" ++ prettyPrintDeBruijn t (c + 1)
| DeBruijnTerm.app t1 t2, c => "(" ++ prettyPrintDeBruijn t1 c ++ " " ++ prettyPrintDeBruijn t2 c ++ ")"


def prettyPrintDeBruijnWrapper (t : DeBruijnTerm) : String :=
  prettyPrintDeBruijn t 0

-- Example De Bruijn terms for testing
def id1_debruijn := DeBruijnTerm.lam (DeBruijnTerm.var 0)
def constz_debruijn := DeBruijnTerm.lam (DeBruijnTerm.lam (DeBruijnTerm.var 1))
def selfApp_debruijn := DeBruijnTerm.lam (DeBruijnTerm.app (DeBruijnTerm.var 0) (DeBruijnTerm.var 0))
def doubleApp_debruijn := DeBruijnTerm.lam (DeBruijnTerm.lam (DeBruijnTerm.app (DeBruijnTerm.var 1) (DeBruijnTerm.app (DeBruijnTerm.var 1) (DeBruijnTerm.var 0))))
def applyArg_debruijn := DeBruijnTerm.app (DeBruijnTerm.lam (DeBruijnTerm.var 0)) (DeBruijnTerm.var 0)
def nestedLambda_debruijn := DeBruijnTerm.lam (DeBruijnTerm.lam (DeBruijnTerm.lam (DeBruijnTerm.app (DeBruijnTerm.var 2) (DeBruijnTerm.app (DeBruijnTerm.var 1) (DeBruijnTerm.var 0)))))
def complexApp_debruijn := DeBruijnTerm.app (DeBruijnTerm.app (DeBruijnTerm.lam (DeBruijnTerm.lam (DeBruijnTerm.app (DeBruijnTerm.var 1) (DeBruijnTerm.var 0)))) (DeBruijnTerm.lam (DeBruijnTerm.var 0))) (DeBruijnTerm.var 0)
def churchTwo_debruijn := DeBruijnTerm.lam (DeBruijnTerm.lam (DeBruijnTerm.app (DeBruijnTerm.var 1) (DeBruijnTerm.app (DeBruijnTerm.var 1) (DeBruijnTerm.var 0))))
def churchAdd_debruijn := DeBruijnTerm.lam (DeBruijnTerm.lam (DeBruijnTerm.lam (DeBruijnTerm.lam (DeBruijnTerm.app (DeBruijnTerm.app (DeBruijnTerm.var 3) (DeBruijnTerm.var 1)) (DeBruijnTerm.app (DeBruijnTerm.app (DeBruijnTerm.var 2) (DeBruijnTerm.var 1)) (DeBruijnTerm.var 0))))))
def combineChurch_debruijn := DeBruijnTerm.app (DeBruijnTerm.app churchAdd_debruijn churchTwo_debruijn) churchTwo_debruijn

-- Conversion and pretty printing
#eval prettyPrintDeBruijnWrapper (toDeBruijn id1)
#eval prettyPrintDeBruijnWrapper (toDeBruijn constz)
#eval prettyPrintDeBruijnWrapper (toDeBruijn selfApp)
#eval prettyPrintDeBruijnWrapper (toDeBruijn doubleApp)
#eval prettyPrintDeBruijnWrapper (toDeBruijn applyArg)
#eval prettyPrintDeBruijnWrapper (toDeBruijn nestedLambda)
#eval prettyPrintDeBruijnWrapper (toDeBruijn complexApp)
#eval prettyPrintDeBruijnWrapper (toDeBruijn churchTwo)
#eval prettyPrintDeBruijnWrapper (toDeBruijn churchAdd)
#eval prettyPrintDeBruijnWrapper (toDeBruijn combineChurch)
