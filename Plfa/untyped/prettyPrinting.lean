import Plfa.untyped.Term
import Plfa.untyped.DeBruijin
import Plfa.untyped.normalizer

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


-- Beta Reduction
def exampleTerm1 := Term.app (Term.lam "x" (Term.var "x")) (Term.var "y")  -- (λx. x) y
#eval prettyPrint  exampleTerm1  -- Should be `y`
#eval prettyPrint (normalize exampleTerm1)  -- Should be `y`

def exampleTerm2 := Term.app (Term.lam "x" (Term.app (Term.var "x") (Term.var "x"))) (Term.lam "x" (Term.var "x"))
#eval prettyPrint exampleTerm2
#eval prettyPrint (normalize exampleTerm2)  -- Should be `λx. x`

def exampleTerm3 := Term.app (Term.app (Term.lam "x" (Term.lam "y" (Term.var "x"))) (Term.var "z")) (Term.var "w")
#eval prettyPrint exampleTerm3
#eval prettyPrint (normalize exampleTerm3)  -- Should be `λy. w z`
