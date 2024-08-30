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

---- Conversion and pretty printing
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


---- Beta Reduction
-- (λx. x) y => y
def exampleTerm1 := toDeBruijn (Term.app (Term.lam "x" (Term.var "x")) (Term.var "y"))
#eval prettyPrintDeBruijnWrapper exampleTerm1  -- Should print: "λ. 0 1"
#eval prettyPrintDeBruijnWrapper (normalizeDeBruijn exampleTerm1)  -- Should print: "1"

-- (λx. x x) (λx. x) => λx. x
def exampleTerm2 := toDeBruijn (Term.app (Term.lam "x" (Term.app (Term.var "x") (Term.var "x"))) (Term.lam "x" (Term.var "x")))
#eval prettyPrintDeBruijnWrapper exampleTerm2  -- Should print: "(λ. 0 0) λ. 0"
#eval prettyPrintDeBruijnWrapper (normalizeDeBruijn exampleTerm2)  -- Should print: "λ. 0"

-- ((λx. λy. x) z) w => λy. z
def exampleTerm3 := toDeBruijn (Term.app (Term.app (Term.lam "x" (Term.lam "y" (Term.var "x"))) (Term.var "z")) (Term.var "w"))
#eval prettyPrintDeBruijnWrapper exampleTerm3  -- Should print: "(λ. λ. 1) 1 0"
#eval prettyPrintDeBruijnWrapper (normalizeDeBruijn exampleTerm3)  -- Should print: "λ. 1"

-- Double application: (λf. λx. f (f x)) (λy. y) => λx. x
def exampleTerm4 := toDeBruijn (Term.app (Term.lam "f" (Term.lam "x" (Term.app (Term.var "f") (Term.app (Term.var "f") (Term.var "x"))))) (Term.lam "y" (Term.var "y")))
#eval prettyPrintDeBruijnWrapper exampleTerm4  -- Should print: "(λ. λ. 1 (1 0)) λ. 0"
#eval prettyPrintDeBruijnWrapper (normalizeDeBruijn exampleTerm4)  -- Should print: "λ. λ. 0 (0 0)"

-- Church numeral 2 applied to a function: (λf. λx. f (f x)) g => λx. g (g x)
def exampleTerm5 := toDeBruijn (Term.app (Term.lam "f" (Term.lam "x" (Term.app (Term.var "f") (Term.app (Term.var "f") (Term.var "x"))))) (Term.var "g"))
#eval prettyPrintDeBruijnWrapper exampleTerm5  -- Should print: "(λ. λ. 1 (1 0)) 0"
#eval prettyPrintDeBruijnWrapper (normalizeDeBruijn exampleTerm5)  -- Should print: "λ. 0 (0 0)"

-- Church numeral addition: (λm. λn. λf. λx. m f (n f x)) 2 2 => λf. λx. f (f (f (f x)))
def exampleTerm6 := toDeBruijn (Term.app (Term.app churchAdd churchTwo) churchTwo)
#eval prettyPrintDeBruijnWrapper exampleTerm6  -- Should print: "λ. λ. 3 2 (1 0)"
#eval prettyPrintDeBruijnWrapper (normalizeDeBruijn exampleTerm6)  -- Should print: "λ. λ. 1 (1 (1 (1 0)))"

-- Complex nested application: ((λx. λy. x y) (λz. z)) w => w
def exampleTerm7 := toDeBruijn (Term.app (Term.app (Term.lam "x" (Term.lam "y" (Term.app (Term.var "x") (Term.var "y")))) (Term.lam "z" (Term.var "z"))) (Term.var "w"))
#eval prettyPrintDeBruijnWrapper exampleTerm7  -- Should print: "(λ. λ. 1 0) λ. 0 1"
#eval prettyPrintDeBruijnWrapper (normalizeDeBruijn exampleTerm7)  -- Should print: "0"

-- Nested Lambda: λx. λy. λz. x (y z)
def exampleTerm8 := toDeBruijn (Term.lam "x" (Term.lam "y" (Term.lam "z" (Term.app (Term.var "x") (Term.app (Term.var "y") (Term.var "z"))))))
#eval prettyPrintDeBruijnWrapper exampleTerm8  -- Should print: "λ. λ. λ. 2 (1 0)"
#eval prettyPrintDeBruijnWrapper (normalizeDeBruijn exampleTerm8)  -- Should print the same since it's already normal

-- Self-application (does not normalize): (λx. x x) (λx. x x)
def exampleTerm9 := toDeBruijn (Term.app (Term.lam "x" (Term.app (Term.var "x") (Term.var "x"))) (Term.lam "x" (Term.app (Term.var "x") (Term.var "x"))))
#eval prettyPrintDeBruijnWrapper exampleTerm9  -- Should print: "(λ. 0 0) λ. 0 0"
#eval prettyPrintDeBruijnWrapper (normalizeDeBruijn exampleTerm9)  -- May cause infinite loop, Lean will handle the stack limit or recursion depth
