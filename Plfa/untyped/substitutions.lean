import Plfa.untyped.Term

---- Named Term Substitution
-- Substitution function for named terms
def subst (x : String) (v : Term) : Term → Term
| Term.var y => if x = y then v else Term.var y
| Term.lam y t => if x = y then Term.lam y t else Term.lam y (subst x v t)
| Term.app t1 t2 => Term.app (subst x v t1) (subst x v t2)

#eval subst "x" (Term.var "y") (Term.var "x")  -- Should be `y`
#eval subst "x" (Term.var "y") (Term.lam "x" (Term.var "x"))  -- Should be `λx. x`
