import Plfa.untyped.Term
import Plfa.untyped.DeBruijin


---- Named Term Substitution
-- Substitution function for named terms
def subst (x : String) (v : Term) : Term → Term
| Term.var y => if x = y then v else Term.var y
| Term.lam y t => if x = y then Term.lam y t else Term.lam y (subst x v t)
| Term.app t1 t2 => Term.app (subst x v t1) (subst x v t2)

#eval subst "x" (Term.var "y") (Term.var "x")  -- Should be `y`
#eval subst "x" (Term.var "y") (Term.lam "x" (Term.var "x"))  -- Should be `λx. x`


def termSize : Term → Nat
| Term.var _ => 1
| Term.lam _ t => 1 + termSize t
| Term.app t1 t2 => 1 + termSize t1 + termSize t2


def betaReduce : Term → Option Term
| Term.app (Term.lam x t1) t2 => some (subst x t2 t1)  -- (λx. t1) t2 => t1[x := t2]
| Term.app t1 t2 =>
    match betaReduce t1 with
    | some t1' => some (Term.app t1' t2)
    | none =>
        match betaReduce t2 with
        | some t2' => some (Term.app t1 t2')
        | none => none
| Term.lam x t =>
    match betaReduce t with
    | some t' => some (Term.lam x t')
    | none => none
| _ => none  -- No reduction possible for variables



partial def normalize (t : Term) : Term :=
  match betaReduce t with
  | some t' => normalize t'
  | none => t
