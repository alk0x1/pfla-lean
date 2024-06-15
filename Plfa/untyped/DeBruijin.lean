import Plfa.untyped.Term
import Plfa.untyped.helpers

inductive DeBruijnTerm
| var : Nat → DeBruijnTerm
| lam : DeBruijnTerm → DeBruijnTerm
| app : DeBruijnTerm → DeBruijnTerm → DeBruijnTerm
deriving Repr, BEq

-- Conversion context keeps track of variable bindings
def toDeBruijnAux : List String → Term → DeBruijnTerm
| ctx, Term.var x     => DeBruijnTerm.var (indexOf x ctx)
| ctx, Term.lam x t   => DeBruijnTerm.lam (toDeBruijnAux (x :: ctx) t)
| ctx, Term.app t1 t2 => DeBruijnTerm.app (toDeBruijnAux ctx t1) (toDeBruijnAux ctx t2)

def toDeBruijn (t : Term) : DeBruijnTerm :=
  toDeBruijnAux [] t


def testToDeBruijn : List (Term × DeBruijnTerm) :=
  [ (Term.var "x", DeBruijnTerm.var 0)  -- x
  , (Term.lam "x" (Term.var "x"), DeBruijnTerm.lam (DeBruijnTerm.var 0))  -- λx. x
  , (Term.lam "x" (Term.var "y"), DeBruijnTerm.lam (DeBruijnTerm.var 1))  -- λx. y
  ]


#eval testToDeBruijn.map (fun (t, expected) => (t, expected, toDeBruijn t, toDeBruijn t == expected))
