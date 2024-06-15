import Plfa.untyped.DeBruijn

-- Test cases for toDeBruijnAux and toDeBruijn functions
def testToDeBruijn : List (NamedTerm × DeBruijnTerm) :=
  [ (NamedTerm.var "x", DeBruijnTerm.var 0)  -- x
  , (NamedTerm.lam "x" (NamedTerm.var "x"), DeBruijnTerm.lam (DeBruijnTerm.var 0))  -- λx. x
  , (NamedTerm.lam "x" (NamedTerm.var "y"), DeBruijnTerm.lam (DeBruijnTerm.var 1))  -- λx. y
  , (NamedTerm.lam "x" (NamedTerm.lam "y" (NamedTerm.var "x")), DeBruijnTerm.lam (DeBruijnTerm.lam (DeBruijnTerm.var 1)))  -- λx. λy. x
  ]

#eval testToDeBruijn.map (fun (t, expected) => (prettyPrintDeBruijnWrapper expected, prettyPrintDeBruijnWrapper (toDeBruijn t), toDeBruijn t == expected))
-- Expected output:
-- [("x", "x", true),
--  ("λa. a", "λa. a", true),
--  ("λa. b", "λa. b", true),
--  ("λa. λb. a", "λa. λb. a", true)]
