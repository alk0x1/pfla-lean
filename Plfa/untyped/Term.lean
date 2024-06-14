import Init.Data.Repr
import Init.Data.String.Basic -- Ensure we have access to string manipulation functions

def Identifier := String
instance : DecidableEq Identifier := inferInstanceAs (DecidableEq String)

-- Repr instance for Identifier
instance : Repr Identifier where
  reprPrec x _ := Std.Format.text x

inductive Term
| var   : Identifier → Term
| lam   : Identifier → Term → Term
| app   : Term → Term → Term
deriving Repr
open Term

-- -- Repr instance for Term
-- instance : Repr Term where
--   reprPrec
--   | var x, _ => Std.Format.bracket "var " (Std.Format.text x) ""
--   | Term.lam x t, _ => Std.Format.bracket "lam " (Std.Format.text x ++ " " ++ repr t) ""
--   | Term.app t1 t2, _ => Std.Format.paren (repr t1 ++ " " ++ repr t2)

-- -- Substitution function
-- def subst (x : Identifier) (v : Term) : Term → Term
-- | (var y) => if x = y then v else var y
-- | (lam y t) => if x = y then lam y t else lam y (subst x v t)
-- | (app t1 t2) => app (subst x v t1) (subst x v t2)




-- -- Example Identifiers
-- def x : Identifier := "x"
-- def y : Identifier := "y"
-- def z : Identifier := "z"



-- -- Example Terms
-- def term1 := var x
-- def term2 := lam y (var x)
-- def term3 := app (var x) (var y)
-- def term4 := lam x (var x)
-- def term5 := lam z (app (var x) (var y))
-- def term6 := app (lam y (var x)) (lam z (var z))
-- def term7 := lam y (app (var x) (var y))

-- -- Example substitution
-- def v := lam z (var z)

-- -- Substitution Examples
-- def test1 := subst x v term1 -- x -> v in x
-- def test2 := subst x v term2 -- x -> v in (\y.x)
-- def test3 := subst x v term3 -- x -> v in (x y)
-- def test4 := subst x v term4 -- x -> v in (\x.x)
-- def test5 := subst x v term5 -- x -> v in (\z.(x y))
-- def test6 := subst x v term6 -- x -> v in ((\y.x) (\z.z))
-- def test7 := subst x v term7 -- x -> v in (\y.(x y))

-- #eval test1 -- Expected: var (lam z . var z)
-- #eval test2 -- Expected: lam y . var (lam z . var z)
-- -- #eval test3 -- Expected: app (lam z . var z) var y
-- -- #eval test4 -- Expected: lam x . var x
-- -- #eval test5 -- Expected: lam z . app (lam z . var z) var y
-- -- #eval test6 -- Expected: app (lam y . var (lam z . var z)) (lam z . var z)
-- -- #eval test7 -- Expected: lam y . app (lam z . var z) var y
