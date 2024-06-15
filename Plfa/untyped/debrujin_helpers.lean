-- import Plfa.untyped.DeBruijin

-- -- Helper function to find the index of a variable in the context
-- def indexOf (x : String) : List String → Nat
-- | []        => 0
-- | (y :: ys) => if x = y then 0 else 1 + indexOf x ys

-- -- Conversion context keeps track of variable bindings
-- def toDeBruijnAux : List String → NamedTerm → DeBruijnTerm
-- | ctx, NamedTerm.var x     => DeBruijnTerm.var (indexOf x ctx)
-- | ctx, NamedTerm.lam x t   => DeBruijnTerm.lam (toDeBruijnAux (x :: ctx) t)
-- | ctx, NamedTerm.app t1 t2 => DeBruijnTerm.app (toDeBruijnAux ctx t1) (toDeBruijnAux ctx t2)

-- def toDeBruijn (t : NamedTerm) : DeBruijnTerm :=
--   toDeBruijnAux [] t

-- -- Helper function to convert De Bruijn indices back to variable names for readability
-- def toVarName (k : Nat) : String :=
--   let asciiOffset := 97  -- 'a' in ASCII
--   String.singleton (Char.ofNat (asciiOffset + k % 26))

-- -- Pretty print function for De Bruijn terms
-- def prettyPrintDeBruijn : DeBruijnTerm → Nat → String
-- | DeBruijnTerm.var k, c     => toVarName (c - k - 1)
-- | DeBruijnTerm.lam t, c     => "λ" ++ toVarName c ++ ". " ++ prettyPrintDeBruijn t (c + 1)
-- | DeBruijnTerm.app t1 t2, c => "(" ++ prettyPrintDeBruijn t1 c ++ " " ++ prettyPrintDeBruijn t2 c ++ ")"

-- def prettyPrintDeBruijnWrapper (t : DeBruijnTerm) : String :=
--   prettyPrintDeBruijn t 0
