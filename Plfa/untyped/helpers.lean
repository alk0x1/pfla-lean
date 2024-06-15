import Plfa.untyped.Term

open Term

-- Example terms for testing

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
def const := lam "x" (lam "y" (var "x"))

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
#eval isFree "y" appExample


def indexOf (x : String) : List String → Nat
| []        => 0
| (y :: ys) => if x = y then 0 else 1 + indexOf x ys

def testIndexOf : List (String × List String × Nat) :=
  [ ("a", ["a", "b", "c"], 0)
  , ("b", ["a", "b", "c"], 1)
  , ("c", ["a", "b", "c"], 2)
  , ("d", ["a", "b", "c"], 3)
  , ("a", [], 0)
  , ("x", ["x", "x", "x"], 0)
  , ("y", ["x", "y", "x"], 1)
  , ("z", ["x", "y", "z"], 2)
  ]

def prettyPrintResult (x : String) (ctx : List String) (result : Nat) (expected : Nat) (correct : Bool) : String :=
  s!"Variable: {x}, Context: {ctx}, Result: {result}, Expected: {expected}, Correct: {correct}"

#eval testIndexOf.map (fun (x, ctx, expected) => prettyPrintResult x ctx (indexOf x ctx) expected (indexOf x ctx == expected))

-- def prettyPrintDeBruijn : DeBruijnTerm → Nat → String
-- | DeBruijnTerm.var k, c     => toVarName (c - k - 1)
-- | DeBruijnTerm.lam t, c     => "λ" ++ toVarName c ++ ". " ++ prettyPrintDeBruijn t (c + 1)
-- | DeBruijnTerm.app t1 t2, c => "(" ++ prettyPrintDeBruijn t1 c ++ " " ++ prettyPrintDeBruijn t2 c ++ ")"

-- def prettyPrintDeBruijnWrapper (t : DeBruijnTerm) : String :=
--   prettyPrintDeBruijn t 0


-- Helper function to convert De Bruijn indices back to variable names for readability
def toVarName (k : Nat) : String :=
  let asciiOffset := 97  -- 'a' in ASCII
  String.singleton (Char.ofNat (asciiOffset + k % 26))
