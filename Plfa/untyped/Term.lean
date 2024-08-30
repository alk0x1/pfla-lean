import Init.Data.Repr
import Init.Data.String.Basic -- Ensure we have access to string manipulation functions

def Identifier := String
instance : DecidableEq Identifier := inferInstanceAs (DecidableEq String)

instance : Repr Identifier where
  reprPrec x _ := Std.Format.text x

inductive Term
| var   : Identifier → Term
| lam   : Identifier → Term → Term
| app   : Term → Term → Term
deriving Repr
open Term


def Context := List Identifier

-- Function to lookup a variable in the context using pattern matching
def lookup (ctx: Context) (name: Identifier) : Option Identifier :=
  match ctx with
  | [] => none
  | (x :: xs) => if x = name then name else lookup xs name

-- Example context
def example_ctx : Context := ["x", "y", "z"]

-- Test the lookup function
#eval lookup example_ctx "y"  -- Expected output: some "y"
#eval lookup example_ctx "a"  -- Expected output: none
