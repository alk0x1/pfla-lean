def Identifier := String
instance : DecidableEq Identifier := inferInstanceAs (DecidableEq String)

inductive Term
| var   : Identifier → Term
| lam   : Identifier → Term → Term
| app   : Term → Term → Term
| zero  : Term
| suc   : Term → Term
| case  : Term → Term → Identifier → Term → Term
| mu    : Identifier → Term → Term

open Term

def two : Term :=
  suc (suc zero)

def plus : Term :=
  mu "+" (
    lam "m" (
      lam "n" (
        case (var "m")
          (var "n")
          "m"
          (suc ( app ( app (var "+") (var "m") ) (var "n") ))
      )
    )
  )

-- Environment
def Env := List (Identifier × Term)

def lookup (env : Env) (x : Identifier) : Option Term :=
  match env with
  | [] => none
  | (y, v) :: ys => if x = y then some v else lookup ys x

def extend (env : Env) (x : Identifier) (v : Term) : Env :=
  (x, v) :: env
