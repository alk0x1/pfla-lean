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

def p : Identifier := "p"
def a : Identifier := "a"
def b : Identifier := "b"
def x : Identifier := "x"
def y : Identifier := "y"

def identity_term : Term := lam x (var x) -- λx.x
def const : Term := lam x (lam y (var x)) -- λx.λy.x
def self_app : Term := lam x (app (var x) (var x)) --λx.xx
def true : Term := lam x (lam y (var x)) --λx.λy.x
def false : Term := lam x (lam y (var y)) -- λx.λy.y
def if_term : Term := lam p (lam a (lam b (app (app (var p) (var a)) (var b)))) -- λp.λa.λb.pab

def two : Term :=
  suc (suc zero)

def four : Term :=
  suc (suc (suc (suc zero)))

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
