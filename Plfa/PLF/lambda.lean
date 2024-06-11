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
def z : Identifier := "z"
def m : Identifier := "m"
def n : Identifier := "n"
def f : Identifier := "f"

def identity_term : Term := lam x (var x) -- λx.x
def const : Term := lam x (lam y (var x)) -- λx.λy.x
def self_app : Term := lam x (app (var x) (var x)) --λx.xx
def true_term : Term := lam x (lam y (var x)) --λx.λy.x
def false_term : Term := lam x (lam y (var y)) -- λx.λy.y
def if_term : Term := lam p (lam a (lam b (app (app (var p) (var a)) (var b)))) -- λp.λa.λb.pab
def add : Term := lam m (lam n (lam f (lam x (app (app (var m) (var f)) (app (app (var n) (var f)) (var x)) )))) -- λm.λn.λf.λx.mf(nfx)

-- Substitution function
def subst (x : Identifier) (v : Term) : Term → Term
| (var y) => if x = y then v else var y
| (lam y t) => if x = y then lam y t else lam y (subst x v t)
| (app t1 t2) => var x
| zero => zero
| (suc t) => var x
| (case t1 t2 y t3) => var x
| (mu y t) => var x

-- Testing Substitutions
def term1 := var x
def term2 := lam y (var x)

def v := lam z (var z)
def test1 := subst x v term1 -- x -> v in x




-- Normalizer
-- def normalizer (term : Term) :=



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
