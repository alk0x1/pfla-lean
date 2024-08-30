import Plfa.untyped.Term
import Plfa.untyped.DeBruijin


def subst (x : String) (v : Term) : Term → Term
| Term.var y => if x = y then v else Term.var y
| Term.lam y t => if x = y then Term.lam y t else Term.lam y (subst x v t)
| Term.app t1 t2 => Term.app (subst x v t1) (subst x v t2)


def termSize : Term → Nat
| Term.var _ => 1
| Term.lam _ t => 1 + termSize t
| Term.app t1 t2 => 1 + termSize t1 + termSize t2


def shift (d : Int) : Nat → DeBruijnTerm → DeBruijnTerm
| _, DeBruijnTerm.var k =>
    let newIdx := (k : Int) + d
    if newIdx >= 0 then DeBruijnTerm.var (newIdx.toNat) else DeBruijnTerm.var k
| cutoff, DeBruijnTerm.lam t => DeBruijnTerm.lam (shift d (cutoff + 1) t)
| cutoff, DeBruijnTerm.app t1 t2 => DeBruijnTerm.app (shift d cutoff t1) (shift d cutoff t2)

def substDeBruijn (j : Nat) (s : DeBruijnTerm) : DeBruijnTerm → DeBruijnTerm
| DeBruijnTerm.var k => if k = j then s else DeBruijnTerm.var k
| DeBruijnTerm.lam t => DeBruijnTerm.lam (substDeBruijn (j + 1) (shift 1 0 s) t)
| DeBruijnTerm.app t1 t2 => DeBruijnTerm.app (substDeBruijn j s t1) (substDeBruijn j s t2)


def betaReduceDeBruijn : DeBruijnTerm → Option DeBruijnTerm
| DeBruijnTerm.app (DeBruijnTerm.lam t1) t2 => some (shift (-1) 0 (substDeBruijn 0 (shift 1 0 t2) t1))
| DeBruijnTerm.app t1 t2 =>
    match betaReduceDeBruijn t1 with
    | some t1' => some (DeBruijnTerm.app t1' t2)
    | none =>
        match betaReduceDeBruijn t2 with
        | some t2' => some (DeBruijnTerm.app t1 t2')
        | none => none
| DeBruijnTerm.lam t =>
    match betaReduceDeBruijn t with
    | some t' => some (DeBruijnTerm.lam t')
    | none => none
| _ => none


partial def normalizeDeBruijn (t : DeBruijnTerm) : DeBruijnTerm :=
  match betaReduceDeBruijn t with
  | some t' => normalizeDeBruijn t'
  | none => t
