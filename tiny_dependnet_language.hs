newtype Name = Name String
  deriving (Show, Eq)

data Ty = Value

data Expr
  = Var Name                           -- x
 | Pi Name Expr Expr                   -- (Π ((x A)) B)
 | Lambda Name Expr                    -- (λ (x) b)
 | App Expr Expr                       -- (rator rand)
 | Sigma Name Expr Expr                -- (Σ ((x A)) D)
 | Cons Expr Expr                      -- (cons a d)
 | Car Expr                            -- (car e)
 | Cdr Expr                            -- (cdr d)
 | Nat                                 -- Nat
 | Zero                                -- zero
 | Add1 Expr                           -- (add1 e)
 | IndNat Expr Expr Expr Expr          -- (ind-Nat tgt mot base step)
 | Equal Expr Expr Expr                -- (= A from to)
 | Same                                -- same
 | Replace Expr Expr Expr              -- (replace tgt mot base)
 | Trivial                             -- Trivial
 | Sole                                -- sole
 | Absurd                              -- Absurd
 | IndAbsurd Expr Expr                 -- (ind-Absurd tgt mot)
 | Atom                                -- Atom
 | Tick String                         -- 0a
 | U                                   -- U
 | The Expr Expr                       -- (the t e)
 deriving (Eq, Show)

data Value
 = VPi Ty Closure
 | VLambda Closure
 | VSigma Ty Closure
 | VPair Value Value
 | VNat
 | VZero
 | VAdd1 Value
 | VEq Ty Value Value
 | VSame
 | VTrivial
 | VSole
 | VAbsurd
 | VAtom
 | VTick String
 | VU
 | VNeutral Ty Neutral
 deriving Show

-- Two terms are alpha-equivalent iff one can be converted into the other purely by renaming bound variables.
-- λx. x   <->   λy. y   <->   λrandom. random
-- λx. λf. f x   <->   λx. λg. g x   <->   λf. λx. x f   <->  λx1. λx2. x2 x1
-- λf. λf. f f   <->   λg. λf. f f   <->   λf. λg. g g
alphaEquiv :: Expr -> Expr -> Bool
alphaEquiv e1 e2 = alphaEquivHelper 0 [ ] e1 [ ] e2

alphaEquivHelper :: Integer ->
 [(Name, Integer)] -> Expr ->
 [(Name, Integer)] -> Expr ->
 Bool

alphaEquivHelper i ns1 (Var x) ns2 (Var y) =
  case (lookup x ns1, lookup y ns2) of 
   (Nothing, Nothing) -> x == y
   (Just i, Just j) -> i == j
   _ -> False

alphaEquivHelper i ns1 (Pi x a1 r1) ns2 (Pi y a2 r2) =
 alphaEquivHelper i ns1 a1 ns2 a2 &&
 alphaEquivHelper (i + 1) ((x, i) : ns1) r1 ((y, i) : ns2) r2

alphaEquivHelper i ns1 (Lambda x body1) ns2 (Lambda y body2) =
 alphaEquivHelper (i + 1) ((x, i) : ns1) body1 ((y, i) : ns2) body2

alphaEquivHelper i ns1 (App rator1 rand1) ns2 (App rator2 rand2) =
 alphaEquivHelper i ns1 rator1 ns2 rator2 &&
 alphaEquivHelper i ns1 rand1 ns2 rand2

alphaEquivHelper i ns1 (Sigma x a1 d1) ns2 (Sigma y a2 d2) =
 alphaEquivHelper i ns1 a1 ns2 a2 &&
 alphaEquivHelper (i + 1) ((x, i) : ns1) d1 ((y, i) : ns2) d2

alphaEquivHelper i ns1 (Cons car1 cdr1) ns2 (Cons car2 cdr2) =
 alphaEquivHelper i ns1 car1 ns2 car2 &&
 alphaEquivHelper i ns1 cdr1 ns2 cdr2

alphaEquivHelper i ns1 (Car pair1) ns2 (Car pair2) =
 alphaEquivHelper i ns1 pair1 ns2 pair2

alphaEquivHelper i ns1 (Cdr pair1) ns2 (Cdr pair2) =
 alphaEquivHelper i ns1 pair1 ns2 pair2

alphaEquivHelper _ _ Nat _ Nat = True

alphaEquivHelper _ _ Zero _ Zero = True

alphaEquivHelper i ns1 (Add1 e1) ns2 (Add1 e2) =
 alphaEquivHelper i ns1 e1 ns2 e2

alphaEquivHelper i ns1 (IndNat tgt1 mot1 base1 step1) ns2 (IndNat tgt2 mot2 base2 step2) =
 alphaEquivHelper i ns1 tgt1 ns2 tgt2 &&
 alphaEquivHelper i ns1 mot1 ns2 mot2 &&
 alphaEquivHelper i ns1 base1 ns2 base2 &&
 alphaEquivHelper i ns1 step1 ns2 step2
 
alphaEquivHelper i ns1 (Equal ty1 from1 to1) ns2 (Equal ty2 from2 to2) =
 alphaEquivHelper i ns1 ty1 ns2 ty2 &&
 alphaEquivHelper i ns1 from1 ns2 from2 &&
 alphaEquivHelper i ns1 to1 ns2 to2

alphaEquivHelper _ _ Same _ Same = True
alphaEquivHelper i ns1 (Replace tgt1 mot1 base1) ns2 (Replace tgt2 mot2 base2) =
 alphaEquivHelper i ns1 tgt1 ns2 tgt2 &&
 alphaEquivHelper i ns1 mot1 ns2 mot2 &&
 alphaEquivHelper i ns1 base1 ns2 base2

alphaEquivHelper _ _ Trivial _ Trivial = True

alphaEquivHelper _ _ Sole _ Sole = True

alphaEquivHelper _ _ Absurd _ Absurd = True

alphaEquivHelper i ns1 (IndAbsurd tgt1 mot1) ns2 (IndAbsurd tgt2 mot2) =
 alphaEquivHelper i ns1 tgt1 ns2 tgt2 &&
 alphaEquivHelper i ns1 mot1 ns2 mot2

alphaEquivHelper _ _ Atom _ Atom = True

alphaEquivHelper _ _ U _ U = True

alphaEquivHelper _ _ (Tick a1) _ (Tick a2) = a1 == a2

alphaEquivHelper _ _ (The Absurd _) _ (The Absurd _) = True
alphaEquivHelper i ns1 (The t1 e1) ns2 (The t2 e2) =
 alphaEquivHelper i ns1 t1 ns2 t2 &&
 alphaEquivHelper i ns1 e1 ns2 e2

alphaEquivHelper _ _ _ _ _ = False

