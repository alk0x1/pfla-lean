newtype Name = Name String
  deriving (Show, Eq)

newtype Message = Message String
  deriving (Show)

type Ty = Value

newtype Env = Env [(Name, Value)]
  deriving (Show)

data Closure = Closure
  { closureEnv :: Env,
    closureName :: Name,
    closureBody :: Expr
  }
  deriving (Show)

data Expr
  = Var Name -- x
  | Pi Name Expr Expr -- (Π ((x A)) B)
  | Lambda Name Expr -- (λ (x) b)
  | App Expr Expr -- (rator rand)
  | Sigma Name Expr Expr -- (Σ ((x A)) D)
  | Cons Expr Expr -- (cons a d)
  | Car Expr -- (car e)
  | Cdr Expr -- (cdr d)
  | Nat -- Nat
  | Zero -- zero
  | Add1 Expr -- (add1 e)
  | IndNat Expr Expr Expr Expr -- (ind-Nat tgt mot base step)
  | Equal Expr Expr Expr -- (= A from to)
  | Same -- same
  | Replace Expr Expr Expr -- (replace tgt mot base)
  | Trivial -- Trivial
  | Sole -- sole
  | Absurd -- Absurd
  | IndAbsurd Expr Expr -- (ind-Absurd tgt mot)
  | Atom -- Atom
  | Tick String -- 0a
  | U -- U
  | The Expr Expr -- (the t e)
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
  deriving (Show)

data Neutral
  = NVar Name
  | NApp Neutral Normal
  | NCar Neutral
  | NCdr Neutral
  | NIndNat Neutral Normal Normal Normal
  | NReplace Neutral Normal Normal
  | NIndAbsurd Neutral Normal
  deriving (Show)

data Normal = Normal Ty Value
  deriving (Show)

-- Two terms are alpa-equivalent iff one can be converted into the other purely by renaming bound variables.
-- λx. x   <->   λy. y   <->   λrandom. randoms
-- λx. λf. f x   <->   λx. λg. g x   <->   λf. λx. x f   <->  λx1. λx2. x2 x1
-- λf. λf. f f   <->   λg. λf. f f   <->   λf. λg. g g
alphaEquiv :: Expr -> Expr -> Bool
alphaEquiv e1 = alphaEquivHelper 0 [] e1 []

alphaEquivHelper ::
  Integer ->
  [(Name, Integer)] ->
  Expr ->
  [(Name, Integer)] ->
  Expr ->
  Bool
alphaEquivHelper i ns1 (Var x) ns2 (Var y) =
  case (lookup x ns1, lookup y ns2) of
    (Nothing, Nothing) -> x == y
    (Just i, Just j) -> i == j
    _ -> False
alphaEquivHelper i ns1 (Pi x a1 r1) ns2 (Pi y a2 r2) =
  alphaEquivHelper i ns1 a1 ns2 a2
    && alphaEquivHelper (i + 1) ((x, i) : ns1) r1 ((y, i) : ns2) r2
alphaEquivHelper i ns1 (Lambda x body1) ns2 (Lambda y body2) =
  alphaEquivHelper (i + 1) ((x, i) : ns1) body1 ((y, i) : ns2) body2
alphaEquivHelper i ns1 (App rator1 rand1) ns2 (App rator2 rand2) =
  alphaEquivHelper i ns1 rator1 ns2 rator2
    && alphaEquivHelper i ns1 rand1 ns2 rand2
alphaEquivHelper i ns1 (Sigma x a1 d1) ns2 (Sigma y a2 d2) =
  alphaEquivHelper i ns1 a1 ns2 a2
    && alphaEquivHelper (i + 1) ((x, i) : ns1) d1 ((y, i) : ns2) d2
alphaEquivHelper i ns1 (Cons car1 cdr1) ns2 (Cons car2 cdr2) =
  alphaEquivHelper i ns1 car1 ns2 car2
    && alphaEquivHelper i ns1 cdr1 ns2 cdr2
alphaEquivHelper i ns1 (Car pair1) ns2 (Car pair2) =
  alphaEquivHelper i ns1 pair1 ns2 pair2
alphaEquivHelper i ns1 (Cdr pair1) ns2 (Cdr pair2) =
  alphaEquivHelper i ns1 pair1 ns2 pair2
alphaEquivHelper _ _ Nat _ Nat = True
alphaEquivHelper _ _ Zero _ Zero = True
alphaEquivHelper i ns1 (Add1 e1) ns2 (Add1 e2) =
  alphaEquivHelper i ns1 e1 ns2 e2
alphaEquivHelper i ns1 (IndNat tgt1 mot1 base1 step1) ns2 (IndNat tgt2 mot2 base2 step2) =
  alphaEquivHelper i ns1 tgt1 ns2 tgt2
    && alphaEquivHelper i ns1 mot1 ns2 mot2
    && alphaEquivHelper i ns1 base1 ns2 base2
    && alphaEquivHelper i ns1 step1 ns2 step2
alphaEquivHelper i ns1 (Equal ty1 from1 to1) ns2 (Equal ty2 from2 to2) =
  alphaEquivHelper i ns1 ty1 ns2 ty2
    && alphaEquivHelper i ns1 from1 ns2 from2
    && alphaEquivHelper i ns1 to1 ns2 to2
alphaEquivHelper _ _ Same _ Same = True
alphaEquivHelper i ns1 (Replace tgt1 mot1 base1) ns2 (Replace tgt2 mot2 base2) =
  alphaEquivHelper i ns1 tgt1 ns2 tgt2
    && alphaEquivHelper i ns1 mot1 ns2 mot2
    && alphaEquivHelper i ns1 base1 ns2 base2
alphaEquivHelper _ _ Trivial _ Trivial = True
alphaEquivHelper _ _ Sole _ Sole = True
alphaEquivHelper _ _ Absurd _ Absurd = True
alphaEquivHelper i ns1 (IndAbsurd tgt1 mot1) ns2 (IndAbsurd tgt2 mot2) =
  alphaEquivHelper i ns1 tgt1 ns2 tgt2
    && alphaEquivHelper i ns1 mot1 ns2 mot2
alphaEquivHelper _ _ Atom _ Atom = True
alphaEquivHelper _ _ U _ U = True
alphaEquivHelper _ _ (Tick a1) _ (Tick a2) = a1 == a2
alphaEquivHelper _ _ (The Absurd _) _ (The Absurd _) = True
alphaEquivHelper i ns1 (The t1 e1) ns2 (The t2 e2) =
  alphaEquivHelper i ns1 t1 ns2 t2
    && alphaEquivHelper i ns1 e1 ns2 e2
alphaEquivHelper _ _ _ _ _ = False

data CtxEntry = Def Ty Value | IsA Ty

newtype Ctx = Ctx [(Name, CtxEntry)]

failure :: String -> Either Message b
failure msg = Left (Message msg)

initCtx :: Ctx
initCtx = Ctx []

ctxNames :: Ctx -> [Name]
ctxNames (Ctx ctx) = map fst ctx

extendCtx :: Ctx -> Name -> Ty -> Ctx
extendCtx (Ctx ctx) x t = Ctx ((x, IsA t) : ctx)

define :: Ctx -> Name -> Ty -> Value -> Ctx
define (Ctx ctx) x t v = Ctx ((x, Def t v) : ctx)

lookupType :: Ctx -> Name -> Either Message Ty
lookupType (Ctx []) x = failure ("Unbound variable: " ++ show x)
lookupType (Ctx ((y, e) : ctx)) x
  | x == y =
      case e of
        Def t _ -> return t
        IsA t -> return t
  | otherwise =
      lookupType (Ctx ctx) x

mkEnv :: Ctx -> Env
mkEnv (Ctx []) = Env []
mkEnv (Ctx ((x, e) : ctx)) = Env ((x, v) : env)
  where
    Env env = mkEnv (Ctx ctx)
    v = case e of
      Def _ v -> v
      IsA t -> VNeutral t (NVar x)

evalVar :: Env -> Name -> Value
evalVar (Env []) x = error ("Missing value for " ++ show x)
evalVar (Env ((y, v) : env)) x
  | x == y = v
  | otherwise = evalVar (Env env) x

eval :: Env -> Expr -> Value
eval env (Var x) = evalVar env x
eval env (Pi x dom ran) = VPi (eval env dom) (Closure env x ran)
eval env (Lambda x body) = VLambda (Closure env x body)
eval env (App rator rand) = doApply (eval env rator) (eval env rand)
eval env (Sigma x carType cdrType) =
  VSigma (eval env carType) (Closure env x cdrType)
eval env (Cons a d) = VPair (eval env a) (eval env d)
eval env (Car e) = doCar (eval env e)
eval env (Cdr e) = doCdr (eval env e)
eval env Nat = VNat
eval env Zero = VZero
eval env (Add1 e) = VAdd1 (eval env e)
eval env (IndNat tgt mot base step) =
  doIndNat (eval env tgt) (eval env mot) (eval env base) (eval env step)
eval env (Equal ty from to) = VEq (eval env ty) (eval env from) (eval env to)
eval env Same = VSame
eval env (Replace tgt mot base) =
  doReplace (eval env tgt) (eval env mot) (eval env base)
eval env Trivial = VTrivial
eval env Sole = VSole
eval env Absurd = VAbsurd
eval env (IndAbsurd tgt mot) = doIndAbsurd (eval env tgt) (eval env mot)
eval env Atom = VAtom
eval env (Tick x) = VTick x
eval env U = VU
eval env (The ty e) = eval env e

evalClosure :: Closure -> Value -> Value
evalClosure (Closure env x e) v = eval (extendEnv env x v) e

extendEnv :: Env -> Name -> Value -> Env
extendEnv (Env env) x v = Env ((x, v) : env)

doCar :: Value -> Value
doCar (VPair v1 v2) = v1
doCar (VNeutral (VSigma aT dT) neu) =
  VNeutral aT (NCar neu)

doCdr :: Value -> Value
doCdr (VPair v1 v2) = v2
doCdr v@(VNeutral (VSigma aT dT) neu) =
  VNeutral (evalClosure dT (doCar v)) (NCdr neu)

doApply :: Value -> Value -> Value
doApply (VLambda closure) arg =
  evalClosure closure arg
doApply (VNeutral (VPi dom ran) neu) arg =
  VNeutral (evalClosure ran arg) (NApp neu (Normal dom arg))

doIndAbsurd :: Value -> Value -> Value
doIndAbsurd (VNeutral VAbsurd neu) mot =
  VNeutral mot (NIndAbsurd neu (Normal VU mot))

doReplace :: Value -> Value -> Value -> Value
doReplace VSame mot base =
  base
doReplace (VNeutral (VEq ty from to) neu) mot base =
  VNeutral (doApply mot to) (NReplace neu (Normal motT mot) (Normal baseT base))
  where
    motT = VPi ty (Closure (Env []) (Name "x") U)
    baseT = doApply mot from

indNatStepType :: Value -> Value
indNatStepType mot =
  eval
    (Env [(Name "mot", mot)])
    ( Pi
        (Name "n-1")
        Nat
        ( Pi
            (Name "almost")
            ( App
                (Var (Name "mot"))
                (Var (Name "n-1"))
            )
            ( App
                (Var (Name "mot"))
                (Add1 (Var (Name "n-1")))
            )
        )
    )

doIndNat :: Value -> Value -> Value -> Value -> Value
doIndNat VZero mot base step =
  base
doIndNat (VAdd1 v) mot base step =
  doApply (doApply step v) (doIndNat v mot base step)
doIndNat tgt@(VNeutral VNat neu) mot base step =
  VNeutral
    (doApply mot tgt)
    ( NIndNat
        neu
        (Normal (VPi VNat (Closure (Env []) (Name "k") U)) mot)
        (Normal (doApply mot VZero) base)
        (Normal (indNatStepType mot) step)
    )

nextName :: Name -> Name
nextName (Name x) = Name (x ++ "'")

freshen :: [Name] -> Name -> Name
freshen used x
  | x `elem` used = freshen used (nextName x)
  | otherwise = x

readBackNormal :: Ctx -> Normal -> Expr
readBackNormal ctx (Normal t v) = readBackTyped ctx t v

readBackTyped :: Ctx -> Ty -> Value -> Expr
readBackTyped ctx VNat VZero = Zero
readBackTyped ctx VNat (VAdd1 v) = Add1 (readBackTyped ctx VNat v)
readBackTyped ctx (VPi dom ran) fun =
  Lambda
    x
    ( readBackTyped
        (extendCtx ctx x dom)
        (evalClosure ran xVal)
        (doApply fun xVal)
    )
  where
    x = freshen (ctxNames ctx) (closureName ran)
    xVal = VNeutral dom (NVar x)
readBackTyped ctx (VSigma aT dT) pair =
  Cons
    (readBackTyped ctx aT carVal)
    (readBackTyped ctx (evalClosure dT carVal) cdrVal)
  where
    carVal = doCar pair
    cdrVal = doCdr pair
readBackTyped ctx VTrivial val = Sole
readBackTyped ctx VAbsurd (VNeutral VAbsurd neu) =
  The Absurd (readBackNeutral ctx neu)
readBackTyped ctx VEq {} VSame = Same
readBackTyped ctx VAtom (VTick x) = Tick x
readBackTyped ctx VU VNat = Nat
readBackTyped ctx VU VAtom = Atom
readBackTyped ctx VU VTrivial = Trivial
readBackTyped ctx VU VAbsurd = Absurd
readBackTyped ctx VU (VEq t from to) =
  Equal
    (readBackTyped ctx VU t)
    (readBackTyped ctx t from)
    (readBackTyped ctx t to)

readBackNeutral :: Ctx -> Neutral -> Expr
readBackNeutral ctx (NVar x) = Var x
readBackNeutral ctx (NApp neu arg) =
  App (readBackNeutral ctx neu) (readBackNormal ctx arg)
readBackNeutral ctx (NCar neu) = Car (readBackNeutral ctx neu)
readBackNeutral ctx (NCdr neu) = Cdr (readBackNeutral ctx neu)
readBackNeutral ctx (NIndNat neu mot base step) =
  IndNat
    (readBackNeutral ctx neu)
    (readBackNormal ctx mot)
    (readBackNormal ctx base)
    (readBackNormal ctx step)
readBackNeutral ctx (NReplace neu mot base) =
  Replace
    (readBackNeutral ctx neu)
    (readBackNormal ctx mot)
    (readBackNormal ctx base)
readBackNeutral ctx (NIndAbsurd neu mot) =
  IndAbsurd
    (The Absurd (readBackNeutral ctx neu))
    (readBackNormal ctx mot)

synth :: Ctx -> Expr -> Either Message Ty
synth ctx (Var x) = do
  lookupType ctx x
synth ctx (Pi x a b) = do
  check ctx a VU
  check (extendCtx ctx x (eval (mkEnv ctx) a)) b VU
  return VU
synth ctx (App rator rand) = do
  funTy <- synth ctx rator
  (a, b) <- isPi ctx funTy
  check ctx rand a
  return (evalClosure b (eval (mkEnv ctx) rand))
synth ctx (Sigma x a b) = do
  check ctx a VU
  check (extendCtx ctx x (eval (mkEnv ctx) a)) b VU
  return VU
synth ctx (Car e) = do
  t <- synth ctx e
  (aT, dT) <- isSigma ctx t
  return aT
synth ctx (Cdr e) = do
  t <- synth ctx e
  (aT, dT) <- isSigma ctx t
  return (evalClosure dT (doCar (eval (mkEnv ctx) e)))
synth ctx Nat = return VU
synth ctx (IndNat tgt mot base step) = do
  t <- synth ctx tgt
  isNat ctx t
  let tgtV = eval (mkEnv ctx) tgt
      motTy = eval (Env []) (Pi (Name "x") Nat U)
  check ctx mot motTy
  let motV = eval (mkEnv ctx) mot
  check ctx base (doApply motV VZero)
  check ctx step (indNatStepType motV)
  return (doApply motV tgtV)
synth ctx (Equal ty from to) = do
  check ctx ty VU
  let tyV = eval (mkEnv ctx) ty
  check ctx from tyV
  check ctx to tyV
  return VU
synth ctx (Replace tgt mot base) = do
  t <- synth ctx tgt
  (ty, from, to) <- isEqual ctx t
  let motTy = eval (Env [(Name "ty", ty)]) (Pi (Name "x") (Var (Name "ty")) U)
  check ctx mot motTy
  let motV = eval (mkEnv ctx) mot
  check ctx base (doApply motV from)
  return (doApply motV to)
synth ctx Trivial = return VU
synth ctx Absurd = return VU
synth ctx (IndAbsurd tgt mot) = do
  t <- synth ctx tgt
  isAbsurd ctx t
  check ctx mot VU
  return (eval (mkEnv ctx) mot)
synth ctx Atom = return VU
synth ctx U = return VU
synth ctx (The ty expr) = do
  check ctx ty VU
  let tyV = eval (mkEnv ctx) ty
  check ctx expr tyV
  return tyV
synth ctx other =
  failure ("Unable to synthesize a type for " ++ show other)

check :: Ctx -> Expr -> Ty -> Either Message ()
check ctx (Lambda x body) t = do
  (a, b) <- isPi ctx t
  let xV = evalClosure b (VNeutral a (NVar x))
  check (extendCtx ctx x a) body xV
check ctx (Cons a d) t = do
  (aT, dT) <- isSigma ctx t
  check ctx a aT
  let aV = eval (mkEnv ctx) a
  check ctx d (evalClosure dT aV)
check ctx Zero t =
  isNat ctx t
check ctx (Add1 n) t = do
  isNat ctx t
  check ctx n VNat
check ctx Same t = do
  (t, from, to) <- isEqual ctx t
  convert ctx t from to
check ctx Sole t =
  isTrivial ctx t
check ctx (Tick a) t =
  isAtom ctx t
check ctx other t = do
  t' <- synth ctx other
  convert ctx VU t' t

convert :: Ctx -> Ty -> Value -> Value -> Either Message ()
convert ctx t v1 v2 =
  if alphaEquiv e1 e2
    then return ()
    else failure (show e1 ++ " is not the same type as " ++ show e2)
  where
    e1 = readBackTyped ctx t v1
    e2 = readBackTyped ctx t v2

unexpected :: Ctx -> String -> Value -> Either Message a
unexpected ctx msg t = failure (msg ++ ": " ++ show e)
  where
    e = readBackTyped ctx VU t

isPi :: Ctx -> Value -> Either Message (Ty, Closure)
isPi _ (VPi a b) = return (a, b)
isPi ctx other = unexpected ctx "Not a Pi type" other

isSigma :: Ctx -> Value -> Either Message (Ty, Closure)
isSigma_ :: (Monad m) => Value -> m (Ty, Closure)
isSigma_ (VSigma a b) = return (a, b)
isSigma ctx = unexpected ctx "Not a Sigma type"

isNat :: Ctx -> Value -> Either Message ()
isNat_ :: (Monad m) => Value -> m ()
isNat_ VNat = return ()
isNat ctx = unexpected ctx "Not Nat"

isEqual :: Ctx -> Value -> Either Message (Ty, Value, Value)
isEqual_ :: (Monad m) => Value -> m (Ty, Value, Value)
isEqual_ (VEq ty from to) = return (ty, from, to)
isEqual ctx = unexpected ctx "Not an equality type"

isAbsurd :: Ctx -> Value -> Either Message ()
isAbsurd_ :: (Monad m) => Value -> m ()
isAbsurd_ VAbsurd = return ()
isAbsurd ctx = unexpected ctx "Not Absurd: "

isTrivial :: Ctx -> Value -> Either Message ()
isTrivial_ :: (Monad m) => Value -> m ()
isTrivial_ VTrivial = return ()
isTrivial ctx = unexpected ctx "Not Trivial"

isAtom :: Ctx -> Value -> Either Message ()
isAtom_ :: (Monad m) => Value -> m ()
isAtom_ VAtom = return ()
isAtom ctx = unexpected ctx "Not Atom"
