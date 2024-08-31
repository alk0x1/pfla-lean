import Debug.Trace (trace)

newtype Name = Name String
  deriving (Show, Eq)

data Ty = TNat
  | TArr Ty Ty deriving (Eq, Show)

data Expr = Var Name
  | Lambda Name Expr
  | App Expr Expr
  | Zero
  | Add1 Expr
  | Rec Ty Expr Expr Expr
  | Ann Expr Ty
  deriving Show

newtype Env val = Env[(Name, val)]
  deriving Show
initEnv :: Env val
initEnv = Env []

type Context = Env Ty
initCtx :: Context
initCtx = initEnv

newtype Message = Message String
  deriving Show

failure :: String -> Either Message b
failure msg = Left (Message msg)

lookupVar :: Env val -> Name -> Either Message val
lookupVar (Env []) (Name x)
  = failure ("Not Found: " ++x)
lookupVar (Env ((y,v): env')) x
  | y == x = Right v
  | otherwise = lookupVar (Env env') x

extend :: Env val -> Name -> val -> Env val
extend (Env env) x v = Env ((x, v): env)


-- inference
synth :: Context -> Expr -> Either Message Ty
synth ctx (Var x) =
  lookupVar ctx x -- Γ1, x : t, Γ2 |- x : t
synth ctx (App rator rand) = do -- if Γ |- e1 ⇒ A → B Γ |- e2 => A then Γ |- e1 e2 ⇒ B
  ty <- synth ctx rator
  case ty of
    TArr argT retT -> do
      check ctx rand argT
      Right retT
    other ->
      failure ("Not a function type: " ++ show other)
synth ctx (Rec ty tgt base step) = do -- if Γ |- n ⇒ Nat Γ |- b ⇐ A Γ |- s ⇐ Nat → A → A then Γ |- rec[A] n b s ⇒ A
  tgtT <- synth ctx tgt
  case tgtT of
    TNat -> do
      check ctx base tgtT
      check ctx step (TArr TNat (TArr ty ty))
      Right ty
    other ->
      failure ("Not the type Nat: " ++ show other)
synth ctx (Ann e t) = do -- if Γ |- e ⇐ t1 then Γ |- e ∈ t1 ⇒ t1
  check ctx e t
  Right t
synth _ other =
  failure ("Can't find a type for " ++ show other ++ ". " ++
           "Try adding a type annotation.")

-- checker
check :: Context -> Expr -> Ty -> Either Message ()
check ctx (Lambda x body) t = -- if Γ, x : A |- e ⇐ B then Γ |- λx.e ⇐ A → B
  case t of
    TArr arg ret ->
      check (extend ctx x arg) body ret
    other ->
      failure ("Lambda requires a function type, but got " ++ show other)
check ctx Zero t = -- Γ |- zero ⇐ Nat
  case t of
    TNat -> Right ()
    other ->
      failure ("Zero should be a Nat, but was used where a " ++ show other ++ " was expected")
check ctx (Add1 n) t = -- if Γ |- e ⇒ t2 and t2 = t1 then Γ |- e ⇐ t1
  case t of
    TNat ->
      check ctx n TNat
    other ->
      failure ("Add1 should be a Nat, but was used where a " ++ show other ++ " was expected")
check ctx other t =
  do t' <- synth ctx other
     if t' == t
       then Right ()
       else failure ("Expected " ++ show t ++ " but got " ++ show t')

addDefs::Context->[(Name, Expr)] -> Either Message Context
addDefs ctx [] = Right ctx
addDefs ctx ((x,e) : defs) =
 do t <- synth ctx e
    addDefs (extend ctx x t) defs

-- Type check both a partial and full application of addition.
test :: Either Message (Ty, Ty)
test = do
  ctx <- addDefs initCtx
    [ (Name "two",
        Ann (Add1 (Add1 Zero)) TNat),
      (Name "three",
        Ann (Add1 (Add1 (Add1 Zero))) TNat),
      (Name "+",
        Ann (Lambda (Name "n")
             (Lambda (Name "k")
               (Rec TNat (Var (Name "n"))
                (Var (Name "k"))
                (Lambda (Name "pred")
                  (Lambda (Name "almostSum")
                    (Add1 (Var (Name "almostSum"))))))))
        (TArr TNat (TArr TNat TNat)))
    ]

  let expr1 = App (Var (Name "+")) (Var (Name "three"))
  let expr2 = App (App (Var (Name "+")) (Var (Name "three"))) (Var (Name "two"))

  trace ("Evaluating expression: " ++ show expr1) $ return ()
  t1 <- synth ctx expr1

  trace ("Evaluating expression: " ++ show expr2) $ return ()
  t2 <- synth ctx expr2

  Right (t1, t2)