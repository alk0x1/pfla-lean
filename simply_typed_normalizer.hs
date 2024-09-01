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


instance Functor Env where
  fmap :: (a -> b) -> Env a -> Env b
  fmap f (Env xs) =
    Env (map (\(x, v) -> (x, f v)) xs)

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

addDefs::Defs->[(Name, Expr)] -> Either Message Defs
addDefs defs [] = 
  Right defs
addDefs defs ((x,e) : more) =
  do norm <- normWithDefs defs e
     addDefs (extend defs x norm) more
definedNames::Defs -> [Name]
definedNames (Env defs) = map fst defs

-- Type check both a partial and full application of addition.
normWithTestDefs :: Expr -> Either Message Expr
normWithTestDefs e = do
    defs <- addDefs noDefs
        [ (Name "two",
            Ann (Add1 (Add1 Zero)) TNat)
        , (Name "three",
            Ann (Add1 (Add1 (Add1 Zero))) TNat)
        , (Name "+",
            Ann (Lambda (Name "n")
                      (Lambda (Name "k")
                          (Rec TNat (Var (Name "n"))
                                    (Var (Name "k"))
                                    (Lambda (Name "pred")
                                        (Lambda (Name "almostSum")
                                            (Add1 (Var (Name "almostSum"))))))))
                (TArr TNat (TArr TNat TNat)))
        ]
    norm <- normWithDefs defs e
    Right (readBackNormal (definedNames defs) norm)

test1, test2, test3 :: Either Message Expr
test1 = normWithTestDefs (Var (Name "+"))
test2 = normWithTestDefs (App (Var (Name "+")) (Var (Name "three")))
test3 = normWithTestDefs (App (App (Var (Name "+")) (Var (Name "three"))) (Var (Name "two")))


nextName :: Name -> Name
nextName (Name x) = Name (x ++ "'")

freshen :: [Name] -> Name -> Name
freshen used x
  | x `elem` used = freshen used (nextName x)
  | otherwise = x

data Neutral
  = NVar Name
  | NApp Neutral Value
  | NRec Ty Neutral Normal Normal
  deriving (Show)

data Value
 = VZero
 | VAdd1 Value
 | VClosure (Env Value) Name Expr
 | VNeutral Ty Neutral
 deriving (Show)

data Normal
 = Normal  { normalType :: Ty,
   normalValue :: Value}
 deriving (Show)


doApply :: Value -> Value -> Value
doApply (VClosure env x body) arg =
 eval (extend env x arg) body
doApply (VNeutral (TArr t1 t2) neu) arg =
  VNeutral t2 (NApp neu arg)


doRec :: Ty -> Value -> Value -> Value -> Value
doRec t VZero base step = base
doRec t (VAdd1 n) base step =
 doApply (doApply step n)
  (doRec t n base step)
doRec t (VNeutral TNat neu) base step =
 VNeutral t
  (NRec t neu
   (Normal t base)
   (Normal (TArr TNat (TArr t t)) step))


eval :: Env Value -> Expr -> Value
eval env (Var x) =
 case lookupVar env x of
 Left msg ->
  error ("Internal error: " ++ show msg)
 Right v -> v
eval env (Lambda x body) =
 VClosure env x body
eval env (App rator rand) =
  doApply (eval env rator) (eval env rand)
eval env Zero = VZero
eval env (Add1 n) = VAdd1 (eval env n)
eval env (Rec t tgt base step) =
 doRec t (eval env tgt) (eval env base) (eval env step)
eval env (Ann e t) = eval env e

readBackNormal :: [Name] -> Normal -> Expr
readBackNormal used (Normal t v) = readBack used t v

readBack::[Name] -> Ty -> Value -> Expr
readBack used TNat VZero =
  Zero
readBack used TNat (VAdd1 pred) =
  Add1 (readBack used TNat pred)
readBack used (TArr t1 t2) fun =
  let x = freshen used (argName fun)
      xVal = VNeutral t1 (NVar x)
  in Lambda x
  (readBack used t2
    (doApply fun xVal))
  where
    argName (VClosure _ x _ ) = x
    argName _ = Name "x"
readBack used t1 (VNeutral t2 neu) =
  if t1 == t2
then readBackNeutral used neu
else error "Internal error: mismatched types at readBackNeutral"

readBackNeutral :: [Name] -> Neutral -> Expr
readBackNeutral used (NVar x) = Var x
readBackNeutral used (NApp rator arg) =
  let argNormal = Normal (inferType arg) arg  -- Wrap the arg in a Normal with its type
  in App (readBackNeutral used rator) (readBackNormal used argNormal)
readBackNeutral used (NRec t neu base step) =
  Rec t (readBackNeutral used neu)
  (readBackNormal used base)
  (readBackNormal used step)

inferType :: Value -> Ty
inferType VZero = TNat
inferType (VAdd1 _) = TNat
inferType (VClosure {}) = error "Cannot infer type of a closure"
inferType (VNeutral ty _) = ty

type Defs = Env Normal
noDefs :: Defs
noDefs = initEnv
defsToContext :: Defs -> Context
defsToContext = fmap normalType
defsToEnv :: Defs -> Env Value
defsToEnv = fmap normalValue

normWithDefs :: Defs -> Expr -> Either Message Normal
normWithDefs defs e =
  do t <- synth (defsToContext defs) e
     let v = eval (defsToEnv defs) e
     Right (Normal t v)

