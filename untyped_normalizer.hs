newtype Name = Name String
  deriving (Show, Eq)

newtype Env val = Env[(Name, val)]
  deriving Show

initEnv :: Env val
initEnv = Env[]

data Expr
  = Var Name
  | Lambda Name Expr
  | App Expr Expr
  deriving Show

data Value
  = VClosure (Env Value) Name Expr
  | VNeutral Neutral
  deriving (Show)

data Neutral
  = NVar Name
  | NApp Neutral Value
  deriving (Show)

instance Functor Env where
  fmap :: (a -> b) -> Env a -> Env b
  fmap f (Env xs) =
    Env (map (\(x, v) -> (x, f v)) xs)


freshen :: [Name] -> Name -> Name
freshen used x
  | elem x used = freshen used (nextName x)
  | otherwise = x

nextName :: Name -> Name
nextName (Name x) = Name (x ++ "'")


newtype Message = Message String
  deriving Show
failure :: String -> Either Message b
failure msg = Left (Message msg)

lookupVar (Env []) (Name x)
  = failure ("Not Found: " ++x)
lookupVar (Env ((y,v): env')) x
  | y == x = Right v
  | otherwise = lookupVar (Env env') x

extend :: Env val -> Name -> val -> Env val
extend (Env env) x v = Env ((x, v): env)

-- Environment-based evaluator
eval :: Env Value -> Expr -> Either Message Value
eval env (Var x) =
  lookupVar env x
eval env (Lambda x body) =
  Right (VClosure env x body)
eval env (App rator rand) = 
  do fun <- eval env rator
     arg <- eval env rand
     doApply fun arg

-- Apply a function value to an argument
doApply :: Value -> Value -> Either Message Value
doApply(VClosure env x body) arg =
  eval (extend env x arg) body


readBack::[Name] -> Value -> Either Message Expr
readBack used (VNeutral (NVar x)) = Right (Var x)
readBack used (VNeutral (NApp fun arg)) =
  do rator <- readBack used (VNeutral fun)
     rand <- readBack used arg
     Right (App rator rand)
readBack used fun@(VClosure _ x _ ) =
  do let x' = freshen used x
     bodyVal <- doApply fun (VNeutral (NVar x'))
     bodyExpr <- readBack (x': used) bodyVal
     Right (Lambda x' bodyExpr)



normalize::Expr -> Either Message Expr
normalize expr =
  do val <- eval initEnv expr
     readBack[] val


runProgram :: [ (Name, Expr) ] -> Expr -> Either Message Expr 
runProgram defs expr = 
  do env <- addDefs initEnv defs
     val <- eval env expr 
     readBack (map fst defs) val

addDefs :: Env Value -> [ (Name, Expr) ] -> Either Message (Env Value)
addDefs env [ ] = Right env
addDefs env ((x, e): defs) =
  do v <- eval env e
     addDefs(extend env x v) defs

