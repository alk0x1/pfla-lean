newtype Name = Name String
  deriving (Show, Eq)

data Ty = TNat
  | TArr Ty Ty deriving (Eq, Show)

data Expr = Var Name
  | Lambda Name Expr
  | App Expr Expr
  | Zero
  | Add1 Expr
  | Rec Ty Expr Expr Expr | Ann Expr Ty
  deriving Show

-- introduction and elimination forms
