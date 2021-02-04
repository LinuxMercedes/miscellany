-- Syntax
data Expr n v =
    Forall n (Expr n v)
  | Exists n (Expr n v)
  | Var n
  | Const v
  | Not (Expr n v)
  | And (Expr n v) (Expr n v)
  | Or (Expr n v) (Expr n v)
  | Implies (Expr n v) (Expr n v)
  | Equal (Expr n v) (Expr n v)
  deriving (Eq, Show)

forall :: Expr n v -> Expr n v -> Expr n v
forall (Var n) = Forall n

exists :: Expr n v -> Expr n v -> Expr n v
exists (Var n) = Exists n

-- Semantics
bind :: (Applicative e, Eq n) => n -> v -> (n -> e v) -> n -> e v
bind name val env n | name == n = pure val
                    | otherwise = env n

eval :: (Applicative e, Eq n) => (n -> e Bool) -> Expr n Bool -> e Bool
eval env (Forall name expr) = (&&) <$> eval (bind name True env) expr <*> eval (bind name False env) expr
eval env (Exists name expr) = (||) <$> eval (bind name True env) expr <*> eval (bind name False env) expr
eval env (Var n)            = env n
eval _   (Const v)          = pure v
eval env (Not expr)         = not <$> eval env expr
eval env (And e1 e2)        = (&&) <$> eval env e1 <*> eval env e2
eval env (Or e1 e2)         = (||) <$> eval env e1 <*> eval env e2
eval env (Implies e1 e2)    = eval env $ (Not e1) `Or` e2
eval env (Equal e1 e2)      = (==) <$> eval env e1 <*> eval env e2

assert :: Eq n => Expr n Bool -> IO ()
assert expr = let v = eval (const $ Left "Undefined variable name") expr
              in case v of
                Left err -> fail err
                Right val -> if val then putStrLn "Valid" else fail "Does not hold!"

-- Examples
modus_ponens :: Expr String Bool
modus_ponens =
  let p  = Var "p"
      q  = Var "q"
      h1 = p `Implies` q
      h2 = p
      c  = q
  in  forall p $ forall q $ (h1 `And` h2) `Implies` c

modus_ponens_proof :: IO ()
modus_ponens_proof = assert modus_ponens -- Valid


modus_tollens :: Expr String Bool
modus_tollens =
  let p  = Var "p"
      q  = Var "q"
      h1 = p `Implies` q
      h2 = Not q
      c  = Not p
  in  forall p $ forall q $ (h1 `And` h2) `Implies` c

modus_tollens_proof :: IO ()
modus_tollens_proof = assert modus_tollens -- Valid


absurdity :: Expr String Bool
absurdity = Forall "p" $ (Var "p") `And` (Not $ Var "p")

absurdity_proof :: IO ()
absurdity_proof = assert absurdity -- Does not hold!


demorgans_and_or :: Expr String Bool
demorgans_and_or =
  let p   = Var "p"
      q   = Var "q"
      r   = Var "r"
      lhs = p `And` (q `Or` r)
      rhs = (p `And` q) `Or` (p `And` r)
  in  forall p $ forall q $ forall r $ lhs `Equal` rhs

demorgans_or_and :: Expr String Bool
demorgans_or_and =
  let p   = Var "p"
      q   = Var "q"
      r   = Var "r"
      lhs = p `Or` (q `And` r)
      rhs = (p `Or` q) `And` (p `Or` r)
  in  forall p $ forall q $ forall r $ lhs `Equal` rhs

demorgans_proof :: IO ()
demorgans_proof = assert demorgans_and_or >> assert demorgans_or_and -- Valid


equal_equiv_iff :: Expr String Bool
equal_equiv_iff =
  let p = Var "p"
      q = Var "q"
      lhs = p `Equal` q
      rhs = (p `Implies` q) `And` (q `Implies` p)
  in  forall p $ forall q $ lhs `Equal` rhs

equal_equiv_iff_proof :: IO ()
equal_equiv_iff_proof = assert equal_equiv_iff -- Valid
