{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Control.Monad.Gen
import Control.Monad.Trans.Writer
import Data.Foldable (traverse_)
import Data.Functor.Foldable
import Data.List (findIndex, intercalate)
import Data.Monoid
import GHC.Exts (IsString(..))

main :: IO ()
main = do
  -- -> foo; { -> bar; foo bar call } foo call
  test $ let
    in Lam ["x"] $ cat [Quo (Lam ["y"] $ cat [Var "x", Var "y", call]), Var "x", call]
  -- -> x; { x }
  test $ Lam ["x"] $ Quo $ Var "x"
  -- -> f, g; { f call g call }
  test $ Lam ["f", "g"] $ Quo $ cat [Var "f", call, Var "g", call]
  where

    test :: Church Exp -> IO ()
    test e = do
      putStr "Input:               "
      print e
      putStr "Closures converted:  "
      print $ convertClosures [] e
      putStrLn "Lambdas lifted: "
      traverse_ (putStrLn . ("                     " <>) . show . deBruijnDef)
        $ eliminateLambdas [] $ Def (Name "test") [] e
      putStrLn ""

newtype Name = Name String
  deriving (Eq)

instance Show Name where
  show (Name s) = s

instance IsString Name where
  fromString = Name

data Opr = Add | Sub | Mul | Div | Call
  deriving (Eq)

call :: Exp r b
call = Opr Call

instance Show Opr where
  show = \ case
    Add -> "(+)"
    Sub -> "(-)"
    Mul -> "(*)"
    Div -> "(/)"
    Call -> "call"

data Exp r b
  = Var r                    -- Push variable
  | Cat (Exp r b) (Exp r b)  -- Compose expressions
  | Quo (Exp r b)            -- Quoted expression (push function expression)
  | Esc Name                 -- Escaped name (push function by name)
  | Lam b (Exp r b)          -- Lambda (introduce local variables)
  | Opr Opr                  -- Intrinsic operation
  | Lit Int                  -- Literal
  | Nop                      -- Identity function
  | Clo Int                  -- New closure of given size
  deriving (Eq)

type Church f = f Name [Name]
type DeBruijn f = f Ind Int

newtype Ind = Ind Int
  deriving (Eq)

instance Show Ind where
  show (Ind i) = '#' : show i

cat :: [Exp r b] -> Exp r b
cat = foldr Cat Nop

instance (Show r, Show b) => Show (Exp r b) where
  showsPrec p = \ case
    Var v -> shows v
    Cat l Nop -> showsPrec p l
    Cat Nop r -> showsPrec p r
    Cat l r -> showsPrec catPrec l . showChar ' ' . showsPrec catPrec r
    Quo e -> showString "{ " . shows e . showString " }"
    Esc n -> showChar '\\' . shows n
    Lam vs e -> showParen (p >= catPrec)
      $ showString "-> "
      . shows vs
      . showString "; "
      . shows e
    Opr o -> shows o
    Lit i -> shows i
    Nop -> id
    Clo n -> showString "clo." . shows n
    where
      catPrec = 10

data ExpF r b a
  = VarF r
  | CatF a a
  | QuoF a
  | EscF Name
  | LamF b a
  | OprF Opr
  | LitF Int
  | NopF
  | CloF Int
  deriving (Functor)

type instance Base (Exp r b) = ExpF r b

instance Recursive (Exp r b) where
  project = \ case
    Var v -> VarF v
    Cat l r -> CatF l r
    Quo e -> QuoF e
    Esc n -> EscF n
    Lam vs e -> LamF vs e
    Opr p -> OprF p
    Lit i -> LitF i
    Nop -> NopF
    Clo n -> CloF n

instance Corecursive (Exp r b) where
  embed = \ case
    VarF v -> Var v
    CatF l r -> Cat l r
    QuoF e -> Quo e
    EscF n -> Esc n
    LamF vs e -> Lam vs e
    OprF p -> Opr p
    LitF i -> Lit i
    NopF -> Nop
    CloF n -> Clo n

data Def r b = Def Name b (Exp r b)
  deriving (Eq)

instance (Show r, Show b) => Show (Def r b) where
  show (Def name args body) = unwords
    ["define", show name, "{", show (Lam args body), "}"]

without :: Eq a => [a] -> [a] -> [a]
without = foldr (filter . (/=))

freeVars :: Church Exp -> [Name]
freeVars = cata $ \ case
  VarF v -> [v]
  CatF l r -> l <> r
  QuoF e -> e
  EscF _n -> []  -- Technically [n]
  LamF vs e -> e `without` vs
  OprF _ -> []
  LitF _ -> []
  NopF -> []
  CloF _ -> []

applyTo :: Exp r b -> [r] -> Exp r b
applyTo e (a : as) = applyTo (cat [Var a, e, call]) as
applyTo e [] = e

deBruijnDef :: Church Def -> DeBruijn Def
deBruijnDef (Def name args body)
  = Def name (length args) (deBruijn args body)

deBruijn :: [Name] -> Church Exp -> DeBruijn Exp
deBruijn = go
  where
    go env = recur
      where
        recur = \ case
          Var r -> case findIndex (== r) env of
            Just i -> Var (Ind i)
            Nothing -> error "unbound variable"
          Cat a b -> Cat (recur a) (recur b)
          Quo e -> Quo (recur e)
          Esc n -> Esc n
          Lam vs e -> Lam (length vs) (go (vs ++ env) e)
          Opr o -> Opr o
          Lit i -> Lit i
          Nop -> Nop
          Clo n -> Clo n

convertClosures :: [Name] -> Church Exp -> Church Exp
convertClosures globals = cata $ \ case
  LamF vs e -> let
    vars = freeVars e `without` (globals <> vs)
    in cat $ (Var <$> vars) <> [close (length vars) $ Lam (vs <> vars) e]
  QuoF e -> let
    vars = freeVars e `without` globals
    in cat $ (Var <$> vars) <> [close (length vars) $ Lam vars e]
  e -> embed e
  where
    close :: Int -> Exp r b -> Exp r b
    close 0 = id
    close n = (`Cat` Clo n) . Quo

type ClosureM = WriterT [Def Name [Name]] (Gen Int)

eliminateLambdas :: [Name] -> Church Def -> [Church Def]
eliminateLambdas globals (Def name args body) = Def name args body' : defs
  where
    (body', defs) = runGen . runWriterT . liftLambdas
      $ convertClosures globals body

    liftLambdas :: Church Exp -> ClosureM (Church Exp)
    liftLambdas = cata $ \ case
      CatF l r -> Cat <$> l <*> r
      QuoF e -> do
        e' <- e
        case e' of
          Var n -> pure $ Esc n
          _ -> do
            var <- Name . ("lam." <>) . show <$> gen
            tell [Def var args e']
            pure $ Esc var
      EscF n -> pure $ Esc n
      VarF v -> pure $ Var v
      OprF p -> pure $ Opr p
      LitF i -> pure $ Lit i
      NopF -> pure Nop
      CloF n -> pure $ Clo n
      LamF vs e -> {- do
        fresh <- Gen <$> gen
        e' <- e
        tell [Def fresh vs e']
        pure $ Var fresh -}
        Lam vs <$> e
