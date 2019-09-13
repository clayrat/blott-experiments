module Syntax

%access public export
%default total

data T = Var Nat -- DeBruijn indices for variables & ticks
       | Let T {- BINDS -} T  
       | Check T T
       | N 
       | Zero 
       | Suc T 
       | NRec {- BINDS -} T T {- BINDS 2 -} T T
       | Pi T {- BINDS -} T 
       | Lam {- BINDS -} T 
       | Ap T T
       | Sg T {- BINDS -} T 
       | Pair T T 
       | Fst T 
       | Snd T
       | Id T T T 
       | Refl T 
       | J {- BINDS 3 -} T {- BINDS -} T T
       | Box T 
       | Open T 
       | Shut T
       | Uni Nat

Env : Type
Env = List T

condense : T -> Maybe Nat
condense  Zero   = Just Z
condense (Suc t) = S <$> condense t
condense  _      = Nothing

Show T where 
  show (Var i)               = show i
  show (Let def body)        = "let " ++ show def ++ " in " ++ show body
  show (Check term tp)       = "(" ++ show term ++ " : " ++ show tp ++ ")"
  show  N                    = "nat"
  show  Zero                 = "0"
  show (Suc t)               = maybe ("suc(" ++ show t ++ ")") (show . S) (condense t)
  show (NRec mot zero suc n) = "rec(" ++ show mot ++ " " ++ show zero ++ " " ++ show suc ++ " " ++ show n ++ ")"
  show (Pi l r)              = "Pi(" ++ show l ++ " " ++ show r ++ ")"
  show (Lam body)            = "lam(" ++ show body ++ ")"
  show (Ap l r)              = "app(" ++ show l ++ " " ++ show r ++ ")"
  show (Sg l r)              = "Sg(" ++ show l ++ " " ++ show r ++ ")"
  show (Fst body)            = "fst(" ++ show body ++ ")"
  show (Snd body)            = "snd(" ++ show body ++ ")"
  show (Pair l r)            = "pair(" ++ show l ++ " " ++ show r ++ ")"
  show (Id tp l r)           = "Id("  ++ show tp  ++ " " ++ show l ++ " " ++ show r ++ ")"
  show (Refl t)              = "refl(" ++ show t ++ ")"
  show (J mot refl eq)       = "J(" ++ show mot ++ " " ++ show refl ++ " " ++ show eq ++ ")"
  show (Box t)               = "[box " ++ show t ++ "]"
  show (Shut t)              = "[lock " ++ show t ++ "]"
  show (Open t)              = "[unlock " ++ show t ++ "]"
  show (Uni i)               = "U" ++ show i