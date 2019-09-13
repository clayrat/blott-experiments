module Domain

import Syntax

%access public export
%default total

mutual
  Env : Type 
  Env = List DT
  
  data Clos = Cl T Domain.Env
            | ConstCl DT
  
  data DT = Lam Clos
          | Neutral DT Ne
          | N
          | Zero
          | Suc DT
          | Pi DT Clos
          | Sg DT Clos
          | Pair DT DT
          | Box DT
          | Shut DT
          | Refl DT
          | Id DT DT DT
          | Uni Nat

  data Clos2 = Cl2 T Domain.Env
  data Clos3 = Cl3 T Domain.Env
    
  data Nf = Normal DT DT
  
  data Ne = Var Nat -- DeBruijn levels for variables
          | Ap Ne Nf
          | Fst Ne
          | Snd Ne
          | Open Ne
          | NRec Clos DT Clos2 Ne
          | J Clos3 Clos DT DT DT Ne

mutual 
  Show Clos where
    show (Cl t env) = assert_total $ "Cl(" ++ show t ++ " " ++ show env ++ ")"
    show (ConstCl t) = assert_total $ "ConstCl(" ++ show t ++ ")" 

  Show DT where
    show (Lam cl) = "Lam(" ++ show cl ++ ")"
    show (Neutral t ne) = "Neutral(" ++ show t ++ " " ++ show ne ++ ")"
    show  N = "Nat" 
    show  Zero = "Zero"
    show (Suc t) = "Suc(" ++ show t ++ ")"
    show (Pi t cl) = "Pi(" ++ show t ++ " " ++ show cl ++ ")"
    show (Sg t cl) = "Sg(" ++ show t ++ " " ++ show cl ++ ")"
    show (Pair fst snd) = "Pair(" ++ show fst ++ " " ++ show snd ++ ")"
    show (Box t) = "Box(" ++ show t ++ ")"
    show (Shut t) = "Shut(" ++ show t ++ ")"
    show (Refl t) = "Refl(" ++ show t ++ ")"
    show (Id t l r) = "Id(" ++ show t ++ " " ++ show l ++ " " ++ show r ++ ")"
    show (Uni i) = "Uni(" ++ show i ++ ")"

  Show Clos2 where
    show (Cl2 t env) = assert_total $ "Cl2(" ++ show t ++ " " ++ show env ++ ")"

  Show Clos3 where
    show (Cl3 t env) = assert_total $ "Cl3(" ++ show t ++ " " ++ show env ++ ")"

  Show Nf where
    show (Normal tp tm) = "Normal(" ++ show tp ++ " " ++ show tm ++ ")"

  Show Ne where 
    show (Var l) = "#" ++ show l
    show (Ap ne nf) = "Ap(" ++ show ne ++ " " ++ show nf ++ ")"
    show (Fst ne) = "Fst(" ++ show ne ++ ")"
    show (Snd ne) = "Snd(" ++ show ne ++ ")"
    show (Open ne) = "Open(" ++ show ne ++ ")"
    show (NRec tp zero suc n) = "NRec(" ++ show tp ++ " " ++ show zero ++ " " ++ show suc ++ " " ++ show n ++ ")"
    show (J mot refl tp left right eq) = "J(" ++ show mot ++ " " ++ show refl ++ " " ++ show tp ++ " " ++ show left ++ " " ++ show right ++ " " ++ show eq ++ ")"

mkVar : DT -> Nat -> DT
mkVar tp lev = Neutral tp (Var lev)