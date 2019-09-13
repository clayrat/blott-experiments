module Blott.ConcreteSyntax

%access public export
%default total

mutual
  data Binder = Bind String T

  data BinderN = BindN (List String) T

  data Binder2 = Bind2 String String T

  data Binder3 = Bind3 String String String T

  data Cell = MkCell String T

  data Spine = Term T

  data T = Var String
         | Let T Binder
         | Check T T
         | N
         | Suc T
         | Lit Nat
         | NRec Binder T Binder2 T
         | Pi (List Cell) T
         | Lam BinderN
         | Ap T (List Spine)
         | Sg (List Cell) T
         | Pair T T
         | Fst T
         | Snd T
         | Id T T T
         | Refl T
         | J Binder3 Binder T
         | Box T
         | Open T
         | Shut T
         | Uni Nat

data Decl = Def String T T
          | NormalizeDef String
          | NormalizeTerm T T
          | Quit

Signature : Type
Signature = List Decl
