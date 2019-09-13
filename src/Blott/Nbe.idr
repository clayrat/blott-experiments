module Blott.Nbe

-- This file implements the normalization procedure. In addition the "unary" quotation
-- algorithm described by the paper, we also implement a binary operation for increased
-- efficiency.

import Control.Catchable
import Blott.Syntax as Syn
import Blott.Domain as D
import Blott.Error

%access public export
%default covering

-- Functions to manipulate elements of the semantic domain

mutual
  doRec : (Monad m, Catchable m Error) =>
          D.Clos -> DT -> D.Clos2 -> DT -> m DT
  doRec _  zero _      D.Zero         = pure zero
  doRec tp zero suc   (D.Suc n)       = doClos2 suc n !(doRec tp zero suc n)
  doRec tp zero suc n@(D.Neutral _ e) =
    do finalTp <- doClos tp n
       pure $ D.Neutral finalTp (D.NRec tp zero suc e)
  doRec _  _    _      _              = throw $ NbeError "Not a number"

  doFst : (Monad m, Catchable m Error) =>
          DT -> m DT
  doFst (D.Pair p1 _)             = pure p1
  doFst (D.Neutral (D.Sg t _) ne) = pure $ D.Neutral t (D.Fst ne)
  doFst  _                        = throw $ NbeError "Couldn't fst argument in doFst"

  doSnd : (Monad m, Catchable m Error) =>
          DT -> m DT
  doSnd   (D.Pair _ p2)               = pure p2
  doSnd p@(D.Neutral (D.Sg _ clo) ne) =
    do fst <- doFst p
       tp' <- doClos clo fst
       pure $ D.Neutral tp' (D.Snd ne)
  doSnd _                             = throw $ NbeError "Couldn't snd argument in doSnd"

  doClos : (Monad m, Catchable m Error) =>
           D.Clos -> DT -> m DT
  doClos (Cl term env) a = eval term (a :: env)
  doClos (ConstCl t)   _ = pure t

  doClos2 : (Monad m, Catchable m Error) =>
            D.Clos2 -> DT -> DT -> m DT
  doClos2 (D.Cl2 term env) a1 a2 = eval term (a2 :: a1 :: env)

  doClos3 : (Monad m, Catchable m Error) =>
            D.Clos3 -> DT -> DT -> DT -> m DT
  doClos3 (D.Cl3 term env) a1 a2 a3 = eval term (a3 :: a2 :: a1 :: env)

  doOpen : (Monad m, Catchable m Error) =>
           DT -> m DT
  doOpen (D.Shut t)                  = pure t
  doOpen (D.Neutral (D.Box tp) term) = pure $ D.Neutral tp (D.Open term)
  doOpen (D.Neutral _ _)             = throw $ NbeError "Not a box in doOpen"
  doOpen  _                          = throw $ NbeError "Not a box or neutral in open"

  doJ : (Monad m, Catchable m Error) =>
        D.Clos3 -> D.Clos -> DT -> m DT
  doJ mot refl (D.Refl t)                               = doClos refl t
  doJ mot refl eq@(D.Neutral (D.Id tp left right) term) =
    do tp' <- doClos3 mot left right eq
       pure $ D.Neutral tp' (D.J mot refl tp left right term)
  doJ mot refl (D.Neutral _ _)                          = throw $ NbeError "Not an Id in doJ"
  doJ _   _     _                                       = throw $ NbeError "Not a refl or neutral in doJ"

  doAp : (Monad m, Catchable m Error) =>
         DT -> DT -> m DT
  doAp (D.Lam  clos)                a = doClos clos a
  doAp (D.Neutral (D.Pi src dst) e) a =
    do dst' <- doClos dst a
       pure $ D.Neutral dst' (D.Ap e (D.Normal src a))
  doAp (D.Neutral _  _            ) _ = throw $ NbeError "Not a Pi in doAp"
  doAp  _                           _ = throw $ NbeError "Not a function in doAp"

-- Functions to pass between various semantic domains

  eval : (Monad m, Catchable m Error) =>
         Syn.T -> D.Env -> m DT
  eval (Syn.Var i)              env = maybe (throw $ NbeError "Lookup out of bounds in env") pure $ List.index' i env
  eval (Syn.Let def body)       env =
    do hd <- eval def env
       eval body (hd :: env)
  eval (Syn.Check term _)       env = eval term env
  eval  Syn.N                   _   = pure D.N
  eval  Syn.Zero                _   = pure D.Zero
  eval (Syn.Suc t)              env = D.Suc <$> eval t env
  eval (Syn.NRec tp zero suc n) env = doRec (Cl tp env) !(eval zero env) (Cl2 suc env) !(eval n env)
  eval (Syn.Pi src dest)        env =
    do src' <- eval src env
       pure $ D.Pi src' (Cl dest env)
  eval (Syn.Lam t)              env = pure $ D.Lam (Cl t env)
  eval (Syn.Ap t1 t2)           env = doAp !(eval t1 env) !(eval t2 env)
  eval (Syn.Uni i)              _   = pure $ D.Uni i
  eval (Syn.Sg t1 t2)           env =
    do t1' <- eval t1 env
       pure $ D.Sg t1' (Cl t2 env)
  eval (Syn.Pair t1 t2)         env = [| D.Pair (eval t1 env) (eval t2 env) |]
  eval (Syn.Fst t)              env = doFst !(eval t env)
  eval (Syn.Snd t)              env = doSnd !(eval t env)
  eval (Syn.Box t)              env = D.Box <$> eval t env
  eval (Syn.Open t)             env = doOpen !(eval t env)
  eval (Syn.Shut t)             env = D.Shut <$> eval t env
  eval (Syn.Refl t)             env = D.Refl <$> eval t env
  eval (Syn.Id tp left right)   env = [| D.Id (eval tp env) (eval left env) (eval right env) |]
  eval (Syn.J mot refl eq)      env = doJ (D.Cl3 mot env) (D.Cl refl env) !(eval eq env)

-- Note that readBack* is referred to as quotation in the paper
mutual
  readBackNf : (Monad m, Catchable m Error) =>
               Nat -> Nf -> m T
  -- Functions
  readBackNf size (D.Normal (D.Pi src dest)  f                ) =
    do let arg = D.mkVar src size
       cl <- doClos dest arg
       ap <- doAp f arg
       nf <- readBackNf (S size) (D.Normal cl ap)
       pure $ Syn.Lam nf
  -- Pairs
  readBackNf size (D.Normal (D.Sg fst snd)   p                ) =
    do fst' <- doFst p
       snd0 <- doClos snd fst'
       snd' <- doSnd p
       sfst <- readBackNf size (D.Normal fst fst')
       ssnd <- readBackNf size (D.Normal snd0 snd')
       pure $ Syn.Pair sfst ssnd
  -- Numbers
  readBackNf size (D.Normal  D.N             D.Zero           ) = pure $ Syn.Zero
  readBackNf size (D.Normal  D.N            (D.Suc nf)        ) = Syn.Suc <$> (readBackNf size (D.Normal D.N nf))
  readBackNf size (D.Normal  D.N            (D.Neutral _ ne)  ) = readBackNe size ne
  -- Box
  readBackNf size (D.Normal (D.Box tp)       term             ) =
    do tm <- doOpen term
       rbnf <- readBackNf size (D.Normal tp tm)
       pure $ Syn.Shut rbnf
  -- Id
  readBackNf size (D.Normal (D.Id tp _ _)   (D.Refl term)     ) = Syn.Refl <$> (readBackNf size (D.Normal tp term))
  readBackNf size (D.Normal (D.Id _ _ _)    (D.Neutral _ term)) = readBackNe size term
  -- Types
  readBackNf size (D.Normal (D.Uni _)        t                ) = readBackTp size t
  readBackNf size (D.Normal (D.Neutral _ _) (D.Neutral _ ne)  ) = readBackNe size ne
  readBackNf _     _                                            = throw $ NbeError "Ill-typed readBackNf"

  readBackTp : (Monad m, Catchable m Error) =>
               Nat -> DT -> m T
  readBackTp size (D.Neutral _ term)   = readBackNe size term
  readBackTp size  D.N                 = pure Syn.N
  readBackTp size (D.Pi src dest)      =
    do src' <- readBackTp size src
       clos <- doClos dest (D.mkVar src size)
       dest' <- readBackTp (S size) clos
       pure $ Syn.Pi src' dest'
  readBackTp size (D.Sg fst snd)       =
    do fst' <- readBackTp (S size) fst
       clos <- doClos snd (D.mkVar fst size)
       snd' <- readBackTp (S size) clos
       pure $ Syn.Sg fst' snd'
  readBackTp size (D.Box t)            = Syn.Box <$> readBackTp size t
  readBackTp size (D.Id tp left right) =
    do tp' <- readBackTp size tp
       left' <- readBackNf size (D.Normal tp left)
       right' <- readBackNf size (D.Normal tp right)
       pure $ Syn.Id tp' left' right'
  readBackTp _ (D.Uni k)               = pure $ Syn.Uni k
  readBackTp _ _                       = throw $ NbeError "Not a type in readBackTp"

  readBackNe : (Monad m, Catchable m Error) =>
               Nat -> Ne -> m T
  readBackNe size (D.Var x) = pure $ Syn.Var (size `minus` S x)
  readBackNe size (D.Ap ne arg) = [| Syn.Ap (readBackNe size ne) (readBackNf size arg) |]
  readBackNe size (D.NRec tp zero suc n) =
    do let tpVar = D.mkVar D.N size
       appliedTp <- doClos tp tpVar
       zeroTp <- doClos tp D.Zero
       appliedSucTp <- doClos tp (D.Suc tpVar)
       tp' <- readBackTp (size + 1) appliedTp
       let sucVar = D.mkVar appliedTp (S size)
       appliedSuc <- doClos2 suc tpVar sucVar
       zero' <- readBackNf size (D.Normal zeroTp zero)
       suc' <- readBackNf (2 + size) (D.Normal appliedSucTp appliedSuc)
       n' <- readBackNe size n
       pure $ Syn.NRec tp' zero' suc' n'
  readBackNe size (D.Fst ne) = Syn.Fst <$> readBackNe size ne
  readBackNe size (D.Snd ne) = Syn.Snd <$> readBackNe size ne
  readBackNe size (D.Open ne) = Syn.Open <$> readBackNe size ne
  readBackNe size (D.J mot refl tp left right eq) =
    do let motVar1 = D.mkVar tp size
       let motVar2 = D.mkVar tp (S size)
       let motVar3 = D.mkVar (D.Id tp left right) (2 + size)
       motClos <- doClos3 mot motVar1 motVar2 motVar3
       motSyn <- readBackTp (3 + size) motClos
       let reflVar = D.mkVar tp size
       reflClosTp <- doClos3 mot reflVar reflVar (D.Refl reflVar)
       reflClosTerm <- doClos refl reflVar
       reflSyn <- readBackNf (S size) (D.Normal reflClosTp reflClosTerm)
       eqSyn <- readBackNe size eq
       pure $ Syn.J motSyn reflSyn eqSyn

mutual
  checkNf : (Monad m, Catchable m Error) =>
            Nat -> Nf -> Nf -> m Bool
  -- Functions
  checkNf size (D.Normal (D.Pi src1 dest1) f1)              (D.Normal (D.Pi _ dest2) f2)                 =
    do let arg = D.mkVar src1 size
       clos1 <- doClos dest1 arg
       ap1 <- doAp f1 arg
       clos2 <- doClos dest2 arg
       ap2 <- doAp f2 arg
       checkNf (S size) (D.Normal clos1 ap1) (D.Normal clos2 ap2)
  -- Pairs
  checkNf size (D.Normal (D.Sg fst1 snd1) p1)               (D.Normal (D.Sg fst2 snd2) p2)               =
    do p11 <- doFst p1
       p21 <- doFst p2
       chkfst <- checkNf size (D.Normal fst1 p11) (D.Normal fst2 p21)
       p12 <- doSnd p1
       p22 <- doSnd p2
       snd1' <- doClos snd1 p11
       snd2' <- doClos snd2 p21
       chksnd <- checkNf size (D.Normal snd1' p12) (D.Normal snd2' p22)
       pure $ chkfst && chksnd
  -- Numbers
  checkNf size (D.Normal D.N  D.Zero)                       (D.Normal D.N  D.Zero)                       =
    pure True
  checkNf size (D.Normal D.N (D.Suc nf1))                   (D.Normal D.N (D.Suc nf2))                   =
    checkNf size (D.Normal D.N nf1) (D.Normal D.N nf2)
  checkNf size (D.Normal D.N (D.Neutral _ ne1))             (D.Normal D.N (D.Neutral _ ne2))             =
    checkNe size ne1 ne2
  -- Id
  checkNf size (D.Normal (D.Id tp _ _) (D.Refl term1))      (D.Normal (D.Id _ _ _) (D.Refl term2))       =
    checkNf size (D.Normal tp term1) (D.Normal tp term2)
  checkNf size (D.Normal (D.Id _ _ _) (D.Neutral _ term1))  (D.Normal (D.Id _ _ _) (D.Neutral _ term2))  =
    checkNe size term1 term2
  -- Box
  checkNf size (D.Normal (D.Box tp) term1)                  (D.Normal (D.Box _) term2)                   =
    do open1 <- doOpen term1
       open2 <- doOpen term2
       checkNf size (D.Normal tp open1) (D.Normal tp open2)
  -- Types
  checkNf size (D.Normal (D.Uni _) t1)                      (D.Normal (D.Uni _) t2)                      =
    checkTp False size t1 t2
  checkNf size (D.Normal (D.Neutral _ _) (D.Neutral _ ne1)) (D.Normal (D.Neutral _ _) (D.Neutral _ ne2)) =
    checkNe size ne1 ne2
  checkNf _     _                                            _                                           =
    pure False

  checkNe : (Monad m, Catchable m Error) =>
            Nat -> Ne -> Ne -> m Bool
  checkNe size (D.Var x)                             (D.Var y)                             = pure $ x == y
  checkNe size (D.Ap ne1 arg1)                       (D.Ap ne2 arg2)                       =
    do chkne <- checkNe size ne1 ne2
       chkarg <- checkNf size arg1 arg2
       pure $ chkne && chkarg
  checkNe size (D.NRec tp1 zero1 suc1 n1) (D.NRec tp2 zero2 suc2 n2) =
    do let tpVar = D.mkVar D.N size
       appliedTp1 <- doClos tp1 tpVar
       appliedTp2 <- doClos tp2 tpVar
       zeroTp <- doClos tp1 D.Zero
       appliedSucTp <- doClos tp1 (D.Suc tpVar)
       appliedSuc1 <- doClos2 suc1 tpVar (D.mkVar appliedTp1 (S size))
       appliedSuc2 <- doClos2 suc2 tpVar (D.mkVar appliedTp2 (S size))
       chktp <- checkTp False (S size) appliedTp1 appliedTp2
       chkzero <- checkNf size (D.Normal zeroTp zero1) (D.Normal zeroTp zero2)
       chksuc <- checkNf (2 + size) (D.Normal appliedSucTp appliedSuc1) (D.Normal appliedSucTp appliedSuc2)
       chkn <- checkNe size n1 n2
       pure $ chktp && chkzero && chksuc && chkn
  checkNe size (D.Fst ne1)                           (D.Fst ne2)                           = checkNe size ne1 ne2
  checkNe size (D.Snd ne1)                           (D.Snd ne2)                           = checkNe size ne1 ne2
  checkNe size (D.Open ne1)                          (D.Open ne2)                          = checkNe size ne1 ne2
  checkNe size (D.J mot1 refl1 tp1 left1 right1 eq1) (D.J mot2 refl2 tp2 left2 right2 eq2) =
    do chktp <- checkTp False size tp1 tp2
       chkleft <- checkNf size (D.Normal tp1 left1) (D.Normal tp2 left2)
       chkright <- checkNf size (D.Normal tp1 right1) (D.Normal tp2 right2)
       let motVar1 = D.mkVar tp1 size
       let motVar2 = D.mkVar tp1 (S size)
       let motVar3 = D.mkVar (D.Id tp1 left1 right1) (2 + size)
       motclos1 <- doClos3 mot1 motVar1 motVar2 motVar3
       motclos2 <- doClos3 mot2 motVar1 motVar2 motVar3
       chkmot <- checkTp False (3 + size) motclos1 motclos2
       let reflVar = D.mkVar tp1 size
       reflTp1 <- doClos refl1 reflVar
       reflTerm1 <- doClos3 mot1 reflVar reflVar (D.Refl reflVar)
       reflTp2 <- doClos refl2 reflVar
       reflTerm2 <- doClos3 mot2 reflVar reflVar (D.Refl reflVar)
       chkrefl <- checkNf (S size) (D.Normal reflTp1 reflTerm1) (D.Normal reflTp2 reflTerm2)
       chkeq <- checkNe size eq1 eq2
       pure $ chktp && chkleft && chkright && chkmot && chkrefl && chkeq
  checkNe _     _                                     _                                    = pure False

  checkTp : (Monad m, Catchable m Error) =>
            (subtype : Bool) -> Nat -> DT -> DT -> m Bool
  checkTp subtype size (D.Neutral _ term1)     (D.Neutral _ term2)     = checkNe size term1 term2
  checkTp subtype size  D.N                     D.N                    = pure True
  checkTp subtype size (D.Id tp1 left1 right1) (D.Id tp2 left2 right2) =
    do chktp <- checkTp subtype size tp1 tp2
       chkleft <- checkNf size (D.Normal tp1 left1) (D.Normal tp1 left2)
       chkright <- checkNf size (D.Normal tp1 right1) (D.Normal tp1 right2)
       pure $ chktp && chkleft && chkright
  checkTp subtype size (D.Pi src dest)         (D.Pi src' dest')       =
    do let var = D.mkVar src' size
       chksrc <- checkTp subtype size src' src
       destclos <- doClos dest var
       destclos' <- doClos dest' var
       chkdest <- checkTp subtype (S size) destclos destclos'
       pure $ chksrc && chkdest
  checkTp subtype size (D.Sg fst snd)          (D.Sg fst' snd')        =
    do let var = D.mkVar fst size
       chkfst <- checkTp subtype size fst fst'
       sndclos <- doClos snd var
       sndclos' <- doClos snd' var
       chksnd <- checkTp subtype (S size + 1) sndclos sndclos'
       pure $ chkfst && chksnd
  checkTp subtype size (D.Box t)               (D.Box t')              = checkTp subtype size t t'
  checkTp subtype size (D.Uni k)               (D.Uni j)               = pure $ if subtype then k <= j else k == j
  checkTp _       _     _                       _                      = pure False

initialEnv : (Monad m, Catchable m Error) =>
             Syn.Env -> m D.Env
initialEnv [] = pure []
initialEnv (t :: env) =
  do env' <- initialEnv env
     t' <- eval t env'
     pure $ D.Neutral t' (D.Var (List.length env)) :: env'

-- Main function for doing a full normalization
normalize : (Monad m, Catchable m Error) =>
            Syn.Env -> Syn.T -> Syn.T -> m Syn.T
normalize env term tp =
  do env' <- initialEnv env
     tp' <- eval tp env'
     term' <- eval term env'
     readBackNf (List.length env') (D.Normal tp' term')