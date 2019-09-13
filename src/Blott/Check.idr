-- This file implements the semantic type-checking algorithm described in the paper. 
module Check

import Control.Catchable
import Domain as D
import Syntax as Syn
import Error
import Nbe

%access public export
%default total

data EnvEntry = Term DT DT Nat
              | TopLevel DT DT

CEnv : Type
CEnv = List EnvEntry

addTerm : DT -> DT -> CEnv -> CEnv
addTerm term tp env = Term term tp Z :: env

envToSemEnv : CEnv -> D.Env  
envToSemEnv = map conv 
  where 
  conv : EnvEntry -> DT
  conv (TopLevel _ term) = term
  conv (Term _ term _)   = term

stripEnv : CEnv -> CEnv
stripEnv = map go
  where 
  go : EnvEntry -> EnvEntry
  go (TopLevel tp tm) = TopLevel tp tm
  go (Term tp tm _) = Term tp tm Z
  
applyLock : CEnv -> CEnv
applyLock = map go
  where 
  go : EnvEntry -> EnvEntry
  go (TopLevel tp tm) = TopLevel tp tm
  go (Term tp tm l) = Term tp tm (S l)

getVar : (Monad m, Catchable m Error) =>
         CEnv -> Nat -> m DT
getVar {m} env n = maybe (throw $ Misc "Env out of bounds") go (List.index' n env)
  where 
  go : EnvEntry -> m DT
  go (Term tp _ Z) = pure tp
  go (TopLevel tp _) = pure tp
  go (Term _ _ _) = throw UsingLockedVariable

covering 
assertSubtype : (Monad m, Catchable m Error) => 
                Nat -> DT -> DT -> m ()
assertSubtype size t1 t2 = 
  if !(Nbe.checkTp True size t1 t2)
    then pure () 
    else throw $ TypeMismatch t1 t2

covering
assertEqual : (Monad m, Catchable m Error) => 
              Nat -> DT -> DT -> DT -> m ()
assertEqual size t1 t2 tp =
  if !(Nbe.checkNf size (D.Normal tp t1) (D.Normal tp t2))
    then pure ()
    else throw $ TypeMismatch t1 t2

mutual
  covering 
  check : (Monad m, Catchable m Error) => 
          CEnv -> Nat -> Syntax.T -> Domain.DT -> m ()    
  check env size (Syn.Let def body)    tp =
    do defTp <- synth env size def
       defVal <- Nbe.eval def (envToSemEnv env)
       check (addTerm defVal defTp env) (S size) body tp
  check env size  Syn.N                   (D.Uni _)             = pure ()
  check env size  Syn.N                tp                       = throw $ ExpectingUniverse tp
  check env size (Syn.Id tp' l r)      tp@(D.Uni _)             =
    do check env size tp' tp
       tp'' <- Nbe.eval tp' (envToSemEnv env)
       check env size l tp''
       check env size r tp''
  check env size (Syn.Id tp' l r)      tp                       = throw $ ExpectingUniverse tp
  check env size (Syn.Refl term)          (D.Id tp left right)  =
    do check env size term tp
       term' <- Nbe.eval term (envToSemEnv env)
       assertEqual size term' left tp
       assertEqual size term' right tp
  check env size (Syn.Refl term)       tp                       = throw $ Misc $ "Expecting Id but found\n" ++ show tp
  check env size (Syn.Pi l r)          tp@(D.Uni _)             =
    do check env size l tp
       lSem <- Nbe.eval l (envToSemEnv env)
       let var = D.mkVar lSem size
       check (addTerm var lSem env) size r tp
  check env size (Syn.Pi l r)          tp                       = throw $ ExpectingUniverse tp
  check env size (Syn.Sg l r)          tp@(D.Uni _)             =
    do check env size l tp
       lSem <- Nbe.eval l (envToSemEnv env)
       let var = D.mkVar lSem size
       check (addTerm var lSem env) size r tp
  check env size (Syn.Sg l r)          tp                       = throw $ ExpectingUniverse tp
  check env size (Syn.Lam body)           (D.Pi argTp clos)     =
    do let var = D.mkVar argTp size
       destTp <- Nbe.doClos clos var
       check (addTerm var argTp env) (S size) body destTp
  check env size (Syn.Lam body)        tp                       = throw $ Misc $ "Expecting Pi but found\n" ++ show tp
  check env size (Syn.Pair left right)    (D.Sg leftTp rightTp) =
    do check env size left leftTp
       leftSem <- Nbe.eval left (envToSemEnv env)
       rightTp' <- Nbe.doClos rightTp leftSem
       check env size right rightTp'
  check env size (Syn.Pair left right) tp                       = throw $ Misc $ "Expecting Sg but found\n" ++ show tp
  check env size (Syn.Box term)        tp@(D.Uni _)             = check (applyLock env) size term tp
  check env size (Syn.Box term)        tp                       = throw $ ExpectingUniverse tp
  check env size (Syn.Shut term)          (D.Box tp)            = check (applyLock env) size term tp
  check env size (Syn.Shut term)       tp                       = throw $ Misc $ "Expecting Box but found\n" ++ show tp
  check env size (Syn.Uni i)              (D.Uni j)             = 
    if i < j 
      then pure () 
      else throw $ Misc $ "Universe mismatch: " ++ show i ++ ">=" ++ show j
  check env size (Syn.Uni i)           tp                       = throw $ Misc $ "Expecting universe over " ++ show i ++ " but found\n" ++ show tp
  check env size  term                 tp                       = assertSubtype size !(synth env size term) tp
  
  covering 
  synth : (Monad m, Catchable m Error) => 
          CEnv -> Nat -> Syntax.T -> m Domain.DT
  | Syn.Var i -> get_var env i
  | Check (term, tp') ->
    let tp = Nbe.eval tp' (env_to_sem_env env) in
    check ~env ~size ~term ~tp;
    tp
  | Zero -> D.Nat
  | Suc term -> check ~env ~size ~term ~tp:Nat; D.Nat
  | Fst p ->
    begin
      match synth ~env ~size ~term:p with
      | Sg (left_tp, _) -> left_tp
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Snd p ->
    begin
      match synth ~env ~size ~term:p with
      | Sg (_, right_tp) ->
        let proj = Nbe.eval (Fst p) (env_to_sem_env env) in
        Nbe.do_clos right_tp proj
      | t -> tp_error (Misc ("Expecting Sg but found\n" ^ D.show t))
    end
  | Ap (f, a) ->
    begin
      match synth ~env ~size ~term:f with
      | Pi (src, dest) ->
        check ~env ~size ~term:a ~tp:src;
        let a_sem = Nbe.eval a (env_to_sem_env env) in
        Nbe.do_clos dest a_sem
      | t -> tp_error (Misc ("Expecting Pi but found\n" ^ D.show t))
    end
  | NRec (mot, zero, suc, n) ->
    check ~env ~size ~term:n ~tp:Nat;
    let var = D.mk_var Nat size in
    check_tp ~env:(add_term ~term:var ~tp:Nat env) ~size:(size + 1) ~term:mot;
    let sem_env = env_to_sem_env env in
    let zero_tp = Nbe.eval mot (Zero :: sem_env) in
    let ih_tp = Nbe.eval mot (var :: sem_env) in
    let ih_var = D.mk_var ih_tp (size + 1) in
    let suc_tp = Nbe.eval mot (Suc var :: sem_env) in
    check ~env ~size ~term:zero ~tp:zero_tp;
    check
      ~env:(add_term ~term:var ~tp:Nat env |> add_term ~term:ih_var ~tp:ih_tp)
      ~size:(size + 2)
      ~term:suc
      ~tp:suc_tp;
    Nbe.eval mot (Nbe.eval n sem_env :: sem_env)
  | Open term ->
    let env = strip_env env in
    begin
      match synth ~env ~size ~term with
      | Box tp -> tp
      | t -> tp_error (Misc ("Expecting Box but found\n" ^ D.show t))
    end
  | J (mot, refl, eq) ->
    let eq_tp = synth ~env ~size ~term:eq in
    begin
      let sem_env = env_to_sem_env env in
      match eq_tp with
      | D.Id (tp', left, right) ->
        let mot_var1 = D.mk_var tp' size in
        let mot_var2 = D.mk_var tp' (size + 1) in
        let mot_var3 = D.mk_var (D.Id (tp', mot_var1, mot_var2)) (size + 1) in
        let mot_env =
          add_term ~term:mot_var1 ~tp:tp' env
          |> add_term ~term:mot_var2 ~tp:tp'
          |> add_term ~term:mot_var3 ~tp:(D.Id (tp', mot_var1, mot_var2)) in
        check_tp ~env:mot_env ~size:(size + 3) ~term:mot;
        let refl_var = D.mk_var tp' size in
        let refl_tp = Nbe.eval mot (D.Refl refl_var :: refl_var :: refl_var :: sem_env) in
        check ~env:(add_term ~term:refl_var ~tp:tp' env) ~size:(size + 1) ~term:refl ~tp:refl_tp;
        Nbe.eval mot (Nbe.eval eq sem_env :: right :: left :: sem_env)
      | t -> tp_error (Misc ("Expecting Id but found\n" ^ D.show t))
    end
  | _ -> tp_error (Cannot_synth_term term)

  covering 
  checkTp : (Monad m, Catchable m Error) => 
            CEnv -> Nat -> Syntax.T -> m ()
  | Syn.Nat -> ()
  | Uni _ -> ()
  | Box term -> check_tp ~env:(apply_lock env) ~size ~term
  | Pi (l, r) | Sg (l, r) ->
    check_tp ~env ~size ~term:l;
    let l_sem = Nbe.eval l (env_to_sem_env env) in
    let var = D.mk_var l_sem size in
    check_tp ~env:(add_term ~term:var ~tp:l_sem env) ~size:(size + 1) ~term:r
  | Let (def, body) ->
    let def_tp = synth ~env ~size ~term:def in
    let def_val = Nbe.eval def (env_to_sem_env env) in
    check_tp ~env:(add_term ~term:def_val ~tp:def_tp env) ~size:(size + 1) ~term:body
  | Id (tp, l, r) ->
    check_tp ~env ~size ~term:tp;
    let tp = Nbe.eval tp (env_to_sem_env env) in
    check ~env ~size ~term:l ~tp;
    check ~env ~size ~term:r ~tp
  | term ->
    begin
      match synth ~env ~size ~term with
      | D.Uni _ -> ()
      | t -> tp_error (Expecting_universe t)
    end            