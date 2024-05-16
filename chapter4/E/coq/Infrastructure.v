Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf.

Require Import List. Import ListNotations.
Require Import Strings.String.


Definition irred e : Prop := forall b, ~(step e b).


Notation "Γ ⊢ E ⇒ A" := (Typing Γ E Inf A) (at level 45).
Notation "Γ ⊢ E ⇐ A" := (Typing Γ E Chk A) (at level 45).


Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).
Notation "e ^ x"        := (open_exp_wrt_exp e (e_var_f x)).

Notation "v ~-> A v'" := (Cast v A v') (at level 68).

Notation "t ->* r" := (steps t r) (at level 68). 
(* Notation "t ->** r" := (gsteps t r) (at level 68). *)

Lemma star_one:
forall a b, step a (Expr b) -> steps a (Expr b).
Proof.
eauto using steps.
Qed.

Lemma star_trans:
forall a b, steps a (Expr b) -> forall c, steps b (Expr c) -> steps a (Expr c).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.

(* 
Lemma gstar_one:
forall a b, gstep a (Expr b) -> gsteps a (Expr b).
Proof.
eauto using steps.
Qed.

Lemma gstar_trans:
forall a b, gsteps a (Expr b) -> forall c, gsteps b (Expr c) -> gsteps a (Expr c).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.


Lemma gstar_transb:
forall a b, gsteps a (Expr b) -> gsteps b Blame -> gsteps a Blame.
Proof.
  introv red1 red2.
  inductions red1; eauto using gsteps.
Qed. *)

Hint Resolve star_one star_trans  : core.




(** [x # E] to be read x fresh from E captures the fact that
    x is unbound in E . *)

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let E := gather_atoms_with (fun x : ctx => dom x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union` C `union` D `union` F).



Lemma pval_lc : forall v,
    pval v -> lc_exp v.
Proof.
  intros v H.
  induction* H. 
Qed.



Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  intros v H.
  induction* H.
  forwards*: pval_lc H. 
Qed.


Lemma fval_lc : forall v,
    fval v -> lc_exp v.
Proof.
  intros v H.
  induction* H. 
Qed.

Lemma fval_pval : forall v,
    fval v -> pval v.
Proof.
  intros v H.
  induction* H. 
Qed.


Hint Resolve value_lc pval_lc fval_lc fval_pval: core.

(* 
Lemma pval_blame: forall (v:exp),
    pval v -> not(step v Blame).
Proof.
  introv sval.
  unfold not;intros nt. 
  inductions sval;inverts nt;
  try solve[destruct E; unfold simpl_fill in H0; inverts* H0].
  -
  inverts H1; try solve[destruct E; unfold simpl_fill in H0; inverts* H0].
  -
  inverts H4; try solve[destruct E; unfold simpl_fill in H0; inverts* H0].
  -
  destruct E; unfold simpl_fill in H; inverts* H.
  -
  destruct E; unfold simpl_fill in H; inverts* H.
Qed. *)

Lemma step_not_value: forall (v:exp),
    value v -> irred v.
Proof.
  introv.
  unfold irred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros.
  - inverts* H; try solve[inverts H1].
    destruct E; unfold simpl_fill in H0; inverts* H0.
    destruct E; unfold simpl_fill in H0; inverts* H0.
Qed.

Lemma step_not_fvalue: forall (v:exp),
    irred (e_fval v).
Proof.
  introv.
  unfold irred.
  introv H.
  inverts* H;
  unfold not;intros;
  try solve[ destruct E; unfold simpl_fill in H0; inverts* H0].
Qed.

Lemma sfill_appl : forall e1 e2,
  (e_app e1 e2) = (simpl_fill (sappCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_appr : forall e1 e2,
  (e_app e1 e2) = (simpl_fill (sappCtxR e1) e2).
Proof.
  intros. eauto.
Qed.




Lemma sfill_prol : forall e1 e2,
  (e_pro e1 e2) = (simpl_fill (sproCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_pror : forall e1 e2,
  (e_pro e1 e2) = (simpl_fill (sproCtxR e1) e2).
Proof.
  intros. eauto.
Qed.


Lemma sfill_l : forall e1,
  (e_l e1) = (simpl_fill (slCtx) e1).
Proof.
  intros. eauto.
Qed.

Lemma sfill_r : forall e1,
(e_r e1) = (simpl_fill (srCtx) e1).
Proof.
  intros. eauto.
Qed.


Lemma sfill_anno : forall e t,
  (e_anno e t) = (simpl_fill (sannoCtx t) e).
Proof.
  intros. eauto.
Qed.


Lemma multi_red_app : forall e t t',
    t ->* (Expr t') -> (e_app (e_abs e) t) ->* (Expr (e_app (e_abs e) t')).
Proof.
  introv Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (sappCtxR (e_abs e))). eauto.
  forwards*: Step_eval H0 H.
Qed.


Lemma multi_red_app2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* (Expr t1') -> (e_app t1 t2) ->* (Expr (e_app t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (sappCtxL t2)). eauto.
  forwards*: Step_eval H0 H.
Qed.


Lemma multi_red_pro : forall v t t',
    value v -> t ->* (Expr t') -> (e_pro v t) ->* (Expr (e_pro v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (sproCtxR v)). eauto.
  forwards*: Step_eval H0 H.
Qed.


Lemma multi_red_pro2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* (Expr t1') -> (e_pro t1 t2) ->* (Expr (e_pro t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (sproCtxL t2)). eauto.
  forwards*: Step_eval H0 H.
Qed.


Lemma multi_red_l : forall t1 t1',
     t1 ->* (Expr t1') -> (e_l t1) ->* (Expr (e_l t1')).
Proof.
  introv Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (slCtx)). eauto.
  forwards*: Step_eval H0 H.
Qed.


Lemma multi_red_r : forall t1 t1',
     t1 ->* (Expr t1') -> (e_r t1) ->* (Expr (e_r t1')).
Proof.
  introv Red.
  inductions Red; eauto.
  -
  assert(simpl_wf (srCtx)). eauto.
  forwards*: Step_eval H0 H.
Qed.

(* 
Lemma step_not_pval: forall e e', 
 step e (Expr e') ->
 not(pval e').
Proof.
  introv red.
  inductions red; try solve[unfold not;intros nt;inverts* nt].
  -
  destruct E; unfold simpl_fill;unfold not;intros nt;inverts* nt.
  -
  unfold not;intros nt;inverts* nt.
  inverts red; try solve[
    destruct E; unfold simpl_fill in *;inverts* H0
  ].
  inverts* H2.
  -
  inverts* H0;
  unfold not;intros nt;inverts* nt; try solve[inverts H3].
  -
  inverts H.
  unfold not;intros nt;inverts* nt; try solve[inverts H2].
  inverts H2. inverts H4.
  -
  inverts H.
  unfold not;intros nt;inverts* nt; try solve[inverts H2].
  inverts H2. inverts H5.
Qed. *)



Lemma multi_red_anno : forall A t t',
    t ->* (Expr t') -> (e_anno t A) ->* (Expr (e_anno t' A)).
Proof.
  introv Red.
  inductions Red; eauto.
  assert(simpl_wf (sannoCtx A)). eauto.
  forwards*: Step_eval H0 H.
Qed.



