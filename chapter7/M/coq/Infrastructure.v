Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf.

Require Import List. Import ListNotations.
Require Import Strings.String.


Definition irred e : Prop := forall b, ~(step e b).


Definition nirred e : Prop := forall b, ~(cbn e b).

Notation "Γ ⊢ E ⇒ A" := (Typing Γ E Inf A) (at level 45).
Notation "Γ ⊢ E ⇐ A" := (Typing Γ E Chk A) (at level 45).

Notation "[ z ~> u ] e" := (subst_dexp u z e) (at level 0).
Notation "t ^^ u"       := (open_dexp_wrt_dexp t u) (at level 67).
Notation "e ^ x"        := (open_dexp_wrt_dexp e (de_var_f x)).

Notation "v |-> A v'" := (Cast v A v') (at level 68).
Notation "e ~-> r" := (step e r) (at level 68).

(* Notation "t ->* r" := (steps t r) (at level 68).  *)


(* Lemma star_one:
forall a b, step a (r_e b) -> steps a (r_e b).
Proof.
eauto using steps.
Qed.

Lemma star_trans:
forall a b, steps a (r_e b) -> forall c, steps b (r_e c) -> steps a (r_e c).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.

Lemma star_transb:
forall a b, steps a (r_e b) -> steps b r_blame -> steps a r_blame.
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.



Hint Resolve star_one star_trans star_transb: core. *)




(** [x # E] to be read x fresh from E captures the fact that
    x is unbound in E . *)

Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * dexp).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * dtyp) => dom x) in
  let D := gather_atoms_with (fun x : dexp => fv_dexp x) in
  let E := gather_atoms_with (fun x : dctx => dom x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union` C `union` D `union` F).




Lemma fvalue_lc : forall v,
  fvalue v -> lc_dexp v.
Proof.
 intros v H.
 induction* H.
Qed.


Lemma value_lc : forall v,
    value v -> lc_dexp v.
Proof.
  intros v H.
  induction* H; 
  try solve[inverts* IHvalue1; inverts* IHvalue2];
  try solve[inverts* IHvalue];
  try solve[forwards*: fvalue_lc H].
Qed.


Lemma step_not_abs: forall (e:dexp),
    irred (de_abs e).
Proof.
  introv.
  unfold irred.
  introv H;
  inverts* H;
  unfold not;intros; try solve[destruct E; unfold fill in *; inverts* H0].
Qed.


Lemma nstep_not_abs: forall (e:dexp),
    nirred (de_abs e).
Proof.
  introv.
  unfold nirred.
  introv H;
  inverts* H;
  unfold not;intros; try solve[destruct E; unfold fill in *; inverts* H0].
Qed.


Lemma step_not_fix: forall (e:dexp),
    irred (de_fixpoint e).
Proof.
  introv.
  unfold irred.
  introv H;
  inverts* H;
  unfold not;intros; try solve[destruct E; unfold fill in *; inverts* H0].
Qed.


Lemma nstep_not_fix: forall (e:dexp),
    nirred (de_fixpoint e).
Proof.
  introv.
  unfold nirred.
  introv H;
  inverts* H;
  unfold not;intros; try solve[destruct E; unfold fill in *; inverts* H0].
Qed.



Lemma step_not_fvalue: forall (v:dexp),
    fvalue v -> irred v.
Proof.
  introv.
  unfold irred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros; try solve[inverts* H0];
  try solve[inverts* H;
  destruct E; unfold fill in H1; inverts* H1];
  try solve[inverts* H;
  try solve[destruct E; unfold fill in H0; inverts* H0];
  try solve[inverts H0]];
  try solve[inverts H0].
  -
    inverts* H; try solve[destruct E; unfold fill in H0; inverts* H0].
    destruct E; unfold fill in H0; inverts* H0.
    inverts* H3.
    destruct E; unfold fill in H; inverts* H.
  -
    inverts* H; try solve[destruct E; unfold fill in H0; inverts* H0].
    inverts* H1.
Qed.


Lemma nstep_not_fvalue: forall (v:dexp),
    fvalue v -> nirred v.
Proof.
  introv.
  unfold nirred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros; try solve[inverts* H0];
  try solve[inverts* H;
  destruct E; unfold nfill in H1; inverts* H1];
  try solve[inverts* H;
  try solve[destruct E; unfold nfill in H0; inverts* H0];
  try solve[inverts H0]];
  try solve[inverts H0].
  -
    inverts* H; try solve[destruct E; unfold fill in H0; inverts* H0].
    destruct E; unfold fill in H0; inverts* H0.
    inverts* H3.
    destruct E; unfold fill in H; inverts* H.
  -
    inverts* H; try solve[destruct E; unfold fill in H0; inverts* H0].
    inverts* H1.
Qed.

Lemma step_not_value: forall (v:dexp),
    value v -> irred v.
Proof.
  introv.
  unfold irred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros; try solve[inverts* H0];
  try solve[inverts* H;
  destruct E; unfold fill in H1; inverts* H1];
  try solve[inverts* H;
  try solve[destruct E; unfold fill in H0; inverts* H0];
  try solve[inverts H0]];
  try solve[inverts H0].
  forwards*: step_not_fvalue H.
Qed. 


Lemma nstep_not_value: forall (v:dexp),
    value v -> nirred v.
Proof.
  introv.
  unfold nirred.
  inductions v; introv H;
  unfold not;intros;
  inverts* H;
  try solve[
    inverts* H1;
    try solve[destruct E; unfold fill in H; inverts* H1];
    try solve[inverts* H] ];
  try solve[
  inverts* H0;
  try solve[destruct E; unfold fill in H; inverts* H]].
  -
    forwards* h1: nstep_not_fvalue H1.
    unfold nirred in *.
    forwards*: h1.
Qed. 




(* Lemma multi_red_anno : forall A t t',
    not (value (e_anno t A)) ->
    t ->* (r_e t') -> (e_anno t A) ->* (r_e (e_anno t' A)).
Proof.
  introv nt Red.
  inductions Red; eauto.
  forwards*:  step_not_pvalue H.
  assert(not (value (e_anno e' A))).
  unfold not; intros ntt; inverts* ntt.
  forwards*: IHRed.
Qed. *)


(* Lemma multi_red_anno : forall A t t',
    t ->* (r_e t') -> (e_anno t A) ->* (r_e (e_anno t' A)).
Proof.
  introv Red.
  inductions Red; eauto.
Qed.


Lemma multi_red_app : forall v t t',
    value v -> t ->* (r_e t') -> (e_app v t) ->* (r_e (e_app v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (appCtxR v)). 
  apply wf_appCtxR; auto. 
  forwards*: do_step H1 H.
Qed.

Lemma multi_red_app2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* (r_e t1') -> (e_app t1 t2) ->* (r_e (e_app t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformed (appCtxL t2)). eauto.
  forwards*: do_step H0 H.
Qed.

Lemma multi_red_merge : forall v t t',
    value v -> t ->* (r_e t') -> (e_merge v t) ->* (r_e (e_merge v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (mergeCtxR v)). eauto.
  forwards*: do_step H1 H.
Qed.


Lemma multi_red_merge2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* (r_e t1') -> (e_merge t1 t2) ->* (r_e (e_merge t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformed (mergeCtxL t2)). eauto.
  forwards*: do_step H0 H.
Qed.


Lemma multi_red_rcd : forall t t' l,
    t ->* (r_e t') -> (e_rcd l t) ->* (r_e (e_rcd l t')).
Proof.
  introv Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (rcdCtx l)); eauto.
  forwards*: do_step H1 H.
Qed.



Lemma multi_red_proj : forall t t' l,
    t ->* (r_e t') -> (e_proj t l) ->* (r_e (e_proj t' l)).
Proof.
  introv Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (prjCtx l)); eauto.
  forwards*: do_step H1 H.
Qed.
 *)



