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
Notation "A <:~ B" := (csub A B) (at level 45).
Notation "A << B" := (tpre A B) (at level 45).
(* Notation "e1 <<< e2" := (epre e1 e2) (at level 45). *)

Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).
Notation "e ^ x"        := (open_exp_wrt_exp e (e_var_f x)).

Notation "v |-> A v'" := (Cast v A v') (at level 68).
Notation "e ~-> r" := (step e r) (at level 68).

Notation "t ->* r" := (steps t r) (at level 68). 


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

Definition env := list (atom * exp).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let E := gather_atoms_with (fun x : ctx => dom x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  constr:(A `union` B `union` C `union` D `union` F).



Lemma fvalue_lc : forall v,
  fvalue v -> lc_exp v.
Proof.
 intros v H.
 induction* H.
Qed.


Lemma fvalue_value : forall v,
  fvalue v -> value v.
Proof.
 intros v H.
 induction* H.
Qed.



Lemma pvalue_value : forall v,
  pvalue v -> value v.
Proof.
 intros v H.
 induction* H.
Qed.


Lemma pvalue_lc : forall v,
  pvalue v -> lc_exp v.
Proof.
  intros v H.
  inductions H; eauto.
  forwards*: fvalue_lc H.
Qed.


Lemma gvalue_lc : forall v,
    gvalue v -> lc_exp v.
Proof.
  intros v H.
  induction* H; try solve[forwards*: svalue_lc H];try solve[forwards*: ssvalue_lc H];
  try solve[forwards*: pvalue_lc H;forwards*: pvalue_lc H0];
  try solve[forwards*: fvalue_lc H].
Qed.  

Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  intros v H.
  induction* H; try solve[forwards*: svalue_lc H];try solve[forwards*: ssvalue_lc H];
  try solve[forwards*: pvalue_lc H;forwards*: pvalue_lc H0];
  try solve[forwards*: fvalue_lc H];
  try solve[forwards*: gvalue_lc H].
Qed.  



Lemma uvalue_lc : forall v,
    uvalue v -> lc_exp v.
Proof.
  intros v H.
  induction* H; try solve[forwards*: value_lc H];try solve[forwards*: value_lc H];
  try solve[forwards*: value_lc H;forwards*: value_lc H0];
  try solve[forwards*: fvalue_lc H].
Qed.


Lemma svalue_lc : forall v,
    svalue v -> lc_exp v.
Proof.
  intros v H.
  induction* H; try solve[forwards*: value_lc H];try solve[forwards*: value_lc H];
  try solve[forwards*: value_lc H;forwards*: value_lc H0];
  try solve[forwards*: fvalue_lc H].
Qed.




Lemma uvalue_value: forall u,
 uvalue u ->
 value u.
Proof.
  introv val.
  inductions val; eauto.
Qed.


Lemma svalue_uvalue: forall u,
 svalue u ->
 uvalue u.
Proof.
  introv val.
  inductions val; eauto.
Qed.

(* Lemma uvalued_value: forall u,
 uvalue u ->
 value (e_anno u t_dyn).
Proof.
  introv val.
  inductions val; eauto.
Qed. *)


(* Lemma valued_uvalue: forall u, 
 value (e_anno u t_dyn) ->
 uvalue u.
Proof.
  introv val.
  inductions val; eauto.
  inverts* H.
Qed. *)


Lemma gvalue_value: forall g,
 gvalue g ->
 value g.
Proof.
  introv gval.
  inductions gval; eauto.
Qed.


Lemma valued_value: forall u, 
 value (e_anno u t_dyn) ->
 value u.
Proof.
  introv val.
  inductions val; eauto.
  +
  inverts* H.
  +
  forwards*: gvalue_value H.
Qed.

Hint Resolve fvalue_value pvalue_value pvalue_lc value_lc: core.


Lemma step_not_abs: forall (e:exp),
    irred (e_abs e).
Proof.
  introv.
  unfold irred.
  introv H;
  inverts* H;
  unfold not;intros; try solve[destruct E; unfold fill in *; inverts* H0].
Qed.


Lemma nstep_not_abs: forall (e:exp),
    nirred (e_abs e).
Proof.
  introv.
  unfold nirred.
  introv H;
  inverts* H;
  unfold not;intros; try solve[destruct E; unfold fill in *; inverts* H0].
Qed.


Lemma step_not_fix: forall (e:exp),
    irred (e_fixpoint e).
Proof.
  introv.
  unfold irred.
  introv H;
  inverts* H;
  unfold not;intros; try solve[destruct E; unfold fill in *; inverts* H0].
Qed.


Lemma nstep_not_fix: forall (e:exp),
    nirred (e_fixpoint e).
Proof.
  introv.
  unfold nirred.
  introv H;
  inverts* H;
  unfold not;intros; try solve[destruct E; unfold fill in *; inverts* H0].
Qed.

Lemma step_not_fvalue: forall (v:exp),
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
    destruct E; unfold fill in H0; inverts* H0.
    inverts* H3.
    destruct E; unfold fill in H; inverts* H.
    inverts* H4.
    inverts* H8.
  -
    inverts* H; try solve[destruct E; unfold fill in H0; inverts* H0].
    inverts* H6.
    inverts H1.
Qed.


Lemma nstep_not_fvalue: forall (v:exp),
    fvalue v -> nirred v.
Proof.
  introv.
  unfold nirred.
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
    destruct E; unfold fill in H0; inverts* H0.
    inverts* H3.
    destruct E; unfold fill in H; inverts* H.
    inverts* H4.
    inverts* H8.
  -
    inverts* H; try solve[destruct E; unfold fill in H0; inverts* H0].
    inverts* H6.
    inverts* H1.
Qed.


Lemma step_not_value: forall (v:exp),
    value v -> irred v.
Proof.
  introv.
  unfold irred.
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
    forwards* h1: step_not_fvalue H1.
    unfold irred in *.
    forwards*: h1.
  -
  inverts* H0;
  try solve[inverts* H6];
  try solve[
    destruct E; unfold fill in H; inverts* H;
    try solve[forwards*: gvalue_value H2]];
  try solve[forwards*: gvalue_value H2];
  try solve[inverts H2].
Qed. 



Lemma nstep_not_value: forall (v:exp),
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
  -
  inverts* H0;
  try solve[inverts* H6];
  try solve[
    destruct E; unfold fill in H; inverts* H;
    try solve[forwards*: gvalue_value H2]];
  try solve[forwards*: gvalue_value H2].
  inverts H2.
  inverts H2.
Qed. 


(* 
Lemma multi_red_anno : forall A t t',
    t ->* (r_e t') -> (e_anno t A) ->* (r_e (e_anno t' A)).
Proof.
  introv Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (annoCtx A)). 
  apply wf_annoCtx; auto. 
  forwards*: step_eval H1 H.
Qed.


Lemma multi_red_app : forall v t t',
    value v -> t ->* (r_e t') -> (e_app v t) ->* (r_e (e_app v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (appCtxR v)). 
  apply wf_appCtxR; auto. 
  forwards*: step_eval H1 H.
Qed.

Lemma multi_red_app2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* (r_e t1') -> (e_app t1 t2) ->* (r_e (e_app t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformed (appCtxL t2)). eauto.
  forwards*: step_eval H0 H.
Qed.

Lemma multi_red_merge : forall v t t',
    value v -> t ->* (r_e t') -> (e_merge v t) ->* (r_e (e_merge v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (mergeCtxR v)). eauto.
  forwards*: step_eval H1 H.
Qed.


Lemma multi_red_merge2 : forall t1 t2 t1',
    lc_exp t2 -> t1 ->* (r_e t1') -> (e_merge t1 t2) ->* (r_e (e_merge t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformed (mergeCtxL t2)). eauto.
  forwards*: step_eval H0 H.
Qed.


Lemma multi_red_rcd : forall t t' l,
    t ->* (r_e t') -> (e_rcd l t) ->* (r_e (e_rcd l t')).
Proof.
  introv Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (rcdCtx l)); eauto.
  forwards*: step_eval H1 H.
Qed.



Lemma multi_red_proj : forall t t' l,
    t ->* (r_e t') -> (e_proj t l) ->* (r_e (e_proj t' l)).
Proof.
  introv Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (prjCtx l)); eauto.
  forwards*: step_eval H1 H.
Qed.



 *)
