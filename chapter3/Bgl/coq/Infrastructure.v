Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               syntaxn_ott.

Require Import List. Import ListNotations.
Require Import Strings.String.


Definition irred e : Prop := forall b, ~(step e b).

Notation "Γ ⊢ E ⇒ A" := (Typing Γ E Inf A) (at level 45).
Notation "Γ ⊢ E ⇐ A" := (Typing Γ E Chk A) (at level 45).


Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).


(* Notation "v ~-> A v'" := (Cast v A v') (at level 68). *)


Notation "t ->** r" := (steps t r) (at level 68).


Lemma stars_one:
forall a b, step a (e_exp b) -> steps a (e_exp b).
Proof.
eauto using steps.
Qed.

Lemma stars_trans:
forall a b, steps a (e_exp b) -> forall c, steps b (e_exp c) -> steps a (e_exp c).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.


Lemma stars_transb:
forall a b l bb, steps a (e_exp b) -> steps b (e_blame l bb) -> steps a (e_blame l bb).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.


Lemma sstars_one:
forall a b, step a (e_exp b) -> ssteps a (e_exp b).
Proof.
eauto using steps.
Qed.

Lemma sstars_trans:
forall a b, ssteps a (e_exp b) -> forall c, ssteps b (e_exp c) -> ssteps a (e_exp c).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.


Lemma sstars_transb:
forall a b l bb, steps a (e_exp b) -> ssteps b (e_blame l bb) -> ssteps a (e_blame l bb).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.


Lemma starn_one:
forall a b, step a (e_exp b) -> sstep_sz a (e_exp b) 1.
Proof.
eauto using steps.
Qed.

Lemma starn_trans:
forall a b n1, sstep_sz a (e_exp b) n1 -> forall c n2, sstep_sz b (e_exp c) n2 -> sstep_sz a (e_exp c) (n1 + n2).
Proof.
  introv H.
  inductions H; eauto using step.
  intros.
  forwards*: IHsstep_sz H1.
  eapply ssteps_n; eauto.
Qed.


Lemma starn_transb:
forall a b l bb n m, sstep_sz a (e_exp b) n -> sstep_sz b (e_blame l bb) m -> sstep_sz a (e_blame l bb) (n+m).
Proof.
  introv H.
  inductions H; eauto using steps.
  intros.
  forwards*: IHsstep_sz H1.
  eapply ssteps_nb; eauto.
Qed.

Hint Resolve starn_one starn_trans starn_transb stars_one stars_trans stars_transb sstars_one sstars_trans sstars_transb:core.


Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let E := gather_atoms_with (fun x : ctx => dom x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : term => fv_term x) in
  let H := gather_atoms_with (fun x : nexp => fv_nexp x) in
  constr:(A `union` B `union` C `union` D `union` E `union` F `union` G `union` H).



Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  intros v H.
  induction* H. 
Qed.


Hint Resolve value_lc : core.


Lemma step_not_value: forall (v:exp),
    value v -> irred v.
Proof.
  introv.
  unfold irred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros;
  try solve[inverts* H;destruct E; unfold fill in H0; inverts* H0];
  try solve[inverts* H;destruct E; unfold fill in H0; inverts* H0;
  inverts* H3;destruct E; unfold fill in H; inverts* H];
  try solve[inverts* H3;destruct E; unfold fill in H; inverts* H].
Qed.


Lemma multi_rred_app : forall v t t' l b A B,
    (dynamic_type v) = (t_arrow A B) ->
     value v -> t ->** (e_exp t') -> (e_app v l b t) ->** (e_exp (e_app v l b t')).
Proof.
  introv ty Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (appCtxR v l b)). eauto.
  forwards*: Step_eval H1 H.
Qed.


Lemma multi_rred_pro : forall v t t',
     value v -> t ->** (e_exp t') -> (e_pro v t) ->** (e_exp (e_pro v t')).
Proof.
  introv  Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (proCtxR v)). eauto.
  forwards*: Step_eval H1 H.
Qed.


Lemma multi_bblame_app : forall v t l1 b1 l2 b2 A B,
(dynamic_type v) = (t_arrow A B) ->
    value v -> t ->** (e_blame l1 b1) -> (e_app v l2 b2 t) ->** (e_blame l1 b1).
Proof.
  introv ty Val Red.
  inductions Red; eauto.
  eapply step_nb.
  assert(wellformed (appCtxR v l2 b2)). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply step_b. 
  assert(wellformed (appCtxR v l2 b2 )). eauto.
  forwards*: Step_blame H0 H.
Qed.

Lemma multi_bblame_pro : forall v t l1 b1 ,
    value v -> t ->** (e_blame l1 b1) -> (e_pro v t) ->** (e_blame l1 b1).
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply step_nb.
  assert(wellformed (proCtxR v)). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply step_b. 
  assert(wellformed (proCtxR v)). eauto.
  forwards*: Step_blame H0 H.
Qed.


Lemma multi_bblame_appv : forall v t l1 b1,
    value v -> t ->** (e_blame l1 b1) -> (e_appv v t) ->** (e_blame l1 b1).
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply step_nb.
  assert(wellformed (appvCtxR v)). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply step_b. 
  assert(wellformed (appvCtxR v)). eauto.
  forwards*: Step_blame H0 H.
Qed.



Lemma multi_rred_appv : forall v t t',
     value v -> t ->** (e_exp t') -> (e_appv v t) ->** (e_exp (e_appv v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformed (appvCtxR v)). eauto.
  forwards*: Step_eval H1 H.
Qed.



Lemma multi_rred_appv2 : forall t1 t2 t1' ,
    lc_exp t2 -> t1 ->** (e_exp t1') -> (e_appv t1 t2) ->** (e_exp (e_appv t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformed (appvCtxL t2)). eauto.
  forwards*: Step_eval H0 H.
Qed.


Lemma multi_bblame_appv2 : forall t1 t2 l1 b1,
    lc_exp t2 -> t1 ->** e_blame l1 b1 -> (e_appv t1 t2) ->** e_blame l1 b1.
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply step_nb.
  assert(wellformed (appvCtxL t2 )). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply step_b. 
  assert(wellformed (appvCtxL t2)). eauto.
  forwards*: Step_blame H0 H.
Qed.





Lemma multi_rred_pro2 : forall t1 t2 t1' ,
    lc_exp t2 -> t1 ->** (e_exp t1') -> (e_pro t1 t2) ->** (e_exp (e_pro t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformed (proCtxL t2)). eauto.
  forwards*: Step_eval H0 H.
Qed.


Lemma multi_bblame_pro2 : forall t1 t2 l1 b1,
    lc_exp t2 -> t1 ->** e_blame l1 b1 -> (e_pro t1 t2) ->** e_blame l1 b1.
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply step_nb.
  assert(wellformed (proCtxL t2 )). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply step_b. 
  assert(wellformed (proCtxL t2)). eauto.
  forwards*: Step_blame H0 H.
Qed.




Lemma multi_rred_app2 : forall t1 t2 t1' l b,
    lc_exp t2 -> t1 ->** (e_exp t1') -> (e_app t1 l b t2) ->** (e_exp (e_app t1' l b t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformed (appCtxL t2 l b)). eauto.
  forwards*: Step_eval H0 H.
Qed.


Lemma multi_bblame_app2 : forall t1 t2 l1 b1 l2 b2,
    lc_exp t2 -> t1 ->** e_blame l1 b1 -> (e_app t1 l2 b2 t2) ->** e_blame l1 b1.
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply step_nb.
  assert(wellformed (appCtxL t2 l2 b2 )). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply step_b. 
  assert(wellformed (appCtxL t2 l2 b2 )). eauto.
  forwards*: Step_blame H0 H.
Qed.

Lemma multi_rred_anno : forall t t' A l b ,
    t ->** (e_exp t') -> (e_anno t l b A) ->** (e_exp (e_anno t' l b A )).
Proof.
  introv Red.
  inductions Red; eauto.
  assert(wellformed (annoCtx l b A)). eauto.
  forwards*: Step_eval H0 H.
Qed.

Lemma multi_bblame_l : forall t l0 b0 l b,
    t ->** e_blame l b -> (e_l t l0 b0) ->** e_blame l b.
Proof.
  introv Red.
  inductions Red; eauto.
  eapply step_nb.
  assert(wellformed (lCtx l0 b0)). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply step_b. 
  assert(wellformed (lCtx l0 b0)). eauto.
  forwards*: Step_blame H0 H.
Qed.



Lemma multi_rred_l : forall t t' l b ,
    t ->** (e_exp t') -> (e_l t l b) ->** (e_exp (e_l t' l b)).
Proof.
  introv Red.
  inductions Red; eauto.
  assert(wellformed (lCtx l b)). eauto.
  forwards*: Step_eval H0 H.
Qed.



Lemma multi_bblame_r : forall t l0 b0 l b,
    t ->** e_blame l b -> (e_r t l0 b0) ->** e_blame l b.
Proof.
  introv Red.
  inductions Red; eauto.
  eapply step_nb.
  assert(wellformed (rCtx l0 b0)). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply step_b. 
  assert(wellformed (rCtx l0 b0)). eauto.
  forwards*: Step_blame H0 H.
Qed.



Lemma multi_rred_r : forall t t' l b ,
    t ->** (e_exp t') -> (e_r t l b) ->** (e_exp (e_r t' l b)).
Proof.
  introv Red.
  inductions Red; eauto.
  assert(wellformed (rCtx l b)). eauto.
  forwards*: Step_eval H0 H.
Qed.


Lemma multi_bblame_anno : forall t A l0 b0 l b,
    t ->** e_blame l b -> (e_anno t l0 b0 A) ->** e_blame l b.
Proof.
  introv Red.
  inductions Red; eauto.
  eapply step_nb.
  assert(wellformed (annoCtx l0 b0 A)). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply step_b. 
  assert(wellformed (annoCtx l0 b0 A)). eauto.
  forwards*: Step_blame H0 H.
Qed.




Lemma fillb_cast: forall v A p b B,
  (trm_cast v A p b B) = (fillb (castCtxb A p b B )  v).
Proof.
  introv.
  eauto.
Qed.


Lemma fill_app: forall e1 e2 p b,
  (e_app e1  p b e2) = (fill (appCtxL e2 p b)  e1).
Proof.
  introv.
  eauto.
Qed.


Lemma fill_appv: forall e1 e2,
  (e_appv e1  e2) = (fill (appvCtxL e2 )  e1).
Proof.
  introv.
  eauto.
Qed.


Lemma fill_anno: forall e t l b ,
  (e_anno e l b t) = (fill (annoCtx l b t)  e).
Proof.
  introv.
  unfold fill; eauto.
Qed.

Lemma fill_appl: forall e1 e2 l b,
  (e_app e1 l b e2) = (fill (appCtxL e2 l b)  e1).
Proof.
  introv.
  unfold fill; eauto.
Qed.


Lemma fill_appr: forall e1 e2 l b,
  (e_app e1 l b e2) = (fill (appCtxR e1 l b)  e2).
Proof.
  introv.
  unfold fill; eauto.
Qed.


Lemma fill_appvr: forall e1 e2,
  (e_appv e1 e2) = (fill (appvCtxR e1)  e2).
Proof.
  introv.
  unfold fill; eauto.
Qed.


Lemma fill_prol: forall e1 e2,
  (e_pro e1  e2) = (fill (proCtxL e2 )  e1).
Proof.
  introv.
  eauto.
Qed.


Lemma fill_pror: forall e1 e2,
  (e_pro e1 e2) = (fill (proCtxR e1)  e2).
Proof.
  introv.
  unfold fill; eauto.
Qed.


Lemma fill_l: forall e1 l b,
  (e_l e1 l b) = (fill (lCtx l b)  e1).
Proof.
  introv.
  unfold fill; eauto.
Qed.


Lemma fill_r: forall e1 l b,
  (e_r e1 l b) = (fill (rCtx l b)  e1).
Proof.
  introv.
  unfold fill; eauto.
Qed.



Lemma smulti_rred_app : forall v t t' l b A B,
    (dynamic_type v) = (t_arrow A B) ->
     value v -> ssteps t  (e_exp t') -> ssteps (e_app v l b t) (e_exp (e_app v l b t')).
Proof.
  introv ty Val Red.
  inductions Red; eauto.
  rewrite fill_appr.
  rewrite fill_appr.
  apply sstep_refl.
  apply Step_eval;eauto.
  forwards*: IHRed.
  assert(wellformed (appCtxR v l b)). eauto.
  forwards*: Step_eval H1 H.
Qed.


Lemma smulti_bblame_app : forall v t l1 b1 l2 b2 A B,
(dynamic_type v) = (t_arrow A B) ->
    value v -> ssteps t (e_blame l1 b1) -> ssteps (e_app v l2 b2 t) (e_blame l1 b1).
Proof.
  introv ty Val Red.
  inductions Red; eauto.
  eapply sstep_nb.
  assert(wellformed (appCtxR v l2 b2)). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply sstep_b. 
  assert(wellformed (appCtxR v l2 b2 )). eauto.
  forwards*: Step_blame H0 H.
Qed.




Lemma smulti_bblame_appv : forall v t l1 b1,
    value v -> ssteps t (e_blame l1 b1) -> ssteps (e_appv v t) (e_blame l1 b1).
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply sstep_nb.
  assert(wellformed (appvCtxR v)). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply sstep_b. 
  assert(wellformed (appvCtxR v)). eauto.
  forwards*: Step_blame H0 H.
Qed.



Lemma smulti_rred_appv : forall v t t',
     value v -> ssteps t (e_exp t') -> ssteps (e_appv v t) (e_exp (e_appv v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  rewrite fill_appvr.
  rewrite fill_appvr.
  apply sstep_refl.
  apply Step_eval;eauto.
  assert(wellformed (appvCtxR v)). eauto.
  forwards*: Step_eval H0 H.
Qed.



Lemma smulti_rred_appv2 : forall t1 t2 t1' ,
    lc_exp t2 -> ssteps t1 (e_exp t1') -> ssteps (e_appv t1 t2) (e_exp (e_appv t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  rewrite fill_appv.
  rewrite fill_appv.
  apply sstep_refl.
  apply Step_eval;eauto.
  assert(wellformed (appvCtxL t2)). eauto.
  forwards*: Step_eval H0 H.
Qed.


Lemma smulti_bblame_appv2 : forall t1 t2 l1 b1,
    lc_exp t2 -> ssteps t1 (e_blame l1 b1) -> ssteps  (e_appv t1 t2) (e_blame l1 b1).
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply sstep_nb.
  assert(wellformed (appvCtxL t2 )). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply sstep_b. 
  assert(wellformed (appvCtxL t2)). eauto.
  forwards*: Step_blame H0 H.
Qed.



Lemma smulti_rred_app2 : forall t1 t2 t1' l b,
    lc_exp t2 -> ssteps t1 (e_exp t1') -> ssteps (e_app t1 l b t2) (e_exp (e_app t1' l b t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  rewrite fill_app.
  rewrite fill_app.
  apply sstep_refl.
  apply Step_eval;eauto.
  assert(wellformed (appCtxL t2 l b)). eauto.
  forwards*: Step_eval H0 H.
Qed.


Lemma smulti_bblame_app2 : forall t1 t2 l1 b1 l2 b2,
    lc_exp t2 -> ssteps t1 (e_blame l1 b1) -> ssteps (e_app t1 l2 b2 t2) (e_blame l1 b1).
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply sstep_nb.
  assert(wellformed (appCtxL t2 l2 b2 )). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply sstep_b. 
  assert(wellformed (appCtxL t2 l2 b2 )). eauto.
  forwards*: Step_blame H0 H.
Qed.

Lemma smulti_rred_anno : forall t t' A l b ,
ssteps t (e_exp t') -> ssteps (e_anno t l b A) (e_exp (e_anno t' l b A )).
Proof.
  introv Red.
  inductions Red; eauto.
  assert(wellformed (annoCtx l b A)). eauto.
  forwards*: Step_eval H0 H.
  assert(wellformed (annoCtx l b A)). eauto.
  forwards*: Step_eval H0 H.
Qed.

Lemma smulti_bblame_anno : forall t A l0 b0 l b,
    ssteps t (e_blame l b) -> ssteps (e_anno t l0 b0 A) (e_blame l b).
Proof.
  introv Red.
  inductions Red; eauto.
  eapply sstep_nb.
  assert(wellformed (annoCtx l0 b0 A)). eauto.
  forwards*: Step_eval H0 H.
  simpl. forwards*: IHRed.
  apply sstep_b. 
  assert(wellformed (annoCtx l0 b0 A)). eauto.
  forwards*: Step_blame H0 H.
Qed.


