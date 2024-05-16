Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntaxb_ott
               rulesb_inf.

Require Import List. Import ListNotations.
Require Import Strings.String.

Notation "Γ ⊢ E A" := (Btyping Γ E A) (at level 45).
Notation "[ z ~> u ]' t" := (subst_term u z t) (at level 0).
Notation "t ^^' u"       := (open_term_wrt_term t u) (at level 67).

Notation "t ->* r" := (bsteps t r) (at level 68).


Lemma star_one:
forall a b, bstep a (t_term b) -> bsteps a (t_term b).
Proof.
eauto using bsteps.
Qed.

Lemma star_trans:
forall a b, bsteps a (t_term b) -> forall c, bsteps b (t_term c) -> bsteps a (t_term c).
Proof.
  introv H.
  inductions H; eauto using bsteps.
Qed.

Lemma star_transb:
forall a b l bb, bsteps a (t_term b) -> bsteps b (t_blame l bb) -> bsteps a (t_blame l bb).
Proof.
  introv H.
  inductions H; eauto using bsteps.
Qed.



Lemma sstar_one:
forall a b, bstep a (t_term b) -> bbsteps a (t_term b) 1.
Proof.
eauto using bsteps.
Qed.

Lemma sstar_trans:
forall a b n, bbsteps a (t_term b) n -> forall c m, bbsteps b (t_term c) m -> bbsteps a (t_term c) (n+m).
Proof.
  introv H.
  inductions H; eauto using bsteps.
  intros.
  forwards*: IHbbsteps H1.
  eapply bbstep_n ; eauto.
Qed.

Lemma sstar_transb:
forall a b l bb n m, bbsteps a (t_term b) n -> bbsteps b (t_blame l bb) m -> bbsteps a (t_blame l bb) (n+m).
Proof.
  introv H.
  inductions H; eauto using bsteps.
  intros.
  forwards*: IHbbsteps H1.
  eapply  bbstep_nb ; eauto.
Qed.

Hint Resolve  sstar_one sstar_trans sstar_transb star_one star_trans star_transb: core.

Definition birred e : Prop := forall b, ~(bstep e b).


Lemma UG_not_ground_0: forall A B,
 UG A B ->
 not(Ground A).
Proof.
  introv gr.
  inverts gr as h1 h2.
  inverts h2 as h3 h4.
  inverts h4 as h4 h5.
  unfold not;intros nt.
  inverts h3. 
  - 
    inverts* h1.
  -
    inverts* h1.
    inverts nt.
    apply h4; auto.
  -
    inverts* h1.
    inverts nt.
    apply h4; auto.
Qed.


Lemma bstep_not_value: forall (v:term),
    valueb v -> birred v.
Proof.
  introv.
  unfold birred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros;
  try solve[inverts* H;destruct E; unfold fillb in H0; inverts* H0];
  try solve[inverts* H;destruct E; unfold fillb in H0; inverts* H0;
  inverts* H3;destruct E; unfold fillb in H; inverts* H];
  try solve[inverts* H3;destruct E; unfold fillb in H; inverts* H].
  inverts* H; try solve[ destruct E; unfold fillb in H0; inverts* H0];
  try solve[inverts H4];
  try solve[inverts H6].
  forwards*: UG_not_ground_0 H8.
Qed.

Lemma valueb_lc : forall v,
    valueb v -> lc_term v.
Proof.
  intros v H.
  induction* H. 
Qed.


Lemma multi_red_app : forall v t t',
    valueb v -> t ->* (t_term t') -> (trm_app v t) ->* (t_term (trm_app v t')).
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformedb (appCtxRb v)). eauto.
  forwards*: Step_evalb H1 H.
Qed.

Lemma multi_blame_app : forall v t p b,
    valueb v -> t ->* (t_blame p b) -> (trm_app v t) ->* (t_blame p b ).
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply bstep_nb.
  assert(wellformedb (appCtxRb v)). eauto.
  forwards*: Step_evalb H0 H.
  simpl. forwards*: IHRed.
  apply bstep_b. 
  assert(wellformedb (appCtxRb v)). eauto.
  forwards*: Step_blameb H0 H.
Qed.

Lemma multi_red_app2 : forall t1 t2 t1',
    lc_term t2 -> t1 ->* (t_term t1') -> (trm_app t1 t2) ->* (t_term (trm_app t1' t2)).
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformedb (appCtxLb t2)). eauto.
  forwards*: Step_evalb H0 H.
Qed.


Lemma multi_blame_app2 : forall t1 t2 p b,
    lc_term t2 -> t1 ->* t_blame p b -> (trm_app t1 t2) ->* t_blame p b.
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply bstep_nb.
  assert(wellformedb (appCtxLb t2)). eauto.
  forwards*: Step_evalb H0 H.
  simpl. forwards*: IHRed.
  apply bstep_b. 
  assert(wellformedb (appCtxLb t2)). eauto.
  forwards*: Step_blameb H0 H.
Qed.

Lemma multi_red_cast : forall t t' A B p b,
    t ->* (t_term t') -> (trm_cast t A p b B) ->* (t_term (trm_cast t' A p b B)).
Proof.
  introv Red.
  inductions Red; eauto.
  assert(wellformedb (castCtxb A p b B)). eauto.
  forwards*: Step_evalb H0 H.
Qed.

Lemma multi_blame_cast : forall t A B p b p1 b1,
    t ->* t_blame p b -> (trm_cast t p1 b1 A B) ->* t_blame p b.
Proof.
  introv Red.
  inductions Red; eauto.
  eapply bstep_nb.
  assert(wellformedb (castCtxb p1 b1 A B)). eauto.
  forwards*: Step_evalb H0 H.
  simpl. forwards*: IHRed.
  apply bstep_b. 
  assert(wellformedb (castCtxb p1 b1 A B)). eauto.
  forwards*: Step_blameb H0 H.
Qed.

Lemma mmulti_red_app : forall v t t' n,
    valueb v -> bbsteps t (t_term t') n -> bbsteps (trm_app v t) (t_term (trm_app v t')) n.
Proof.
  introv Val Red.
  inductions Red; eauto.
  forwards*: IHRed.
  assert(wellformedb (appCtxRb v)). eauto.
  forwards*: Step_evalb H1 H.
Qed.

Lemma mmulti_blame_app : forall v t p b n ,
    valueb v ->  bbsteps t (t_blame p b) n ->  bbsteps (trm_app v t) (t_blame p b ) n.
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply bbstep_nb.
  assert(wellformedb (appCtxRb v)). eauto.
  forwards*: Step_evalb H0 H.
  simpl. forwards*: IHRed.
  apply bbstep_b. 
  assert(wellformedb (appCtxRb v)). eauto.
  forwards*: Step_blameb H0 H.
Qed.

Lemma mmulti_red_app2 : forall t1 t2 t1' n,
    lc_term t2 ->  bbsteps t1 (t_term t1') n ->  bbsteps (trm_app t1 t2) (t_term (trm_app t1' t2)) n.
Proof.
  introv Val Red.
  inductions Red; eauto.
  assert(wellformedb (appCtxLb t2)). eauto.
  forwards*: Step_evalb H0 H.
Qed.


Lemma mmulti_blame_app2 : forall t1 t2 p b n,
    lc_term t2 ->  bbsteps t1 (t_blame p b) n ->  bbsteps (trm_app t1 t2) (t_blame p b) n.
Proof.
  introv Val Red.
  inductions Red; eauto.
  eapply bbstep_nb.
  assert(wellformedb (appCtxLb t2)). eauto.
  forwards*: Step_evalb H0 H.
  simpl. forwards*: IHRed.
  apply bbstep_b. 
  assert(wellformedb (appCtxLb t2)). eauto.
  forwards*: Step_blameb H0 H.
Qed.

Lemma mmulti_red_cast : forall t t' A B p b n,
bbsteps t (t_term t') n ->  bbsteps (trm_cast t A p b B) (t_term (trm_cast t' A p b B)) n.
Proof.
  introv Red.
  inductions Red; eauto.
  assert(wellformedb (castCtxb A p b B)). eauto.
  forwards*: Step_evalb H0 H.
Qed.

Lemma mmulti_blame_cast : forall t A B p b p1 b1 n,
     bbsteps t (t_blame p b) n ->  bbsteps (trm_cast t p1 b1 A B) (t_blame p b) n.
Proof.
  introv Red.
  inductions Red; eauto.
  eapply bbstep_nb.
  assert(wellformedb (castCtxb p1 b1 A B)). eauto.
  forwards*: Step_evalb H0 H.
  simpl. forwards*: IHRed.
  apply bbstep_b. 
  assert(wellformedb (castCtxb p1 b1 A B)). eauto.
  forwards*: Step_blameb H0 H.
Qed.
