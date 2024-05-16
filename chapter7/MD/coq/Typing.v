Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               Infrastructure
               Subtyping_inversion.

Require Import List. Import ListNotations.
Require Import Strings.String.


Lemma Typing_chk: forall G e A,
  Typing G e Inf A ->
  exists B, Typing G e Chk B.
Proof.
  introv Typ.
  inductions Typ; eauto.
Qed.



Lemma dmatch_well: forall A B,
 well A ->
 dmatch A B ->
 well B.
Proof.
  introv well pat.
  inductions pat; eauto.
Qed.


Lemma get_ty_well: forall A l B,
 well A ->
 get_ty A l B ->
 well B.
Proof.
  introv well gt.
  inductions gt; try solve[inverts* well]; eauto.
Qed.



Lemma Typing_well: forall G e A dir,
 WF G -> Typing G e dir A -> well A.
Proof.
  introv wf Typ.
  inductions Typ; eauto.
  -
    inductions wf; eauto; 
    try solve[inverts* H0].
    inverts H1 as h1.
    +
    inverts* h1.
    +
    inverts H0.
    forwards*: IHwf.
  -
  pick fresh x.
  forwards*: H0 x.
  inverts* H2.
  -
  forwards* h1: IHTyp1.
  forwards* h2: dmatch_well H.
  inverts* h2.
  -
  forwards*: get_ty_well H.
  -
    forwards* h1: IHTyp.
    pick fresh y.
    forwards*: H0 y.
Qed.

Lemma Typing_Chk: forall G e A,
  WF G ->
  Typing G e Inf A ->
  Typing G e Chk A.
Proof.
  introv wf Typ.
  forwards*: Typing_well Typ.
  eapply Typ_cs;eauto.
  eapply csub_reflexivity.
Qed.

(* Common Lemmas *)
Lemma Typing_regular_1 : forall e G dir A,
    Typing G e dir A -> lc_exp e.
Proof.
  intros e G dir A H.
  inductions H;
    eauto.
Qed.

Lemma Typing_regular_2 : forall G e dir T,
    Typing G e dir T -> uniq G.
Proof.
  intros. induction* H.
  pick fresh y.
  assert (uniq ((y, A1) :: G)) by auto.
  solve_uniq.
  pick fresh y.
  assert (uniq ((y, A) :: G)) by auto.
  solve_uniq.
Qed.


Lemma Typing_weaken : forall G E F e dir T,
    Typing (E ++ G) e dir T ->
    uniq (E ++ F ++ G) ->
    Typing (E ++ F ++ G) e dir T.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply Typ_abs; eauto.
      rewrite_env (([(x, A1)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
    + (* abs *)
      pick fresh x and apply Typ_fix; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
    + (* abs *)
      pick fresh x and apply Typ_rt; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      simpl_env.
      solve_uniq.
Qed.

Lemma Typing_weakening : forall (E F : ctx) e dir T,
    Typing E e dir T ->
    uniq (F ++ E) ->
    Typing (F ++ E) e dir T.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ Typing_weaken.
Qed.


(** Typing is preserved by substitution. *)

Lemma fv_in_dom: forall G e dir T,
    Typing G e dir T -> fv_exp e [<=] dom G.
Proof.
  intros G e dir T H.
  induction H; simpl; try fsetdec.
  - Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,A1)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
  -
    pick fresh x.
    assert (Fx : fv_exp (e ^ x) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (e ^ x)) by
        eapply fv_exp_open_exp_wrt_exp_lower.
    fsetdec.
Qed.

Lemma value_no_fv : forall v dir T,
    Typing [] v dir T -> fv_exp v [<=] empty.
Proof.
  intro v.
  pose proof (fv_in_dom [] v).
  intuition eauto.
Qed.

Lemma fvalue_no_fv : forall v dir T,
    Typing [] v dir T -> fv_exp v [<=] empty.
Proof.
  intro v.
  pose proof (fv_in_dom [] v).
  intuition eauto.
Qed.


Lemma subst_value : forall v T dir z u,
    Typing [] v dir T -> subst_exp u z v = v.
Proof.
  intros v dir T z u Typ.
  lets* Fv: value_no_fv Typ.
  forwards*: subst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.

Lemma subst_fvalue : forall v T dir z u,
    Typing [] v dir T -> subst_exp u z v = v.
Proof.
  intros v dir T z u Typ.
  lets* Fv: fvalue_no_fv Typ.
  forwards*: subst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.



Lemma Typing_subst_1 : forall (E F : ctx) e u S dir T (z : atom),
    Typing (F ++ [(z,S)] ++ E) e dir T ->
    Typing E u Inf S ->
    Typing (F ++ E) ([z ~> u] e) dir T.
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'.
  generalize dependent F.
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : Typing_regular_1 H0;
    lets Uni : Typing_regular_2 H0.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ Typing_weakening.
    solve_uniq.
  -
    pick fresh x and apply Typ_abs; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, A1)] ++ F) ++ E).
    apply~ H1.
  -
    pick fresh x and apply Typ_fix; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
  -
    pick fresh x and apply Typ_rt; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
  (* -
   lets : ((subst_value _ _ _ z u) H1).
   rewrite H2;eauto.
  - 
    lets : ((subst_value _ _ _ z u) H1).
    lets : ((subst_value _ _ _ z u) H2).
    rewrite H5.
    rewrite H4;eauto.
  - lets : ((subst_value _ _ _ z u) H1).
     rewrite H3;eauto.
  - 
    lets : ((subst_value _ _ _ z u) H1).
    rewrite H3;eauto. *)
Qed.


Lemma typing_c_subst_simpl : forall E e u S dir T z,
  Typing ([(z,S)] ++ E) e dir T ->
  Typing E u Inf S ->
  Typing E ([z ~> u] e) dir T.
Proof.
  intros E e u S dir T z H1 H2.
  rewrite_env (nil ++ E).
  eapply Typing_subst_1.
    simpl_env. apply H1.
    apply H2.
Qed.


Lemma get_ty_ityp: forall  t l t1,
 get_ty t l t1 ->
 not(dynamic t) ->
 ityp t l.
Proof.
  introv gt dyn.
  inductions gt; eauto.
  exfalso; apply dyn; auto.
Qed.



Lemma get_ty_uniq: forall t l t1 t2,
 get_ty t l t1 ->
 get_ty t l t2 ->
 t1 = t2.
Proof.
  introv gt1 gt2. gen t2.
  inductions gt1; intros; try solve[inverts* gt2];
  try solve[inverts* gt2;inverts* H0].
  - 
    inverts* gt2.
    exfalso; apply H1; eauto.
  -
    inverts* gt2.
    exfalso; apply H1; eauto.
  -
    inverts* gt2; try solve[inverts* H0];
    try solve[exfalso; apply H; eauto].
  (* -
    inverts* gt2; try solve[inverts* H0];
    try solve[exfalso; apply H1; eauto].
    forwards*: IHgt1_1 H5.
    forwards*: IHgt1_2 H8.
    congruence. *)
Qed.


Lemma dmatch_uniq: forall A B1 B2,
 dmatch A B1 ->
 dmatch A B2 ->
 B1 = B2.
Proof.
  introv ma1 ma2. 
  inductions A; try solve[inverts* ma1; inverts* ma2].
Qed.



(* stronger than inf unique *)
Lemma Typing_strenthening : forall G e A1 A2,
    []  ⊢ e ⇒ A1 ->
    G ⊢ e ⇒ A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2 G.
  inductions Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    inverts H0.
  - (* t_app *)
    forwards * h2: IHTy1_1 H2.
    inverts* h2.
    forwards* h1: dmatch_uniq H H5.
    inverts* h1.
  - (* t_and *)
    forwards * : IHTy1_1 H2.
    substs.
    forwards * : IHTy1_2 H4.
    substs*.
  - (* t_rcd *)
    forwards*: IHTy1 H3.
    inverts H0; auto.
    forwards*: get_ty_uniq H H4.
  - (* t_proj *)
    forwards * : IHTy1 H1.
    inverts* H.
Qed.



Lemma inference_unique : forall G e A1 A2,
    Typing G e Inf A1 ->
    Typing G e Inf A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2.
  induction Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards*: binds_unique H0 H4.
  - (* t_app *)
    forwards * h1: IHTy1_1 H2.
    inverts* h1.
    forwards* h2: dmatch_uniq H H5.
    inverts* h2.
  - (* t_and *)
    forwards * : IHTy1_1 H2.
    substs.
    forwards * : IHTy1_2 H4.
    substs*.
  - (* t_rcd *)
    forwards*: IHTy1 H3.
    inverts H0; auto.
    forwards*: get_ty_uniq H H4.
  - (* t_proj *)
    forwards * : IHTy1 H1.
    inverts* H.
Qed.

Lemma fprincipal_inf: forall p A,
  fvalue p -> Typing nil p Inf A -> (principal_type p) = A .
Proof.
  introv Val Typ.
  gen A.
  inductions Val; introv  Typ; try solve [inverts* Typ];simpl in *.
Qed.



Lemma principal_inf: forall A v,
 value v -> Typing nil v Inf A -> principal_type v = A.
Proof.
  introv Val Typ. gen A.
  inductions Val; introv Typ; try solve [inverts* Typ];simpl in *.
  -
    forwards*: fprincipal_inf Typ.
  - 
    inverts Typ as h1 h2 h3.
    forwards* h4: IHVal1 h1.
    forwards* h5: IHVal2 h2.
    rewrite h4 in *.
    rewrite h5 in *.
    auto.
  -
    inverts Typ as h1.
    forwards* h2: IHVal h1.
    rewrite h2 in *.
    auto.
Qed.
