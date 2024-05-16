Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               Infrastructure.

Require Import List. Import ListNotations.
Require Import Strings.String.


Lemma Typing_chk: forall G e A,
  Typing G e Inf A ->
  exists B, Typing G e Chk B.
Proof.
  introv Typ.
  inductions Typ; eauto.
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
  -
  forwards* h1: IHTyp1.
  inverts* h1.
  -
  forwards*: get_ty_well H.
  -
  forwards* h1: IHTyp.
  pick fresh y.
  forwards*: H0 y.
Qed.


(* Lemma Typing_chk2: forall G e A,
  Typing G e Chk A ->
  exists B, Typing G e Inf B.
Proof.
  introv Typ.
  inductions Typ; eauto.
Qed. *)

(* Check Mode *)
(* Lemma Typing_chk2inf: forall G v A,
    Typing G v Chk A -> exists B, Typing G v Inf B /\ sim B A.
Proof.
  intros G v A Typ.
  inductions Typ; try solve [inverts Val].
  exists.
  split*.
Qed. *)



(* Common Lemmas *)
Lemma Typing_regular_1 : forall e G dir A,
    Typing G e dir A -> lc_dexp e.
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
  assert (uniq ((y, A) :: G)) by auto.
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
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
    +
       pick fresh x and apply Typ_fix; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
    +
      pick fresh x and apply Typ_rt; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      simpl_env.
      solve_uniq.
Qed.

Lemma Typing_weakening : forall (E F : dctx) e dir T,
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
    Typing G e dir T -> fv_dexp e [<=] dom G.
Proof.
  intros G e dir T H.
  induction H; simpl; try fsetdec.
  - Case "Typing_var".
    apply binds_In in H0.
    fsetdec.
  - Case "Typing_abs".
    pick fresh x.
    assert (Fx : fv_dexp (e ^ x) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_dexp e [<=] fv_dexp (e ^ x)) by
        eapply fv_dexp_open_dexp_wrt_dexp_lower.
    fsetdec.
  -
    pick fresh x.
    assert (Fx : fv_dexp (e ^ x) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_dexp e [<=] fv_dexp (e ^ x)) by
        eapply fv_dexp_open_dexp_wrt_dexp_lower.
    fsetdec.
  -
    pick fresh x.
    assert (Fx : fv_dexp (e ^ x) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_dexp e [<=] fv_dexp (e ^ x)) by
        eapply fv_dexp_open_dexp_wrt_dexp_lower.
    fsetdec.
Qed.


Lemma value_no_fv : forall v dir T,
    Typing [] v dir T -> fv_dexp v [<=] empty.
Proof.
  intro v.
  pose proof (fv_in_dom [] v).
  intuition eauto.
Qed.

Lemma fvalue_no_fv : forall v dir T,
    Typing [] v dir T -> fv_dexp v [<=] empty.
Proof.
  intro v.
  pose proof (fv_in_dom [] v).
  intuition eauto.
Qed.


Lemma subst_value : forall v T dir z u,
    Typing [] v dir T -> subst_dexp u z v = v.
Proof.
  intros v dir T z u Typ.
  lets* Fv: value_no_fv Typ.
  forwards*: subst_dexp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.


Lemma subst_value2 : forall v z u,
    fv_dexp v [<=] empty -> subst_dexp u z v = v.
Proof.
  intros v z u Typ.
  forwards*: subst_dexp_fresh_eq.
  fsetdec.
Qed.



Lemma Typing_subst_1 : forall (E F : dctx) e u S dir T (z : atom),
    Typing (F ++ [(z,S)] ++ E) e dir T ->
    value u ->
    Typing E u Inf S ->
    Typing (F ++ E) ([z ~> u] e) dir T.
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'.
  generalize dependent F.
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : Typing_regular_1 H1;
    lets Uni : Typing_regular_2 H1.
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
    rewrite subst_dexp_open_dexp_wrt_dexp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H2.
  -
    pick fresh x and apply Typ_fix; eauto.
    rewrite subst_dexp_open_dexp_wrt_dexp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H2.
  -
    pick fresh x and apply Typ_rt; eauto.
    rewrite subst_dexp_open_dexp_wrt_dexp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H2.
Qed.



Lemma typing_subst_1 : forall (E F : dctx) e u S dir T (z : atom),
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
    rewrite subst_dexp_open_dexp_wrt_dexp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
  -
    pick fresh x and apply Typ_fix; eauto.
    rewrite subst_dexp_open_dexp_wrt_dexp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
  -
    pick fresh x and apply Typ_rt; eauto.
    rewrite subst_dexp_open_dexp_wrt_dexp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
Qed.

Lemma typing_c_subst_simpl : forall E e u S dir T z,
  Typing ([(z,S)] ++ E) e dir T ->
  Typing E u Inf S ->
  Typing E ([z ~> u] e) dir T.
Proof.
  intros E e u S dir T z H1 H2.
  rewrite_env (nil ++ E).
  eapply typing_subst_1; auto.
    simpl_env. apply H1.
    apply H2.
Qed.


Lemma get_ty_ityp: forall  t l t1,
 get_ty t l t1 ->
 ityp t l.
Proof.
  introv gt.
  inductions gt; eauto.
Qed.



Lemma get_ty_uniq: forall t l t1 t2,
 get_ty t l t1 ->
 get_ty t l t2 ->
 t1 = t2.
Proof.
  introv gt1 gt2. gen t2.
  inductions gt1; intros; try solve[inverts* gt2].
  - 
    inverts* gt2.
    forwards*: get_ty_ityp H5.
  -
    inverts* gt2.
    forwards*: get_ty_ityp gt1.
Qed.



Lemma proj_uniq: forall t t1 t2 l,
 proj t l t1 ->
 proj t l t2 ->
 t1 = t2.
Proof.
  introv pj1 pj2. gen t2.
  inductions pj1; intros; eauto.
  - 
    inductions pj2; eauto.
    forwards*: get_ty_uniq H H0.
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
    forwards * : IHTy1_1 H2.
    inverts* H.
  - (* t_and *)
    forwards * : IHTy1_1 H2.
    substs.
    forwards * : IHTy1_2 H4.
    substs*.
  - forwards * : IHTy1 H3.
    inverts* H0.
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
    forwards * : IHTy1_1 H2.
    inverts* H.
  - (* t_and *)
    forwards * : IHTy1_1 H2.
    substs.
    forwards * : IHTy1_2 H4.
    substs*.
  - (* t_proj *)
    forwards * : IHTy1 H3.
    subst.
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
