Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               Infrastructure.

Require Import List. Import ListNotations.
Require Import Strings.String.




Lemma sim_refl: forall A,
  sim A A.
Proof.
  introv.
  induction* A.
Qed.

Hint Resolve sim_refl: core.

Lemma Typing_chk2: forall G e A,
  Typing G e Inf A ->
  Typing G e Chk A.
Proof.
  introv Typ.
  inductions Typ; eauto; try solve[eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H0];
  try solve[eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H1];
  try solve[eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H];
  try solve[eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H2].
Qed.



Lemma etyping_Typing: forall G A e1 e2 dir,
 etyping G e1 dir A e2 ->
 Typing G e2 dir A.
Proof.
  introv typ.
  inductions typ; eauto.
Qed.



(* 
Lemma Typing_chk2: forall G e A,
  Typing G e Chk A ->
  exists B, Typing G e Inf B.
Proof.
  introv Typ.
  inductions Typ; eauto.
Qed. *)


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
    assert (Fx : fv_exp (open_exp_wrt_exp e (e_var_f x)) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_exp e [<=] fv_exp (open_exp_wrt_exp e (e_var_f x))) by
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

Lemma subst_value : forall v dir T z u,
    Typing [] v dir T -> subst_exp u z v = v.
Proof.
  intros v dir T z u Typ.
  lets* Fv: value_no_fv Typ.
  forwards*: subst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.



Lemma Typing_subst_1 : forall (E F : ctx) e u dir S T (z : atom),
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
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
Qed.

Lemma typing_c_subst_simpl : forall E e u dir S T z,
  Typing ([(z,S)] ++ E) e dir T ->
  Typing E u Inf S ->
  Typing E ([z ~> u] e) dir T.
Proof.
  intros E e u dir S T z H1.
  rewrite_env (nil ++ E).
  eapply Typing_subst_1.
    simpl_env. apply H1.
Qed.

Lemma principle_inf: forall v A,
  value v -> Typing nil v Inf A -> (dynamic_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
  inverts Typ as h01 h02; simpl in *.
  forwards* h1: IHVal1 h01.
  forwards* h2: IHVal2 h02.
  rewrite h1. rewrite h2.
  auto.
Qed.

Lemma pattern_uniq: forall A A1 A2,
 pattern A A1 ->
 pattern A A2 ->
 A1 = A2.
Proof.
  introv pa1 pa2.
  inductions pa1; try solve[inverts* pa2].
Qed.

Lemma pattern_pro_uniq: forall t1 t2 t3,
  pattern_pro t1 t2 ->
  pattern_pro t1 t3 ->
  t2 = t3.
Proof.
  introv pa1 pa2.
  inverts pa1; inverts* pa2.
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
    forwards * : IHTy1_1 H7.
    subst.
    forwards*: pattern_uniq H H4.
    inverts* H0.
  - (* t_app *)
    forwards * : IHTy1_1 H2.
    subst*.
    congruence.
    -
    forwards * h1: IHTy1_1 H2.
    inverts* h1.
    forwards * h2: IHTy1_2 H3.
    inverts* h2.
  -
    forwards * h1: IHTy1.
    inverts h1.
    forwards* h1: pattern_pro_uniq H H6.
    inverts* h1.
  -
    forwards * h1: IHTy1.
    inverts h1.
    forwards* h1: pattern_pro_uniq H H6.
    inverts* h1.
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
  forwards * : IHTy1_1 H7.
  subst.
  forwards*: pattern_uniq H H4.
  inverts* H0.
  - (* t_app *)
  forwards * : IHTy1_1 H2.
  subst.
  congruence.
  -
  forwards * h1: IHTy1_1 H2.
  inverts* h1.
  forwards * h2: IHTy1_2 H3.
  inverts* h2.
-
  forwards * h1: IHTy1.
  inverts h1.
  forwards* h1: pattern_pro_uniq H H6.
  inverts* h1.
-
  forwards * h1: IHTy1.
  inverts h1.
  forwards* h1: pattern_pro_uniq H H6.
  inverts* h1.
Qed.

Lemma Typing_c_rename2 : forall (x y : atom) E e T1 T2,
  x `notin` fv_exp e -> y `notin` (dom E `union` fv_exp e) ->
  Typing ((x , T1) :: E) (open_exp_wrt_exp e (e_var_f x)) Chk T2 ->
  Typing ((y , T1) :: E) (open_exp_wrt_exp e (e_var_f y)) Chk T2.
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
  destruct (x == y).
  Case "x = y".
    subst*; eauto.
  Case "x <> y".
    assert (J : uniq (((x , T1) :: E))).
      eapply Typing_regular_2; eauto.
    assert (J' : uniq E).
      inversion J; eauto.
    rewrite (@subst_exp_intro x); eauto.
    rewrite_env (nil ++ ((y , T1) :: E)).
    apply Typing_subst_1 with (S := T1).
    simpl_env.
    SCase "(open x s) is well-typed".
      apply Typing_weaken. eauto. auto.
    SCase "y is well-typed". eauto.
Qed.

Lemma Typing_chk: forall G e A,
  Typing G e Inf A ->
  exists B, Typing G e Chk B.
Proof.
  introv Typ.
  inductions Typ; eauto; try solve[exists; eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H0];
  try solve[exists; eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H1];
  try solve[exists; eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H];
  try solve[exists; eapply Typ_sim; eauto;unfold not; intros nt; inverts* nt; inverts* H2].
  (* pick fresh x.
  forwards*: H0 x.
  inverts* H1.
  exists(t_arrow t_dyn x0).
  eapply Typ_abs with (L := union L (union (dom G) (fv_exp e)));intros;eauto.
  forwards*: Typing_c_rename2 x1 H2. *)
Qed.


Lemma atyping_regular_1 : forall e e2 G dir A,
    atyping G e dir A e2 -> lc_exp e2.
Proof.
  introv H.
  inductions H;
    eauto.
Qed.

Lemma atyping_regular_1r : forall e e2 G dir A,
    atyping G e dir A e2 -> lc_exp e.
Proof.
  introv H.
  inductions H;
    eauto.
Qed.



Lemma atyping_inf : forall v v2 G A,
    value v -> atyping G v Inf A v2 -> dynamic_type v = A.
Proof.
  introv val H.
  inductions H;
    eauto; try solve[inverts val].
Qed.



Lemma atyping_inf2 : forall v v2 G A,
    value v2 -> atyping G v Inf A v2 -> dynamic_type v2 = A.
Proof.
  introv val H.
  inductions H;
    eauto; try solve[inverts val].
Qed.


Lemma atyping_weaken : forall G E F e dir T t,
    atyping (E ++ G) e dir T t ->
    uniq (E ++ F ++ G) ->
    atyping (E ++ F ++ G) e dir T t.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply atyp_abs; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.




Lemma atyping_weakening : forall (E F : ctx) e dir T t,
    atyping E e dir T t ->
    uniq (F ++ E) ->
    atyping (F ++ E) e dir T t.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ atyping_weaken.
Qed.


Lemma atyping_subst_1 : forall (E F : ctx) e u uu S T (z : atom) t,
    atyping (F ++ [(z,S)] ++ E) e Chk T t ->
    atyping E u Inf S uu ->
    atyping (F ++ E) ([z ~> u] e) Chk T ([z ~> uu] t).
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'. gen F .
  lets H': H. 
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : atyping_regular_1 H0;
    lets Uni : atyping_regular_1r H0.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ atyping_weakening. 
    solve_uniq.
  -
    pick fresh x and apply atyp_abs; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
Qed.



Lemma atyping_c_subst_simpl : forall E e u uu t  S T z,
  atyping ([(z,S)] ++ E) e Chk T t ->
  atyping E u Inf S uu ->
  atyping E ([z ~> u] e) Chk T ([z ~> uu] t).
Proof.
  intros E e u uu t S T z H1.
  rewrite_env (nil ++ E).
  eapply atyping_subst_1.
    simpl_env. apply H1.
Qed.


Lemma ainference_unique : forall G e e2 A1 A2,
    atyping G e Inf A1 e2 ->
    atyping G e Inf A2 e2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2.
  induction Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards*: binds_unique H0 H4.
  - (* t_app *)
  forwards * : IHTy1_1 H5.
  subst.
  inverts* H.
  - (* t_app *)
  forwards * : IHTy1_1 H9.
  subst.
  forwards*: pattern_uniq H H7.
  congruence.
Qed.