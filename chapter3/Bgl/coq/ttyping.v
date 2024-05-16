Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               rulesb_inf
               Typing_b
               Typing
               Infrastructure_b
               Infrastructure.

Require Import List. Import ListNotations.
Require Import Strings.String.




Lemma sim_refl: forall A,
  sim A A.
Proof.
  introv.
  induction* A.
Qed.


Lemma lc_trm_abs_exists2 :
forall x1 A1 t1 l b tt1 tt2,
  lc_term (open_term_wrt_term t1 (trm_var_f x1)) ->
  lc_term (trm_abs A1 (trm_cast t1 l b tt1 tt2)).
Proof.
intros; term_lc_exists_tac; eauto with lngen.
Qed.


Lemma lc_e_abs_exists2 :
forall x1 e1 l b tt1 t1,
  lc_exp (e_anno (open_exp_wrt_exp e1 (e_var_f x1)) l b tt1) ->
  lc_exp (e_abs t1 e1 l b tt1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
inverts* H0.
exp_lc_exists_tac; eauto with lngen.
Qed.




(* Common Lemmas *)
Lemma typing_regular_1 : forall e G dir A t,
    typing G e dir A t -> lc_exp e.
Proof.
  introv H.
  induction H;
    eauto.
Qed.


Lemma typing_regular_3 : forall e G dir A t,
    typing G e dir A t -> lc_term t.
Proof.
  introv H.
  induction H;
    eauto;
  pick fresh y;
  forwards*: H0 y;
  forwards*: lc_trm_abs_exists2 H2.
Qed.


Lemma btyping_regular_1 : forall e G A t,
    btyping G t A e -> lc_term t.
Proof.
  introv H.
  inductions H; eauto;
  pick fresh y;
  forwards*: H0 y;
  forwards*: lc_e_abs_exists2 H2.
Qed.


Lemma btyping_regular_3 : forall e G  A t,
    btyping G t A e -> lc_exp e.
Proof.
  introv H.
  inductions H; eauto;
  try solve[
  pick fresh y;
  forwards*: H0 y;
  forwards*: lc_e_abs_exists2 H1].
Qed.


Lemma typing_regular_2 : forall G e dir T t,
    typing G e dir T t -> uniq G.
Proof.
  intros. induction* H;
  try solve[  pick fresh y;
  assert (uniq ((y, A) :: G)) by auto;
  solve_uniq];
  try solve[
    pick fresh y;
  assert (uniq ((y, t_dyn) :: G)) by auto;
  solve_uniq
  ].
Qed.



Lemma btyping_regular_2 : forall G e T t,
    btyping G e T t -> uniq G.
Proof.
  intros. induction* H;
  try solve[  pick fresh y;
  assert (uniq ((y, A) :: G)) by auto;
  solve_uniq];
  try solve[
    pick fresh y;
  assert (uniq ((y, t_dyn) :: G)) by auto;
  solve_uniq
  ].
Qed.


Lemma typing_weaken : forall G E F e dir T t,
    typing (E ++ G) e dir T t ->
    uniq (E ++ F ++ G) ->
    typing (E ++ F ++ G) e dir T t.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply typ_abs; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.




Lemma typing_weakening : forall (E F : ctx) e dir T t,
    typing E e dir T t ->
    uniq (F ++ E) ->
    typing (F ++ E) e dir T t.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ typing_weaken.
Qed.



Lemma btyping_weaken : forall G E F e T t,
    btyping (E ++ G) e T t ->
    uniq (E ++ F ++ G) ->
    btyping (E ++ F ++ G) e T t.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply btyp_abs; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.




Lemma btyping_weakening : forall (E F : ctx) e T t,
    btyping E e T t ->
    uniq (F ++ E) ->
    btyping (F ++ E) e T t.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ btyping_weaken.
Qed.


(** Typing is preserved by substitution. *)
Lemma ttfv_in_dom2: forall G e dir T t,
    typing G e dir T t -> fv_exp e [<=] dom G.
Proof.
  introv H.
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


Lemma ttfv_in_domr2: forall G e dir T t,
    typing G e dir T t -> fv_term t [<=] dom G.
Proof.
  intros G e dir T t H.
  induction H; simpl; try fsetdec.
  - Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_term (open_term_wrt_term t (trm_var_f x)) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_term t [<=] fv_term (open_term_wrt_term t (trm_var_f x))) by
        eapply fv_term_open_term_wrt_term_lower.
    fsetdec.
Qed.



Lemma ttvalue_no_fv2 : forall v dir T t,
    typing [] v dir T t -> fv_exp v [<=] empty.
Proof.
  intro v.
  pose proof (ttfv_in_dom2 [] v).
  intuition eauto.
Qed.

Lemma ttsubst_value2 : forall v dir T t z u,
    typing [] v dir T t -> subst_exp u z v = v.
Proof.
  introv Typ.
  lets* Fv: ttvalue_no_fv2 Typ.
  forwards*: subst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.



Lemma ttvalue_no_fvr2 : forall v dir T t,
    typing [] v dir T t -> fv_term t [<=] empty.
Proof.
  intro v.
  pose proof (ttfv_in_domr2 []).
  intuition eauto.
Qed.

Lemma ttsubst_valuer : forall v dir T t z u,
    typing [] v dir T t -> subst_term u z t = t.
Proof.
  intros v dir T t z u Typ.
  lets* Fv: ttvalue_no_fvr2 Typ.
  forwards*: subst_term_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.




Lemma typing_subst_1 : forall (E F : ctx) e u uu S l1 b1 T (z : atom) t,
    typing (F ++ [(z,S)] ++ E) e (Chk3 l1 b1) T t ->
    typing E u Inf3 S uu ->
    typing (F ++ E) ([z ~> u] e) (Chk3 l1 b1) T ([z ~> uu]' t).
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'. gen F .
  lets H': H. 
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : typing_regular_1 H0;
    lets Uni : typing_regular_2 H0.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ typing_weakening. 
    solve_uniq.
  -
    pick fresh x and apply typ_abs; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite subst_term_open_term_wrt_term_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
    forwards*: typing_regular_3 H0.
Qed.



Lemma typing_c_subst_simpl : forall E e u uu t p b  S T z,
  typing ([(z,S)] ++ E) e (Chk3 p b) T t ->
  typing E u Inf3 S uu ->
  typing E ([z ~> u] e) (Chk3 p b) T ([z ~> uu]' t).
Proof.
  intros E e u uu t p b  S T z H1.
  rewrite_env (nil ++ E).
  eapply typing_subst_1.
    simpl_env. apply H1.
Qed.


Lemma btyping_subst_1 : forall (E F : ctx) e u uu S T (z : atom) t,
    btyping (F ++ [(z,S)] ++ E) e T t ->
    btyping E u S uu ->
    btyping (F ++ E) ([z ~> u]' e) T ([z ~> uu] t).
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'.
  generalize dependent F.
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : btyping_regular_1 H0;
    lets Lc2  : btyping_regular_3 H0;
    lets Uni : btyping_regular_2 H0.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ btyping_weakening.
    solve_uniq.
  -
    pick fresh x and apply btyp_abs; eauto.
    rewrite subst_term_open_term_wrt_term_var; auto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
Qed.

Lemma btyping_c_subst_simpl : forall E e u S T z t uu,
  btyping ([(z,S)] ++ E) e T t ->
  btyping E u S uu ->
  btyping E ([z ~> u]' e) T ([z ~> uu] t).
Proof.
  intros E e u S T z t uu H1 H2.
  rewrite_env (nil ++ E).
  eapply btyping_subst_1.
    simpl_env. apply H1.
    apply H2.
Qed.



Lemma ttinference_unique2 : forall G e t A1 A2,
    typing G e Inf3 A1 t ->
    typing G e Inf3 A2 t->
    A1 = A2.
Proof.
  introv Ty1.
  gen A2.
  inductions Ty1; introv Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards*: binds_unique H0 H4.
  - (* t_app *)
    forwards * : IHTy1_1 H5.
    inverts* H.
  - (* t_app *)
    inverts* Ty1_1. inverts* H.
  - (* t_app *)
    forwards * : IHTy1_1 H5.
    congruence.
  - (* t_app *)
    inverts H5. inverts* Ty1_1. 
Qed.

Lemma ttprinciple_inf: forall v A t,
  value v -> typing nil v Inf3 A t -> (dynamic_type v) = A .
Proof.  
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
Qed.


(* 
Definition Typing_elaboration G dir t A  := 
   match dir with 
    | Chk2 l b B => Btyping G t B 
    | _   => Btyping G t A
   end.


   Lemma typing_elaboration : forall G e t dir A,
   typing G e dir A t ->
   Typing_elaboration G dir t A.
Proof.
 introv Ty1. 
 inductions Ty1;unfold Typing_elaboration in *;  eauto.
 -
   pick fresh y and apply Btyp_abs;eauto.
   unfold open_term_wrt_term in *;simpl.
   eapply Btyp_cast.
   forwards*: H y.
   forwards*: H y.
   inverts* H2; try solve[apply sim_refl].
 -
   pick fresh y and apply Btyp_abs;eauto.
   unfold open_term_wrt_term in *;simpl.
   eapply Btyp_cast.
   forwards*: H0 y.
   inverts* H2; try solve[apply sim_refl].
   forwards*: H0 y.
   inverts* H2; try solve[apply sim_refl].
 -
   eapply Btyp_cast.
   pick fresh y and apply Btyp_abs;eauto.
   unfold open_term_wrt_term in *;simpl.
   eapply Btyp_cast; eauto.
   eauto.
 -
   eapply Btyp_cast.
   pick fresh y and apply Btyp_abs;eauto.
   unfold open_term_wrt_term in *;simpl.
   eapply Btyp_cast; eauto.
   forwards*: H0 y.
   inverts* H2.
   eauto.
 -
   pick fresh y and apply Btyp_abs;eauto.
   unfold open_term_wrt_term in *;simpl.
   eapply Btyp_cast; eauto.
 -
   pick fresh y and apply Btyp_abs;eauto.
   unfold open_term_wrt_term in *;simpl.
   eapply Btyp_cast; eauto.
   forwards*: H0 y.
   inverts* H2.
 -
   eapply Btyp_cast; eauto.
   inverts* Ty1.
 -
   inverts* Ty1.
   inverts* H8.
 (* -
   forwards*: Btyping_weakening G IHTy1_1.
   forwards*: Btyping_weakening G IHTy1_2.
   simpl_env in *; eauto. *)
Qed.
  *)



Lemma elaboration_soundness : forall G e t dir A,
    typing G e dir A t ->
    Btyping G t A.
Proof.
  introv Ty1.
  inductions Ty1; intros; eauto.
Qed.
 
Lemma btyping_typing: forall G e t A,
 btyping G t A e ->
 Typing G e Inf A.
Proof.
  introv typ.
  inductions typ;eauto.
  -
  pick fresh x and apply Typ_abs.
  forwards*: H0 x.
  inverts* H1.
Qed.



(****************************  ttyping   *****************************************)


Lemma ttyping_regular_1 : forall e G dir A t,
    ttyping G e dir A t -> lc_exp e.
Proof.
  introv H.
  induction H;
    eauto.
  inverts* IHttyping2.
  inverts* IHttyping2.
Qed.


Lemma ttyping_regular_3 : forall e G dir A t,
    ttyping G e dir A t -> lc_term t.
Proof.
  introv H.
  induction H;
    eauto.
  pick fresh y.
  forwards*: H0 y.
  forwards*: lc_trm_abs_exists2 H1.
Qed.

Lemma ttyping_regular_2 : forall G e dir T t,
    ttyping G e dir T t -> uniq G.
Proof.
  intros. induction* H.
  pick fresh y.
  assert (uniq ((y, A) :: G)) by auto.
  solve_uniq.
Qed.


Lemma ttyping_weaken : forall G E F e dir T t,
    ttyping (E ++ G) e dir T t ->
    uniq (E ++ F ++ G) ->
    ttyping (E ++ F ++ G) e dir T t.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply ttyp_abs; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.




Lemma ttyping_weakening : forall (E F : ctx) e dir T t,
    ttyping E e dir T t ->
    uniq (F ++ E) ->
    ttyping (F ++ E) e dir T t.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ ttyping_weaken.
Qed.



(** Typing is preserved by substitution. *)

Lemma ttfv_in_dom: forall G e dir T t,
    ttyping G e dir T t -> fv_exp e [<=] dom G.
Proof.
  introv H.
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


Lemma ttfv_in_domr: forall G e dir T t,
    ttyping G e dir T t -> fv_term t [<=] dom G.
Proof.
  intros G e dir T t H.
  induction H; simpl; try fsetdec.
  - Case "typing_var".
    apply binds_In in H0.
    fsetdec.
  - Case "typing_abs".
    pick fresh x.
    assert (Fx : fv_term (open_term_wrt_term t (trm_var_f x)) [<=] dom ([(x,A)] ++ G))
      by eauto.
    simpl in Fx.
    assert (Fy : fv_term t [<=] fv_term (open_term_wrt_term t (trm_var_f x))) by
        eapply fv_term_open_term_wrt_term_lower.
    fsetdec.
Qed.

Lemma ttvalue_no_fv : forall v dir T t,
    ttyping [] v dir T t -> fv_exp v [<=] empty.
Proof.
  intro v.
  pose proof (ttfv_in_dom [] v).
  intuition eauto.
Qed.


Lemma ttsubst_value : forall v dir T t z u,
    ttyping [] v dir T t -> subst_exp u z v = v.
Proof.
  introv Typ.
  lets* Fv: ttvalue_no_fv Typ.
  forwards*: subst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.



Lemma ttvalue_no_fvr : forall v dir T t,
    ttyping [] v dir T t -> fv_term t [<=] empty.
Proof.
  intro v.
  pose proof (ttfv_in_domr []).
  intuition eauto.
Qed.

Lemma ttsubst_valuer2 : forall v dir T t z u,
    ttyping [] v dir T t -> subst_term u z t = t.
Proof.
  intros v dir T t z u Typ.
  lets* Fv: ttvalue_no_fvr Typ.
  forwards*: subst_term_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.



Lemma ttyping_subst_1 : forall (E F : ctx) e u uu S l1 b1 T (z : atom) t tt,
    ttyping (F ++ [(z,S)] ++ E) e (Chk2 l1 b1 tt) T t ->
    ttyping E u Inf2 S uu ->
    ttyping (F ++ E) ([z ~> u] e) (Chk2 l1 b1 tt) T ([z ~> uu]' t).
Proof.
  intros.
  remember (F ++ [(z,S)] ++ E) as E'. gen F .
  lets H': H. 
  induction H; intros F Eq; subst; simpl; autos*;
    lets Lc  : ttyping_regular_1 H0;
    lets Uni : ttyping_regular_2 H0.
  -
    case_if*.
    substs.
    assert (A = S).
    eapply binds_mid_eq; eauto.
    substs.
    apply~ ttyping_weakening. 
    solve_uniq.
  -
    pick fresh x and apply ttyp_abs; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite subst_term_open_term_wrt_term_var; auto.
    rewrite_env (([(x, A)] ++ F) ++ E).
    apply~ H1.
    forwards*: ttyping_regular_3 H0.
Qed.


Lemma ttyping_c_subst_simpl : forall E e u uu t p b  S T z tt,
  ttyping ([(z,S)] ++ E) e (Chk2 p b tt) T t ->
  ttyping E u Inf2 S uu ->
  ttyping E ([z ~> u] e) (Chk2 p b tt) T ([z ~> uu]' t).
Proof.
  intros E e u uu t p b  S T z tt H1.
  rewrite_env (nil ++ E).
  eapply ttyping_subst_1.
    simpl_env. apply H1.
Qed.


Lemma ttinference_unique : forall G e t A1 A2,
    ttyping G e Inf2 A1 t ->
    ttyping G e Inf2 A2 t->
    A1 = A2.
Proof.
  introv Ty1.
  gen A2.
  inductions Ty1; introv Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards*: binds_unique H0 H4.
  - (* t_app *)
    forwards * : IHTy1_1 H5.
    inverts* H.
  - (* t_app *)
    inverts* Ty1_1. 
  -
    inverts* H5. 
  - (* t_app *)
    forwards * : IHTy1_1 H5.
    inverts* H.
Qed.


Lemma tprinciple_inf: forall v A t,
  value v -> ttyping nil v Inf2 A t -> (dynamic_type v) = A .
Proof.
  introv Val Typ.
  gen A.
  induction Val; introv  Typ; try solve [inverts* Typ].
Qed.

  

(**************** ttyping sound and complete *************)

Definition ttyping_btyping_aux G dir t A  := 
   match dir with 
    | Chk2 l b B => Btyping G t B 
    | _   => Btyping G t A
   end.


Lemma ttyping_bc : forall G e t dir A,
    ttyping G e dir A t ->
    ttyping_btyping_aux G dir t A.
Proof.
  introv Ty1. 
  inductions Ty1;unfold  ttyping_btyping_aux in *;  eauto.
  -
    pick fresh y and apply Btyp_abs;eauto.
    unfold open_term_wrt_term in *;simpl.
    eapply Btyp_cast.
    forwards*: H y.
    forwards*: H y.
    inverts* H1; try solve[apply sim_refl].
  -
    eapply Btyp_cast; eauto.
    inverts* Ty1.
Qed.
  


Definition ttyping_typing_aux G dir e A  := 
   match dir with 
    | Chk2 l b B => Typing G e Chk A 
    | _   => Typing G e Inf A
   end.

Lemma ttyping_typing: forall G dir e  A t,
 ttyping G e dir A t ->
 ttyping_typing_aux G dir e A.
Proof.
  introv typ.
  inductions typ; unfold  ttyping_typing_aux in *; intros; eauto.
  eapply Typ_app; eauto.
  inverts* IHtyp2.
  eapply Typ_app; eauto.
  inverts* IHtyp2.
Qed.
