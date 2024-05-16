Require Export Metalib.Metatheory.
Require Import LibTactics.
Require Import Definitions.
Require Import String.
Require Import Lia.

Require Import Infrastructure.
Require Import rules_inf.


(* ********************************************************************** *)
(**  Properties of [wf_typ] *)


Lemma type_from_wf_typ : forall E T,
  wf_typ E T -> type T.
Proof.
  introv H; induction H; eauto.
Qed.


Hint Resolve type_from_wf_typ:core.


Lemma wf_typ_weakening : forall T E F G,
  wf_typ (G ++ E) T ->
  uniq (G ++ F ++ E) ->
  wf_typ (G ++ F ++ E) T.
Proof with simpl_env; eauto.
  intros T E F G Hwf_typ Hk.
  remember (G ++ E) as F'.
  generalize dependent G.
  induction Hwf_typ; intros G Hok Heq; subst...
  Case "type_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H0...
Qed.


Lemma wf_typ_weaken_head : forall T E F,
  wf_typ E T ->
  uniq (F ++ E) ->
  wf_typ (F ++ E) T.
Proof.
  intros.
  rewrite_env (empty ++ F++ E).
  auto using wf_typ_weakening.
Qed.


Lemma wf_typ_strengthening : forall E F x U T,
 wf_typ (F ++ x ~ bind_typ U ++ E) T ->
 wf_typ (F ++ E) T.
Proof with simpl_env; eauto.
  intros E F x U T H.
  remember (F ++ x ~ bind_typ U ++ E) as G.
  generalize dependent F.
  induction H; intros F Heq; subst...
  Case "wf_typ_var".
    analyze_binds H...
  Case "wf_typ_all".
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply H0...
Qed.


Lemma notin_fv_tt_open_inv : forall X T U k,
  X `notin` fv_tt T ->
  X `notin` fv_tt U ->
  X `notin` fv_tt (open_tt_rec k U T).
Proof.
  introv notint notinu. gen k.
  inductions T; intros; simpl in *; eauto.
  destruct(lt_eq_lt_dec n k);eauto.
  destruct s; eauto.
Qed.


Lemma wf_typ_strengthening_1 : forall E F x v T,
 wf_typ (F ++ x ~ v ++ E) T ->
 x `notin` fv_tt T ->
 wf_typ (F ++ E) T.
Proof.
  introv wf1 notin.
  inductions wf1; try(constructor~); simpls~.
  -
    apply binds_remove_mid in H; auto.
  -
     apply~ IHwf1_1.
  -
     apply~ IHwf1_2.
  -
    pick fresh Y and apply wf_typ_all...
    rewrite <- app_assoc.
    apply* H0;eauto.
    apply* notin_fv_tt_open_inv.
  -  apply~ IHwf1.
Qed.


Lemma wf_typ_subst_tb : forall F E Z P T,
  wf_typ (F ++ Z ~tvar  ++ E) T ->
  wf_typ E P ->
  uniq (map (subst_tb Z P) F ++ E) ->
  wf_typ (map (subst_tb Z P) F ++ E) (subst_tt P Z T).
Proof with simpl_env; eauto using wf_typ_weaken_head, type_from_wf_typ.
  introv WT WP.
  remember (F ++ Z ~tvar ++ E) as G.
  generalize dependent F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt...
  -
    destruct (x == Z); subst...
    analyze_binds H.
    apply* wf_typ_var.
    assert (bind_tvar = subst_tb Z P bind_tvar).
    reflexivity. rewrite H.
    assert(binds x (subst_tb Z P bind_tvar) (map (subst_tb Z P) F)).
    forwards: binds_map_2 BindsTac.
    apply H0.
    forwards: binds_app_2 H0.
    apply H1.
  -
    pick fresh Y and apply wf_typ_all...
    rewrite tsubst_typ_open_typ_wrt_typ_var...
    rewrite_env (map (subst_tb Z P) (Y ~tvar ++ F) ++ E).
    apply H0 ...
Qed.


Lemma wf_typ_open : forall E U T2,
  uniq E ->
  wf_typ E (t_all T2) ->
  wf_typ E U ->
  wf_typ E (open_tt T2 U).
Proof with simpl_env; eauto.
  introv Ok WA WU.
  inverts* WA.
  pick fresh X.
  rewrite ( tsubst_typ_intro X)...
  rewrite_env (map (subst_tb X U) empty ++ E).
  eapply wf_typ_subst_tb...
Qed.


(* ********************************************************************** *)
(** Properties of [wf_env] and [wf_typ] *)

Lemma uniq_from_wf_env : forall E,
  wf_env E ->
  uniq E.
Proof.
  intros E H; induction H; auto.
Qed.

Hint Resolve uniq_from_wf_env : core.


Lemma wf_typ_from_binds_typ : forall x U E,
  wf_env E ->
  binds x (bind_typ U) E ->
  wf_typ E U.
Proof with auto using wf_typ_weaken_head.
  induction 1; intros J; analyze_binds J...
  injection BindsTacVal; intros; subst...
Qed.


Lemma wf_typ_from_wf_env_typ : forall x T E,
  wf_env (x ~ bind_typ T ++ E) ->
  wf_typ E T.
Proof.
  intros x T E H. inversion H; auto.
Qed.


(* ********************************************************************** *)
(** Properties of [wf_env] *)


Lemma wf_env_inv : forall E x T,
  wf_env (x ~ T ++ E) -> wf_env E /\  x `notin` dom E.
Proof.
  introv O. inverts* O.
Qed.


Lemma wf_env_strengthening : forall x T E F,
  wf_env (F ++ x ~ bind_typ T ++ E) ->
  wf_env (F ++ E).
Proof with eauto using wf_typ_strengthening.
  induction F; intros Wf_env; inversion Wf_env; subst; simpl_env in *...
Qed.



Lemma wf_env_subst_tb : forall x T E F,
  wf_env (F ++ x ~tvar ++ E) ->
  wf_typ E T ->
  wf_env (map (subst_tb x T) F ++ E).
Proof with eauto using wf_typ_subst_tb.
inductions F; intros Wf_env WP; simpl_env;
    inversion Wf_env; simpl_env in *; simpl subst_tb...
  rewrite <- H in Wf_env.
  applys~ wf_env_typ.
  applys* wf_typ_subst_tb.
Qed.

Lemma notin_fv_tt_open : forall (Y X : atom) T,
  X `notin` fv_tt (open_tt T Y) ->
  X `notin` fv_tt T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros k Fr; eauto.
Qed.

Lemma notin_fv_wf : forall E (X : atom) T,
  wf_typ E T ->
  X `notin` dom E ->
  X `notin` fv_tt T.
Proof with auto.
  intros E X T Wf_typ.
  induction Wf_typ; intros Fr; simpl...
  Case "wf_typ_var".
    assert (x `in` (dom E))...
    eapply binds_In; eauto.
    assert (X <> x) by fsetdec. fsetdec.
  Case "wf_typ_all".
    pick fresh Y.
    apply (notin_fv_tt_open Y)...
Qed.


Lemma map_subst_tb_id : forall G Z P,
  wf_env G ->
  Z `notin` dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros G Z P H.
  induction H; simpl; intros Fr; simpl_env...
  -
  rewrite <- IHwf_env...
  -
  rewrite <- IHwf_env...
  rewrite tsubst_typ_fresh_eq... eapply notin_fv_wf; eauto.
Qed.


Lemma wf_env_concat_left_inv: forall E F,
    wf_env (F ++ E) -> wf_env E.
Proof.
  induction F; introv okt; auto.
  apply* IHF.
  destruct~ a.
  inverts* okt.
Qed.




(* ********************************************************************** *)
(** ** consistent *)

Lemma consist_weakening : forall E F G S T,
  consist (G ++ E) S T ->
  wf_env (G ++ F ++ E) ->
  consist (G ++ F ++ E) S T.
Proof with simpl_env; auto using wf_typ_weakening.
  intros E F G S T Sub Ok.
  remember (G ++ E) as H.
  generalize dependent G.
  induction Sub; intros G Ok EQ; subst...
  -
    pick fresh Y and apply consist_all...
    rewrite <- app_assoc.
    apply H0...
Qed.


Lemma notin_decidable: forall a E,
 wf_env E ->
 a `notin` dom E \/ not(a `notin` dom E).
Proof.
  introv wf.
  inductions E; eauto.
  inverts* wf.
  -
  forwards*: IHE H1. inverts* H.
  destruct(a == x); try solve[left*].
  + inverts e. 
    right.
    simpl. 
    unfold not; intros nt.
    apply nt; eauto.
  -
  forwards*: IHE H1. inverts* H.
  destruct(a == x); try solve[left*].
  + inverts e. 
    right.
    simpl. 
    unfold not; intros nt.
    apply nt; eauto.
Qed.


Lemma consist_refl: forall E A,
 wf_env E ->
 wf_typ E A ->
 consist E A A.
Proof.
 introv ok wft.
 inductions wft; eauto.
 pick fresh y and apply consist_all; eauto.
Qed.


Lemma consist_sym: forall E A B,
 consist E A B ->
 consist E B A.
Proof.
 introv wft.
 inductions wft; eauto.
Qed.


Lemma consist_through_subst_tt : forall E F Y S T A,
  consist (F ++ Y ~tvar ++ E) S T ->
  wf_typ E A ->
  consist (map (subst_tb Y A) F ++ E) (subst_tt A Y  S) (subst_tt A Y  T).
Proof with simpl_env;
     eauto 4 using wf_typ_subst_tb, wf_env_subst_tb, wf_typ_weaken_head.
  introv SsubT PsubQ.
  remember (F ++ Y ~tvar ++ E) as G.
  generalize dependent F.
  induction SsubT; intros G EQ; subst; simpl subst_tt...
  -
    destruct (x == Y); subst.
    apply consist_refl...
    apply consist_refl...
    inverts* H0.
    analyze_binds H3...
    apply* wf_typ_var.
    assert (bind_tvar = subst_tb Y A bind_tvar).
    reflexivity. rewrite H0.
    assert(binds x (subst_tb Y A bind_tvar) (map (subst_tb Y A) G)).
    forwards: binds_map_2 BindsTac.
    apply H1.
    forwards: binds_app_2 H1.
    apply H2.
  -
    apply consist_dyn_l...
  -
    apply consist_dyn_r...
  -
    pick fresh X and apply consist_all...
    rewrite tsubst_typ_open_typ_wrt_typ_var...
    rewrite tsubst_typ_open_typ_wrt_typ_var...
    rewrite_env (map (subst_tb Y A) (X ~tvar ++ G) ++ E).
    apply H0...
Qed.


Lemma consist_subst_simpl : forall E Y S T A,
  consist (Y ~tvar ++ E) S T ->
  wf_typ E A ->
  consist (E) (subst_tt A Y S) (subst_tt A Y T).
Proof.
  introv con type.
  rewrite_env (map (subst_tb Y A) empty ++E).
  apply* consist_through_subst_tt.
Qed.


Lemma wf_typ_rename : forall E F z u A,
    wf_typ (E ++ z ~tvar ++ F) A ->
    wf_env (E ++ u ~tvar ++ F) ->
    wf_typ (E ++ u ~tvar ++ F) (subst_tt  (t_fvar u) z A).
Proof.
  introv wf okt.
  inductions wf; simpls; auto.
  -
    destruct(x == z); try solve[inverts* e].
    forwards*: binds_remove_mid H.
    apply wf_typ_var.
    forwards*: binds_weaken H0.
    simpl_env.
    apply H1.
  - 
    pick fresh x and apply wf_typ_all.
    forwards ~ : H0 x (x ~tvar ++ E) F z.
    simpl_env in *.
    apply wf_env_tvar; eauto.
    rewrite <- tsubst_typ_open_typ_wrt_typ_var in H1; auto.
Qed.


Lemma consist_subst : forall F E A B z u,
    consist (E ++ z ~tvar ++ F) A B ->
    wf_env (E ++ u ~tvar ++ F) ->
    consist (E ++ u ~tvar ++ F) (subst_tt  (t_fvar u) z A)
                           (subst_tt (t_fvar u) z B)
.
Proof.
  introv typt. inductions typt; introv okt; simpl; f_equal~.
  -
    destruct(x == z);eauto.
    apply consist_var;eauto.
    forwards*: uniq_from_wf_env H.
    forwards*: wf_typ_strengthening_1 H0.
    forwards*: uniq_from_wf_env okt.
    forwards*: wf_typ_weakening H2 H3.
  -
    forwards*: wf_typ_rename H0 okt.
  - 
    forwards*: wf_typ_rename H0 okt.
  -
    forwards*: IHtypt1 okt.
    forwards*: IHtypt2 okt.
  -
    pick fresh x and apply consist_all.
    forwards ~ : H0 x F (x ~tvar ++ E) z. 
    simpl.
    apply wf_env_tvar;eauto.
    simpl in H1.
    rewrite_env((x, bind_tvar) :: E ++ (u, bind_tvar) :: F).
    rewrite~ tsubst_typ_open_typ_wrt_typ_var.
    assert((subst_tt u z  B open_tt_var x) =
    (subst_tt u z  (B open_tt_var x))).
    rewrite~ tsubst_typ_open_typ_wrt_typ_var.
    rewrite H2;eauto.
  -
    forwards*: IHtypt okt.
Qed.

Lemma consist_regular : forall E A B,
  consist E A B -> wf_env E /\ wf_typ E A /\ wf_typ E B.
Proof with simpl_env; try solve [auto | intuition auto].
  introv H.
  induction H...
  -
  repeat split...
  +
    pick fresh x.
    forwards*: H0 x.
    destructs~ H1.
    forwards*: wf_env_inv H1.
  +
      pick fresh Y and apply wf_typ_all...
      destruct (H0 Y)...
  +
      pick fresh Y and apply wf_typ_all...
      destruct (H0 Y)...
Qed.


Lemma consist_rename : forall E x y A B,
  consist (x ~tvar ++ E) (A open_tt_var x) (B open_tt_var x) ->
  x \notin dom E \u fv_tt A \u fv_tt B ->
  y \notin dom E \u fv_tt A \u fv_tt B ->
  consist (y ~tvar ++ E) (A open_tt_var y) (B open_tt_var y)
.
Proof.
  introv Typx Frx Fry.
  destruct(x == y). substs*.
  rewrite~ (@tsubst_typ_intro x).
  assert 
  ((B open_tt_var y) =
  subst_tt y x  (B open_tt_var x)).
  rewrite~ (@tsubst_typ_intro x); auto.
  rewrite H.
  rewrite_env (empty ++ x ~tvar ++ E) in Typx.
  rewrite_env (empty ++ y ~tvar ++ E).
  assert(wf_env (empty ++ y ~tvar ++ E)).
  simpl.
  forwards*: consist_regular Typx.
  destruct H0. inverts* H0. 
  apply wf_env_tvar;eauto.
  forwards*: consist_subst Typx H0.
Qed.


Lemma consist_decidable : forall E A B,
  wf_env E ->
  wf_typ E A ->
  wf_typ E B ->
  (consist E A B \/ not(consist E A B)) /\ (consist E B A \/ not(consist E B A)).
Proof.
  introv wf wt1 wt2. gen B.
  inductions wt1; intros;eauto; 
  try solve[split*].
  -
    inductions wt2; try solve[
      split; right; unfold not;intros nt;
      inverts* nt
    ];
    try solve[split*;left*].
  -
     inductions wt2; try solve[
      split; right; unfold not;intros nt;
      inverts* nt
    ];
    try solve[split*;left*].
  - 
    inductions wt2; try solve[
      split; right; unfold not;intros nt;
      inverts* nt
    ];
    try solve[split*;left*].
    destruct(x == x0);try solve[inverts* e; split*].
    try solve[
      split; right; unfold not;intros nt;
      inverts* nt
    ].
  -
    inductions wt2; try solve[
     split; right; unfold not;intros nt;
     inverts* nt
   ];
   try solve[split*;left*].
   clear IHwt2_1 IHwt2_2.
   forwards*: IHwt1_1 wt2_1.
   forwards*: IHwt1_2 wt2_2.
   inverts H. inverts H0.
   split.
   inverts* H2; try solve[
    right; unfold not;intros nt;
    inverts* nt
    ];
    try solve[split*;left*].
    inverts* H; try solve[
    right; unfold not;intros nt;
    inverts* nt
    ];
    try solve[split*;left*].
    inverts* H1; try solve[
    right; unfold not;intros nt;
    inverts* nt
    ];
    try solve[split*;left*].
    inverts* H3; try solve[
    right; unfold not;intros nt;
    inverts* nt
    ];
    try solve[split*;left*].
  - 
   inductions wt2; try solve[
     split; right; unfold not;intros nt;
     inverts* nt
   ];
   try solve[split*;left*].
   pick fresh x.
   forwards*: H0 H1. inverts* H3.
   split.
   +
   inverts H4.
   *
   left.
   pick fresh y and apply consist_all.
   forwards*: consist_rename y H3.
   *
   right.
   unfold not; intros nt.
   apply H3; eauto.
   inverts nt.
   pick fresh y.
   forwards*: H8 y.
   forwards*: consist_rename y H4.
   +
   inverts H5.
   *
   left.
   pick fresh y and apply consist_all.
   forwards*: consist_rename y H3.
   *
   right.
   unfold not; intros nt.
   apply H3; eauto.
   inverts nt.
   pick fresh y.
   forwards*: H8 y.
   forwards*: consist_rename y H5.
  -
    inductions wt2; try solve[
     split; right; unfold not;intros nt;
     inverts* nt
   ];
   try solve[split*;left*].
   forwards*: IHwt1 wt2.
   inverts H. 
   split.
   inverts* H0; try solve[
    right; unfold not;intros nt;
    inverts* nt
    ];
    try solve[split*;left*].
    inverts* H0; try solve[
    right; unfold not;intros nt;
    inverts* nt
    ];
    try solve[split*;left*].
    inverts* H1; try solve[
    right; unfold not;intros nt;
    inverts* nt
    ];
    try solve[split*;left*].
    inverts* H1; try solve[
    right; unfold not;intros nt;
    inverts* nt
    ];
    try solve[split*;left*].
Qed.


Lemma consist_strengthening : forall x U E F S T,
  consist (F ++ x ~ bind_typ U ++ E) S T ->
  consist (F ++ E) S T.
Proof with eauto using wf_typ_strengthening, wf_env_strengthening.
  intros x U E F S T SsubT.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  induction SsubT; intros F EQ; subst...
  Case "consist_all".
    pick fresh X and apply consist_all...
    rewrite <- app_assoc.
    apply H0...
Qed.


Hint Resolve consist_refl consist_sym:core.

(* ********************************************************************** *)
(** * Regularity of relations *)


Lemma wft_pattern_abs: forall E A B,
 pattern_abs A B ->
 wf_typ E A ->
 wf_typ E B.
Proof.
 introv pa wf.
 inductions pa; eauto.
Qed.


Lemma wft_pattern_abs_r: forall E A B,
 pattern_abs A B ->
 wf_typ E B ->
 wf_typ E A.
Proof.
 introv pa wf.
 inductions pa; eauto.
Qed.


Lemma wft_pattern_all: forall E A B,
 pattern_all A B ->
 wf_typ E A ->
 wf_typ E B.
Proof.
 introv pa wf.
 inductions pa; eauto.
 Unshelve.
 pick fresh x.
 apply (union (dom E) (fv_tt_env E)).
Qed.


Lemma wft_pattern_all_r: forall E A B,
 pattern_all A B ->
 wf_typ E B ->
 wf_typ E A.
Proof.
 introv pa wf.
 inductions pa; eauto.
Qed.


Lemma wft_pattern_ref: forall E A B,
 pattern_ref A B ->
 wf_typ E A ->
 wf_typ E B.
Proof.
 introv pa wf.
 inductions pa; eauto.
Qed.


Lemma wft_pattern_ref_r: forall E A B,
 pattern_abs A B ->
 wf_typ E B ->
 wf_typ E A.
Proof.
 introv pa wf.
 inductions pa; eauto.
Qed.


Lemma typing_regular : forall E P e dir T,
  typing E P e dir T -> wf_env E /\ expr e /\ wf_typ E T.
Proof with simpl_env; try solve [auto | intuition auto].
  introv H.
  inductions H ...
  -
    repeat split...
    eauto using wf_typ_from_binds_typ.
  -
     destructs IHtyping1;
     destructs IHtyping2.
     splits~; try solve[inverts* H3].
     inverts* H; try solve[inverts* H4].
  -
    pick fresh y.
    destruct (H0 y) as [Hok [J K]]...
    repeat split. 
    + inversion Hok...
    +
    forwards* : lc_e_abs_exists  J.
    +
    assert(wf_typ E (t_arrow A1 A2)) as h0.
    apply wf_typ_arrow; eauto using wf_typ_from_wf_env_typ.
    rewrite_env (empty ++ E).
    eapply wf_typ_strengthening; simpl_env; eauto.
    forwards* h1: wft_pattern_abs_r H1.
  -
    destructs IHtyping;
    splits~.
    apply* lc_e_anno.
  -
    pick fresh Y.
    destruct (H0 Y) as [Hok [J K]]...
    inversion Hok; subst.
    repeat split...
    + 
     forwards* : lc_e_tabs_exists  J.
    +
      assert(wf_typ E (t_all A1)) as h0.
      pick fresh Z and apply wf_typ_all...
      destruct (H0 Z)...
      forwards* h1: wft_pattern_all_r H1.
  -
    repeat split...
    + apply lc_e_tapp...  
      eauto using type_from_wf_typ.
    +
      destruct IHtyping as [R1' [R2' R3']].
      eapply wf_typ_open; eauto.
      inverts H0.
      inverts R3'.
      pick fresh x and apply wf_typ_all; eauto.
      inverts R3'.
      pick fresh x and apply wf_typ_all; eauto.
  -
    destructs~ IHtyping; splits~.
    forwards*: consist_regular H.
  -
    destructs~ IHtyping; splits~.
    inverts* H.
    inverts* H3.
  -
    destructs~ IHtyping; splits~;
    eauto.
    rewrite_env(E++nil).
    apply wf_typ_weaken_head; auto.
  -
    pick fresh y.
    destruct (H0 y) as [Hok [J K]]...
    repeat split. 
    + inversion Hok...
    +
    forwards* : lc_e_abs_exists  J.
    +
    rewrite_env (empty ++ G).
    eapply wf_typ_strengthening; simpl_env; eauto.
Qed.


(** Automation *)

Hint Extern 1 (wf_env ?E) =>
  match goal with
  | H: typing _ _ _ _ _ |- _ => apply (proj1 (typing_regular _ _ _ _ _ H))
  | H: consist _ _ _ |- _ => apply (proj1 (consist_regular _ _ _ _ H))
  end : core.

Hint Extern 1 (wf_typ ?E ?t) =>
  match goal with
  | H: typing _ _ _ _ _ |- _ => apply (proj2 (proj2 (typing_regular _ _ _ _ _ H)))
  | H: consist _ _ _ |- _ => apply (proj1 (proj2 (consist_regular _ _ _ H)))
  | H: consist _ _ _ |- _ => apply (proj2 (proj2 (consist_regular _ _ _ H)))
  end : core.

Hint Extern 1 (type ?T) =>
  let go E := apply (type_from_wf_typ E); auto in
  match goal with
  | H: typing ?E _ _ _ _ |- _ => go E
  | H: consist ?E _ _ |- _ => go E
  | H: consist ?E _ _ |- _ => go E
  end : core.

Hint Extern 1 (expr ?e) =>
 match goal with
 | H: typing _ _ _ _ _|- _ => apply (proj1 (proj2 (typing_regular _ _ _ _ _ H)))
 end : core.
