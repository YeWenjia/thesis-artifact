Require Export Metalib.Metatheory.
Require Import LibTactics.

Require Import Definitions.
Require Import Infrastructure.
Require Import Lemmas.
Require Import Lia.
Require Import rules_inf.

(* ********************************************************************** *)
(** Weakening (5) *)


Lemma typing_weakening : forall E F G P e T dir,
   typing (E ++ G) P e dir T ->
   wf_env (E ++ F ++ G) ->
   typing (E ++ F ++ G) P e dir T.
Proof with simpl_env;
eauto using 
            wf_typ_from_wf_env_typ,
            wf_typ_weakening,
            consist_weakening.
 introv Typ. gen F. 
 inductions Typ; introv Ok; eauto.
 - forwards*:  wf_typ_weakening H1.
 - 
   pick fresh x and apply typ_abs; auto.
   lapply (H x); [intros K | auto].
    rewrite <- app_assoc.
    apply (H0 x)...
    auto.
  - 
    pick fresh a and apply typ_tabs; auto.
    lapply (H a); [intros K | auto].
    rewrite <- app_assoc.
    apply (H0 a)...
    auto.
  - eapply typ_tapp with (A1:= A1); eauto.
    apply* wf_typ_weakening.
  -
    apply* typ_consist.
    apply* consist_weakening.
  -
    pick fresh x and apply typ_absv; auto.
   lapply (H x); [intros K | auto].
    rewrite <- app_assoc.
    apply (H0 x)...
Qed.


Lemma fv_in_dom: forall G P e dir T,
    typing G P e dir T -> fv_ee e [<=] dom G.
Proof.
  intros G P e dir T H.
  inductions H; simpl; try fsetdec.
  -
    apply binds_In in H0.
    fsetdec.
  -
    pick fresh x for (L \u dom (E) \u fv_ee e).
    assert (Fx : fv_ee (e open_ee_var x) [<=] dom (x ~: A ++ E)).
    { forwards*: H0 x. }
    simpl in Fx.
    assert (Fy : fv_ee e [<=] fv_ee (e open_ee_var x)) by
        eapply fv_exp_open_exp_wrt_exp_rec_lower.
    fsetdec.
  - 
    pick fresh x for (L \u dom (E) \u fv_ee e).
    assert (Fx : fv_ee (open_te e (t_fvar x)) [<=] dom (x ~tvar ++ E)).
    { forwards*: H0 x. }
    simpl in Fx.
    assert (Fy : fv_ee e [<=] fv_ee (open_te e (t_fvar x))).
    eapply fv_exp_open_exp_wrt_typ_rec_lower.
    fsetdec.
  -
    pick fresh x for (L \u dom (G) \u fv_ee e).
    assert (Fx : fv_ee (e open_ee_var x) [<=] dom (x ~: A ++ G)).
    { forwards*: H0 x. }
    simpl in Fx.
    assert (Fy : fv_ee e [<=] fv_ee (e open_ee_var x)) by
        eapply fv_exp_open_exp_wrt_exp_rec_lower.
    fsetdec.
Qed.




Lemma tfv_in_dom_wft: forall E A,
 wf_typ E A ->
 fv_tt A [<=] dom E.
Proof.
  introv wf.
  inductions wf; simpl; try fsetdec.
  -
  apply binds_In in H.
    fsetdec.
  -
  pick fresh x for (L \u dom (E) \u fv_tt A).
  assert (Fx : fv_tt (open_tt A (t_fvar x)) [<=] dom (x ~tvar ++ E)).
  { forwards*: H0 x. }
  simpl in Fx.
  assert (Fy : fv_tt A [<=] fv_tt (open_tt A (t_fvar x))).
  eapply tfv_typ_open_typ_wrt_typ_lower.
  fsetdec.
Qed.



Lemma etfv_in_dom: forall G P e dir T,
    typing G P e dir T -> fv_te e [<=] dom G.
Proof.
  intros G P e dir T H.
  inductions H; simpl; try fsetdec.
  -
    pick fresh x for (L \u dom (E) \u fv_te e).
    assert (Fx : fv_te (e open_ee_var x) [<=] dom (x ~: A ++ E)).
    { forwards*: H0 x. }
    simpl in Fx.
    assert (Fy : fv_te e [<=] fv_te (e open_ee_var x)) by
        eapply tfv_exp_open_exp_wrt_exp_lower.
    fsetdec.
  - 
    forwards* h0: typing_regular H.
    inverts h0 as h01 h02.
    inverts h02 as h02 h03.
    forwards* h1: tfv_in_dom_wft h03. 
    fsetdec.
  -
    pick fresh x for (L \u dom (E) \u fv_te e).
    assert (Fx : fv_te (open_te e (t_fvar x)) [<=] dom (x ~tvar ++ E)).
    { forwards*: H0 x.  }
    simpl in Fx.
    assert (Fy : fv_te e [<=] fv_te (open_te e (t_fvar x))).
    eapply tfv_exp_open_exp_wrt_typ_lower.
    fsetdec.
  -
    forwards* h1: tfv_in_dom_wft H.
    fsetdec.
  -
    forwards* h0: typing_regular H1.
    inverts h0 as h01 h02.
    inverts h02 as h02 h03.
    forwards* h1: tfv_in_dom_wft h03.
    fsetdec.
  - 
    pick fresh x for (L \u dom (G) \u fv_te e).
    assert (Fx : fv_te (e open_ee_var x) [<=] dom (x ~: A ++ G)).
    { forwards*: H0 x. }
    simpl in Fx.
    assert (Fy : fv_te e [<=] fv_te (e open_ee_var x)) by
        eapply tfv_exp_open_exp_wrt_exp_lower.
    fsetdec.
Qed.


Lemma value_no_fv : forall P v dir T,
    typing nil P v dir T -> fv_ee v [<=] {}.
Proof.
  introv Typ.
  pose proof (fv_in_dom nil P v).
  intuition eauto.
Qed.



Lemma value_no_tfv : forall P v dir T,
    typing nil P v dir T -> fv_tt T [<=] {}.
Proof.
  introv Typ.
  forwards*:typing_regular Typ.
  inverts H. inverts H1.
  forwards*: tfv_in_dom_wft H2.
Qed.


Lemma value_no_tefv : forall P v dir T,
    typing nil P v dir T -> fv_te v [<=] {}.
Proof.
  introv Typ.
  pose proof (etfv_in_dom nil P v).
  intuition eauto.
Qed.



Lemma subst_value : forall P v T dir z u,
    typing nil P v dir T -> subst_ee u z v = v.
Proof.
  intros P v dir T z u Typ.
  lets* Fv: value_no_fv Typ.
  forwards*: subst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.


Lemma subst_value_ty : forall P v T dir z u,
    typing nil P v dir T -> subst_tt u z T = T.
Proof.
  intros P v dir T z u Typ.
  lets* Fv: value_no_tfv Typ.
  forwards*: tsubst_typ_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.



Lemma subst_value_te : forall P v T dir z u,
    typing nil P v dir T -> subst_te u z v = v.
Proof.
  introv Typ.
  lets* Fv: value_no_tefv Typ.
  forwards*: tsubst_exp_fresh_eq.
  rewrite Fv.
  fsetdec.
Qed.


Lemma length_less: forall l n,
 l < S n ->
 l = n \/ l < n.
Proof.
  introv les.
  inverts* les.
Qed.


Lemma nth_eq_last : forall A (l:list A) x d,
  nth (length l) (l ++ x::nil) d = x.
Proof.
  induction l; intros; [ auto | simpl; rewrite IHl; auto ].
Qed.


Lemma sto_ok_value: forall l mu,
 l < length mu ->
 sto_ok mu ->
 value ((store_lookup l mu)).
Proof.
  introv len ok. gen l.
  inductions ok; intros; try solve[inverts len];
  simpl in *.
  destruct l; simpl; eauto.
  forwards*: IHok l.
  lia.
Qed.



Lemma principle_typ_inf: forall E P u A,
 value u -> 
 typing E P u Inf A -> 
 dynamic_type u = A.
Proof.
  introv val typ.
  inverts* val; try solve[inverts* typ].
Qed.


Lemma pprinciple_typ_inf: forall E P u A,
 pvalue u -> 
 typing E P u Inf A -> 
 dynamic_type u = A.
Proof.
  introv val typ.
  inverts* val; try solve[inverts* typ].
Qed.



Lemma inference_unique : forall G P e A1 A2,
    typing G P e Inf A1 ->
    typing G P e Inf A2 ->
    A1 = A2.
Proof.
  introv Ty1.
  gen_eq Dir : Inf.
  gen A2.
  induction Ty1; introv Eq Ty2; try (inverts* Eq); try (inverts* Ty2).
  - (* t_var *)
    forwards*: binds_unique H0 H5. inverts* H1.
  - (* t_app *)
    forwards * : IHTy1_1 H5.
    inverts* H0. inverts* H;inverts* H2.
  - (* t_all *)
    forwards * : IHTy1 H7.
    inverts* H1. inverts* H0; inverts* H6.
  - forwards * : IHTy1 H2.
    inverts* H.
  - forwards * : IHTy1 H4.
    inverts* H0. inverts H;inverts* H1.
Qed.



(************************************************************************ *)
(** ** Substitution preserves typing (8) *)

Lemma typing_through_subst_ee : forall P U E F x dir T e u,
  typing (F ++ x ~ bind_typ U ++ E) P e dir T ->
  typing E P u Inf U ->
  typing (F ++ E) P (subst_ee  u x e) dir T.
Proof with simpl_env;
           eauto 4 using wf_typ_strengthening,
                         wf_env_strengthening,
                         consist_strengthening.
Proof.
  introv TypT TypU.
  remember (F ++ x ~ bind_typ U ++ E) as E'.
  generalize dependent F.
  inductions TypT; intros F EQ; subst; simpl subst_ee...
  -
    destruct (x0 == x); try subst x0.
    +
    analyze_binds_uniq H0.
    injection BindsTacVal; intros; subst.
    rewrite_env (empty ++ F ++ E).
    apply typing_weakening...
    +
    analyze_binds H0.
    eauto using wf_env_strengthening.
    eauto using wf_env_strengthening.
  -
    pick fresh y and apply typ_abs.
    rewrite subst_exp_open_exp_wrt_exp_var...
    rewrite <- app_assoc.
    apply H0...
    auto.
  -
    pick fresh y and 
    apply typ_tabs; eauto. 
    rewrite subst_exp_open_exp_wrt_typ_var...
    rewrite <- app_assoc.
    apply H0; auto...
  -
    forwards* h1: subst_value x u  TypT.
    apply typ_rt; try solve[
      rewrite h1; auto
    ] ...
  -
    pick fresh y and apply typ_absv.
    rewrite subst_exp_open_exp_wrt_exp_var...
    rewrite <- app_assoc.
    apply H0...
    auto.
Qed.



Lemma consist_through_subst_tt : forall E F Y S T A,
  consist (F ++ Y ~tvar ++ E) S T ->
  wf_typ E A ->
  consist (map (subst_tb Y A) F ++ E) (subst_tt A Y S) (subst_tt A Y T).
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



Lemma pat_abs_subst_tt : forall Y S T A,
  pattern_abs S T ->
  pattern_abs (subst_tt Y A S) (subst_tt Y A T).
Proof.
  introv SsubT.
  induction SsubT; intros; subst; simpl subst_tt; eauto.
Qed.


Lemma pat_all_subst_tt : forall Y S T A,
  pattern_all S T ->
  pattern_all (subst_tt Y A S) (subst_tt Y A T).
Proof.
  introv SsubT.
  induction SsubT; intros; subst; simpl subst_tt; eauto.
Qed.


Lemma pat_ref_subst_tt : forall Y S T A,
  pattern_ref S T ->
  pattern_ref (subst_tt Y A S) (subst_tt Y A T).
Proof.
  introv SsubT.
  induction SsubT; intros; subst; simpl subst_tt; eauto.
Qed.

Lemma typing_through_subst_te : forall E F Z ph e T P mu dir,
  ph |== mu ->
  typing (F ++ Z~tvar ++ E) ph e dir T ->
  wf_typ E P ->
  typing (map (subst_tb Z P) F ++ E) ph (subst_te P Z  e) dir (subst_tt P Z T).
Proof with simpl_env;
           eauto 6 using wf_env_subst_tb,
                         wf_typ_subst_tb,
                         consist_through_subst_tt.
 introv wel TypT TypU.
 remember (F ++ Z~tvar ++ E) as E'.
 generalize dependent F.
 inductions TypT; intros F EQ; subst; simpl subst_te; simpl subst_tt;
 try solve[inverts* H]...
 -
   apply typ_var...
   rewrite (map_subst_tb_id E Z P);
        [ | auto | eapply fresh_mid_tail; eauto ].
   analyze_binds H0...
   forwards*: wf_env_subst_tb H TypU.
   forwards*: wf_env_concat_left_inv H1.
  -
    forwards*: wf_env_subst_tb H TypU.
    forwards*: wf_typ_subst_tb H1 TypU.
    inverts wel. inverts H5.
    rewrite H6 in H0.
    forwards*: H7 H0.
    forwards*:subst_value_ty H5.
    rewrite <- H6 in H0.
    rewrite H8 in *.
    apply typ_loc; eauto.
  -
    pick fresh y and apply typ_abs.
    rewrite tsubst_exp_open_exp_wrt_exp_var...
    rewrite_env (map (subst_tb Z P) (y ~ bind_typ A1 ++ F) ++ E).
    apply H0...
    forwards*: pat_abs_subst_tt H1.
  -
    pick fresh X and 
    apply typ_tabs.
    forwards* h1: H0 X. 
    rewrite tsubst_exp_open_exp_wrt_typ_var...
    rewrite tsubst_typ_open_typ_wrt_typ_var...
    forwards*: pat_all_subst_tt H1.
  -
    rewrite tsubst_typ_open_tt...
    forwards*: IHTypT.
    inverts H0; simpl in *; eauto.
    eapply typ_tapp...
    eapply typ_tapp ...
  -
    forwards* h1: subst_value_te  Z P TypT.
    rewrite h1.
    forwards* h2: subst_value_ty Z P  TypT.
    rewrite h2.
    apply typ_rt;eauto.
    forwards*: wf_env_subst_tb H TypU.
  -
    pick fresh y and apply typ_absv.
    rewrite tsubst_exp_open_exp_wrt_exp_var...
    rewrite_env (map (subst_tb Z P) (y ~ bind_typ A ++ F) ++ E).
    apply H0...
    forwards* h1: IHTypT. 
  -
    forwards* h0: typing_regular TypT.
    inverts h0 as h0 h1.
    inverts h1 as h1 h2.
    forwards*h3: wf_env_subst_tb h0.
    forwards*h4: wf_typ_subst_tb h2.
    lets ok: wel.
    inverts wel as h5 h6. inverts h6 as h6 h7.
    rewrite h6 in H.
    forwards*h8: h7 H.
    forwards*h9:subst_value_ty h8.
    forwards* h10: IHTypT.
    rewrite h9 in *.
    apply typ_rts; eauto.
    rewrite h6 in *; auto.
Qed.


Lemma typing_subst_simpl_ee : forall P U E x T e u dir,
  typing (x ~ bind_typ U ++ E) P e dir T ->
  typing E P u Inf U ->
  typing E P (subst_ee u x e) dir T.
Proof.
    introv typ1 typ2.
    rewrite_env (nil++E).
    apply* typing_through_subst_ee.
Qed.


Lemma consist_subst_simpl : forall E Y S T A,
  consist (Y ~tvar ++ E) S T ->
  wf_typ E A ->
  consist (E) (subst_tt A Y  S) (subst_tt A Y  T).
Proof.
  introv con type.
  rewrite_env (map (subst_tb Y A) empty ++E).
  apply* consist_through_subst_tt.
Qed.


Lemma typing_subst_simpl_te : forall ph mu E Z e T P dir,
  ph |== mu ->
  typing (Z~tvar ++ E) ph e dir T ->
  wf_typ E P ->
  typing (E) ph (subst_te P Z  e) dir (subst_tt P Z  T).
Proof.
  introv wel typ1 typ2.
  rewrite_env (map (subst_tb Z P) empty ++E).
  apply* typing_through_subst_te.
Qed.



Lemma extends_lookup : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  store_Tlookup l ST' = store_Tlookup l ST.
Proof with auto.
  intros l ST.
  generalize dependent l.
  induction ST as [|a ST2]; intros l ST' Hlen HST'.
  - (* nil *) inversion Hlen.
  - (* cons *) unfold store_Tlookup in *.
    destruct ST'.
    + (* ST' = nil *) inversion HST'.
    + (* ST' = a' :: ST'2 *)
      inversion HST'; subst.
      destruct l as [|l'].
      * (* l = 0 *) auto.
      * (* l = S l' *) simpl. apply IHST2...
        simpl in Hlen; lia.
Qed.


Lemma extends_refl : forall E,
  extends E E.
Proof. 
 intros_all~.
 inductions E; eauto. 
Qed.


Lemma length_extends : forall l ST ST',
  l < length ST ->
  extends ST' ST ->
  l < length ST'.
Proof with eauto.
  intros. generalize dependent l. induction H0; intros l Hlen.
    - inversion Hlen.
    - simpl in *.
      destruct l; try lia.
        apply lt_n_S. apply IHextends. lia.
Qed.


Lemma extends_wf_typ: forall l P1 P2 E,
 l < length P1 ->
 extends P2 P1 ->
 wf_typ E (store_Tlookup l P1) ->
 wf_typ E (store_Tlookup l P2).
Proof.
  introv len ext wf. gen l E.
  inductions ext; intros; eauto;
  try solve[inverts len]; simpl in *.
  destruct l; simpl; eauto.
  forwards*: IHext l E. lia.
Qed.




Lemma store_weakening : forall G ST ST' t dir T,
  extends ST' ST ->
  typing G ST t dir T ->
  typing G ST' t dir T.
Proof with eauto.
  intros. induction H0; eauto.
  - (* T_Loc *)
    rewrite <- (extends_lookup _ _ ST')...
    apply typ_loc; eauto.
    eapply length_extends...
    forwards*: extends_wf_typ H2.
  -
    apply typ_rts; eauto.
    eapply length_extends...
    forwards* h1: extends_lookup H.
    rewrite h1; eauto.
Qed.


Lemma extends_app : forall ST T,
  extends (ST ++ T) ST.
Proof.
  induction ST; intros T.
  auto.
  simpl. auto.
Qed.


Hint Resolve extends_refl extends_app store_weakening: core.



(* ********************************************************************** *)
(** ** Preservation *)

Lemma tpre_refl: forall A,
type A ->
tpre A A.
Proof.
 introv h1.
 inductions h1; eauto.
 Unshelve.
 apply (fv_tt T2).
Qed.


Hint Extern 1 (tpre ?A ?A) =>
 match goal with
 | H: type ?A |- _ => apply tpre_refl
 end : core.

Hint Resolve  tpre_refl: core.

Lemma meet_more_precise: forall A B C,
 meet A B C ->
 tpre C A /\ tpre C B.
Proof.
  introv mt.
  inductions mt; eauto;
  try solve[inverts IHmt1 as h1 h2; eauto;
  inverts IHmt2 as h3 h4; eauto];
  try solve[inverts IHmt as h1 h2; eauto].
  -
    splits;
    pick fresh y and apply tp_all;
    forwards*: H0 y.
Qed.

Lemma Cast_prv_pvalue: forall p A p' mu,
    pvalue p -> 
    tpre A (dynamic_type p) ->
    Cast (p, mu) A ((r_e p')) -> pvalue p'.
Proof.
  introv Val tp Red.
  inductions Red; eauto;
  try solve[inverts Val as h1 h2;eauto; inverts h1];
  try solve[inverts Val as h1 h2; simpl in *; eauto;
  inverts tp; eauto].
Qed.


Lemma meet_sim: forall E A B C,
  wf_env E ->
  wf_typ E A ->
  wf_typ E B ->
  wf_typ E C ->
  meet A B C ->
  consist E A B /\ consist E A C /\ consist E B C .
Proof.
 introv wf wf1 wf2 wf3 mt. gen E.
 inductions mt;intros; 
 try solve[splits*; eauto].
 -
   forwards* h1: IHmt1; try solve[inverts wf1; inverts wf2; 
   inverts wf3;auto].
   forwards* h2: IHmt2; try solve[inverts wf1; inverts wf2; 
   inverts wf3;auto].
 -
   inverts wf1 as wf1.
   inverts wf2 as wf2.
   inverts wf3 as wf3.
   splits;
   pick fresh x and apply consist_all; eauto;
   forwards*: H0 (x ~tvar ++ E);
   try solve[
   apply wf_env_tvar; eauto];
   try solve[forwards*: wf1 x];
   try solve[forwards*: wf2 x];
   try solve[forwards*: wf3 x].
 -
   forwards* h1: IHmt; try solve[inverts wf1; inverts wf2; 
   inverts wf3;auto].
Qed.





Lemma eq_type: forall A B x n,
 x `notin` (fv_tt A) ->
 x `notin` (fv_tt B) ->
 open_tt_rec n x A = open_tt_rec n x B ->
 A = B.
Proof.
  introv nt1 nt2 eq. 
  forwards*: open_typ_wrt_typ_rec_inj A B.
Qed.



Lemma tpre_trans: forall t1 t2 t3,
 tpre t1 t2 ->
 tpre t2 t3 ->
 type t1 ->
 tpre t1 t3.
Proof.
  introv tp1 tp2 ty. gen t1.
  inductions tp2; intros;eauto.
  -
    inverts tp1 as h1; try solve[inverts ty].
    inverts ty as h2.
    pick fresh y and apply tp_all; eauto.
  -
    inverts tp1; try solve[inverts* ty].
  -
    inverts tp1; try solve[inverts* ty].
Qed.



Lemma tpre_sim: forall A B E,
 tpre A B ->
 wf_env E ->
 wf_typ E A ->
 wf_typ E B ->
 consist E A B.
Proof.
  introv tp wf1 wf2 wf3. gen E.
  inductions tp; intros;try solve[inverts wf2;
  inverts wf3; eauto].
  -
    inverts wf2 as wf2.
    inverts wf3 as wf3.
    pick fresh y and apply consist_all; eauto.
Qed.




Lemma Cast_preservation: forall P mu p A p' B,
      P |== mu ->
     pvalue p -> 
     Cast (p, mu) A (r_e p') ->
     meet (dynamic_type p) B A -> 
     wf_typ nil B ->
     typing nil P p Chk A -> typing nil P (e_val p' B) Inf B.
Proof with auto.
  introv well val red mt wft typ.
  lets Red': red. gen B.
  inductions red;intros;try solve[inverts* Val]; 
  try solve [constructor*]; simpl in *.
  -
    inverts typ as h1 h2.
    inverts h2 as h2; simpl in *.
    forwards* h3: meet_sim mt.
    lets(h4&h5&h6):h3.
    inverts h4; try solve[apply typ_rt; eauto].
  -
    inverts typ as h1 h2.
    inverts h2 as h2; simpl in *.
    forwards* h3: meet_sim mt.
    lets(h4&h5&h6):h3.
    inverts h4; try solve[apply typ_rt; eauto].
  -
    inverts val.
    forwards* h1: meet_more_precise mt.
    inverts h1 as h1 h2.
    inverts h1 as h11 h12.
    inverts typ as h3 h4.
    inverts h4 as h4 h5.
    inverts h4 as h4 h6.
    inverts h6 as h6 h7.
    forwards* h8: meet_sim mt.
    inverts h8 as h81 h82.
    inverts h82 as h82 h83.
    forwards: consist_sym h83.
    apply typ_rt; eauto.
  -
    inverts val.
    forwards* h1: meet_more_precise mt.
    inverts h1 as h1 h2.
    inverts h1 as h11 h12.
    inverts typ as h3 h4.
    inverts h4 as h4 h5.
    inverts h4 as h4 h6.
    inverts h6 as h6 h7.
    forwards* h8: meet_sim mt.
    inverts h8 as h81 h82.
    inverts h82 as h82 h83.
    forwards: consist_sym h83.
    apply typ_rt; eauto.
  -
    inverts val.
    forwards* h1: meet_more_precise mt.
    inverts h1 as h1 h2.
    inverts h1 as h11 h12.
    inverts typ as h3 h4.
    inverts h4 as h4 h5.
    inverts h4 as h4 h6.
    inverts h6 as h6 h7.
    forwards* h8: meet_sim mt.
    inverts h8 as h81 h82.
    inverts h82 as h82 h83.
    forwards: consist_sym h83.
    lets wl: well.
    inverts well as h13 h14.
    inverts h14 as h14 h15.
    rewrite h14 in h7.
    forwards* h16: h15 o.
    forwards* h18: sto_ok_value wl.
    forwards* h17: principle_typ_inf h16.
    rewrite h17 in *.
    rewrite <- h14 in *.
    apply typ_rt; eauto.
Qed.




Lemma tpre_type: forall A1 A2,
    tpre A1 A2 ->
    type A1 /\ type A2.
Proof.
  introv ty. inductions ty; simpls~;
  try solve[
    destruct IHty1; destruct IHty2; splits~
  ];
  try solve[
    destruct IHty; splits~
  ].
  -
    splits~.
    +
    pick fresh x.
    forwards* h1: H0 x.
    inverts h1 as h1 h2.
    forwards*: lc_t_all_exists h1.
    +
    pick fresh x.
    forwards* h1: H0 x.
    inverts h1 as h1 h2.
    forwards*: lc_t_all_exists h2.
Qed.


Hint Resolve tpre_type : core.


Lemma Castv_prv_value: forall p A p' mu,
    value p -> 
    Castv (p, mu) A ((r_e p')) -> value p'.
Proof.
  introv Val Red.
  inductions Red; eauto.
  inverts Val as h1 h2.
  forwards* h4: meet_more_precise H0. 
  forwards* h3: Cast_prv_pvalue H.
  inverts h4 as h5 h6.
  forwards*:tpre_type h6.
Qed.



Lemma meet_wft: forall t1 t2 t3 E,
 wf_typ E t1 ->
 wf_typ E t2 ->
 meet t1 t2 t3 ->
 wf_typ E t3.
Proof.
 introv wf1 wf2 wf3. gen E.
 inductions wf3; intros;eauto; 
 try solve[inverts wf1; inverts wf2; eauto].
 inverts wf1 as wf1.
 inverts wf2 as wf2.
 pick fresh y and apply wf_typ_all; eauto.
Qed.


Lemma pvalue_wf: forall p P E dir t,
 pvalue p ->
 typing E P p dir t ->
 wf_typ E (dynamic_type p).
Proof.
  introv pv typ.
  destruct dir.
  -
    forwards* h1: pprinciple_typ_inf typ.
    forwards*: typing_regular typ.
    rewrite h1; eauto.
  -
    inverts typ as  hh1 hh2; try solve[inverts pv].
    forwards* h1: pprinciple_typ_inf hh2.
    forwards*: typing_regular hh2.
    rewrite h1; eauto.
Qed.






Lemma Casts_preservation1: forall v A0 A v' mu P,
 P |== mu ->
 wf_typ empty A ->
 value v -> Castv (v,mu) A ((r_e v')) 
     -> typing nil P v Chk A0 -> typing nil P v' Inf A.
Proof with auto.
  introv well wf1 val tlist typ.
  inverts tlist as h3 h4; try solve[inverts h4].
  inverts val as val1 val2.
  forwards* h5: meet_more_precise h4.
  forwards* h6: Cast_prv_pvalue h3.
  inverts typ as typ1 typ2.
  inverts typ2 as typ2 typ3 typ4 typ5.
  forwards* h7: typing_regular typ4.
  forwards* h8: pvalue_wf typ3.
  forwards* h9: meet_wft h4.
  forwards* h10: meet_sim h4.
  inverts typ4 as typ4 typ6; try solve[inverts typ3].
  forwards* typ8: pprinciple_typ_inf typ6.
  rewrite <- typ8 in *.
  forwards* h11: Cast_preservation h3 h4.
Qed.


Lemma sto_ok_app: forall st1 st2,
 sto_ok st1 ->
 sto_ok st2 ->
 sto_ok (st1 ++ st2).
Proof.
  introv ok1 ok2.
  inductions ok1; simpl; eauto.
Qed.




Lemma add_sym : forall m,
 1 + m = m + 1.
Proof.
  introv. 
  inductions m; intros; eauto.
  simpl.
  rewrite <- IHm.
  simpl.
  reflexivity.
Qed.


Lemma store_well_typed_app : forall ST st t1 T1,
  value t1 ->
  sto_typing ST st ->
  typing nil  ST t1 Inf T1 ->
  sto_typing (ST ++ T1::nil) (st ++ t1::nil).
Proof with auto.
  intros.
  unfold sto_typing in *.
  destruct H0. destruct H2. 
  rewrite app_length. simpl.
  rewrite app_length. simpl.
  split;eauto.
  - apply sto_ok_app;eauto.
  - (* types match. *)
    split;eauto.
    intros l Hl.
    unfold store_lookup, store_Tlookup.
    apply le_lt_eq_dec in Hl; destruct Hl as [Hlt | Heq].
    + (* l < length st *)
      rewrite !app_nth1; try solve[lia].
      * apply store_weakening with ST. apply extends_app.
        forwards*: H3. lia.
    + (* l = length st *)
      assert(1 + length st = S (length st)).
      simpl;eauto.
      rewrite add_sym in H4.
      rewrite H4 in *.
      injection Heq as Heq; subst.
      rewrite app_nth2; try lia.
      rewrite <- H2.
      rewrite minus_diag. simpl.
      apply store_weakening with ST...
      rewrite app_nth2; [|lia].
      rewrite minus_diag. simpl. assumption.
Qed.


Lemma length_replace : forall A n x (l:list A),
  length (replace n x l) = length l.
Proof with auto.
  intros A n x l. generalize dependent n.
  induction l; intros n.
    destruct n...
    destruct n...
      simpl. rewrite IHl...
Qed.


Lemma lookup_replace_eq : forall l t st,
  l < length st ->
  store_lookup l (replace l t st) = t.
Proof with auto.
  intros l t st.
  unfold store_lookup.
  generalize dependent l.
  induction st as [|t' st']; intros l Hlen.
  - (* st =  *)
   inversion Hlen.
  - (* st = t' :: st' *)
    destruct l; simpl...
    apply IHst'. simpl in Hlen. lia.
Qed.


Lemma replace_nil : forall A n (x:A),
  replace n x nil = nil.
Proof.
  destruct n; auto.
Qed.



Lemma lookup_replace_neq : forall l1 l2 t st,
  l1 <> l2 ->
  store_lookup l1 (replace l2 t st) = store_lookup l1 st.
Proof with auto.
  unfold store_lookup.
  induction l1 as [|l1']; intros l2 t st Hneq.
  - (* l1 = 0 *)
    destruct st.
    + (* st =  *) rewrite replace_nil...
    + (* st = _ :: _ *) destruct l2... contradict Hneq...
  - (* l1 = S l1' *)
    destruct st as [|t2 st2].
    + (* st =  *) destruct l2...
    + (* st = t2 :: st2 *)
      destruct l2...
      simpl; apply IHl1'...
Qed.


Lemma replace_sto_ok : forall l v st,
 l < length st ->
 value v ->
 sto_ok st ->
 sto_ok (replace l v st).
Proof.
  introv len val ok. gen l v.
  inductions ok; intros;
  try solve[inverts len];
  simpl in *.
  destruct l; simpl; eauto.
  apply sto_ok_push; auto.
  forwards*: IHok l val. lia.
Qed. 


Lemma assign_pres_store_typing : forall ST st l t,
  l < length st ->
  value t ->
  sto_typing ST st ->
  typing nil ST t Inf (store_Tlookup l ST) ->
  sto_typing ST (replace l t st).
Proof with auto.
  introv  Hlen val HST Ht.
  inverts HST. inverts H0.
  unfold sto_typing.
  split.
  forwards*: replace_sto_ok Hlen val.
  split.
  rewrite length_replace...
  intros l' Hl'.
  destruct (l' == l).
  - (* l' = l *)
    inverts e.
    rewrite lookup_replace_eq...
  - (* l' <> l *)
    rewrite lookup_replace_neq...
    rewrite length_replace in Hl'.
    apply H2...
Qed.



Lemma pattern_abs_uniq: forall A B1 B2,
 pattern_abs A B1 ->
 pattern_abs A B2 ->
 B1 = B2.
Proof.
  introv pa1 pa2.
  inverts pa1; inverts* pa2.
Qed.


Lemma pattern_all_uniq: forall A B1 B2,
 pattern_all A B1 ->
 pattern_all A B2 ->
 B1 = B2.
Proof.
  introv pa1 pa2.
  inverts pa1; inverts* pa2.
Qed.


Lemma pattern_ref_uniq: forall A B1 B2,
 pattern_ref A B1 ->
 pattern_ref A B2 ->
 B1 = B2.
Proof.
  introv pa1 pa2.
  inverts pa1; inverts* pa2.
Qed.


Lemma pattern_consist: forall E t1 t2 B C,
 wf_typ E (t_arrow t1 t2) ->
 consist E (t_arrow t1 t2) B ->
 pattern_abs B C ->
 consist E (t_arrow t1 t2) C.
Proof.
  introv ty sm pa.
  inverts* pa.
  inverts* ty.
  forwards*: consist_regular sm.
Qed.

Lemma pattern_all_consist: forall E t1 B C,
 wf_typ E (t_all t1) ->
 consist E (t_all t1) B ->
 pattern_all B C ->
 consist E (t_all t1) C.
Proof.
  introv ty sm pa.
  inverts* pa.
  inverts* ty.
  forwards* h1: consist_regular sm.
  inverts h1 as h1 h2.
  inverts h2 as h2 h3.
  inverts h2 as h2.
  pick fresh y and apply consist_all.
  assert( (t_dyn open_tt_var y) = t_dyn) as h4.
  unfold open_tt; simpl in *; auto.
  rewrite h4.
  apply consist_dyn_r; eauto.
Qed.


Lemma pattern_ref_consist: forall E t1  B C,
 wf_typ E (t_ref t1) ->
 consist E (t_ref t1) B ->
 pattern_ref B C ->
 consist E (t_ref t1) C.
Proof.
  introv ty sm pa.
  inverts* pa.
  inverts* ty.
  forwards* h1: consist_regular sm.
Qed.

Lemma pattern_abs_tp: forall A B1,
 type A ->
 pattern_abs A B1 ->
 tpre B1 A.
Proof.
  introv ty pa1.
  inverts* pa1; eauto.
Qed.


Lemma pattern_ref_tp: forall A B1,
 type A ->
 pattern_ref A B1 ->
 tpre B1 A.
Proof.
  introv ty pa1.
  inverts* pa1; eauto.
Qed.


Lemma pattern_all_tp: forall A B1,
 type A ->
 pattern_all A B1 ->
 tpre B1 A.
Proof.
  introv ty pa1.
  inverts* pa1.
Qed.



Lemma step_not_rv: forall l mu mu',
  irred (e_rval (e_loc l)) mu mu'.
Proof.
  introv.
  unfold irred.
  introv H;
  inverts* H;
  unfold not;intros;
  try solve[
    inverts* H;
    try solve[
    destruct F; unfold fill in H0; inverts* H0];
    try solve[inverts* H7];
    try solve[inverts* H2;inverts H4]].
    destruct F; unfold fill in H0; inverts* H0.
    destruct F; unfold fill in H0; inverts* H0.
Qed. 


Theorem preservation : forall P mu mu' e e' dir T,
  P |== mu ->
  typing nil P e dir T ->
  step (e,mu) ((r_e e'), mu') ->
  exists P', 
  extends P' P /\ 
  typing nil P' e' dir T /\
  P' |== mu'.
Proof with eauto.
  introv well Typ Red. lets Typ': Typ. gen mu mu' e'.
  inductions Typ; introv well Red.
  - (* var *)
    inverts* Red; try solve[destruct F in H1; unfold fill in H1; inverts* H1];
    try solve[inverts* H6].
  - (* lit *)
    inverts* Red; try solve[destruct F in H0; unfold fill in H0; inverts* H0];
    try solve[inverts* H6].
    exists* P; split*.
  - (* unit *)
    inverts* Red; try solve[destruct F in H0; unfold fill in H0; inverts* H0];
    try solve[inverts* H6].
    exists* P; split*.
  - (* loc *)
    inverts* Red; 
    try solve[destruct F in H2; unfold fill in H2; 
    inverts* H2].
    lets wl: well.
    inverts well as h1 h2. inverts h2 as h2 h3.
    rewrite h2 in *.    
    forwards* h4: h3 H0.
    forwards* h5: sto_ok_value h1.
    forwards* h6: principle_typ_inf h4.
    rewrite h6.
    exists* P; split*. split*.
    eapply typ_rt; eauto.
    eapply typ_consist.
    apply consist_refl; auto.
    apply typ_anno; eauto.
  - (* app *)
    inverts Red as h1 h2;
    try solve[inverts Typ1 as h0; inverts h0].
    +
      destruct F; unfold fill in *; inverts* H0; simpl in *.
      * 
      forwards* h3: IHTyp1 h2.
      lets(x&hh1&hh2&hh3): h3.
      exists* x.
      *
      forwards* h3: IHTyp2 h2.
      lets(x&hh1&hh2&hh3): h3.
      exists* x.
    +
       inverts Typ1 as h3 h4 h5 h6.
      inverts h5 as h7 h8.
      forwards* h01: typing_regular h8.
      inverts h01 as h01 h001.
      inverts h001 as h001 h002.
      inverts h8 as h9 h10.
      inverts h9 as h11 h12.
      forwards* h02: typing_regular h12.
      inverts h02 as h02 h003.
      inverts h003 as h003 h004.
      inverts h12 as h12 h13.
      inverts h12 as h12 h14; try solve[inverts h14].
      inverts h14.
      inverts h004 as h0041 h0042.
      forwards* h15: pattern_abs_uniq H H7.
      inverts h15.
      inverts h002 as h005 h006.
      forwards* h16: pattern_consist h7.
      inverts h16 as h17 h18.
      inverts h11 as h19 h20.
      exists. splits*.
      apply~ typ_anno.
      apply typ_consist with (A := B2); eauto.
      apply~ typ_anno.
      apply typ_consist with (A := A5); eauto.
      apply~ typ_anno.
      pick fresh x and apply typ_absv; eauto.
      apply~ typ_anno.
      apply typ_consist with (A := B1); eauto.
  - (* abs *)
    inverts Red as h1 h2 h3; try solve[destruct F in *; unfold fill in *; inverts* h3].
  - (* anno *)
    inverts Red as h1 h2 h3; try solve[destruct F in *; unfold fill in *; inverts* h3].
    +
      destruct F; unfold fill in *; inverts* h3; simpl in *.
      * 
      forwards* h3: IHTyp h2.
      lets(x&hh1&hh2&hh3): h3.
      exists* x.
    +
      forwards*: typing_regular Typ.
      forwards*: Casts_preservation1 h3.
    +
      forwards* h0: typing_regular Typ'.
      forwards* h: wft_pattern_abs h2.
      inverts Typ as h4 h5; try solve[inverts h5].
      forwards* h6: pattern_abs_uniq h5 h2.
      inverts h6.
      forwards* h7: pattern_abs_tp h2.
      forwards* h8: tpre_sim h7.
      exists* P. split*. split*.
      apply typ_rt; eauto.
      eapply typ_consist; eauto.
      eapply typ_anno; eauto.
    +
      forwards* h0: typing_regular Typ'.
      forwards* h: wft_pattern_all h2.
      inverts Typ as h4 h5; try solve[inverts h5]. 
      forwards* h6: pattern_all_uniq h5 h2.
      inverts h6.
      forwards* h7: pattern_all_tp h2.
      forwards* h8: tpre_sim h7.
      exists* P. split*. split*.
      apply typ_rt; eauto.
      eapply typ_consist; eauto.
      eapply typ_anno; eauto.
  - (* tabs *)
    inverts Red as h1 h2 h3; try solve[destruct F in *; unfold fill in *; inverts* h3].
  - (* tapp *)
    inverts Red as h1 h2 h3; try solve[destruct F in *; unfold fill in *; inverts* h3].
    +
      destruct F; unfold fill in *; inverts* h3; simpl in *.
      * 
      forwards* h3: IHTyp h2.
      lets(x&hh1&hh2&hh3): h3.
      exists* x.
    +
      inverts Typ as h3 h4 h5 h6. 
      inverts h5 as h7 h8.
      inverts h8 as h8.
      inverts h8 as h8 h9.
      inverts h9 as h9.
      forwards* hh1: typing_regular h9.
      inverts h9 as h9 h10; inverts h10.
      assert(consist empty (t_all A5) (t_all A5)) as hh.
      apply consist_refl; eauto.
      inverts hh as hh.
      forwards* h11: pattern_all_uniq H0 h2.
      inverts h11.
      forwards* h: pattern_all_consist h7 h2.
      inverts h as h.
      inverts h8 as h8.
      *
      exists P. split*. split*.
      eapply typ_anno; eauto.
      apply typ_consist with (A := (open_tt A3 A)); eauto.
      pick_fresh Y.
      rewrite (@tsubst_typ_intro Y).
      assert( (open_tt A4 A) = (subst_tt A Y (A4 open_tt_var Y))) as h12.
      rewrite* (@tsubst_typ_intro Y).
      rewrite h12.
      apply* consist_subst_simpl.
      fsetdec.

      eapply typ_anno; eauto.
      apply typ_consist with (A := (open_tt A5 A)); eauto.
      pick_fresh Y.
      rewrite* (@tsubst_typ_intro Y).
      assert( (open_tt A3 A) = (subst_tt  A Y (A3 open_tt_var Y))) as h12.
      rewrite* (@tsubst_typ_intro Y).
      rewrite h12.
      apply* consist_subst_simpl.

      eapply typ_anno; eauto.
      pick fresh X.
      forwards* h13: h9 X.
      rewrite* (@tsubst_exp_intro X).
      rewrite* (@tsubst_typ_intro X).
      apply* typing_subst_simpl_te.
  - (* chk *)
    forwards*: IHTyp Red.
    lets(P'&extend&rtyp&rwell): H0.
    exists* P'.
  - (* ref *)
    inverts Red as h1 h2 h3; try solve[destruct F in *; unfold fill in *; inverts* h3].
    +
      destruct F; unfold fill in *; inverts* h3; simpl in *.
      * 
      forwards* h3: IHTyp h2.
      lets(x&hh1&hh2&hh3): h3.
      exists* x.
    +
      lets well': well.
      inverts well. inverts H0.
      exists*(P++A::nil).
      split*.
      split*.
      replace (t_ref A)
      with (t_ref (store_Tlookup (length mu) (P ++ A :: nil))).
      apply typ_loc; eauto.
      rewrite <- H1.
      rewrite app_length. simpl. lia.
      unfold store_Tlookup.
      rewrite <- H1.
      rewrite nth_eq_last; eauto.
      unfold store_Tlookup.
      rewrite <- H1.
      rewrite nth_eq_last; eauto.
      apply store_well_typed_app; assumption.
  - (* get *)
    inverts Red as h1 h2 h3; try solve[destruct F in *; unfold fill in *; inverts* h3].
    +
      destruct F; unfold fill in *; inverts* h3; simpl in *.
      * 
      forwards* h3: IHTyp h2.
      lets(x&hh1&hh2&hh3): h3.
      exists* x.
    +
      inverts Typ as h3 h4  h5 h6. 
      forwards* h7: typing_regular h5.
      inverts h5 as h5 h8.
      inverts h8 as h8 h9.
      inverts h8 as h10 h11.
      inverts h11 as h11 h12 h13.
      forwards* h14: pattern_ref_uniq H h2.
      inverts h14.
      exists* P. split*. split*.
      inverts well as h15 h16. 
      inverts h16 as h16 h17.
      inverts h10 as h10.
      rewrite <- h16 in *.
      forwards* h18: h17 l0.
      forwards* h19: pattern_ref_consist h2.
      inverts h19 as h19.
      apply typ_anno; eauto.
  -  (* set *)
    inverts Red as h1 h2 h3; try solve[destruct F in *; unfold fill in *; inverts* h3];
    try solve[inverts* Typ1].
    +
      destruct F; unfold fill in *; inverts* h3; simpl in *.
      * 
        forwards* h3: IHTyp1 h2.
        lets(x&hh1&hh2&hh3): h3.
        exists* x.
      *
        forwards* h3: IHTyp2 h2.
        lets(x&hh1&hh2&hh3): h3.
        exists* x.
    +
      inverts Typ1 as h4 h5 h6 h7. 
      inverts h6 as h8 h9.
      inverts h9 as h9 h10.
      inverts h9 as h9 h11.
      inverts h11 as h11 h12 h13.
      inverts h9 as h9.
      forwards* h14: pattern_ref_consist h2.
      inverts h14 as h14.
      forwards* h15:consist_regular h9.
      forwards* h16:consist_regular h14.
      lets well':well.
      inverts well as h17 h18. 
      inverts h18 as h18 h19.
      rewrite h18 in *.
      forwards*h20: h19 l0.
      forwards*h22: sto_ok_value l0 h17.
      forwards* h21: principle_typ_inf h20.
      rewrite h21 in *.
      forwards* h23: pattern_ref_uniq H h2.
      inverts h23.
      exists P. split*. split*.
      eapply typ_rts.
      rewrite h18; auto.
      apply~ typ_anno.
      apply typ_consist with (A := A0); eauto.
      (* inverts Typ1 as h4 h5 h6 h7. 
      inverts h6 as h8 h9.
      inverts h9 as h9 h10.
      inverts h9 as h9 h11.
      inverts h11 as h11 h12 h13.
      inverts h9 as h9.
      forwards* h14: pattern_ref_consist H8.
      inverts h14 as h14.
      forwards* h15:consist_regular h9.
      forwards* h16:consist_regular h14.
      lets well':well.
      inverts well as h17 h18. 
      inverts h18 as h18 h19.
      rewrite h18 in *.
      forwards*h20: h19 l0.
      forwards*h22: sto_ok_value l0 h17.
      forwards* h21: principle_typ_inf h20.
      rewrite h21 in *.
      forwards* h23: Casts_preservation h3.
      exists P. split*. split*.
      forwards* h24: length_replace l0 v2' mu.
      forwards* h25: assign_pres_store_typing h23.
      forwards*: Casts_prv_value h3. *)
  - (* val *)
     inverts Red as h1 h2 h3; try solve[destruct F in *; unfold fill in *; inverts* h3].
  -
    inverts Red as h1 h2 h3; try solve[destruct F in *; unfold fill in *; inverts* h3].
    +
      destruct F; unfold fill in *; inverts* h3; simpl in *.
      *
      forwards* h3: step_not_ires h2.
      *
      forwards* h3: IHTyp h2.
      lets(x&hh1&hh2&hh3): h3.
      exists x.
      splits; auto.
      pick fresh y and apply typ_absv; auto.
      forwards h4:H y; auto.
      forwards h5: store_weakening hh1 h4.
      apply h5.
      auto.
    +
      exists* P. split*. split*.
      pick_fresh x.
      rewrite* (@subst_exp_intro x).
      apply* typing_subst_simpl_ee.
  -
    inverts Red as h1 h2 h3; try solve[destruct F in *; unfold fill in *; inverts* h3].
    +
      destruct F; unfold fill in *; inverts* h3; simpl in *.
      *
      forwards* h3: step_not_rv h2.
      *
      lets ok1: well.
      inverts well as h4 h5.
      inverts h5 as h5 h6.
      forwards* h3: IHTyp h2.
      lets(x&hh1&hh2&hh3): h3.
      lets ok2: hh3.
      inverts hh3 as hh4 hh5.
      inverts hh5 as hh5 hh6.
      exists* x.
      splits*.
      apply typ_rts.
      forwards* hh7: length_extends hh1.
      forwards* hh8: extends_lookup hh1.
      rewrite hh8; auto.
    +
      lets well':well.
      inverts well as h17 h18. 
      inverts h18 as h18 h19.
      rewrite h18 in *.
      forwards*h20: h19 l.
      forwards*h22: sto_ok_value l h17.
      forwards* h24: length_replace l e2 mu.
      forwards* h25: assign_pres_store_typing Typ.
Qed.


(* ********************************************************************** *)
(** ** Progress (16) *)

Lemma subst_type: forall x y A,
  type A ->
  type (subst_tt (t_fvar y) x A).
Proof.
  introv ty.
  forwards*: tsubst_typ_type ty.
Qed.


Lemma meet_subst: forall t1 t2 t3 x y,
 meet t1 t2 t3 ->
 meet (subst_tt (t_fvar y) x  t1) (subst_tt (t_fvar y) x  t2) (subst_tt (t_fvar y) x t3).
Proof.
  introv ed.
  inductions ed; simpl in *; eauto; try solve[
    forwards*: subst_type H
  ].
  -
    destruct(x0 == x); try solve[inverts* e];eauto.
  -
     pick fresh z and apply me_all.
     forwards* h1: H0 z.
     rewrite 3 tsubst_typ_open_typ_wrt_typ_var; eauto.
Qed.



Lemma meet_progress: forall E A B,
 consist E A B ->
 exists C, meet A B C.
Proof.
  introv sm.
  inductions sm; try solve[exists*];
  try solve[inverts IHsm1; inverts* IHsm2]; 
  try solve[inverts IHsm; eauto].
  -
    pick fresh y.
    forwards* h1: H0 y.
    inverts h1 as h1.
    exists (t_all (close_typ_wrt_typ y x)).
    pick fresh z and
    apply me_all.
    forwards* h2:  meet_subst y z h1.
    forwards* h3: tsubst_typ_spec x z y.
    rewrite h3 in h2.
    rewrite (@tsubst_typ_intro y); eauto.
    rewrite (@tsubst_typ_intro y B ); eauto.
Qed.




Lemma Cast_progress: forall P p A A' mu,
    P |== mu ->
    pvalue p -> typing nil P p Chk A' -> 
    meet (dynamic_type p) A A' ->
    exists r, Cast (p,mu) A' r.
Proof.
  introv well Val Typ mt. 
  inductions Val; intros; simpl in *; eauto.
  -
    inverts Typ as typ1 typ2.
    inverts typ2 as typ2.
    inverts typ2 as typ2 typ3.
    forwards* h2: typing_regular typ3.
    inverts typ3 as typ3.
    forwards* h1: consist_decidable (t_arrow A0 B) A'.
  -
    inverts Typ as typ1 typ2.
    inverts typ2 as typ2.
    inverts typ2 as typ2 typ3.
    forwards* h2: typing_regular typ3.
    inverts typ3 as typ3.
    forwards* h1: consist_decidable (t_all A0) A'.
  -
    inverts Typ as typ1 typ2.
    inverts typ2 as typ2.
    inverts typ2 as typ2 typ3.
    forwards* h2: typing_regular typ3.
    inverts typ3 as typ3 typ4 typ5.
    inverts well as h3 h4.
    inverts h4 as h4 h5.
    rewrite h4 in *.
    forwards* h6: sto_ok_value h3.
    forwards* h7: h5 l.
    forwards* h8: principle_typ_inf h7.
    rewrite <- h8 in *.
    forwards* h1: consist_decidable (t_ref (dynamic_type (store_lookup l mu))) A'.    
Qed.


Lemma Casts_progress1: forall P v A B mu,
    P |== mu ->
    value v -> 
    typing nil P v Chk B -> 
    wf_typ nil A ->
    exists r, Castv (v,mu) A r.
Proof.
  introv well Val Typ ty.
  inverts Val as h1 h2.
  inverts Typ as h4 h5.
  inverts h5 as h5 h6 h7 h8.
  inverts h7 as h7 h9; try solve[inverts h6].
  forwards* h10: pprinciple_typ_inf h9.
  forwards* h11: typing_regular h9.
  rewrite <- h10 in *.
  forwards* h3: consist_decidable (dynamic_type u) A.
  inverts h3 as h12 h13.
  inverts h12 as h12; eauto.
  -
    forwards* h14: meet_progress h12.
    inverts h14 as h14.
    forwards* h17: meet_wft h14.
    forwards* h16: meet_sim h14.
    forwards* h15: Cast_progress h14.
    inverts h15 as h15; eauto.
    destruct x0; eauto. 
Qed.




Lemma Castv_prv_value1: forall v A0 A v' mu P,
 P |== mu ->
 wf_typ empty A ->
 value v -> Castv (v,mu) A ((r_e v')) 
     -> typing nil P v Chk A0 -> value v'.
Proof with auto.
  introv well wf1 val tlist typ.
  forwards* h1: Casts_preservation1 tlist.
  inverts tlist as h2 h3; try solve[inverts h3].
  inverts h1 as h4 h5; eauto. 
Qed.


Lemma fill_appl : forall e1 e2,
  (e_app e1 e2) = (fill (appCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_appr : forall e1 e2,
  (e_app e1 e2) = (fill (appCtxR e1) e2).
Proof.
  intros. eauto.
Qed.


Lemma fill_setl : forall e1 e2,
  (e_set e1 e2) = (fill (setCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_setr : forall e1 e2,
  (e_set e1 e2) = (fill (setCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma fill_ref : forall e,
  (e_ref e) = (fill (refCtx) e).
Proof.
  intros. eauto.
Qed.


Lemma fill_get : forall e,
  (e_get e) = (fill (getCtx) e).
Proof.
  intros. eauto.
Qed.

Lemma fill_tapp : forall e1 A,
  (e_tapp e1 A) = (fill (tappCtx A) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_anno : forall e1 A,
  (e_anno e1 A) = (fill (annoCtx A) e1).
Proof.
  intros. eauto.
Qed.


Lemma ires_decidable: forall e,
  expr e ->
  ires e \/ not (ires e).
Proof.
  introv ee.
  inductions ee; 
  try solve [right; unfold not; intros nt; inverts nt];
  try solve[left*].
Qed.



Lemma pvalue_decidable: forall e,
 expr e -> pvalue e \/ not (pvalue e).
Proof.
  introv lc.
  inductions lc; 
  try solve [right; unfold not; intros nt; inverts nt];
  try solve[left*].
  -
    inverts IHlc.
    +
    inverts* H0;right; unfold not; intros nt; inverts nt.
    +
    inductions lc;
    try solve [right; unfold not; intros nt; inverts nt as nt; inverts* nt];
    try solve[left*].
    *
      inductions H;try solve[right; unfold not; intros nt; inverts nt as nt; inverts* nt]; try solve[left*].
    *
      forwards* h1: ires_decidable e.
      inverts h1 as h1; try solve[right; unfold not; intros nt; inverts nt as nt; inverts* nt]; try solve[left*].
      inverts h1 as h1.
      --
      inverts H0;
      try solve[right; unfold not; intros nt; inverts nt].
      inverts H;
      try solve[right; unfold not; intros nt; inverts nt];
      try solve[left*].
      --
      inverts H0;
      try solve[right; unfold not; intros nt; inverts nt].
      inverts H;
      try solve[right; unfold not; intros nt; inverts nt];
      try solve[left*].
Qed.


Lemma value_decidable: forall e,
 expr e -> value e \/ not (value e).
Proof.
  introv exp.
  inductions exp; try 
  solve[right; unfold not; intros nt; inverts* nt].
  forwards*: pvalue_decidable exp.
  inverts* H0; try 
  solve[right; unfold not; intros nt; inverts* nt].
Qed.



Lemma pattern_type_abs: forall A B,
 type A ->
 pattern_abs A B -> 
 type B.
Proof.
  introv ty pa.
  inverts* pa; eauto.
Qed.

Lemma pattern_type_all: forall A B,
 type A ->
 pattern_all A B -> 
 type B.
Proof.
  introv ty pa.
  inverts pa; auto.
Qed.

Lemma pattern_type_ref: forall A B,
 type A ->
 pattern_ref A B -> 
 type B.
Proof.
  introv ty pa.
  inverts* pa; eauto.
Qed.


Lemma ptype_inf: forall G u P dir A,
 pvalue u ->
 typing G P u dir A ->
 wf_typ G (dynamic_type u).
Proof.
 introv val typ.
 destruct dir.
 -
   forwards* h1: pprinciple_typ_inf typ.
   rewrite h1 in *.
   forwards*: typing_regular typ.
 -
   inverts typ as h1 h2; try solve[inverts val].
   forwards* h3: pprinciple_typ_inf h2.
   rewrite h3 in *.
   forwards*: typing_regular h2.
Qed.


Lemma progress : forall P mu e dir T,
  P |== mu ->
  typing nil P e dir T ->
  value e \/ (exists r mu', step (e, mu) (r, mu')) \/ (ires e).
Proof.
  introv wel Typ.
  lets Typ': Typ.
  inductions Typ;
    try solve [left*];
    try solve [right*];
    try solve [inverts* wel];
    try solve [inverts* H0]; eauto. 
  - (* app *)
    right. 
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp1.
    lets* [Val2 | [[e2' Red2] | abs2]]: IHTyp2.
    +
      inverts Val1 as val1.
      forwards* wf1: typing_regular Typ1.
      inverts Typ1 as h1 h2 h3 h4.
      forwards* h5: ptype_inf h3.
      forwards* h6: consist_decidable (dynamic_type u) (t_arrow t_dyn t_dyn).
      inverts h6 as h6 h7; eauto.
      lets wl: wel.
      inverts wel as wl1 wl2.
      inverts h6 as h6; eauto.
      *
        inverts h2 as h2; try solve[inverts h6].
        inverts h3 as h3 h8; try solve[inverts val1].
        forwards* h9: typing_regular h8.
      *
        inverts H as h7; eauto.
        inverts h2; simpl in *;inverts h5;try solve[inverts h4;
        simpl in *; exfalso; apply h6; auto];
        try solve[exfalso; apply h6; eauto].
    +
      inverts Val1 as val1.
      forwards* wf1: typing_regular Typ1.
      inverts Typ1 as h1 h2 h3 h4.
      forwards* h5: ptype_inf h3.
      forwards* h6: consist_decidable (dynamic_type u) (t_arrow t_dyn t_dyn).
      inverts h6 as h6 h7; eauto.
      lets wl: wel.
      inverts wel as wl1 wl2.
      inverts h6 as h6; eauto.
      *
        inverts h2 as h2; try solve[inverts h6].
        inverts h3 as h3 h8; try solve[inverts val1].
        forwards* h9: typing_regular h8.
      *
        inverts H as h7; eauto.
        inverts h2; simpl in *;inverts h5;try solve[inverts h4;
        simpl in *; exfalso; apply h6; auto];
        try solve[exfalso; apply h6; eauto].
    +
      inverts Val1 as val1.
      forwards* wf1: typing_regular Typ1.
      inverts Typ1 as h1 h2 h3 h4.
      forwards* h5: ptype_inf h3.
      forwards* h6: consist_decidable (dynamic_type u) (t_arrow t_dyn t_dyn).
      inverts h6 as h6 h7; eauto.
      lets wl: wel.
      inverts wel as wl1 wl2.
      inverts h6 as h6; eauto.
      *
        inverts h2 as h2; try solve[inverts h6].
        inverts h3 as h3 h8; try solve[inverts val1].
        forwards* h9: typing_regular h8.
      *
        inverts H as h7; eauto.
        inverts h2; simpl in *;inverts h5;try solve[inverts h4;
        simpl in *; exfalso; apply h6; auto];
        try solve[exfalso; apply h6; eauto].
    +
      left.
      inverts* Red1.
      rewrite fill_appl. destruct e1'; exists*.
    +
      inverts abs1 as h1 h2; try solve[inverts Typ1].
  - (* anno *)
    right. 
    left.
    lets wl: wel.
    inverts wl as wl1 wl2.
    lets* [Val | [[e1' Red] | abs]]: IHTyp.
    +
      forwards* h1: typing_regular Typ.
      forwards* h2: Casts_progress1 e A.
      inverts h2 as h2; eauto.
    +
      inverts* Red.
      rewrite fill_anno. destruct e1'; exists*.
    +
      forwards* hh1: typing_regular Typ.
      inverts hh1 as hh1 hh2.
      inverts hh2 as hh2 hh3.
      inverts abs as h1; 
      try solve[inverts Typ as h2 h3; try solve[inverts h3]; eauto].
  - (* tapp *)
     right. 
    lets* [Val | [[e' Red] | abs]]: IHTyp.
    +
       inverts Val as h1 h2. 
       inverts Typ as h3 h4 h5 h6.
       forwards* h7: ptype_inf h5.
       forwards* h8: consist_decidable (dynamic_type u) (t_all t_dyn).
       inverts h8 as h8 h9.
       lets wl: wel.
       inverts wel as wl1 wl2.
       inverts h8 as h8; eauto.
       *
         inverts h4 as h4; try solve[inverts h8]; eauto.
       *
         inverts* H0.
         inverts h4 as h4; try solve[inverts h8]; eauto;simpl in *;
         try solve[exfalso; apply h8; eauto];
         try solve[inverts h6].
    +
      left.
      inverts Red.
      rewrite fill_tapp.  destruct e'; exists*.
    +
      inverts abs; try solve[inverts Typ; eauto].
  - (* ref *)
     right. 
     left.
    lets* [Val | [[e' Red] | abs]]: IHTyp.
    + inverts* wel.
    +
    inverts* Red. 
    rewrite fill_ref.  destruct e'; exists*.
    +
    inverts abs; try solve[inverts Typ; eauto].
  - (* get *)
    right. 
    left.
    lets* [Val | [[e' Red] | abs]]: IHTyp.
    +
    inverts Val as h1 h2. 
    inverts Typ as h3 h4 h5 h6.
    forwards* h7: ptype_inf h5.
    forwards* h8: consist_decidable (dynamic_type u) (t_ref t_dyn).
    inverts h8 as h8 h9.
    lets wl: wel.
    inverts wel as wl1 wl2.
    inverts h8 as h8; eauto.
    *
      inverts h4 as h4; try solve[inverts h8]; eauto.
    *
      inverts* H.
      inverts h4 as h4; try solve[inverts h8]; eauto;simpl in *;
      try solve[exfalso; apply h8; eauto];
      try solve[inverts h6].
    +
    inverts Red. 
    rewrite fill_get. destruct e'; exists*.
    +
    inverts abs; try solve[inverts Typ; eauto].
  - (* set *)
   right. left.
   lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp1.
   lets* [Val2 | [[e2' Red2] | abs2]]: IHTyp2.
   +
    inverts Val1 as val1.
    forwards* wf1: typing_regular Typ1.
    inverts Typ1 as h1 h2 h3 h4.
    forwards* h5: ptype_inf h3.
    forwards* h6: consist_decidable (dynamic_type u) (t_ref t_dyn).
    inverts h6 as h6 h7; eauto.
    lets wl: wel.
    inverts wel as wl1 wl2.
    inverts h6 as h6; eauto.
    *
      inverts h2 as h2; try solve[inverts h6].
      inverts h3 as h3 h8; try solve[inverts val1].
      forwards* h9: typing_regular h8.
    *
      inverts H as h7; eauto.
      inverts h2; simpl in *;inverts h5;try solve[inverts h4;
      simpl in *; exfalso; apply h6; auto];
      try solve[exfalso; apply h6; eauto].   
   +
     inverts Val1 as val1.
    forwards* wf1: typing_regular Typ1.
    inverts Typ1 as h1 h2 h3 h4.
    forwards* h5: ptype_inf h3.
    forwards* h6: consist_decidable (dynamic_type u) (t_ref t_dyn).
    inverts h6 as h6 h7; eauto.
    lets wl: wel.
    inverts wel as wl1 wl2.
    inverts h6 as h6; eauto.
    *
      inverts h2 as h2; try solve[inverts h6].
      inverts h3 as h3 h8; try solve[inverts val1].
      forwards* h9: typing_regular h8.
    *
      inverts H as h7; eauto.
      inverts h2; simpl in *;inverts h5;try solve[inverts h4;
      simpl in *; exfalso; apply h6; auto];
      try solve[exfalso; apply h6; eauto].  
   +
     inverts Val1 as val1.
    forwards* wf1: typing_regular Typ1.
    inverts Typ1 as h1 h2 h3 h4.
    forwards* h5: ptype_inf h3.
    forwards* h6: consist_decidable (dynamic_type u) (t_ref t_dyn).
    inverts h6 as h6 h7; eauto.
    lets wl: wel.
    inverts wel as wl1 wl2.
    inverts h6 as h6; eauto.
    *
      inverts h2 as h2; try solve[inverts h6].
      inverts h3 as h3 h8; try solve[inverts val1].
      forwards* h9: typing_regular h8.
    *
      inverts H as h7; eauto.
      inverts h2; simpl in *;inverts h5;try solve[inverts h4;
      simpl in *; exfalso; apply h6; auto];
      try solve[exfalso; apply h6; eauto].  
   +
     inverts Red1.
     forwards*: typing_regular Typ2.
    rewrite fill_setl. destruct e1'; exists*.
   +
     inverts abs1 as h1 h2; try solve[inverts Typ1].
  -
    forwards* h0: typing_regular Typ'.
    inverts h0 as h1 h2.
    inverts h2 as h2 h3.
    inverts h2 as h2 h4.
    lets ok: wel.
    right. left.
    lets* [Val2 | [[e2' Red2] | abs2]]: IHTyp;
    inverts* ok.
    +
     inverts Red2.
     rewrite fill_appr. 
     destruct e2'; exists*.
    +
    inverts abs2 as h1 h2; try solve[inverts Typ].
  -
    forwards* h0: typing_regular Typ'.
    inverts h0 as h1 h2.
    inverts h2 as h2 h3.
    inverts h2 as h2 h4.
    lets ok: wel.
    right. left.
    lets* [Val2 | [[e2' Red2] | abs2]]: IHTyp;
    inverts* ok.
    +
     inverts Red2.
     rewrite fill_setr. 
     destruct e2'; exists*.
    +
    inverts abs2 as h1 h2; try solve[inverts Typ].
  Unshelve.
  apply {}.
Qed.