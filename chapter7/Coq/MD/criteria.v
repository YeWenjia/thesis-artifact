Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Deterministic
        Type_Safety
        Typing
        Key_Properties
        Subtyping_inversion.

Require Import List. Import ListNotations.
Require Import Lia.
Require Import Strings.String.


Lemma tpre_refl: forall A,
  tpre A A.
Proof.
   inductions A; eauto.
Qed.


Lemma sim_refl: forall A,
 sim A A.
Proof.
  introv.
  inductions A; eauto.
Qed.


Lemma precise_lc: forall e1 e2,
 precise e1 e2 ->
 lc_exp e1 ->
 lc_exp e2.
Proof.
  introv ep lc.
  inductions ep; intros; eauto;
  try solve [inverts* lc];
  try solve[inverts* lc; inverts* H1].
Qed.


Lemma precise_llc: forall e1 e2,
 precise e1 e2 ->
 lc_exp e1 /\
 lc_exp e2.
Proof.
  introv ep.
  inductions ep; intros; eauto;try solve[splits*].
  - splits*.
    pick fresh x.
    forwards* h1: H0 x. inverts* h1.
    forwards*: lc_e_abs_exists H1.
    pick fresh x.
    forwards*: H0 x. inverts* H1.
    forwards*: lc_e_abs_exists H3.
  - splits*.
    pick fresh x.
    forwards* h1: H0 x. inverts h1 as h1 h2.
    forwards*: lc_e_fix_exists h1.
    pick fresh x.
    forwards* h1: H0 x. inverts h1 as h1 h2.
    forwards*: lc_e_fix_exists h2.
Qed.


Lemma precise_lc2: forall e1 e2,
 precise e1 e2 ->
 lc_exp e2 ->
 lc_exp e1.
Proof.
  introv ep lc. gen e1.
  inductions lc; intros; eauto;
  try solve [inverts ep; eauto].
Qed.


Lemma precise_open: forall e1 e2 u1 u2 x,
 precise e1 e2 ->
 precise u1 u2 ->
 lc_exp u1 ->
 lc_exp u2 ->
 precise [x~> u1]e1 [x~>u2]e2.
Proof.
  introv ep1 ep2 lc1 lc2. gen u1 u2 x.
  inductions ep1; intros; 
  simpl; eauto.
  -  destruct (x == x0); eauto.
  - pick fresh x0.
      apply precise_abs with (L := union L
      (union (singleton x)
         (union (fv_exp e1)
            (union (fv_exp e2) (union (fv_exp u1) (fv_exp u2)))))); intros; auto.
         forwards*: H0 x1 ep2 x. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto.
  - pick fresh x0.
      apply precise_fix with (L := union L
      (union (singleton x)
         (union (fv_exp e1)
            (union (fv_exp e2) (union (fv_exp u1) (fv_exp u2)))))); intros; auto.
         forwards*: H0 x1 ep2 x. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto.
Qed.



Lemma Typing_c_rename : forall (x y : atom) E e T1 T2,
  well T1 ->
  x `notin` fv_exp e -> y `notin` (dom E `union` fv_exp e) ->
  Typing ((x , T1) :: E) (open_exp_wrt_exp e (e_var_f x)) Inf T2 ->
  Typing ((y , T1) :: E) (open_exp_wrt_exp e (e_var_f y)) Inf T2.
Proof.
  intros x y E e T1 T2 well Fr1 Fr2 H.
  destruct (x == y).
  Case "x = y".
    subst; eauto.
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



Lemma ityp_tpre: forall t1 l t2,
 tpre t1 t2 ->
 ityp t2 l ->
 ityp t1 l.
Proof.
  introv tp it. gen l.
  inductions tp; intros; try solve[inverts* it];eauto.
Qed.



Lemma nityp_tpre: forall t1 l t2,
 tpre t1 t2 ->
 not(ityp t1 l) ->
 not(ityp t2 l).
Proof.
  introv tp it. gen l.
  inductions tp; intros; try solve[unfold not; intros nt;inverts* nt];eauto.
Qed.



Lemma tpre_dyn_dyn: forall A B,
 dynamic A ->
 tpre A B ->
 dynamic B.
Proof.
  introv dyn tp.
  inductions tp; intros; try solve[inverts dyn];eauto.
  inverts dyn.
  forwards*: IHtp1 H0.
  forwards*: IHtp2 H0.
Qed.

Lemma tpre_ddyn_ddyn: forall A B,
 ddyn A ->
 tpre A B ->
 ddyn B.
Proof.
  introv dyn tp.
  inductions tp; intros; try solve[inverts dyn];eauto.
  inverts dyn.
  forwards*: IHtp1 H0.
  forwards*: IHtp2 H0.
Qed.


Lemma tpre_get_ty: forall t1 t2 l t3 t4,
 tpre t1 t2 ->
 get_ty t1 l t3 ->
 get_ty t2 l t4 ->
 tpre t3 t4.
Proof.
  introv tp gt1 gt2. gen l t3 t4.
  inductions tp; intros; 
  try solve[inverts* gt1; inverts gt2];
  try solve[inverts* gt2];
  try solve[inverts gt1; inverts* H0];eauto.
  -
    inverts* gt1; inverts* gt2.
    forwards*: ityp_tpre l tp2.
    forwards*: nityp_tpre l tp1.
    forwards*: ityp_tpre l tp1.
    exfalso; apply H; eauto.
    forwards*: ityp_tpre l tp2.
    exfalso; apply H; eauto.
  -
    inverts* gt1; inverts* gt2.
    inverts H0.
Qed.


Lemma env_less_precise_binds : forall x A E F,
    binds x A E ->
    cpre E F ->
    exists B, binds x B F /\ tpre A B.
Proof.
  introv bind cp.
  inductions cp; try solve[inverts* bind];eauto.
  inverts* bind. inverts* H0.
  forwards*: IHcp.
  inverts* H1.
Qed.


Lemma cpre_notin: forall x E F,
 x # E ->
 cpre E F ->
 x # F.
Proof.
  introv uq cp.
  inductions cp; try solve[inverts* uq]; eauto.
Qed.



Lemma cpre_uniq: forall E F,
 uniq E ->
 cpre E F ->
 uniq F.
Proof.
  introv uq cp.
  inductions cp; try solve[inverts* uq]; eauto.
  inverts* uq.
  forwards*: IHcp.
  forwards*: cpre_notin cp.
Qed.



(* Lemma tpre_toplike: forall C A B,
 topLike A ->
 tpre A B ->
 csub C B.
Proof.
  introv tl tp. gen C.
  inductions tp; intros; try solve[inverts* tl];eauto.
Qed. *)


Lemma precise_csub : forall A1 B1 A2 B2,
  csub A1 B1 ->
  tpre A1 A2 ->
  tpre B1 B2 ->
  csub A2 B2.
Proof.
  introv s1 tp1 tp2. gen A2 B2.
  inductions s1; intros;try solve[inverts* tp1]; 
  try solve[inverts* tp2]; try solve[inverts* tp2; inverts* tp1]; eauto.
Qed.

Lemma dmatch_tpre2: forall t1 t2 t3 t4 t5 t6,
 tpre t1 t2 ->
 dmatch t1 (t_arrow t3 t4) ->
 dmatch t2 (t_arrow t5 t6) ->
 tpre t3 t5 /\ tpre t4 t6.
Proof.
  introv tp dm1 dm2. gen t3 t4 t5 t6.
  inductions tp; intros; eauto;
  try solve[inverts* dm1];
  try solve[inverts* dm2];
  try solve[inverts* dm1; inverts* dm2].
Qed.


Lemma binds_tpre: forall x T T' E1 E2,
 uniq E1 ->
 uniq E2 ->
 cpre E1 E2 ->
 binds x T E1 ->
 binds x T' E2 ->
 tpre T T'.
Proof.
  introv uq1 uq2 cp bind1 bind2. gen x T T'.
  inductions cp; intros;try solve[inverts uq1;inverts uq2;inverts bind1;inverts* bind2].
  inverts uq1;inverts uq2;inverts bind1;inverts* bind2;
  try solve[inverts* H0;inverts* H1]; try solve[inverts* H0];
  try solve[inverts* H1].
  inverts* H0. 
  exfalso. apply H6;eauto.
  inverts H1.
  exfalso. apply H4;eauto.
Qed.


Lemma tpre_dis: forall A B A1 B1,
 disjoint A B ->
 tpre A A1 ->
 tpre B B1 ->
 disjoint A1 B1.
Proof.
  introv dis tp1 tp2. gen A1 B1.
  inductions dis;intros; try solve[inverts* tp1];
  try solve[inverts* tp2];
  try solve[inverts* tp1;inverts* tp2].
Qed.



Lemma tpre_well: forall A B,
 well A ->
 tpre A B ->
 well B.
Proof.
  introv well tp.
  inductions tp; try solve[inverts* well].
  inverts* well.
  forwards*: tpre_dis tp1 tp2.
Qed.



Lemma typin_csub: forall A B C,
 csub A B ->
 typin A C ->
 csub C B.
Proof.
  introv sub tin. gen C.
  inductions sub; intros; try solve [inductions tin; eauto];eauto.  
Qed.



Lemma tpre_ityp_dyn: forall t1 t2 l,
 ityp t1 l ->
 tpre t1 t2 ->
 ityp t2 l \/ dynamic t2.
Proof.
  introv it tp.
  inductions tp; try solve[inverts* it].
Qed.


Lemma get_ty_nityp_dyn: forall t1 l t2,
 get_ty t1 l t2 ->
 not(ityp t1 l) ->
 dynamic t1.
Proof.
  introv gt nity.
  inductions gt; eauto; try solve[exfalso; apply nity; eauto].
Qed.



Lemma tpre_get_ty_progress: forall t1 l t2 t3,
 tpre t1 t2 ->
 get_ty t1 l t3 ->
 exists t4, get_ty t2 l t4 /\ tpre t3 t4.
Proof.
  introv tp gt. gen l t3.
  inductions tp; intros;try solve[inverts* gt;inverts* H0];
  try solve[inverts* gt;inverts* H;try solve[inverts* H0];
  try solve[inverts* H]]; 
  try solve[inverts* gt];eauto.
  inverts* gt; try solve[exists t_dyn; split*;
  apply g_dyn; try solve[unfold not; intros nt; inverts nt];eauto].
  inverts* gt.
  forwards*: IHtp1 H1. inverts H. inverts H0.
  forwards*: nityp_tpre tp2.
  destruct(ityp_decidable C l); eauto.
  forwards*: get_ty_nityp_dyn H.
  exists t_dyn; split*.
  apply g_dyn; try solve[unfold not; intros nt; inverts* nt];eauto.
  forwards*: IHtp2 H5. inverts H. inverts H0.
  forwards*: nityp_tpre tp1.
  destruct(ityp_decidable D l); eauto.
  forwards*: get_ty_nityp_dyn H.
  exists t_dyn; split*.
  apply g_dyn; try solve[unfold not; intros nt; inverts* nt];eauto.
  forwards*: nityp_tpre tp1.
  forwards*: nityp_tpre tp2.
  inverts H0.
  forwards*: tpre_dyn_dyn tp1.
  exists t_dyn; split*.
  apply g_dyn; eauto.
  unfold not; intros nt; inverts* nt.
  forwards*: tpre_dyn_dyn tp2.
  exists t_dyn; split*.
  apply g_dyn; eauto.
  unfold not; intros nt; inverts* nt.
Qed.




Lemma dmatch_tpre: forall t1 t2 t3 t4,
 tpre t1 t4 ->
 dmatch t1 (t_arrow t2 t3) ->
 exists t5 t6, dmatch t4 (t_arrow t5 t6) /\
 tpre t2 t5 /\ tpre t3 t6.
Proof.
  introv tp dm. gen t2 t3.
  inductions tp; intros; eauto;
  try solve[inverts* dm].
Qed.


Theorem precise_type: forall E1 E2 e e' T T',
precise e e' ->
cpre E1 E2 ->  
Typing E1 e Inf T ->
Typing E2 e' Inf T'->
tpre T T'.
Proof.
 introv ep cp Typ1 Typ2.
 gen E1 E2 T T'.
 inductions ep; intros;
 try solve[inverts* Typ1; inverts* Typ2].
 - inverts Typ1. inverts Typ2.
   forwards*: binds_tpre H2 H4.
 - 
   inverts* Typ1.
   inverts* Typ2.
   forwards*: IHep1 H1 H2.
   forwards*: dmatch_tpre2 H4 H7.
 -
   inverts Typ1; inverts Typ2; eauto.
   forwards*: IHep H2 H4.
   forwards*: tpre_get_ty H3 H5.
Qed.



Lemma inf_chk_epre: forall E1 E2 e1 e2 A B,
 precise e1 e2 ->
 E1 ⊢ e1 ⇒ A ->
 E2 ⊢ e2 ⇐ B ->
 exists t,  E2 ⊢ e2 ⇒ t.
Proof.
  introv ep ty1 ty2.
  inverts* ty2.
  -
   inverts ep. inverts ty1.
  -
   inverts ep. inverts ty1.
  -
   inverts ep. inverts* H4.
   inverts ty1. inverts H4.
Qed.



Lemma tpre_chk: forall e1 e2 E1 E2 t t2,
 cpre E1 E2 ->
 precise e1 e2 ->
 Typing E1 e1 Chk t ->
 tpre t t2 ->
 WF E1 ->
 Typing E2 e2 Chk t2.
Proof.
  introv cp ep typ tp wf. gen t t2 E1 E2.
  inductions ep; intros.
  - (* x*)
    inverts typ.
    inverts H.
    forwards*: env_less_precise_binds H5. inverts H. inverts H2.
    forwards*: cpre_uniq cp.
    forwards*: precise_csub H0 H4 tp.
    (* forwards*: tpre_well H4. *)
    forwards*: tpre_well tp.
  - (* top *)
    inverts typ. inverts H.
    forwards*: cpre_uniq cp.
    assert(tpre t_top t_top);eauto.
    forwards*: tpre_well tp.
    forwards*: precise_csub H0 H3 tp.
  - (* int *)
    inverts typ. inverts H.
    forwards*: cpre_uniq cp.
    assert(tpre t_int t_int);eauto.
    forwards*: tpre_well tp.
    forwards*: precise_csub H0 H2 tp.
  - (* lambda *)
    inverts typ; try solve[inverts H1].
    inverts H5.
    +
    inverts tp.
    *
    pick fresh x and apply Typ_abs;eauto.
    (* assert(cpre ((x, A) :: E1) ((x, t_dyn) :: E2));eauto. *)
    *
    pick fresh x and apply Typ_abs;eauto.
    forwards*: tpre_well H5.
    +
    inverts tp.
    pick fresh x and apply Typ_abs;eauto.
  - (* app*)
    inverts typ. inverts H.
    +
      forwards* hh1: Typing_chk H4. inverts hh1.
      forwards* h1: IHep1.
      forwards* h2: inf_chk_epre H4 h1.
      inverts h2 as h2.
      forwards* h3: precise_type ep1 H4 h2.
      forwards* h4: dmatch_tpre h3 H7.
      lets(t4&t5&h5&h6):h4.
      inverts h6 as h61 h62; try solve[inverts h5].
      forwards* h7: IHep2 h61.
      forwards* h8: precise_csub H0 h62 tp.
      forwards*: tpre_well tp.
    + 
      inverts ep1.
      forwards* h1: Typing_chk H3. inverts h1 as h1.
      forwards* hh1: IHep2 h1.
      forwards* hh2: inf_chk_epre H3 hh1.
      inverts hh2 as hh2.
      forwards* h3: precise_type ep2 H3 hh2.
      forwards h5: IHep1 (t_arrow A t) (t_arrow x0 t2) cp; auto.
      forwards h6: Typing_well H3; auto.
      pick fresh yy and apply Typ_abs;eauto.
      inverts h5 as h51 h52 h53; try solve[inverts h51].
      inverts h53. 
      pick fresh y and apply Typ_rt; auto.
  - (* anno *)
    inverts typ. inverts H0.
    forwards*: IHep H.
    forwards*: precise_csub H1 H tp.
    forwards*: tpre_well tp.
  - (* merge *)
    inverts typ. inverts H.
    forwards* h1: Typing_chk H4. inverts h1 as h1.
    forwards* h2: IHep1. 
    forwards* h3: inf_chk_epre ep1 H4 h2.
    inverts h3 as h3.
    forwards* h4: Typing_chk H6. inverts h4 as h4.
    forwards* h5: IHep2 h4. 
    forwards* h7: inf_chk_epre ep2 H6 h5.
    inverts h7 as h7.
    forwards* h8: precise_type H4 h3.
    forwards* h9: precise_type H6 h7.
    assert(tpre (t_and A0 B) (t_and x0 x2)) as h10; auto.
    forwards*: precise_csub  H0 h10 tp.
    forwards*: tpre_well tp.
    forwards*: tpre_dis H7 h8 h9.
  - (* rcd *)
    inverts typ. inverts H.
    forwards* h1: Typing_chk H4. inverts h1 as h1.
    forwards* h2: IHep h1.
    forwards* h3: inf_chk_epre ep H4 h2.
    inverts h3 as h3.
    forwards* h4: precise_type H4 h3.
    assert( t_rcd l A0 <<  t_rcd l x0) as h5; auto.
    forwards*: precise_csub H0 h5 tp.
    forwards*: tpre_well tp.
  - (* proj *)
    inverts typ. inverts H.
    forwards* h1: Typing_chk H5. inverts h1 as h1.
    forwards* h2: IHep h1.
    forwards* h3: inf_chk_epre ep H5 h2.
    inverts h3 as h3.
    forwards* h4: precise_type H5 h3.
    forwards* h5: tpre_get_ty_progress h4 H6.
    lets(t4&gtt&tpp): h5.
    forwards*: precise_csub H0 tpp tp.
    forwards*: tpre_well tp.
  - (* fix *)
    inverts typ as h1; try solve[inverts h1].
    forwards: tpre_well tp; auto.
    pick fresh y and apply Typ_fix; auto.
    forwards h2: H0 y tp ((y, t) :: E1) ((y, t2) :: E2); auto.
Qed.




Theorem SGG_chk: forall e e' T E1 E2,
   precise e e' ->  
   Typing E1 e Chk T ->
   cpre E1 E2 ->
   WF E1 ->
   exists T', Typing E2 e' Chk T' /\ tpre T T'.
Proof.
  introv ep Typ1 cp wf.
  assert(tpre T T).
  apply tpre_refl.
  forwards*: tpre_chk Typ1 H.
Qed.




Theorem SGG_both_gen: forall e e' T E1 E2 dir,
   precise e e' ->  
   Typing E1 e dir T ->
   cpre E1 E2 ->
   WF E1 ->
   exists T', Typing E2 e' dir T' /\ tpre T T'.
Proof.
  introv ep Typ1 cp wf.
  destruct dir.
  -
   forwards* h1: Typing_chk Typ1.
   inverts h1 as h1.
   forwards* h2: SGG_chk ep h1.
   lets(tt1&h3&h4): h2.
   forwards* h5: inf_chk_epre ep Typ1 h3.
   lets(tt2&h6): h5.
   forwards*: precise_type Typ1 h6.
  -
  forwards*: SGG_chk Typ1.
Qed.



Theorem SGG_both: forall e e' T dir,
   precise e e' ->  
   Typing nil e dir T ->
   exists T', Typing nil e' dir T' /\ tpre T T'.
Proof.
  introv ep Typ1.
  forwards*: SGG_both_gen ep Typ1.
Qed.

(* dgg *)

(* Lemma epre_lc: forall e1 e2,
 epre e1 e2 ->
 lc_exp e1 ->
 lc_exp e2.
Proof.
  introv ep lc.
  inductions ep; intros; eauto;
  try solve [inverts* lc];
  try solve[inverts* lc; inverts* H1].
Qed.


Lemma epre_llc: forall e1 e2,
 epre e1 e2 ->
 lc_exp e1 /\
 lc_exp e2.
Proof.
  introv ep.
  inductions ep; intros; eauto;try solve[splits*].
  - splits*.
    pick fresh x.
    forwards*: H0 x. inverts* H3.
    forwards*: lc_e_abs_exists H4.
    pick fresh x.
    forwards*: H0 x. inverts* H3.
    forwards*: lc_e_abs_exists H5.
Qed.


Lemma epre_lc2: forall e1 e2,
 epre e1 e2 ->
 lc_exp e2 ->
 lc_exp e1.
Proof.
  introv ep lc. gen e1.
  inductions lc; intros; eauto;
  try solve [inverts ep; eauto].
Qed.


Lemma epre_open: forall e1 e2 u1 u2 x,
 epre e1 e2 ->
 epre u1 u2 ->
 lc_exp u1 ->
 lc_exp u2 ->
 epre [x~> u1]e1 [x~>u2]e2.
Proof.
  introv ep1 ep2 lc1 lc2. gen u1 u2 x.
  inductions ep1; intros; 
  simpl; eauto.
  -  destruct (x == x0); eauto.
  - pick fresh x0.
      apply ep_abs with (L := union L
      (union (singleton x)
         (union (fv_exp e1)
            (union (fv_exp e2) (union (fv_exp u1) (fv_exp u2)))))); intros; auto.
         forwards*: H0 x1 ep2 x. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto.
Qed. *)



Print Assumptions consub_prop.
Print Assumptions consub_propr.
Print Assumptions Cast_progress.
Print Assumptions step_unique.
Print Assumptions step_unique.
Print Assumptions preservation.
Print Assumptions Progress.
Print Assumptions SGG_both.

























