Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Bool.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Deterministic
        Type_Safety
        Typing.

Require Import List. Import ListNotations.
Require Import Lia.
Require Import Strings.String.



Lemma epre_lc: forall e1 e2,
 epre e1 e2 ->
 lc_exp e1 ->
 lc_exp e2.
Proof.
  introv ep lc. gen e2.
  inductions lc; intros; eauto;
  try solve [inverts ep; eauto].
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


Lemma subst_pvalue : forall p z u,
    lc_exp u ->
    pval p -> pval (subst_exp u z p).
Proof.
  introv lc pval.
  inductions pval; simpl in *; eauto.
  eapply pval_abs; eauto.
  forwards*: subst_exp_lc_exp H lc.
Qed.


Lemma subst_principal : forall p z u,
    lc_exp u ->
    pval p -> dynamic_type (subst_exp u z p) = dynamic_type p.
Proof.
  introv lc pval.
  inductions pval; simpl in *; eauto.
  rewrite IHpval1.
  rewrite IHpval2.
  eauto.
Qed.


Lemma epre_open: forall e1 e2 u1 u2 x,
 epre e1 e2 ->
 epre u1 u2 ->
 lc_exp u1 ->
 lc_exp u2 ->
 epre [x~> u1]e1 [x~>u2]e2 .
Proof.
  introv ep1 ep2 lc1 lc2. gen u1 u2 x.
  inductions ep1; intros; 
  simpl; eauto.
  -  destruct (x == x0); eauto.
  - 
    apply ep_abs with (L := (union L (singleton x))); intros; auto.
    forwards*: H0 x0 ep2 x.
    rewrite subst_exp_open_exp_wrt_exp_var; eauto. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto.
  -
    forwards* h1: subst_pvalue x lc2 H.
    forwards* h2: subst_principal x lc2 H.
    eapply ep_val; eauto.
    rewrite h2 ; eauto.
  -
    forwards* h1: IHep1 ep2 x.
    forwards* h2: fval_subst_fval f2 x u2.
Qed. 


Lemma Typing_c_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv_exp e -> y `notin` (dom E `union` fv_exp e) ->
  Typing ((x , T1) :: E) (open_exp_wrt_exp e (e_var_f x)) Inf T2 ->
  Typing ((y , T1) :: E) (open_exp_wrt_exp e (e_var_f y)) Inf T2.
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
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



Inductive cpre : ctx -> ctx -> Prop :=
  | cp_nil: 
      cpre nil nil
  | cp_cons: forall E F x A1 A2,
      tpre A1 A2 ->
      cpre E F ->
      cpre (cons ( x , A1 )  E) (cons ( x , A2 )  F) 
.

Hint Constructors cpre : core.


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




Lemma dmatch_tpre: forall t1 t2 t3,
 tpre t1 t2 ->
 pattern t1 t3 ->
 exists t4, pattern t2 t4 /\
 tpre t3 t4.
Proof.
  introv tp dm. gen t3.
  inductions tp; intros; eauto;
  try solve[inverts* dm].
Qed.


Lemma dmatch_pro_tpre: forall t1 t2 t3,
 tpre t1 t2 ->
 pattern_pro t1 t3 ->
 exists t4, pattern_pro t2 t4 /\
 tpre t3 t4.
Proof.
  introv tp dm. gen t3.
  inductions tp; intros; eauto;
  try solve[inverts* dm].
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



Lemma dmatch_tpre2: forall t1 t2 t3 t4,
 tpre t1 t2 ->
 pattern t1 t3 ->
 pattern t2 t4 ->
 tpre t3 t4.
Proof.
  introv tp dm1 dm2. gen t3 t4.
  inductions tp; intros; eauto;
  try solve[inverts* dm1];
  try solve[inverts* dm2];
  try solve[inverts* dm1; inverts* dm2].
Qed.


Lemma dmatch_pro_tpre2: forall t1 t2 t3 t4,
 tpre t1 t2 ->
 pattern_pro t1 t3 ->
 pattern_pro t2 t4 ->
 tpre t3 t4.
Proof.
  introv tp dm1 dm2. gen t3 t4.
  inductions tp; intros; eauto;
  try solve[inverts* dm1];
  try solve[inverts* dm2];
  try solve[inverts* dm1; inverts* dm2].
Qed.



Theorem precise_type_gen: forall E1 E2 e e' T T' n,
size_exp e + size_exp e' < n ->
epre e e' ->
cpre E1 E2 ->  
Typing E1 e Inf T ->
Typing E2 e' Inf T'->
tpre T T'.
Proof.
 introv sz ep cp Typ1 Typ2.
 gen E1 E2 T T' e e'.
 inductions n; intros; try solve[lia].
 gen E1 E2 T T'.
 inductions ep; intros;
 try solve[inverts Typ1; inverts Typ2;auto].
 - inverts Typ1. inverts Typ2.
   forwards*: binds_tpre H2 H4.   
 - 
   inverts Typ1.
   +
   inverts Typ2.
   *
     forwards*: IHep1 H1 H2.
     simpl in *; lia.
     forwards: dmatch_tpre2 H3 H6; auto.
     inverts* H0.
   *
     inverts ep1; try solve[inverts H1].
   +
     inverts ep1 as h1 h2.
     inverts Typ2 as h3 h4 h5; try solve[inverts h3].
     forwards h6: IHn cp H3 h2 h4; auto.
     simpl in *;lia.
     inverts* h6.
 -
   inverts Typ1.
   inverts Typ2.
   forwards*: IHep1 H2 H4.
   simpl in *; lia.
   forwards*: IHep2 H3 H5.
   simpl in *; lia.
 -
   inverts Typ1.
   inverts Typ2.
   forwards*: IHep H0 H1.
   simpl in *; lia.
   forwards*: dmatch_pro_tpre2 H2 H4.
   inverts* H3.
 -
   inverts Typ1.
   inverts Typ2.
   forwards*: IHep H0 H1.
   simpl in *; lia.
   forwards: dmatch_pro_tpre2 H2 H4; auto.
   inverts* H3.
Qed.


Theorem precise_type: forall E1 E2 e e' T T',
epre e e' ->
cpre E1 E2 ->  
Typing E1 e Inf T ->
Typing E2 e' Inf T'->
tpre T T'.
Proof.
 introv ep cp Typ1 Typ2.
 eapply precise_type_gen; eauto.
Qed.


Theorem precise_type2: forall E1 E2 e e' T T',
sepre e e' ->
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
   inverts* Typ1; try solve[inverts* ep1].
   inverts* Typ2; try solve[inverts* ep1].
   forwards*: IHep1 H1 H2.
   forwards*: dmatch_tpre2 H3 H6.
    inverts* H0.
 -
   inverts Typ1.
   inverts Typ2.
   forwards*: IHep H0 H1.
   forwards*: dmatch_pro_tpre2 H2 H4.
   inverts* H3.
 -
   inverts Typ1.
   inverts Typ2.
   forwards*: IHep H0 H1.
   forwards*: dmatch_pro_tpre2 H2 H4.
   inverts* H3.
Qed.




Lemma inf_chk_epre: forall E1 E2 e1 e2 A B,
 epre e1 e2 ->
 E1 ⊢ e1 ⇒ A ->
 E2 ⊢ e2 ⇐ B ->
 exists t,  E2 ⊢ e2 ⇒ t.
Proof.
  introv ep ty1 ty2.
  inverts* ty2.
  -
   inverts ep. inverts ty1.
  -
   inverts ep. inverts* H4.
   inverts ty1. inverts H4.
Qed.



Lemma inf_chk_epre2: forall E1 E2 e1 e2 A B,
 sepre e1 e2 ->
 E1 ⊢ e1 ⇒ A ->
 E2 ⊢ e2 ⇐ B ->
 exists t,  E2 ⊢ e2 ⇒ t.
Proof.
  introv ep ty1 ty2.
  inverts* ty2.
  -
   inverts ep. inverts ty1.
  -
   inverts ep. inverts* H4.
   inverts ty1. inverts H4.
Qed.



Lemma tpre_chk: forall e1 e2 E1 E2 t t2,
 cpre E1 E2 ->
 sepre e1 e2 ->
 Typing E1 e1 Chk t ->
 tpre t t2 ->
 Typing E2 e2 Chk t2.
Proof.
  introv cp ep typ tp. 
  gen E1 E2 t t2.
  inductions ep; intros.
  - (* x *)
    inverts typ.
    inverts H.
    forwards*: env_less_precise_binds H4. inverts H. inverts H1.
    forwards*: cpre_uniq cp.
    forwards*: epre_sim H0 H3 tp.
  - (* lit *)
    inverts typ. inverts H.
    forwards*: cpre_uniq cp.
    assert(tpre t_int t_int);eauto.
    forwards*: epre_sim H0 H1 tp.
  - (* abs *)
    inverts typ; try solve[inverts H1].
    inverts H2.
    +
    inverts tp.
    *
    pick fresh x and apply Typ_abs;eauto.
    assert(cpre ((x, A) :: E1) ((x, t_dyn) :: E2));eauto.
    *
    pick fresh x and apply Typ_abs;eauto.
    assert(cpre ((x, A) :: E1) ((x, C) :: E2));eauto.
    +
    inverts tp.
    pick fresh x and apply Typ_abs;eauto.
    assert(cpre ((x, t_dyn) :: E1) ((x, t_dyn) :: E2));eauto.
  - (* app *)
    inverts typ. inverts H; try solve[inverts ep1].
    +
    forwards*: Typing_chk H3. inverts H.
    forwards* h1: IHep1.
    inverts h1; try solve[inverts ep1; inverts* H3].
    *
      forwards* h3: precise_type2 ep1 H3 H.
      forwards* h4: dmatch_tpre h3 H5.
      lets(t4&h5&h6):h4.
      inverts h6; try solve[inverts h5].
      forwards* h2: IHep2 H8.
      forwards*: epre_sim H0 H10 tp.
    *
      inverts ep1.
      inverts* H9. inverts* H3.
      inverts* H9.
    + 
      inverts ep1.
      forwards* h1: Typing_chk H3. inverts h1 as h1.
      forwards*: IHep2 h1.
      inverts h1; try solve[inverts* H3];
      try solve[inverts* H3; inverts* H7].
      inverts H; try solve[inverts* ep2; inverts* H3];
      try solve[inverts* ep2; inverts* H9; inverts H3; inverts H9].
      forwards* h3: precise_type2 ep2 H1 H5.
      forwards* h4: inference_unique H3 H1. subst.
      assert(tpre (t_arrow A0 t) (t_arrow A1 t2)); auto.
      forwards* h5: IHep1 H.
      inverts* h5; try solve[inverts* H7].
      inverts* H8.
  - 
    inverts typ. inverts H0.
    forwards*: IHep H4 H.
    forwards*: epre_sim H1 H tp.
  -
    inverts typ. inverts H.
    forwards* h1: Typing_chk H4. inverts h1.
    forwards* h3: IHep1.
    forwards* h2: Typing_chk H5. inverts h2.
    forwards* h4: IHep2.
    forwards* hh3: inf_chk_epre2 ep1 H4 h3.
    inverts hh3 as hh3.
    forwards* hh4: inf_chk_epre2 ep2 H5 h4.
    inverts hh4 as hh4.
    forwards* h5: precise_type2 ep1 H4 hh3.
    forwards* h6: precise_type2 ep2 H5 hh4.
    assert(tpre (t_pro A1 A2) (t_pro x1 x2)) as h; auto.
    forwards*: epre_sim H0 h tp. 
  -
    inverts typ. inverts H.
    forwards*: Typing_chk H2. inverts H.
    forwards*: IHep.
    forwards* hh3: inf_chk_epre2 ep H2 H.
    inverts hh3 as hh3.
    forwards*: precise_type2 ep H2 hh3.
    forwards* h1: dmatch_pro_tpre H3 H4.
    inverts h1. inverts H5. inverts H7; try solve[inverts H6].
    forwards*: epre_sim H0 H9 tp.
  -
    inverts typ. inverts H.
    forwards*: Typing_chk H2. inverts H.
    forwards*: IHep.
    forwards* hh3: inf_chk_epre2 ep H2 H.
    inverts hh3 as hh3.
    forwards*: precise_type2 ep H2 hh3.
    forwards* h1: dmatch_pro_tpre H3 H4.
    inverts h1. inverts H5. inverts H7; try solve[inverts H6].
    forwards*: epre_sim H0 H11 tp.
  -
    inverts typ.
    inverts H2 as h1.
    forwards*: IHep H8 H0.
    forwards*: epre_sim H3 H0 tp.
    forwards*: cpre_uniq cp.
  -
    inverts typ as h1 h2; simpl in *.
    inverts h1.
    forwards*: epre_sim (t_arrow t_int (t_arrow t_int t_int)) t (t_arrow t_int (t_arrow t_int t_int)) t2.
    forwards*: cpre_uniq cp.
  -
    inverts typ as h1 h2; simpl in *.
    inverts h1.
    forwards*: epre_sim ((t_arrow t_int t_int)) t ((t_arrow t_int t_int)) t2.
    forwards*: cpre_uniq cp.
Qed.



Theorem SGG_chk: forall e e' T E1 E2,
   sepre e e' ->  
   Typing E1 e Chk T ->
   cpre E1 E2 ->
   exists T', Typing E2 e' Chk T' /\ tpre T T'.
Proof.
  introv ep Typ1 cp.
  assert(tpre T T).
  apply tpre_refl.
  forwards*: tpre_chk Typ1 H.
Qed.


Theorem SGG_both: forall e e' T E1 E2 dir,
   sepre e e' ->  
   Typing E1 e dir T ->
   cpre E1 E2 ->
   exists T', Typing E2 e' dir T' /\ tpre T T'.
Proof.
  introv ep Typ1 cp.
  destruct dir.
  -
   forwards* h1: Typing_chk Typ1.
   inverts h1 as h1.
   forwards* h2: SGG_chk ep h1.
   lets(tt1&h3&h4): h2.
   forwards* h5: inf_chk_epre2 ep Typ1 h3.
   lets(tt2&h6): h5.
   forwards*: precise_type2 Typ1 h6.
  -
   forwards* h2: SGG_chk ep Typ1.
Qed.




Lemma pval_pre: forall e1 e2,
  epre e1 e2 ->
  pval e2 ->
  pval e1.
Proof.
  introv ep val.
  inductions ep; intros; try solve[inverts* val].
  -
  inverts val.
  forwards*: epre_lc2 ep.
  inductions ep; eauto.
  inverts ep. inverts* H.
  inverts H2.
  inverts* H0.
Qed. 


Lemma val_pre: forall e1 e2,
  epre e1 e2 ->
  value e2 ->
  value e1.
Proof.
  introv ep val.
  inductions ep; intros; try solve[inverts* val].
  -
  inverts val.
  forwards*: pval_pre ep.
Qed.



Lemma val_prel: forall e1 e2,
  epre e1 e2 ->
  value e1 ->
  value e2.
Proof.
  introv ep val.
  inductions ep; intros; try solve[inverts* val].
Qed.


Lemma fval_epre: forall e1 e2,
  epre e1 e2 ->
  fval e1 ->
  pval e2 ->
  fval e2.
Proof.
  introv ep val.
  inductions ep; intros; try solve[inverts* val].
  inverts* H0; inverts* val.
Qed. 


Lemma epre_dynamic_type: forall e1 e2,
 pval e1 ->
 epre e1 e2 ->
 tpre (dynamic_type e1) (dynamic_type e2).
Proof.
  introv sval ep.
  inductions ep; simpl;eauto.
  inverts* sval.
Qed.




Lemma anno_chk: forall e t1 t2,
 [] ⊢ e_anno e t1 ⇒ t2 ->
 exists t3, Typing nil e Chk t3.
Proof.
  introv typ.
  inverts* typ.
Qed.



Lemma ano_ano_epre: forall e t e2,
 epre (e_anno e t) e2 ->
 exists e3 t2, e2 = (e_anno e3 t2) /\ epre e e3 /\ tpre t t2.
Proof.
  introv ep.
  inverts* ep.
Qed.



Lemma erase_epre: forall e1 e2,
 value e1 ->
 value e2 ->
 epre e1 e2 ->
 epre (erase e1) (erase e2).
Proof.
  introv wal1 wal2 ep.
  inductions ep; try solve[inverts* wal1;inverts H];
  try solve[inverts* wal2]; simpl;eauto.
Qed.


Lemma meet_tpre: forall t1 t2 t3 t4 t5 t6,
 meet t1 t2 t3 ->
 tpre t1 t4 ->
 tpre t2 t5 ->
 meet t4 t5 t6 ->
 tpre t3 t6.
Proof.
  introv me1 tp1 tp2 me2. gen t4 t5 t6.
  inductions me1; introv tp1 tp2 me2;
  try solve[inverts* tp1; inverts* tp2; try solve[inverts* me2]].  
Qed.




Lemma tpre_principle: forall e1 e2,
 value e1 ->
 value e2 ->
 epre e1 e2 ->
 tpre (dynamic_type e1) (dynamic_type e2).
Proof.
  introv wal1 wal2 ep.
  inductions ep; simpl; eauto.
  inverts wal1. 
Qed.


Lemma pval_tpre_principle: forall e1 e2,
 pval e1 ->
 pval e2 ->
 epre e1 e2 ->
 tpre (dynamic_type e1) (dynamic_type e2).
Proof.
  introv wal1 wal2 ep.
  inductions ep; simpl; eauto.
  inverts* wal1.
  inverts* wal2. 
Qed.


Lemma add_tpre:forall A,
 sim (dynamic_type e_add) A ->
 tpre (dynamic_type e_add) A.
Proof.
  introv sm; simpl in *.
  inverts sm as h1 h2; eauto.
  -
    inverts h1 as h1.
    +
    inverts h2 as h21 h22; eauto.
    inverts h21; inverts* h22.
    +
    inverts h2 as h21 h22; eauto.
    inverts h21; inverts* h22.
Qed.

Lemma addl_tpre:forall A i,
 sim (dynamic_type (e_addl i)) A ->
 tpre (dynamic_type (e_addl i)) A.
Proof.
  introv sm; simpl in *.
  inverts sm as h1 h2; eauto.
  -
    inverts h1 as h1;
    inverts* h2.
Qed.


Lemma lit_tpre:forall A i,
 sim (dynamic_type (e_lit i)) A ->
 tpre (dynamic_type (e_lit i)) A.
Proof.
  introv sm; simpl in *.
  inverts sm as h1 h2; eauto.
Qed.



Lemma Cast_dgg: forall p1 p2 v1' A1 B1 A2 B2 t1 t2,
  epre p1 p2 ->  
  tpre A2 B2 ->
  pval p1 ->
  pval p2 ->
  Typing nil p1 Chk t1 ->
  Typing nil p2 Chk t2 -> 
  meet (dynamic_type p1) A2 A1 ->
  meet (dynamic_type p2) B2 B1 ->
  Cast p1 A1 (Expr v1') ->
  exists v2', Cast p2 B1 (Expr v2') /\ epre (e_val v1' A2) (e_val v2' B2).
Proof.
  introv ep tp val1 val2 typ1 typ2 mt1 mt2 red. gen p2 A2 B1 B2 t1 t2.
  inductions red; intros; eauto.
  -
    inverts* ep.
    simpl in *.
    inverts* mt2.
  -
    inverts val1 as val1.
    inverts ep as ep1 ep2.
    inverts ep2 as ep2 ep3.
    inverts ep3 as ep3.
    inverts val2 as val2.
    forwards* h2: meet_tpre mt1 mt2.
    forwards* h1:epre_sim H ep2 h2.
    simpl in *.
    forwards* h3: meet_more_precise mt1.
    lets(h4&h5): h3.
    inverts h4 as h4.
    forwards* h7: meet_more_precise mt2.
    lets(h8&h9): h7.
    inverts h8.
    exists. splits*.
    eapply ep_val;eauto. 
  -
    assert(exists t1 t2, pattern_pro A0 (t_pro t1 t2)) as h0.
    inverts* mt1.
    lets(ttt1&ttt2&H):h0.
    forwards* h1: dmatch_pro_tpre tp H.
    lets(tt1& h2&h3):h1.
    inverts h3 as h3; try solve[inverts h2].
    inverts ep as ep1 ep2.
    inverts val2 as h4 h5.
    simpl in *.
    assert(meet (dynamic_type p1) ttt1 A1) as h7.
    inverts H; try solve[inverts* mt1].
    assert(meet (dynamic_type p2) ttt2 A2) as h8.
    inverts H; try solve[inverts* mt1].
    forwards* h11: meet_more_precise mt2.
    lets(h12&h13): h11.
    inverts h12 as h12.
    assert(meet (dynamic_type e1') C A) as h9.
    inverts h2; try solve[inverts* mt2].
    assert(meet (dynamic_type e2') D B) as h10.
    inverts h2; try solve[inverts* mt2].
    inverts val1 as val11 val12.
    inverts typ1 as typ1.
    inverts typ1 as typ1.
    inverts typ2 as typ2.
    inverts typ2 as typ2.
    forwards* h6: IHred1 ep1 h7 h9.
    lets(vv1&h14&h15):h6.
    forwards* h16: IHred2 ep2 h8  h10.
    lets(vv2&h17&h18):h16.
    inverts h15.
    inverts* h18.
    assert(tpre (dynamic_type (e_pro vv1 vv2)) B2).
    simpl.
    inverts* h2.
    exists. splits*.
  -
    inverts ep.
    simpl in *.
    forwards* h4: meet_sim mt1.
    forwards* h3: add_tpre A2.
    forwards* h2: meet_tpre mt1 mt2.
    forwards* h5: epre_sim (t_arrow t_int (t_arrow t_int t_int)) A2 
    (t_arrow t_int (t_arrow t_int t_int)) B2.
    forwards* h6: add_tpre B2.
  -
    inverts ep.
    simpl in *.
    forwards* h4: meet_sim mt1.
    forwards* h3: addl_tpre A2.
    forwards* h2: meet_tpre mt1 mt2.
    forwards* h5: epre_sim ((t_arrow t_int t_int)) A2 
    ((t_arrow t_int t_int)) B2.
    forwards* h6: addl_tpre B2.
Qed.




Lemma dynamic_guaranteel_chk: forall e1 e2 e1' T1 T2,
 epre e1 e2 ->  
 Typing nil e1 Chk T1 ->
 Typing nil e2 Chk T2 -> 
 step e1 (Expr e1') ->
 exists e2', step e2 (Expr e2') /\ epre e1' e2'.
Proof.
  introv ep typ1 typ2 red. gen e1' T1 T2.
  inductions ep; intros;
  try solve[inverts* red;destruct E; unfold simpl_fill in H; inverts* H];
  try solve[inverts* red;destruct E; unfold simpl_fill in H1; inverts* H1]; eauto.
  - (* app *)
    inverts red.
    + destruct E; unfold simpl_fill in H; inverts* H.
      *
      inverts typ1; try solve[forwards*: step_not_abs H2].
      inverts typ2; try solve[inverts ep1;forwards*: step_not_abs H2].
      inverts H; try solve[
        forwards*: step_not_fvalue H2
      ]. 
      inverts H3;
      try solve[inverts ep1; forwards*: step_not_fvalue H2].
      forwards* h1: Typing_chk H7. inverts h1.
      forwards* h2: Typing_chk H6. inverts h2.
      forwards* h3: IHep1 H2. 
      lets(ee1& rred1& eep1): h3.
      forwards* h4: Typing_regular_1 H12.
      exists. split. inverts H1. 
      rewrite sfill_appl.
      apply Step_eval;eauto.
      unfold simpl_fill in *.
      apply ep_app; eauto.
      *
      inverts typ1 as hh1 hh2;
      try solve[forwards*: step_not_fvalue H2].
      --
      inverts typ2 as hh4 hh5.
      ++
      inverts hh1 as hh1 hh3.
      **
        inverts hh4 as hh4 hh6;
        try solve[inverts H1; try solve[inverts hh1]].
      **
        inverts hh4 as hh4 hh6;
        try solve[inverts ep1; try solve[inverts hh4]].
        forwards* h3: IHep2 H2.
        lets(ee2& rred2& eep2): h3.
        inverts H1;inverts ep1 as hhh1 hhh2.
        ---
        inverts hhh2.
        exists. split. 
        rewrite sfill_appr.
        apply Step_eval; auto.
        apply rred2.
        apply ep_app; eauto.
        ---
        inverts hhh2.
        exists. split. 
        rewrite sfill_appr.
        apply Step_eval; auto.
        apply rred2.
        apply ep_app; eauto.
      ++
      inverts hh1 as hh1 hh3; try solve[inverts ep1].
      forwards* h3: IHep2 H2.
      lets(ee2& rred2& eep2): h3.
      exists. split. 
      rewrite sfill_appr.
      apply Step_eval.
      unfold simpl_fill in *.
      inverts H1; try solve[inverts* ep1];
      try solve[inverts ep1 as hh7 hh8;inverts* hh8].
      apply rred2.
      apply ep_app; eauto.
      --
      inverts typ2 as hh4 hh5.
      ++
      inverts hh4 as hh4 hh6; try solve[inverts ep1].
      forwards* h3: IHep2 H2.
      lets(ee2& rred2& eep2): h3.
      exists. split. 
      rewrite sfill_appr.
      apply Step_eval.
      unfold simpl_fill in *.
      inverts H1; try solve[inverts* ep1];
      try solve[inverts ep1 as hh7 hh8;inverts* hh8].
      apply rred2.
      apply ep_app; eauto.
      ++
      forwards* h3: IHep2 H2.
      lets(ee2& rred2& eep2): h3.
      exists. split. 
      rewrite sfill_appr.
      apply Step_eval.
      unfold simpl_fill in *.
      inverts H1; try solve[inverts* ep1];
      try solve[inverts ep1 as hh7 hh8;inverts* hh8].
      apply rred2.
      apply ep_app; eauto.
    + 
      forwards* h1: epre_lc ep1.
      forwards* h2: val_prel ep2.
      inverts ep1 as h3.
      exists. split.
      eapply Step_beta; eauto.
      pick fresh xx.
      assert((e0 ^^ e2') = [xx ~> e2'] (e0 ^ xx)).
      rewrite (subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite H.
      forwards*: h3 xx.
      forwards*: epre_open H0 ep2.
    + 
      inverts ep1 as h1 h2 h3 h4.
      forwards* h8: fval_epre h2.
      forwards* h9: dmatch_tpre h3 H3.
      lets(tt1&h10&h11):h9.
      inverts h11; try solve[inverts h10].
      forwards* h12: pval_tpre_principle h2.
      rewrite H4 in *.
      inverts h12 as h12;
      try solve[inverts h1; simpl in *; inverts h12].
      exists. splits.
      eapply Step_fv; eauto.
      eapply ep_anno; eauto.
    +
      inverts ep1 as h1 h2 h3 h4.
      inverts h2 as h5 h6; try solve[inverts h1].
      inverts h6 as h6 h7; try solve[inverts h1].
      inverts h1.
      inverts h5.
      inverts h6.
      exists. splits.
      eapply Step_app; eauto.
      eapply ep_anno; eauto.
    +   
      inverts ep1 as h1 h2; simpl in *.
      inverts h2; simpl in *.
      inverts ep2 as h3 h4 ; simpl in *.
      inverts h4; simpl in *.
      inverts typ2 as h13 h14.
      inverts h13 as h13 h15 h16;
      try solve[inverts h13].
      inverts h15.
      inverts h16 as h16; eauto.
    +
      inverts ep1 as h1 h2; simpl in *.
      inverts h2; simpl in *.
      inverts ep2 as h3 h4 ; simpl in *.
      inverts h4; simpl in *.
      inverts typ2 as h13 h14.
      inverts h13 as h13 h15 h16;
      try solve[inverts h13].
      inverts h15.
      inverts h16 as h16; eauto.
  - (* anno *)
    inverts* red.
    +
      inverts* ep.
      forwards* h1: dmatch_tpre H H4.
      lets(tt1& h2 & h3): h1.
      inverts h3; try solve[inverts h2].
      forwards* h4: Typing_regular_1 typ2.
      inverts h4. 
      exists. splits*.
      eapply ep_val; eauto.
      eapply ep_anno; eauto.
      inverts* h2.
    +
      destruct E; unfold simpl_fill in H0; inverts H0.
      inverts typ1 as typ1. inverts typ2 as typ2.
      inverts typ1 as typ1. inverts typ2 as typ2.
      forwards* h1: IHep H3.
      lets(ee1&h2&h3): h1.
      rewrite sfill_anno.
      exists. splits*.
      simpl; eauto.
    +
      inverts ep. 
      inverts typ1 as typ1.
      inverts typ1 as typ1.
      inverts typ1 as typ1.
      inverts typ1.
      inverts typ2 as typ2.
      inverts typ2 as typ2.
      inverts typ2 as typ2.
      inverts typ2.
      forwards* h1: meet_sim H4.
      lets(h2&h3&h4): h1.
      forwards* h5: pval_tpre_principle H6.
      forwards* h6: epre_sim h2 h5 H.
      forwards* h7: meet_progress  h6.
      lets(tt1&h8):h7.
      forwards* h9: meet_tpre H4 h8.
      forwards* h10: Cast_dgg H6 H4 h8 H3.
      lets(ee1&h11&h12):h10.
      exists. splits*.
  - (* pro *)
    inverts red.
    +
    inverts ep1. inverts ep2.
    exists. splits*.
    eapply ep_val; simpl;eauto.
    +
    destruct E; unfold simpl_fill; inverts H.
    *
    inverts typ1. inverts H.
    inverts typ2. inverts H.
    forwards* h1: Typing_chk H6. inverts h1.
    forwards* h2: Typing_chk H9. inverts h2.
    forwards* h3: IHep1 H2.
    lets (ee1&rred1&epp1): h3.
    inverts H1.
    forwards*: epre_lc ep2.
    rewrite sfill_prol.
    exists. splits.
    eapply Step_eval; unfold simpl_fill.
    eauto.
    apply rred1.
    eapply ep_pro; eauto.
    *
    inverts typ1. inverts H.
    inverts typ2. inverts H.
    forwards* h1: Typing_chk H6. inverts h1.
    forwards* h2: Typing_chk H9. inverts h2.
    forwards* h3: IHep2 H2.
    lets (ee1&rred1&epp1): h3.
    inverts H1.
    forwards*: val_prel H8.
    rewrite sfill_pror.
    exists. splits.
    eapply Step_eval; unfold simpl_fill.
    eauto.
    apply rred1.
    eapply ep_pro; eauto.
  - (* projl *)
    inverts red.
    + 
    destruct E; unfold simpl_fill; inverts H.
    inverts typ1. inverts H.
    inverts typ2. inverts H.
    forwards* h1: Typing_chk H4. inverts h1.
    forwards* h2: Typing_chk H7. inverts h2.
    forwards* h3: IHep H2.
    lets (ee1&rred1&epp1): h3.
    rewrite sfill_l.
    exists. splits.
    eapply Step_eval; unfold simpl_fill.
    eauto.
    apply rred1.
    simpl in *.
    eapply ep_l; eauto.
    +
    inverts ep. inverts H5.
    inverts H4.
    forwards* h1: dmatch_pro_tpre H6 H1.
    lets(tt1&h8&h9): h1.
    inverts h9; try solve[inverts h8].
    simpl in *.
    exists. splits*.
    eapply ep_val; eauto.
    inverts * H8; try solve[inverts* h8].
  - (* projr *)
    inverts red.
    +
    destruct E; unfold simpl_fill; inverts H.
    inverts typ1. inverts H.
    inverts typ2. inverts H.
    forwards* h1: Typing_chk H4. inverts h1.
    forwards* h2: Typing_chk H7. inverts h2.
    forwards* h3: IHep H2.
    lets (ee1&rred1&epp1): h3.
    rewrite sfill_r.
    exists. splits.
    eapply Step_eval; unfold simpl_fill.
    eauto.
    apply rred1.
    simpl in *.
    eapply ep_r; eauto.
    +
    inverts ep. inverts H5.
    inverts H4.
    forwards* h1: dmatch_pro_tpre H6 H1.
    lets(tt1&h8&h9): h1.
    inverts h9; try solve[inverts h8].
    simpl in *.
    exists. splits*.
    eapply ep_val; eauto.
    inverts * H8; try solve[inverts* h8].
  -
    inverts typ1. inverts H2.
    forwards*: step_not_value red.
  -
    forwards*: step_not_fvalue red.
Qed.


Lemma dynamic_guaranteel_dir: forall e1 e2 e1' dir T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 -> 
 step e1 (Expr e1') ->
 exists e2', step e2 (Expr e2') /\ epre e1' e2'.
Proof.
  introv ep typ1 typ2 red.
  destruct dir.
  - forwards*: Typing_chk typ1. inverts H. 
    forwards*: Typing_chk typ2. inverts H.
    forwards*: dynamic_guaranteel_chk H0 H1.
  - forwards*: dynamic_guaranteel_chk typ1 typ2.
Qed.


Lemma DGGL: forall e1 e2 dir v1 T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 value v1 ->
 e1 ->* (Expr v1) ->
 exists v2, value v2 /\ e2 ->* (Expr v2) /\ epre v1 v2.
Proof.
  introv ep typ1 typ2 val red. gen e2 T1 dir T2 . 
  inductions red; intros.
  -
    forwards*: val_prel ep.
  - forwards*:  dynamic_guaranteel_dir ep typ1 typ2 H.
    inverts H0. inverts H1.
    forwards*: preservation H.
    forwards*: preservation H0.
    forwards*: IHred val H2 H1.
    inverts H4. inverts H5. inverts H6.
    exists. split. apply H4. split.
    eapply step_n.
    apply H0.
    apply H5. auto.
Qed.


Lemma dynamic_guaranteer_dir: forall e1 e2 e2' dir T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 -> 
 step e2 (Expr e2') ->
 (exists e1', step e1 (Expr e1') /\ epre e1' e2') \/ step e1 Blame.
Proof.
  introv ep typ1 typ2 red.
  forwards* h1: progress_dir typ1.
  inverts h1 as h1.
  -
  inverts h1 as h1; eauto.
  forwards* h2: val_prel ep.
  forwards*: step_not_value red.
  -
    inverts h1 as h1.
    +
    inverts h1.
    destruct x; eauto.
    forwards* h2: dynamic_guaranteel_dir H.
    lets(ee1& h3& h5): h2.
    forwards* h6: step_unique red h3.
    inverts* typ2.
    inverts* h6. 
    +
    inverts h1 as h1.
    inverts ep.
    forwards*: step_not_abs red.
Qed.


Lemma DGGR: forall e1 e2 dir v2 T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 value v2 ->
 e2 ->* (Expr v2) ->
 (exists v1, value v1 /\ e1 ->* (Expr v1) /\ epre v1 v2) \/ e1 ->* Blame.
Proof.
  introv ep typ1 typ2 val red. gen e1 T1 dir T2 . 
  inductions red; intros.
  -
    forwards*: val_pre ep.
  - 
    forwards* h1:  dynamic_guaranteer_dir ep typ1 typ2 H.
    inverts h1 as h1.
    +
      lets(ee1& h2 & h3): h1.
      forwards* h4: preservation h2.
      forwards* h5: preservation H.
      forwards* h6: IHred  val h3 h4 h5.
      inverts h6 as h6.
      *
        lets(vv1& h7&h8&h9):h6.
        left.
        exists. splits.
        apply h7.
        eapply step_n.
        apply h2.
        apply h8. auto.
      *
        right.
        eapply step_nb.
        apply h2.
        apply h6. 
    +
      right.
      eapply step_b; eauto.
Qed.



Theorem multi_progress : forall e dir T,
  Typing nil e dir T ->
  exists r, steps e r.
Proof.
  introv typ.
  forwards* h1: progress_dir typ.
Qed.



Theorem DGG_blame_aux: forall e1 e2 dir T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 step e2 Blame ->
 step e1 Blame.
Proof.
  introv ep typ1 typ2 red.
  forwards* h1: progress_dir typ1.
  inverts h1 as h1.
  -
   forwards* h2: val_prel ep.
   forwards* h3:step_not_value red.
  -
   inverts h1 as h1.
   +
   inverts h1 as h1.
   destruct x; eauto.
   forwards* h2: dynamic_guaranteel_dir ep h1.
   lets(ee1&h3&h5): h2.
   destruct dir.
   *
    forwards* h6: Typing_chk typ2.
    inverts h6.
    forwards* h7: step_unique red h3.
    inverts* h7.
   *
    forwards* h7: step_unique red h3.
    inverts* h7.
   +
   inverts* h1.
   inverts ep.
   forwards*: step_not_abs red.
Qed.



Theorem DGG_blame: forall e1 e2 dir T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 steps e2 Blame ->
 steps e1 Blame.
Proof.
  introv ep typ1 typ2 red. gen e1 T1 T2.
  inductions red; intros.
  -
    forwards* h3: dynamic_guaranteer_dir ep H.
    inverts h3 as h3; eauto.
    lets(ee1 & h4 & h5): h3.
    forwards* h6: preservation H.
    forwards* h7: preservation typ1.
  -
    forwards*: DGG_blame_aux ep.
Qed.



Theorem Diverge: forall e1 e2 dir T1 T2,
 epre e1 e2 ->  
 Typing nil e1 dir T1 ->
 Typing nil e2 dir T2 ->
 diverge e1 ->
 diverge e2.
Proof.
  introv ep typ1 typ2 dv.
  unfold diverge in *.
  unfold not in *; intros nt.
  apply dv.
  inverts nt as nt.
  -
    lets(vv1&h1&h2): nt.
    forwards* h3: DGGR h1.
    inverts h3 as h3.
    +
    lets(vv2&h4&h5&h6): h3.
    left. exists*.
    +
    right*.
  -
    forwards* h1: multi_progress typ1.
    lets(r&h2): h1.
    destruct r.
    +
    forwards* h3: DGG_blame ep nt.
    +
    right*.
Qed.