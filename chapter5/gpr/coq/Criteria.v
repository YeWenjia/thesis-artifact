Require Export Metalib.Metatheory.
Require Import LibTactics.

Require Import Definitions
              rules_inf
              Infrastructure
              Lemmas
              Determinism
              Soundness
              Lia.




Lemma pvalue_expr: forall v,
 pvalue v -> expr v.
Proof.
  introv val.
  inductions val; eauto.
Qed.


Lemma value_expr: forall v,
 value v -> expr v.
Proof.
  introv val.
  inductions val; eauto.
  forwards*: pvalue_expr H.
Qed.


Inductive epre : exp -> exp -> Prop :=  
 | ep_var : forall (x:var),
    epre (e_fvar x) (e_fvar x)
 | ep_i i:
    epre (e_lit i) (e_lit i) 
 | ep_unit :
    epre e_unit e_unit 
 | ep_abs : forall (L:vars) (e1 e2:exp),
     ( forall x , x \notin  L  -> 
      epre  ( open_ee e1 (e_fvar x) )   ( open_ee e2 (e_fvar x) )  )  ->
     epre (e_abs e1 ) (e_abs e2)
 | ep_tabs : forall (L:vars) (e1 e2:exp),
      (forall x , x \notin  L  -> 
      epre  ( open_te e1 (t_fvar x) )   ( open_te e2 (t_fvar x) )  )  ->
     epre (e_tabs e1) (e_tabs e2)
 | ep_app : forall (e1 e2 e1' e2':exp) ,
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_app e1 e2) (e_app e1' e2')
 | ep_tapp : forall (e1 e2:exp) A B,
     tpre A B ->
     epre e1 e2 ->
     epre (e_tapp e1 A) (e_tapp e2 B)
 | ep_anno : forall (e1 e2:exp) A B,
     tpre A B ->
     epre e1 e2 ->
     epre (e_anno e1 A) (e_anno e2 B)
 | ep_loc i:
     epre (e_loc i) (e_loc i) 
 | ep_ref : forall (e1 e2:exp),
     epre e1 e2 ->
     epre (e_ref e1) (e_ref e2)
 | ep_get : forall (e1 e2:exp),
     epre e1 e2 ->
     epre (e_get e1) (e_get e2)
 | ep_set : forall (e1 e2 e1' e2':exp) ,
     epre e1 e1' ->
     epre e2 e2' ->
     epre (e_set e1 e2) (e_set e1' e2')
 | ep_val: forall p1 p2 t1 t2,
    pvalue p2 ->
    epre p1 p2 ->
    tpre t1 t2 ->
    tpre (dynamic_type p2) t2 ->
    epre (e_val p1 t1) (e_val p2 t2)
  | ep_rval: forall i,
    epre (e_rval (e_loc i)) (e_rval (e_loc i))
.



Inductive sepre : exp -> exp -> Prop :=  
 | sep_var : forall (x:var),
    sepre (e_fvar x) (e_fvar x)
 | sep_i i:
    sepre (e_lit i) (e_lit i) 
 | sep_unit :
    sepre e_unit e_unit 
 | sep_abs : forall (L:vars) (e1 e2:exp),
     ( forall x , x \notin  L  -> 
      sepre  ( open_ee e1 (e_fvar x) )   ( open_ee e2 (e_fvar x) )  )  ->
     sepre (e_abs e1 ) (e_abs e2)
 | sep_tabs : forall (L:vars) (e1 e2:exp),
      (forall x , x \notin  L  -> 
      sepre  ( open_te e1 (t_fvar x) )   ( open_te e2 (t_fvar x) )  )  ->
     sepre (e_tabs e1) (e_tabs e2)
 | sep_app : forall (e1 e2 e1' e2':exp) ,
     sepre e1 e1' ->
     sepre e2 e2' ->
     sepre (e_app e1 e2) (e_app e1' e2')
 | sep_tapp : forall (e1 e2:exp) A B,
     tpre A B ->
     sepre e1 e2 ->
     sepre (e_tapp e1 A) (e_tapp e2 B)
 | sep_anno : forall (e1 e2:exp) A B,
     tpre A B ->
     sepre e1 e2 ->
     sepre (e_anno e1 A) (e_anno e2 B)
 | sep_loc i:
     sepre (e_loc i) (e_loc i) 
 | sep_ref : forall (e1 e2:exp),
     sepre e1 e2 ->
     sepre (e_ref e1) (e_ref e2)
 | sep_get : forall (e1 e2:exp),
     sepre e1 e2 ->
     sepre (e_get e1) (e_get e2)
 | sep_set : forall (e1 e2 e1' e2':exp) ,
     sepre e1 e1' ->
     sepre e2 e2' ->
     sepre (e_set e1 e2) (e_set e1' e2')
.



Inductive mpre : sto -> sto -> Prop :=  
 | mp_nil : 
    mpre nil nil
 | mp_cons: forall v1 m1 v2 m2,
    epre v1 v2 ->
    mpre m1 m2 ->  
    mpre (v1::m1) (v2::m2). 


Inductive ppre : phi -> phi -> Prop :=  
 | pp_nil : 
    ppre nil nil
 | pp_cons: forall t1 m1 t2 m2,
    tpre t1 t2 ->
    ppre m1 m2 ->  
    ppre (t1::m1) (t2::m2). 


Inductive cpre : env -> env -> Prop :=
  | cp_nil: 
      cpre nil nil
  | cp_cons: forall E F x A1 A2,
      tpre A1 A2 ->
      cpre E F ->
      cpre ([(x ,bind_typ A1)] ++ E) ([(x, bind_typ A2)] ++ F)
  | cp_cons2: forall E F x,
      cpre E F ->
      cpre (x ~tvar ++ E) (x ~tvar ++ F)
.


Hint Constructors cpre sepre epre mpre ppre: core.



Lemma tpre_wf_typ: forall E A B,
 tpre A B ->
 wf_typ E A ->
 wf_typ E B.
Proof.
  introv tp wft. gen E.
  inductions tp; intros; auto;
  try solve[
    inverts wft; auto
  ].
  - 
  inverts wft.
  pick fresh y and apply wf_typ_all.
  forwards: H3 y. eauto.
  forwards: H0 H1. eauto.
  simpl; eauto.
Qed.


Lemma tpre_consist : forall E A1 B1 A2 B2,
  wf_env E ->
  consist E A1 B1 ->
  tpre A1 A2 ->
  tpre B1 B2 ->
  consist E A2 B2.
Proof.
  introv wfv s1 tp1 tp2. gen A2 B2.
  lets s1': s1.
  inductions s1; intros; 
  try solve[inverts tp2; inverts tp1].
  - inverts tp2; inverts tp1; eauto.
  - inverts tp2; inverts tp1; eauto.
  - inverts tp2; inverts tp1; eauto.
  - forwards*: tpre_wf_typ tp2.
    inverts* tp1.
  - forwards*: tpre_wf_typ tp1.
    inverts* tp2.
  - inverts tp1; inverts tp2; eauto.
    + 
    forwards*: consist_regular s1'. inverts H0. inverts H3.
    forwards*: tpre_wf_typ (t_arrow B1 B2) (t_arrow C D) H5.
    +
    forwards*: consist_regular s1'. inverts H0. inverts H4.
    forwards*: tpre_wf_typ (t_arrow A1 A2) (t_arrow C D) H0.
  - 
    lets tp1': tp1. lets tp2': tp2.
    inverts tp1; inverts tp2; eauto.
    +
    pick fresh y and apply consist_all.
    forwards*: H y. 
    +
    forwards*: consist_regular s1'.
    destruct H3. destruct H4.
    forwards*: tpre_wf_typ tp1'.
    +
    forwards*: consist_regular s1'.
    destruct H2. destruct H4.
    forwards*: tpre_wf_typ tp2'.
  -
    forwards*: tpre_wf_typ tp1.
    forwards*: tpre_wf_typ tp2.
    inverts* tp1; inverts* tp2. 
Qed.


Lemma epre_exp: forall e1 e2,
 epre e1 e2 ->
 expr e1 /\
 expr e2.
Proof.
  introv ep. 
  inductions ep; intros; try solve[
  forwards*: tpre_type H];
  try solve[inverts* IHep1];
  try solve[forwards*: IHep]; 
  try solve[forwards* h1: tpre_type H0]; eauto.
  - 
    pick fresh y.
    forwards* h1: H0 y.
    inverts h1 as h1 h2.
    forwards*: lc_e_abs_exists h1.
    forwards*: lc_e_abs_exists h2.
  - 
    pick fresh y.
    forwards* h1: H0 y.
    inverts h1 as h1 h2.
    forwards*: lc_e_tabs_exists h1.
    forwards*: lc_e_tabs_exists h2.
Qed.


Lemma epre_expr: forall e1 e2,
 epre e1 e2 ->
 expr e1 ->
 expr e2.
Proof.
  introv ep lc. 
  inductions ep; intros; try solve[inverts~ lc; 
  forwards*: tpre_type H];
  try solve[inverts~ lc; 
  forwards*: tpre_type H0].
Qed.


Lemma epre_exprl: forall e1 e2,
 epre e1 e2 ->
 expr e2 ->
 expr e1.
Proof.
  introv ep lc. 
  inductions ep; intros; try solve[inverts~ lc; 
  forwards*: tpre_type H];
  try solve[inverts~ lc; 
  forwards*: tpre_type H0].
Qed.



Lemma pval_pre: forall e1 e2,
  epre e1 e2 ->
  pvalue e2 ->
  pvalue e1.
Proof.
  introv ep val.
  forwards* lc2: pvalue_expr val.
  forwards* lc: epre_exprl ep.
  inductions ep; intros; try solve[inverts* val].
  inverts val as h1 h2 h3.
  -
    inverts ep as h4 h5.
    inverts* h5.
    inverts* h4.
    inverts* H.
    inverts lc as h6 h7.
    inverts h6 as h61 h62.
    eauto.
  -
     inverts ep as h4 h5.
    inverts* h5.
    inverts* h4.
    inverts* H.
    inverts lc as h6 h7.
    inverts h6 as h61 h62.
    eauto.
  -
    inverts ep as h4 h5.
    inverts* H.
    inverts lc as h6 h7.
    inverts h7 as h71 h72.
    eauto.
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
  forwards*: tpre_type H0.
  forwards*: pval_pre ep.
Qed.



Lemma val_prel: forall e1 e2,
  epre e1 e2 ->
  value e1 ->
  value e2.
Proof.
  introv ep val.
  inductions ep; intros; try solve[inverts* val].
  forwards*: tpre_type H0.
Qed.


Lemma subst_pvalue : forall p z u,
    expr u ->
    pvalue p -> pvalue (subst_ee u z p).
Proof.
  introv lc pval.
  inductions pval; simpl in *; eauto.
  -
  eapply pv_arr; eauto.
  forwards*: subst_exp_expr H lc.
  -
  eapply pv_all; eauto.
  forwards*: subst_exp_expr H lc.
Qed.


Lemma subste_pvalue : forall p z u,
    type u ->
    pvalue p -> pvalue (subst_te u z p).
Proof.
  introv lc pval.
  inductions pval; simpl in *; eauto.
  -
  eapply pv_arr; eauto.
  forwards*: tsubst_exp_expr H lc.
  forwards*: tsubst_typ_type H0 lc.
  forwards*: tsubst_typ_type H1 lc.
  -
  eapply pv_all; eauto.
  forwards*: tsubst_exp_expr H lc.
  forwards*: tsubst_typ_type H0 lc.
  forwards*: tsubst_typ_type H1 lc.
  -
  forwards*: tsubst_typ_type H lc.
Qed.



Lemma subst_principal : forall p z u,
    expr u ->
    pvalue p -> dynamic_type (subst_ee u z p) = dynamic_type p.
Proof.
  introv lc pval.
  inductions pval; simpl in *; eauto.
Qed.



Lemma subste_principal : forall p z u,
    type u ->
    pvalue p -> dynamic_type (subst_te u z p) = subst_tt u z (dynamic_type p).
Proof.
  introv lc pval.
  inductions pval; simpl in *; eauto.
Qed.

Lemma epre_open: forall e1 e2 u1 u2 x,
 epre e1 e2 ->
 epre u1 u2 ->
 expr u1 ->
 expr u2 ->
 epre ([x ~> u1]e1) ([x ~> u2]e2).
Proof.
  introv ep1 ep2 lc1 lc2. gen u1 u2 x.
  inductions ep1; intros; 
  simpl; eauto.
  -  destruct (x == x0); eauto.
  - pick fresh x0 and
      apply ep_abs. 
         forwards*: H0 x0 ep2 x. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto. 
      rewrite subst_exp_open_exp_wrt_exp_var; eauto.
  -
    pick fresh y and apply ep_tabs.
    forwards*: H0 y ep2 x. 
    rewrite subst_exp_open_exp_wrt_typ_var; eauto. 
    rewrite subst_exp_open_exp_wrt_typ_var; eauto.
  -
     forwards* h1: subst_pvalue x lc2 H.
    forwards* h2: subst_principal x lc2 H.
    eapply ep_val; eauto.
    rewrite h2 ; eauto.
Qed.


Lemma  susbt_tt_type: forall A u1 x,
 type A ->
 type u1 ->
 type (subst_tt u1 x A).
Proof.
  introv typ1 typ2. gen x u1.
  inductions typ1; intros; unfold subst_tt; eauto.
  -
  destruct(X == x); eauto.
  -
  fold subst_tt.
  pick fresh y.
  forwards* h1: H0 y x typ2.
  rewrite <- tsubst_typ_open_typ_wrt_typ_var in h1; auto.
  forwards*: lc_t_all_exists h1.
Qed.


Lemma tpre_open: forall t1 t2 u1 u2 x,
 tpre t1 t2 ->
 tpre u1 u2 ->
 type u1 ->
 type u2 ->
 tpre (subst_tt  u1 x t1) (subst_tt  u2 x t2).
Proof.
  introv ep1 ep2 lc1 lc2. gen u1 u2 x.
  inductions ep1; intros; 
  simpl; eauto.
  - destruct (x == x0); eauto.
  - pick fresh y and apply tp_all.
    forwards* h1: H0 y ep2 x.
    rewrite <- tsubst_typ_open_typ_wrt_typ_var  in h1; auto.
    rewrite <- tsubst_typ_open_typ_wrt_typ_var  in h1; auto.
  - forwards*: susbt_tt_type H lc1.
Qed.



Lemma etpre_open: forall e1 e2 u1 u2 x,
 epre e1 e2 ->
 tpre u1 u2 ->
 type u1 ->
 type u2 ->
 epre (subst_te  u1 x e1) (subst_te u2 x e2).
Proof.
  introv ep1 ep2 lc1 lc2. gen u1 u2 x.
  inductions ep1; intros; 
  simpl; eauto.
  - pick fresh y
    and apply ep_abs. 
    rewrite tsubst_exp_open_exp_wrt_exp_var; eauto. 
    rewrite tsubst_exp_open_exp_wrt_exp_var; eauto.
  - pick fresh y and 
    apply ep_tabs. 
    forwards*: H0 y ep2 x.
    rewrite tsubst_exp_open_exp_wrt_typ_var; eauto. 
    rewrite tsubst_exp_open_exp_wrt_typ_var; eauto.
  - apply ep_tapp.
    forwards*: tpre_open H lc1 lc2.
    forwards*: IHep1 ep2 x.
  - apply ep_anno.
    forwards*: tpre_open H lc1 lc2.
    forwards*: IHep1 ep2 x.
  -
    forwards* h1: tpre_open x H0 ep2.
    forwards* h2: subste_pvalue x lc2 H.
    forwards* h4: subste_principal p2 x lc2.
    forwards* h5: tpre_open H1 lc2.
    apply ep_val; simpl ; auto.
    rewrite h4.
    apply h5.
Qed.



Lemma env_less_precise_binds : forall x A E F,
    binds x (bind_typ A) E ->
    cpre E F ->
    exists B, binds x (bind_typ B) F /\ tpre A B.
Proof.
  introv bind cp.
  inductions cp; try solve[inverts* bind];eauto.
  inverts* bind. inverts* H0.
  forwards*: IHcp.
  inverts* H1.
  inverts* bind. inverts* H.
  forwards*: IHcp.
  inverts* H0.
Qed.



Lemma cpre_notin: forall x E F,
  x `notin` dom E ->
 cpre E F ->
 x \notin dom F.
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
  inverts* uq.
  forwards*: IHcp.
  forwards*: cpre_notin cp.
Qed.


Lemma binds_tpre: forall x T T' E1 E2,
 uniq E1 ->
 uniq E2 ->
 cpre E1 E2 ->
 binds x (bind_typ T) E1 ->
 binds x (bind_typ T') E2 ->
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
  inverts bind1;inverts* bind2;try solve[inverts* H;inverts* H0];
  try solve[inverts* H0].
  forwards*: IHcp x0 T T'.
  inverts* uq1.
  inverts* uq2.
Qed.




Lemma mpre_length:forall mu1 mu2,
 mpre mu1 mu2 ->
 length mu1 = length mu2.
Proof.
  introv mp.
  inductions mp; simpl; eauto.
Qed.


Lemma mpre_app:forall mu1 mu2 mu3 mu4,
 mpre mu1 mu2 ->
 mpre mu3 mu4 ->
 mpre (mu1++mu3) (mu2++mu4).
Proof.
  introv mp1 mp2.
  inductions mp1; simpl; eauto.
Qed.


Lemma store_lookup_epre: forall l mu1 mu2,
 mpre mu1 mu2 ->
 epre (store_lookup l mu1) (store_lookup l mu2).
Proof.
  introv mp.
  inductions l;
  try solve[inductions mp; eauto].
Qed.

Lemma epre_dynamic_type: forall e1 e2,
 epre e1 e2 ->
 tpre (dynamic_type e1) (dynamic_type e2).
Proof.
  introv ep.
  inductions ep; eauto.
Qed.



Lemma dmatch_tpre_abs2: forall t1 t2 t3 t5 ,
 tpre t1 t2 ->
 pattern_abs t1 t3  ->
 pattern_abs t2 t5 ->
 tpre t3 t5 .
Proof.
  introv tp dm1 dm2. gen t3 t5 .
  inductions tp; intros; eauto;
  try solve[inverts* dm1];
  try solve[inverts* dm2];
  try solve[inverts* dm2; inverts* dm1;inverts* H].
Qed.


Lemma dmatch_tpre_ref2: forall t1 t2 t3 t5 ,
 tpre t1 t2 ->
 pattern_ref t1 t3  ->
 pattern_ref t2 t5 ->
 tpre t3 t5 .
Proof.
  introv tp dm1 dm2. gen t3 t5 .
  inductions tp; intros; eauto;
  try solve[inverts* dm1];
  try solve[inverts* dm2];
  try solve[inverts* dm2; inverts* dm1;inverts* H].
Qed.


Lemma dmatch_tpre_all2: forall t1 t2 t3 t5 ,
 tpre t1 t2 ->
 pattern_all t1 t3  ->
 pattern_all t2 t5 ->
 tpre t3 t5 .
Proof.
  introv tp dm1 dm2. gen t3 t5.
  inductions tp; intros; 
  try solve[inverts dm1];
  try solve[inverts dm1;inverts* dm2];
  try solve[inverts dm2].
  inverts dm2. inverts dm1. inverts H.
  pick fresh x.
  forwards*: H1 x.
  pick fresh x and apply tp_all; eauto.
  Unshelve.
  apply (fv_tt B).
Qed.


Theorem precise_type2: forall E1 E2 e e' T T' P mu,
   P |== mu ->
   cpre E1 E2 -> 
   sepre e e' ->  
   typing E1 P e Inf T ->
   typing E2 P e' Inf T'->
   tpre T T'.
Proof.
    introv well cp ep Typ1 Typ2.
    gen T T'.
    inductions ep; intros;
    try solve[inverts* Typ1; inverts* Typ2].
    - 
      inverts Typ1. inverts Typ2.
      forwards*: binds_tpre H3 H5.
    -
      inverts* Typ1.
      inverts* Typ2.
      forwards*: IHep1 H4 H7.
      forwards*: dmatch_tpre_abs2 H1 H2.
      inverts* H0.
    -
      inverts* Typ1.
      inverts* Typ2.
      forwards*: IHep H6 H9.
      forwards*: dmatch_tpre_all2 H0 H5.
      inverts* H1.
      pick fresh y.
      forwards*: H10 y.
      assert(open_tt B1 B = subst_tt  B y (B1 open_tt_var y)).
      rewrite ( tsubst_typ_intro y); eauto.
      rewrite ( tsubst_typ_intro y); eauto.
      rewrite H4.
      forwards*: tpre_open H1 H.
    - inverts* Typ1.
      inverts* Typ2.
      forwards*: IHep H3 H5.
      forwards*: dmatch_tpre_ref2 H0 H1.
      inverts* H2.
Qed.



Theorem precise_type: forall E1 E2 e e' T T' P mu,
   P |== mu ->
   cpre E1 E2 -> 
   epre e e' ->  
   typing E1 P e Inf T ->
   typing E2 P e' Inf T'->
   tpre T T'.
Proof.
    introv well cp ep Typ1 Typ2.
    gen T T'.
    inductions ep; intros;
    try solve[inverts* Typ1; inverts* Typ2].
    - 
      inverts Typ1. inverts Typ2.
      forwards*: binds_tpre H3 H5.
    -
      inverts* Typ1.
      inverts* Typ2.
      forwards*: IHep1 H4 H7.
      forwards*: dmatch_tpre_abs2 H1 H2.
      inverts* H0.
    -
      inverts* Typ1.
      inverts* Typ2.
      forwards*: IHep H6 H9.
      forwards*: dmatch_tpre_all2 H0 H5.
      inverts* H1.
      pick fresh y.
      forwards*: H10 y.
      assert(open_tt B1 B = subst_tt  B y (B1 open_tt_var y)).
      rewrite ( tsubst_typ_intro y); eauto.
      rewrite ( tsubst_typ_intro y); eauto.
      rewrite H4.
      forwards*: tpre_open H1 H.
    - inverts* Typ1.
      inverts* Typ2.
      forwards*: IHep H3 H5.
      forwards*: dmatch_tpre_ref2 H0 H1.
      inverts* H2.
Qed.



Lemma env_less_precise_binds2 : forall x E F,
    binds x bind_tvar E ->
    cpre E F ->
    binds x bind_tvar F.
Proof.
  introv bind cp.
  inductions cp; try solve[inverts* bind];eauto.
  inverts* bind. inverts* H0.
  inverts* bind. inverts* H.
Qed.


Lemma tpre_wf_typ2: forall E F A B,
 tpre A B ->
 cpre E F ->
 wf_typ E A ->
 wf_typ F B.
Proof.
  introv tp wft. gen E F.
  inductions tp; intros; 
  try solve[inverts* H];auto.
  -
    inverts H.
    forwards*: env_less_precise_binds2 H2.
  - 
  inverts H1.
  pick fresh y and apply wf_typ_all.
  assert(cpre ((y, bind_tvar) :: E) ((y, bind_tvar) :: F)); eauto.
  eapply cp_cons2; eauto.
Qed.

Lemma cpre_wf_env: forall E1 E2,
 cpre E1 E2 ->
 wf_env E1 ->
 wf_env E2.
Proof.
  introv cp wf.
  inductions cp; eauto.
  inverts wf.
  forwards*: tpre_wf_typ2 H cp.
  forwards*: IHcp.
  forwards*: cpre_notin H5.
  inverts wf.
  forwards*: IHcp.
  forwards*: cpre_notin cp.
Qed.



Lemma cpre_consist : forall E F A1 B1,
  wf_env E ->
  cpre E F ->
  consist E A1 B1 ->
  consist F A1 B1.
Proof.
  introv wfv cp con. gen F.
  inductions con; intros; 
  try solve[forwards: cpre_wf_env cp;auto ].
  -
    forwards*: cpre_wf_env cp.
    forwards*: tpre_wf_typ2 H0.
  -
    assert(tpre A A). 
    forwards*: type_from_wf_typ H0.
    forwards*: tpre_wf_typ2 H1 H0.
    forwards*: cpre_wf_env cp.
  -
    assert(tpre A A). 
    forwards*: type_from_wf_typ H0.
    forwards*: tpre_wf_typ2 H1 H0.
    forwards*: cpre_wf_env cp.
  -
    pick fresh x and apply consist_all; auto.
Qed.



Lemma tpre_sim : forall E F A1 B1 A2 B2,
  wf_env E ->
  cpre E F ->
  consist E A1 B1 ->
  tpre A1 A2 ->
  tpre B1 B2 ->
  consist F A2 B2.
Proof.
  introv wfv cp s1 tp1 tp2.
  forwards*: tpre_consist s1 tp1 tp2.
  forwards*:  cpre_consist cp H.
Qed.


Lemma dmatch_tpre_abs: forall t1 t2 t4,
 tpre t1 t4 ->
 pattern_abs t1 t2 ->
 exists t5, pattern_abs t4 t5 /\
 tpre t2 t5.
Proof.
  introv tp dm. gen t2.
  inductions tp; intros; eauto;
  try solve[inverts* dm].
  inverts* dm.
  exists(t_arrow t_dyn t_dyn). splits*.
  inverts* H.
Qed.



Lemma dmatch_tpre_ref: forall t1 t2 t4,
 tpre t1 t4 ->
 pattern_ref t1 t2 ->
 exists t5, pattern_ref t4 t5 /\
 tpre t2 t5.
Proof.
  introv tp dm. gen t2.
  inductions tp; intros; eauto;
  try solve[inverts* dm].
  inverts* dm.
  exists(t_ref t_dyn). splits*.
  inverts* H.
Qed.

Lemma dmatch_tpre_all: forall t1 t2 t4,
 tpre t1 t4 ->
 pattern_all t1 t2 ->
 exists t5, pattern_all t4 t5 /\
 tpre t2 t5.
Proof.
  introv tp dm. gen t2.
  inductions tp; intros; eauto;
  try solve[inverts* dm].
  inverts dm. 
  inverts H.
  exists(t_all t_dyn). splits.
  eauto. pick fresh x and apply tp_all; eauto.
  inverts H.
  exists(t_all t_dyn). splits.
  eauto. pick fresh x and apply tp_all; eauto.
Qed.




Lemma inf_chk_epre2: forall E1 E2 P e1 e2 A B,
 sepre e1 e2 ->
 typing E1 P e1 Inf A ->
 typing E2 P e2 Chk B ->
 exists t,  typing E2 P e2 Inf t.
Proof.
  introv ep ty1 ty2.
  inverts* ty2.
  -
   inverts ep. inverts ty1.
  -
   inverts ep. inverts* ty1.
  -
    inverts ep. inverts* H4.
    inverts ty1.
    inverts H8.
Qed.


Theorem tpre_chk: forall E1 E2 e1 e2 T T' P mu,
   P |== mu ->
   cpre E1 E2 -> 
   sepre e1 e2 ->  
   typing E1 P e1 Chk T ->
   tpre T T' ->
   typing E2 P e2 Chk T'.
Proof.
  introv well cp ep typ tp. gen E1 E2 T T' P mu.
  inductions ep; intros.
  - inverts typ.
    inverts H0.
    forwards*: env_less_precise_binds H5. inverts H0. inverts H1.
    forwards*: cpre_uniq cp.
    forwards*: tpre_sim H H3 tp.
    forwards*: cpre_wf_env cp.
  -
    forwards*: cpre_wf_env cp.
    inverts typ. inverts H1.
    assert(tpre t_int t_int);eauto.
    forwards*: tpre_sim H0 H1 tp.
  -
    forwards*: cpre_wf_env cp.
    inverts typ. inverts H1.
    assert(tpre t_unit t_unit);eauto.
    forwards*: tpre_sim H0 H1 tp.
  -
    inverts typ as h1 h2; try solve[inverts h2].
    forwards h3: dmatch_tpre_abs tp h2.
    lets (tt1& h4 & h5): h3.
    inverts h5 as h51 h52; try solve[inverts h4].
    pick fresh x and apply typ_abs.
    assert(cpre ((x, bind_typ A1) :: E1) ((x, bind_typ C) :: E2)) as h6.
    apply cp_cons; auto.
    forwards h7: h1 x; auto.
    forwards h8: H0 x h6 h52 h7 well; eauto.
    auto.
  -
    inverts typ as h1 h2; try solve[inverts h2].
    forwards h3: dmatch_tpre_all tp h2.
    lets (tt1& h4 & h5): h3.
    inverts h5 as h51 h52; try solve[inverts h4].
    pick fresh x and apply typ_tabs.
    assert(cpre ((x, bind_tvar) :: E1) ((x, bind_tvar) :: E2)) as h6.
    apply cp_cons2; auto.
    forwards h7: h1 x; auto.
    forwards h8: H0 x h6 h7 well; eauto.
    auto.
  -
    inverts typ as h1 h2. 
    +
      inverts h2 as h2 h3 h4.
      forwards*h5: typing_chk h3.
      forwards* h6: IHep1 h5.
      inverts h6 as h6 h7; try solve[inverts ep1; inverts h3].
      *
        forwards* h8: precise_type2 ep1 h3 h7.
        forwards* h9: dmatch_tpre_abs h8 h2.
        lets(tt1&mma&tpp1): h9.
        inverts tpp1; try solve[inverts mma].
        forwards* h10: IHep2 H1 h4.
        forwards* h11: tpre_sim h1 H3 tp.
      *
       inverts ep1 as h8 h9.
       inverts h8 as h8.
       inverts h3 as h31 h32.
       inverts h32; auto.
    +
      inverts ep1.
      forwards* h3: typing_chk h2. 
      forwards*h4: IHep2 h3.
      inverts h4; try solve[inverts ep2 as hh1;
      inverts hh1 as hh1;
      inverts h2 as hh2 hh3;
      inverts hh3];
      try solve[inverts ep2; inverts* h2].
      forwards* h5: precise_type2 ep2 h2 H1.
      assert(tpre (t_arrow A T) (t_arrow A0 T')); auto.
      forwards* h6: IHep1 H2 well.
      inverts* h6; try solve[inverts* H4].
      inverts* H7.
  - 
    inverts typ as h1 h2. inverts h2 as h2 h3 h4.
    forwards h5: typing_chk h4. 
    forwards* h6: IHep cp h5 well.
    inverts h6 as h6 h7; try solve[inverts ep; inverts h4].
    +
    forwards h8: precise_type2 well ep h4 h7; auto.
    forwards* h9: dmatch_tpre_all h8 h3.
    lets(tt1&mma&tpp1): h9.
    inverts tpp1; try solve[inverts mma].
    assert(tpre (open_tt B0 A) (open_tt B1 B)) as h10.
    forwards*: tpre_type H.
    pick fresh y.
    forwards: H1 y. auto.
    rewrite (tsubst_typ_intro y); eauto.
    assert((open_tt B1 B) =
      (subst_tt B y (B1 open_tt_var y))).
    rewrite (tsubst_typ_intro y); eauto.
    rewrite H3.
    forwards*: tpre_open H2 H.
    forwards*: tpre_sim h1 h10 tp.
    eapply typ_consist with (A:= (open_tt B1 B)); eauto.
    eapply typ_tapp;eauto.
    forwards*: tpre_wf_typ2 cp h2.
    +
    inverts ep as h8 h9.
    inverts h8 as h8.
    inverts h4 as h41 h42.
       inverts h42; auto.
  -
    inverts typ. inverts H1.
    forwards*: IHep H.
    forwards*: tpre_sim H0 H tp.
  -
    inverts typ. inverts H0.
    forwards*: consist_regular H.
    destructs~ H0.
    forwards*: type_from_wf_typ H1.
    assert(tpre  (t_ref (store_Tlookup i P))  (t_ref (store_Tlookup i P))).
    eauto.
    forwards*: tpre_sim H H7 tp.
    eapply typ_consist; eauto.
    forwards*: consist_regular H8.
    destructs~ H9.
    apply typ_loc; eauto.
    inverts* H10.
  -
    inverts typ as h1 h2. inverts h2 as h2.
    forwards*h5: typing_chk h2.
    forwards* h6: IHep h5.
    inverts h6 as h6 h7; try solve[inverts ep; inverts h2].
    +
    forwards* h8: precise_type2 ep h2 h7.
    assert(tpre (t_ref A0) (t_ref A)) as h9; auto.
    forwards* h11: tpre_sim h1 h9 tp.
    +
    inverts ep as h8 h9.
    inverts h8 as h8.
    inverts h2 as h21 h22.
    inverts h22; auto.
  -
    inverts typ as h1 h2. inverts h2 as h2 h3.
    forwards*h5: typing_chk h3.
    forwards* h6: IHep h5.
    inverts h6 as h6 h7; try solve[inverts ep; inverts h3].
    +
    forwards* h8: precise_type2 ep h3 h7.
    forwards* h9: dmatch_tpre_ref h8 h2.
    lets(tt1&mma&tpp1): h9.
    inverts tpp1; try solve[inverts mma].
    assert(tpre (t_ref A) (t_ref B)) as h10; auto.
    forwards* h11: tpre_sim h1 H0 tp.
    +
    inverts ep as h8 h9.
    inverts h8 as h8.
    inverts h3 as h31 h32.
    inverts h32; auto.
  -
    inverts typ as h1 h2. inverts h2 as h2 h3 h4.
    forwards*h5: typing_chk h3.
    forwards* h6: IHep1 h5.
    inverts h6 as h6 h7; try solve[inverts ep1; inverts h3].
    +
    forwards* h8: precise_type2 ep1 h3 h7.
    forwards* h9: dmatch_tpre_ref h8 h2.
    lets(tt1&mma&tpp1): h9.
    inverts tpp1; try solve[inverts mma].
    forwards* h10: IHep2 h4.
    forwards* h11: tpre_sim h1 tp.
    +
    inverts ep1 as h8 h9.
    inverts h8 as h8.
    inverts h3 as h31 h32.
    inverts h32; auto.
    +
    inverts ep1 as h8.
Qed.



Theorem SGG_chk: forall E1 E2 e1 e2 T P mu,
   P |== mu ->
   cpre E1 E2 -> 
   sepre e1 e2 ->  
   typing E1 P e1 Chk T ->
   exists T', typing E2 P e2 Chk T' /\  tpre T T'.
Proof.
  introv well cp ep typ.
  assert(tpre T T).
  apply tpre_refl; eauto.
  forwards*: tpre_chk typ H.
Qed.


Theorem SGG_both: forall E1 E2 e1 e2 dir T P mu,
   P |== mu ->
   cpre E1 E2 -> 
   sepre e1 e2 ->  
   typing E1 P e1 dir T ->
   exists T', typing E2 P e2 dir T' /\  tpre T T'.
Proof.
  introv wel cp ep Typ1.
  destruct dir.
  -
  forwards* h1: typing_chk Typ1.
  forwards* h2: SGG_chk ep h1.
  lets(tt1&h3&h4): h2.
  forwards* h5: inf_chk_epre2 ep Typ1 h3.
  lets(tt2&h6): h5.
  forwards*: precise_type2 Typ1 h6.
  -
  forwards*: SGG_chk Typ1.
Qed.

Lemma meet_type:forall t1 t2 t3,
 meet t1 t2 t3 ->
 type t1 /\ type t2 /\ type t3.
Proof.
 introv me.
 inductions me; try solve[splits*];eauto.
 pick fresh y.
 forwards* h1: H0 y.
 inverts h1 as h1 h2.
 inverts h2 as h2 h3.
 forwards*: lc_t_all_exists h1. 
 forwards*: lc_t_all_exists h2.
 forwards*: lc_t_all_exists h3.  
Qed.



Lemma meet_tpre: forall t1 t2 t3 t4 t5 t6,
 meet t1 t2 t3 ->
 tpre t1 t4 ->
 tpre t2 t5 ->
 meet t4 t5 t6 ->
 tpre t3 t6.
Proof.
  introv me1 tp1 tp2 me2. gen t4 t5 t6.
  lets m1: me1.
  inductions me1; introv tp1 tp2 me2;
  try solve[inverts tp1; inverts tp2; auto; try solve[inverts me2; auto]];
  try solve[
    forwards* h1: meet_type m1;
    inverts h1 as hh1 hh2;
    inverts hh2 as hh2 hh3;
    forwards* h2: meet_type me2;
    inverts h2 as hh4 hh5;
    inverts hh5 as hh5 hh6;
    inverts tp1; inverts tp2; eauto; inverts me2; eauto
  ].  
  -
    forwards* h1: meet_type m1.
    inverts h1 as hh1 hh2.
    inverts hh2 as hh2 hh3.
    forwards* h2: meet_type me2.
    inverts h2 as hh4 hh5.
    inverts hh5 as hh5 hh6.
    inverts tp1; inverts tp2; eauto; inverts me2; eauto.
    +
      inverts hh1 as hh11 hh12.
      inverts hh5 as hh51 hh52.
      forwards* h3: IHme1_1 me1_1 H2 t_dyn.
    +
      inverts hh2 as hh21 hh22.
      inverts hh6 as hh61 hh62.
      forwards* h3: IHme1_2 me1_2 H3 t_dyn.
  -
    forwards* h1: meet_type m1.
    inverts h1 as hh1 hh2.
    inverts hh2 as hh2 hh3.
    forwards* h2: meet_type me2.
    inverts h2 as hh4 hh5.
    inverts hh5 as hh5 hh6.
    inverts tp1; inverts tp2; eauto; inverts me2; eauto;
    try solve[
      pick fresh y and apply tp_all;
      forwards* h3: H y
    ].
    +
    pick fresh y and apply tp_all.
    forwards* h3: H2 y.
    forwards* h4: H y.
    assert(t_dyn = t_dyn open_tt_var y) as h5.
    unfold open_tt; simpl; auto.
    inverts hh4 as hh4.
    forwards* h6: hh4 y.
    inverts hh2 as hh2.
    forwards* h8: hh2 y.
    +
    pick fresh y and apply tp_all.
    forwards* h3: H3 y.
    forwards* h4: H y.
    assert(t_dyn = t_dyn open_tt_var y) as h5.
    unfold open_tt; simpl; auto.
    inverts hh1 as hh1.
    forwards* h6: hh1 y.
    inverts hh6 as hh6.
    forwards* h8: hh6 y.
  -
    forwards* h1: meet_type m1.
    inverts h1 as hh1 hh2.
    inverts hh2 as hh2 hh3.
    forwards* h2: meet_type me2.
    inverts h2 as hh4 hh5.
    inverts hh5 as hh5 hh6.
    inverts tp1; inverts tp2; eauto; inverts me2; eauto.
    +
    inverts hh1 as hh1.
    inverts hh5 as hh5.
    forwards* h3: IHme1 me1 t_dyn H1 B0.
    +
    inverts hh2 as hh2.
    inverts hh6 as hh6.
    forwards* h3: IHme1 me1 H0 t_dyn.
Qed.




Lemma tpre_principle: forall e1 e2,
 value e1 ->
 value e2 ->
 epre e1 e2 ->
 tpre (dynamic_type e1) (dynamic_type e2).
Proof.
  introv wal1 wal2 ep.
  inductions ep; simpl; eauto.
Qed.


Lemma pval_tpre_principle: forall e1 e2,
 pvalue e1 ->
 pvalue e2 ->
 epre e1 e2 ->
 tpre (dynamic_type e1) (dynamic_type e2).
Proof.
  introv wal1 wal2 ep.
  inductions ep; simpl; eauto.
Qed.


Lemma Cast_dgg: forall P1 P2 mu1 mu2 p1 p2 v1' A1 B1 A2 B2 t1 t2,
 P1 |== mu1 ->
 P2 |== mu2 ->  
 mpre mu1 mu2 ->
 epre p1 p2 ->  
 tpre A2 B2 ->
 pvalue p1 ->
 pvalue p2 -> 
 typing nil P1 p1 Chk t1 ->
 typing nil P2 p2 Chk t2 -> 
 meet (dynamic_type p1) A2 A1 ->
 meet (dynamic_type p2) B2 B1 ->
 Cast (p1,mu1) A1 (r_e v1') ->
 exists v2' , Cast (p2,mu2) B1 (r_e v2') 
 /\ epre (e_val v1' A2) (e_val v2' B2).
Proof.
  introv wel1 wel2 mp. introv ep tp val1 val2 typ1 typ2 mt1 mt2 red. 
  gen P1 P2 mu2 p2 A2 B1 B2 t1 t2.
  inductions red; intros; eauto.
  -
    inverts* ep.
    simpl in *.
    inverts* mt2; try solve[exists*].
  -
    inverts* ep.
    simpl in *.
    inverts* mt2; try solve[exists*].
  -
    inverts val1 as val1.
    inverts ep as ep1 ep2.
    inverts ep2 as ep2 ep3.
    inverts ep3 as ep3.
    inverts val2 as val2.
    forwards* h2: meet_tpre mt1 mt2.
    forwards* h1:tpre_sim H ep2 h2.
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
    inverts val1 as val1.
    inverts ep as ep1 ep2.
    inverts ep2 as ep2 ep3.
    inverts ep3 as ep3.
    inverts val2 as val2.
    forwards* h2: meet_tpre mt1 mt2.
    forwards* h1:tpre_sim H ep2 h2.
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
    inverts val1 as val1.
    inverts ep as ep1 ep2.
    inverts ep2 as ep2 ep3.
    inverts val2 as val2.
    forwards* h2: meet_tpre mt1 mt2.
    forwards* hh1: store_lookup_epre o mp.
    forwards* hh2: epre_dynamic_type hh1.
    forwards* h1:tpre_sim (t_ref (dynamic_type (store_lookup o mu2))) H h2.
    simpl in *.
    forwards* h3: meet_more_precise mt1.
    lets(h4&h5): h3.
    inverts h4 as h4.
    forwards* h7: meet_more_precise mt2.
    lets(h8&h9): h7.
    inverts h8.
    exists. 
    splits*.
Qed.



Lemma Casts_dgg1: forall P1 P2 mu1 mu2 v1 v2 v1' A2 B2 t1 t2,
 P1 |== mu1 ->
 P2 |== mu2 ->  
 mpre mu1 mu2 ->
 epre v1 v2 ->  
 tpre A2 B2 ->
 value v1 ->
 value v2 -> 
 typing nil P1 v1 Chk t1 ->
 typing nil P2 v2 Chk t2 -> 
 Castv (v1,mu1) A2 (r_e v1') ->
 wf_typ nil A2 ->
 exists v2' , Castv (v2,mu2) B2 (r_e v2') 
 /\ epre v1' v2'.
Proof.
  introv wel1 wel2 mp. introv ep tp val1 val2 typ1 typ2 red wf.
  inverts red as h1 h2; try solve[inverts h2].
  inverts val1 as h3.
  inverts typ1 as h4 h5.
  inverts h5 as h5 h6 h7 h8.
  inverts ep as h9 h10.
  inverts val2 as h11 h12.
  inverts typ2 as h13 h14.
  inverts h14 as h14 h15.
  forwards* h18:pvalue_wf h7.
  forwards* h17: meet_sim2 h2.
  forwards* h19: epre_dynamic_type h10.
  forwards* h20: tpre_sim h17 h19 tp.
  forwards* h21: meet_progress  h20.
  lets(tt1&h22):h21.
  forwards* h23: meet_tpre h2 h22.
  forwards* h24: Cast_dgg h10 tp h2 h1.
  lets(ee1&h25&h26):h24.
  exists. splits*. 
Qed. 
    


Lemma Casts_prv_value1: forall v A v' mu,
 value v -> 
 Castv (v,mu) A (r_e v') 
     ->  value v'.
Proof with auto.
 introv val tlist.
 inverts tlist as h1 h2; try solve[inverts h2].
 inverts val as val1 val2.
 forwards* h6: meet_more_precise h2.
 inverts h6 as h6 h7.
 forwards* h8: tpre_type h7.
 forwards* h5: Cast_prv_pvalue h1.
Qed.



Lemma replace_epre:forall mu1 mu2 l v1 v2,
 mpre mu1 mu2 ->
 epre v1 v2 ->
 mpre (replace l v1 mu1) (replace l v2 mu2).
Proof.
  introv mp ep. gen mu1 mu2 v1 v2.
  inductions l; intros;
  try solve[inductions mp;  simpl; eauto].
Qed.


Lemma epre_ires: forall e1 e2,
 ires e1 ->
 epre e1 e2 ->
 ires e2.
Proof.
 introv ir ep.
 inverts ir; try solve[inverts* ep].
Qed.



Lemma typing_wf : forall E P e dir T,
  typing E P e dir T -> wf_typ E T.
Proof with simpl_env; try solve [auto | intuition auto].
  introv H.
  forwards* h1: typing_regular H.
Qed.


Lemma dynamic_guarantee_chk: forall e1 e2 P1 P2 mu1 mu1' mu2 e1' T1 T2, 
 P1 |== mu1 ->
 P2 |== mu2 ->  
 mpre mu1 mu2 ->
 epre e1 e2 -> 
 typing nil P1 e1 Chk T1 ->
 typing nil P2 e2 Chk T2 -> 
 step ( e1, mu1) ((r_e e1'),mu1') ->
 exists e2' mu2', step (e2,mu2) ((r_e e2'),mu2') /\ 
 epre e1' e2' /\ mpre mu1' mu2'.
Proof.
  introv wel1 wel2 mp ep typ1 typ2 red. gen e1' P1 P2 mu1 mu2 T1 T2.
  inductions ep; intros;
  try solve[inverts red as h1 h2 h3;
  destruct F; unfold fill in *; inverts h3].
  - (* lit *)
    inverts red as h1 h2 h3;
    try solve[destruct F; unfold fill in *; inverts h3];
    try solve[exists; splits*].
  - (* unit *)
    inverts red as h1 h2 h3;
    try solve[destruct F; unfold fill in *; inverts h3];
    try solve[exists; splits*].
  - (* app *)
    inverts red as h1 h2 h3.
    +
      destruct F; unfold fill in *; inverts* h3.
      *
      inverts typ1 as h4 h5;
      try solve[inverts ep1 as hh1; 
        forwards*: step_not_ires h2
      ].
      inverts typ2 as h6 h7;
      try solve[inverts ep1 as hh1; 
        forwards*: step_not_ires h2
      ].
      inverts h5 as h8 h9 h10. 
      inverts h7 as h11 h12 h13.
      forwards* h14: typing_chk h9.
      forwards* h15: typing_chk h12.
      forwards* h16: IHep1 h2. 
      lets(ee1& mmu1 & rred1& eep1&mp1): h16.
      forwards* h17: epre_expr ep2.
      exists. split*. 
      rewrite fill_appl.
      rewrite fill_appl.
      apply step_eval;eauto.
      *
      inverts typ1 as h4 h5;
      try solve[
      inverts h1;
      inverts h5 as h5 hh1; inverts hh1].
      inverts typ2 as h6 h7;
      try solve[
        inverts ep1 as hh1; 
        inverts h7 as hh2 hh3; inverts hh3
      ].
      forwards* h14: typing_chk h5.
      forwards* h15: typing_chk h7.
      forwards* h16: IHep2 h2. 
      lets(ee1& mmu1 & rred1& eep1&mp1): h16.
      inverts h1 as h1.
      exists. split*. 
      rewrite fill_appr.
      rewrite fill_appr.
      apply step_eval;eauto.
    +
      forwards*h4: val_prel ep2.
      forwards* h20: epre_exp ep1.
      forwards* h21: epre_exp ep2.
      inverts ep1 as h5 h6 h7 h8.
      lets ok: wel2.
      inverts wel2 as ok1 ok2.
      exists. splits*.
      pick fresh xx.
      assert((e0 ^^ e2') = [xx ~> e2'] (e0 ^ xx)) as h36.
      rewrite ( subst_exp_intro xx); eauto.
      rewrite (subst_exp_intro xx); eauto.
      rewrite h36.
      forwards* h37: h5 xx.
      forwards* h38: epre_open h37 ep2.
    +
      forwards*h5:epre_dynamic_type ep1.
      simpl in *.
      forwards*h6:dmatch_tpre_abs h5 h3.
      lets(tt1&h7&h8): h6.
      inverts h8; try solve[inverts h7].
      inverts typ1 as h10 h11.
      inverts h11 as h11 h12 h13.
      forwards* h14: typing_regular h12.
      inverts h14 as h14 h15.
      inverts h15 as h15 h16.
      inverts h15 as h15.
      inverts h15 as h15.
      inverts h15 as h15.
      forwards*h9: val_prel ep1.
      lets ok: wel2.
      inverts wel2 as h17 h18.
      inverts ep1 as h19 h20; inverts h9.
      inverts h20 as h20 h21.
      inverts h21; try solve[inverts h19].
      inverts H12.
      inverts* h19.
      inverts h20.
      inverts H9.
      exists.
      splits*.
      apply ep_anno; eauto.
      apply ep_anno; eauto.
      apply ep_anno; eauto.
      apply ep_app; eauto.    
  - (* tapp *)
    inverts red as h1 h2 h3.
    +
      inverts typ1 as h4 h5.
      inverts h5 as h5 h6 h7.
      inverts typ2 as h8 h9.
      inverts h9 as h9 h10 h11.
      forwards* h12: typing_chk h7.
      forwards* h13: typing_chk h11.
      destruct F; unfold fill in *; inverts h3. 
      forwards* h14: IHep h2. 
      lets(ee2&mmu1&h15&h16&h17): h14.
      exists. split*. 
      rewrite fill_tapp.
      assert((e_tapp ee2 B) = fill (tappCtx B) ee2) as h18.
      eauto.
      rewrite h18;eauto.
    +
      inverts ep as h3 h4 h5 h6.
      inverts h4 as h7 h8.
      inverts h8 as h8 h9.
      forwards*h10: epre_expr h9.
      inverts h9 as h9. 
      forwards* h11: dmatch_tpre_all h5 h2.
      lets(tt1&h12&h13): h11.
      inverts h3 as h14 h15.
      inverts h13 as h13; try solve[inverts h12].
      forwards* h: tpre_type H.
      exists. splits*.
      apply ep_anno; eauto.
      pick fresh xx.
      assert(open_tt B0 B = subst_tt B xx (B0 open_tt_var xx)) as h16.
      rewrite ( tsubst_typ_intro xx); eauto.
      rewrite ( tsubst_typ_intro xx); eauto.
      rewrite h16.
      forwards*h17: h13 xx.
      forwards*h18: tpre_open h17 H.
      
      apply ep_anno; eauto.
      inverts h7 as h7.
      pick fresh xx.
      assert(open_tt B2 B = subst_tt B xx (B2 open_tt_var xx)) as h16.
      rewrite ( tsubst_typ_intro xx); eauto.
      rewrite ( tsubst_typ_intro xx); eauto.
      rewrite h16.
      forwards*h17: h7 xx.
      forwards*h18: tpre_open h17 H.

      apply ep_anno; eauto.
      inverts h8 as h8.
      pick fresh xx.
      assert(open_tt A4 B = subst_tt B xx (A4 open_tt_var xx)) as h16.
      rewrite ( tsubst_typ_intro xx); eauto.
      rewrite ( tsubst_typ_intro xx); eauto.
      rewrite h16.
      forwards*h17: h8 xx.
      forwards*h18: tpre_open h17 H.

      pick fresh xx.
      assert(open_te e2 B = subst_te  B xx (e2 open_te_var xx)) as h16.
      rewrite ( tsubst_exp_intro xx); eauto.
      rewrite ( tsubst_exp_intro xx); eauto.
      rewrite h16.
      forwards* h17: h9 xx.
      forwards*: etpre_open h17 H.
  - (* anno *)
    inverts red as h1 h2 h3.
    +
      inverts typ1 as h4 h5.
      inverts h5 as h5 h6.
      inverts typ2 as h7 h8.
      inverts h8 as h8 h9.
      destruct F; unfold fill in *; inverts h3. 
      forwards* h11: IHep h2. 
      lets(ee2&mmu1&h12&h13&h14): h11.
      exists. split*. 
      rewrite fill_anno.
      assert((e_anno ee2 A) = fill (annoCtx A) ee2) as h15.
      eauto.
      rewrite h15;eauto.
    +
      inverts typ1 as h4 h5.
      inverts h5 as h5 h6.
      inverts typ2 as h7 h8.
      inverts h8 as h8 h9.
      forwards* h11: val_prel ep.
      forwards* h12: tpre_type H.
      lets wel2': wel2.
      inverts wel2 as ok1 ok2.
      forwards* h10: Casts_dgg1 ep H h3; auto.
      lets(ee1&h13&h14): h10.
      exists. splits*. 
    +
      forwards* h: epre_expr ep.
      inverts ep as h4.
      forwards* h5: dmatch_tpre_abs H h2.
      lets(tt1&h6&h7): h5.
      forwards* h8: tpre_type H.
      inverts h8 as h8 h9.
      inverts h7; try solve[inverts h6].
      inverts h6 as h10; simpl in *.
      *
        exists. splits*.
        apply ep_val; eauto.
        apply ep_anno; eauto.
      *
        exists. splits*.
        apply ep_val;simpl in *; eauto.
        apply ep_anno; eauto.
    +
      forwards* h: epre_expr ep.
      inverts ep as h4.
      forwards* h5: dmatch_tpre_all H h2.
      lets(tt1&h6&h7): h5.
      forwards* h8: tpre_type H.
      inverts h8 as h8 h9.
      inverts h7; try solve[inverts h6].
      inverts h6 as h10; simpl in *.
      *
        exists. splits*.
        apply ep_val; eauto.
        apply ep_anno; eauto.
      *
        exists. splits*.
        apply ep_val;simpl in *; eauto.
        apply ep_anno; eauto.
  - (* loc *)
    inverts red as h1 h2 h3;
    try solve[destruct F; unfold fill in *; inverts h3];
    try solve[exists; splits].
    forwards* h4: store_lookup_epre i mp.
    forwards* h5: epre_dynamic_type h4.
    forwards* h6:tpre_type h5.
    inverts h6 as h61 h62.
    exists. splits*.
  - (* ref *)
    inverts red as h1 h2 h3; try solve[
    ]; try solve[].
    +
      inverts typ2 as h4 h5.
      inverts h5 as h5.
      forwards* h6: typing_chk h5.
      inverts typ1 as h7 h8.
      inverts h8 as h8 h9.
      forwards* h10: typing_chk h8.
      destruct F; unfold fill in *; inverts h3. 
      forwards* h11: IHep h2. 
      lets(ee2&mmu1&h12&h13&h14): h11.
      exists. split*. 
      rewrite fill_ref.
      assert((e_ref ee2) = fill refCtx ee2) as h15.
      eauto.
      rewrite h15;eauto.
    +
      forwards* h4: mpre_length mp.
      rewrite h4.
      forwards* h5: val_prel ep.
      inverts wel2 as h6 h7.
      exists (e_loc (length mu2)) (mu2++e2::nil).
      split*. split*.
      apply mpre_app; eauto.  
  - (* get *)
    inverts red as h1 h2 h3.
    +
      inverts typ2 as h4 h5.
      inverts h5 as h51 h52.
      forwards* h6: typing_chk h52.
      inverts typ1 as h7 h8.
      inverts h8 as h8 h9.
      forwards* h10: typing_chk h9.
      destruct F; unfold fill in *; inverts h3. 
      forwards* h11: IHep h2. 
      lets(ee2&mmu1&h12&h13&h14): h11.
      exists. split*. 
      rewrite fill_get.
      assert((e_get ee2) = fill getCtx ee2) as h15.
      eauto.
      rewrite h15;eauto.
    +
      inverts ep as h4 h5 h6 h7. 
      inverts h5 as h5 h8.
      inverts h8.
      inverts h4 as h4.
      simpl in *. 
      forwards* h9: store_lookup_epre l0 mp.
      forwards* h10: dmatch_tpre_ref h6 h2. 
      lets(tt1& h11 & h12): h10.
      inverts h12; try solve[inverts h11].
      inverts wel2 as h13 h14.
      inverts h14 as h14 h15.
      inverts h5 as h5.
      exists. splits*.
  - (* set *)
    inverts red as h1 h2 h3.
    +
      destruct F; unfold fill in *; inverts* h3.
      *
      inverts typ1 as h4 h5.
      inverts typ2 as h6 h7.
      inverts h5 as h8 h9 h10;
      try solve[forwards* hh0:step_not_rv h2].
      inverts h7 as h11 h12 h13;
      try solve[inverts ep1;forwards* hh0:step_not_rv h2].
      forwards* h14: typing_chk h9.
      forwards* h15: typing_chk h12.
      forwards* h16: IHep1 h2. 
      lets(ee1& mmu1 & rred1& eep1&mp1): h16.
      forwards* h17: epre_expr ep2.
      exists. split*. 
      rewrite fill_setl.
      rewrite fill_setl.
      apply step_eval;eauto.
      *
      inverts typ1 as h4 h5.
      inverts typ2 as h6 h7.
      inverts h5 as h8 h9 h10;
      try solve[inverts h1 as h1; inverts h9].
      inverts h7 as h11 h12 h13.
      --
      forwards* h14: typing_chk h9.
      forwards* h15: typing_chk h12.
      forwards* h16: IHep2 h2. 
      lets(ee1& mmu1 & rred1& eep1&mp1): h16.
      inverts h1 as h1.
      inverts ep1.
      exists. split*. 
      rewrite fill_setr.
      rewrite fill_setr.
      apply step_eval;eauto.
      --
      forwards* h14: typing_chk h9.
      forwards* h15: typing_chk h12.
      forwards* h16: IHep2 h2. 
      lets(ee1& mmu1 & rred1& eep1&mp1): h16.
      inverts h1 as h1.
      inverts ep1.
      exists. split*. 
      rewrite fill_setr.
      rewrite fill_setr.
      apply step_eval;eauto.
    +
      forwards*h4: val_prel ep2.
      inverts ep1 as h5 h6 h7 h8.
      inverts typ1 as h9 h10.
      inverts h10 as h10 h11 h12; try solve[inverts h11].
      inverts typ2 as h21 h22.
      inverts h22 as h22 h23 h24; try solve[inverts h23].
      forwards* hh1: store_lookup_epre l0 mp.
      forwards* tp3: epre_dynamic_type hh1.

      lets ok1: wel1.
      lets ok2: wel2.
      inverts ok1 as ok1 ok3.
      inverts ok3 as ok3 ok4.
      inverts ok2 as ok5 ok6.
      inverts ok6 as ok6 ok7.
      rewrite ok3 in *.
      rewrite ok6 in *.
      forwards* hh2: ok4 l0.
      forwards* hh3: ok7 l0.
      forwards* hh4: sto_ok_value ok1.
      forwards* hh5: sto_ok_value ok5.
      forwards* hh6: principle_typ_inf hh2.
      forwards* hh7: principle_typ_inf hh3.
      rewrite <- hh6 in *.
      rewrite <- hh7 in *.
      lets ok: wel2.
      inverts wel2 as ok1 ok2.
      forwards* hh8: replace_epre l0 mp ep2.
      exists.
      split*.
    +
      forwards*h10: typing_regular typ1.
      inverts h10 as h11 h12.
      inverts h12 as h12 h13.
      inverts h12 as h12.
      inverts h12 as h12.
      inverts h12 as h12.
      forwards*h5:epre_dynamic_type ep1.
      forwards*h6:dmatch_tpre_ref h5 h2.
      lets(tt1&h7&h8): h6.
      inverts h8; try solve[inverts h7].
      forwards*h9: val_prel ep1.
      lets ok: wel2.
      inverts wel2.
      inverts ep1 as h14 h15; try solve[inverts h9].
      inverts h15 as h15 h16; try solve[inverts h14].
      inverts h16.
      inverts h14.
      simpl in *.
      forwards* h17: store_lookup_epre l0 mp.
      forwards* h18: epre_dynamic_type h17.
      inverts h15.
      exists. splits*.
      Unshelve.
      apply {}.
      apply {}.
Qed.



Lemma dynamic_guarantee_dir: forall e1 e2 P1 P2 mu1 mu1' mu2 e1' T1 T2 dir, 
 P1 |== mu1 ->
 P2 |== mu2 ->  
 mpre mu1 mu2 ->
 epre e1 e2 -> 
 typing nil P1 e1 dir T1 ->
 typing nil P2 e2 dir T2 -> 
 step ( e1, mu1) ((r_e e1'),mu1') ->
 exists e2' mu2', step (e2,mu2) ((r_e e2'),mu2') /\ 
 epre e1' e2' /\ mpre mu1' mu2'.
Proof.
  introv wel1 wel2 mp ep typ1 typ2 red. 
  destruct dir.
  - forwards* h1: typing_chk typ1. 
    forwards* h2: typing_chk typ2. 
    forwards*: dynamic_guarantee_chk h1 h2 red.
  - forwards*: dynamic_guarantee_chk typ1 typ2.
Qed.














