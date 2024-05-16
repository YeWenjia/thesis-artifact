Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
    syntax_ott
    syntaxb_ott
    rules_inf
    rulesb_inf
    Typing 
    Infrastructure
    Infrastructure_b
    Typing_b
    Type_Safety
    ttyping
    Omega
    Lia.



    Lemma ssub_sub: forall A B,
    ssub A B ->
    sub A B.
   Proof.
     introv sub.
     inductions sub; eauto.
   Qed.
   
   
   
   
   Lemma tpre_factoring_right_gen2: forall t1 t2 n,
   size_typ t1 + size_typ t2 < n ->
   ssuba t1 t2 ->
   ssubb t2 t1 ->
   tpre t1 t2.
   Proof.
    introv sz suba subb. gen t1 t2.
    inductions n; intros;try solve[omega].
    inductions suba; eauto; simpl in *;
    try solve[
    inverts subb;
    try solve[eauto]].
    -
    inverts subb.
    forwards*: IHn H3 H. omega.
    forwards*: IHn suba H5. omega.
    eauto.
    -
    inverts subb as h1 h2.
    forwards*: IHn suba1 h1. omega.
    forwards*: IHn suba2 h2. omega.
   Qed.
   
   
   
   Lemma ttpre_factoring_right2: forall t1 t2,
   ssuba t1 t2 ->
   ssubb t2 t1 ->
   tpre t1 t2.
   Proof.
    introv suba subb.
    eapply tpre_factoring_right_gen2; eauto.
   Qed.
   
   
   Lemma ssub_factoring_right_gen2: forall t1 t2 n,
   size_typ t1 + size_typ t2 < n ->
   ssuba t1 t2 ->
   ssubb t1 t2 ->
   ssub t1 t2.
   Proof.
    introv sz suba subb. gen t1 t2.
    inductions n; intros; try solve[omega].
    inductions suba; eauto.
    -
    inverts* subb; eauto. simpl in *.
    forwards*: IHn H3 H. omega.
    forwards*: IHn suba H5. omega.
    inverts suba.
    inverts* H.
    -
    inverts* subb.
    -
    inverts subb as h1 h2; eauto. simpl in *.
    forwards*: IHn suba1 h1. omega.
    forwards*: IHn suba2 h2. omega.
   Qed.
   
   
   Lemma ssub_factoring_right2: forall t1 t2,
   ssuba t1 t2 ->
   ssubb t1 t2 ->
   ssub t1 t2.
   Proof.
    introv suba subb.
    eapply ssub_factoring_right_gen2; eauto.
   Qed.
   
   
   Lemma ssub_factoring: forall t1 t2,
   ssub t1 t2 ->
   ssuba t1 t2 /\
   ssubb t1 t2.
   Proof.
    introv sub.
    inductions sub; eauto;
    try solve[inverts IHsub1; inverts* IHsub2].
   Qed.
   
   
   
   Lemma ttpre_factoring: forall t1 t2,
   tpre t1 t2 ->
   ssuba t1 t2 /\
   ssubb t2 t1.
   Proof.
    introv tp.
    inductions tp; eauto;
    try solve[inverts IHtp1; inverts* IHtp2].
   Qed.
   
   Lemma subb_arrow: forall t t1 t2,
    Ground t ->
    subb (t_arrow t1 t2) t ->
    t1 = t_dyn /\ subb t2 t_dyn.
   Proof.
     introv gr sub.
     inductions sub;inverts* gr;eauto.
     inductions H; eauto.
   Qed.


   Lemma subb_pro: forall t t1 t2,
   Ground t ->
   subb (t_pro t1 t2) t ->
   subb t1 t_dyn /\ subb t2 t_dyn.
  Proof.
    introv gr sub.
    inductions sub;inverts* gr;eauto.
  Qed.
   
   
   
   Lemma tpre_factoring_right_gen: forall t1 t2 n,
   size_typ t1 + size_typ t2 < n ->
   suba t1 t2 ->
   subb t2 t1 ->
   tpre t1 t2.
   Proof.
    introv sz suba subb. gen t1 t2.
    inductions n; intros;try solve[omega].
    inverts* suba; eauto; simpl in *.
    inverts* subb; eauto.
    -
      forwards*: IHn H4 H. omega.
      forwards*: IHn H0 H6. omega.
    -
      forwards* h1: subb_arrow H2. inverts h1. subst.
      inverts* H4.
      assert(subb D B) as h2; eauto.
      forwards*: IHn H0 h2. omega.
    -
      inverts subb as h1 h2.
      +
      forwards* h3: subb_pro h2. inverts h3 as h3 h4. 
      inverts* h3.
      *
        inverts* h4.
        assert(subb D B) as h5; eauto.
        forwards*: IHn H0 h5. omega.
      *
        assert(subb C A) as h6; eauto.
        forwards*: IHn H h6. omega.
        inverts* h4.
        assert(subb D B) as h5; eauto.
        forwards*: IHn H0 h5. omega.
      +
      forwards*: IHn H h1. omega.
      forwards*: IHn H0 h2. omega.
   Qed.
   
   
   
   Lemma tpre_factoring_right: forall t1 t2,
   suba t1 t2 ->
   subb t2 t1 ->
   tpre t1 t2.
   Proof.
    introv suba subb.
    eapply tpre_factoring_right_gen; eauto.
   Qed.
   
   
   
   
   
   Lemma sub_factoring_right_gen: forall t1 t2 n,
   size_typ t1 + size_typ t2 < n ->
   suba t1 t2 ->
   subb t1 t2 ->
   sub t1 t2.
   Proof.
    introv sz suba subb. gen t1 t2.
    inductions n; intros; try solve[omega].
    inverts* suba; eauto.
    -
     inverts* subb; eauto. simpl in *.
     forwards*: IHn H0 H6. omega.
     forwards*: IHn H4 H. omega.
     forwards* h1: subb_arrow H2.
     inverts* h1.
     assert(suba C t_dyn) as h1; eauto.
     forwards* h2: IHn h1 H. simpl in *; lia.
     inverts* H4.
     +
     assert(subb t_dyn D) as h3; eauto.
     forwards* h5: IHn H0 h3. simpl in *; lia.
     +
     assert(subb B D) as h3; eauto.
     forwards* h5: IHn H0 h3. simpl in *; lia.
    -
      destruct t1; inverts* subb.
      +
      forwards* h1: subb_arrow H0.
      inverts* h1.
      assert(suba t1_2 t_dyn) as h1; eauto.
     forwards* h2: IHn h1 H2. simpl in *; lia.
     +
     forwards* h1: subb_pro H0.
     inverts h1 as h1 h2.
     assert(suba t1_1 t_dyn) as h3; eauto.
     forwards* h4: IHn h3 h1. simpl in *; lia.
     assert(suba t1_2 t_dyn) as h5; eauto.
     forwards* h6: IHn h5 h2. simpl in *; lia.
    -
     inductions subb; eauto. 
     +
        forwards* h1: subb_pro subb.
        inverts h1 as h1 h2.
        inverts* h1.
        *
          inductions H0.
          inverts* h2.
          --
          inductions H1; eauto.
          --
          assert(syntax_ott.subb B D) as h3; eauto.
          forwards* h4: IHn H1 h3. simpl in *; lia.
        *  
          assert(syntax_ott.subb A C) as h3; eauto.
          forwards* h4: IHn H0 h3. simpl in *; lia.
          inverts* h2.
          --
          inductions H1; eauto.
          --
          assert(syntax_ott.subb B D) as h5; eauto.
          forwards* h6: IHn H1 h5. simpl in *; lia.
     +
     simpl in *.
     forwards*: IHn H subb1. omega.
     forwards*: IHn H0 subb2. omega.
Qed.
   
   
   Lemma sub_factoring_right: forall t1 t2,
   suba t1 t2 ->
   subb t1 t2 ->
   sub t1 t2.
   Proof.
    introv suba subb.
    eapply sub_factoring_right_gen; eauto.
   Qed.
   
   
   Lemma sub_factoring: forall t1 t2,
   sub t1 t2 ->
   suba t1 t2 /\
   subb t1 t2.
   Proof.
    introv sub.
    inductions sub; eauto;
    try solve[inverts IHsub1; inverts* IHsub2].
    -
    inductions H; try solve[inverts* sub].
   Qed.
   
   
   
   
   Lemma tpre_factoring: forall t1 t2,
   tpre t1 t2 ->
   suba t1 t2 /\
   subb t2 t1.
   Proof.
    introv tp.
    inductions tp; eauto;
    try solve[inverts IHtp1; inverts* IHtp2].
Qed.
   

Lemma UG_tp: forall A B,
  UG A B ->
  tpre A B.
Proof.
 introv h1.
 inverts h1 as h1 h2.
 inverts h2 as h2 h3.
 inverts h3 as h3 h4.
 inverts h2; inverts* h1.
Qed.


Lemma subb_dyn_inv: forall A B,
 subb A t_dyn ->
 subb A B.
Proof.
 introv sb.
 inductions sb; eauto.
Qed.


Lemma subb_ground: forall A B,
 Ground A ->
 subb A B.
Proof.
 introv sb.
 inductions sb; eauto.
Qed.


Lemma subb_pro_inv: forall A1 A2 A B,
 subb (t_pro A1 A2) (t_pro A B) ->
 subb A1 A /\ subb A2 B.
Proof.
  introv sb.
  inductions sb; eauto.
  forwards h1: subb_pro sb; auto.
  inverts h1 as h1 h2.
  forwards h3: subb_dyn_inv A h1.
  forwards h4: subb_dyn_inv B h2.
  auto.
Qed.


Lemma safe_Cast: forall w A w' l b l0 b0,
 value w ->
 Safe nil (e_anno w l0 b0 A) l b ->
 Cast w l0 b0 A (e_exp w') ->
 Safe nil w' l b.
Proof.
  introv wal sf red. 
  gen l b.
  inductions red; intros;eauto;
  try solve[inverts* sf].
  -
    forwards* h1: ug_ground_r H.
    forwards* h3: UG_tp H.
    forwards* h2: tpre_factoring h3.
    inverts h2 as h2 h4.
    inverts sf as h5 h6 h7; try solve[inverts wal].
    +
      forwards h8: principle_inf h5; auto.
      rewrite h8 in *. 
      assert(Safe nil ((e_anno v l b0 B)) l b0) as h9; eauto.
      forwards h10: IHred v' h9; auto.
      forwards h12: Cast_sim red h5; auto.
      forwards h11:Cast_preservation red; eauto.
    + 
      forwards h8: principle_inf h5; auto.
      rewrite h8 in *.
      forwards h13: subb_dyn_inv B h6.
      assert(Safe nil ((e_anno v l (negb b0) B)) l b0) as h9; eauto.
      forwards h10: IHred v' h9; auto.
      forwards h12: Cast_sim red h5; auto.
      forwards h11:Cast_preservation red; eauto.
      forwards h14: subb_ground t_dyn h1.
      eauto.
    +
      assert(Safe nil ((e_anno v p b B)) l b0) as h9; eauto.
  -
    inverts sf as h1 h2 h3.
    +
      inverts h1 as h1. inverts h1 as h1. inverts h2 as h2.
      inverts* H.
    +
      inverts wal as h01 h02.
      inverts h1 as h1. inverts h1 as h1. 
      forwards* h6: principle_inf h1.
      rewrite h6 in *.
      inverts* h2.
      *
        forwards* h7: subb_ground A h01.
        assert(Safe nil v l b) as h8.
        inverts* h3.
        assert(Safe nil (e_anno v l (negb b) A) l b) as h5. eauto.
        forwards*: IHred.
      *
        forwards* h7: subb_ground A h01.
        assert(Safe nil v l b) as h8.
        inverts* h3.
        assert(Safe nil (e_anno v l (negb b) A) l b) as h5. eauto.
        forwards*: IHred.
     +
        inverts wal.
        assert(Safe nil v l b) as h8.
        inverts* h1.
        assert(Safe nil (e_anno v p b2 A) l b) as h5. eauto.
        forwards*: IHred.
  -
    inverts* sf;try solve[ inverts* H8];
    try solve[inverts* H4].
  -
    inverts wal.
    inverts sf as h1 h2 h3.
    +
      inverts h1 as h4 h5.
      inverts h2 as h6 h7.
      assert(Safe nil (e_anno v1 l b0 A) l b0) as h8.
      inverts* h3.
      assert(Safe nil (e_anno v2 l b0 B) l b0) as h9.
      inverts* h3.
      forwards* h10: IHred1.
    +
      inverts h1 as h4 h5.
      forwards* h6: subb_pro_inv h2.
      inverts h6 as h6 h7.
      assert(Safe nil (e_anno v1 l (negb b0) A) l b0) as h8;eauto.
      inverts* h3.
      assert(Safe nil (e_anno v2 l (negb b0) B) l b0) as h9;eauto.
      inverts* h3.
    +
      inverts h1 as h4 h5.
      assert(Safe nil (e_anno v1 p b A) l b0) as h8;eauto.
Qed.



Lemma anno_chk: forall e t1 t2 l b,
 nil ⊢ e_anno e l b t1 ⇒ t2 ->
 exists t3, Typing nil e Chk t3.
Proof.
  introv typ.
  inverts* typ.
Qed.




Lemma safe_weaken: forall  F1 G1 G3 e1 l b ,
 Safe (G3 ++ G1) e1 l b ->
 uniq (G3 ++F1 ++  G1) ->
 Safe (G3 ++F1 ++  G1) e1 l b .
Proof.
  introv sf. gen F1.
  inductions sf; intros;eauto;
  try solve[forwards*: Typing_weaken H H0];
  try solve[forwards*: Typing_weaken H H1].
  -
    pick fresh y. eapply Safe_abs with (L := union L
    (union (singleton l1)
       (union (singleton l2)
          (union (dom G1) (union (dom G3) (union (dom F1) (fv_exp e)))))));intros; auto.
    rewrite_env (((x, A) :: G3) ++ F1 ++ G1).
    forwards: H0 x G1 ([(x, A)] ++ G3). 
    auto.
    auto.
    auto.
    assert(uniq (((x, A) :: G3) ++ F1 ++ G1)).
    solve_uniq.
    apply H3. 
    assert(uniq (((x, A) :: G3) ++ F1 ++ G1)).
    solve_uniq.
    apply H3.
Qed.


Lemma safe_weakening : forall E1 F1 e1 l b,
    Safe E1 e1 l b ->
    uniq (F1 ++ E1) ->
    Safe (F1 ++ E1) e1 l b.
Proof.
  intros.
  rewrite_env (nil ++ F1 ++ E1).
  apply~ safe_weaken.
Qed.


Lemma safe_open1: forall e1 u1 x A GG1 G1 l b,
 Safe (GG1 ++ [(x,A)] ++ G1) e1 l b ->
 Safe G1 u1 l b ->
 Typing G1 u1 Inf A ->
 Safe (GG1++G1) [x~> u1]e1 l b.
Proof.
  introv sf1 sf2 ty1 . gen u1.
  inductions sf1; intros; 
  simpl; eauto;
  try solve[forwards* h1: IHsf1_1;
  forwards* h2: IHsf1_2;
  forwards*: Typing_subst_1 H ty1];
  try solve[forwards* h1: IHsf1;
  forwards*: Typing_subst_1 H ty1].
  -
    forwards*: Typing_weakening ty1.
    forwards*: Typing_weaken H0 H.
    forwards* h1: Typing_regular_2 H0.
    forwards*: safe_weakening sf2 h1.
    destruct (x0 == x); eauto.
  -
    pick fresh y.
    eapply Safe_abs with (L:=  union L
    (union (singleton l1)
       (union (singleton l2)
          (union (singleton x)
             (union (dom GG1)
                (union (dom G1) (union (fv_exp e) (fv_exp u1))))))));intros; auto.
    forwards* lc: Typing_regular_1 ty1. 
    rewrite subst_exp_open_exp_wrt_exp_var; auto.
    rewrite_env (([(x0, A0)] ++ GG1) ++ G1).
    forwards*: H0 x0 x  ty1 .
    auto.
Qed.


Lemma safe_open: forall e1 u1 x A  G1 l b,
 Safe ( [(x,A)] ++ G1) e1 l b ->
 Safe G1 u1 l b ->
 Typing G1 u1 Inf A ->
 Safe (G1) [x~> u1]e1 l b.
Proof.
  introv sf1 sf2 ty1 . introv.
  rewrite_env (nil ++ G1).
  eapply safe_open1; eauto.
Qed.



Lemma anno_prv: forall e1 e2 l1 b1 l2 b2 t t2,
 nil ⊢ e1 ⇒ t ->
 nil ⊢ e2 ⇒ t ->
 Safe nil e2 l2 b2 ->
 Safe nil (e_anno e1 l1 b1 t2) l2 b2 ->
 Safe nil (e_anno e2 l1 b1 t2) l2 b2.
Proof.
  introv typ1 typ2 sf1 sf2.
  inverts* sf2; try solve[inverts typ1].
  -
  forwards*: inference_unique typ1 H6. subst*.
  -
  forwards*: inference_unique typ1 H6. subst*.
Qed.


Lemma safe_inner: forall e A l1 b1 l2 b2,
  Safe nil (e_anno e l1 b1 A) l2 b2 ->
  Safe nil e l2 b2.
Proof.
  introv sf.
  inverts* sf; try solve[inverts typ].
Qed.



Lemma safe_preservation: forall dir e A l b e',
 Typing nil e dir A ->
 Safe nil e l b ->
 step e (e_exp e') ->
 Safe nil e' l b.
Proof.
  introv Typ safe Red. gen dir A.
  inductions Red;intros; eauto.
  - (* do step *)
    destruct E; unfold fill in *.
    +
      inverts Typ. 
      --
      inverts safe.
      *
        forwards*: safe_inner H11.
        forwards*: IHRed H8.
        forwards: preservation H10 Red.
        forwards*: anno_prv H1 H11.
      *
        forwards*: IHRed H8.
        forwards*: preservation H10 Red.
      --
      inverts H0.
      inverts safe.
      *
      forwards*: safe_inner H12.
      forwards*: IHRed H11.
      forwards: preservation H11 Red.
      forwards*: anno_prv H2 H12.
      *
      forwards*: IHRed H12.
      forwards*: preservation H11 Red.
    +
      inverts Typ. 
      --
      inverts safe.
      *
        inverts H.
        forwards*: principle_inf H10.
        rewrite H in *. inverts H2.
      *
      forwards*: Typing_regular_1 H10.
      inverts H9.
      forwards: safe_inner H12.
      forwards*: IHRed H3.
      forwards: preservation H1 Red.
      forwards*: anno_prv H4 H12.
      --
      inverts safe.
      *
        inverts H.
        forwards*: principle_inf H9.
        rewrite H in *. inverts H4.
      *
      inverts H0.
      forwards*: Typing_regular_1 H12.
      inverts H13.
      forwards: safe_inner H11.
      forwards*: IHRed H4.
      forwards: preservation H2 Red.
      forwards*: anno_prv H5 H11.
    +
      inverts Typ. 
      --
      inverts safe.
      *
      forwards*: IHRed H7.
      forwards*: preservation H8 Red.
      *
      forwards*: IHRed H7.
      forwards*: preservation H8 Red.
      *
      forwards*: IHRed H7.
      --
      inverts H0.
      inverts safe.
      *
      forwards*: IHRed H11.
      forwards*: preservation H9 Red.
      *
      forwards*: IHRed H11.
      forwards*: preservation H9 Red.
      *
      forwards*: IHRed H8.
    +
      inverts Typ. 
      --
      inverts safe.
      inverts* H0.
      --
      inverts* safe.
    +
       inverts Typ. 
      --
      inverts safe.
      inverts* H0.
      --
      inverts* safe.
    +
      inverts Typ as typ1 typ2. 
      --
        inverts typ1 as typ11 typ12.
        inverts safe as h1 h2.
        forwards* h3: IHRed h1.
      --
        inverts safe as h1 h2.
        forwards* h3: IHRed h1.
    +
       inverts Typ as typ1 typ2. 
      --
        inverts typ1 as typ11 typ12.
        inverts safe as h1 h2.
        forwards* h3: IHRed h2.
      --
        inverts safe as h1 h2.
        forwards* h3: IHRed h2.
    +
      inverts Typ as typ1 typ2. 
      --
        inverts typ1 as typ11 typ12.
        forwards* h3: IHRed.
        inverts safe as h1; try solve[inverts* h1]; auto.
        inverts safe as h1 h2 h22.
        *
          forwards: preservation h2 Red.
          eauto.
        *
          forwards h5: preservation h2 Red.
          inverts h1 as h6 h7 h8; eauto.
          ++
          forwards h4: inference_unique h2 h6.
          substs*.
      --
         forwards* h3: IHRed.
        inverts safe as h1; try solve[inverts* h1]; auto.
        inverts safe as h1 h2 h22.
        *
          forwards: preservation h2 Red.
          eauto.
        *
          forwards h5: preservation h2 Red.
          inverts h1 as h6 h7 h8; eauto.
          ++
          forwards h4: inference_unique h2 h6.
          substs*.
    +
      inverts Typ as typ1 typ2. 
      --
        inverts typ1 as typ11 typ12.
        forwards* h3: IHRed.
        inverts safe as h1; try solve[inverts* h1]; auto.
        inverts safe as h1 h2 h22.
        *
          forwards: preservation h2 Red.
          eauto.
        *
          forwards h5: preservation h2 Red.
          inverts h1 as h6 h7 h8; eauto.
          ++
          forwards h4: inference_unique h2 h6.
          substs*.
      --
         forwards* h3: IHRed.
        inverts safe as h1; try solve[inverts* h1]; auto.
        inverts safe as h1 h2 h22.
        *
          forwards: preservation h2 Red.
          eauto.
        *
          forwards h5: preservation h2 Red.
          inverts h1 as h6 h7 h8; eauto.
          ++
          forwards h4: inference_unique h2 h6.
          substs*.
  -
    inverts safe.
    inverts* H4.
    inverts Typ. 
    + 
    inverts H1.
    inverts* H6.
    pick fresh y.
    forwards*: H11.
    rewrite (subst_exp_intro y); eauto.
    forwards*: safe_open H1 H7.
    +
    inverts H4.
    pick fresh y.
    forwards*: H11.
    rewrite (subst_exp_intro y); eauto.
    forwards*: safe_open H1 H8.
  - 
   forwards*: safe_Cast safe.
  -
   inverts safe. inverts H6.
   + 
    inverts Typ.
    *
    inverts H3. inverts H8.
    inverts H6.
    forwards* h1: principle_inf H12.  
    forwards* h2: principle_inf H3.
    rewrite h2 in *. rewrite h1 in *. 
    inverts h1. inverts H2.
    inverts H5.
    inverts H13.  
    eapply Safe_annoeq; eauto. 
    *
    inverts H6. inverts H. 
    forwards* h1: principle_inf H12.
    rewrite h1 in *. subst*. inverts H13. 
    inverts H5.
    forwards* h2: principle_inf H.
    rewrite h2 in *. subst*. 
    inverts H15. inverts H2. 
    eapply Safe_annoeq; eauto.
   +
    inverts H.
    forwards* h1: principle_inf H12.
    rewrite h1 in *. subst.
    assert((negb (negb b)) = b) as h2.
    destruct b; unfold negb; eauto.
    rewrite h2.
    inverts Typ.
    --
    inverts H. inverts H7.
    inverts H4.
    forwards* h3: principle_inf H. rewrite h3 in *. subst.
    inverts H3.
    inverts H10.
    inverts H13.
    ** 
    eapply Safe_annoeqn; eauto.
    **
    eapply Safe_annoeqn; eauto.
    inductions H4; eauto. inverts H3. 
    inductions H4; eauto. 
    eapply Safe_appv; eauto.
    inductions H4; eauto. inverts H3. 
    inverts* H6.  
    --
    inverts H4. 
    inverts H10.
    inverts H3.
    forwards* h3: principle_inf H. rewrite h3 in *. subst.
    inverts H2.
    inverts H13.
    ** 
    eapply Safe_annoeqn; eauto.
    **
    eapply Safe_annoeqn; eauto.
    inductions H3; eauto. inverts H2. 
    inductions H3; eauto. 
    eapply Safe_appv; eauto.
    inductions H3; eauto. inverts H2. 
    inverts* H4.
   +
    inverts Typ. 
    *
    inverts H3. inverts H8.
    apply Safe_anno; eauto.
    inverts H.
    inverts H6.
    forwards*: principle_inf H.
    rewrite H5 in *. subst. 
    eapply Safe_appv; eauto.
    eapply Safe_anno; eauto.
    destruct b1; unfold negb; eauto.
    *
    inverts H6.
    inverts H5.
    inverts H.
    forwards* h1: principle_inf H3.
    rewrite <- H17 in *. subst.
    apply Safe_anno; eauto.
    eapply Safe_appv; eauto.
    destruct b1; unfold negb; eauto. 
  -
    inverts Typ. 
    +
    forwards* h1: principle_inf H11.
    rewrite h1 in *. substs. inverts H10.
    assert(Safe nil (e_anno v2 l0 b0 A1) l b).
    inverts* safe; try solve[
    forwards*: inference_unique H11 H9; inverts* H1];
    try solve[
    forwards*: inference_unique H12 H8; inverts* H1].
    forwards*: safe_Cast H2.
    inverts* safe; try solve[
      forwards* h2: inference_unique H11 H13; inverts* h2].
    +
    inverts H3.
    forwards* h1: principle_inf H12.
    rewrite h1 in *. subst*. inverts H9.
    assert(Safe nil (e_anno v2 l0 b0 A2) l b).
    inverts* safe; try solve[
    forwards* h2: inference_unique H12 H10; inverts* h2];
    try solve[
      forwards*: inference_unique H12 H11; inverts* H1].
    forwards*: safe_Cast H2.
    inverts* safe;try solve[
      forwards* h3: inference_unique H12 H14; inverts* h3].
  -
    inverts safe; try solve[inverts H8].
    inverts Typ. 
    +
    inverts H12. inverts H11. 
    inverts* H9.
    +
    inverts H1. inverts H13. 
    inverts* H7.
  -
    inverts safe as h1 h2; try solve[inverts h2].
    inverts h2 as h2; eauto.
  -
    inverts safe as h1 h2; try solve[inverts h2].
    inverts h2 as h2; eauto.
  -
    inverts safe as h1 h2; try solve[inverts h2].
    inverts h1 as h1; eauto.
  -
    inverts safe as h1 h2; try solve[inverts h2].
    inverts h1 as h1; eauto.
Qed.



Lemma cast_suba: forall v A l b,
  suba (dynamic_type v) A ->
  not(Cast v l b A (e_blame l b))
 .
Proof.
  introv sa.
  unfold not;intros nt.
  inductions nt; simpl in *; try solve[inverts* sa].
Qed.



Lemma safe_progress: forall e A l b,
 Typing nil e Chk A ->
 Safe nil e l b ->
 not(step e (e_blame l b)).
Proof.
  introv Typ safe. gen A.
  inductions safe; intros;
  try solve[unfold not;intros nt; 
  forwards*: step_not_value nt];
  try solve[unfold not;intros nt; 
  inverts* nt];
  try solve[inverts* Typ; inverts* H].
  - unfold not;intros nt; 
  inverts* nt; destruct E; unfold fill in *;inverts H0.
  -
    forwards*: Typing_regular_1 Typ.
    inverts H1.
    unfold not;intros nt; 
    forwards*: step_not_value nt.
  -
    inverts Typ. inverts H0.
    forwards*: IHsafe1.
    unfold not;intros nt;inverts* nt.
    +
    destruct E; unfold fill in *; inverts* H2.
    *
    assert(not(value (e_anno e1 l1 b1 (t_arrow t_dyn t_dyn)))).
    unfold not;intros nt; inverts nt;try solve[
      forwards*: step_not_value H7
    ].
    apply H0. rewrite fill_anno.
    apply Step_blame; auto.
    *
    inverts H5.
    forwards* h1: principle_inf H.
    rewrite h1 in *. inverts H4.
    +
    forwards* h1: principle_inf H.
    rewrite h1 in *. inverts H13.
  -
    unfold not;intros nt;inverts* nt.
    +
    destruct E; unfold fill in *; inverts* H0.
    inverts Typ. inverts H0. inverts H3.
    forwards* h1: principle_inf H11.
    forwards* h2: principle_inf H.
    rewrite h2 in *. subst.
    inverts H8.
    forwards*: IHsafe2.
    assert(not(value (e_anno e2 l1 b1 A3))).
    unfold not;intros nt; inverts nt;try solve[
      forwards*: step_not_value H4
    ].
    apply H0. rewrite fill_anno.
    apply Step_blame; auto.
    +
    inverts Typ. inverts H0.
    forwards* h1: principle_inf H.
    rewrite h1 in *. inverts H8.
    inverts* safe2.
    *
      forwards* h3: principle_inf H12.
      rewrite <- h3 in *.
      forwards* h2: cast_suba H9.
    *
      destruct b; unfold negb in H11; inverts H11.
  -
    unfold not;intros nt;inverts* nt.
    +
    destruct E; unfold fill in *; inverts* H1.
    +
    forwards* h3: principle_inf H.
      rewrite <- h3 in *.
      forwards* h2: cast_suba H7.
  -
    unfold not;intros nt;inverts* nt.
    +
    destruct E; unfold fill in *; inverts* H1.
    +
    forwards* h4: cast_label H7.
    inverts h4 as h41 h42.
    destruct b; inverts h42. 
  -
    unfold not;intros nt;inverts* nt.
    +
    destruct E; unfold fill in *; inverts* H2.
    inverts Typ. inverts H2.
    forwards*: IHsafe.
    +
    forwards* h4: cast_label H7.
  -
    unfold not;intros nt;inverts* nt.
    destruct E; unfold fill in *; inverts* H.
    +
    inverts* Typ. inverts* H.
    +
    inverts* Typ. inverts* H.
  -
    inverts Typ as typ1.
    inverts typ1 as typ1 typ2.
    forwards* h1: IHsafe1.
    forwards* h2: IHsafe2.
    unfold not;intros nt.
    inverts nt as h3 h4 h5.
    destruct E; unfold fill in *;inverts* h5.
  -
    forwards*: IHsafe.
    unfold not;intros nt.
    inverts nt as h1 h2 h3.
    destruct E; unfold fill in *;inverts* h3.
  -
    forwards*: IHsafe.
    unfold not;intros nt.
    inverts nt as h1 h2 h3.
    destruct E; unfold fill in *;inverts* h3.
  -
    forwards* h4: IHsafe.
    unfold not;intros nt.
    inverts nt as h1 h2 h3.
    destruct E; unfold fill in *;inverts h3.
    apply h4.
    assert(not(value (e_anno e1 l2 b2 (t_pro t_dyn t_dyn)))) as h5.
    unfold not;intros nt; inverts nt;try solve[
      forwards*: step_not_value h2
    ].
    rewrite fill_anno.
    apply Step_blame; auto.
  -
     forwards* h4: IHsafe.
    unfold not;intros nt.
    inverts nt as h1 h2 h3.
    destruct E; unfold fill in *;inverts h3.
    apply h4.
    assert(not(value (e_anno e1 l2 b2 (t_pro t_dyn t_dyn)))) as h5.
    unfold not;intros nt; inverts nt;try solve[
      forwards*: step_not_value h2
    ].
    rewrite fill_anno.
    apply Step_blame; auto.  
Qed.


Lemma Safe_progress: forall e A l b dir,
 Typing nil e dir A ->
 Safe nil e l b ->
 not(step e (e_blame l b)).
Proof.
  introv typ sf.
  destruct dir.
  -
  forwards*: Typing_chk2 typ.
  forwards*: safe_progress sf.
  -
  forwards*: safe_progress sf.
Qed.
