Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Deterministic
        Typing.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.


Lemma eq_type: forall A,
 (A = t_dyn) \/ ~(A = t_dyn).
Proof.
  introv.
  inductions A;
  try solve[left;
  reflexivity];
  try solve[right;
  unfold not; intros H; 
  inverts* H].
Qed.


Lemma Cast_sim: forall v A r B,
    value v -> Cast v A r -> Typing nil v Inf B -> sim B A.
Proof with auto.
  introv Val Red Typ.
  gen B.
  lets Red': Red.
  inductions Red; introv Typ;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*];
  try solve [inverts* Typ].
  -
    forwards*: principle_inf Typ.
    rewrite H1 in H0.
    rewrite H0.
    auto.
  -
    inverts Typ as h1 h2.
    inverts Val as h3 h4.
    forwards*: IHRed1 Red1.
  -
    inverts Typ as h1 h2.
    inverts Val as h3 h4.
    forwards* h5: IHRed1 Red1.
  -
    inverts Typ as h1 h2.
    inverts Val as h3 h4.
    forwards* h5: IHRed1 Red1.
Qed.


Lemma Cast_preservation: forall v A v',
    value v -> Cast v A (e_exp v') -> Typing nil v Chk A -> Typing nil v' Inf A.
Proof with auto.
  introv Val Red Typ'.
  lets Typ: Typ'.
  inductions Red; intros;
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*];
  try solve [inverts* Typ].
  -
    inverts Typ. inverts* H0.
  - 
    inverts Typ as typ.
    forwards* h2: Cast_sim Red.
    forwards* h1: principle_inf typ.
    rewrite h1 in *; auto.
    forwards*: IHRed.
  -
   inverts Typ as typ. 
   inverts typ as typ.
   inverts typ as typ.
   inverts Val.
   forwards* h1: Cast_sim Red.
  -
    inverts Typ as typ. inverts typ as typ.
    inverts typ as typ.
    inverts Val.
    forwards* h1: principle_inf typ.
    rewrite h1 in *; auto.
  -
    inverts Val.
    inverts Typ as typ typ3. 
    inverts typ as typ1 typ2.
    inverts* typ3.
    forwards* h1:  IHRed1.
Qed.


Lemma Cast_simp_prv: forall v v' A,
  value v ->
  Cast v A (e_exp v') ->
  dynamic_type v' = A.
Proof.
  introv val red.
  inductions red; simpl in *; eauto;
  try solve[inverts* val].
  -
  inverts* val.
  forwards* h1: IHred1.
  forwards* h2: IHred2.
  substs*.
Qed.

Lemma ug_ground_r: forall t1 t2,
 UG t1 t2 ->
 Ground t2.
Proof.
 introv h1.
 inverts* h1.
Qed.


Lemma Cast_value: forall v v' A,
  value v ->
  Cast v A (e_exp v') ->
  value v'.
Proof.
  introv Val Red.
  inductions Red;
  try solve[inverts* Val]; eauto.
  -
    forwards* h1: IHRed.
    forwards* h2: Cast_simp_prv Red.
    forwards*: ug_ground_r H.
    rewrite <- h2 in *; auto.
Qed.


Theorem preservation : forall e e' dir A,
    Typing nil e dir A ->
    step e (e_exp e') ->
    Typing nil e' dir A.
Proof.
  introv Typ Red. gen A dir.
  inductions Red; intros.
  - 
    inductions E; unfold fill in *.
    + inverts Typ.
      forwards*: IHRed H4.
      inverts H0.
      forwards*: IHRed H6.
    + inverts Typ.
      forwards*: IHRed H7.
      inverts H0.
      forwards*: IHRed H7.
    + inverts Typ.
      forwards*: IHRed H5.
      inverts H0.
      forwards*: IHRed H4.
    +
      inverts Typ as typ.
      inverts typ as typ1 typ2.
      forwards*: IHRed typ1.
      forwards*: IHRed typ.
    +
      inverts Typ as typ typ0.
      inverts typ as typ1 typ2.
      forwards*: IHRed typ2.
      forwards*: IHRed typ0.
    +
      inverts Typ as typ.
      inverts typ as typ.
      forwards*: IHRed typ.
      forwards*: IHRed typ.
    +
      inverts Typ as typ.
      inverts typ as typ.
      forwards*: IHRed typ.
      forwards*: IHRed typ.
  - 
    inverts Typ.
    + 
    inverts H6. inverts H4.
    pick fresh y.
    apply Typ_anno.
    rewrite (subst_exp_intro y); eauto.
    eapply typing_c_subst_simpl; eauto.
    forwards*: Cast_preservation H1.
    +
    inverts H2. 
    inverts H8. inverts H6. 
    pick fresh x.
    eapply Typ_sim; eauto.
    apply Typ_anno; eauto.
    rewrite (subst_exp_intro x); eauto.
    eapply typing_c_subst_simpl; eauto.
    forwards*: Cast_preservation H1.
  - 
    inverts Typ. 
    + 
    inverts H7.
    forwards*: Cast_preservation H0.
    +
    inverts H2. 
    forwards*: Cast_preservation H0.
  - inverts Typ. 
    +
    inverts H5. inverts H3.
    forwards*: Cast_preservation H0.
    +
    inverts H1. inverts H7. inverts H5. 
    eapply Typ_sim;eauto.
  - 
    inverts Typ. 
    +
    inverts H5. inverts H3.
    forwards*: Cast_preservation H0.
    +
    inverts H1. inverts H7. inverts H5.
    eapply Typ_sim; eauto.
  - 
    inverts Typ. 
    +
    inverts H7. inverts H5.
    forwards* h1: Cast_preservation H0.
    inverts H6. 
    forwards* h2: principle_inf H3.
    rewrite H2 in *. inverts h2.
    inverts H4.
    eapply Typ_anno; auto.
    eapply Typ_sim with (A := B); auto.
    eapply Typ_app; eauto.
    +
    inverts H3. inverts H9. inverts H7.
    forwards* h1: Cast_preservation H0.
    inverts H6. 
    forwards* h2: principle_inf H3.
    rewrite H2 in *. inverts h2.
    inverts H5.
    eapply Typ_sim with (A := A1); auto.
    eapply Typ_anno; auto.
    eapply Typ_sim with (A := B); auto.
    eapply Typ_app; eauto.
  -
    inverts Typ.
    +
    inverts H4. inverts* H2.
    +
    inverts H0. inverts H6.
    inverts H4.
    eapply Typ_sim;eauto.
  -
    inverts Typ as typ typ0.
    +
    inverts typ as typ typ1.
    inverts typ as typ.
    inverts* typ1.
    eapply Typ_sim;eauto.
    +
    inverts typ as typ1 typ2.
    inverts typ0 as typ0; eauto.
  -
     inverts Typ as typ typ0.
    +
    inverts typ as typ typ1.
    inverts typ as typ.
    inverts* typ1.
    eapply Typ_sim;eauto.
    +
    inverts typ as typ1 typ2.
    inverts typ0 as typ0; eauto.
  -
    inverts Typ as typ1 typ2.
    +
    inverts typ1 as typ1 typ3.
    inverts  typ1; inverts* typ3.
    +
    inverts typ1 as typ4 typ5.
    inverts*  typ2.
  -
    inverts Typ as typ1 typ2.
    +
    inverts typ1 as typ1 typ3.
    inverts  typ1; inverts* typ3.
    +
    inverts typ1 as typ4 typ5.
    inverts*  typ2.
Qed.


Theorem preservation_multi_step : forall t t' dir  T,
    Typing nil t dir T ->
    t ->** (e_exp t') ->
    Typing nil t' dir T.
Proof.
  introv Typ Red.
  inductions Red; eauto.
  lets*: preservation Typ H.
Qed.


Lemma sim_decidable:forall A B,
sim A B \/ ~ (sim A B).
Proof.
  introv.
  gen A.
  inductions B; intros; eauto;
  try solve[inductions A; eauto;
  try solve[right; unfold not;intros nt;inverts nt]].
  - inductions A; eauto;
    try solve[right; unfold not;intros nt;inverts nt].
    forwards* h1: IHB1 A1.
    forwards* h2: IHB2 A2.
    inverts h1 as h1; try solve[
      right; unfold not;intros nt;inverts* nt
    ].
    inverts h2 as h2; try solve[
      right; unfold not;intros nt;inverts* nt
    ]; eauto.
  - 
  inductions A; eauto;
    try solve[right; unfold not;intros nt;inverts nt].
    forwards* h1: IHB1 A1.
    forwards* h2: IHB2 A2.
    inverts h1 as h1; try solve[
      right; unfold not;intros nt;inverts* nt
    ].
    inverts h2 as h2; try solve[
      right; unfold not;intros nt;inverts* nt
    ]; eauto.
Qed.




Lemma Ground_decidable : forall A,
  Ground A \/ not (Ground A).
Proof.
  introv.
  inductions A; intros; eauto;
  try solve[right; unfold not;intros nt;inverts nt].
  -
  destruct(eq_type A1); destruct(eq_type A2); try solve[substs*];
  try solve[right; unfold not;intros nt;inverts nt; apply H0; auto];
  try solve[right; unfold not;intros nt;inverts nt; apply H; auto].
  -
  destruct(eq_type A1); destruct(eq_type A2); try solve[substs*];
  try solve[right; unfold not;intros nt;inverts nt; apply H0; auto];
  try solve[right; unfold not;intros nt;inverts nt; apply H; auto].
Qed.
  


Lemma UG_arrow: forall t1 t2,
 ~ Ground (t_arrow t1 t2) ->
 UG (t_arrow t1 t2) (t_arrow t_dyn t_dyn).
Proof.
  introv h1.
  unfold UG; try solve[unfold not; intros nt;inverts nt];
  splits*; try solve[unfold not; intros nt;inverts nt];
  try solve[unfold not; intros nt;inverts nt; apply h1; auto].
Qed.


Lemma UG_pro: forall t1 t2,
 ~ Ground (t_pro t1 t2) ->
 UG (t_pro t1 t2) (t_pro t_dyn t_dyn).
Proof.
  introv h1.
  unfold UG; try solve[unfold not; intros nt;inverts nt];
  splits*; try solve[unfold not; intros nt;inverts nt];
  try solve[unfold not; intros nt;inverts nt; apply h1; auto].
Qed.

Lemma UG_decidable: forall A,
 (exists B, UG A B) \/ (forall B, not(UG A B)).
Proof.
  introv.
  inductions A.
  -
    right.
    intros.
    unfold not; intros nt.
    inverts nt as nt1 nt2.
    inverts nt2 as nt2 nt3.
    inverts nt3 as nt3 nt4.
    inverts* nt1.
    inverts nt2.
  -
    forwards* h1: Ground_decidable (t_arrow A1 A2).
    inverts h1 as h1.
    inverts h1.
    +
    right.
    intros.
    unfold not;intros nt.
    inverts nt as nt1 nt2.
    inverts nt2 as nt2 nt3.
    inverts nt3 as nt3 nt4.
    inverts nt1;inverts nt2.
    exfalso; apply nt3; auto.
    +
    forwards*: UG_arrow h1.
  -
    right.
    intros.
    unfold not;intros nt.
    inverts nt as nt1 nt2.
    inverts nt2 as nt2 nt3.
    inverts nt3 as nt3 nt4.
    exfalso; apply nt4; auto.
  -
    forwards* h1: Ground_decidable (t_pro A1 A2).
    inverts h1 as h1.
    inverts h1.
    +
    right.
    intros.
    unfold not;intros nt.
    inverts nt as nt1 nt2.
    inverts nt2 as nt2 nt3.
    inverts nt3 as nt3 nt4.
    inverts nt1;inverts nt2.
    exfalso; apply nt3; auto.
    +
    forwards*: UG_pro h1.
Qed.



Lemma cast_dyn_not_fail: forall v r,
    value v -> 
    Cast v t_dyn r ->
    exists v', r = (e_exp v') .
Proof.
   introv val red.
   inductions red; try solve[unfold not; intros nt;inverts nt];
   try solve[inverts* val];eauto;
   try solve[exfalso; apply H; auto].
Qed.


Lemma Ground_sim_case: forall A B,
  Ground A ->
  sim A B ->
  B = A \/ B = t_dyn \/ UG B A.
Proof.
  introv gr ss.
  inverts* gr; try solve[inverts* ss].
  -
    forwards* h1: Ground_decidable B.
    inverts h1 as h1.
    +
    inverts h1; 
    inverts* ss.
    +
    inverts* ss.
    forwards*: UG_arrow h1.
  -
    forwards* h1: Ground_decidable B.
    inverts h1 as h1.
    +
    inverts h1; 
    inverts* ss.
    +
    inverts* ss.
    forwards*: UG_pro h1.
Qed.



Lemma Cast_progress: forall v A,
    value v -> Typing [] v Chk A -> exists r, Cast v A r.
Proof.
  intros v A Val Typ. gen A.
  inductions Val; intros. 
  - 
    inverts Typ as typ1 typ2.
    inverts typ1; inverts* typ2.
  - 
    inverts Typ as typ1 typ2.
    inverts typ1; inverts* typ2.
    assert(UG (dynamic_type e_add) (t_arrow t_dyn t_dyn)) as h0.
    unfold UG; simpl; repeat split*;
    try solve[
    unfold not;intros nt;inverts nt].
    assert(Cast e_add (t_arrow t_dyn t_dyn) (e_exp (e_anno e_add (t_arrow t_dyn t_dyn))) ) as h1.
    assert(dynamic_type e_add = (t_arrow t_int (t_arrow t_int t_int))); simpl; auto.
    eauto.
    exists*.
  - 
    inverts Typ as typ1 typ2.
    inverts typ1; inverts* typ2.
    assert(UG (dynamic_type (e_addl i5)) (t_arrow t_dyn t_dyn)) as h0.
    unfold UG; simpl; repeat split*;
    try solve[
    unfold not;intros nt;inverts nt].
    assert(Cast (e_addl i5) (t_arrow t_dyn t_dyn) (e_exp (e_anno (e_addl i5) (t_arrow t_dyn t_dyn))) ) as h1.
    assert(dynamic_type (e_addl i5) = (t_arrow t_int t_int)); simpl; auto.
    eauto.
    exists*.
  - 
    inverts Typ as typ1 typ2.
    inverts typ1; inverts* typ2.
    forwards* h1: UG_decidable (t_arrow t1 t2).
    inverts h1 as h1.
    +
      inverts h1 as h1.
      lets h1': h1.
      inverts h1 as h1 h2.
      inverts h2 as h2 h3.
      inverts h1; inverts h2.
      assert(Cast (e_abs t1 e t2) (t_arrow t_dyn t_dyn) (e_exp (e_anno (e_abs t1 e t2) (t_arrow t_dyn t_dyn))) ) as h1.
    assert(dynamic_type (e_abs t1 e t2) = (t_arrow t1 t2)); simpl; auto.
    eauto.
    exists*.
    +
    forwards* h2: Ground_decidable (t_arrow t1 t2).
    inverts h2 as h2; eauto.
    forwards* h3: h1  (t_arrow t_dyn t_dyn).
    forwards*: UG_arrow h2.
  -
     inverts Typ as typ1 typ2.
     inverts typ1 as typ1.
     inverts* typ2.
     forwards* h1: UG_decidable (t_arrow A B).
    inverts h1 as h1.
    +
      inverts h1 as h1.
      lets h1': h1.
      inverts h1 as h1 h2.
      inverts h2 as h2 h3.
      inverts h1; inverts h2.
      assert(Cast (e_anno v (t_arrow A B)) (t_arrow t_dyn t_dyn) (e_exp (e_anno (e_anno v (t_arrow A B)) (t_arrow t_dyn t_dyn))) ) as h1.
    assert(dynamic_type (e_anno v (t_arrow A B)) = ( (t_arrow A B))); simpl; auto.
    eauto.
    exists*.
    +
    forwards* h2: Ground_decidable ( (t_arrow A B)).
    inverts h2 as h2; eauto.
    forwards* h3: h1  (t_arrow t_dyn t_dyn).
    forwards*: UG_arrow h2.
  -
     destruct(sim_decidable (dynamic_type v) A); eauto.
     inverts Typ as typ1 typ2.
    inverts typ1 as typ1.
    inverts typ1 as typ1.
    forwards* h1: principle_inf typ1.
    rewrite h1 in *.
    forwards* h2: IHVal A.
    inverts* h2.
    forwards* h3: UG_decidable A.
    inverts h3 as h3.
    +
      inverts* h3.
    +
      forwards* h4: Ground_sim_case H0.
      inverts h4 as h4 h5.
      --
      rewrite <- h1 in *; exists*.
      --
      inverts h4 as h4 h5.
      forwards*: value_lc Val.
      forwards* : h3 A0.
  -
    inverts Typ as typ1 typ2.
    inverts typ1 as typ1 typ3.
    inverts* typ2.
    +
      forwards* h1: UG_decidable (dynamic_type (e_pro v1 v2)).
      inverts h1 as h1.
      *
        inverts h1 as h1.
        lets h1': h1.
        inverts h1 as h1 h2.
        inverts h2 as h2 h3.
        inverts h1; inverts h2.
        forwards* h1: IHVal1 t_dyn.
        forwards* h2: IHVal2 t_dyn.
        inverts h1 as h1.
        inverts h2 as h2.
        assert(exists v, Cast (e_pro v1 v2) (t_pro t_dyn t_dyn) (e_exp v)) as h4.
        forwards* h5: cast_dyn_not_fail h1.
        inverts h5 as h5.
        forwards* h6: cast_dyn_not_fail h2.
        inverts h6 as h6.
        exists*.
        inverts h4 as h4.
        exists*.
      *
        forwards* h2: Ground_decidable (t_pro (dynamic_type v1) (dynamic_type v2)).
        inverts h2 as h2; eauto.
        forwards* h3: h1  (t_pro t_dyn t_dyn).
        forwards*: UG_pro h2.
    +
    forwards* h1: IHVal1.
    forwards* h2: IHVal2.
    inverts h1 as h1.
    inverts h2 as h2.
    destruct x;destruct x0; eauto.
Qed.


Lemma dyn_decidable: forall A,
 (A = t_dyn) \/ not(A = t_dyn).
Proof.
  introv.
  inductions A; try solve[right; unfold not; intros nt; inverts* nt];
  try solve[left*].
Qed.


Lemma value_decidable: forall e,
  lc_exp e -> value e \/ not(value e).
Proof.
  introv lc.
  inductions lc; try solve[right; unfold not; intros nt; inverts* nt];
  try solve[left*].
  inverts IHlc;
  try solve[right; unfold not; intros nt; inverts* nt].
  - 
    inductions H; try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    right; unfold not; intros nt; inverts* nt.
    inverts* H3.
    + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    left. eapply value_fanno; eauto. reflexivity.
    right; unfold not; intros nt; inverts* nt. inverts* H0.
    + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    left. eapply value_fanno; eauto. reflexivity.
    right; unfold not; intros nt; inverts* nt. inverts* H0.
    + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
      try solve[left*].
      left. eapply value_fanno; eauto. reflexivity.
      destruct(dyn_decidable t1);destruct(dyn_decidable t2);subst*;
      try solve[right; unfold not; intros nt; inverts* nt; inverts* H2];
      try solve[right; unfold not; intros nt; inverts* nt; inverts* H3];
      try solve[left*].
    + inductions A;try solve[right; unfold not; intros nt; inverts* nt];
      try solve[left*].
      *
      left. eapply value_fanno; eauto. reflexivity.
      *
      destruct(dyn_decidable A0);destruct(dyn_decidable B);subst*;
      try solve[right; unfold not; intros nt; inverts* nt; inverts* H4];
      try solve[right; unfold not; intros nt; inverts* nt; inverts* H3];
      try solve[left*].
    +
    right; unfold not; intros nt; inverts* nt; inverts* H3. inverts H4.
    +
    inductions A;try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    *
      right; unfold not; intros nt; inverts nt as h0 h1.
      inverts h1.
    *
      destruct(dyn_decidable (dynamic_type v1));destruct(dyn_decidable (dynamic_type v2));substs*;
      try solve[right; unfold not; intros nt; inverts* nt; inverts* H4];
      try solve[right; unfold not; intros nt; inverts* nt; inverts* H3];
      try solve[left*].
      assert(Ground (t_pro (dynamic_type v1) (dynamic_type v2))).
      rewrite H1; rewrite H2; auto.
      left*.
  - inverts IHlc1;try solve[exfalso; apply H; auto];
    try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
    inverts IHlc2;try solve[exfalso; apply H; auto];
    try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*].
Qed.


Theorem progress : forall e dir T,
    Typing nil e dir T ->
    value e \/ (exists r, step e r).
Proof.
  introv Typ. lets Typ': Typ.
  inductions Typ; 
      lets Lc  : Typing_regular_1 Typ';
      try solve [left*];
      try solve [right*].
  - Case "var".
    inverts* H0.
  - (* app *)
    right. inverts Lc.
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    inverts* Typ1;
    try solve [ inverts* Val1; inverts* H3 ];
    try solve[inverts* H]; inverts* H.
    + forwards*: Cast_progress Typ2.
      inverts* H.
      inductions x; try solve[exists*].
      exists. 
      eapply Step_betap; simpl in *;auto.
    + 
      forwards* h0: Cast_progress Typ2.
      inverts h0 as h0.
      inductions x.
      *
      forwards* h1: Cast_preservation h0.
      forwards* h2: Cast_value h0.
      inverts h2;inverts h1.
      exists*.
      *
      exists.
      eapply Step_betap; simpl in *;auto.
    + 
      forwards* h0: Cast_progress Typ2.
      inverts h0 as h0.
      inductions x.
      *
      forwards* h1: Cast_preservation h0.
      forwards* h2: Cast_value h0.
      inverts h2;inverts h1.
      exists*.
      *
      exists.
      eapply Step_betap; simpl in *;auto.
    +
      forwards*: Cast_progress Typ2.
      inverts H.
      inverts Val1.
      inductions x; try solve[exists*].
      *
      exists.
      eapply Step_betap; simpl in *;eauto.
    + 
      inverts* H.
      *
      forwards*: principle_inf Typ1.
       inductions e2'.
       assert(fill ((appCtxR e1)) e2 = e_app e1 e2); eauto.
       rewrite <- H0.
       exists. apply Step_eval; eauto.
       assert(fill ((appCtxR e1)) e2 = e_app e1 e2); eauto.
       rewrite <- H0.
       exists. apply Step_blame; eauto.
       *
       inverts Val1;inverts* Typ1.
    + inductions e1'.
      assert(fill ((appCtxL e2)) e1 = e_app e1 e2); eauto.
      rewrite <- H0.
      exists. apply Step_eval; eauto.
      assert(fill ((appCtxL e2)) e1 = e_app e1 e2); eauto.
      rewrite <- H0.
      exists. apply Step_blame; eauto.
  - Case "anno".
    inverts* Lc.
    destruct~ IHTyp as [ Val | [t' Red]].
    + SCase "e_anno v A".
      forwards*: Cast_progress Typ.
      inverts* H.
      destruct(value_decidable (e_anno e A)); eauto. 
    + right.
      induction t'.
      * 
        assert(fill ((annoCtx A)) e = e_anno e A); eauto.
        rewrite <- H.
        exists. apply Step_eval; eauto.
      *
        assert(fill ((annoCtx A)) e = e_anno e A); eauto.
        rewrite <- H.
        exists. apply Step_blame; eauto.
  - forwards*: IHTyp Typ.
  -
    inverts Lc.
    lets* [Val1 | [e1' Red1]]: IHTyp1.
    lets* [Val2 | [e2' Red2]]: IHTyp2.
    + 
      destruct e2'.
      assert(fill ((proCtxR e1)) e2 = e_pro e1 e2) as h1; eauto.
      rewrite <- h1.
      right. exists*. 
      assert(fill ((proCtxR e1)) e2 = e_pro e1 e2) as h1; eauto.
      rewrite <- h1.
      right. exists*. 
    +
      destruct e1'.
      assert(fill ((proCtxL e2)) e1 = e_pro e1 e2) as h1; eauto.
      rewrite <- h1.
      right. exists*. 
      assert(fill ((proCtxL e2)) e1 = e_pro e1 e2) as h1; eauto.
      rewrite <- h1.
      right. exists*. 
  -
    inverts Lc.
    lets* [Val | [e' Red]]: IHTyp.
    +
      inverts H.
      inverts* Val;inverts Typ.
      inverts* Val; inverts Typ.
    +
      destruct e'.
      assert(fill ((lCtx)) e = e_l e) as h1; eauto.
      rewrite <- h1.
      right. exists*. 
      assert(fill ((lCtx)) e = e_l e) as h1; eauto.
      rewrite <- h1.
      right. exists*. 
  -
    inverts Lc.
    lets* [Val | [e' Red]]: IHTyp.
    +
      inverts H.
      inverts* Val;inverts Typ.
      inverts* Val; inverts Typ.
    +
       destruct e'.
      assert(fill ((rCtx)) e = e_r e) as h1; eauto.
      rewrite <- h1.
      right. exists*. 
      assert(fill ((rCtx)) e = e_r e) as h1; eauto.
      rewrite <- h1.
      right. exists*. 
Qed.
