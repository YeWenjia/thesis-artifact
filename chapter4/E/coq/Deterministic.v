Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        syntax_ott
        rules_inf
        Typing
        Infrastructure.

Require Import Strings.String.

Lemma sim_refl: forall A,
  sim A A.
Proof.
  intros.
  inductions A; eauto.
Qed.


Lemma tpre_refl: forall A,
  tpre A A.
Proof.
   inductions A; eauto.
Qed.

Lemma sim_sym: forall t1 t2,
 sim t1 t2 ->
 sim t2 t1.
Proof.
  introv sim.
  inductions sim; eauto.
Qed.

Hint Resolve sim_refl sim_sym tpre_refl: core.

Lemma epre_sim : forall A1 B1 A2 B2,
  sim A1 B1 ->
  tpre A1 A2 ->
  tpre B1 B2 ->
  sim A2 B2.
Proof.
  introv s1 tp1 tp2. gen A2 B2.
  inductions s1; intros; eauto.
  - inverts tp1. inverts* tp2. inverts* tp2.
  - inverts* tp1.
    inverts* tp2.
  - inverts* tp1.
  - inverts* tp2.
  - inverts* tp1. inverts* tp2. 
Qed.


Lemma tpre_trans: forall t1 t2 t3,
 tpre t1 t2 ->
 tpre t2 t3 ->
 tpre t1 t3.
Proof.
  introv tp1 tp2. gen t1.
  inductions tp2; intros;
  try solve[inductions tp1; eauto].
Qed.


Lemma meet_progress: forall A B,
 sim A B ->
 exists C, meet A B C.
Proof.
 introv sm.
 inductions sm; try solve[exists*].
 -
 inverts IHsm1.
 inverts* IHsm2.
 -
 inverts IHsm1.
 inverts* IHsm2.
Qed.


Lemma meet_sim: forall A B C,
 meet A B C->
 sim A B /\ sim A C /\ sim B C.
Proof.
  introv mt.
  inductions mt; eauto.
  - 
   lets(h1&h2&h3):IHmt1.
   lets(h4&h5&h6):IHmt2.
   splits*.
  - 
   lets(h1&h2&h3):IHmt1.
   lets(h4&h5&h6):IHmt2.
   splits*.
Qed.


Lemma meet_unique: forall A B C1 C2,
 meet A B C1 ->
 meet A B C2 ->
 C1 = C2.
Proof.
 introv me1 me2. gen C2.
 inductions me1; intros;try solve[inductions me2;eauto].
 -
  inverts me2 as h1 h2;eauto.
  forwards*: IHme1_1 h1.
  forwards*: IHme1_2 h2.
  subst*.
 -
 inverts me2 as h1 h2;eauto.
 forwards*: IHme1_1 h1.
 forwards*: IHme1_2 h2.
 subst*.
Qed.


Lemma tpre_sim: forall A B,
 tpre A B ->
 sim A B.
Proof.
  introv tp.
  inductions tp; eauto.
Qed.


Lemma Cast_unique: forall p p1 p2 C A,
    pval p -> Typing nil p Chk C -> Cast p A p1 -> Cast p A p2 -> p1 = p2.
Proof.
  introv pval Typ R1 R2.
  gen p2 C.
  lets R1': R1.
  induction R1; introv R2;
  introv Typ;
    try solve [inverts* R2].
  -
    inductions R2;eauto.
    +
    clear IHR2_1 IHR2_2.
    inverts Typ as h1 h2.
    inverts h1 as h3 h4.
    inverts pval as pval1 pval2.
    (* forwards* h8: pattern_pro_uniq H H0. *)
    (* inverts h8. *)
    forwards* h5:IHR1_1 R2_1.
    forwards* h6:IHR1_2 R2_2.
    inverts h5. inverts* h6.
    +
    clear IHR2_1.  clear IHR2_2.
    inverts Typ as h1 h2.
    inverts h1 as h3 h4.
    inverts pval as pval1 pval2.
    (* forwards* h8: pattern_pro_uniq H H0. *)
    (* inverts h8. *)
    forwards* h5:IHR1_1 R2_1.
    inverts* h5.
    +
    clear IHR2_1.  clear IHR2_2.
    inverts Typ as h1 h2.
    inverts h1 as h3 h4.
    inverts pval as pval1 pval2.
    (* forwards* h8: pattern_pro_uniq H H0. *)
    (* inverts h8. *)
    forwards* h5:IHR1_2 R2_2.
    inverts* h5.
  -
     inductions R2;eauto.
     clear IHR2_1 IHR2_2.
     inverts Typ as h1 h2.
     inverts h1 as h3 h4.
     inverts pval as pval1 pval2.
     (* forwards* h8: pattern_pro_uniq H H0. *)
     (* inverts h8. *)
     forwards* h5:IHR1_1 R2_1.
     inverts* h5.
  -
     inductions R2;eauto.
     clear IHR2_1 IHR2_2.
     inverts Typ as h1 h2.
     inverts h1 as h3 h4.
     inverts pval as pval1 pval2.
     (* forwards* h8: pattern_pro_uniq H H0. *)
     (* inverts h8. *)
     forwards* h5:IHR1_2 R2_2.
     inverts* h5.
Qed.



Lemma Cast_prv_pvalue: forall p A v',
    pval p -> Cast p A (Expr v') -> tpre A (dynamic_type p) -> pval v'.
Proof.
  introv Val Red tp.
  inductions Red;eauto; simpl in *;
  try solve[inverts* Val].
  -
    inverts Val as val.
    inverts* tp.
  -
    inverts* tp.
    inverts Val as pval1 pval2.
    forwards* h1: IHRed1.
Qed.

(* Lemma Cast_prv_value: forall p A B v',
    pval p -> Cast p A B (Expr v') -> tpre A (dynamic_type p) -> value v'.
Proof.
  introv Val Red tp.
  inductions Red;eauto; simpl in *;
  try solve[inverts* Val].
  -
    inverts Val as val.
    inverts* tp.
  -
    inverts* tp.
    inverts Val as pval1 pval2.
    forwards* h1: IHRed1.
    inverts* h1.
    forwards* h2: IHRed2.
    inverts* h2.
Qed. *)


Lemma Cast_prv_value: forall p A B v',
    pval p -> Cast p A (Expr v') -> tpre A (dynamic_type p) ->
   value (e_val v' B).
Proof.
  introv Val Red tp.
  inductions Red;eauto; simpl in *;
  try solve[inverts* Val].
  -
    inverts Val as val.
    inverts* tp.
  -
    inverts* tp.
    inverts Val as pval1 pval2.
    forwards* h1: IHRed1.
    inverts* h1.
    forwards* h2: IHRed2.
    inverts* h2.
Qed.



Lemma sim_decidable:forall A B,
sim A B \/ ~ (sim A B).
Proof.
  introv.
  gen A.
  inductions B; intros; eauto.
  - inductions A; eauto; try solve[right; unfold not;  intros nt; inverts* nt].
  - inductions A; eauto; try solve[right; unfold not;  intros nt; inverts* nt].
    forwards*: IHB1 A1. forwards*: IHB2 A2.
    destruct H; destruct H0; try solve[left;  eauto];
    try solve[ right;
    unfold not; intros nt; inverts* nt]. 
  -
    inductions A; eauto; try solve[right; unfold not;  intros nt; inverts* nt].
    forwards*: IHB1 A1. forwards*: IHB2 A2.
    destruct H; destruct H0; try solve[left;  eauto];
    try solve[ right;
    unfold not; intros nt; inverts* nt]. 
Qed.



Lemma step_not_abs: forall e r,
 step (e_abs e) r -> False.
Proof.
  introv red.
  inverts* red; try solve[destruct E; unfold simpl_fill in *; inverts* H].
Qed.




Lemma sfill_eq: forall E0 e0 E e1 r1 r2,
  simpl_fill E0 e0 = simpl_fill E e1 ->
  step e0 r1 ->
  step e1 r2 ->
  simpl_wf E ->
  simpl_wf E0 ->
  E = E0 /\ e0 = e1.
Proof.
  introv eq red1 red2 wf1 wf2. gen E e0 e1 r1 r2.
  inductions E0; unfold simpl_fill in *;  intros.
  - inductions E; unfold simpl_fill in *; inverts* eq;
    inverts wf1;
    try solve[
    forwards*: step_not_abs red2];
    try solve[
    forwards*: step_not_abs red1];
    try solve[forwards*: step_not_value red1];
    try solve[forwards*: step_not_value red2];
    try solve[forwards*: step_not_fvalue red1];
    try solve[forwards*: step_not_fvalue red2]
    .
  - inductions E; unfold simpl_fill in *; inverts* eq;
    inverts wf2; try solve[
    forwards*: step_not_abs red2];
    try solve[forwards*: step_not_value red1];
    try solve[forwards*: step_not_value red2];
    try solve[forwards*: step_not_fvalue red1];
    try solve[forwards*: step_not_fvalue red2]
    .
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_value red1.
  - inductions E; unfold simpl_fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_value red2.
  -
    inductions E; unfold simpl_fill in *; inverts* eq.
  -
    inductions E; unfold simpl_fill in *; inverts* eq.
  -
     inductions E; unfold simpl_fill in *; inverts* eq.
Qed.


Lemma principle_uniq: forall v A B,
 value v ->
 dynamic_type v = A ->
 dynamic_type v = B ->
 A = B.
Proof.
  introv val typ1 typ2.
  inductions val; try solve[inverts* typ1; inverts typ2].
Qed.



Lemma fill_chk:  forall E e A,
  nil ⊢ simpl_fill E e ⇐  A ->
  exists B, nil ⊢ e ⇐  B \/ exists f, e = e_fval f.
Proof.
  introv typ.
  forwards* h2: Typing_regular_1 typ.
  inverts typ as typ1 typ2. 
  -
    destruct E; unfold simpl_fill in *; inverts* H.
  -
    destruct E; unfold simpl_fill in *; inverts typ1 as h1 h2; eauto.
  -
    destruct E; unfold simpl_fill in *; inverts* H.
  Unshelve.
  apply t_int.
Qed.


Lemma meet_more_precise: forall A B C,
 meet A B C ->
 tpre C A /\ tpre C B.
Proof.
  introv mt.
  inductions mt; eauto;
  try solve[inverts IHmt1 as h1 h2; eauto;
  inverts IHmt2 as h3 h4; eauto].
Qed.



Theorem step_unique: forall A e r1 r2,
    Typing nil e Chk A -> step e r1 -> step e r2 -> r1 = r2.
Proof.
  introv Typ Red1.
  gen A r2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - (* \x.e:a->b ---> \x.e:a->b:a->b:a->b *)
    inverts* Red2; try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    +
      forwards* h1: pattern_abs_uniq H0 H5.
      inverts* h1.
    +
      destruct E; unfold simpl_fill in H1; inverts* H1.
      inverts H3; destruct E; unfold simpl_fill in H1; inverts* H1.
    +
      destruct E; unfold simpl_fill in H1; inverts* H1.
      inverts H3; destruct E; unfold simpl_fill in H1; inverts* H1.
  - (* i ---> i:int *)
    inverts* Red2. destruct E; unfold simpl_fill in H; inverts* H.
    destruct E; unfold simpl_fill in H; inverts* H.
  - (* c ---> c:int *)
    inverts* Red2. destruct E; unfold simpl_fill in H; inverts* H.
    destruct E; unfold simpl_fill in H; inverts* H.
  - (* c ---> c:int *)
    inverts* Red2. destruct E; unfold simpl_fill in H; inverts* H.
    destruct E; unfold simpl_fill in H; inverts* H.   
  - (* (p1:a, p2:b) *)
     inverts* Red2;
    try solve[destruct E; unfold simpl_fill in *; inverts* H1;
    forwards*: step_not_value H3].
  - (* e1 e2 ---> e1' e2 *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in *; inverts H1];
    try solve[destruct E; unfold simpl_fill in *; inverts H0;
    try solve[forwards*: step_not_abs Red1];
    try solve[forwards*: step_not_value Red1];
    try solve[inverts H]
    ].
    + forwards*: sfill_eq H0.             
      destruct H3. subst.
      forwards* h2: fill_chk Typ. inverts h2 as h2.
      inverts h2 as h2; try solve[
        inverts h2 as h2; forwards*: step_not_fvalue H2
      ].
      forwards*: IHRed1 Red1 H2. congruence.
    + forwards*: sfill_eq H0.             
      destruct H3. subst. 
      forwards* h2: fill_chk Typ. 
      inverts h2 as h2.
      inverts h2 as h2; try solve[
        inverts h2 as h2; forwards*: step_not_fvalue H2
      ].
      forwards*: IHRed1 Red1 H2. congruence.
    +
      destruct E; unfold simpl_fill in *; inverts H0;
      try solve[forwards*: step_not_value Red1];
      try solve[forwards*: step_not_fvalue Red1].
      inverts H.
    +
      destruct E; unfold simpl_fill in *; inverts H1;
      try solve[forwards*: step_not_value Red1];
      try solve[forwards*: step_not_fvalue Red1]
      .
    +
      destruct E; unfold simpl_fill in *; inverts H1;
      try solve[forwards*: step_not_value Red1];
      try solve[forwards*: step_not_fvalue Red1]
      .
  - (* e1 e2 ---> blame e2 *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H0; inverts* H0;
    try solve[forwards*: step_not_abs Red1];
    try solve[forwards*: step_not_value Red1];
    try solve[inverts H]];
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1].
    + forwards*: sfill_eq H0.
      destruct H3. subst. 
      forwards* h2: fill_chk Typ. inverts h2 as h2.
      inverts h2 as h2; try solve[
        inverts h2 as h2; forwards*: step_not_fvalue H2
      ].
      forwards*: IHRed1 Red1 H2. congruence.
    +
      destruct E; unfold simpl_fill in H0; inverts* H0;
      try solve[forwards*: step_not_value Red1];
      try solve[forwards*: step_not_fvalue Red1];
      try solve[inverts* H].
    +
      destruct E; unfold simpl_fill in *; inverts* H1;
      try solve[forwards*: step_not_value Red1];
      try solve[forwards*: step_not_fvalue Red1];
      try solve[inverts* H].
    +
      destruct E; unfold simpl_fill in *; inverts* H1;
      try solve[forwards*: step_not_value Red1];
      try solve[forwards*: step_not_fvalue Red1];
      try solve[inverts* H].
  - (* \x.e v *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1;
    try solve[forwards*: step_not_abs H3];
    try solve[forwards*: step_not_value H3]].
  -
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in *; inverts* H2;
    try solve[forwards*: step_not_abs H4];
    try solve[forwards*: step_not_value H4];
    try solve[forwards*: step_not_fvalue H4];
    try solve[inverts* H3]].
    +
    forwards* h1: pattern_abs_uniq H0 H7.
    inverts* h1.
    rewrite H1 in *.
    inverts* H8.
    +
    inverts H7; try solve[simpl in *; exfalso; apply H6; auto; inverts H].
  - (* abeta *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in *; inverts* H0;
    try solve[forwards*: step_not_value H2];
    try solve[forwards*: step_not_fvalue H2];
    try solve[inverts* H2];
    try solve[inverts* H1]]; simpl in *.
  - (* p:dyn v *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in *; inverts* H1; simpl in *;
    try solve[forwards*: step_not_value H3];
    try solve[inverts* H2;simpl in *; exfalso; apply H; auto]]; simpl in *; try solve[exfalso; apply H; auto];
    try solve[inverts* H5;simpl in *; exfalso; apply H; auto];
    try solve[rewrite H7 in *; exfalso; apply H; auto].
  - (* v: a *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in *; inverts* H2;
    try solve[forwards*: step_not_value H4]].
    +
     inverts Typ as h1. inverts h1 as h1.
     inverts h1 as h1. inverts h1 as h1.
     forwards*: meet_unique H0 H7.
     subst.
     forwards*:  Cast_unique H H5.
     congruence.
    +
      exfalso; apply H6; eauto.
      forwards*: meet_sim H0.
    +
     inverts Typ as h1. inverts h1 as h1.
     inverts h1 as h1. inverts h1 as h1.
     forwards*: meet_unique H0 H7.
     subst.
     forwards*:  Cast_unique H H5.
     congruence.
  - (* annovp *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in *; inverts* H1;
    try solve[forwards*: step_not_value H3]].
    exfalso; apply H; eauto.
    forwards*: meet_sim H6.
  -
    (* annovp *)
    inverts* Red2;
    try solve[destruct E; unfold simpl_fill in *; inverts* H2;
    try solve[forwards*: step_not_value H4]].
    inverts Typ as h1. inverts h1 as h1.
     inverts h1 as h1. inverts h1 as h1.
     forwards*: meet_unique H0 H7.
     subst.
     forwards*:  Cast_unique H H5.
     congruence.
  - (* e_l v --> blame *)
     inverts* Red2;
    try solve[destruct E; unfold simpl_fill in H1; inverts* H1;
    forwards*: step_not_value H3];
    try solve[inverts H];
    try solve[forwards*: step_not_value H3]; simpl in *.
    exfalso; apply H; simpl; eauto.
  - (* e_l v --> *)
     inverts* Red2;
    try solve[destruct E; unfold simpl_fill in *; inverts* H2;
    forwards*: step_not_value H4];
    try solve[inverts H];
    try solve[forwards*: step_not_value H3]; simpl in *.
    +
    exfalso; apply H4; simpl; eauto.
    +
    forwards* h1: pattern_pro_uniq H H5. inverts* h1.
  - (* e_r v --> blame *)
    inverts* Red2;
   try solve[destruct E; unfold simpl_fill in H1; inverts* H1;
   forwards*: step_not_value H3];
   try solve[inverts H];
   try solve[forwards*: step_not_value H3]; simpl in *.
   exfalso; apply H; simpl; eauto.
 - (* e_r v --> *)
    inverts* Red2;
   try solve[destruct E; unfold simpl_fill in *; inverts* H2;
   forwards*: step_not_value H4];
   try solve[inverts H];
   try solve[forwards*: step_not_value H3]; simpl in *.
   +
   exfalso; apply H4; simpl; eauto.
   +
   forwards* h1: pattern_pro_uniq H H5. inverts* h1.
 - (* |add| v*)
  inverts* Red2;
   try solve[destruct E; unfold simpl_fill in *; inverts* H;
   try solve[forwards*: step_not_value H1];
   try solve[forwards*: step_not_fvalue H1]].
 - (* |addl i| v*)
   inverts* Red2;
   try solve[destruct E; unfold simpl_fill in *; inverts* H;
   try solve[forwards*: step_not_value H1];
   try solve[forwards*: step_not_fvalue H1]].
Qed.


