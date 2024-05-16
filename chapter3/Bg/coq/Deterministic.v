Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        syntax_ott
        syntaxb_ott
        rules_inf
        Typing
        Infrastructure.

Require Import Strings.String.



Lemma flike_not_ground: forall v,
 value v ->
 FLike (dynamic_type v) ->
 not(Ground (dynamic_type v)).
Proof.
  introv val fl.
  inductions val; simpl in *; try solve[inverts* fl;
  inverts* H0;inverts* H2];
  try solve[unfold not; intros nt; inverts* nt].
  inverts* fl. inverts H1.
  unfold not; intros nt; inverts* nt.
  inverts* fl. inverts H1.
  unfold not; intros nt; inverts* nt.
Qed.



Lemma UG_not_ground: forall A B,
 UG A B ->
 not(Ground A).
Proof.
  introv gr.
  inverts gr as h1 h2.
  inverts h2 as h3 h4.
  inverts h4 as h4 h5.
  unfold not;intros nt.
  inverts h3. 
  - 
    inverts* h1.
  -
    inverts* h1.
    inverts nt.
    apply h4; auto.
  -
    inverts* h1.
    inverts nt.
    apply h4; auto.
Qed.



Lemma UG_sim: forall A B C,
  UG A B ->
  Ground C ->
  sim C B ->
  sim C A .
Proof.
  introv h1 h2 h0.
  inverts h1 as h11 h12.
  inverts h12 as h12 h13.
  inverts h13 as h13 h14.
  inverts h12.
  -
    inverts h11.
    exfalso; apply h13; auto.
    exfalso; apply h14; auto.
  -
    inverts h11.
    inverts h0.
    inverts* h2.
    inverts* h2.
    exfalso; apply h14; auto.
  -
    
    inverts h11.
    inverts h0.
    inverts* h2.
    exfalso; apply h14; auto.
    inverts h0.
    inverts* h2.
    inverts* h2.  
Qed.



Lemma UG_uniq: forall A B1 B2,
 UG A B1 ->
 UG A B2 ->
 B1 = B2.
Proof.
  introv gr1 gr2.
  inverts gr1 as h1 h2.
  inverts h2 as h3 h4.
  inverts h4 as h4 h5.
  inverts gr2 as h21 h22.
  inverts h22 as h23 h24.
  inverts h24 as h24 h25.
  destruct A; try solve[inverts* h1].
  -
    inverts* h1.
    inverts* h3.
  -
    inverts* h1.
    inverts* h3.
    inverts* h21.
    inverts* h23.
    inverts* h23.
    inverts* h3.
  -
    inverts* h1.
    inverts* h3.
    inverts* h21.
    inverts* h23.
    inverts* h23.
    inverts* h3.
Qed.


Lemma Cast_sim_aux: forall v A r,
    value v -> Cast v A r -> sim (dynamic_type v) A.
Proof with auto.
  introv Val Red.
  lets Red': Red.
  inductions Red; simpl in *; eauto.
  -
    rewrite H0.
    auto.
  -
    inverts Val as h3 h4.
    forwards*: IHRed1 Red1.
  -
    inverts Val as h3 h4.
    forwards* h5: IHRed1 Red1.
  -
    inverts Val as h3 h4.
    forwards* h5: IHRed1 Red1.
Qed.


Lemma Cast_unique: forall v r1 r2 (A: typ) B,
    value v -> Typing nil v Chk B -> Cast v A r1 -> Cast v A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2. 
  gen r2 B.
  lets R1': R1.
  inductions R1; introv R2 typ;
    try solve [inverts* R2].
  - 
    inverts* R2; try solve[inverts* H0].
  - 
    inverts* R2; try solve[inverts H].
    forwards*: UG_not_ground H0.
  - 
    inverts* R2; try solve[ inverts* H1];
    try solve[ inverts* H0].
    +
      inverts Val.
      rewrite H2 in *.
      inverts H1.
    +
      exfalso.
      apply H1.
      eauto.
  - 
    inverts* R2;
    try solve[forwards*: UG_not_ground H];
    try solve[inverts* H].
    forwards* h1: UG_uniq H H0.
    inverts* h1.
    forwards*: IHR1.
    congruence.
  - 
    inverts* R2;
    try solve[inverts* H];
    try solve[inverts* H1];
    try solve[inverts* H2];
    try solve[
    inverts Val; try solve[forwards*: UG_not_ground H]; eauto].
    +
    inverts typ as typ.
    inverts typ as typ.
    inverts* Val.
    +
    inverts typ as typ.
    inverts typ as typ.
    inverts typ as typ.
    inverts* Val.
    forwards*: Cast_sim_aux R1.
  - inverts* R2; try solve[inverts* H3];
    try solve[inverts* H2];
    try solve[inverts* H1].
    +
    inverts* Val.
    rewrite <- H0 in H2. inverts H2.
    +
    inverts* Val.
    rewrite <- H in *. inverts H3.
    +
    inverts* Val.
    forwards*: UG_not_ground H2.
    +
    exfalso; apply H0;eauto.
  -
    inverts* R2; try solve[inverts* H3];
    try solve[inverts* H1];
    try solve[inverts* H0].
    +
    exfalso; apply H; eauto.
    +
    inverts Val.
    forwards*: Cast_sim_aux H2.
    +
    exfalso; apply H;simpl; eauto.
  -
    inverts* R2; try solve[inverts* Val; inverts typ as h1; inverts* h1];
    try solve[inverts* H1];
    try solve[inverts* H0].
    +
    inverts typ as typ1.
    inverts typ1 as typ1 typ2.
    inverts Val.
    forwards* h1: IHR1_1 H4.
    forwards* h2: IHR1_2 H5.
    congruence.
    +
    inverts typ as typ1.
    inverts typ1 as typ1 typ2.
    inverts Val.
    forwards* h1: IHR1_1 H4.
    forwards* h2: IHR1_2 H5.
    congruence.
    +
    inverts typ as typ1.
    inverts typ1 as typ1 typ2.
    inverts Val.
    forwards* h1: IHR1_1 H4.
    forwards* h2: IHR1_2 H5.
    congruence.
  -
    inverts* R2; try solve[inverts* Val; inverts typ as h1; inverts* h1];
    try solve[inverts* H1];
    try solve[inverts* H0].
    +
    inverts typ as typ1.
    inverts typ1 as typ1 typ2.
    inverts Val.
    forwards* h1: IHR1_1 H4.
    forwards* h2: IHR1_2 H5.
    congruence.
  -
    inverts* R2; try solve[inverts* Val; inverts typ as h1; inverts* h1];
    try solve[inverts* H1];
    try solve[inverts* H0].
    +
    inverts typ as typ1.
    inverts typ1 as typ1 typ2.
    inverts Val.
    forwards* h1: IHR1_1 H4.
    forwards* h2: IHR1_2 H5.
    congruence.
Qed.


Lemma fill_auxi: forall E1 E0 e0 e1 r2 r1,
 fill E0 e0 = fill E1 e1 ->
 wellformed E0 ->
 wellformed E1 ->
 step e0 r1 ->
 step e1 r2 ->
 (E1 = E0)/\ (e0 = e1).
Proof.
  introv eq wf1 wf2 red1 red2. gen E1 e0 e1 r1 r2.
  inductions E0; unfold fill in *;  intros. 
  - inductions E1; unfold fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_value red1.
  - inductions E1; unfold fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_value red2.
  - inductions E1; unfold fill in *; inverts* eq.   
  -
     inductions E1; unfold fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_value red1.
  -
    inductions E1; unfold fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_value red2.
  -
    inductions E1; unfold fill in *; inverts* eq.
  -
    inductions E1; unfold fill in *; inverts* eq.
Qed.


Lemma fill_typ: forall E e1 A,
 wellformed E ->
 Typing nil (fill E e1) Chk A ->
 exists B, Typing nil e1 Chk B.
Proof.
  introv wf Typ. gen e1 A. 
  inductions E; intros;
  try solve[simpl in *;
  inverts Typ; inverts H;
  exists*].
Qed.


Theorem step_unique: forall A e r1 r2,
    Typing nil e Chk A -> step e r1 -> step e r2 -> r1 = r2.
Proof.
  introv Typ Red1.
  gen A r2.
  lets Red1' : Red1.
  induction Red1;
    introv Typ Red2.
  - (* fill -e *)
    inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_value Red1];
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value Red1];
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value Red1].
    +
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
    +
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
    +
    destruct E; unfold fill in H0; inverts* H0.
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value Red1.
    inverts H. inverts H2.
  - (* fill -blame *)
    inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value Red1];
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value Red1;
    try solve[inverts* H;inverts* H2]].
    +
    forwards*: fill_auxi H0. inverts H3. 
    forwards*: fill_typ Typ. inverts H3.
    forwards*: IHRed1 Red1 H2. congruence.
    +
    destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1.
    inverts H. inverts H2.
  - (* beta *)
    inverts* Red2; try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value H4].
    +
    inverts Typ.
    inverts H2. 
    forwards*: Cast_unique H1 H9.
    congruence.
    +
    inverts Typ.
    inverts H2. 
    inverts H12.
    inverts H10.
    inverts H5. 
    forwards*: Cast_unique H1 H6.
    congruence.
  - (* anno beta -> blame*)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H3;inverts* H0;
    forwards*: step_not_value H5;eapply value_fanno;eauto;reflexivity;
    forwards*: step_not_value H5];
    try solve[inverts* H0].
    +
    inverts H0.
    inverts Typ.
    inverts H0. 
    forwards*: Cast_unique H1 H8.
    congruence.
    +
    inverts* H0.
    inverts Typ.
    inverts H0. 
    forwards*: Cast_unique H1 H7.
    congruence.
    +
    inverts* H0.
    inverts Typ.
    inverts H0. 
    forwards*: Cast_unique H1 H7.
    congruence.
    +
    inverts* H0.
    inverts Typ.
    inverts H0. 
    forwards*: Cast_unique H1 H6.
    congruence.
  - (* annov *)
    inverts* Red2;
    try solve[destruct E; unfold fill in H2; inverts* H2;
    forwards*: step_not_value H4;
    forwards*: step_not_value H4].
    inverts Typ. inverts H2.
    forwards*: Cast_unique H0 H5.
  - (* add *) 
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H1;
    forwards*: step_not_value H3;
    forwards*: step_not_value H3];
    try solve[inverts* H8];
    try solve[inverts* H0].
    +
    inverts Typ.
    inverts H1. inverts H4.
    forwards*: Cast_unique H0 H5.
    congruence.
    +
    inverts Typ.
    inverts H1. 
    forwards*: Cast_unique H0 H3.
    congruence.
  - (* addl *) 
    inverts* Red2;
    try solve[destruct E; unfold fill in H1; inverts* H1;
    forwards*: step_not_value H3;
    forwards*: step_not_value H3].
    +
    inverts Typ.
    inverts H1.
    inverts H4.
    forwards*: Cast_unique H0 H5.
    congruence.
    +
    inverts Typ.
    inverts H1.
    forwards*: Cast_unique H0 H5.
    congruence.
  - (* annotate beta *) 
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H3; 
    forwards*: step_not_value H5; eapply value_fanno; simpl; eauto].
    +
    inverts Typ.
    inverts H3.
    inverts* H6.
    forwards*: Cast_unique H0 H7.
    congruence.
    +
    inverts Typ.
    inverts H3.
    forwards*: Cast_unique H0 H9.
    congruence.
  - (* v1:dyn:dyn->dyn v2 *) 
    inverts* Red2.
    +
    destruct E; unfold fill in *; inverts* H0;
    forwards*: step_not_value H2.
    inverts* H1. inverts* H3.
    +
    destruct E; unfold fill in *; inverts* H0;
    forwards*: step_not_value H2.
    inverts* H1. inverts* H3.
    +
    inverts* H3.
  - (* l *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H0; 
    forwards*: step_not_value H2; eapply value_fanno; simpl; eauto].
  -
    (* r *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H0; 
    forwards*: step_not_value H2; eapply value_fanno; simpl; eauto].
  -
    (* prol *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H1; 
    forwards*: step_not_value H3; eapply value_fanno; simpl; eauto].
  -
    (* prol *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H1; 
    forwards*: step_not_value H3; eapply value_fanno; simpl; eauto].
Qed.


