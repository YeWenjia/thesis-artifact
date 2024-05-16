Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import Lia.
Require Import
        syntax_ott
        rules_inf
        Typing
        Infrastructure
        Key_Properties
        Subtyping_inversion.

Require Import Strings.String.


Lemma sub_decidable:forall A B,
(sub A B \/ ~ (sub A B)) /\ (sub B A \/ ~ (sub B A)).
Proof.
  introv. gen B. 
  inductions A; intros;eauto.
  - inductions B; eauto; 
    try solve[split*; right; unfold not; intros nt; inverts* nt; inverts* H];
    try solve[split*; left*].
    + forwards*: IHB1. forwards*: IHB2.
      split.
      inverts H. inverts H0. inverts H1; inverts H.
      left*.
      right. unfold not; intros nt; inverts* nt; inverts* H.
      right. unfold not; intros nt; inverts* nt; inverts* H.
      right. unfold not; intros nt; inverts* nt; inverts* H.
      inverts H. inverts H0. inverts H2; inverts H3. 
      left*.
      left*.
      left*.
      right. unfold not; intros nt; inverts* nt.
  - inductions B; eauto; 
    try solve[split*; right; unfold not; intros nt; inverts* nt; inverts* H].
    + forwards*: IHB1. forwards*: IHB2.
      split.
      inverts H. inverts H0. inverts H1; inverts H.
      left*.
      right. unfold not; intros nt; inverts* nt; inverts* H.
      right. unfold not; intros nt; inverts* nt; inverts* H.
      right. unfold not; intros nt; inverts* nt; inverts* H.
      inverts H. inverts H0. inverts H2; inverts H3.
      left*.
      left*.
      left*.
      right. unfold not; intros nt; inverts* nt.
  - inductions B; eauto; 
    try solve[split*; right; unfold not; intros nt; inverts* nt; inverts* H];
    try solve[split*; left*].
    + forwards*: IHB1. forwards*: IHB2.
      split.
      inverts H. inverts H0. inverts H1; inverts H.
      left*.
      right. unfold not; intros nt; inverts* nt; inverts* H.
      right. unfold not; intros nt; inverts* nt; inverts* H.
      right. unfold not; intros nt; inverts* nt; inverts* H.
      inverts H. inverts H0. inverts H2; inverts H3. 
      left*.
      left*.
      left*.
      right. unfold not; intros nt; inverts* nt.
  - inductions B; eauto; 
    try solve[split*; right; unfold not; intros nt; inverts* nt;inverts* H].
    + split.
      forwards*: IHA1 B1. forwards*: IHA2 B2. inverts H0. inverts H.
      inverts H3; inverts H1.
      left*.
      right. unfold not; intros nt; inverts* nt; inverts H1.
      right. unfold not; intros nt; inverts* nt;inverts H1.
      right. unfold not; intros nt; inverts* nt;inverts H1.

      forwards*: IHA1 B1. forwards*: IHA2 B2. inverts H0. inverts H.
      inverts H0; inverts H2.
      left*.
      right. unfold not; intros nt; inverts* nt;inverts H2.
      right. unfold not; intros nt; inverts* nt;inverts H2.
      right. unfold not; intros nt; inverts* nt;inverts H2.
    +
      split.
      forwards*: IHB1. forwards*: IHB2.
      inverts H. inverts H0.
      inverts H1; inverts H.
      left*.
      right. unfold not; intros nt; inverts* nt;inverts* H.
      right. unfold not; intros nt; inverts* nt;inverts* H.
      right. unfold not; intros nt; inverts* nt;inverts* H.

      forwards*: IHB1. forwards*: IHB2.
      inverts H. inverts H0.
      inverts H2; inverts H3.
      left*. left*. left*.
      right. unfold not; intros nt; inverts* nt.
  - 
    inductions B; eauto; 
    try solve[split*; right; unfold not; intros nt; inverts* nt;inverts* H].
    + split.
      forwards*: IHA1 dt_int. forwards*: IHA2 dt_int.
      inverts H. inverts H0.
      inverts H1; inverts H.
      left*. left*. left*.
      right. unfold not; intros nt; inverts* nt.

      forwards*: IHA1 dt_int. forwards*: IHA2 dt_int.
      inverts H. inverts H0.
      inverts H2; inverts H3.
      left*.
      right. unfold not; intros nt; inverts* nt; inverts* H3.
      right. unfold not; intros nt; inverts* nt; inverts* H3.
      right. unfold not; intros nt; inverts* nt; inverts* H3.
    + split.
      forwards*: IHA1 dt_top. 
      forwards*: IHA1 dt_top. forwards*: IHA2 dt_top.
      inverts H. inverts H0.
      inverts H2; inverts H3.
      left*.
      right. unfold not; intros nt; inverts* nt; inverts* H3.
      right. unfold not; intros nt; inverts* nt; inverts* H3.
      right. unfold not; intros nt; inverts* nt; inverts* H3.
    + split. 
      forwards*: IHA1 (dt_bot). forwards*: IHA2 (dt_bot).
      inverts* H. inverts H0.
      inverts* H1. inverts H.
      left*. right. unfold not; intros nt; inverts* nt.
      left*.
    + split. 
      forwards*: IHA1 (dt_arrow B1 B2). forwards*: IHA2 (dt_arrow B1 B2).
      inverts* H. inverts H0.
      inverts* H1. inverts H.
      left*. right. unfold not; intros nt; inverts* nt.

      forwards*: IHA1 (dt_arrow B1 B2). forwards*: IHA2 (dt_arrow B1 B2).
      inverts* H. inverts H0.
      inverts* H2. inverts H3.
      left*. right. unfold not; intros nt; inverts* nt; inverts* H3. 
      right. unfold not; intros nt; inverts* nt; inverts* H2.
    + split.
      forwards: IHB1. forwards: IHB2.
      inverts H. inverts H0.
      inverts H1; inverts H.
      left*. 
      right. unfold not; intros nt; inverts* nt;try solve [inverts* H].
      apply H1. forwards*: dand_inversion H6.
      apply H1. forwards*: dand_inversion H6.
      right. unfold not; intros nt; inverts* nt;try solve [inverts* H].
      apply H0. forwards*: dand_inversion H6.
      apply H0. forwards*: dand_inversion H6.
      right. unfold not; intros nt; inverts* nt;try solve [inverts* H].
      apply H1. forwards*: dand_inversion H6.
      apply H1. forwards*: dand_inversion H6.
      
      forwards: IHA1 (dt_and B1 B2). forwards: IHA2 (dt_and B1 B2).
      inverts H. inverts H0.
      inverts H2; inverts H3.
      left*. 
      right. unfold not; intros nt; inverts* nt;try solve [inverts* H3].
      apply H2. forwards*: dand_inversion H6.
      apply H2. forwards*: dand_inversion H6.
      right. unfold not; intros nt; inverts* nt;try solve [inverts* H3].
      apply H0. forwards*: dand_inversion H6.
      apply H0. forwards*: dand_inversion H6.
      right. unfold not; intros nt; inverts* nt;try solve [inverts* H3].
      apply H0. forwards*: dand_inversion H6.
      apply H0. forwards*: dand_inversion H6.
    + split.
      forwards: IHA1 (dt_rcd l B). forwards: IHA2 (dt_rcd l B).
      inverts H. inverts H0. inverts H1. inverts H.
      left*. left*.
      inverts H. left*.
      right. unfold not; intros nt; inverts* nt. 
     
      forwards: IHA1 (dt_rcd l B). forwards: IHA2 (dt_rcd l B).
      inverts H. inverts H0. inverts H2. inverts H3.
      left*. 
      right. unfold not; intros nt; inverts* nt;try solve[inverts* H3].
      right. unfold not; intros nt; inverts* nt;try solve[inverts* H2].
  - inductions B; eauto; 
    try solve[split*; right; unfold not; intros nt; inverts* nt].
    + 
      inverts IHB1. inverts IHB2. 
      split. inverts H1. inverts H.
      left*.
      right; unfold not; intros nt; inverts* nt; inverts* H.
      right; unfold not; intros nt; inverts* nt; inverts* H1.
      inverts H0; inverts H2.
      left*. left*. left*. 
      right; unfold not; intros nt; inverts* nt; inverts* H1.      
    + destruct(l == l0). inverts e.
      * forwards: IHA B. inverts H. 
        split. inverts H0. left*.
        right; unfold not; intros nt; inverts* nt; inverts* H0.
        inverts H1. left*.
        right; unfold not; intros nt; inverts* nt; inverts* H1.
      * 
        split; try solve[right; unfold not; intros nt; inverts* nt;inverts H].
Qed.




Lemma Cast_unique: forall v r1 r2 A,
    value v -> (exists B, Typing nil v Chk B) -> Cast v A r1 -> Cast v A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2.
  gen r2.
  lets R1': R1.
  inductions R1; introv R2;
    try solve [inverts~ R2; try solve[inverts H2];try solve_false;
    try solve[forwards* h1: not_top_cs; inverts* h1] ];
    try solve [forwards*: Cast_toplike_uniq R1' R2];eauto.
  - 
    inverts* R2; try solve_false; simpl in *;
    try solve[inverts* H1].
  -
    inverts* R2; try solve_false; simpl in *;
    try solve[inverts* H0];
    try solve[inverts* H6].
    inverts H as h1.
    inverts h1 as h1.
    inverts h1 as h1.
    inverts Val as h3; try solve[inverts h3].
    forwards* h2: IHR1 H4.
    congruence.
  -
    inverts* R2; try solve_false; simpl in *;
    try solve[inverts* H0];
    try solve[inverts* H2].
    +
    inverts H as h1.
    inverts h1 as h1.
    inverts h1 as h1.
    inverts Val as h3; try solve[inverts h3].
    forwards* h2: IHR1 H6.
    +
    forwards* h1: Cast_sub R1.
    forwards* h2: Cast_sub H6.
    inverts H as hh1.
    inverts hh1 as hh1.
    inverts hh1 as hh1 hh2 hh3.
    rewrite <- disjoint_eqv in hh3.
    unfold disjointSpec in *.
    inverts Val as h5; try solve[inverts h5].
    forwards* h4: principal_inf hh1.
    forwards* h6: principal_inf hh2.
    rewrite h4 in *.
    rewrite h6 in *.
    forwards* h7: hh3 h1 h2.
    forwards* h8: Cast_toplike_uniq R1 H6.
    rewrite topLike_super_top; auto.
  -
    inverts* R2; try solve_false; simpl in *;
    try solve[inverts* H0];
    try solve[inverts* H2].
    +
    forwards* h1: Cast_sub R1.
    forwards* h2: Cast_sub H6.
    inverts H as hh1.
    inverts hh1 as hh1.
    inverts hh1 as hh1 hh2 hh3.
    rewrite <- disjoint_eqv in hh3.
    unfold disjointSpec in *.
    inverts Val as h5; try solve[inverts h5].
    forwards* h4: principal_inf hh1.
    forwards* h6: principal_inf hh2.
    rewrite h4 in *.
    rewrite h6 in *.
    forwards* h7: hh3 h2 h1.
    forwards* h8: Cast_toplike_uniq R1 H6.
    rewrite topLike_super_top; auto.
    +
    inverts H as h1.
    inverts h1 as h1.
    inverts h1 as h1.
    inverts Val as h3; try solve[inverts h3].
    forwards* h2: IHR1 H6.
  -
    inverts* R2; try solve_false; simpl in *;
    try solve[inverts* H0];
    try solve[inverts* H2].
    +
    forwards*: IHR1_1 R1_1 H3.
    forwards*: IHR1_2 R1_2 H5.
    congruence.
Qed.


Lemma dsfill_eq: forall E0 e0 E e1 r1 r2,
  fill E0 e0 = fill E e1 ->
  step e0 r1 ->
  step e1 r2 ->
  wellformed E ->
  wellformed E0 ->
  E = E0 /\ e0 = e1.
Proof.
  introv eq red1 red2 wf1 wf2. gen E e0 e1 r1 r2.
  inductions E0; unfold fill in *;  intros.
  - inductions E; unfold fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_abs red1.
  - inductions E; unfold fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_abs red2.
  - inductions E; unfold fill in *; inverts* eq.
    inverts wf1.
    forwards*: step_not_value red1.
  - inductions E; unfold fill in *; inverts* eq.
    inverts wf2.
    forwards*: step_not_value red2.
  - inductions E; unfold fill in *; inverts* eq.
  - inductions E; unfold fill in *; inverts* eq.
  - inductions E; unfold fill in *; inverts* eq.
Qed.


Lemma dsfill_eq_cbn: forall E0 e0 E e1 r1 r2,
  filln E0 e0 = filln E e1 ->
  cbn e0 r1 ->
  cbn e1 r2 ->
  wellformedn E ->
  wellformedn E0 ->
  E = E0 /\ e0 = e1.
Proof.
  introv eq red1 red2 wf1 wf2. gen E e0 e1 r1 r2.
  inductions E0; unfold fill in *;  intros;
  try solve[inductions E; unfold fill in *; inverts* eq];
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf1;
  forwards*: nstep_not_value red1];
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf2;
  forwards*: nstep_not_value red2].
Qed.



Lemma dmergel_inf: forall e1 e2 t,
 Typing nil (de_merge e1 e2) Inf t ->
 exists t2, Typing nil e1 Inf t2.
Proof.
  introv typ.
  inverts* typ.
Qed.


Lemma dmerger_inf: forall e1 e2 t,
 Typing nil (de_merge e1 e2) Inf t ->
 exists t2, Typing nil e2 Inf t2.
Proof.
  introv typ.
  inverts* typ.
Qed.




Lemma get_value_inp: forall t l t',
 get_value t l t' ->
 inp t l.
Proof.
  introv gv.
  inductions gv; eauto.
Qed.



Lemma fill_chk:  forall E e A,
  nil ⊢ fill E e ⇐  A ->
  exists B, nil ⊢ e ⇐  B .
Proof.
  introv typ.
  forwards* h2: Typing_regular_1 typ.
  inverts typ as typ1 typ2. 
  -
    destruct E; unfold fill in *; inverts* H.
  -
    destruct E; unfold fill in *; inverts* typ1.
  -
    destruct E; unfold fill in *; inverts* H.
  -
    destruct E; unfold fill in *; inverts* H.
    exists.
    forwards*: Typing_well typ2.
Qed.


Lemma filln_chk:  forall E e A,
  nil ⊢ filln E e ⇐  A ->
  exists B, nil ⊢ e ⇐  B .
Proof.
  introv typ.
  forwards* h2: Typing_regular_1 typ.
  inverts typ as typ1 typ2. 
  -
    destruct E; unfold filln in *; inverts* H.
  -
    destruct E; unfold filln in *; inverts* typ1.
  -
    destruct E; unfold filln in *; inverts* H.
  -
    destruct E; unfold filln in *; inverts* H.
    exists.
    forwards*: Typing_well typ2.
Qed.


Theorem step_unique: forall A e r1 r2,
   Typing nil e Chk A -> step e r1 -> step e r2 -> r1 = r2.
Proof.
  introv Typ Red1.
  gen A r2.
  lets Red1' : Red1.
  inductions Red1; eauto;
    introv Typ Red2.
  - (* fill E e -> fill E e' *)
    inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_value Red1];
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_abs Red1];
    try solve[destruct E; unfold fill in H1; inverts* H1];
    try solve[
      destruct E; unfold fill in *; inverts* H0;
      try solve[forwards*: step_not_value Red1];
      try solve[
      forwards*: step_not_abs Red1];
      try solve[inverts H]
    ];
    try solve[
      destruct E; unfold fill in *; inverts* H0;
      try solve[forwards*: step_not_value Red1];
      try solve[
      forwards*: step_not_fix Red1];
      try solve[inverts H]
    ].
    + 
      forwards*: dsfill_eq H0.
      destruct H3. subst.
      forwards*: fill_chk Typ. inverts H3.
      destruct E0; unfold fill in H4; inverts H4;
      forwards*: IHRed1 Red1 H2; congruence.
  - (* beta *)
     inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H1;
    try solve[
    forwards*: step_not_abs H3];
    try solve[forwards*: step_not_value H3]]
    .
  - (*  abeta *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H0;
    try solve[
    forwards*: step_not_abs H2];
    try solve[forwards*: step_not_value H2];
    try solve[inverts* H1]].
  - (* v:a *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H2;
    forwards*: step_not_value H4];
    try solve[inverts H as h0;inverts h0];
    try solve[inverts* H3];
    try solve[forwards*: step_not_value H5].
    inverts Typ as h1.
    inverts h1 as h1.
    forwards*: Cast_unique H0 H5.
  - (* v.l -> v *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H2;
    forwards*: step_not_value H4];
    try solve[inverts* H1].
    inverts Typ as h1.
    inverts h1 as h1.
    forwards* h3:get_ty_uniq H0 H5.
    subst.
    forwards* h2: Cast_unique H1 H7.
    congruence.
  -
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H0;
    forwards*: step_not_value H2];
    try solve[destruct E; unfold fill in *; inverts* H0;
    forwards*: step_not_fix H2];
    try solve[inverts H2 as h0;inverts h0].
Qed.



Theorem step_unique_cbn: forall A e r1 r2,
   Typing nil e Chk A -> cbn e r1 -> cbn e r2 -> r1 = r2.
Proof.
  introv Typ Red1.
  gen A r2.
  lets Red1' : Red1.
  inductions Red1; eauto;
    introv Typ Red2.
  - (* fill E e -> fill E e' *)
    inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: nstep_not_value Red1;
    forwards*: nstep_not_value Red1];
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: nstep_not_value Red1;
    forwards*: nstep_not_abs Red1];
    try solve[destruct E; unfold fill in H1; inverts* H1];
    try solve[
      destruct E; unfold fill in *; inverts* H0;
      try solve[forwards*: nstep_not_value Red1];
      try solve[
      forwards*: nstep_not_abs Red1];
      try solve[inverts H]
    ];
    try solve[
      destruct E; unfold fill in *; inverts* H0;
      try solve[forwards*: nstep_not_value Red1];
      try solve[
      forwards*: nstep_not_fix Red1];
      try solve[inverts H]
    ].
    + 
      forwards*: dsfill_eq_cbn H0.
      destruct H3. subst.
      forwards*: filln_chk Typ. inverts H3.
      destruct E0; unfold fill in H4; inverts H4;
      forwards*: IHRed1 Red1 H2; congruence.
  - (* beta *)
     inverts* Red2;
    try solve[destruct E; unfold filln in *; inverts* H0;
    try solve[
    forwards*: nstep_not_abs H2];
    try solve[forwards*: nstep_not_value H2]]
    .
  - (*  abeta *)
    inverts* Red2;
    try solve[destruct E; unfold filln in *; inverts* H0;
    try solve[
    forwards*: nstep_not_abs H2];
    try solve[forwards*: nstep_not_value H2];
    try solve[inverts* H1]].
  - (* v:a *)
    inverts* Red2;
    try solve[destruct E; unfold filln in *; inverts* H2;
    forwards*: nstep_not_value H4];
    try solve[inverts H as h0;inverts h0];
    try solve[inverts* H3];
    try solve[forwards*: nstep_not_value H5].
    inverts Typ as h1.
    inverts h1 as h1.
    forwards*: Cast_unique H0 H5.
  - (* v.l -> v *)
    inverts* Red2;
    try solve[destruct E; unfold filln in *; inverts* H2;
    forwards*: nstep_not_value H4];
    try solve[inverts* H1].
    inverts Typ as h1.
    inverts h1 as h1.
    forwards* h3:get_ty_uniq H0 H5.
    subst.
    forwards* h2: Cast_unique H1 H7.
    congruence.
  -
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H0;
    forwards*: nstep_not_fix H2];
    try solve[inverts H2 as h0;inverts h0].
Qed.