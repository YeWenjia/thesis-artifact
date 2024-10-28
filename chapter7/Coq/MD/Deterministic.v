Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        syntax_ott
        rules_inf
        Typing
        Infrastructure
        Key_Properties
        Subtyping_inversion.
Require Import Lia.

Require Import Strings.String.


Lemma eq_type: forall A,
 (A = t_dyn) \/ not(A = t_dyn).
Proof.
  introv.
  inductions A; try solve[left*];
  try solve[right; unfold not;intros nt;inverts* nt].
Qed.




(* Lemma eq_dec : forall x y:res, {x = y} + {x <> y}.
Proof.
  decide equality; auto;
  try solve[forwards*: eq_dec_exp].
  destruct e; destruct e0; eauto.
  right. unfold not;intros nt;inverts nt.
  right. unfold not;intros nt;inverts nt.
Defined. *)


Lemma csub_decidable:forall A B,
(csub A B \/ ~ (csub A B)) /\ (csub B A \/ ~ (csub B A)).
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
    try solve[split*; right; unfold not; intros nt; inverts* nt;inverts* H].
    +
      split*.
      forwards*: IHB1. forwards*: IHB2.
      inverts H. inverts H0.
      inverts* H2. inverts* H3.
      right. unfold not; intros nt; inverts* nt;inverts* H.
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
      forwards*: IHA1 t_int. forwards*: IHA2 t_int.
      inverts H. inverts H0.
      inverts H1; inverts H.
      left*. left*. left*.
      right. unfold not; intros nt; inverts* nt.

      forwards*: IHA1 t_int. forwards*: IHA2 t_int.
      inverts H. inverts H0.
      inverts H2; inverts H3.
      left*.
      right. unfold not; intros nt; inverts* nt; inverts* H3.
      right. unfold not; intros nt; inverts* nt; inverts* H3.
      right. unfold not; intros nt; inverts* nt; inverts* H3.
    + split.
      forwards*: IHA1 t_top. 
      forwards*: IHA1 t_top. forwards*: IHA2 t_top.
      inverts H. inverts H0.
      inverts H2; inverts H3.
      left*.
      right. unfold not; intros nt; inverts* nt; inverts* H3.
      right. unfold not; intros nt; inverts* nt; inverts* H3.
      right. unfold not; intros nt; inverts* nt; inverts* H3.
    + split.
      forwards*: IHA1 t_bot. forwards*: IHA2 t_bot.
      inverts H. inverts H0.
      inverts* H1. inverts* H.
      right. unfold not; intros nt; inverts* nt.
      left*.
    + split. 
      forwards*: IHA1 (t_arrow B1 B2). forwards*: IHA2 (t_arrow B1 B2).
      inverts* H. inverts H0.
      inverts* H1. inverts H.
      left*. right. unfold not; intros nt; inverts* nt.

      forwards*: IHA1 (t_arrow B1 B2). forwards*: IHA2 (t_arrow B1 B2).
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
      apply H1. forwards*: cand_inversion H6.
      apply H1. forwards*: cand_inversion H6.
      right. unfold not; intros nt; inverts* nt;try solve [inverts* H].
      apply H0. forwards*: cand_inversion H6.
      apply H0. forwards*: cand_inversion H6.
      right. unfold not; intros nt; inverts* nt;try solve [inverts* H].
      apply H1. forwards*: cand_inversion H6.
      apply H1. forwards*: cand_inversion H6.
      
      forwards: IHA1 (t_and B1 B2). forwards: IHA2 (t_and B1 B2).
      inverts H. inverts H0.
      inverts H2; inverts H3.
      left*. 
      right. unfold not; intros nt; inverts* nt;try solve [inverts* H3].
      apply H2. forwards*: cand_inversion H6.
      apply H2. forwards*: cand_inversion H6.
      right. unfold not; intros nt; inverts* nt;try solve [inverts* H3].
      apply H0. forwards*: cand_inversion H6.
      apply H0. forwards*: cand_inversion H6.
      right. unfold not; intros nt; inverts* nt;try solve [inverts* H3].
      apply H0. forwards*: cand_inversion H6.
      apply H0. forwards*: cand_inversion H6.
    + split.
      forwards: IHA1 (t_rcd l B). forwards: IHA2 (t_rcd l B).
      inverts H. inverts H0. inverts H1. inverts H.
      left*. left*.
      inverts H. left*.
      right. unfold not; intros nt; inverts* nt. 
     
      forwards: IHA1 (t_rcd l B). forwards: IHA2 (t_rcd l B).
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


Lemma Typing_ord_chk: forall p1 p2 A,
 oord A ->
 nil ⊢ e_merge p1 p2 ⇐ A ->
 nil ⊢ p1 ⇐ A \/ nil ⊢ p2 ⇐ A.
Proof.
  introv ord Typ.
  inverts* Typ.
  -
  inverts* H.
  forwards*: csub_andl2 H0.
Qed.


Lemma Typing_rcd_chk: forall p1 p2 l A,
 nil ⊢ e_merge p1 p2 ⇐ t_rcd l A ->
 nil ⊢ p1 ⇐ t_rcd l A \/ nil ⊢ p2 ⇐ t_rcd l A.
Proof.
  introv Typ.
  inverts* Typ.
  -
  inverts* H.
  inverts* H0. 
Qed.



Lemma ddyn_decidable : forall A,
    ddyn A \/ ~ddyn A.
Proof.
  induction A; try solve[right; unfold not; intros nt; invert* nt]; 
  try solve[left*].
  - destruct IHA1.
    + left*.
    + destruct IHA2.
      * left*.
      * right;
        unfold not;
        intros nt;
        inverts* nt.
Qed.   


Lemma not_top_cs : forall A,
    not(csub A t_top) -> False.
Proof.
  introv H.
  exfalso; apply H; eauto.
Qed.



Lemma sz_one: forall A,
 size_typ A >= 1.
Proof.
  introv.
  inductions A; simpl in *; try solve[lia].
Qed.



Lemma const_sz: forall A,
  size_typ(const(A)) <= size_typ A.
Proof.
  introv.
  inductions A; simpl in *; try solve[lia].
  -
    forwards* h1: sz_one A1.
    forwards* h2: sz_one A2.
    lia.
  -
    forwards* h1: sz_one A.
    lia.
Qed.


Lemma const_well: forall A,
 ord A ->
 well (const(A)).
Proof.
  introv ord.
  inductions ord; simpl in *;eauto.
Qed.


Lemma csub_top_not_ord: forall A,
 csub t_top A ->
 not (ord A).
Proof.
  introv cs.
  inductions cs; try solve[unfold not; intros nt;inverts* nt];eauto.
Qed.



Lemma Cast_preservation_gen2: forall v' v A B n,
    size_exp v + size_typ A < n ->
    well A ->
    value v -> Typing nil v Chk B -> 
    Cast v A (r_e v') -> Typing nil v' Inf A.
Proof.
  introv sz Well Val Typ Red. gen v A B v'.
  inductions n; intros; try solve[lia].
  inductions Red; intros;try solve[inverts Typ]; auto.
  - (* f *)
    inverts Typ as h1; try solve[inverts Val as h2; inverts h2].
    +
    forwards h2: fprincipal_inf h1; auto.
    rewrite h2 in *.
    eapply Typ_anno; eauto.
  - (* u:dyn *)
    inverts Typ as h1. inverts h1 as h1. 
    inverts h1 as h1; try solve[inverts Val as h3; try solve[inverts h3]].
    inverts Val as h3; try solve[inverts h3].
    forwards hh1:gvalue_value h3.
    forwards* h2: IHn Red.
    simpl in *; lia.
  - (* rcd *)
    inverts Well. inverts Val as h1; try solve[inverts h1].
    inverts Typ as h3. inverts h3 as h3.
    forwards* h2: IHn Red. 
    simpl in *; lia.
  - (* vdyn *)
    inverts Typ as h1. inverts h1 as h1.
    eapply Typ_anno; auto.
  - (* s dyn *)
    inverts Typ as h1; try solve[inverts Val as h0;inverts h0].
    inverts H; simpl in *; try solve[inverts Red];
    try solve[inverts H0].
    + inverts* Red.
    + inverts* Red.
    + forwards h2: fvalue_ftype H0; auto.
      lets(t1&t2&h3): h2.
      rewrite h3 in *.
      simpl in *.
      inverts Red; try solve[inverts H0].
      eapply Typ_anno; eauto.
      eapply Typ_cs with (A := (t_arrow t_dyn t_dyn)); auto.
      eapply Typ_anno; eauto.
      forwards h4: principal_inf h1; auto.
      rewrite h3 in *; subst.
      eapply Typ_cs with (A := (t_arrow t1 t2)); auto.
    + inverts Red.
      inverts h1 as h1.
      forwards* h2: IHn H3.
      simpl in *; lia.
  - (* merge dyn *) 
    inverts Val as h1; try solve[inverts h1].
    inverts Typ as h2. inverts h2 as h3 h4.
    forwards h5: Typing_Chk h3; auto.
    forwards h6: Typing_Chk h4; auto.
    forwards h7: IHn h5 Red1 ; auto.
    simpl in *; lia.
    forwards h8: IHn h6 Red2 ; auto.
    simpl in *; lia.
    eapply Typ_anno; eauto.
  - (* v1 v2*)
    inverts Val as h1; try solve[inverts h1].
    inverts Typ as h2. inverts h2 as h3 h4.
    inverts H0.
    +
    forwards* h2: IHn Red1. 
    simpl in *; lia.
    +
    forwards* h2: IHn Red2. 
    simpl in *; lia.
    +
    forwards* h2: IHn Red1. 
    simpl in *; lia.
   - (* v *)
      inverts Well.
      inverts H.
      forwards h1: IHn Typ Red1; auto.
      simpl in *; lia.
      forwards h2: IHn Typ Red2; auto.
      simpl in *; lia.
Qed.



Lemma Cast_preservation2: forall v' v A B,
    well A ->
    value v -> Typing nil v Chk B -> 
    Cast v A (r_e v') -> Typing nil v' Inf A.
Proof.
  introv Well Val Typ Red.
  eapply Cast_preservation_gen2;eauto.
Qed.



Lemma ncs_and: forall A t1 t2,
 not(csub (t_and t1 t2) A) ->
 ord A ->
 not(csub t1 A) /\ not(csub t2 A).
Proof.
  introv cs ord.
  splits*.
Qed.



Lemma Cast_ncs: forall v A r,
  Cast v A r ->
  not(csub (principal_type v) A) ->
   r = (r_blame err_b).
Proof.
  introv red ncs.
  inductions red; simpl in *; eauto;
  try solve[exfalso; apply ncs; eauto].
  -
  forwards*: Cast_csub red.
  exfalso; apply ncs; simpl; eauto.
  -
  forwards* h1: ncs_and ncs.
  forwards* h2: IHred1.
  forwards* h3: IHred2.
  subst; inverts* H0.
  -
  inverts* H; try solve[
    forwards*: Cast_csub red1;
  forwards*: Cast_csub red2;
  exfalso; apply ncs; eauto
  ];
  try solve[
    forwards*: Cast_csub_a red1;
    forwards*: Cast_csub red2;
    exfalso; apply ncs; eauto
  ].
Qed.



Lemma svalue_value: forall u,
 svalue u ->
 value u.
Proof.
  introv val.
  inductions val; eauto.
Qed.


Lemma svalue_well: forall u,
 svalue u ->
 well (const (principal_type u)).
Proof.
  introv val.
  inductions val; simpl in *; eauto.
  forwards* h1: fvalue_ftype H.
  lets(t1&t2&h2): h1.
  rewrite h2 in *; simpl in *;auto.
Qed.


Lemma Cast_unique: forall v r1 r2 (A: typ),
    value v -> (exists B, Typing nil v Chk B) -> Cast v A r1 -> Cast v A r2 -> r1 = r2.
Proof.
  introv Val H R1 R2.
  gen r2.
  lets R1': R1.
  inductions R1; introv R2;
    try solve [inverts~ R2; try solve[inverts H2];try solve_false;
    try solve[forwards* h1: not_top_cs; inverts* h1] ];
    try solve [forwards*:Cast_top_normal R2];
    eauto.
  - (* f a->b*)
    inverts* R2; try solve_false; simpl in *;
    try solve[inverts* H3];
    try solve[inverts* H1].
  - (* u :dyn a *)
    inverts* R2; try solve_false; simpl in *;
    try solve[inverts* H1];
    try solve[inverts* H0];
    try solve[inverts H0 as hh1;inverts hh1];
    try solve[inverts* H2].
    + 
      inverts H as typ.
      inverts typ as typ.
      inverts typ as typ.
      inverts Val as h1; try solve[inverts h1].
      forwards hh1: gvalue_value h1.
      forwards* h2: IHR1 R1 H3.
  - (* rcd *)
    inverts* R2; try solve_false; simpl in *;
    try solve[inverts* H1].
    +
    inverts H as h1.
    inverts h1 as h1.
    inverts h1 as h1.
    inverts Val as h3; try solve[inverts h3].
    forwards* h2: IHR1 H4.
    congruence.
    +
    inverts H as h1.
    inverts h1 as h1.
    inverts h1 as h1.
    inverts Val as h3; try solve[inverts h3].
    forwards* h2: IHR1 H4.
    congruence.
    +
    forwards* h1: Cast_csub R1.
    exfalso; apply H1; auto.
  - (* rcd *)
    inverts* R2; try solve_false; simpl in *;
    try solve[inverts* H1].
    +
    inverts H as h1.
    inverts h1 as h1.
    inverts h1 as h1.
    inverts Val as h3; try solve[inverts h3].
    forwards* h2: IHR1 H4.
    congruence.
    +
    inverts H as h1.
    inverts h1 as h1.
    inverts h1 as h1.
    inverts Val as h3; try solve[inverts h3].
    forwards* h2: IHR1 H4.
    +
    destruct b; auto.
    forwards* h1: Cast_csub_a R1.
    exfalso; apply H1; auto.
  - (*v:dyn dyn *)
    inverts* R2; try solve_false; simpl in *;
    try solve[inverts H1 as h1; inverts h1];
    try solve[inverts* H3];
    try solve[inverts* H2].
  - (* s ->dyn *)
    inverts* R2; try solve[inverts H0 as h1; inverts h1];
    try solve[inverts H2];
    try solve[inverts H1];
    try solve[exfalso; apply H2; auto].
    forwards* h1: IHR1 H2.
    inverts* h1.
  -
    inverts H as h1.
    inverts h1 as h1.
    inverts h1 as h1.
    inverts Val as h3; try solve[inverts h3].
    inverts* R2; try solve[inverts H as h4; inverts h4];
    try solve[inverts H];
    try solve[inverts H3];
    try solve[exfalso; apply H2; auto].
    forwards* h5: IHR1_1 H3.
    forwards* h6: IHR1_2 H7.
    congruence.
  - (* not cs *)
    lets R2': R2.
    inverts* R2;
    try solve[exfalso; apply H1; auto].
    +
    forwards*: Cast_csub H2.
    exfalso; apply H1; simpl;auto.
    +
    forwards*: Cast_ncs H2.
    simpl in *; eauto.
    +
    simpl in *.
    forwards*: Cast_ncs H3.
    forwards*: Cast_ncs H4.
    subst*.
    inverts* H5.
    +
    simpl in *.
    forwards*: Cast_ncs R2'.
  - (* merge *)
    lets R2': R2.
    inverts* R2; try solve_false; simpl in *;
    try solve[inverts* H0];
    try solve[inverts* H3].
    +
    forwards*: Cast_ncs R1'.
    +
    inverts H as h4.
    inverts h4 as h4.
    inverts h4 as h4 h5.
    inverts Val as h1; try solve[inverts h1].
    forwards* h2: IHR1_1 H5.
    forwards* h3: IHR1_2 H6.
    subst.
    forwards*: joina_uniq H1 H9.
  - (* and *)
    inverts~ R2;try solve_false.
    +
    forwards*: Cast_ncs R1'.
    +
    forwards*: IHR1_1 R1_1 H3.
    forwards*: IHR1_2 R1_2 H5.
    subst.
    forwards*: joint_uniq H0 H7.
  - (* bot *)
    inverts~ R2;try solve_false;
    try solve[inverts H2];
    try solve[inverts H1].
Qed.



Lemma static_not_ddyn: forall A,
 static A -> not(ddyn A) .
Proof.
  introv sta.
  inductions sta; try solve[unfold not; intros nt; inverts* nt].
Qed.



Lemma ddyn_not_static: forall A,
 ddyn A -> not(static A) .
Proof.
  introv sta.
  inductions sta; try solve[unfold not; intros nt; inverts* nt].
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


Lemma typin_inversion: forall A1 A2 A,
 typin (t_and A1 A2) A ->
 typin A1 A /\ typin A2 A.
Proof.
  introv tin.
  inductions tin; eauto.
  forwards*: IHtin. 
  forwards*: IHtin. 
Qed.


Lemma sfill_eq: forall E0 e0 E e1 r1 r2,
  fill E0 e0 = fill E e1 ->
  step e0 r1 ->
  step e1 r2 ->
  wellformed E ->
  wellformed E0 ->
  E = E0 /\ e0 = e1.
Proof.
  introv eq red1 red2 wf1 wf2. gen E e0 e1 r1 r2.
  inductions E0; unfold fill in *;  intros;
  try solve[inductions E; unfold fill in *; inverts* eq];
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf1;
  forwards*: step_not_value red1];
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf2;
  forwards*: step_not_value red2].
  -
    inductions E; unfold fill in *; inverts* eq;
    inverts wf1;
    forwards*: step_not_abs red1.
  -
    inductions E; unfold fill in *; inverts* eq;
    inverts wf2;
    forwards*: step_not_abs red2.
Qed.



Lemma oord_ndyn: forall A,
 oord A ->
 not(ddyn A).
Proof.
  introv ord.
  inductions ord; eauto;
  try solve[unfold not; intros nt;
  inverts* nt].
Qed.



Theorem step_unique_chk: forall A e r1 r2,
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
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_fix Red1];
    try solve[destruct E; unfold fill in H1; inverts* H1];
    try solve[
      destruct E; unfold fill in *; inverts* H0;
      try solve[forwards*: step_not_value Red1];
      try solve[
      forwards*: step_not_abs Red1];
      try solve[inverts H]
    ].
    + 
      forwards*: sfill_eq H0.
      destruct H3. subst.
      forwards*: fill_chk Typ. inverts H3.
      destruct E0; unfold fill in H4; inverts H4;
      forwards*: IHRed1 Red1 H2; congruence.
    + 
      forwards*: sfill_eq H0.
      destruct H3. subst. 
      forwards*: fill_chk Typ. inverts H3.
      destruct E0; unfold fill in H4; inverts H4;
      forwards*: IHRed1 Red1; congruence.
  -  (* fill E e -> blame *)
    inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: step_not_value Red1;
    forwards*: step_not_value Red1];
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
      forwards*: sfill_eq H0.
      destruct H3. subst. 
      forwards*: fill_chk Typ. inverts H3.
      destruct E0; unfold fill in H4; inverts H4; 
      forwards*: IHRed1 Red1; congruence.
    +
      forwards*: sfill_eq H0.
      destruct H3. subst. 
      forwards*: fill_chk Typ. inverts H3.
      destruct E0; unfold fill in H4; inverts H4; 
      forwards*: IHRed1 Red1; congruence.
  - (* \x.e:a1->b1 v*)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H1;
    try solve[
    forwards*: step_not_abs H3];
    try solve[forwards*: step_not_value H3]]
    .
  - (* f:a1->b1 v2  *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H0;
    try solve[
    forwards*: step_not_abs H2];
    try solve[forwards*: step_not_value H2];
    try solve[inverts* H1]].
  - (* dyn  *)
    inverts* Red2;try solve[destruct E; unfold fill in *; inverts* H0;
    try solve[forwards*: step_not_value H2];
    try solve[inverts* H1]].
  - (* v:a *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H2;
    forwards*: step_not_value H4];
    try solve[inverts H as h0;inverts h0].
    +
    inverts Typ as h2.
    inverts h2 as h2.
    forwards* h1: Cast_unique H0 H5.
  - (* v.l -> v *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H2;
    forwards*: step_not_value H4].
    +
      forwards* h1: get_ty_uniq H0 H5.
      subst.
      inverts Typ as h2.
      inverts h2 as h2.
      forwards* h1: Cast_unique H1 H7.
      congruence.
    +
      forwards* h1: get_ty_uniq H0 H5.
      subst.
      inverts Typ as h2.
      inverts h2 as h2.
      forwards* h1: Cast_unique H1 H7.
      congruence.
  - (* v.l -> blame *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H2;
    forwards*: step_not_value H4].
    +
      forwards* h1: get_ty_uniq H0 H5.
      subst.
      inverts Typ as h2.
      inverts h2 as h2.
      forwards* h1: Cast_unique H1 H7.
      congruence.
    +
      forwards* h1: get_ty_uniq H0 H5.
      subst.
      inverts Typ as h2.
      inverts h2 as h2.
      forwards* h1: Cast_unique H1 H7.
  - (* fix*)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H0;
    forwards*: step_not_value H2;
    forwards*: step_not_fix H2];
    try solve[inverts H2 as h0;inverts h0].
  -
     inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H0;
    forwards*: step_not_abs H2];
    try solve[inverts H3 as h0;inverts h0];
    try solve[inverts H2 as h0;inverts h0].
Qed.


Theorem step_unique: forall dir A e r1 r2,
   Typing nil e dir A -> step e r1 -> step e r2 -> r1 = r2.
Proof.
  introv Typ Red1 Red2.
  destruct dir.
  -
    forwards*: Typ_cs Typ.
    forwards*: step_unique_chk Red1.
  -
    forwards*: step_unique_chk Red1.
Qed.


Lemma sfill_eq_cbn: forall E0 e0 E e1 r1 r2,
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
    try solve[destruct E; unfold filln in H0; inverts* H0;
    forwards*: nstep_not_value Red1;
    forwards*: nstep_not_value Red1];
    try solve[destruct E; unfold filln in H1; inverts* H1];
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
      forwards*: sfill_eq_cbn H0.
      destruct H3. subst.
      forwards*: filln_chk Typ. inverts H3.
      destruct E0; unfold fill in H4; inverts H4;
      forwards*: IHRed1 Red1 H2; congruence.
    + 
      forwards*: sfill_eq_cbn H0.
      destruct H3. subst. 
      forwards*: filln_chk Typ. inverts H3.
      destruct E0; unfold fill in H4; inverts H4;
      forwards*: IHRed1 Red1; congruence.  
  -  (* fill E e -> blame *)
    inverts* Red2;
    try solve[destruct E; unfold fill in H0; inverts* H0;
    forwards*: nstep_not_value Red1;
    forwards*: nstep_not_value Red1];
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
      forwards*: sfill_eq_cbn H0.
      destruct H3. subst. 
      forwards*: filln_chk Typ. inverts H3.
      destruct E0; unfold fill in H4; inverts H4; 
      forwards*: IHRed1 Red1; congruence.
    +
      forwards*: sfill_eq_cbn H0.
      destruct H3. subst. 
      forwards*: filln_chk Typ. inverts H3.
      destruct E0; unfold fill in H4; inverts H4; 
      forwards*: IHRed1 Red1; congruence.
  - (* \x.e:a1->b1 v*)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H1;
    try solve[
    forwards*: nstep_not_abs H3];
    try solve[forwards*: nstep_not_value H3]]
    .
  - (* f:a1->b1 v2  *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H1;
    forwards*: nstep_not_value H3];
    try solve[inverts* H2].
  - (* dyn  *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H1;
    forwards*: nstep_not_value H3];
    try solve[inverts* H2].
  - (* v:a *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H2;
    forwards*: nstep_not_value H4]; 
    try solve[inverts H as h0; inverts h0].
    inverts Typ as h2.
    inverts h2 as h2.
    forwards* h1: Cast_unique H0 H5.
  - (* v.l -> v *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H2;
    forwards*: nstep_not_value H4].
    +
      forwards* h1: get_ty_uniq H0 H5.
      subst.
      inverts Typ as h2.
      inverts h2 as h2.
      forwards* h1: Cast_unique H1 H7.
      congruence.
    +
      forwards* h1: get_ty_uniq H0 H5.
      subst.
      inverts Typ as h2.
      inverts h2 as h2.
      forwards* h1: Cast_unique H1 H7.
      congruence.
  - (* v.l -> blame *)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H2;
    forwards*: nstep_not_value H4].
    +
      forwards* h1: get_ty_uniq H0 H5.
      subst.
      inverts Typ as h2.
      inverts h2 as h2.
      forwards* h1: Cast_unique H1 H7.
      congruence.
    +
      forwards* h1: get_ty_uniq H0 H5.
      subst.
      inverts Typ as h2.
      inverts h2 as h2.
      forwards* h1: Cast_unique H1 H7.
  - (* fix*)
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H0;
    forwards*: nstep_not_value H2;
    forwards*: nstep_not_fix H2];
    try solve[inverts H2 as h0;inverts h0].
  -
    inverts* Red2;
    try solve[destruct E; unfold fill in *; inverts* H0;
    forwards*: nstep_not_abs H2];
    try solve[inverts H2 as h0 ;inverts h0].
Qed.