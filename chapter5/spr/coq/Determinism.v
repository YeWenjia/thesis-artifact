Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        Definitions
        Lemmas
        Infrastructure
        Soundness.



(* Lemma ptype_uniq: forall mu u A B,
 sto_ok mu ->
 pvalue u -> ptype mu u A -> ptype mu u B -> A = B.
Proof.
  introv ok pval ptyp1 ptyp2.
  inductions pval; try solve[inverts* ptyp1; inverts* ptyp2].
Qed.


Lemma TypedReduce_unique: forall P v mu r1 r2 (A: typ),
    sto_ok mu -> value v -> (exists B, typing nil P v Inf B) -> TypedReduce (v, mu) A r1 -> TypedReduce (v, mu) A r2 -> r1 = r2.
Proof.
  introv ok Val H R1 R2.
  gen r2.
  lets R1': R1.
  inductions R1; introv R2;
    try solve [inverts~ R2].
  -
  inverts~ R2.
  forwards*: ptype_uniq H0 H9. subst*.
  -
  inverts~ R2.
  forwards*: ptype_uniq H0 H9. subst*.
Qed. *)





Lemma fill_eq: forall mu E0 e0 E e1 r1 r2 mu1 mu2,
  fill E0 e0 = fill E e1 ->
  step (e0, mu) (r1,mu1) ->
  step (e1, mu) (r2,mu2) ->
  wellformed E ->
  wellformed E0 ->
  E = E0 /\ e0 = e1.
Proof.
  introv eq red1 red2 wf1 wf2. gen mu mu1 mu2 E e0 e1 r1 r2.
  inductions E0; unfold fill in *;  intros;
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf1;
  forwards*: step_not_value red1];
  try solve[inductions E; unfold fill in *; inverts* eq];
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf2;
  forwards*: step_not_value red2].
Qed.


Lemma typing_chk: forall E e P A,
 typing E P e Inf A ->
 typing E P e Chk A.
Proof.
  introv typ.
  eapply typ_eq; eauto.
Qed.


Lemma fill_chk: forall F e dir P A,
 typing empty P (fill F e) dir A ->
 exists B, typing empty P e Chk B.
Proof.
  introv typ.
  destruct F; unfold fill in *;inverts* typ; try solve[inverts* H].
Qed.



Theorem step_unique: forall P mu A e r1 r2,
   P |== mu -> typing nil P e Chk A -> step (e, mu) r1 -> step (e, mu) r2 -> r1 = r2.
Proof.
  introv well Typ Red1.
  gen P A r2.
  lets Red1' : Red1.
  inductions Red1; 
    introv well Typ Red2.
  - (* fill *)
    inverts* Red2; 
    try solve[destruct F; unfold fill in H0; inverts* H0];
    try solve[
    forwards*: typing_regular Typ;destructs~ H1;destruct F; unfold fill in H0; inverts* H0;
    inverts* H4;
    inverts* H8;
    forwards: step_not_value Red1; auto; inverts H0];
    try solve[
    forwards*: typing_regular Typ;destructs~ H1;destruct F; unfold fill in H0; inverts* H0;
    inverts* H2;
    inverts* H6;
    forwards: step_not_value Red1; auto; inverts H0];
    try solve[ destruct F; unfold fill in *; inverts* H0;
    forwards: step_not_value Red1; auto; inverts* H0];
    try solve[destruct F; unfold fill in H5; inverts* H5].
    + forwards*: fill_eq H0.
      destruct H1. subst. inverts Typ.
      forwards*: fill_chk H1. inverts* H3.
      forwards*: IHRed1 Red1 H4. congruence.
  - 
    inverts* Red2; 
    try solve[destruct F; unfold fill in H2; inverts* H2;
    forwards: step_not_value H6; auto; inverts H2];
    try solve[inverts H7]. 
  -
   inverts* Red2; 
    try solve[destruct F; unfold fill in H1; inverts* H1;
    forwards: step_not_value H5; auto; inverts H1];
    try solve[inverts H7]. 
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H0; inverts H0];
    try solve[destruct F; unfold fill in *; inverts H0];
    try solve[inverts* H8];
    try solve[inverts* H8];
    try solve[inverts* H3];
    try solve[
      destruct F; unfold fill in *; inverts H0;
      forwards*: step_not_value H4; auto; inverts H; auto].
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H0; inverts H0];
    try solve[destruct F; unfold fill in *; inverts H0];
    try solve[inverts* H8];
    try solve[inverts* H8];
    try solve[inverts* H3];
    try solve[
      destruct F; unfold fill in *; inverts H1;
      forwards*: step_not_value H5; auto; inverts H; auto].
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H0; inverts H0];
    try solve[destruct F; unfold fill in *; inverts H0];
    try solve[inverts* H4];
    try solve[
      destruct F; unfold fill in *; inverts H1;
      forwards: step_not_value H5; auto; inverts H1].
  -
    inverts* Red2; 
    try solve[destruct F; unfold fill in H0; inverts H0];
    try solve[destruct F; unfold fill in *; inverts H0];
    try solve[inverts* H3];
    try solve[
      destruct F; unfold fill in *; inverts H0;
      forwards: step_not_value H4; auto; inverts H0].
Qed.

  


