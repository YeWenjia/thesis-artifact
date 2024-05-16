Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               Typing
               Subtyping_inversion
               Lia.


(* TypedReduces *)
Lemma Cast_top_normal : forall (p p': dexp),
    Cast p dt_top p' -> p' = de_top.
Proof.
  intros p p' H.
  remember dt_top.
  inductions H;
    try solve [inverts* Heqd];
    try solve[subst*; exfalso; apply H; eauto];
    try solve[inverts H0].
Qed.


Lemma Cast_ord_toplike_normal : forall (v v': dexp) (A : dtyp),
    oord A -> topLike A -> Cast v A v' -> v' = de_top.
Proof.
  introv H1 H2 Red.
  induction~ Red; try solve_false.
  inverts* H2. inverts* H2.
Qed.


Lemma Cast_top_normal2 : forall (p p': dexp) A,
    topLike A ->
    Cast p A p' ->  topLike (principal_type p').
Proof.
  introv tlike H.
  inductions H;simpl in *;
    try solve[subst*; exfalso; apply H; eauto];
    try solve[inverts* tlike].
Qed.


Lemma Cast_sub: forall p p' A,
 Cast p A p' ->
 sub (principal_type p) A.
Proof.
  introv red.
  inductions red; simpl in *;try solve[inverts* pval; try solve[ inverts H1];
  simpl; eauto];eauto.
Qed.


Lemma Cast_toplike_uniq :
  forall A, topLike A ->
            forall (p1 p2 : dexp) p1' p2', Cast p1 A p1' -> Cast p2 A p2' -> p1' = p2'.
Proof.
  intros A Typ.
  induction Typ;
    introv Red1 Red2.
  - apply Cast_top_normal in Red1.
    apply Cast_top_normal in Red2.
    subst*.
  - inverts~ Red1; try solve_false;
      inverts~ Red2; try solve_false.
    forwards: IHTyp1 H2 H3.
    forwards: IHTyp2 H4 H6.
    subst*.
Qed.

Lemma fvalue_ftype: forall f, 
 fvalue f ->
 exists t1 t2, principal_type f = (dt_arrow t1 t2).
Proof.
  introv fval.
  inverts* fval; simpl in *; eauto.
Qed.


Lemma Cast_value: forall v A v',
 value v ->
 Cast v A v' ->
 value v'.
Proof.
  introv Val Red.
  inductions Red; try solve[inverts Val as h1; try solve[inverts* h1];
  try solve[exfalso; apply H0; auto]; auto];eauto.
Qed.