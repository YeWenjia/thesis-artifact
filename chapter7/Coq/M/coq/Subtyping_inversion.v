Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import syntax_ott
               rules_inf.

Ltac solve_false := try intro; solve [false; eauto with falseHd].


Lemma ord_and_inv : forall A B,
    ord (dt_and A B) -> False.
Proof.
  introv H.
  inverts H.
Qed.

Lemma oord_and_inv : forall A B,
    oord (dt_and A B) -> False.
Proof.
  introv H.
  inverts H.
Qed.

Lemma topLike_int_inv :
    topLike dt_int -> False.
Proof.
  introv H.
  inverts H.
Qed.

Lemma topLike_arrow_inv : forall A B,
    topLike (dt_arrow A B) -> topLike B.
Proof.
  introv H.
  inverts~ H.
Qed.

Hint Resolve ord_and_inv oord_and_inv topLike_int_inv topLike_arrow_inv : falseHd.

Lemma sub_inversion_arrow : forall A1 A2 B1 B2,
    sub (dt_arrow A1 A2) (dt_arrow B1 B2) -> sub dt_top B2 \/ (sub B1 A1 /\ sub A2 B2).
Proof.
  intros.
  inverts* H.
Qed.

Lemma sub_inversion_andl_arrr : forall A1 A2 B1 B2,
    sub (dt_and A1 A2) (dt_arrow B1 B2) -> sub A1 (dt_arrow B1 B2) \/ sub A2 (dt_arrow B1 B2).
Proof.
  intros.
  inverts* H.
Qed.

Lemma sub_reflexivity : forall A,
    sub A A.
Proof.
  intros A.
  induction* A.
Qed.


Require Import Program.Equality.

Hint Constructors sub : core.

Lemma dand_inversion : forall A B C,
    sub A (dt_and B C) -> sub A B /\ sub A C.
Proof.
  intros A B C H.
  dependent induction H; eauto.
  lets*: IHsub B C.
  lets*: IHsub B C.
Qed.


Lemma sub_andl : forall A1 A2 C,
    ord C -> sub (dt_and A1 A2) C -> 
    sub A1 C \/ sub A2 C.
Proof.
  intros.
  inverts* H0.
  inverts H.
Qed.


Lemma sub_andl2 : forall A1 A2 C,
    oord C -> sub (dt_and A1 A2) C -> 
    sub A1 C \/ sub A2 C.
Proof.
  intros.
  inverts* H0.
  inverts H.
Qed. 


Lemma sub_transtivity : forall B A,
      sub A B -> forall C, sub B C -> sub A C.
Proof.
  induction B;
    intros;
    eauto;
    try solve [dependent induction H;
               eauto].
  - dependent induction H; eauto.
    dependent induction H0; eauto.
  - dependent induction H; eauto.
    dependent induction H1; eauto.
  - dependent induction H; eauto.
    clear IHsub1 IHsub2.
    dependent induction H1; eauto.
  - dependent induction H; eauto.
    dependent induction H0; eauto.
Qed.
    

Ltac auto_sub :=
  try match goal with
      | [ |- sub ?A ?A ] => apply sub_reflexivity 
      | [ H: sub ?A (dt_and ?B ?C) |- sub ?A ?B ] => (
        eapply sub_transtivity;
        try apply H;
        try apply DS_andl1;
        try apply sub_reflexivity)
      | [ H: sub ?A (dt_and ?B ?C) |- sub ?A ?C ] => (
        try eapply sub_transtivity;
        try apply H;
        try apply DS_andl2;
        try apply sub_reflexivity)
      | [ H: sub (dt_arrow _ _) (dt_arrow _ _) |- sub _ _ ] => (apply sub_inversion_arrow in H; destruct H; auto_sub)
      | [ H1: sub ?A ?B, H2: sub ?B ?C |- sub ?A ?C ] => forwards*: sub_transtivity H1 H2
      | [ H1: sub ?A ?B, H2: sub ?B ?C |- sub ?A ?C ] => forwards*: sub_transtivity H1 H2
    | |- _ => try constructor*
      end.


(* topLike *)
Lemma topLike_super_top: forall A,
    topLike A <-> sub dt_top A.
Proof.
  intro A.
  split.
  - intro H.
    inductions H; eauto.
  - intro H.
    induction A;
      try solve [inverts* H].
Qed.


Lemma sub_inversion_toparr : forall B C,
    sub dt_top B -> sub B C -> sub dt_top C.
Proof.
  intros B C S1 S2.
  gen C.
  remember (dt_top).
  induction S1;
    inverts* Heqd;
    intros C S2.
  - inductions S2; try solve[inverts* H0]; eauto.
Qed.

Lemma topLike_decidable : forall A,
    topLike A \/ ~topLike A.
Proof.
  inductions A.
  - right.
    unfold not.
    intros H.
    inversion H.
  - left*.
  - right.
    unfold not.
    intros H.
    inversion H.
  - right*.
    unfold not; intros nt; inverts nt. 
  - destruct IHA1.
    + destruct IHA2.
      * left*.
      * right.
        unfold not.
        intros H1.
        inverts H1.
        auto.
    + right.
      unfold not.
      intros H0.
      inverts H0.
      auto.
  - right*.
    unfold not;intros. inverts* H.
Qed.   
        
(* disjoint *)


Lemma ord_oord: forall C,
 ord C -> oord C.
Proof.
  introv ord.
  inductions ord; eauto.
Qed.

Lemma oord_ord: forall C,
 oord C -> ord C \/ topLike C.
Proof.
  introv oord.
  inductions oord; eauto.
Qed.

Lemma ord_not_toplike: forall C,
 ord C -> not(topLike C).
Proof.
  introv ord.
  inductions ord; unfold not;intros nt;inverts* nt;eauto.
Qed.


(* 
Lemma disjointSpec_eqv: forall A B,
    disjointSpec A B -> disjointSpecc A B.
Proof.
  intros A B.
  unfold disjointSpec.
  intros.
    unfold disjointSpecc; intros.
    unfold not; intros nt; inverts nt.
    forwards*: H H1 H2.
    forwards*: ord_not_toplike H0.
Qed. *)


Lemma topLike_super_toplc: forall B A,
    oord A -> topLike B -> topLike A <-> sub B A.
Proof.
  introv sta tl.
  split.
  - intro H.
    inductions H; try solve[inverts* tl]; try solve[inverts* sta];eauto.
  - intro H.
    inductions H; try solve[inverts* tl]; try solve[inverts* sta];eauto.
Qed.


Lemma topLike_super_toplc2: forall B A,
    topLike B -> topLike A <-> sub B A.
Proof.
  introv tl.
  split.
  - intro H.
    inductions H; try solve[inverts* tl]; try solve[inverts* sta];eauto.
  - intro H.
    inductions H; try solve[inverts* tl]; try solve[inverts* sta];eauto.
Qed.

Lemma disjoint_eqv: forall A B,
    disjointSpec A B <-> disjoint A B.
Proof.
  intros A B.
  unfold disjointSpec.
  split.
  - gen B.
    inductions A;
      introv H;
      inductions B;
      try solve [constructor*].
    + (* int int *)
      assert (~ sub dt_top  dt_int). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards*: (H dt_int).
    + (* int bot *)
      assert (~ sub dt_top  dt_int). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards*: (H dt_int).
    + (* bot int *)
      assert (~ sub dt_top  dt_int). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards*: (H dt_int).
    + (* bot bot *)
      assert (~ sub dt_top  dt_int). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards*: (H dt_int).
    + assert (~ sub dt_top  (dt_arrow dt_bot dt_top)). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards*: (H (dt_arrow dt_bot dt_top)).
    + assert (~ sub dt_top (dt_rcd l dt_top)). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards*: (H  (dt_rcd l dt_top)).
    + assert (~ sub dt_top (dt_arrow dt_bot dt_top)). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards*: (H (dt_arrow dt_bot dt_top)).
    + assert (~ sub dt_top (dt_arrow dt_bot dt_top)). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards*: (H (dt_arrow dt_bot dt_top)).
    + assert (~ sub dt_top (dt_rcd l dt_top)). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards*: (H  (dt_rcd l dt_top)).
    + destruct(l == l0); eauto. inverts e.
      forwards*: H (dt_rcd l0 dt_top). inverts H0.
  - 
    intros H C S1 S2.
    gen B C.
    induction* A;
      intros B H;
      [ induction* B | inductions B | skip | skip | induction* B  ];
      intros C S1 S2;
      try solve [inverts H; inverts* H0].
    + (* int arr *)
      induction* C;
      inverts S1;
      inverts* S2; try solve[inverts* S].
    + (* int and *)
      induction* C;
      inverts H;
      inverts* S1;  
      try solve[forwards*: topLike_super_toplc2 H0];
      try solve[forwards*: sub_andl S2];
      try solve[forwards*: dand_inversion S2];
      try solve[inverts* H0].
    + (* int rcd *)
      induction* C;
        inverts S1;
        inverts* S2.
    + (* bot top *)
      induction* C;
      inverts S1;
      inverts* S2; try solve[inverts* S].
    + (* bot and *)
      induction* C;
      inverts H;
      inverts* S1;  
      try solve[inverts* S2];
      try solve[forwards*: dand_inversion S2];
      try solve[inverts* H0].
    + (* rcd int *)
      induction* C;
        inverts S1;
        inverts* S2.
    + (* rcd arr *)
      induction* C;
        inverts S1;
        inverts* S2.
    + (* arr and *)
        induction* C;
        inverts H;
        inverts* S1;  
        try solve[forwards*: topLike_super_toplc2 H0];
        try solve[forwards*: sub_andl S2];
        try solve[forwards*: dand_inversion S2];
        try solve[inverts* H0].
    + (* rcd rcd*)
      induction* C;
      inverts H;
      inverts* S1; 
      try solve[inverts* H0];
      try solve[inverts* S2].
Qed. 


Lemma disjoint_and: forall A B C,
     disjointSpec (dt_and B C) A <-> disjointSpec B A /\ disjointSpec C A.
Proof.
  introv.
  split;
  intro H.
  - apply disjoint_eqv in H; eauto.  
    split;
      apply disjoint_eqv; auto;
      inductions A;
      inverts* H; try solve[inverts* H0].
  - destruct H.
    apply disjoint_eqv in H; eauto.
    apply disjoint_eqv in H0; eauto.
    apply disjoint_eqv; eauto.
Qed.


Lemma disjoint_and2: forall A B C,
    disjoint (dt_and B C) A <-> disjoint B A /\ disjoint C A.
Proof.
  split;
  intro H.
  - 
    split;
      inductions A;
      inverts* H; inverts* H0. 
  - destruct H.
    inductions A; eauto.
Qed. 


Lemma disjoint_symmetric: forall A B,
    disjointSpec A B -> disjointSpec B A.
Proof.
  intros A B H.
  unfold disjointSpec in H.
  unfold disjointSpec.
  intros C H0 H1.
  forwards*: H H1 H0.
Qed.

Lemma disjoint_symmetric2: forall A B,
    disjoint A B -> disjoint B A.
Proof.
  intros A B H.
  apply disjoint_eqv in H; auto.
  apply disjoint_eqv; auto.
  unfold disjointSpec in H.
  unfold disjointSpec.
  intros C H0 H1.
  forwards*: H H1 H0.
Qed. 


(* Lemma disjointSpec_disjointSpecc: forall A B,
    disjointSpec A B <-> disjointSpecc A B.
Proof.
  intros A B.
  unfold disjointSpec.
  split.
  - intros.
    unfold disjointSpecc; intros.
    unfold not; intros nt; inverts nt.
    forwards*: H H1 H2.
    forwards*: ord_not_toplike H0.
  - 
    unfold disjointSpecc in *.
    intros.
    inductions C; eauto.
    forwards*: H dt_int.
    forwards*: H dt_bot.
    forwards*: H (dt_arrow C1 C2).
    forwards*: dand_inversion H0.
    forwards*: dand_inversion H1.
    forwards*: H (dt_rcd l C).
Qed. *)

(* 
Lemma disjointSpecc_common: forall A B,
    disjointSpecc A B <-> not(co A B).
Proof.
  intros A B.
  rewrite <- disjointSpec_disjointSpecc.
  unfold disjointSpec.
  split.
  - gen B.
    inductions A;
      introv H;
      inductions B;
      try solve [unfold not; intros nt; inverts* nt].
    + forwards*: H dt_int. inverts* H0.
    + forwards*: H dt_int. inverts* H0.
    + forwards*: H dt_int. inverts* H0.
    + forwards*: H dt_int. inverts* H0.
    + forwards*: H (dt_arrow dt_bot dt_top). inverts* H0.
    + forwards*: H (dt_rcd l dt_top). inverts* H0.
    + forwards*: H (dt_arrow dt_bot dt_top). inverts* H0.
    + forwards*: H (dt_arrow dt_bot dt_top). inverts* H0.
    + forwards*: H (dt_rcd l dt_top). inverts* H0.
    + destruct(l == l0).
      inverts e.
      forwards*: H (dt_rcd l0 dt_top). inverts* H0.
      unfold not; intros nt; inverts* nt. 
  - intros.  gen B.
    inductions H0; intros;
    try solve[inductions H1; try solve[inverts* H0];
    try solve[ inductions H1; try solve[exfalso; apply H; eauto]; eauto];
    try solve[exfalso; apply H; eauto]];eauto.
    + inductions H1; try solve[exfalso; apply H; eauto]; eauto.
    +
      forwards*: dand_inversion H1.
Qed. *)


Lemma co_and_lem: forall A B C,
    co (dt_and B C) A <-> co B A \/ co C A.
Proof.
  split;
  intro H.
  - 
      inductions A;
      try solve[
      inverts* H; inverts* H0].
      inverts* H.
      forwards* h1:IHA1.
      forwards* h1:IHA2.
  - inverts* H.
Qed. 



Lemma co_andl_lem: forall A B C,
    co  A (dt_and B C) -> co A B  \/ co A C .
Proof.
  introv H.
      inductions A;
      try solve[
      inverts* H; inverts* H0].
      inverts* H.
      forwards* h1:IHA1.
      forwards* h1:IHA2.
Qed. 


Lemma disjoint_eqv2: forall A B,
    not(co A B) <-> disjoint A B.
Proof.
  intros A B.
  split.
  - gen B.
    inductions A;
      introv H;
      inductions B;
      try solve [constructor*];
      try solve[exfalso; apply H; eauto].
    + destruct(l == l0); eauto. inverts e.
      exfalso; apply H; auto. 
  - 
    intros Dis.
    unfold not;intros 
    coh.
    inductions Dis; simpl in *; try solve[inverts* coh];
    try solve[
    inductions B; simpl in *; 
    try solve[inverts* coh];eauto].
    +
    inductions A; simpl in *; 
    try solve[inverts* coh];eauto.
    +
    rewrite co_and_lem in coh.
    inverts* coh.
    +
    forwards* h1:co_andl_lem coh.
Qed. 
  


(* disjoint principal types *)
Lemma disjoint_domain_type: forall A B C B',
    disjointSpec (dt_arrow B C) A -> disjointSpec (dt_arrow B' C) A.
Proof.
  intros A B C B' H.
  apply disjoint_eqv in H; auto. 
  apply disjoint_eqv; auto.
  inductions A;
    inverts* H; inverts* H0. 
Qed.





 