Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import syntax_ott
               rules_inf.
Require Import Lia.

Ltac solve_false := try intro; solve [false; eauto with falseHd].


Lemma ord_and_inv : forall A B,
    ord (t_and A B) -> False.
Proof.
  introv H.
  inverts H.
Qed.

Lemma oord_and_inv : forall A B,
    oord (t_and A B) -> False.
Proof.
  introv H.
  inverts H.
Qed.

Lemma toplike_int_inv :
    topLike t_int -> False.
Proof.
  introv H.
  inverts H.
Qed.

Lemma toplike_arrow_inv : forall A B,
    topLike (t_arrow A B) -> topLike B.
Proof.
  introv H.
  inverts~ H.
Qed.



Hint Resolve ord_and_inv oord_and_inv toplike_int_inv toplike_arrow_inv : falseHd.

Lemma sub_inversion_arrow : forall A1 A2 B1 B2,
    sub (t_arrow A1 A2) (t_arrow B1 B2) -> sub t_top B2 \/ (sub B1 A1 /\ sub A2 B2).
Proof.
  intros.
  inverts* H.
Qed.

Lemma sub_inversion_andl_arrr : forall A1 A2 B1 B2,
    sub (t_and A1 A2) (t_arrow B1 B2) -> sub A1 (t_arrow B1 B2) \/ sub A2 (t_arrow B1 B2).
Proof.
  intros.
  inverts* H.
Qed.

Lemma csub_inversion_andl_arrr : forall A1 A2 B1 B2,
    csub (t_and A1 A2) (t_arrow B1 B2) -> csub A1 (t_arrow B1 B2) \/ csub A2 (t_arrow B1 B2).
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

Lemma sim_reflexivity : forall A,
    sim A A.
Proof.
  intros A.
  induction* A.
Qed.


Lemma csub_reflexivity : forall A,
    csub A A.
Proof.
  intros A.
  induction* A.
Qed.



Require Import Program.Equality.

Hint Constructors sub : core.

Lemma and_inversion : forall A B C,
    sub A (t_and B C) -> sub A B /\ sub A C.
Proof.
  intros A B C H.
  dependent induction H; eauto.
  lets*: IHsub B C.
  lets*: IHsub B C.
Qed.

Lemma cand_inversion : forall A B C,
    csub A (t_and B C) -> csub A B /\ csub A C.
Proof.
  intros A B C H.
  dependent induction H; eauto.
  lets*: IHcsub B C.
  lets*: IHcsub B C.
Qed.



Lemma csub_andl : forall A1 A2 C,
    ord C -> csub (t_and A1 A2) C -> 
    csub A1 C \/ csub A2 C.
Proof.
  intros.
  inverts* H0.
  inverts H.
Qed.


Lemma sub_andl : forall A1 A2 C,
    oord C -> sub (t_and A1 A2) C -> 
    sub A1 C \/ sub A2 C.
Proof.
  intros.
  inverts* H0.
  inverts* H1.
  inverts H.
Qed.


Lemma csub_andl2 : forall A1 A2 C,
    oord C -> csub (t_and A1 A2) C -> 
    csub A1 C \/ csub A2 C.
Proof.
  intros.
  inverts* H0.
  inverts H.
Qed.

(* Lemma csub_transtivity : forall B A,
csub A B -> static B -> forall C, csub B C -> csub A C.
Proof.
  induction B;
  intros;
  eauto;
  try solve [dependent induction H;
          eauto].
  - dependent induction H; eauto.
    dependent induction H1; eauto.
  - inverts* H0. 
  dependent induction H; eauto.
  dependent induction H1; eauto.
  - inverts* H0. 
  dependent induction H; eauto.
  clear IHcsub1 IHcsub2.
  dependent induction H1; eauto.
  - inverts H0.
Qed. *)


(* Lemma sub_transtivity : forall B A,
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
    clear IHsub1 IHsub2.
    dependent induction H1; eauto.

    clear IHsub.

  - dependent induction H; eauto.
    clear IHsub1 IHsub2.
    dependent induction H1; eauto.

Qed.
     *)

(* 
Lemma csub_transtivity : forall B A,
     sub A B -> sub B A -> forall C, csub B C -> csub A C.
Proof.
 induction B;
   intros;
   eauto;
   try solve [dependent induction H;
              eauto].
 - dependent induction H; eauto; try solve[
   dependent induction H1; eauto;
   dependent induction H0; eauto].
 -
    dependent induction H; eauto; try solve[
   dependent induction H1; eauto;
   dependent induction H0; eauto].  
Qed. *)

Ltac auto_sub :=
  try match goal with
      | [ |- sub ?A ?A ] => apply sub_reflexivity 
      (* | [ H: sub ?A (t_and ?B ?C) |- sub ?A ?B ] => (
        eapply sub_transtivity;
        try apply H;
        try apply S_andl1;
        try apply sub_reflexivity) *)
      (* | [ H: sub ?A (t_and ?B ?C) |- sub ?A ?C ] => (
        try eapply sub_transtivity;
        try apply H;
        try apply S_andl2;
        try apply sub_reflexivity) *)
      | [ H: sub (t_arrow _ _) (t_arrow _ _) |- sub _ _ ] => (apply sub_inversion_arrow in H; destruct H; auto_sub)
      (* | [ H1: sub ?A ?B, H2: sub ?B ?C |- sub ?A ?C ] => forwards*: sub_transtivity H1 H2 *)
      (* | [ H1: sub ?A ?B, H2: sub ?B ?C |- sub ?A ?C ] => forwards*: sub_transtivity H1 H2 *)
    | |- _ => try constructor*
      end.


(* topLike *)
(* Lemma toplike_super_top: forall A,
    topLike A <-> sub t_top A.
Proof.
  intro A.
  split.
  - intro H.
    inductions H; eauto.
  - intro H.
    induction A;
      try solve [inverts* H].
Qed. *)


(* Lemma sub_inversion_toparr : forall B C,
    sub t_top B -> sub B C -> sub t_top C.
Proof.
  intros B C S1 S2.
  gen C.
  remember (t_top).
  induction S1;
    inverts* Heqt;
    intros C S2.
  - inductions S2; try solve[inverts* H0]; eauto.
  (* - intuition eauto.
    remember (t_and A2 A3).
    induction S2;
      inverts* Heqt. *)
Qed. *)


(* Lemma toplike_static: forall A,
 topLike A -> static A.
Proof.
  introv tl.
  inductions tl; eauto.
Qed. *)


Lemma toplike_super_topc: forall A,
   topLike A <-> csub t_top A.
Proof.
  introv.
  split.
  - intro H.
    inductions H; try solve[inverts sta];eauto.
  - intro H.
    inductions A;eauto;
      try solve [inverts* H];
      try solve[inverts* sta].
Qed.



(* 
Lemma toplike_super_toplc2: forall B A,
    static A -> topLike B -> topLike A <-> csub B A.
Proof.
  introv sta tl.
  split.
  - intro H.
    inductions H; try solve[inverts* sta];eauto.
  - intro H.
    inductions H; try solve[inverts* tl]; try solve[inverts* sta];eauto.
Qed.

Lemma toplike_super_toplc: forall B A,
    oord A -> topLike B -> topLike A <-> csub B A.
Proof.
  introv sta tl.
  split.
  - intro H.
    inductions H; try solve[inverts sta];eauto.
  - intro H.
    inductions H; try solve[inverts* tl]; try solve[inverts* sta];eauto.
Qed. *)

Lemma toplike_csub: forall A B,
 topLike B ->
 csub A B.
Proof.
  introv top.
  inductions top; eauto.
Qed.

Lemma toplike_decidable : forall A,
    topLike A \/ ~topLike A.
Proof.
  induction A.
  - right.
    unfold not.
    intros H.
    inversion H.
  - left*.
  - right*.
    unfold not; intros nt; inverts nt. 
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
  - left*.
  - right.
      unfold not.
      intros H0.
      inverts H0.
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


Lemma static_not_dyn: forall A,
 static A -> not(dynamic A) .
Proof.
  introv sta.
  inductions sta; try solve[unfold not; intros nt; inverts* nt].
Qed.


Lemma dyn_not_static: forall A,
 dynamic A -> not(static A) .
Proof.
  introv sta.
  inductions sta; try solve[unfold not; intros nt; inverts* nt].
Qed.




Lemma ord_static_ntl: forall A,
 ord A ->
 static A ->
 not(topLike A).
Proof.
  introv ord oord.
  inductions ord; try solve[inverts* oord];
  try solve[unfold not; intros nt; inverts* nt];eauto.
Qed.



Lemma change_static : forall A,
   static (change_typ A).
Proof.
  introv.
  inductions A; unfold change_typ in *; eauto.
Qed.


Lemma change_tpre: forall A,
 tpre (change_typ A) A.
Proof.
  introv.
  inductions A; simpl in *;eauto.
Qed.



Lemma disjoint_eqv: forall A B,
    disjointSpec A B <-> disjoint A B.
Proof.
  intros A B.
  unfold disjointSpec.
  split.
  - gen B.
    inductions A;simpl in *;
      introv H;
      inductions B;simpl in *;
      try solve [constructor*].
    + forwards*: H t_int. inverts H0.
    + forwards*: H t_int. inverts H0.
    + forwards*: H t_int. inverts H0.
    + forwards*: H t_int. inverts H0.
    +
    assert (~ csub t_top  (t_arrow t_dyn t_dyn)). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards*: (H (t_arrow t_dyn t_dyn)).
    +
    forwards*: H (t_rcd l t_top). 
     inverts H0.
    +
    assert (~ csub t_top  (t_arrow t_dyn t_dyn)). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards*: (H (t_arrow t_dyn t_dyn)).
    +
    assert (~ csub t_top  (t_arrow t_dyn t_dyn)). {
        unfold not.
        intro F.
        inversion F.
      }
      forwards*: (H (t_arrow t_dyn t_dyn)).
    +
    forwards*: H (t_rcd l t_top). 
     inverts H0. 
    + destruct(l == l0); eauto. inverts e.
      forwards*: H (t_rcd l0 t_top). 
      inverts H0.
  - 
      intros H C S1 S2.
      (* apply toplike_super_topc; auto. *)
      gen B C.
      induction* A;
        intros B H;
        [ induction* B | inductions B | skip | skip| induction* B  ];
        intros C S1 S2;
        try solve [inverts H; inverts* H0]; simpl in *. 
    + (* int arr *)
      induction* C;
      inverts S1;
      inverts* S2.
    + (* int and *)
      induction* C;
      inverts H;
      inverts* S1;
      try solve[forwards*: toplike_super_toplc S];
      try solve[forwards*: csub_andl S2];
      try solve[forwards*: cand_inversion S2];
      try solve [
        inverts S2;inverts S;
        try solve[inverts H0];
        [ forwards*: IHB1 |
          forwards*: IHB2 ]
          ].
    + (* int rcd *)
      induction* C;
        inverts S1;
        inverts* S2.
    + (* bot top *)
     induction* C;
      inverts H;
      inverts* S1;  
      try solve[forwards*: toplike_super_toplc S];
      try solve[forwards*: csub_andl S2];
      try solve[inverts* H0].
    + (* bot and *)
      induction* C;
      inverts H;
      inverts* S1;  
      try solve[forwards*: toplike_super_toplc S];
      try solve[forwards*: csub_andl S2];
      try solve[forwards*: cand_inversion S2];
      try solve[inverts* H0].
      inverts* S2.
    + (*bot dyn*)
      induction* C;
        inverts S1;
        inverts* S2.
    + (* rcd int *)
      induction* C;
        inverts S1;
        inverts* S2.
    + (* rcd arr *)
      induction* C;
        inverts S1;
        inverts* S2.
    + 
      (* rcd and *)
      induction* C;
      inverts H;
      inverts* S1;  
      try solve[forwards*: toplike_super_toplc S];
      try solve[forwards*: csub_andl S2];
      try solve[forwards*: cand_inversion S2];
      try solve[inverts* H0].
    + (* rcd rcd*)
      induction* C;
      inverts H;
      inverts* S1; 
      try solve[forwards*: toplike_super_toplc S];
      try solve[inverts* H0];
      try solve[inverts* S2].
Qed. 




Lemma disjoint_change_gen: forall A B C n,
 size_typ A + size_typ B + size_typ C < n ->
 disjoint A B ->
 sub (change_typ A) C ->
 sub (change_typ B) C ->
 sub t_top C.
Proof.
  introv sz dis sub1 sub2.
  gen A B C.
  inductions n; intros;try solve[lia].
  inductions dis; simpl in *;try solve[inverts sub1; inverts sub2].
  -
     inverts* sub1.
  -
     inverts* sub2.
  -
     inverts* sub1.
  -
     inverts* sub2.
  -
  inductions C; 
  try solve[forwards: sub_andl sub1];
  try solve[forwards: and_inversion sub1]; simpl in *;auto.
    +
      forwards h1: sub_andl sub1; auto.
      inverts h1 as h1 h2.
      forwards: IHn h1 sub2; auto. simpl in *;lia.
      forwards: IHn h1 sub2; auto. simpl in *;lia.
    +
      inverts sub1 as h1 h2.
      forwards: IHn h1 sub2; auto. simpl in *;lia.
      forwards: IHn h1 sub2; auto. simpl in *;lia.
    +
      forwards h1: sub_andl sub1; auto.
      inverts h1 as h1 h2.
      forwards: IHn h1 sub2; auto. simpl in *;lia.
      forwards: IHn h1 sub2; auto. simpl in *;lia.
    +
      forwards h1: and_inversion sub1.
      inverts h1 as h1 h2.
      forwards h3: and_inversion sub2.
      inverts h3 as h3 h4.
      forwards: IHn (t_and A1 A2) B C1; auto.
      simpl in * ; lia.
      forwards: IHn (t_and A1 A2) B C2; auto.
      simpl in * ; lia.
    +
      inverts sub1 as h1 h2.
      forwards: IHn h1 sub2; auto. simpl in *;lia.
      forwards: IHn h1 sub2; auto. simpl in *;lia.
    +
      forwards h1: sub_andl sub1; auto.
      inverts h1 as h1 h2.
      forwards: IHn h1 sub2; auto. simpl in *;lia.
      forwards: IHn h1 sub2; auto. simpl in *;lia.
  -
  inductions C; 
  try solve[forwards: sub_andl sub1];
  try solve[forwards: and_inversion sub1]; simpl in *;auto.
    +
      forwards h1: sub_andl sub2; auto.
      inverts h1 as h1 h2.
      forwards: IHn sub1 h1; auto. simpl in *;lia.
      forwards: IHn sub1 h1; auto. simpl in *;lia.
    +
      inverts sub2 as h1 h2.
      forwards: IHn sub1 h1; auto. simpl in *;lia.
      forwards: IHn sub1 h1; auto. simpl in *;lia.
    +
      forwards h1: sub_andl sub2; auto.
      inverts h1 as h1 h2.
      forwards: IHn sub1 h1; auto. simpl in *;lia.
      forwards: IHn sub1 h1; auto. simpl in *;lia.
    +
      forwards h1: and_inversion sub1.
      inverts h1 as h1 h2.
      forwards h3: and_inversion sub2.
      inverts h3 as h3 h4.
      forwards: IHn A (t_and B1 B2) C1; auto.
      simpl in * ; lia.
      forwards: IHn A (t_and B1 B2) C2; auto.
      simpl in * ; lia.
    +
      inverts sub2 as h1 h2.
      forwards: IHn sub1 h1; auto. simpl in *;lia.
      forwards: IHn sub1 h1; auto. simpl in *;lia.
    +
      forwards h1: sub_andl sub2; auto.
      inverts h1 as h1 h2.
      forwards: IHn sub1 h1; auto. simpl in *;lia.
      forwards: IHn sub1 h1; auto. simpl in *;lia.
  -
    inductions C; 
    try solve[inverts sub2];
    try solve[inverts sub1]; simpl in *;auto.
    forwards h1: and_inversion sub2.
      inverts h1 as h1 h2.
      forwards h3: and_inversion sub1.
      inverts h3 as h3 h4.
    forwards: IHC1; auto. simpl in *; lia.
    forwards: IHC2; auto. simpl in *; lia.
  -
    inductions C; 
    try solve[inverts sub2];
    try solve[inverts sub1]; simpl in *;auto.
    forwards h1: and_inversion sub2.
      inverts h1 as h1 h2.
      forwards h3: and_inversion sub1.
      inverts h3 as h3 h4.
    forwards: IHC1; auto. simpl in *; lia.
    forwards: IHC2; auto. simpl in *; lia.
  -
    inductions C; 
    try solve[inverts sub2];
    try solve[inverts sub1]; simpl in *;auto.
    forwards h1: and_inversion sub2.
      inverts h1 as h1 h2.
      forwards h3: and_inversion sub1.
      inverts h3 as h3 h4.
    forwards: IHC1; auto. simpl in *; lia.
    forwards: IHC2; auto. simpl in *; lia.
    inverts sub1;inverts sub2.
    exfalso; apply H; auto.
  -
    inductions C; 
    try solve[inverts sub2];
    try solve[inverts sub1]; simpl in *;auto.
    forwards h1: and_inversion sub2.
      inverts h1 as h1 h2.
      forwards h3: and_inversion sub1.
      inverts h3 as h3 h4.
    forwards: IHC1; auto. simpl in *; lia.
    forwards: IHC2; auto. simpl in *; lia.
  -
    inductions C; 
    try solve[inverts sub2];
    try solve[inverts sub1]; simpl in *;auto.
    forwards h1: and_inversion sub2.
      inverts h1 as h1 h2.
      forwards h3: and_inversion sub1.
      inverts h3 as h3 h4.
    forwards: IHC1; auto. simpl in *; lia.
    forwards: IHC2; auto. simpl in *; lia.
  -
    inductions C; 
    try solve[inverts sub2];
    try solve[inverts sub1]; simpl in *;auto.
    forwards h1: and_inversion sub2.
      inverts h1 as h1 h2.
      forwards h3: and_inversion sub1.
      inverts h3 as h3 h4.
    forwards: IHC1; auto. simpl in *; lia.
    forwards: IHC2; auto. simpl in *; lia.
  -
    inductions C; 
    try solve[inverts sub2];
    try solve[inverts sub1]; simpl in *;auto.
    forwards h1: and_inversion sub2.
      inverts h1 as h1 h2.
      forwards h3: and_inversion sub1.
      inverts h3 as h3 h4.
    forwards: IHC1; auto. simpl in *; lia.
    forwards: IHC2; auto. simpl in *; lia.
Qed.




Lemma disjoint_change: forall A B C,
 disjoint A B ->
 sub (change_typ A) C ->
 sub (change_typ B) C ->
 sub t_top C.
Proof.
  introv dis sub1 sub2.
  eapply disjoint_change_gen; eauto.
Qed.




Lemma disjointspec_Disjointspec: forall A B,
 disjointSpec A B -> DisjointSpec A B.
Proof.
  intros A B.
  (* split. *)
  intros h1.
  unfold DisjointSpec.
  forwards*: change_static A.
  forwards*: change_static B.
  forwards*: change_tpre A.
  forwards*: change_tpre B.
  exists (change_typ A) (change_typ B); splits*.
  introv h2 h3.
  rewrite disjoint_eqv in h1.
  forwards*: disjoint_change h1 h2 h3.
Qed.


Lemma Disjoint_eqv: forall A B,
    DisjointSpec A B <-> disjoint A B.
Proof.
  intros A B.
  split.
  - 
    unfold DisjointSpec.
    gen B.
    inductions A;simpl in *;
      introv H;
      inductions B;simpl in *;
      try solve [constructor*].
    +
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      forwards*: h5 t_int. inverts H0.
    + 
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      forwards*: h5 t_int. inverts H0.
    + 
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      inverts* h2.
      apply D_andR.
      apply IHB1.
      exists t_int A; splits*.
      apply IHB2.
      exists t_int B; splits*.
    + 
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      forwards*: h5 t_int. inverts H0.
    + 
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      forwards*: h5 t_int. inverts H0.
    +
     assert (~ sub t_top  (t_arrow t_bot t_top)). {
        unfold not.
        intro F.
        inversion F.
      }
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h4.
      inverts h3.
      inverts h2. 
      forwards*: (h5 (t_arrow t_bot t_top)).
    +
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      inverts* h2.
      apply D_andR.
      apply IHB1.
      exists t_bot A; splits*.
      apply IHB2.
      exists t_bot B; splits*.
    +
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h4.
      inverts h3.
      inverts h2. 
     forwards*: h5 (t_rcd l t_top). 
     inverts H0.
    +
    assert (~ sub t_top  (t_arrow t_bot t_top)). {
        unfold not.
        intro F.
        inversion F.
      }
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h4.
      inverts h3.
      inverts h2.
      inverts h1. 
      forwards*: (h5 (t_arrow t_bot t_top)).
    +
   assert (~ sub t_top  (t_arrow t_bot t_top)). {
        unfold not.
        intro F.
        inversion F.
      }
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h4.
      inverts h3.
      inverts h2.
      inverts h1. 
      forwards*: (h5 (t_arrow t_bot t_top)).
    +
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      inverts* h2.
      apply D_andR.
      apply IHB1.
      exists (t_arrow A B) A0; splits*.
      apply IHB2.
      exists (t_arrow A B) B0; splits*.
    +
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      inverts* h1.
      apply D_andL.
      apply IHA1.
      exists A t_int; splits*.
      apply IHA2.
      exists B t_int; splits*.
    +
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      inverts* h1.
      apply D_andL.
      apply IHA1.
      exists A t_bot; splits*.
      apply IHA2.
      exists B t_bot; splits*.
    +
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      inverts* h1. 
      apply D_andL.
      apply IHA1.
      exists A (t_arrow A0 B0); splits*.
      apply IHA2.
      exists B (t_arrow A0 B0); splits*.
    +
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      inverts* h1. inverts h2. 
      apply D_andL.
      apply IHA1.
      exists A (t_and A0 B0); splits*.
      apply IHA2.
      exists B (t_and A0 B0); splits*.
    +
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      inverts* h1. inverts h2. 
      apply D_andL.
      apply IHA1.
      exists A (t_rcd l A0); splits*.
      apply IHA2.
      exists B0 (t_rcd l A0); splits*.
    +
     lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h4.
      inverts h3.
      inverts h1. 
     forwards*: h5 (t_rcd l t_top). 
     inverts H0.
    +
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3;inverts h4.
      inverts* h1. inverts h2. 
      apply D_andR.
      apply IHB1.
      exists(t_rcd l A0) A1; splits*.
      apply IHB2.
      exists (t_rcd l A0) B; splits*.
    + destruct(l == l0); eauto. inverts e.
      lets(t1&t2&h1&h2&h3&h4&h5): H.
      inverts h3.
      inverts h4.
      inverts h1.
      inverts h2. 
      forwards*: h5 (t_rcd l0 t_top). 
      inverts H0.
  -
      intros H.
      rewrite <-  disjoint_eqv  in H.
      forwards*: disjointspec_Disjointspec H.
Qed. 


Lemma disjoint_and: forall A B C,
     disjointSpec (t_and B C) A <-> disjointSpec B A /\ disjointSpec C A.
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
    disjoint (t_and B C) A <-> disjoint B A /\ disjoint C A.
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


Lemma co_and_lem: forall A B C,
    co (t_and B C) A <-> co B A \/ co C A.
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
    co  A (t_and B C) -> co A B  \/ co A C .
Proof.
  introv H.
      inductions A;
      try solve[
      inverts* H; inverts* H0].
      inverts* H.
      forwards* h1:IHA1.
      forwards* h1:IHA2.
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




Lemma disjoint_eqv2: forall A B,
    not(co (A) (B)) <-> disjoint A B.
Proof.
  intros A B.
  split.
  - gen B.
    inductions A;
      introv H;
      inductions B;
      try solve [constructor*];
      try solve[simpl in *; exfalso; apply H; auto]; simpl in *;
      try solve[apply D_andR; eauto];
      try solve[apply D_andL; eauto].
      destruct(l == l0); eauto. inverts e.
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
    disjointSpec (t_arrow B C) A -> disjointSpec (t_arrow B' C) A.
Proof.
  intros A B C B' H.
  apply disjoint_eqv in H; auto. 
  apply disjoint_eqv; auto.
  inductions A;
    inverts* H; inverts* H0. 
Qed.



 (* Consistent Subtyping*)



Lemma change_sim : forall A,
   sim A (change_typ A).
Proof.
  introv.
  inductions A;
  try solve[ unfold change_typ in *; eauto].
Qed.


Lemma BA_AB: forall B A,
  sim A B -> sim B A.
Proof.
  introv H.
  induction* H.
Qed.


Lemma consub_prop: forall A B,
 csub A B ->
 exists C D, sub A C /\ sim C D /\ sub D B.
Proof.
  introv csub. inductions csub; eauto.
  - exists A t_dyn. split. apply sub_reflexivity; eauto. split. eauto.
    eauto.
  - exists A (change_typ A).
    split. apply sub_reflexivity; eauto. split. 
    apply change_sim. 
    apply S_top.
    apply change_static.
  - forwards*: IHcsub1.
    inverts* H. inverts* H0. inverts* H. inverts* H1.
    forwards*: IHcsub2.
    inverts* H1. inverts* H3. inverts* H1. inverts* H4.
    exists (t_arrow x0 x1) (t_arrow x x2).
    split. eauto.
    split. apply sim_arr. apply BA_AB. auto. auto.
    eauto.
  - forwards*: IHcsub.
    inverts* H. inverts* H0. inverts* H. 
  - forwards*: IHcsub.
    inverts* H. inverts* H0. inverts* H. 
  - forwards*: IHcsub1.
    inverts* H. inverts* H0. inverts* H. inverts* H1.
    forwards*: IHcsub2.
    inverts* H1. inverts* H3. inverts* H1. inverts* H4.
    exists (t_and x x1) (t_and x0 x2).
    split. eauto.
    split. eauto. eauto.
  - forwards*: IHcsub.
    inverts* H. inverts* H0. inverts* H. inverts* H1.
    exists  (t_rcd l x) (t_rcd l x0).
    split*.
Qed.


Inductive sub_size : typ -> typ -> nat -> Prop :=    (* defn sub *)
 | sub_size_z : 
     sub_size  t_int t_int 1
 | sub_size_bot : forall (A:typ),
 sub_size t_bot A 1
 | sub_size_top : forall (A:typ),
     static A ->
     sub_size A t_top 1
 | sub_size_arr : forall (A1 A2 B1 B2:typ) n1 n2,
     sub_size B1 A1 n1 ->
     sub_size A2 B2 n2 ->
     sub_size (t_arrow A1 A2) (t_arrow B1 B2) (1+n1+n2)
 | sub_size_andl1 : forall (A1 A2 A3:typ) n1,
     sub_size A1 A3 n1 ->
     sub_size (t_and A1 A2) A3 (1+n1)
 | sub_size_andl2 : forall (A1 A2 A3:typ) n1 ,
     sub_size A2 A3 n1 ->
     sub_size (t_and A1 A2) A3 (1+n1)
 | sub_size_andr : forall (A1 A2 A3:typ) n1 n2,
     sub_size A1 A2 n1 ->
     sub_size A1 A3 n2 ->
     sub_size A1 (t_and A2 A3) (1+n1+n2)
 | sub_size_dyn : 
     sub_size t_dyn t_dyn 1
 | sub_size_rcd : forall l (C D:typ) n,
     sub_size C D n ->
     sub_size (t_rcd l C) (t_rcd l D) (1+n).

Hint Constructors sub_size: core.


Lemma and_inversion_size : forall A B C n,
    sub_size A (t_and B C) n -> exists n1 n2, sub_size A B n1 /\ sub_size A C n2 /\ n1 <= n /\ n2 <= n.
Proof.
  intros A B C n H.
  dependent induction H; intros;try solve[exists*];eauto.
  -
  forwards*: IHsub_size B C.
  lets(n2&n3&sb1&sb2&ls1&ls2): H0.
  exists (1+n2) (1+n3).
  splits*.
  lia.
  lia.
  -
  forwards*: IHsub_size B C.
  lets(n2&n3&sb1&sb2&ls1&ls2): H0.
  exists (1+n2) (1+n3).
  splits*.
  lia.
  lia.
  -
  exists n1 n2.
  splits*.
  lia.
  lia.
Qed.

Lemma consub_propr_gen: forall A B C D n1 n2 n,
  n1 + n2 < n ->
  sub_size A C n1 -> sim C D -> sub_size D B n2 -> csub A B.
Proof.
  introv sz sub1 cons sub2. gen A B C D n1 n2.
  inductions n; intros; try solve[lia].
  inductions sub2.
  -
    inductions sub1; auto; try solve [inverts cons].
    +
    assert(sub_size t_int t_int 1). auto.
    forwards: IHn cons sub1 H. lia.
    auto.
    +
    assert(sub_size t_int t_int 1). auto.
    forwards: IHn cons sub1 H. lia.
    auto.
  -   
    inductions sub1; auto; try solve [inverts cons].
    +
    assert(sub_size t_bot A0 1). auto.
    forwards: IHn cons sub1 H. lia.
    auto.
    +
    assert(sub_size t_bot A0 1). auto.
    forwards: IHn cons sub1 H. lia.
    auto.
  -
    inductions sub1; auto; try solve [inverts cons].
  -
    inductions sub1; auto; try solve [inverts cons].
    +
    inverts cons.
    apply BA_AB in H2.
    forwards: IHn H2 sub2_1 sub1_1. lia.
    forwards: IHn H4 sub1_2 sub2_2. lia.
    auto.
    +
    assert(sub_size (t_arrow A1 A2) (t_arrow B1 B2) (1+n0+n2)). auto.
    forwards: IHn cons sub1 H. lia.
    auto.
    +
    assert(sub_size (t_arrow A1 A2) (t_arrow B1 B2) (1+n0+n2)). auto.
    forwards: IHn cons sub1 H. lia.
    auto.
  -
    inverts cons.
    + 
    forwards: IHn sub1 sub2. auto. lia. auto.
    +
    forwards ha: and_inversion_size sub1.
    lets(n2&n3&sb1&sb2&ls1&ls2): ha.    
    forwards: IHn H2 sb1 sub2; auto.
    lia.
  -
    inverts cons.
    + 
    forwards: IHn sub1 sub2. auto. lia. auto.
    +
    forwards ha: and_inversion_size sub1.
    lets(n2&n3&sb1&sb2&ls1&ls2): ha.    
    forwards: IHn H3 sb2 sub2; auto.
    lia.
  -
    forwards: IHn cons sub1 sub2_1; auto.
    lia.
    forwards: IHn cons sub1 sub2_2; auto.
    lia.
  -
    auto.
  -
    inductions sub1; auto; try solve [inverts cons].
    +
    inverts cons.
    assert(sub_size (t_rcd l C0) (t_rcd l D) (1+n0)). auto.
    forwards: IHn sub1 H. auto. lia. auto.
    assert(sub_size (t_rcd l C0) (t_rcd l D) (1+n0)). auto.
    forwards: IHn sub1 H. auto. lia. auto.
    +
    inverts cons.
    assert(sub_size (t_rcd l C0) (t_rcd l D) (1+n0)). auto.
    forwards: IHn sub1 H. auto. lia. auto.
    assert(sub_size (t_rcd l C0) (t_rcd l D) (1+n0)). auto.
    forwards: IHn sub1 H. auto. lia. auto.
    +
    inverts cons.
    forwards: IHn sub1 sub2. auto. lia. auto.
Qed.



Lemma consub_proprs: forall A B C D n1 n2,
  sub_size A C n1 -> sim C D -> sub_size D B n2 -> csub A B.
Proof.
  intros.
  eapply consub_propr_gen; eauto.
Qed.



Lemma sub_size_sub: forall t1 t2 n,
 sub_size t1 t2 n -> sub t1 t2.
Proof.
  introv sz.
  inductions sz; eauto.
Qed.


Lemma sub_sub_size: forall t1 t2,
 sub t1 t2 -> exists n, sub_size t1 t2 n.
Proof.
  introv sz.
  inductions sz; 
  try solve[exists*];
  try solve[inverts* IHsz1;inverts* IHsz2];
  try solve[inverts* IHsz];eauto.
Qed.


Lemma consub_propr: forall A B C D,
  sub A C -> sim C D -> sub D B -> csub A B.
Proof.
  introv h1 h2 h3.
  forwards* hh1: sub_sub_size h1.
  forwards* hh2: sub_sub_size h3.
  inverts hh1 as hh1.
  inverts hh2 as hh2.
  forwards* h4: consub_proprs hh1 h2 hh2.
Qed.



Lemma sub_csub: forall A B,
 sub A B ->
 csub A B.
Proof.
  introv sub.
  inductions sub; eauto.
Qed.


