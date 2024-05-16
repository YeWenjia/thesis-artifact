Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               Typing
               Subtyping_inversion
               Infrastructure.


Lemma eq_dec_typ : forall x y:typ, {x = y} + {x <> y}.
Proof.
 decide equality; auto.
Defined.

Lemma eq_dec : forall x y:exp, {x = y} + {x <> y}.
Proof.
  decide equality; auto;
  try solve[forwards*: eq_dec_typ].
  -
  destruct(n == n0); eauto.
  -
  destruct(i5 == i0); eauto.
Defined.


(* Cast *)
Lemma Cast_top_normal : forall (v: exp) r,
   Cast v t_top r -> r = (r_e e_top).
Proof.
  introv H.
  remember t_top.
  lets red: H.
  inductions H;
    try solve [inverts* Heqt;
    try solve[exfalso; apply H1; auto];
    try solve[exfalso; apply H0; auto]];
    try solve[subst*; exfalso; apply H; eauto];
    try solve[inverts* Heqt;inverts* H];
    try solve[inverts pval as h1 h2; inverts* h1].
Qed.



(* Lemma toplike_not_dyn: forall A,
 topLike A ->
 not(dynamic A).
Proof.
  introv tlike.
  inductions tlike; 
  try solve [unfold not; intros nt; inverts* nt].
Qed. *)


(* Lemma TypedReduce_ord_toplike_normal : forall (v v': exp) (A : typ),
   oord A -> topLike A -> Cast v A (r_e v') -> v' = e_top.
Proof.
  introv H1 H2 Red.
  inductions Red; try solve_false; eauto; 
  try solve[inverts* H2];
  try solve[inverts pval as h1 h2; inverts* h1].
  inverts* H0.
Qed. *)


(* Lemma Cast_top_normal2 : forall (v v': exp) A,
    topLike A ->
    Cast v A (r_e v') ->  topLike (principal_type v').
Proof.
  introv tlike H.
  inductions H;simpl in *;
    try solve[subst*; exfalso; apply H; eauto];
    try solve[inverts* tlike].
    inverts* H2.
    inverts* H1; simpl in *.
    inverts* tlike.
Qed. *)


Lemma Cast_csub: forall v v'  A,
 Cast v A (r_e v') ->
 csub (principal_type v) A.
Proof.
  introv red.
  inductions red; simpl in *;try solve[inverts* pval; try solve[ inverts H1];
  simpl; eauto];eauto.
  -
  inverts* H0.
  -
  inverts* H.
Qed.


Lemma Cast_csub_a: forall v A,
 Cast v A (r_blame err_a) ->
 csub (principal_type v) A.
Proof.
  introv red.
  inductions red; simpl in *;try solve[inverts* pval; try solve[ inverts H1];
  simpl; eauto];eauto.
  -
  inverts* H0.
  forwards*: Cast_csub red1.
  -
  inverts* H.
  forwards*: Cast_csub red1.
  forwards*: Cast_csub red2.
Qed.


(* Lemma toplike_static: forall A,
 topLike A ->
 static A.
Proof.
  introv tl.
  inductions tl; eauto.
Qed. *)



Lemma joint_uniq: forall r1 r2 r3 r4,
 joint r1 r2 r3 ->
 joint r1 r2 r4 ->
 r3 = r4.
Proof.
  introv j1 j2.
  inductions j1; try solve[inductions j2; eauto]; eauto.
Qed.


Lemma joint_progress: forall r1 r2,
 exists r3, joint r1 r2 r3.
Proof.
  introv.
  destruct r1; destruct r2; try solve[exists*];eauto;
  try solve[destruct e0; try solve[exists*];eauto];
  try solve[destruct e; try solve[exists*];eauto].
  +
  destruct e0; try solve[exists*];eauto.
  destruct e; try solve[exists*];eauto.
Qed.

Lemma joina_uniq: forall r1 r2 r3 r4,
 joina r1 r2 r3 ->
 joina r1 r2 r4 ->
 r3 = r4.
Proof.
  introv j1 j2.
  inductions j1; try solve[inductions j2; eauto]; 
  try solve[inverts* j2];eauto.
Qed.


Lemma joina_progress: forall r1 r2,
 exists r3, joina r1 r2 r3.
Proof.
  introv.
  destruct r1; destruct r2; try solve[exists*];eauto;
  try solve[destruct e0; try solve[exists*];eauto];
  try solve[destruct e; try solve[exists*];eauto].
  +
  forwards* h1: eq_dec e e0.
  inverts* h1.
Qed.

(* Lemma Cast_toplike_uniq :
  forall A, topLike A ->
            forall (v1 v2 : exp) r1 r2, 
            value v1 -> value v2 -> Cast v1 A r1 -> Cast v2 A r2 -> r1 = r2.
Proof.
  intros A Typ.
  induction Typ;
    introv pval1 pval2 Red1 Red2.
  - apply Cast_top_normal in Red1; auto.
    apply Cast_top_normal in Red2; auto.
    subst*.
  - inverts~ Red1; try solve_false;
      inverts~ Red2; try solve_false;
      try solve[
        exfalso; apply H0;
        forwards*: toplike_csub (principal_type v1) (t_and A B)
      ];
      try solve[
        exfalso; apply H0;
        forwards*: toplike_csub (principal_type v2) (t_and A B)
      ];
      try solve[
        forwards h1: IHTyp1 H2 H3; auto;
    forwards h2: IHTyp2 H4 H6; auto;
    congruence
      ].
    forwards h1: IHTyp1 H1 H2; auto.
    forwards h2: IHTyp2 H3 H6; auto.
    inverts h1; inverts h2.
    forwards h3: joint_uniq H5 H8; auto.
Qed. *)


Lemma fvalue_ftype: forall f, 
 fvalue f ->
 exists t1 t2, principal_type f = (t_arrow t1 t2).
Proof.
  introv fval.
  inverts* fval; simpl in *; eauto.
Qed.


Lemma Cast_ty: forall v A v',
 Cast v A (r_e v') ->
 principal_type v' = A.
Proof.
  introv h1.
  inductions h1; simpl in *;eauto.
  -
    forwards* h2:IHh1.
    rewrite h2 in *; auto.
  -
    inverts* H0.
  -
    inverts* H; simpl in *; eauto.
    forwards* h1: IHh1_1.
    forwards* h2: IHh1_2.
    rewrite h1 in *.
    rewrite h2 in *.
    auto.
Qed.


Lemma value_ground: forall v,
 value v ->
 Ground (principal_type v) ->
 gvalue v.
Proof.
  introv h1 h2.
  inductions h1; simpl in *;try solve[inverts* h2].
  -
     forwards* h5: fvalue_ftype H.
    lets(t1&t2&h6): h5.
    rewrite h6 in *.
    inverts h2.
    inverts H; simpl in *;inverts* h6.
  -
    inverts h2 as h2 h3.
    assert(exists e1', gvalue e1' /\ e1 = (e_anno e1' t_dyn)) as h4.
    inverts h1_1; try solve[simpl in *;inverts h2]; eauto.
    forwards* h5: fvalue_ftype H.
    lets(t1&t2&h6): h5.
    rewrite <- h2 in *. inverts h6.
    assert(exists e2', gvalue e2' /\ e2 = (e_anno e2' t_dyn)) as h7.
    inverts h1_2; try solve[simpl in *;inverts h3]; eauto.
    forwards* h5: fvalue_ftype H.
    lets(t1&t2&h6): h5.
    rewrite <- h3 in *. inverts h6.
    lets(g1&h8&h9): h4.
    lets(g2&h10&h11): h7.
    inverts h9. inverts* h11.
  -
    inverts h2 as h2.
    assert(exists e1', gvalue e1' /\ e = (e_anno e1' t_dyn)) as h4.
    inverts h1; try solve[simpl in *;inverts h2]; eauto.
    forwards* h5: fvalue_ftype H.
    lets(t1&t2&h6): h5.
    rewrite <- h2 in *. inverts h6.
    lets(g2&h10&h11): h4.
   inverts* h11.
Qed.


Lemma Cast_value: forall v A v',
 value v ->
 Cast v A (r_e v') ->
 value v'.
Proof.
  introv Val Red.
  inductions Red; try solve[inverts Val as h1; try solve[inverts* h1];
  try solve[exfalso; apply H0; auto]; auto];eauto.
  -
    assert(Ground (const(principal_type s))) as h1.
    inverts H as h2; simpl in *; eauto.
    forwards* h3: fvalue_ftype h2.
    lets(t1&t2&h4):h3.
    rewrite h4 ; simpl; auto.
    forwards* h5: Cast_ty Red.
    rewrite <- h5 in *; auto.
    forwards*: value_ground h1.
  -
    inverts Val as h0;try solve[inverts h0].
    forwards* h1: Cast_ty Red1.
    forwards* h2: Cast_ty Red2.
    forwards* h3: IHRed1.
    forwards* h4: IHRed2.
    assert(Ground (principal_type (e_merge v1' v2'))) as h5. simpl.
    rewrite h1. rewrite h2.
    eauto.
    forwards*: value_ground h5.
  -
    inverts Val as h1; try solve[inverts* h1].
    inverts* H0.
  -
    inverts* H.
Qed.








