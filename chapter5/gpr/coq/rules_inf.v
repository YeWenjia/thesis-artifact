Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export Definitions.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  typ_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme exp_ind' := Induction for exp Sort Prop.

Definition exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 =>
  exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.

Scheme exp_rec' := Induction for exp Sort Set.

Definition exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 =>
  exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_typ_wrt_typ_rec (n1 : nat) (X1 : X) (A1 : typ) {struct A1} : typ :=
  match A1 with
    | t_fvar  X2 => if (X1 == X2) then (t_bvar  n1) else (t_fvar  X2)
    | t_bvar  n2 => if (lt_ge_dec n2 n1) then (t_bvar  n2) else (t_bvar  (S n2))
    | t_int => t_int
    | t_arrow A2 B1 => t_arrow (close_typ_wrt_typ_rec n1 X1 A2) (close_typ_wrt_typ_rec n1 X1 B1)
    | t_unit => t_unit
    | t_dyn => t_dyn
    | t_all B1 => t_all (close_typ_wrt_typ_rec (S n1) X1 B1)
    | t_ref A2 => t_ref (close_typ_wrt_typ_rec n1 X1 A2)
  end.

Definition close_typ_wrt_typ X1 A1 := close_typ_wrt_typ_rec 0 X1 A1.

Fixpoint close_exp_wrt_typ_rec (n1 : nat) (X1 : X) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | e_fvar  x1 => e_fvar  x1
    | e_bvar  n2 => e_bvar  n2
    | e_unit => e_unit
    | e_lit i1 => e_lit i1
    | e_abs e2 => e_abs (close_exp_wrt_typ_rec n1 X1 e2)
    | e_app e2 e3 => e_app (close_exp_wrt_typ_rec n1 X1 e2) (close_exp_wrt_typ_rec n1 X1 e3)
    | e_ref e2 => e_ref (close_exp_wrt_typ_rec n1 X1 e2)
    | e_loc o1 => e_loc o1
    | e_anno e2 A1 => e_anno (close_exp_wrt_typ_rec n1 X1 e2) (close_typ_wrt_typ_rec n1 X1 A1)
    | e_tabs e2 => e_tabs (close_exp_wrt_typ_rec (S n1) X1 e2)
    | e_tapp e2 A1 => e_tapp (close_exp_wrt_typ_rec n1 X1 e2) (close_typ_wrt_typ_rec n1 X1 A1)
    | e_get e2 => e_get (close_exp_wrt_typ_rec n1 X1 e2)
    | e_set e2 e3 => e_set (close_exp_wrt_typ_rec n1 X1 e2) (close_exp_wrt_typ_rec n1 X1 e3)
    | e_val e2 A1 => e_val (close_exp_wrt_typ_rec n1 X1 e2) (close_typ_wrt_typ_rec n1 X1 A1)
    | e_rval e2 => e_rval (close_exp_wrt_typ_rec n1 X1 e2)
  end.

Fixpoint close_exp_wrt_exp_rec (n1 : nat) (x1 : termvar) (e1 : exp) {struct e1} : exp :=
  match e1 with
    | e_fvar  x2 => if (x1 == x2) then (e_bvar  n1) else (e_fvar  x2)
    | e_bvar  n2 => if (lt_ge_dec n2 n1) then (e_bvar  n2) else (e_bvar  (S n2))
    | e_unit => e_unit
    | e_lit i1 => e_lit i1
    | e_abs e2 => e_abs (close_exp_wrt_exp_rec (S n1) x1 e2)
    | e_app e2 e3 => e_app (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | e_ref e2 => e_ref (close_exp_wrt_exp_rec n1 x1 e2)
    | e_loc o1 => e_loc o1
    | e_anno e2 A1 => e_anno (close_exp_wrt_exp_rec n1 x1 e2) A1
    | e_tabs e2 => e_tabs (close_exp_wrt_exp_rec n1 x1 e2)
    | e_tapp e2 A1 => e_tapp (close_exp_wrt_exp_rec n1 x1 e2) A1
    | e_get e2 => e_get (close_exp_wrt_exp_rec n1 x1 e2)
    | e_set e2 e3 => e_set (close_exp_wrt_exp_rec n1 x1 e2) (close_exp_wrt_exp_rec n1 x1 e3)
    | e_val e2 A1 => e_val (close_exp_wrt_exp_rec n1 x1 e2) A1
    | e_rval e2 => e_rval (close_exp_wrt_exp_rec n1 x1 e2) 
  end.

Definition close_exp_wrt_typ X1 e1 := close_exp_wrt_typ_rec 0 X1 e1.

Definition close_exp_wrt_exp x1 e1 := close_exp_wrt_exp_rec 0 x1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_fvar  X1 => 1
    | t_bvar  n1 => 1
    | t_int => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_unit => 1
    | t_dyn => 1
    | t_all B1 => 1 + (size_typ B1)
    | t_ref A2 => 1 + (size_typ A2)
  end.

Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
  match e1 with
    | e_fvar  x1 => 1
    | e_bvar  n1 => 1
    | e_unit => 1
    | e_lit i1 => 1
    | e_abs e2 => 1 + (size_exp e2)
    | e_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | e_ref e2 => 1 + (size_exp e2)
    | e_loc o1 => 1
    | e_anno e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | e_tabs e2 => 1 + (size_exp e2)
    | e_tapp e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | e_get e2 => 1 + (size_exp e2)
    | e_set e2 e3 => 1 + (size_exp e2) + (size_exp e3)
    | e_val e2 A1 => 1 + (size_exp e2) + (size_typ A1)
    | e_rval e2 => 1 + (size_exp e2) 
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_typ_wrt_typ : nat -> typ -> Prop :=
  | degree_wrt_typ_t_fvar  : forall n1 X1,
    degree_typ_wrt_typ n1 (t_fvar  X1)
  | degree_wrt_typ_t_bvar  : forall n1 n2,
    lt n2 n1 ->
    degree_typ_wrt_typ n1 (t_bvar  n2)
  | degree_wrt_typ_t_int : forall n1,
    degree_typ_wrt_typ n1 (t_int)
  | degree_wrt_typ_t_arrow : forall n1 A1 B1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 B1 ->
    degree_typ_wrt_typ n1 (t_arrow A1 B1)
  | degree_wrt_typ_t_unit : forall n1,
    degree_typ_wrt_typ n1 (t_unit)
  | degree_wrt_typ_t_dyn : forall n1,
    degree_typ_wrt_typ n1 (t_dyn)
  | degree_wrt_typ_t_all : forall n1 B1,
    degree_typ_wrt_typ (S n1) B1 ->
    degree_typ_wrt_typ n1 (t_all B1)
  | degree_wrt_typ_t_ref : forall n1 A1,
    degree_typ_wrt_typ n1 A1 ->
    degree_typ_wrt_typ n1 (t_ref A1).

Scheme degree_typ_wrt_typ_ind' := Induction for degree_typ_wrt_typ Sort Prop.

Definition degree_typ_wrt_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  degree_typ_wrt_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Hint Constructors degree_typ_wrt_typ : core lngen.

Inductive degree_exp_wrt_typ : nat -> exp -> Prop :=
  | degree_wrt_typ_e_fvar  : forall n1 x1,
    degree_exp_wrt_typ n1 (e_fvar  x1)
  | degree_wrt_typ_e_bvar  : forall n1 n2,
    degree_exp_wrt_typ n1 (e_bvar  n2)
  | degree_wrt_typ_e_unit : forall n1,
    degree_exp_wrt_typ n1 (e_unit)
  | degree_wrt_typ_e_lit : forall n1 i1,
    degree_exp_wrt_typ n1 (e_lit i1)
  | degree_wrt_typ_e_abs : forall n1 e1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_abs e1)
  | degree_wrt_typ_e_app : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (e_app e1 e2)
  | degree_wrt_typ_e_ref : forall n1 e1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_ref e1)
  | degree_wrt_typ_e_loc : forall n1 o1,
    degree_exp_wrt_typ n1 (e_loc o1)
  | degree_wrt_typ_e_anno : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (e_anno e1 A1)
  | degree_wrt_typ_e_tabs : forall n1 e1,
    degree_exp_wrt_typ (S n1) e1 ->
    degree_exp_wrt_typ n1 (e_tabs e1)
  | degree_wrt_typ_e_tapp : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (e_tapp e1 A1)
  | degree_wrt_typ_e_get : forall n1 e1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_get e1)
  | degree_wrt_typ_e_set : forall n1 e1 e2,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 e2 ->
    degree_exp_wrt_typ n1 (e_set e1 e2)
  | degree_wrt_typ_e_val : forall n1 e1 A1,
    degree_exp_wrt_typ n1 e1 ->
    degree_typ_wrt_typ n1 A1 ->
    degree_exp_wrt_typ n1 (e_val e1 A1)
    | degree_wrt_typ_e_rval : forall n1 e1,
    degree_exp_wrt_typ n1 e1 ->
    degree_exp_wrt_typ n1 (e_rval e1).

Inductive degree_exp_wrt_exp : nat -> exp -> Prop :=
  | degree_wrt_exp_e_fvar  : forall n1 x1,
    degree_exp_wrt_exp n1 (e_fvar  x1)
  | degree_wrt_exp_e_bvar  : forall n1 n2,
    lt n2 n1 ->
    degree_exp_wrt_exp n1 (e_bvar  n2)
  | degree_wrt_exp_e_unit : forall n1,
    degree_exp_wrt_exp n1 (e_unit)
  | degree_wrt_exp_e_lit : forall n1 i1,
    degree_exp_wrt_exp n1 (e_lit i1)
  | degree_wrt_exp_e_abs : forall n1 e1,
    degree_exp_wrt_exp (S n1) e1 ->
    degree_exp_wrt_exp n1 (e_abs e1)
  | degree_wrt_exp_e_app : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (e_app e1 e2)
  | degree_wrt_exp_e_ref : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_ref e1)
  | degree_wrt_exp_e_loc : forall n1 o1,
    degree_exp_wrt_exp n1 (e_loc o1)
  | degree_wrt_exp_e_anno : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_anno e1 A1)
  | degree_wrt_exp_e_tabs : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_tabs e1)
  | degree_wrt_exp_e_tapp : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_tapp e1 A1)
  | degree_wrt_exp_e_get : forall n1 e1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_get e1)
  | degree_wrt_exp_e_set : forall n1 e1 e2,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 e2 ->
    degree_exp_wrt_exp n1 (e_set e1 e2)
  | degree_wrt_exp_e_val : forall n1 e1 A1,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_val e1 A1)
  | degree_wrt_exp_e_rval : forall n1 e1 ,
    degree_exp_wrt_exp n1 e1 ->
    degree_exp_wrt_exp n1 (e_rval e1).

Scheme degree_exp_wrt_typ_ind' := Induction for degree_exp_wrt_typ Sort Prop.

Definition degree_exp_wrt_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  degree_exp_wrt_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.

Scheme degree_exp_wrt_exp_ind' := Induction for degree_exp_wrt_exp Sort Prop.

Definition degree_exp_wrt_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 =>
  degree_exp_wrt_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.

Hint Constructors degree_exp_wrt_typ : core lngen.

Hint Constructors degree_exp_wrt_exp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_typ : typ -> Set :=
  | lc_set_t_fvar  : forall X1,
    lc_set_typ (t_fvar  X1)
  | lc_set_t_int :
    lc_set_typ (t_int)
  | lc_set_t_arrow : forall A1 B1,
    lc_set_typ A1 ->
    lc_set_typ B1 ->
    lc_set_typ (t_arrow A1 B1)
  | lc_set_t_unit :
    lc_set_typ (t_unit)
  | lc_set_t_dyn :
    lc_set_typ (t_dyn)
  | lc_set_t_all : forall B1,
    (forall X1 : X, lc_set_typ (open_tt B1 (t_fvar  X1))) ->
    lc_set_typ (t_all B1)
  | lc_set_t_ref : forall A1,
    lc_set_typ A1 ->
    lc_set_typ (t_ref A1).

Scheme lc_typ_ind' := Induction for type Sort Prop.

Definition lc_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  lc_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme lc_set_typ_ind' := Induction for lc_set_typ Sort Prop.

Definition lc_set_typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  lc_set_typ_ind' H1 H2 H3 H4 H5 H6 H7 H8.

Scheme lc_set_typ_rec' := Induction for lc_set_typ Sort Set.

Definition lc_set_typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 =>
  lc_set_typ_rec' H1 H2 H3 H4 H5 H6 H7 H8.

Hint Constructors type   : core lngen.

Hint Constructors lc_set_typ : core lngen.

Inductive lc_set_exp : exp -> Set :=
  | lc_set_e_fvar  : forall x1,
    lc_set_exp (e_fvar  x1)
  | lc_set_e_unit :
    lc_set_exp (e_unit)
  | lc_set_e_lit : forall i1,
    lc_set_exp (e_lit i1)
  | lc_set_e_abs : forall e1,
    (forall x1 : termvar, lc_set_exp (open_ee   e1 (e_fvar  x1))) ->
    lc_set_exp (e_abs e1)
  | lc_set_e_app : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (e_app e1 e2)
  | lc_set_e_ref : forall e1,
    lc_set_exp e1 ->
    lc_set_exp (e_ref e1)
  | lc_set_e_loc : forall o1,
    lc_set_exp (e_loc o1)
  | lc_set_e_anno : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (e_anno e1 A1)
  | lc_set_e_tabs : forall e1,
    (forall X1 : X, lc_set_exp (open_te e1 (t_fvar  X1))) ->
    lc_set_exp (e_tabs e1)
  | lc_set_e_tapp : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (e_tapp e1 A1)
  | lc_set_e_get : forall e1,
    lc_set_exp e1 ->
    lc_set_exp (e_get e1)
  | lc_set_e_set : forall e1 e2,
    lc_set_exp e1 ->
    lc_set_exp e2 ->
    lc_set_exp (e_set e1 e2)
  | lc_set_e_val : forall e1 A1,
    lc_set_exp e1 ->
    lc_set_typ A1 ->
    lc_set_exp (e_val e1 A1)
  | lc_set_e_rval : forall e1,
    lc_set_exp e1 ->
    lc_set_exp (e_rval e1).

Scheme lc_exp_ind' := Induction for expr Sort Prop.

Definition lc_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  lc_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.

Scheme lc_set_exp_ind' := Induction for lc_set_exp Sort Prop.

Definition lc_set_exp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  lc_set_exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.

Scheme lc_set_exp_rec' := Induction for lc_set_exp Sort Set.

Definition lc_set_exp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 =>
  lc_set_exp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15.

Hint Constructors expr   : core lngen.

Hint Constructors lc_set_exp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_typ_wrt_typ A1 := forall X1, type   (open_tt A1 (t_fvar  X1)).

Hint Unfold body_typ_wrt_typ : core.

Definition body_exp_wrt_typ e1 := forall X1, expr   (open_te e1 (t_fvar  X1)).

Definition body_exp_wrt_exp e1 := forall x1, expr   (open_ee   e1 (e_fvar  x1)).

Hint Unfold body_exp_wrt_typ : core.

Hint Unfold body_exp_wrt_exp : core.


(* *********************************************************************** *)
(** * Tactic support *)

(** Additional hint declarations. *)

Hint Resolve @plus_le_compat : lngen.

(** Redefine some tactics. *)

Ltac default_case_split ::=
  first
    [ progress destruct_notin
    | progress destruct_sum
    | progress safe_f_equal
    ].


(* *********************************************************************** *)
(** * Theorems about [size] *)

Ltac default_auto ::= auto with arith lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma size_typ_min_mutual :
(forall A1, 1 <= size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_typ_min :
forall A1, 1 <= size_typ A1.
Proof.
pose proof size_typ_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_min : lngen.

(* begin hide *)

Lemma size_exp_min_mutual :
(forall e1, 1 <= size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_exp_min :
forall e1, 1 <= size_exp e1.
Proof.
pose proof size_exp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_min : lngen.

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  size_typ (close_typ_wrt_typ_rec n1 X1 A1) = size_typ A1.
Proof.
pose proof size_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_close_typ_wrt_typ_rec : lngen.
Hint Rewrite size_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  size_exp (close_exp_wrt_typ_rec n1 X1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_close_exp_wrt_typ_rec : lngen.
Hint Rewrite size_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  size_exp (close_exp_wrt_exp_rec n1 x1 e1) = size_exp e1.
Proof.
pose proof size_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite size_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_close_typ_wrt_typ :
forall A1 X1,
  size_typ (close_typ_wrt_typ X1 A1) = size_typ A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve size_typ_close_typ_wrt_typ : lngen.
Hint Rewrite size_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_typ :
forall e1 X1,
  size_exp (close_exp_wrt_typ X1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve size_exp_close_exp_wrt_typ : lngen.
Hint Rewrite size_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma size_exp_close_exp_wrt_exp :
forall e1 x1,
  size_exp (close_exp_wrt_exp x1 e1) = size_exp e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve size_exp_close_exp_wrt_exp : lngen.
Hint Rewrite size_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  size_typ A1 <= size_typ (open_tt_rec    n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_tt_rec    :
forall A1 A2 n1,
  size_typ A1 <= size_typ (open_tt_rec    n1 A2 A1).
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_open_tt_rec    : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1,
  size_exp e1 <= size_exp (open_te_rec     n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_te_rec     :
forall e1 A1 n1,
  size_exp e1 <= size_exp (open_te_rec     n1 A1 e1).
Proof.
pose proof size_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_te_rec     : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  size_exp e1 <= size_exp (open_ee_rec     n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_ee_rec     :
forall e1 e2 n1,
  size_exp e1 <= size_exp (open_ee_rec     n1 e2 e1).
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_ee_rec     : lngen.

(* end hide *)

Lemma size_typ_open_tt :
forall A1 A2,
  size_typ A1 <= size_typ (open_tt A1 A2).
Proof.
unfold open_tt;      default_simp.
Qed.

Hint Resolve size_typ_open_tt : lngen.

Lemma size_exp_open_te :
forall e1 A1,
  size_exp e1 <= size_exp (open_te e1 A1).
Proof.
unfold open_te; default_simp.
Qed.

Hint Resolve size_exp_open_te : lngen.

Lemma size_exp_open_ee   :
forall e1 e2,
  size_exp e1 <= size_exp (open_ee   e1 e2).
Proof.
unfold open_ee; default_simp.
Qed.

Hint Resolve size_exp_open_ee   : lngen.

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var_mutual :
(forall A1 X1 n1,
  size_typ (open_tt_rec    n1 (t_fvar  X1) A1) = size_typ A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_typ_open_typ_wrt_typ_rec_var :
forall A1 X1 n1,
  size_typ (open_tt_rec    n1 (t_fvar  X1) A1) = size_typ A1.
Proof.
pose proof size_typ_open_typ_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_rec_var : lngen.
Hint Rewrite size_typ_open_typ_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var_mutual :
(forall e1 X1 n1,
  size_exp (open_te_rec     n1 (t_fvar  X1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_typ_rec_var :
forall e1 X1 n1,
  size_exp (open_te_rec     n1 (t_fvar  X1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_typ_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_typ_rec_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_typ_rec_var using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var_mutual :
(forall e1 x1 n1,
  size_exp (open_ee_rec     n1 (e_fvar  x1) e1) = size_exp e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall e1 x1 n1,
  size_exp (open_ee_rec     n1 (e_fvar  x1) e1) = size_exp e1.
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_rec_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_typ_open_typ_wrt_typ_var :
forall A1 X1,
  size_typ (open_tt A1 (t_fvar  X1)) = size_typ A1.
Proof.
unfold open_tt;      default_simp.
Qed.

Hint Resolve size_typ_open_typ_wrt_typ_var : lngen.
Hint Rewrite size_typ_open_typ_wrt_typ_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_typ_var :
forall e1 X1,
  size_exp (open_te e1 (t_fvar  X1)) = size_exp e1.
Proof.
unfold open_te; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_typ_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_typ_var using solve [auto] : lngen.

Lemma size_exp_open_exp_wrt_exp_var :
forall e1 x1,
  size_exp (open_ee   e1 (e_fvar  x1)) = size_exp e1.
Proof.
unfold open_ee; default_simp.
Qed.

Hint Resolve size_exp_open_exp_wrt_exp_var : lngen.
Hint Rewrite size_exp_open_exp_wrt_exp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_typ_wrt_typ_S_mutual :
(forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind degree_typ_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_S :
forall n1 A1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_typ_S_mutual :
(forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_typ_S :
forall n1 e1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_exp_wrt_typ_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_S : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_S_mutual :
(forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind degree_exp_wrt_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_S :
forall n1 e1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_S : lngen.

Lemma degree_typ_wrt_typ_O :
forall n1 A1,
  degree_typ_wrt_typ O A1 ->
  degree_typ_wrt_typ n1 A1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_O : lngen.

Lemma degree_exp_wrt_typ_O :
forall n1 e1,
  degree_exp_wrt_typ O e1 ->
  degree_exp_wrt_typ n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_O : lngen.

Lemma degree_exp_wrt_exp_O :
forall n1 e1,
  degree_exp_wrt_exp O e1 ->
  degree_exp_wrt_exp n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_O : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 e1 ->
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 e1 ->
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp_rec : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  degree_typ_wrt_typ 0 A1 ->
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_close_typ_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_close_exp_wrt_exp : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_typ : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  degree_exp_wrt_exp 0 e1 ->
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv :
forall A1 X1 n1,
  degree_typ_wrt_typ (S n1) (close_typ_wrt_typ_rec n1 X1 A1) ->
  degree_typ_wrt_typ n1 A1.
Proof.
pose proof degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1,
  degree_exp_wrt_typ (S n1) (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1 n2,
  degree_exp_wrt_typ n2 (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_typ n2 e1.
Proof.
pose proof degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual :
(forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv :
forall e1 X1 n1 n2,
  degree_exp_wrt_exp n2 (close_exp_wrt_typ_rec n1 X1 e1) ->
  degree_exp_wrt_exp n2 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv :
forall e1 x1 n1,
  degree_exp_wrt_exp (S n1) (close_exp_wrt_exp_rec n1 x1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_close_typ_wrt_typ_inv :
forall A1 X1,
  degree_typ_wrt_typ 1 (close_typ_wrt_typ X1 A1) ->
  degree_typ_wrt_typ 0 A1.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_typ_wrt_typ_close_typ_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_typ_inv :
forall e1 X1,
  degree_exp_wrt_typ 1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_typ 0 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_typ_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_close_exp_wrt_exp_inv :
forall e1 x1 n1,
  degree_exp_wrt_typ n1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_typ_close_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_typ_inv :
forall e1 X1 n1,
  degree_exp_wrt_exp n1 (close_exp_wrt_typ X1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_close_exp_wrt_exp_inv :
forall e1 x1,
  degree_exp_wrt_exp 1 (close_exp_wrt_exp x1 e1) ->
  degree_exp_wrt_exp 0 e1.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_close_exp_wrt_exp_inv : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_tt_rec    n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_tt_rec    :
forall A1 A2 n1,
  degree_typ_wrt_typ (S n1) A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (open_tt_rec    n1 A2 A1).
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_open_tt_rec    : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_te_rec     n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_te_rec     :
forall e1 A1 n1,
  degree_exp_wrt_typ (S n1) e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (open_te_rec     n1 A1 e1).
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_open_te_rec     : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_ee_rec     n2 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_ee_rec     :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_ee_rec     n2 e2 e1).
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_open_ee_rec     : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_te_rec     n2 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_te_rec     :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_te_rec     n2 A1 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_open_te_rec     : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_ee_rec     n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_ee_rec     :
forall e1 e2 n1,
  degree_exp_wrt_exp (S n1) e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (open_ee_rec     n1 e2 e1).
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_open_ee_rec     : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_tt :
forall A1 A2,
  degree_typ_wrt_typ 1 A1 ->
  degree_typ_wrt_typ 0 A2 ->
  degree_typ_wrt_typ 0 (open_tt A1 A2).
Proof.
unfold open_tt;      default_simp.
Qed.

Hint Resolve degree_typ_wrt_typ_open_tt : lngen.

Lemma degree_exp_wrt_typ_open_te :
forall e1 A1,
  degree_exp_wrt_typ 1 e1 ->
  degree_typ_wrt_typ 0 A1 ->
  degree_exp_wrt_typ 0 (open_te e1 A1).
Proof.
unfold open_te; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_open_te : lngen.

Lemma degree_exp_wrt_typ_open_ee   :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (open_ee   e1 e2).
Proof.
unfold open_ee; default_simp.
Qed.

Hint Resolve degree_exp_wrt_typ_open_ee   : lngen.

Lemma degree_exp_wrt_exp_open_te :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (open_te e1 A1).
Proof.
unfold open_te; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_open_te : lngen.

Lemma degree_exp_wrt_exp_open_ee   :
forall e1 e2,
  degree_exp_wrt_exp 1 e1 ->
  degree_exp_wrt_exp 0 e2 ->
  degree_exp_wrt_exp 0 (open_ee   e1 e2).
Proof.
unfold open_ee; default_simp.
Qed.

Hint Resolve degree_exp_wrt_exp_open_ee   : lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual :
(forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_tt_rec    n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv :
forall A1 A2 n1,
  degree_typ_wrt_typ n1 (open_tt_rec    n1 A2 A1) ->
  degree_typ_wrt_typ (S n1) A1.
Proof.
pose proof degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_te_rec     n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 (open_te_rec     n1 A1 e1) ->
  degree_exp_wrt_typ (S n1) e1.
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_ee_rec     n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1 n2,
  degree_exp_wrt_typ n1 (open_ee_rec     n2 e2 e1) ->
  degree_exp_wrt_typ n1 e1.
Proof.
pose proof degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual :
(forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_te_rec     n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv :
forall e1 A1 n1 n2,
  degree_exp_wrt_exp n1 (open_te_rec     n2 A1 e1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_rec_inv : lngen.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_ee_rec     n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv :
forall e1 e2 n1,
  degree_exp_wrt_exp n1 (open_ee_rec     n1 e2 e1) ->
  degree_exp_wrt_exp (S n1) e1.
Proof.
pose proof degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_rec_inv : lngen.

(* end hide *)

Lemma degree_typ_wrt_typ_open_typ_wrt_typ_inv :
forall A1 A2,
  degree_typ_wrt_typ 0 (open_tt A1 A2) ->
  degree_typ_wrt_typ 1 A1.
Proof.
unfold open_tt;      eauto with lngen.
Qed.

Hint Immediate degree_typ_wrt_typ_open_typ_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_typ_inv :
forall e1 A1,
  degree_exp_wrt_typ 0 (open_te e1 A1) ->
  degree_exp_wrt_typ 1 e1.
Proof.
unfold open_te; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_typ_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_typ_open_exp_wrt_exp_inv :
forall e1 e2 n1,
  degree_exp_wrt_typ n1 (open_ee   e1 e2) ->
  degree_exp_wrt_typ n1 e1.
Proof.
unfold open_ee; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_typ_open_exp_wrt_exp_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_typ_inv :
forall e1 A1 n1,
  degree_exp_wrt_exp n1 (open_te e1 A1) ->
  degree_exp_wrt_exp n1 e1.
Proof.
unfold open_te; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_typ_inv : lngen.

Lemma degree_exp_wrt_exp_open_exp_wrt_exp_inv :
forall e1 e2,
  degree_exp_wrt_exp 0 (open_ee   e1 e2) ->
  degree_exp_wrt_exp 1 e1.
Proof.
unfold open_ee; eauto with lngen.
Qed.

Hint Immediate degree_exp_wrt_exp_open_exp_wrt_exp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj_mutual :
(forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_inj :
forall A1 A2 X1 n1,
  close_typ_wrt_typ_rec n1 X1 A1 = close_typ_wrt_typ_rec n1 X1 A2 ->
  A1 = A2.
Proof.
pose proof close_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj_mutual :
(forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_inj :
forall e1 e2 X1 n1,
  close_exp_wrt_typ_rec n1 X1 e1 = close_exp_wrt_typ_rec n1 X1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_inj :
forall e1 e2 x1 n1,
  close_exp_wrt_exp_rec n1 x1 e1 = close_exp_wrt_exp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_inj :
forall A1 A2 X1,
  close_typ_wrt_typ X1 A1 = close_typ_wrt_typ X1 A2 ->
  A1 = A2.
Proof.
unfold close_typ_wrt_typ; eauto with lngen.
Qed.

Hint Immediate close_typ_wrt_typ_inj : lngen.

Lemma close_exp_wrt_typ_inj :
forall e1 e2 X1,
  close_exp_wrt_typ X1 e1 = close_exp_wrt_typ X1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_typ; eauto with lngen.
Qed.

Hint Immediate close_exp_wrt_typ_inj : lngen.

Lemma close_exp_wrt_exp_inj :
forall e1 e2 x1,
  close_exp_wrt_exp x1 e1 = close_exp_wrt_exp x1 e2 ->
  e1 = e2.
Proof.
unfold close_exp_wrt_exp; eauto with lngen.
Qed.

Hint Immediate close_exp_wrt_exp_inj : lngen.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  X1 `notin` fv_tt  A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_tt_rec    n1 (t_fvar  X1) A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_open_tt_rec    :
forall A1 X1 n1,
  X1 `notin` fv_tt  A1 ->
  close_typ_wrt_typ_rec n1 X1 (open_tt_rec    n1 (t_fvar  X1) A1) = A1.
Proof.
pose proof close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_typ_wrt_typ_rec_open_tt_rec    : lngen.
Hint Rewrite close_typ_wrt_typ_rec_open_tt_rec    using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  X1 `notin` fv_te   e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_te_rec     n1 (t_fvar  X1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_open_te_rec     :
forall e1 X1 n1,
  X1 `notin` fv_te   e1 ->
  close_exp_wrt_typ_rec n1 X1 (open_te_rec     n1 (t_fvar  X1) e1) = e1.
Proof.
pose proof close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_typ_rec_open_te_rec     : lngen.
Hint Rewrite close_exp_wrt_typ_rec_open_te_rec     using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fv_ee    e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_ee_rec     n1 (e_fvar  x1) e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_open_ee_rec     :
forall e1 x1 n1,
  x1 `notin` fv_ee    e1 ->
  close_exp_wrt_exp_rec n1 x1 (open_ee_rec     n1 (e_fvar  x1) e1) = e1.
Proof.
pose proof close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_exp_rec_open_ee_rec     : lngen.
Hint Rewrite close_exp_wrt_exp_rec_open_ee_rec     using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_open_tt :
forall A1 X1,
  X1 `notin` fv_tt  A1 ->
  close_typ_wrt_typ X1 (open_tt A1 (t_fvar  X1)) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_tt;      default_simp.
Qed.

Hint Resolve close_typ_wrt_typ_open_tt : lngen.
Hint Rewrite close_typ_wrt_typ_open_tt using solve [auto] : lngen.

Lemma close_exp_wrt_typ_open_te :
forall e1 X1,
  X1 `notin` fv_te   e1 ->
  close_exp_wrt_typ X1 (open_te e1 (t_fvar  X1)) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_te; default_simp.
Qed.

Hint Resolve close_exp_wrt_typ_open_te : lngen.
Hint Rewrite close_exp_wrt_typ_open_te using solve [auto] : lngen.

Lemma close_exp_wrt_exp_open_ee   :
forall e1 x1,
  x1 `notin` fv_ee    e1 ->
  close_exp_wrt_exp x1 (open_ee   e1 (e_fvar  x1)) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_ee; default_simp.
Qed.

Hint Resolve close_exp_wrt_exp_open_ee   : lngen.
Hint Rewrite close_exp_wrt_exp_open_ee   using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  open_tt_rec    n1 (t_fvar  X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  open_tt_rec    n1 (t_fvar  X1) (close_typ_wrt_typ_rec n1 X1 A1) = A1.
Proof.
pose proof open_typ_wrt_typ_rec_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_typ_wrt_typ_rec_close_typ_wrt_typ_rec : lngen.
Hint Rewrite open_typ_wrt_typ_rec_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  open_te_rec     n1 (t_fvar  X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  open_te_rec     n1 (t_fvar  X1) (close_exp_wrt_typ_rec n1 X1 e1) = e1.
Proof.
pose proof open_exp_wrt_typ_rec_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_typ_rec_close_exp_wrt_typ_rec : lngen.
Hint Rewrite open_exp_wrt_typ_rec_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  open_ee_rec     n1 (e_fvar  x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  open_ee_rec     n1 (e_fvar  x1) (close_exp_wrt_exp_rec n1 x1 e1) = e1.
Proof.
pose proof open_exp_wrt_exp_rec_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_exp_rec_close_exp_wrt_exp_rec : lngen.
Hint Rewrite open_exp_wrt_exp_rec_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_close_typ_wrt_typ :
forall A1 X1,
  open_tt (close_typ_wrt_typ X1 A1) (t_fvar  X1) = A1.
Proof.
unfold close_typ_wrt_typ; unfold open_tt;      default_simp.
Qed.

Hint Resolve open_typ_wrt_typ_close_typ_wrt_typ : lngen.
Hint Rewrite open_typ_wrt_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_typ_close_exp_wrt_typ :
forall e1 X1,
  open_te (close_exp_wrt_typ X1 e1) (t_fvar  X1) = e1.
Proof.
unfold close_exp_wrt_typ; unfold open_te; default_simp.
Qed.

Hint Resolve open_exp_wrt_typ_close_exp_wrt_typ : lngen.
Hint Rewrite open_exp_wrt_typ_close_exp_wrt_typ using solve [auto] : lngen.

Lemma open_exp_wrt_exp_close_exp_wrt_exp :
forall e1 x1,
  open_ee   (close_exp_wrt_exp x1 e1) (e_fvar  x1) = e1.
Proof.
unfold close_exp_wrt_exp; unfold open_ee; default_simp.
Qed.

Hint Resolve open_exp_wrt_exp_close_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj_mutual :
(forall A2 A1 X1 n1,
  X1 `notin` fv_tt  A2 ->
  X1 `notin` fv_tt  A1 ->
  open_tt_rec    n1 (t_fvar  X1) A2 = open_tt_rec    n1 (t_fvar  X1) A1 ->
  A2 = A1).
Proof.
apply_mutual_ind typ_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_inj :
forall A2 A1 X1 n1,
  X1 `notin` fv_tt  A2 ->
  X1 `notin` fv_tt  A1 ->
  open_tt_rec    n1 (t_fvar  X1) A2 = open_tt_rec    n1 (t_fvar  X1) A1 ->
  A2 = A1.
Proof.
pose proof open_typ_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_typ_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj_mutual :
(forall e2 e1 X1 n1,
  X1 `notin` fv_te   e2 ->
  X1 `notin` fv_te   e1 ->
  open_te_rec     n1 (t_fvar  X1) e2 = open_te_rec     n1 (t_fvar  X1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_inj :
forall e2 e1 X1 n1,
  X1 `notin` fv_te   e2 ->
  X1 `notin` fv_te   e1 ->
  open_te_rec     n1 (t_fvar  X1) e2 = open_te_rec     n1 (t_fvar  X1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_typ_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_exp_wrt_typ_rec_inj : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fv_ee    e2 ->
  x1 `notin` fv_ee    e1 ->
  open_ee_rec     n1 (e_fvar  x1) e2 = open_ee_rec     n1 (e_fvar  x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind exp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_ee    e2 ->
  x1 `notin` fv_ee    e1 ->
  open_ee_rec     n1 (e_fvar  x1) e2 = open_ee_rec     n1 (e_fvar  x1) e1 ->
  e2 = e1.
Proof.
pose proof open_exp_wrt_exp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_exp_wrt_exp_rec_inj : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_inj :
forall A2 A1 X1,
  X1 `notin` fv_tt  A2 ->
  X1 `notin` fv_tt  A1 ->
  open_tt A2 (t_fvar  X1) = open_tt A1 (t_fvar  X1) ->
  A2 = A1.
Proof.
unfold open_tt;      eauto with lngen.
Qed.

Hint Immediate open_typ_wrt_typ_inj : lngen.

Lemma open_exp_wrt_typ_inj :
forall e2 e1 X1,
  X1 `notin` fv_te   e2 ->
  X1 `notin` fv_te   e1 ->
  open_te e2 (t_fvar  X1) = open_te e1 (t_fvar  X1) ->
  e2 = e1.
Proof.
unfold open_te; eauto with lngen.
Qed.

Hint Immediate open_exp_wrt_typ_inj : lngen.

Lemma open_exp_wrt_exp_inj :
forall e2 e1 x1,
  x1 `notin` fv_ee    e2 ->
  x1 `notin` fv_ee    e1 ->
  open_ee   e2 (e_fvar  x1) = open_ee   e1 (e_fvar  x1) ->
  e2 = e1.
Proof.
unfold open_ee; eauto with lngen.
Qed.

Hint Immediate open_exp_wrt_exp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_typ_wrt_typ_of_lc_typ_mutual :
(forall A1,
  type   A1 ->
  degree_typ_wrt_typ 0 A1).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_typ_wrt_typ_of_type   :
forall A1,
  type   A1 ->
  degree_typ_wrt_typ 0 A1.
Proof.
pose proof degree_typ_wrt_typ_of_lc_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_typ_wrt_typ_of_type   : lngen.

(* begin hide *)

Lemma degree_exp_wrt_typ_of_lc_exp_mutual :
(forall e1,
  expr   e1 ->
  degree_exp_wrt_typ 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_typ_of_expr   :
forall e1,
  expr   e1 ->
  degree_exp_wrt_typ 0 e1.
Proof.
pose proof degree_exp_wrt_typ_of_lc_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_typ_of_expr   : lngen.

(* begin hide *)

Lemma degree_exp_wrt_exp_of_lc_exp_mutual :
(forall e1,
  expr   e1 ->
  degree_exp_wrt_exp 0 e1).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let X1 := fresh "X1" in pick_fresh X1;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_exp_wrt_exp_of_expr   :
forall e1,
  expr   e1 ->
  degree_exp_wrt_exp 0 e1.
Proof.
pose proof degree_exp_wrt_exp_of_lc_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_exp_wrt_exp_of_expr   : lngen.

(* begin hide *)

Lemma lc_typ_of_degree_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  degree_typ_wrt_typ 0 A1 ->
  type   A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_degree :
forall A1,
  degree_typ_wrt_typ 0 A1 ->
  type   A1.
Proof.
intros A1; intros;
pose proof (lc_typ_of_degree_size_mutual (size_typ A1));
intuition eauto.
Qed.

Hint Resolve lc_typ_of_degree : lngen.

(* begin hide *)

Lemma lc_exp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  expr   e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutind;
default_simp;
(* non-trivial cases *)
constructor; default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_degree :
forall e1,
  degree_exp_wrt_typ 0 e1 ->
  degree_exp_wrt_exp 0 e1 ->
  expr   e1.
Proof.
intros e1; intros;
pose proof (lc_exp_of_degree_size_mutual (size_exp e1));
intuition eauto.
Qed.

Hint Resolve lc_exp_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_typ_wrt_typ_of_type   in J1; clear H
          end).

Ltac exp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_exp_wrt_typ_of_expr   in J1;
              let J2 := fresh in pose proof H as J2; apply degree_exp_wrt_exp_of_expr   in J2; clear H
          end).

Lemma lc_t_all_exists :
forall X1 B1,
  type   (open_tt B1 (t_fvar  X1)) ->
  type   (t_all B1).
Proof.
intros; typ_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_e_abs_exists :
forall x1 e1,
  expr   (open_ee   e1 (e_fvar  x1)) ->
  expr   (e_abs e1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_e_tabs_exists :
forall X1 e1,
  expr   (open_te e1 (t_fvar  X1)) ->
  expr   (e_tabs e1).
Proof.
intros; exp_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (type   (t_all _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_t_all_exists X1) : core.

Hint Extern 1 (expr   (e_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_e_abs_exists x1) : core.

Hint Extern 1 (expr   (e_tabs _)) =>
  let X1 := fresh in
  pick_fresh X1;
  apply (lc_e_tabs_exists X1) : core.

Lemma lc_body_typ_wrt_typ :
forall A1 A2,
  body_typ_wrt_typ A1 ->
  type   A2 ->
  type   (open_tt A1 A2).
Proof.
unfold body_typ_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
typ_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_typ_wrt_typ : lngen.

Lemma lc_body_exp_wrt_typ :
forall e1 A1,
  body_exp_wrt_typ e1 ->
  type   A1 ->
  expr   (open_te e1 A1).
Proof.
unfold body_exp_wrt_typ;
default_simp;
let X1 := fresh "x" in
pick_fresh X1;
specialize_all X1;
exp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_exp_wrt_typ : lngen.

Lemma lc_body_exp_wrt_exp :
forall e1 e2,
  body_exp_wrt_exp e1 ->
  expr   e2 ->
  expr   (open_ee   e1 e2).
Proof.
unfold body_exp_wrt_exp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
exp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_exp_wrt_exp : lngen.

Lemma lc_body_t_all_1 :
forall B1,
  type   (t_all B1) ->
  body_typ_wrt_typ B1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_t_all_1 : lngen.

Lemma lc_body_e_abs_1 :
forall e1,
  expr   (e_abs e1) ->
  body_exp_wrt_exp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_e_abs_1 : lngen.

Lemma lc_body_e_tabs_1 :
forall e1,
  expr   (e_tabs e1) ->
  body_exp_wrt_typ e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_e_tabs_1 : lngen.

(* begin hide *)

Lemma lc_typ_unique_mutual :
(forall A1 (proof2 proof3 : type   A1), proof2 = proof3).
Proof.
apply_mutual_ind lc_typ_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_typ_unique :
forall A1 (proof2 proof3 : type   A1), proof2 = proof3.
Proof.
pose proof lc_typ_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_typ_unique : lngen.

(* begin hide *)

Lemma lc_exp_unique_mutual :
(forall e1 (proof2 proof3 : expr   e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_exp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_exp_unique :
forall e1 (proof2 proof3 : expr   e1), proof2 = proof3.
Proof.
pose proof lc_exp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_exp_unique : lngen.

(* begin hide *)

Lemma lc_typ_of_lc_set_typ_mutual :
(forall A1, lc_set_typ A1 -> type   A1).
Proof.
apply_mutual_ind lc_set_typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_typ_of_lc_set_typ :
forall A1, lc_set_typ A1 -> type   A1.
Proof.
pose proof lc_typ_of_lc_set_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_typ_of_lc_set_typ : lngen.

(* begin hide *)

Lemma lc_exp_of_lc_set_exp_mutual :
(forall e1, lc_set_exp e1 -> expr   e1).
Proof.
apply_mutual_ind lc_set_exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_exp_of_lc_set_exp :
forall e1, lc_set_exp e1 -> expr   e1.
Proof.
pose proof lc_exp_of_lc_set_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_exp_of_lc_set_exp : lngen.

(* begin hide *)

Lemma lc_set_typ_of_lc_typ_size_mutual :
forall i1,
(forall A1,
  size_typ A1 = i1 ->
  type   A1 ->
  lc_set_typ A1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind typ_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_typ_of_lc_typ   :
forall A1,
  type   A1 ->
  lc_set_typ A1.
Proof.
intros A1; intros;
pose proof (lc_set_typ_of_lc_typ_size_mutual (size_typ A1));
intuition eauto.
Qed.

Hint Resolve lc_set_typ_of_lc_typ   : lngen.

(* begin hide *)

Lemma lc_set_exp_of_lc_exp_size_mutual :
forall i1,
(forall e1,
  size_exp e1 = i1 ->
  expr   e1 ->
  lc_set_exp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind exp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_exp_of_lc_exp];
default_simp; eapply_first_lt_hyp;
(* instantiate the size *)
match goal with
  | |- _ = _ => reflexivity
  | _ => idtac
end;
instantiate;
(* everything should be easy now *)
default_simp.
Qed.

(* end hide *)

Lemma lc_set_exp_of_lc_exp  :
forall e1,
  expr   e1 ->
  lc_set_exp e1.
Proof.
intros e1; intros;
pose proof (lc_set_exp_of_lc_exp_size_mutual (size_exp e1));
intuition eauto.
Qed.

Hint Resolve lc_set_exp_of_lc_exp   : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` fv_tt  A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A1 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 `notin` fv_tt  A1 ->
  close_typ_wrt_typ_rec n1 X1 A1 = A1.
Proof.
pose proof close_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve close_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
Hint Rewrite close_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` fv_te   e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  X1 `notin` fv_te   e1 ->
  close_exp_wrt_typ_rec n1 X1 e1 = e1.
Proof.
pose proof close_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
Hint Rewrite close_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fv_ee    e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e1 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 `notin` fv_ee    e1 ->
  close_exp_wrt_exp_rec n1 x1 e1 = e1.
Proof.
pose proof close_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite close_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma close_typ_wrt_typ_type   :
forall A1 X1,
  type   A1 ->
  X1 `notin` fv_tt  A1 ->
  close_typ_wrt_typ X1 A1 = A1.
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve close_typ_wrt_typ_type   : lngen.
Hint Rewrite close_typ_wrt_typ_type   using solve [auto] : lngen.

Lemma close_exp_wrt_typ_expr   :
forall e1 X1,
  expr   e1 ->
  X1 `notin` fv_te   e1 ->
  close_exp_wrt_typ X1 e1 = e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve close_exp_wrt_typ_expr   : lngen.
Hint Rewrite close_exp_wrt_typ_expr   using solve [auto] : lngen.

Lemma close_exp_wrt_exp_expr   :
forall e1 x1,
  expr   e1 ->
  x1 `notin` fv_ee    e1 ->
  close_exp_wrt_exp x1 e1 = e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve close_exp_wrt_exp_expr   : lngen.
Hint Rewrite close_exp_wrt_exp_expr   using solve [auto] : lngen.

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual :
(forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_tt_rec    n1 A1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_typ_wrt_typ_rec_degree_typ_wrt_typ :
forall A2 A1 n1,
  degree_typ_wrt_typ n1 A2 ->
  open_tt_rec    n1 A1 A2 = A2.
Proof.
pose proof open_typ_wrt_typ_rec_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve open_typ_wrt_typ_rec_degree_typ_wrt_typ : lngen.
Hint Rewrite open_typ_wrt_typ_rec_degree_typ_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual :
(forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_te_rec     n1 A1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_typ_rec_degree_exp_wrt_typ :
forall e1 A1 n1,
  degree_exp_wrt_typ n1 e1 ->
  open_te_rec     n1 A1 e1 = e1.
Proof.
pose proof open_exp_wrt_typ_rec_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_typ_rec_degree_exp_wrt_typ : lngen.
Hint Rewrite open_exp_wrt_typ_rec_degree_exp_wrt_typ using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual :
(forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_ee_rec     n1 e1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_exp_wrt_exp_rec_degree_exp_wrt_exp :
forall e2 e1 n1,
  degree_exp_wrt_exp n1 e2 ->
  open_ee_rec     n1 e1 e2 = e2.
Proof.
pose proof open_exp_wrt_exp_rec_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_exp_wrt_exp_rec_degree_exp_wrt_exp : lngen.
Hint Rewrite open_exp_wrt_exp_rec_degree_exp_wrt_exp using solve [auto] : lngen.

(* end hide *)

Lemma open_typ_wrt_typ_type   :
forall A2 A1,
  type   A2 ->
  open_tt A2 A1 = A2.
Proof.
unfold open_tt;      default_simp.
Qed.

Hint Resolve open_typ_wrt_typ_type   : lngen.
Hint Rewrite open_typ_wrt_typ_type   using solve [auto] : lngen.

Lemma open_exp_wrt_typ_expr   :
forall e1 A1,
  expr   e1 ->
  open_te e1 A1 = e1.
Proof.
unfold open_te; default_simp.
Qed.

Hint Resolve open_exp_wrt_typ_expr   : lngen.
Hint Rewrite open_exp_wrt_typ_expr   using solve [auto] : lngen.

Lemma open_exp_wrt_exp_expr   :
forall e2 e1,
  expr   e2 ->
  open_ee   e2 e1 = e2.
Proof.
unfold open_ee; default_simp.
Qed.

Hint Resolve open_exp_wrt_exp_expr   : lngen.
Hint Rewrite open_exp_wrt_exp_expr   using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma tfv_typ_close_typ_wrt_typ_rec_mutual :
(forall A1 X1 n1,
  fv_tt  (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (fv_tt  A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tfv_typ_close_typ_wrt_typ_rec :
forall A1 X1 n1,
  fv_tt  (close_typ_wrt_typ_rec n1 X1 A1) [=] remove X1 (fv_tt  A1).
Proof.
pose proof tfv_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_typ_close_typ_wrt_typ_rec : lngen.
Hint Rewrite tfv_typ_close_typ_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tfv_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  fv_te   (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (fv_te   e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tfv_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  fv_te   (close_exp_wrt_typ_rec n1 X1 e1) [=] remove X1 (fv_te   e1).
Proof.
pose proof tfv_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_close_exp_wrt_typ_rec : lngen.
Hint Rewrite tfv_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma tfv_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  fv_te   (close_exp_wrt_exp_rec n1 x1 e1) [=] fv_te   e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tfv_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  fv_te   (close_exp_wrt_exp_rec n1 x1 e1) [=] fv_te   e1.
Proof.
pose proof tfv_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite tfv_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 X1 n1,
  fv_ee    (close_exp_wrt_typ_rec n1 X1 e1) [=] fv_ee    e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_close_exp_wrt_typ_rec :
forall e1 X1 n1,
  fv_ee    (close_exp_wrt_typ_rec n1 X1 e1) [=] fv_ee    e1.
Proof.
pose proof fv_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_close_exp_wrt_typ_rec : lngen.
Hint Rewrite fv_exp_close_exp_wrt_typ_rec using solve [auto] : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 x1 n1,
  fv_ee    (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fv_ee    e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_close_exp_wrt_exp_rec :
forall e1 x1 n1,
  fv_ee    (close_exp_wrt_exp_rec n1 x1 e1) [=] remove x1 (fv_ee    e1).
Proof.
pose proof fv_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_close_exp_wrt_exp_rec : lngen.
Hint Rewrite fv_exp_close_exp_wrt_exp_rec using solve [auto] : lngen.

(* end hide *)

Lemma tfv_typ_close_typ_wrt_typ :
forall A1 X1,
  fv_tt  (close_typ_wrt_typ X1 A1) [=] remove X1 (fv_tt  A1).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve tfv_typ_close_typ_wrt_typ : lngen.
Hint Rewrite tfv_typ_close_typ_wrt_typ using solve [auto] : lngen.

Lemma tfv_exp_close_exp_wrt_typ :
forall e1 X1,
  fv_te   (close_exp_wrt_typ X1 e1) [=] remove X1 (fv_te   e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve tfv_exp_close_exp_wrt_typ : lngen.
Hint Rewrite tfv_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma tfv_exp_close_exp_wrt_exp :
forall e1 x1,
  fv_te   (close_exp_wrt_exp x1 e1) [=] fv_te   e1.
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve tfv_exp_close_exp_wrt_exp : lngen.
Hint Rewrite tfv_exp_close_exp_wrt_exp using solve [auto] : lngen.

Lemma fv_exp_close_exp_wrt_typ :
forall e1 X1,
  fv_ee    (close_exp_wrt_typ X1 e1) [=] fv_ee    e1.
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve fv_exp_close_exp_wrt_typ : lngen.
Hint Rewrite fv_exp_close_exp_wrt_typ using solve [auto] : lngen.

Lemma fv_exp_close_exp_wrt_exp :
forall e1 x1,
  fv_ee    (close_exp_wrt_exp x1 e1) [=] remove x1 (fv_ee    e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve fv_exp_close_exp_wrt_exp : lngen.
Hint Rewrite fv_exp_close_exp_wrt_exp using solve [auto] : lngen.

(* begin hide *)

Lemma tfv_typ_open_typ_wrt_typ_rec_lower_mutual :
(forall A1 A2 n1,
  fv_tt  A1 [<=] fv_tt  (open_tt_rec    n1 A2 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tfv_typ_open_typ_wrt_typ_rec_lower :
forall A1 A2 n1,
  fv_tt  A1 [<=] fv_tt  (open_tt_rec    n1 A2 A1).
Proof.
pose proof tfv_typ_open_typ_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_typ_open_typ_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tfv_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  fv_te   e1 [<=] fv_te   (open_te_rec     n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tfv_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  fv_te   e1 [<=] fv_te   (open_te_rec     n1 A1 e1).
Proof.
pose proof tfv_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma tfv_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  fv_te   e1 [<=] fv_te   (open_ee_rec     n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tfv_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  fv_te   e1 [<=] fv_te   (open_ee_rec     n1 e2 e1).
Proof.
pose proof tfv_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_typ_rec_lower_mutual :
(forall e1 A1 n1,
  fv_ee    e1 [<=] fv_ee    (open_te_rec     n1 A1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_typ_rec_lower :
forall e1 A1 n1,
  fv_ee    e1 [<=] fv_ee    (open_te_rec     n1 A1 e1).
Proof.
pose proof fv_exp_open_exp_wrt_typ_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_open_exp_wrt_typ_rec_lower : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_lower_mutual :
(forall e1 e2 n1,
  fv_ee    e1 [<=] fv_ee    (open_ee_rec     n1 e2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_lower :
forall e1 e2 n1,
  fv_ee    e1 [<=] fv_ee    (open_ee_rec     n1 e2 e1).
Proof.
pose proof fv_exp_open_exp_wrt_exp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_open_exp_wrt_exp_rec_lower : lngen.

(* end hide *)

Lemma tfv_typ_open_typ_wrt_typ_lower :
forall A1 A2,
  fv_tt  A1 [<=] fv_tt  (open_tt A1 A2).
Proof.
unfold open_tt;      default_simp.
Qed.

Hint Resolve tfv_typ_open_typ_wrt_typ_lower : lngen.

Lemma tfv_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  fv_te   e1 [<=] fv_te   (open_te e1 A1).
Proof.
unfold open_te; default_simp.
Qed.

Hint Resolve tfv_exp_open_exp_wrt_typ_lower : lngen.

Lemma tfv_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fv_te   e1 [<=] fv_te   (open_ee   e1 e2).
Proof.
unfold open_ee; default_simp.
Qed.

Hint Resolve tfv_exp_open_exp_wrt_exp_lower : lngen.

Lemma fv_exp_open_exp_wrt_typ_lower :
forall e1 A1,
  fv_ee    e1 [<=] fv_ee    (open_te e1 A1).
Proof.
unfold open_te; default_simp.
Qed.

Hint Resolve fv_exp_open_exp_wrt_typ_lower : lngen.

Lemma fv_exp_open_exp_wrt_exp_lower :
forall e1 e2,
  fv_ee    e1 [<=] fv_ee    (open_ee   e1 e2).
Proof.
unfold open_ee; default_simp.
Qed.

Hint Resolve fv_exp_open_exp_wrt_exp_lower : lngen.

(* begin hide *)

Lemma tfv_typ_open_typ_wrt_typ_rec_upper_mutual :
(forall A1 A2 n1,
  fv_tt  (open_tt_rec    n1 A2 A1) [<=] fv_tt  A2 `union` fv_tt  A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tfv_typ_open_typ_wrt_typ_rec_upper :
forall A1 A2 n1,
  fv_tt  (open_tt_rec    n1 A2 A1) [<=] fv_tt  A2 `union` fv_tt  A1.
Proof.
pose proof tfv_typ_open_typ_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_typ_open_typ_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tfv_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  fv_te   (open_te_rec     n1 A1 e1) [<=] fv_tt  A1 `union` fv_te   e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tfv_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  fv_te   (open_te_rec     n1 A1 e1) [<=] fv_tt  A1 `union` fv_te   e1.
Proof.
pose proof tfv_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma tfv_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  fv_te   (open_ee_rec     n1 e2 e1) [<=] fv_te   e2 `union` fv_te   e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma tfv_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  fv_te   (open_ee_rec     n1 e2 e1) [<=] fv_te   e2 `union` fv_te   e1.
Proof.
pose proof tfv_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_typ_rec_upper_mutual :
(forall e1 A1 n1,
  fv_ee    (open_te_rec     n1 A1 e1) [<=] fv_ee    e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_typ_rec_upper :
forall e1 A1 n1,
  fv_ee    (open_te_rec     n1 A1 e1) [<=] fv_ee    e1.
Proof.
pose proof fv_exp_open_exp_wrt_typ_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_open_exp_wrt_typ_rec_upper : lngen.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_upper_mutual :
(forall e1 e2 n1,
  fv_ee    (open_ee_rec     n1 e2 e1) [<=] fv_ee    e2 `union` fv_ee    e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_exp_open_exp_wrt_exp_rec_upper :
forall e1 e2 n1,
  fv_ee    (open_ee_rec     n1 e2 e1) [<=] fv_ee    e2 `union` fv_ee    e1.
Proof.
pose proof fv_exp_open_exp_wrt_exp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_open_exp_wrt_exp_rec_upper : lngen.

(* end hide *)

Lemma tfv_typ_open_typ_wrt_typ_upper :
forall A1 A2,
  fv_tt  (open_tt A1 A2) [<=] fv_tt  A2 `union` fv_tt  A1.
Proof.
unfold open_tt;      default_simp.
Qed.

Hint Resolve tfv_typ_open_typ_wrt_typ_upper : lngen.

Lemma tfv_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  fv_te   (open_te e1 A1) [<=] fv_tt  A1 `union` fv_te   e1.
Proof.
unfold open_te; default_simp.
Qed.

Hint Resolve tfv_exp_open_exp_wrt_typ_upper : lngen.

Lemma tfv_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fv_te   (open_ee   e1 e2) [<=] fv_te   e2 `union` fv_te   e1.
Proof.
unfold open_ee; default_simp.
Qed.

Hint Resolve tfv_exp_open_exp_wrt_exp_upper : lngen.

Lemma fv_exp_open_exp_wrt_typ_upper :
forall e1 A1,
  fv_ee    (open_te e1 A1) [<=] fv_ee    e1.
Proof.
unfold open_te; default_simp.
Qed.

Hint Resolve fv_exp_open_exp_wrt_typ_upper : lngen.

Lemma fv_exp_open_exp_wrt_exp_upper :
forall e1 e2,
  fv_ee    (open_ee   e1 e2) [<=] fv_ee    e2 `union` fv_ee    e1.
Proof.
unfold open_ee; default_simp.
Qed.

Hint Resolve fv_exp_open_exp_wrt_exp_upper : lngen.

(* begin hide *)

Lemma tfv_typ_tsubst_typ_fresh_mutual :
(forall A1 A2 X1,
  X1 `notin` fv_tt  A1 ->
  fv_tt  (subst_tt A2 X1 A1) [=] fv_tt  A1).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tfv_typ_tsubst_typ_fresh :
forall A1 A2 X1,
  X1 `notin` fv_tt  A1 ->
  fv_tt  (subst_tt A2 X1 A1) [=] fv_tt  A1.
Proof.
pose proof tfv_typ_tsubst_typ_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_typ_tsubst_typ_fresh : lngen.
Hint Rewrite tfv_typ_tsubst_typ_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tfv_exp_tsubst_exp_fresh_mutual :
(forall e1 A1 X1,
  X1 `notin` fv_te   e1 ->
  fv_te   (subst_te A1 X1 e1) [=] fv_te   e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tfv_exp_tsubst_exp_fresh :
forall e1 A1 X1,
  X1 `notin` fv_te   e1 ->
  fv_te   (subst_te A1 X1 e1) [=] fv_te   e1.
Proof.
pose proof tfv_exp_tsubst_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_tsubst_exp_fresh : lngen.
Hint Rewrite tfv_exp_tsubst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tfv_exp_subst_exp_fresh_mutual :
(forall e1 A1 X1,
  fv_ee    (subst_te A1 X1 e1) [=] fv_ee    e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tfv_exp_subst_exp_fresh :
forall e1 A1 X1,
  fv_ee    (subst_te A1 X1 e1) [=] fv_ee    e1.
Proof.
pose proof tfv_exp_subst_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_subst_exp_fresh : lngen.
Hint Rewrite tfv_exp_subst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_ee    e1 ->
  fv_ee    (subst_ee  e2 x1 e1) [=] fv_ee    e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_subst_exp_fresh :
forall e1 e2 x1,
  x1 `notin` fv_ee    e1 ->
  fv_ee    (subst_ee  e2 x1 e1) [=] fv_ee    e1.
Proof.
pose proof fv_exp_subst_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_subst_exp_fresh : lngen.
Hint Rewrite fv_exp_subst_exp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma tfv_typ_tsubst_typ_lower_mutual :
(forall A1 A2 X1,
  remove X1 (fv_tt  A1) [<=] fv_tt  (subst_tt A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tfv_typ_tsubst_typ_lower :
forall A1 A2 X1,
  remove X1 (fv_tt  A1) [<=] fv_tt  (subst_tt A2 X1 A1).
Proof.
pose proof tfv_typ_tsubst_typ_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_typ_tsubst_typ_lower : lngen.

(* begin hide *)

Lemma tfv_exp_tsubst_exp_lower_mutual :
(forall e1 A1 X1,
  remove X1 (fv_te   e1) [<=] fv_te   (subst_te A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tfv_exp_tsubst_exp_lower :
forall e1 A1 X1,
  remove X1 (fv_te   e1) [<=] fv_te   (subst_te A1 X1 e1).
Proof.
pose proof tfv_exp_tsubst_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_tsubst_exp_lower : lngen.

(* begin hide *)

Lemma tfv_exp_subst_exp_lower_mutual :
(forall e1 e2 x1,
  fv_te   e1 [<=] fv_te   (subst_ee  e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tfv_exp_subst_exp_lower :
forall e1 e2 x1,
  fv_te   e1 [<=] fv_te   (subst_ee  e2 x1 e1).
Proof.
pose proof tfv_exp_subst_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_subst_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_tsubst_exp_lower_mutual :
(forall e1 A1 X1,
  fv_ee    e1 [<=] fv_ee    (subst_te A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_tsubst_exp_lower :
forall e1 A1 X1,
  fv_ee    e1 [<=] fv_ee    (subst_te A1 X1 e1).
Proof.
pose proof fv_exp_tsubst_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_tsubst_exp_lower : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_ee    e1) [<=] fv_ee    (subst_ee  e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_subst_exp_lower :
forall e1 e2 x1,
  remove x1 (fv_ee    e1) [<=] fv_ee    (subst_ee  e2 x1 e1).
Proof.
pose proof fv_exp_subst_exp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_subst_exp_lower : lngen.

(* begin hide *)

Lemma tfv_typ_tsubst_typ_notin_mutual :
(forall A1 A2 X1 X2,
  X2 `notin` fv_tt  A1 ->
  X2 `notin` fv_tt  A2 ->
  X2 `notin` fv_tt  (subst_tt A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tfv_typ_tsubst_typ_notin :
forall A1 A2 X1 X2,
  X2 `notin` fv_tt  A1 ->
  X2 `notin` fv_tt  A2 ->
  X2 `notin` fv_tt  (subst_tt A2 X1 A1).
Proof.
pose proof tfv_typ_tsubst_typ_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_typ_tsubst_typ_notin : lngen.

(* begin hide *)

Lemma tfv_exp_tsubst_exp_notin_mutual :
(forall e1 A1 X1 X2,
  X2 `notin` fv_te   e1 ->
  X2 `notin` fv_tt  A1 ->
  X2 `notin` fv_te   (subst_te A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tfv_exp_tsubst_exp_notin :
forall e1 A1 X1 X2,
  X2 `notin` fv_te   e1 ->
  X2 `notin` fv_tt  A1 ->
  X2 `notin` fv_te   (subst_te A1 X1 e1).
Proof.
pose proof tfv_exp_tsubst_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_tsubst_exp_notin : lngen.

(* begin hide *)

Lemma tfv_exp_subst_exp_notin_mutual :
(forall e1 e2 x1 X1,
  X1 `notin` fv_te   e1 ->
  X1 `notin` fv_te   e2 ->
  X1 `notin` fv_te   (subst_ee  e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tfv_exp_subst_exp_notin :
forall e1 e2 x1 X1,
  X1 `notin` fv_te   e1 ->
  X1 `notin` fv_te   e2 ->
  X1 `notin` fv_te   (subst_ee  e2 x1 e1).
Proof.
pose proof tfv_exp_subst_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_subst_exp_notin : lngen.

(* begin hide *)

Lemma fv_exp_tsubst_exp_notin_mutual :
(forall e1 A1 X1 x1,
  x1 `notin` fv_ee    e1 ->
  x1 `notin` fv_ee    (subst_te A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_tsubst_exp_notin :
forall e1 A1 X1 x1,
  x1 `notin` fv_ee    e1 ->
  x1 `notin` fv_ee    (subst_te A1 X1 e1).
Proof.
pose proof fv_exp_tsubst_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_tsubst_exp_notin : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_ee    e1 ->
  x2 `notin` fv_ee    e2 ->
  x2 `notin` fv_ee    (subst_ee  e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_subst_exp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_ee    e1 ->
  x2 `notin` fv_ee    e2 ->
  x2 `notin` fv_ee    (subst_ee  e2 x1 e1).
Proof.
pose proof fv_exp_subst_exp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_subst_exp_notin : lngen.

(* begin hide *)

Lemma tfv_typ_tsubst_typ_upper_mutual :
(forall A1 A2 X1,
  fv_tt  (subst_tt A2 X1 A1) [<=] fv_tt  A2 `union` remove X1 (fv_tt  A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tfv_typ_tsubst_typ_upper :
forall A1 A2 X1,
  fv_tt  (subst_tt A2 X1 A1) [<=] fv_tt  A2 `union` remove X1 (fv_tt  A1).
Proof.
pose proof tfv_typ_tsubst_typ_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_typ_tsubst_typ_upper : lngen.

(* begin hide *)

Lemma tfv_exp_tsubst_exp_upper_mutual :
(forall e1 A1 X1,
  fv_te   (subst_te A1 X1 e1) [<=] fv_tt  A1 `union` remove X1 (fv_te   e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tfv_exp_tsubst_exp_upper :
forall e1 A1 X1,
  fv_te   (subst_te A1 X1 e1) [<=] fv_tt  A1 `union` remove X1 (fv_te   e1).
Proof.
pose proof tfv_exp_tsubst_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_tsubst_exp_upper : lngen.

(* begin hide *)

Lemma tfv_exp_subst_exp_upper_mutual :
(forall e1 e2 x1,
  fv_te   (subst_ee  e2 x1 e1) [<=] fv_te   e2 `union` fv_te   e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma tfv_exp_subst_exp_upper :
forall e1 e2 x1,
  fv_te   (subst_ee  e2 x1 e1) [<=] fv_te   e2 `union` fv_te   e1.
Proof.
pose proof tfv_exp_subst_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve tfv_exp_subst_exp_upper : lngen.

(* begin hide *)

Lemma fv_exp_tsubst_exp_upper_mutual :
(forall e1 A1 X1,
  fv_ee    (subst_te A1 X1 e1) [<=] fv_ee    e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_tsubst_exp_upper :
forall e1 A1 X1,
  fv_ee    (subst_te A1 X1 e1) [<=] fv_ee    e1.
Proof.
pose proof fv_exp_tsubst_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_tsubst_exp_upper : lngen.

(* begin hide *)

Lemma fv_exp_subst_exp_upper_mutual :
(forall e1 e2 x1,
  fv_ee    (subst_ee  e2 x1 e1) [<=] fv_ee    e2 `union` remove x1 (fv_ee    e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_exp_subst_exp_upper :
forall e1 e2 x1,
  fv_ee    (subst_ee  e2 x1 e1) [<=] fv_ee    e2 `union` remove x1 (fv_ee    e1).
Proof.
pose proof fv_exp_subst_exp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_exp_subst_exp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma tsubst_typ_close_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` fv_tt  A1 ->
  subst_tt A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (subst_tt A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_close_typ_wrt_typ_rec :
forall A2 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` fv_tt  A1 ->
  subst_tt A1 X1 (close_typ_wrt_typ_rec n1 X2 A2) = close_typ_wrt_typ_rec n1 X2 (subst_tt A1 X1 A2).
Proof.
pose proof tsubst_typ_close_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_close_typ_wrt_typ_rec : lngen.

(* begin hide *)

Lemma tsubst_exp_close_exp_wrt_typ_rec_mutual :
(forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` fv_tt  A1 ->
  subst_te A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (subst_te A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_exp_close_exp_wrt_typ_rec :
forall e1 A1 X1 X2 n1,
  degree_typ_wrt_typ n1 A1 ->
  X1 <> X2 ->
  X2 `notin` fv_tt  A1 ->
  subst_te A1 X1 (close_exp_wrt_typ_rec n1 X2 e1) = close_exp_wrt_typ_rec n1 X2 (subst_te A1 X1 e1).
Proof.
pose proof tsubst_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma tsubst_exp_close_exp_wrt_exp_rec_mutual :
(forall e1 A1 x1 X1 n1,
  subst_te A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_te A1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_exp_close_exp_wrt_exp_rec :
forall e1 A1 x1 X1 n1,
  subst_te A1 x1 (close_exp_wrt_exp_rec n1 X1 e1) = close_exp_wrt_exp_rec n1 X1 (subst_te A1 x1 e1).
Proof.
pose proof tsubst_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_close_exp_wrt_exp_rec : lngen.

(* begin hide *)

Lemma subst_exp_close_exp_wrt_typ_rec_mutual :
(forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` fv_te   e1 ->
  subst_ee  e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_ee  e1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_close_exp_wrt_typ_rec :
forall e2 e1 X1 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  x1 `notin` fv_te   e1 ->
  subst_ee  e1 X1 (close_exp_wrt_typ_rec n1 x1 e2) = close_exp_wrt_typ_rec n1 x1 (subst_ee  e1 X1 e2).
Proof.
pose proof subst_exp_close_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_close_exp_wrt_typ_rec : lngen.

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_ee    e1 ->
  subst_ee  e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_ee  e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_close_exp_wrt_exp_rec :
forall e2 e1 x1 x2 n1,
  degree_exp_wrt_exp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_ee    e1 ->
  subst_ee  e1 x1 (close_exp_wrt_exp_rec n1 x2 e2) = close_exp_wrt_exp_rec n1 x2 (subst_ee  e1 x1 e2).
Proof.
pose proof subst_exp_close_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_close_exp_wrt_exp_rec : lngen.

Lemma tsubst_typ_close_typ_wrt_typ :
forall A2 A1 X1 X2,
  type   A1 ->  X1 <> X2 ->
  X2 `notin` fv_tt  A1 ->
  subst_tt A1 X1 (close_typ_wrt_typ X2 A2) = close_typ_wrt_typ X2 (subst_tt A1 X1 A2).
Proof.
unfold close_typ_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_typ_close_typ_wrt_typ : lngen.

Lemma tsubst_exp_close_exp_wrt_typ :
forall e1 A1 X1 X2,
  type   A1 ->  X1 <> X2 ->
  X2 `notin` fv_tt  A1 ->
  subst_te A1 X1 (close_exp_wrt_typ X2 e1) = close_exp_wrt_typ X2 (subst_te A1 X1 e1).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve tsubst_exp_close_exp_wrt_typ : lngen.

Lemma tsubst_exp_close_exp_wrt_exp :
forall e1 A1 x1 X1,
  type   A1 ->  subst_te A1 x1 (close_exp_wrt_exp X1 e1) = close_exp_wrt_exp X1 (subst_te A1 x1 e1).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve tsubst_exp_close_exp_wrt_exp : lngen.

Lemma subst_exp_close_exp_wrt_typ :
forall e2 e1 X1 x1,
  expr   e1 ->  x1 `notin` fv_te   e1 ->
  subst_ee  e1 X1 (close_exp_wrt_typ x1 e2) = close_exp_wrt_typ x1 (subst_ee  e1 X1 e2).
Proof.
unfold close_exp_wrt_typ; default_simp.
Qed.

Hint Resolve subst_exp_close_exp_wrt_typ : lngen.

Lemma subst_exp_close_exp_wrt_exp :
forall e2 e1 x1 x2,
  expr   e1 ->  x1 <> x2 ->
  x2 `notin` fv_ee    e1 ->
  subst_ee  e1 x1 (close_exp_wrt_exp x2 e2) = close_exp_wrt_exp x2 (subst_ee  e1 x1 e2).
Proof.
unfold close_exp_wrt_exp; default_simp.
Qed.

Hint Resolve subst_exp_close_exp_wrt_exp : lngen.

(* begin hide *)

Lemma tsubst_typ_degree_typ_wrt_typ_mutual :
(forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (subst_tt A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_degree_typ_wrt_typ :
forall A1 A2 X1 n1,
  degree_typ_wrt_typ n1 A1 ->
  degree_typ_wrt_typ n1 A2 ->
  degree_typ_wrt_typ n1 (subst_tt A2 X1 A1).
Proof.
pose proof tsubst_typ_degree_typ_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_degree_typ_wrt_typ : lngen.

(* begin hide *)

Lemma tsubst_exp_degree_exp_wrt_typ_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (subst_te A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_exp_degree_exp_wrt_typ :
forall e1 A1 X1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_typ_wrt_typ n1 A1 ->
  degree_exp_wrt_typ n1 (subst_te A1 X1 e1).
Proof.
pose proof tsubst_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma tsubst_exp_degree_exp_wrt_exp_mutual :
(forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_te A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_exp_degree_exp_wrt_exp :
forall e1 A1 X1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 (subst_te A1 X1 e1).
Proof.
pose proof tsubst_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma subst_exp_degree_exp_wrt_typ_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_ee  e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_degree_exp_wrt_typ :
forall e1 e2 x1 n1,
  degree_exp_wrt_typ n1 e1 ->
  degree_exp_wrt_typ n1 e2 ->
  degree_exp_wrt_typ n1 (subst_ee  e2 x1 e1).
Proof.
pose proof subst_exp_degree_exp_wrt_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_degree_exp_wrt_typ : lngen.

(* begin hide *)

Lemma subst_exp_degree_exp_wrt_exp_mutual :
(forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_ee  e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_degree_exp_wrt_exp :
forall e1 e2 x1 n1,
  degree_exp_wrt_exp n1 e1 ->
  degree_exp_wrt_exp n1 e2 ->
  degree_exp_wrt_exp n1 (subst_ee  e2 x1 e1).
Proof.
pose proof subst_exp_degree_exp_wrt_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_degree_exp_wrt_exp : lngen.

(* begin hide *)

Lemma tsubst_typ_fresh_eq_mutual :
(forall A2 A1 X1,
  X1 `notin` fv_tt  A2 ->
  subst_tt A1 X1 A2 = A2).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_fresh_eq :
forall A2 A1 X1,
  X1 `notin` fv_tt  A2 ->
  subst_tt A1 X1 A2 = A2.
Proof.
pose proof tsubst_typ_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_fresh_eq : lngen.
Hint Rewrite tsubst_typ_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma tsubst_exp_fresh_eq_mutual :
(forall e1 A1 X1,
  X1 `notin` fv_te   e1 ->
  subst_te A1 X1 e1 = e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_exp_fresh_eq :
forall e1 A1 X1,
  X1 `notin` fv_te   e1 ->
  subst_te A1 X1 e1 = e1.
Proof.
pose proof tsubst_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_fresh_eq : lngen.
Hint Rewrite tsubst_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_ee    e2 ->
  subst_ee  e1 x1 e2 = e2).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_ee    e2 ->
  subst_ee  e1 x1 e2 = e2.
Proof.
pose proof subst_exp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_fresh_eq : lngen.
Hint Rewrite subst_exp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma tsubst_typ_fresh_same_mutual :
(forall A2 A1 X1,
  X1 `notin` fv_tt  A1 ->
  X1 `notin` fv_tt  (subst_tt A1 X1 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_fresh_same :
forall A2 A1 X1,
  X1 `notin` fv_tt  A1 ->
  X1 `notin` fv_tt  (subst_tt A1 X1 A2).
Proof.
pose proof tsubst_typ_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_fresh_same : lngen.

(* begin hide *)

Lemma tsubst_exp_fresh_same_mutual :
(forall e1 A1 X1,
  X1 `notin` fv_tt  A1 ->
  X1 `notin` fv_te   (subst_te A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_exp_fresh_same :
forall e1 A1 X1,
  X1 `notin` fv_tt  A1 ->
  X1 `notin` fv_te   (subst_te A1 X1 e1).
Proof.
pose proof tsubst_exp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_fresh_same : lngen.

(* begin hide *)

Lemma subst_exp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_ee    e1 ->
  x1 `notin` fv_ee    (subst_ee  e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_ee    e1 ->
  x1 `notin` fv_ee    (subst_ee  e1 x1 e2).
Proof.
pose proof subst_exp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_fresh_same : lngen.

(* begin hide *)

Lemma tsubst_typ_fresh_mutual :
(forall A2 A1 X1 X2,
  X1 `notin` fv_tt  A2 ->
  X1 `notin` fv_tt  A1 ->
  X1 `notin` fv_tt  (subst_tt A1 X2 A2)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_fresh :
forall A2 A1 X1 X2,
  X1 `notin` fv_tt  A2 ->
  X1 `notin` fv_tt  A1 ->
  X1 `notin` fv_tt  (subst_tt A1 X2 A2).
Proof.
pose proof tsubst_typ_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_fresh : lngen.

(* begin hide *)

Lemma tsubst_exp_fresh_mutual :
(forall e1 A1 X1 X2,
  X1 `notin` fv_te   e1 ->
  X1 `notin` fv_tt  A1 ->
  X1 `notin` fv_te   (subst_te A1 X2 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_exp_fresh :
forall e1 A1 X1 X2,
  X1 `notin` fv_te   e1 ->
  X1 `notin` fv_tt  A1 ->
  X1 `notin` fv_te   (subst_te A1 X2 e1).
Proof.
pose proof tsubst_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_fresh : lngen.

(* begin hide *)

Lemma subst_exp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_ee    e2 ->
  x1 `notin` fv_ee    e1 ->
  x1 `notin` fv_ee    (subst_ee  e1 x2 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_ee    e2 ->
  x1 `notin` fv_ee    e1 ->
  x1 `notin` fv_ee    (subst_ee  e1 x2 e2).
Proof.
pose proof subst_exp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_fresh : lngen.

Lemma tsubst_typ_type   :
forall A1 A2 X1,
  type   A1 ->
  type   A2 ->
  type   (subst_tt A2 X1 A1).
Proof.
default_simp.
Qed.

Hint Resolve tsubst_typ_type   : lngen.

Lemma tsubst_exp_expr   :
forall e1 A1 X1,
  expr   e1 ->
  type   A1 ->
  expr   (subst_te A1 X1 e1).
Proof.
default_simp.
Qed.

Hint Resolve tsubst_exp_expr   : lngen.

Lemma subst_exp_expr   :
forall e1 e2 x1,
  expr   e1 ->
  expr   e2 ->
  expr   (subst_ee  e2 x1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_expr   : lngen.

(* begin hide *)

Lemma tsubst_typ_open_typ_wrt_typ_rec_mutual :
(forall A3 A1 A2 X1 n1,
  type   A1 ->
  subst_tt A1 X1 (open_tt_rec    n1 A2 A3) = open_tt_rec    n1 (subst_tt A1 X1 A2) (subst_tt A1 X1 A3)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_typ_open_tt_rec    :
forall A3 A1 A2 X1 n1,
  type   A1 ->
  subst_tt A1 X1 (open_tt_rec    n1 A2 A3) = open_tt_rec    n1 (subst_tt A1 X1 A2) (subst_tt A1 X1 A3).
Proof.
pose proof tsubst_typ_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_open_tt_rec    : lngen.

(* end hide *)

(* begin hide *)

Lemma tsubst_exp_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 A2 X1 n1,
  type   A1 ->
  subst_te A1 X1 (open_te_rec     n1 A2 e1) = open_te_rec     n1 (subst_tt A1 X1 A2) (subst_te A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_exp_open_te_rec     :
forall e1 A1 A2 X1 n1,
  type   A1 ->
  subst_te A1 X1 (open_te_rec     n1 A2 e1) = open_te_rec     n1 (subst_tt A1 X1 A2) (subst_te A1 X1 e1).
Proof.
pose proof tsubst_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_open_te_rec     : lngen.

(* end hide *)

(* begin hide *)

Lemma tsubst_exp_open_exp_wrt_exp_rec_mutual :
(forall e2 A1 e1 X1 n1,
  subst_te A1 X1 (open_ee_rec     n1 e1 e2) = open_ee_rec     n1 (subst_te A1 X1 e1) (subst_te A1 X1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_exp_open_ee_rec     :
forall e2 A1 e1 X1 n1,
  subst_te A1 X1 (open_ee_rec     n1 e1 e2) = open_ee_rec     n1 (subst_te A1 X1 e1) (subst_te A1 X1 e2).
Proof.
pose proof tsubst_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_open_ee_rec     : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 A1 x1 n1,
  expr   e1 ->
  subst_ee  e1 x1 (open_te_rec     n1 A1 e2) = open_te_rec     n1 A1 (subst_ee  e1 x1 e2)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_te_rec     :
forall e2 e1 A1 x1 n1,
  expr   e1 ->
  subst_ee  e1 x1 (open_te_rec     n1 A1 e2) = open_te_rec     n1 A1 (subst_ee  e1 x1 e2).
Proof.
pose proof subst_exp_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_open_te_rec     : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_exp_wrt_exp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  expr   e1 ->
  subst_ee  e1 x1 (open_ee_rec     n1 e2 e3) = open_ee_rec     n1 (subst_ee  e1 x1 e2) (subst_ee  e1 x1 e3)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_open_ee_rec     :
forall e3 e1 e2 x1 n1,
  expr   e1 ->
  subst_ee  e1 x1 (open_ee_rec     n1 e2 e3) = open_ee_rec     n1 (subst_ee  e1 x1 e2) (subst_ee  e1 x1 e3).
Proof.
pose proof subst_exp_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_open_ee_rec     : lngen.

(* end hide *)

Lemma tsubst_typ_open_tt :
forall A3 A1 A2 X1,
  type   A1 ->
  subst_tt A1 X1 (open_tt A3 A2) = open_tt (subst_tt A1 X1 A3) (subst_tt A1 X1 A2).
Proof.
unfold open_tt;      default_simp.
Qed.

Hint Resolve tsubst_typ_open_tt : lngen.

Lemma tsubst_exp_open_te :
forall e1 A1 A2 X1,
  type   A1 ->
  subst_te A1 X1 (open_te e1 A2) = open_te (subst_te A1 X1 e1) (subst_tt A1 X1 A2).
Proof.
unfold open_te; default_simp.
Qed.

Hint Resolve tsubst_exp_open_te : lngen.

Lemma tsubst_exp_open_ee   :
forall e2 A1 e1 X1,
  subst_te A1 X1 (open_ee   e2 e1) = open_ee   (subst_te A1 X1 e2) (subst_te A1 X1 e1).
Proof.
unfold open_ee; default_simp.
Qed.

Hint Resolve tsubst_exp_open_ee   : lngen.

Lemma subst_exp_open_te :
forall e2 e1 A1 x1,
  expr   e1 ->
  subst_ee  e1 x1 (open_te e2 A1) = open_te (subst_ee  e1 x1 e2) A1.
Proof.
unfold open_te; default_simp.
Qed.

Hint Resolve subst_exp_open_te : lngen.

Lemma subst_exp_open_ee   :
forall e3 e1 e2 x1,
  expr   e1 ->
  subst_ee  e1 x1 (open_ee   e3 e2) = open_ee   (subst_ee  e1 x1 e3) (subst_ee  e1 x1 e2).
Proof.
unfold open_ee; default_simp.
Qed.

Hint Resolve subst_exp_open_ee   : lngen.

Lemma tsubst_typ_open_typ_wrt_typ_var :
forall A2 A1 X1 X2,
  X1 <> X2 ->
  type   A1 ->
  open_tt (subst_tt A1 X1 A2) (t_fvar  X2) = subst_tt A1 X1 (open_tt A2 (t_fvar  X2)).
Proof.
intros; rewrite tsubst_typ_open_tt;      default_simp.
Qed.

Hint Resolve tsubst_typ_open_typ_wrt_typ_var : lngen.

Lemma tsubst_exp_open_exp_wrt_typ_var :
forall e1 A1 X1 X2,
  X1 <> X2 ->
  type   A1 ->
  open_te (subst_te A1 X1 e1) (t_fvar  X2) = subst_te A1 X1 (open_te e1 (t_fvar  X2)).
Proof.
intros; rewrite tsubst_exp_open_te; default_simp.
Qed.

Hint Resolve tsubst_exp_open_exp_wrt_typ_var : lngen.

Lemma tsubst_exp_open_exp_wrt_exp_var :
forall e1 A1 X1 x1,
  open_ee   (subst_te A1 X1 e1) (e_fvar  x1) = subst_te A1 X1 (open_ee   e1 (e_fvar  x1)).
Proof.
intros; rewrite tsubst_exp_open_ee; default_simp.
Qed.

Hint Resolve tsubst_exp_open_exp_wrt_exp_var : lngen.

Lemma subst_exp_open_exp_wrt_typ_var :
forall e2 e1 x1 X1,
  expr   e1 ->
  open_te (subst_ee  e1 x1 e2) (t_fvar  X1) = subst_ee  e1 x1 (open_te e2 (t_fvar  X1)).
Proof.
intros; rewrite subst_exp_open_te; default_simp.
Qed.

Hint Resolve subst_exp_open_exp_wrt_typ_var : lngen.

Lemma subst_exp_open_exp_wrt_exp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  expr   e1 ->
  open_ee   (subst_ee  e1 x1 e2) (e_fvar  x2) = subst_ee  e1 x1 (open_ee   e2 (e_fvar  x2)).
Proof.
intros; rewrite subst_exp_open_ee; default_simp.
Qed.

Hint Resolve subst_exp_open_exp_wrt_exp_var : lngen.

(* begin hide *)

Lemma tsubst_typ_spec_rec_mutual :
(forall A1 A2 X1 n1,
  subst_tt A2 X1 A1 = open_tt_rec    n1 A2 (close_typ_wrt_typ_rec n1 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_typ_spec_rec :
forall A1 A2 X1 n1,
  subst_tt A2 X1 A1 = open_tt_rec    n1 A2 (close_typ_wrt_typ_rec n1 X1 A1).
Proof.
pose proof tsubst_typ_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma tsubst_exp_spec_rec_mutual :
(forall e1 A1 X1 n1,
  subst_te A1 X1 e1 = open_te_rec     n1 A1 (close_exp_wrt_typ_rec n1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_exp_spec_rec :
forall e1 A1 X1 n1,
  subst_te A1 X1 e1 = open_te_rec     n1 A1 (close_exp_wrt_typ_rec n1 X1 e1).
Proof.
pose proof tsubst_exp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_spec_rec : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_ee  e2 x1 e1 = open_ee_rec     n1 e2 (close_exp_wrt_exp_rec n1 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_spec_rec :
forall e1 e2 x1 n1,
  subst_ee  e2 x1 e1 = open_ee_rec     n1 e2 (close_exp_wrt_exp_rec n1 x1 e1).
Proof.
pose proof subst_exp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_spec_rec : lngen.

(* end hide *)

Lemma tsubst_typ_spec :
forall A1 A2 X1,
  subst_tt A2 X1 A1 = open_tt (close_typ_wrt_typ X1 A1) A2.
Proof.
unfold close_typ_wrt_typ; unfold open_tt;      default_simp.
Qed.

Hint Resolve tsubst_typ_spec : lngen.

Lemma tsubst_exp_spec :
forall e1 A1 X1,
  subst_te A1 X1 e1 = open_te (close_exp_wrt_typ X1 e1) A1.
Proof.
unfold close_exp_wrt_typ; unfold open_te; default_simp.
Qed.

Hint Resolve tsubst_exp_spec : lngen.

Lemma subst_exp_spec :
forall e1 e2 x1,
  subst_ee  e2 x1 e1 = open_ee   (close_exp_wrt_exp x1 e1) e2.
Proof.
unfold close_exp_wrt_exp; unfold open_ee; default_simp.
Qed.

Hint Resolve subst_exp_spec : lngen.

(* begin hide *)

Lemma tsubst_typ_tsubst_typ_mutual :
(forall A1 A2 A3 X2 X1,
  X2 `notin` fv_tt  A2 ->
  X2 <> X1 ->
  subst_tt A2 X1 (subst_tt A3 X2 A1) = subst_tt (subst_tt A2 X1 A3) X2 (subst_tt A2 X1 A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_subst_tt :
forall A1 A2 A3 X2 X1,
  X2 `notin` fv_tt  A2 ->
  X2 <> X1 ->
  subst_tt A2 X1 (subst_tt A3 X2 A1) = subst_tt (subst_tt A2 X1 A3) X2 (subst_tt A2 X1 A1).
Proof.
pose proof tsubst_typ_tsubst_typ_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_subst_tt : lngen.

(* begin hide *)

Lemma tsubst_exp_tsubst_exp_mutual :
(forall e1 A1 A2 X2 X1,
  X2 `notin` fv_tt  A1 ->
  X2 <> X1 ->
  subst_te A1 X1 (subst_te A2 X2 e1) = subst_te (subst_tt A1 X1 A2) X2 (subst_te A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_exp_subst_te :
forall e1 A1 A2 X2 X1,
  X2 `notin` fv_tt  A1 ->
  X2 <> X1 ->
  subst_te A1 X1 (subst_te A2 X2 e1) = subst_te (subst_tt A1 X1 A2) X2 (subst_te A1 X1 e1).
Proof.
pose proof tsubst_exp_tsubst_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_subst_te : lngen.

(* begin hide *)

Lemma tsubst_exp_subst_exp_mutual :
(forall e1 A1 e2 x1 X1,
  subst_te A1 X1 (subst_ee  e2 x1 e1) = subst_ee  (subst_te A1 X1 e2) x1 (subst_te A1 X1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_exp_subst_ee  :
forall e1 A1 e2 x1 X1,
  subst_te A1 X1 (subst_ee  e2 x1 e1) = subst_ee  (subst_te A1 X1 e2) x1 (subst_te A1 X1 e1).
Proof.
pose proof tsubst_exp_subst_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_subst_ee  : lngen.

(* begin hide *)

Lemma subst_exp_tsubst_exp_mutual :
(forall e1 e2 A1 X1 x1,
  X1 `notin` fv_te   e2 ->
  subst_ee  e2 x1 (subst_te A1 X1 e1) = subst_te A1 X1 (subst_ee  e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_subst_te :
forall e1 e2 A1 X1 x1,
  X1 `notin` fv_te   e2 ->
  subst_ee  e2 x1 (subst_te A1 X1 e1) = subst_te A1 X1 (subst_ee  e2 x1 e1).
Proof.
pose proof subst_exp_tsubst_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_subst_te : lngen.

(* begin hide *)

Lemma subst_exp_subst_exp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_ee    e2 ->
  x2 <> x1 ->
  subst_ee  e2 x1 (subst_ee  e3 x2 e1) = subst_ee  (subst_ee  e2 x1 e3) x2 (subst_ee  e2 x1 e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_subst_ee  :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_ee    e2 ->
  x2 <> x1 ->
  subst_ee  e2 x1 (subst_ee  e3 x2 e1) = subst_ee  (subst_ee  e2 x1 e3) x2 (subst_ee  e2 x1 e1).
Proof.
pose proof subst_exp_subst_exp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_subst_ee  : lngen.

(* begin hide *)

Lemma tsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual :
(forall A2 A1 X1 X2 n1,
  X2 `notin` fv_tt  A2 ->
  X2 `notin` fv_tt  A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tt A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (subst_tt A1 X1 (open_tt_rec    n1 (t_fvar  X2) A2))).
Proof.
apply_mutual_ind typ_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_typ_close_typ_wrt_typ_rec_open_tt_rec    :
forall A2 A1 X1 X2 n1,
  X2 `notin` fv_tt  A2 ->
  X2 `notin` fv_tt  A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_tt A1 X1 A2 = close_typ_wrt_typ_rec n1 X2 (subst_tt A1 X1 (open_tt_rec    n1 (t_fvar  X2) A2)).
Proof.
pose proof tsubst_typ_close_typ_wrt_typ_rec_open_typ_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_close_typ_wrt_typ_rec_open_tt_rec    : lngen.

(* end hide *)

(* begin hide *)

Lemma tsubst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e1 A1 X1 X2 n1,
  X2 `notin` fv_te   e1 ->
  X2 `notin` fv_tt  A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_te A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (subst_te A1 X1 (open_te_rec     n1 (t_fvar  X2) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_exp_close_exp_wrt_typ_rec_open_te_rec     :
forall e1 A1 X1 X2 n1,
  X2 `notin` fv_te   e1 ->
  X2 `notin` fv_tt  A1 ->
  X2 <> X1 ->
  degree_typ_wrt_typ n1 A1 ->
  subst_te A1 X1 e1 = close_exp_wrt_typ_rec n1 X2 (subst_te A1 X1 (open_te_rec     n1 (t_fvar  X2) e1)).
Proof.
pose proof tsubst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_close_exp_wrt_typ_rec_open_te_rec     : lngen.

(* end hide *)

(* begin hide *)

Lemma tsubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e1 A1 X1 x1 n1,
  x1 `notin` fv_ee    e1 ->
  subst_te A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_te A1 X1 (open_ee_rec     n1 (e_fvar  x1) e1))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma tsubst_exp_close_exp_wrt_exp_rec_open_ee_rec     :
forall e1 A1 X1 x1 n1,
  x1 `notin` fv_ee    e1 ->
  subst_te A1 X1 e1 = close_exp_wrt_exp_rec n1 x1 (subst_te A1 X1 (open_ee_rec     n1 (e_fvar  x1) e1)).
Proof.
pose proof tsubst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_close_exp_wrt_exp_rec_open_ee_rec     : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual :
(forall e2 e1 x1 X1 n1,
  X1 `notin` fv_te   e2 ->
  X1 `notin` fv_te   e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_ee  e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_ee  e1 x1 (open_te_rec     n1 (t_fvar  X1) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_typ_rec_open_te_rec     :
forall e2 e1 x1 X1 n1,
  X1 `notin` fv_te   e2 ->
  X1 `notin` fv_te   e1 ->
  degree_exp_wrt_typ n1 e1 ->
  subst_ee  e1 x1 e2 = close_exp_wrt_typ_rec n1 X1 (subst_ee  e1 x1 (open_te_rec     n1 (t_fvar  X1) e2)).
Proof.
pose proof subst_exp_close_exp_wrt_typ_rec_open_exp_wrt_typ_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_close_exp_wrt_typ_rec_open_te_rec     : lngen.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_ee    e2 ->
  x2 `notin` fv_ee    e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_ee  e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_ee  e1 x1 (open_ee_rec     n1 (e_fvar  x2) e2))).
Proof.
apply_mutual_ind exp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_exp_close_exp_wrt_exp_rec_open_ee_rec     :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_ee    e2 ->
  x2 `notin` fv_ee    e1 ->
  x2 <> x1 ->
  degree_exp_wrt_exp n1 e1 ->
  subst_ee  e1 x1 e2 = close_exp_wrt_exp_rec n1 x2 (subst_ee  e1 x1 (open_ee_rec     n1 (e_fvar  x2) e2)).
Proof.
pose proof subst_exp_close_exp_wrt_exp_rec_open_exp_wrt_exp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_close_exp_wrt_exp_rec_open_ee_rec     : lngen.

(* end hide *)

Lemma tsubst_typ_close_typ_wrt_typ_open_tt :
forall A2 A1 X1 X2,
  X2 `notin` fv_tt  A2 ->
  X2 `notin` fv_tt  A1 ->
  X2 <> X1 ->
  type   A1 ->
  subst_tt A1 X1 A2 = close_typ_wrt_typ X2 (subst_tt A1 X1 (open_tt A2 (t_fvar  X2))).
Proof.
unfold close_typ_wrt_typ; unfold open_tt;      default_simp.
Qed.

Hint Resolve tsubst_typ_close_typ_wrt_typ_open_tt : lngen.

Lemma tsubst_exp_close_exp_wrt_typ_open_te :
forall e1 A1 X1 X2,
  X2 `notin` fv_te   e1 ->
  X2 `notin` fv_tt  A1 ->
  X2 <> X1 ->
  type   A1 ->
  subst_te A1 X1 e1 = close_exp_wrt_typ X2 (subst_te A1 X1 (open_te e1 (t_fvar  X2))).
Proof.
unfold close_exp_wrt_typ; unfold open_te; default_simp.
Qed.

Hint Resolve tsubst_exp_close_exp_wrt_typ_open_te : lngen.

Lemma tsubst_exp_close_exp_wrt_exp_open_ee   :
forall e1 A1 X1 x1,
  x1 `notin` fv_ee    e1 ->
  type   A1 ->
  subst_te A1 X1 e1 = close_exp_wrt_exp x1 (subst_te A1 X1 (open_ee   e1 (e_fvar  x1))).
Proof.
unfold close_exp_wrt_exp; unfold open_ee; default_simp.
Qed.

Hint Resolve tsubst_exp_close_exp_wrt_exp_open_ee   : lngen.

Lemma subst_exp_close_exp_wrt_typ_open_te :
forall e2 e1 x1 X1,
  X1 `notin` fv_te   e2 ->
  X1 `notin` fv_te   e1 ->
  expr   e1 ->
  subst_ee  e1 x1 e2 = close_exp_wrt_typ X1 (subst_ee  e1 x1 (open_te e2 (t_fvar  X1))).
Proof.
unfold close_exp_wrt_typ; unfold open_te; default_simp.
Qed.

Hint Resolve subst_exp_close_exp_wrt_typ_open_te : lngen.

Lemma subst_exp_close_exp_wrt_exp_open_ee   :
forall e2 e1 x1 x2,
  x2 `notin` fv_ee    e2 ->
  x2 `notin` fv_ee    e1 ->
  x2 <> x1 ->
  expr   e1 ->
  subst_ee  e1 x1 e2 = close_exp_wrt_exp x2 (subst_ee  e1 x1 (open_ee   e2 (e_fvar  x2))).
Proof.
unfold close_exp_wrt_exp; unfold open_ee; default_simp.
Qed.

Hint Resolve subst_exp_close_exp_wrt_exp_open_ee   : lngen.

Lemma tsubst_typ_t_all :
forall X2 B1 A1 X1,
  type   A1 ->
  X2 `notin` fv_tt  A1 `union` fv_tt  B1 `union` singleton X1 ->
  subst_tt A1 X1 (t_all B1) = t_all (close_typ_wrt_typ X2 (subst_tt A1 X1 (open_tt B1 (t_fvar  X2)))).
Proof.
default_simp.
Qed.

Hint Resolve tsubst_typ_t_all : lngen.

Lemma tsubst_exp_e_abs :
forall x1 e1 A1 X1,
  type   A1 ->
  x1 `notin` fv_ee    e1 ->
  subst_te A1 X1 (e_abs e1) = e_abs (close_exp_wrt_exp x1 (subst_te A1 X1 (open_ee   e1 (e_fvar  x1)))).
Proof.
default_simp.
Qed.

Hint Resolve tsubst_exp_e_abs : lngen.

Lemma tsubst_exp_e_tabs :
forall X2 e1 A1 X1,
  type   A1 ->
  X2 `notin` fv_tt  A1 `union` fv_te   e1 `union` singleton X1 ->
  subst_te A1 X1 (e_tabs e1) = e_tabs (close_exp_wrt_typ X2 (subst_te A1 X1 (open_te e1 (t_fvar  X2)))).
Proof.
default_simp.
Qed.

Hint Resolve tsubst_exp_e_tabs : lngen.

Lemma subst_exp_e_abs :
forall x2 e2 e1 x1,
  expr   e1 ->
  x2 `notin` fv_ee    e1 `union` fv_ee    e2 `union` singleton x1 ->
  subst_ee  e1 x1 (e_abs e2) = e_abs (close_exp_wrt_exp x2 (subst_ee  e1 x1 (open_ee   e2 (e_fvar  x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_e_abs : lngen.

Lemma subst_exp_e_tabs :
forall X1 e2 e1 x1,
  expr   e1 ->
  X1 `notin` fv_te   e1 `union` fv_te   e2 ->
  subst_ee  e1 x1 (e_tabs e2) = e_tabs (close_exp_wrt_typ X1 (subst_ee  e1 x1 (open_te e2 (t_fvar  X1)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_exp_e_tabs : lngen.

(* begin hide *)

Lemma tsubst_typ_intro_rec_mutual :
(forall A1 X1 A2 n1,
  X1 `notin` fv_tt  A1 ->
  open_tt_rec    n1 A2 A1 = subst_tt A2 X1 (open_tt_rec    n1 (t_fvar  X1) A1)).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_typ_intro_rec :
forall A1 X1 A2 n1,
  X1 `notin` fv_tt  A1 ->
  open_tt_rec    n1 A2 A1 = subst_tt A2 X1 (open_tt_rec    n1 (t_fvar  X1) A1).
Proof.
pose proof tsubst_typ_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_typ_intro_rec : lngen.
Hint Rewrite tsubst_typ_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma tsubst_exp_intro_rec_mutual :
(forall e1 X1 A1 n1,
  X1 `notin` fv_te   e1 ->
  open_te_rec     n1 A1 e1 = subst_te A1 X1 (open_te_rec     n1 (t_fvar  X1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma tsubst_exp_intro_rec :
forall e1 X1 A1 n1,
  X1 `notin` fv_te   e1 ->
  open_te_rec     n1 A1 e1 = subst_te A1 X1 (open_te_rec     n1 (t_fvar  X1) e1).
Proof.
pose proof tsubst_exp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve tsubst_exp_intro_rec : lngen.
Hint Rewrite tsubst_exp_intro_rec using solve [auto] : lngen.

(* begin hide *)

Lemma subst_exp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fv_ee    e1 ->
  open_ee_rec     n1 e2 e1 = subst_ee  e2 x1 (open_ee_rec     n1 (e_fvar  x1) e1)).
Proof.
apply_mutual_ind exp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_exp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_ee    e1 ->
  open_ee_rec     n1 e2 e1 = subst_ee  e2 x1 (open_ee_rec     n1 (e_fvar  x1) e1).
Proof.
pose proof subst_exp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_exp_intro_rec : lngen.
Hint Rewrite subst_exp_intro_rec using solve [auto] : lngen.

Lemma tsubst_typ_intro :
forall X1 A1 A2,
  X1 `notin` fv_tt  A1 ->
  open_tt A1 A2 = subst_tt A2 X1 (open_tt A1 (t_fvar  X1)).
Proof.
unfold open_tt;      default_simp.
Qed.

Hint Resolve tsubst_typ_intro : lngen.

Lemma tsubst_exp_intro :
forall X1 e1 A1,
  X1 `notin` fv_te   e1 ->
  open_te e1 A1 = subst_te A1 X1 (open_te e1 (t_fvar  X1)).
Proof.
unfold open_te; default_simp.
Qed.

Hint Resolve tsubst_exp_intro : lngen.

Lemma subst_exp_intro :
forall x1 e1 e2,
  x1 `notin` fv_ee    e1 ->
  open_ee   e1 e2 = subst_ee  e2 x1 (open_ee   e1 (e_fvar  x1)).
Proof.
unfold open_ee; default_simp.
Qed.

Hint Resolve subst_exp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
