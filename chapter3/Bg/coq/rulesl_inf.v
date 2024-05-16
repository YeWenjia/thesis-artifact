(* !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export syntaxb_ott.
Require Export syntaxl_ott.
Definition l : Set := var.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
  fun H1 H2 H3 H4 H5 =>
  typ_ind' H1 H2 H3 H4 H5.

Scheme typ_rec' := Induction for typ Sort Set.

Definition typ_mutrec :=
  fun H1 H2 H3 H4 H5 =>
  typ_rec' H1 H2 H3 H4 H5.

Scheme eexp_ind' := Induction for eexp Sort Prop.

Definition eexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  eexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Scheme eexp_rec' := Induction for eexp Sort Set.

Definition eexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  eexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_eexp_wrt_eexp_rec (n1 : nat) (l1 : l) (e1 : eexp) {struct e1} : eexp :=
  match e1 with
    | ee_var_f l2 => if (l1 == l2) then (ee_var_b n1) else (ee_var_f l2)
    | ee_var_b n2 => if (lt_ge_dec n2 n1) then (ee_var_b n2) else (ee_var_b (S n2))
    | ee_lit i1 => ee_lit i1
    | ee_abs A1 e2 l2 b1 B1 => ee_abs A1 (close_eexp_wrt_eexp_rec (S n1) l1 e2) l2 b1 B1
    | ee_app e2 l2 b1 e3 => ee_app (close_eexp_wrt_eexp_rec n1 l1 e2) l2 b1 (close_eexp_wrt_eexp_rec n1 l1 e3)
    | ee_anno e2 l2 b1 A1 => ee_anno (close_eexp_wrt_eexp_rec n1 l1 e2) l2 b1 A1
    | ee_add => ee_add
    | ee_addl i1 => ee_addl i1
    | ee_pro e2 e3 => ee_pro (close_eexp_wrt_eexp_rec n1 l1 e2) (close_eexp_wrt_eexp_rec n1 l1 e3)
    | ee_l e2 l2 b1 => ee_l (close_eexp_wrt_eexp_rec n1 l1 e2) l2 b1
    | ee_r e2 l2 b1 => ee_r (close_eexp_wrt_eexp_rec n1 l1 e2) l2 b1
  end.

Definition close_eexp_wrt_eexp l1 e1 := close_eexp_wrt_eexp_rec 0 l1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
  match A1 with
    | t_int => 1
    | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_pro A2 B1 => 1 + (size_typ A2) + (size_typ B1)
    | t_dyn => 1
  end.

Fixpoint size_eexp (e1 : eexp) {struct e1} : nat :=
  match e1 with
    | ee_var_f x1 => 1
    | ee_var_b n1 => 1
    | ee_lit i1 => 1
    | ee_abs A1 e2 l1 b1 B1 => 1 + (size_typ A1) + (size_eexp e2) + (size_typ B1)
    | ee_app e2 l1 b1 e3 => 1 + (size_eexp e2) + (size_eexp e3)
    | ee_anno e2 l1 b1 A1 => 1 + (size_eexp e2) + (size_typ A1)
    | ee_add => 1
    | ee_addl i1 => 1
    | ee_pro e2 e3 => 1 + (size_eexp e2) + (size_eexp e3)
    | ee_l e2 l1 b1 => 1 + (size_eexp e2)
    | ee_r e2 l1 b1 => 1 + (size_eexp e2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_eexp_wrt_eexp : nat -> eexp -> Prop :=
  | degree_wrt_eexp_ee_var_f : forall n1 x1,
    degree_eexp_wrt_eexp n1 (ee_var_f x1)
  | degree_wrt_eexp_ee_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_eexp_wrt_eexp n1 (ee_var_b n2)
  | degree_wrt_eexp_ee_lit : forall n1 i1,
    degree_eexp_wrt_eexp n1 (ee_lit i1)
  | degree_wrt_eexp_ee_abs : forall n1 A1 e1 l1 b1 B1,
    degree_eexp_wrt_eexp (S n1) e1 ->
    degree_eexp_wrt_eexp n1 (ee_abs A1 e1 l1 b1 B1)
  | degree_wrt_eexp_ee_app : forall n1 e1 l1 b1 e2,
    degree_eexp_wrt_eexp n1 e1 ->
    degree_eexp_wrt_eexp n1 e2 ->
    degree_eexp_wrt_eexp n1 (ee_app e1 l1 b1 e2)
  | degree_wrt_eexp_ee_anno : forall n1 e1 l1 b1 A1,
    degree_eexp_wrt_eexp n1 e1 ->
    degree_eexp_wrt_eexp n1 (ee_anno e1 l1 b1 A1)
  | degree_wrt_eexp_ee_add : forall n1,
    degree_eexp_wrt_eexp n1 (ee_add)
  | degree_wrt_eexp_ee_addl : forall n1 i1,
    degree_eexp_wrt_eexp n1 (ee_addl i1)
  | degree_wrt_eexp_ee_pro : forall n1 e1 e2,
    degree_eexp_wrt_eexp n1 e1 ->
    degree_eexp_wrt_eexp n1 e2 ->
    degree_eexp_wrt_eexp n1 (ee_pro e1 e2)
  | degree_wrt_eexp_ee_l : forall n1 e1 l1 b1,
    degree_eexp_wrt_eexp n1 e1 ->
    degree_eexp_wrt_eexp n1 (ee_l e1 l1 b1)
  | degree_wrt_eexp_ee_r : forall n1 e1 l1 b1,
    degree_eexp_wrt_eexp n1 e1 ->
    degree_eexp_wrt_eexp n1 (ee_r e1 l1 b1).

Scheme degree_eexp_wrt_eexp_ind' := Induction for degree_eexp_wrt_eexp Sort Prop.

Definition degree_eexp_wrt_eexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
  degree_eexp_wrt_eexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Hint Constructors degree_eexp_wrt_eexp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_eexp : eexp -> Set :=
  | lc_set_ee_var_f : forall x1,
    lc_set_eexp (ee_var_f x1)
  | lc_set_ee_lit : forall i1,
    lc_set_eexp (ee_lit i1)
  | lc_set_ee_abs : forall A1 e1 l1 b1 B1,
    (forall x1 : l, lc_set_eexp (open_eexp_wrt_eexp e1 (ee_var_f x1))) ->
    lc_set_eexp (ee_abs A1 e1 l1 b1 B1)
  | lc_set_ee_app : forall e1 l1 b1 e2,
    lc_set_eexp e1 ->
    lc_set_eexp e2 ->
    lc_set_eexp (ee_app e1 l1 b1 e2)
  | lc_set_ee_anno : forall e1 l1 b1 A1,
    lc_set_eexp e1 ->
    lc_set_eexp (ee_anno e1 l1 b1 A1)
  | lc_set_ee_add :
    lc_set_eexp (ee_add)
  | lc_set_ee_addl : forall i1,
    lc_set_eexp (ee_addl i1)
  | lc_set_ee_pro : forall e1 e2,
    lc_set_eexp e1 ->
    lc_set_eexp e2 ->
    lc_set_eexp (ee_pro e1 e2)
  | lc_set_ee_l : forall e1 l1 b1,
    lc_set_eexp e1 ->
    lc_set_eexp (ee_l e1 l1 b1)
  | lc_set_ee_r : forall e1 l1 b1,
    lc_set_eexp e1 ->
    lc_set_eexp (ee_r e1 l1 b1).

Scheme lc_eexp_ind' := Induction for lc_eexp Sort Prop.

Definition lc_eexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  lc_eexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme lc_set_eexp_ind' := Induction for lc_set_eexp Sort Prop.

Definition lc_set_eexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  lc_set_eexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Scheme lc_set_eexp_rec' := Induction for lc_set_eexp Sort Set.

Definition lc_set_eexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 =>
  lc_set_eexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11.

Hint Constructors lc_eexp : core lngen.

Hint Constructors lc_set_eexp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_eexp_wrt_eexp e1 := forall l1, lc_eexp (open_eexp_wrt_eexp e1 (ee_var_f l1)).

Hint Unfold body_eexp_wrt_eexp : core.


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

Lemma size_eexp_min_mutual :
(forall e1, 1 <= size_eexp e1).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_eexp_min :
forall e1, 1 <= size_eexp e1.
Proof.
pose proof size_eexp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_eexp_min : lngen.

(* begin hide *)

Lemma size_eexp_close_eexp_wrt_eexp_rec_mutual :
(forall e1 l1 n1,
  size_eexp (close_eexp_wrt_eexp_rec n1 l1 e1) = size_eexp e1).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_eexp_close_eexp_wrt_eexp_rec :
forall e1 l1 n1,
  size_eexp (close_eexp_wrt_eexp_rec n1 l1 e1) = size_eexp e1.
Proof.
pose proof size_eexp_close_eexp_wrt_eexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_eexp_close_eexp_wrt_eexp_rec : lngen.
Hint Rewrite size_eexp_close_eexp_wrt_eexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_eexp_close_eexp_wrt_eexp :
forall e1 l1,
  size_eexp (close_eexp_wrt_eexp l1 e1) = size_eexp e1.
Proof.
unfold close_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve size_eexp_close_eexp_wrt_eexp : lngen.
Hint Rewrite size_eexp_close_eexp_wrt_eexp using solve [auto] : lngen.

(* begin hide *)

Lemma size_eexp_open_eexp_wrt_eexp_rec_mutual :
(forall e1 e2 n1,
  size_eexp e1 <= size_eexp (open_eexp_wrt_eexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_eexp_open_eexp_wrt_eexp_rec :
forall e1 e2 n1,
  size_eexp e1 <= size_eexp (open_eexp_wrt_eexp_rec n1 e2 e1).
Proof.
pose proof size_eexp_open_eexp_wrt_eexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_eexp_open_eexp_wrt_eexp_rec : lngen.

(* end hide *)

Lemma size_eexp_open_eexp_wrt_eexp :
forall e1 e2,
  size_eexp e1 <= size_eexp (open_eexp_wrt_eexp e1 e2).
Proof.
unfold open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve size_eexp_open_eexp_wrt_eexp : lngen.

(* begin hide *)

Lemma size_eexp_open_eexp_wrt_eexp_rec_var_mutual :
(forall e1 l1 n1,
  size_eexp (open_eexp_wrt_eexp_rec n1 (ee_var_f l1) e1) = size_eexp e1).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_eexp_open_eexp_wrt_eexp_rec_var :
forall e1 l1 n1,
  size_eexp (open_eexp_wrt_eexp_rec n1 (ee_var_f l1) e1) = size_eexp e1.
Proof.
pose proof size_eexp_open_eexp_wrt_eexp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_eexp_open_eexp_wrt_eexp_rec_var : lngen.
Hint Rewrite size_eexp_open_eexp_wrt_eexp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_eexp_open_eexp_wrt_eexp_var :
forall e1 l1,
  size_eexp (open_eexp_wrt_eexp e1 (ee_var_f l1)) = size_eexp e1.
Proof.
unfold open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve size_eexp_open_eexp_wrt_eexp_var : lngen.
Hint Rewrite size_eexp_open_eexp_wrt_eexp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_eexp_wrt_eexp_S_mutual :
(forall n1 e1,
  degree_eexp_wrt_eexp n1 e1 ->
  degree_eexp_wrt_eexp (S n1) e1).
Proof.
apply_mutual_ind degree_eexp_wrt_eexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_eexp_wrt_eexp_S :
forall n1 e1,
  degree_eexp_wrt_eexp n1 e1 ->
  degree_eexp_wrt_eexp (S n1) e1.
Proof.
pose proof degree_eexp_wrt_eexp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_eexp_wrt_eexp_S : lngen.

Lemma degree_eexp_wrt_eexp_O :
forall n1 e1,
  degree_eexp_wrt_eexp O e1 ->
  degree_eexp_wrt_eexp n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_eexp_wrt_eexp_O : lngen.

(* begin hide *)

Lemma degree_eexp_wrt_eexp_close_eexp_wrt_eexp_rec_mutual :
(forall e1 l1 n1,
  degree_eexp_wrt_eexp n1 e1 ->
  degree_eexp_wrt_eexp (S n1) (close_eexp_wrt_eexp_rec n1 l1 e1)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_eexp_wrt_eexp_close_eexp_wrt_eexp_rec :
forall e1 l1 n1,
  degree_eexp_wrt_eexp n1 e1 ->
  degree_eexp_wrt_eexp (S n1) (close_eexp_wrt_eexp_rec n1 l1 e1).
Proof.
pose proof degree_eexp_wrt_eexp_close_eexp_wrt_eexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_eexp_wrt_eexp_close_eexp_wrt_eexp_rec : lngen.

(* end hide *)

Lemma degree_eexp_wrt_eexp_close_eexp_wrt_eexp :
forall e1 l1,
  degree_eexp_wrt_eexp 0 e1 ->
  degree_eexp_wrt_eexp 1 (close_eexp_wrt_eexp l1 e1).
Proof.
unfold close_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve degree_eexp_wrt_eexp_close_eexp_wrt_eexp : lngen.

(* begin hide *)

Lemma degree_eexp_wrt_eexp_close_eexp_wrt_eexp_rec_inv_mutual :
(forall e1 l1 n1,
  degree_eexp_wrt_eexp (S n1) (close_eexp_wrt_eexp_rec n1 l1 e1) ->
  degree_eexp_wrt_eexp n1 e1).
Proof.
apply_mutual_ind eexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_eexp_wrt_eexp_close_eexp_wrt_eexp_rec_inv :
forall e1 l1 n1,
  degree_eexp_wrt_eexp (S n1) (close_eexp_wrt_eexp_rec n1 l1 e1) ->
  degree_eexp_wrt_eexp n1 e1.
Proof.
pose proof degree_eexp_wrt_eexp_close_eexp_wrt_eexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_eexp_wrt_eexp_close_eexp_wrt_eexp_rec_inv : lngen.

(* end hide *)

Lemma degree_eexp_wrt_eexp_close_eexp_wrt_eexp_inv :
forall e1 l1,
  degree_eexp_wrt_eexp 1 (close_eexp_wrt_eexp l1 e1) ->
  degree_eexp_wrt_eexp 0 e1.
Proof.
unfold close_eexp_wrt_eexp; eauto with lngen.
Qed.

Hint Immediate degree_eexp_wrt_eexp_close_eexp_wrt_eexp_inv : lngen.

(* begin hide *)

Lemma degree_eexp_wrt_eexp_open_eexp_wrt_eexp_rec_mutual :
(forall e1 e2 n1,
  degree_eexp_wrt_eexp (S n1) e1 ->
  degree_eexp_wrt_eexp n1 e2 ->
  degree_eexp_wrt_eexp n1 (open_eexp_wrt_eexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_eexp_wrt_eexp_open_eexp_wrt_eexp_rec :
forall e1 e2 n1,
  degree_eexp_wrt_eexp (S n1) e1 ->
  degree_eexp_wrt_eexp n1 e2 ->
  degree_eexp_wrt_eexp n1 (open_eexp_wrt_eexp_rec n1 e2 e1).
Proof.
pose proof degree_eexp_wrt_eexp_open_eexp_wrt_eexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_eexp_wrt_eexp_open_eexp_wrt_eexp_rec : lngen.

(* end hide *)

Lemma degree_eexp_wrt_eexp_open_eexp_wrt_eexp :
forall e1 e2,
  degree_eexp_wrt_eexp 1 e1 ->
  degree_eexp_wrt_eexp 0 e2 ->
  degree_eexp_wrt_eexp 0 (open_eexp_wrt_eexp e1 e2).
Proof.
unfold open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve degree_eexp_wrt_eexp_open_eexp_wrt_eexp : lngen.

(* begin hide *)

Lemma degree_eexp_wrt_eexp_open_eexp_wrt_eexp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_eexp_wrt_eexp n1 (open_eexp_wrt_eexp_rec n1 e2 e1) ->
  degree_eexp_wrt_eexp (S n1) e1).
Proof.
apply_mutual_ind eexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_eexp_wrt_eexp_open_eexp_wrt_eexp_rec_inv :
forall e1 e2 n1,
  degree_eexp_wrt_eexp n1 (open_eexp_wrt_eexp_rec n1 e2 e1) ->
  degree_eexp_wrt_eexp (S n1) e1.
Proof.
pose proof degree_eexp_wrt_eexp_open_eexp_wrt_eexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_eexp_wrt_eexp_open_eexp_wrt_eexp_rec_inv : lngen.

(* end hide *)

Lemma degree_eexp_wrt_eexp_open_eexp_wrt_eexp_inv :
forall e1 e2,
  degree_eexp_wrt_eexp 0 (open_eexp_wrt_eexp e1 e2) ->
  degree_eexp_wrt_eexp 1 e1.
Proof.
unfold open_eexp_wrt_eexp; eauto with lngen.
Qed.

Hint Immediate degree_eexp_wrt_eexp_open_eexp_wrt_eexp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_eexp_wrt_eexp_rec_inj_mutual :
(forall e1 e2 l1 n1,
  close_eexp_wrt_eexp_rec n1 l1 e1 = close_eexp_wrt_eexp_rec n1 l1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind eexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_eexp_wrt_eexp_rec_inj :
forall e1 e2 l1 n1,
  close_eexp_wrt_eexp_rec n1 l1 e1 = close_eexp_wrt_eexp_rec n1 l1 e2 ->
  e1 = e2.
Proof.
pose proof close_eexp_wrt_eexp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_eexp_wrt_eexp_rec_inj : lngen.

(* end hide *)

Lemma close_eexp_wrt_eexp_inj :
forall e1 e2 l1,
  close_eexp_wrt_eexp l1 e1 = close_eexp_wrt_eexp l1 e2 ->
  e1 = e2.
Proof.
unfold close_eexp_wrt_eexp; eauto with lngen.
Qed.

Hint Immediate close_eexp_wrt_eexp_inj : lngen.

(* begin hide *)

Lemma close_eexp_wrt_eexp_rec_open_eexp_wrt_eexp_rec_mutual :
(forall e1 l1 n1,
  l1 `notin` fv_eexp e1 ->
  close_eexp_wrt_eexp_rec n1 l1 (open_eexp_wrt_eexp_rec n1 (ee_var_f l1) e1) = e1).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_eexp_wrt_eexp_rec_open_eexp_wrt_eexp_rec :
forall e1 l1 n1,
  l1 `notin` fv_eexp e1 ->
  close_eexp_wrt_eexp_rec n1 l1 (open_eexp_wrt_eexp_rec n1 (ee_var_f l1) e1) = e1.
Proof.
pose proof close_eexp_wrt_eexp_rec_open_eexp_wrt_eexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_eexp_wrt_eexp_rec_open_eexp_wrt_eexp_rec : lngen.
Hint Rewrite close_eexp_wrt_eexp_rec_open_eexp_wrt_eexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_eexp_wrt_eexp_open_eexp_wrt_eexp :
forall e1 l1,
  l1 `notin` fv_eexp e1 ->
  close_eexp_wrt_eexp l1 (open_eexp_wrt_eexp e1 (ee_var_f l1)) = e1.
Proof.
unfold close_eexp_wrt_eexp; unfold open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve close_eexp_wrt_eexp_open_eexp_wrt_eexp : lngen.
Hint Rewrite close_eexp_wrt_eexp_open_eexp_wrt_eexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_eexp_wrt_eexp_rec_close_eexp_wrt_eexp_rec_mutual :
(forall e1 l1 n1,
  open_eexp_wrt_eexp_rec n1 (ee_var_f l1) (close_eexp_wrt_eexp_rec n1 l1 e1) = e1).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_eexp_wrt_eexp_rec_close_eexp_wrt_eexp_rec :
forall e1 l1 n1,
  open_eexp_wrt_eexp_rec n1 (ee_var_f l1) (close_eexp_wrt_eexp_rec n1 l1 e1) = e1.
Proof.
pose proof open_eexp_wrt_eexp_rec_close_eexp_wrt_eexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_eexp_wrt_eexp_rec_close_eexp_wrt_eexp_rec : lngen.
Hint Rewrite open_eexp_wrt_eexp_rec_close_eexp_wrt_eexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_eexp_wrt_eexp_close_eexp_wrt_eexp :
forall e1 l1,
  open_eexp_wrt_eexp (close_eexp_wrt_eexp l1 e1) (ee_var_f l1) = e1.
Proof.
unfold close_eexp_wrt_eexp; unfold open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve open_eexp_wrt_eexp_close_eexp_wrt_eexp : lngen.
Hint Rewrite open_eexp_wrt_eexp_close_eexp_wrt_eexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_eexp_wrt_eexp_rec_inj_mutual :
(forall e2 e1 l1 n1,
  l1 `notin` fv_eexp e2 ->
  l1 `notin` fv_eexp e1 ->
  open_eexp_wrt_eexp_rec n1 (ee_var_f l1) e2 = open_eexp_wrt_eexp_rec n1 (ee_var_f l1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind eexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_eexp_wrt_eexp_rec_inj :
forall e2 e1 l1 n1,
  l1 `notin` fv_eexp e2 ->
  l1 `notin` fv_eexp e1 ->
  open_eexp_wrt_eexp_rec n1 (ee_var_f l1) e2 = open_eexp_wrt_eexp_rec n1 (ee_var_f l1) e1 ->
  e2 = e1.
Proof.
pose proof open_eexp_wrt_eexp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_eexp_wrt_eexp_rec_inj : lngen.

(* end hide *)

Lemma open_eexp_wrt_eexp_inj :
forall e2 e1 l1,
  l1 `notin` fv_eexp e2 ->
  l1 `notin` fv_eexp e1 ->
  open_eexp_wrt_eexp e2 (ee_var_f l1) = open_eexp_wrt_eexp e1 (ee_var_f l1) ->
  e2 = e1.
Proof.
unfold open_eexp_wrt_eexp; eauto with lngen.
Qed.

Hint Immediate open_eexp_wrt_eexp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_eexp_wrt_eexp_of_lc_eexp_mutual :
(forall e1,
  lc_eexp e1 ->
  degree_eexp_wrt_eexp 0 e1).
Proof.
apply_mutual_ind lc_eexp_mutind;
intros;
let l1 := fresh "l1" in pick_fresh l1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_eexp_wrt_eexp_of_lc_eexp :
forall e1,
  lc_eexp e1 ->
  degree_eexp_wrt_eexp 0 e1.
Proof.
pose proof degree_eexp_wrt_eexp_of_lc_eexp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_eexp_wrt_eexp_of_lc_eexp : lngen.

(* begin hide *)

Lemma lc_eexp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_eexp e1 = i1 ->
  degree_eexp_wrt_eexp 0 e1 ->
  lc_eexp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind eexp_mutind;
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

Lemma lc_eexp_of_degree :
forall e1,
  degree_eexp_wrt_eexp 0 e1 ->
  lc_eexp e1.
Proof.
intros e1; intros;
pose proof (lc_eexp_of_degree_size_mutual (size_eexp e1));
intuition eauto.
Qed.

Hint Resolve lc_eexp_of_degree : lngen.

Ltac typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac eexp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_eexp_wrt_eexp_of_lc_eexp in J1; clear H
          end).

Lemma lc_ee_abs_exists :
forall x1 A1 e1 l1 b1 B1,
  lc_eexp (open_eexp_wrt_eexp e1 (ee_var_f x1)) ->
  lc_eexp (ee_abs A1 e1 l1 b1 B1).
Proof.
intros; eexp_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_eexp (ee_abs _ _ _ _ _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_ee_abs_exists x1) : core.

Lemma lc_body_eexp_wrt_eexp :
forall e1 e2,
  body_eexp_wrt_eexp e1 ->
  lc_eexp e2 ->
  lc_eexp (open_eexp_wrt_eexp e1 e2).
Proof.
unfold body_eexp_wrt_eexp;
default_simp;
let l1 := fresh "x" in
pick_fresh l1;
specialize_all l1;
eexp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_eexp_wrt_eexp : lngen.

Lemma lc_body_ee_abs_2 :
forall A1 e1 l1 b1 B1,
  lc_eexp (ee_abs A1 e1 l1 b1 B1) ->
  body_eexp_wrt_eexp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_ee_abs_2 : lngen.

(* begin hide *)

Lemma lc_eexp_unique_mutual :
(forall e1 (proof2 proof3 : lc_eexp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_eexp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_eexp_unique :
forall e1 (proof2 proof3 : lc_eexp e1), proof2 = proof3.
Proof.
pose proof lc_eexp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_eexp_unique : lngen.

(* begin hide *)

Lemma lc_eexp_of_lc_set_eexp_mutual :
(forall e1, lc_set_eexp e1 -> lc_eexp e1).
Proof.
apply_mutual_ind lc_set_eexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_eexp_of_lc_set_eexp :
forall e1, lc_set_eexp e1 -> lc_eexp e1.
Proof.
pose proof lc_eexp_of_lc_set_eexp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_eexp_of_lc_set_eexp : lngen.

(* begin hide *)

Lemma lc_set_eexp_of_lc_eexp_size_mutual :
forall i1,
(forall e1,
  size_eexp e1 = i1 ->
  lc_eexp e1 ->
  lc_set_eexp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind eexp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_typ_of_lc_typ
 | apply lc_set_eexp_of_lc_eexp];
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

Lemma lc_set_eexp_of_lc_eexp :
forall e1,
  lc_eexp e1 ->
  lc_set_eexp e1.
Proof.
intros e1; intros;
pose proof (lc_set_eexp_of_lc_eexp_size_mutual (size_eexp e1));
intuition eauto.
Qed.

Hint Resolve lc_set_eexp_of_lc_eexp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_eexp_wrt_eexp_rec_degree_eexp_wrt_eexp_mutual :
(forall e1 l1 n1,
  degree_eexp_wrt_eexp n1 e1 ->
  l1 `notin` fv_eexp e1 ->
  close_eexp_wrt_eexp_rec n1 l1 e1 = e1).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_eexp_wrt_eexp_rec_degree_eexp_wrt_eexp :
forall e1 l1 n1,
  degree_eexp_wrt_eexp n1 e1 ->
  l1 `notin` fv_eexp e1 ->
  close_eexp_wrt_eexp_rec n1 l1 e1 = e1.
Proof.
pose proof close_eexp_wrt_eexp_rec_degree_eexp_wrt_eexp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_eexp_wrt_eexp_rec_degree_eexp_wrt_eexp : lngen.
Hint Rewrite close_eexp_wrt_eexp_rec_degree_eexp_wrt_eexp using solve [auto] : lngen.

(* end hide *)

Lemma close_eexp_wrt_eexp_lc_eexp :
forall e1 l1,
  lc_eexp e1 ->
  l1 `notin` fv_eexp e1 ->
  close_eexp_wrt_eexp l1 e1 = e1.
Proof.
unfold close_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve close_eexp_wrt_eexp_lc_eexp : lngen.
Hint Rewrite close_eexp_wrt_eexp_lc_eexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_eexp_wrt_eexp_rec_degree_eexp_wrt_eexp_mutual :
(forall e2 e1 n1,
  degree_eexp_wrt_eexp n1 e2 ->
  open_eexp_wrt_eexp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_eexp_wrt_eexp_rec_degree_eexp_wrt_eexp :
forall e2 e1 n1,
  degree_eexp_wrt_eexp n1 e2 ->
  open_eexp_wrt_eexp_rec n1 e1 e2 = e2.
Proof.
pose proof open_eexp_wrt_eexp_rec_degree_eexp_wrt_eexp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_eexp_wrt_eexp_rec_degree_eexp_wrt_eexp : lngen.
Hint Rewrite open_eexp_wrt_eexp_rec_degree_eexp_wrt_eexp using solve [auto] : lngen.

(* end hide *)

Lemma open_eexp_wrt_eexp_lc_eexp :
forall e2 e1,
  lc_eexp e2 ->
  open_eexp_wrt_eexp e2 e1 = e2.
Proof.
unfold open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve open_eexp_wrt_eexp_lc_eexp : lngen.
Hint Rewrite open_eexp_wrt_eexp_lc_eexp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_eexp_close_eexp_wrt_eexp_rec_mutual :
(forall e1 l1 n1,
  fv_eexp (close_eexp_wrt_eexp_rec n1 l1 e1) [=] remove l1 (fv_eexp e1)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_eexp_close_eexp_wrt_eexp_rec :
forall e1 l1 n1,
  fv_eexp (close_eexp_wrt_eexp_rec n1 l1 e1) [=] remove l1 (fv_eexp e1).
Proof.
pose proof fv_eexp_close_eexp_wrt_eexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_eexp_close_eexp_wrt_eexp_rec : lngen.
Hint Rewrite fv_eexp_close_eexp_wrt_eexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_eexp_close_eexp_wrt_eexp :
forall e1 l1,
  fv_eexp (close_eexp_wrt_eexp l1 e1) [=] remove l1 (fv_eexp e1).
Proof.
unfold close_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve fv_eexp_close_eexp_wrt_eexp : lngen.
Hint Rewrite fv_eexp_close_eexp_wrt_eexp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_eexp_open_eexp_wrt_eexp_rec_lower_mutual :
(forall e1 e2 n1,
  fv_eexp e1 [<=] fv_eexp (open_eexp_wrt_eexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_eexp_open_eexp_wrt_eexp_rec_lower :
forall e1 e2 n1,
  fv_eexp e1 [<=] fv_eexp (open_eexp_wrt_eexp_rec n1 e2 e1).
Proof.
pose proof fv_eexp_open_eexp_wrt_eexp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_eexp_open_eexp_wrt_eexp_rec_lower : lngen.

(* end hide *)

Lemma fv_eexp_open_eexp_wrt_eexp_lower :
forall e1 e2,
  fv_eexp e1 [<=] fv_eexp (open_eexp_wrt_eexp e1 e2).
Proof.
unfold open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve fv_eexp_open_eexp_wrt_eexp_lower : lngen.

(* begin hide *)

Lemma fv_eexp_open_eexp_wrt_eexp_rec_upper_mutual :
(forall e1 e2 n1,
  fv_eexp (open_eexp_wrt_eexp_rec n1 e2 e1) [<=] fv_eexp e2 `union` fv_eexp e1).
Proof.
apply_mutual_ind eexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_eexp_open_eexp_wrt_eexp_rec_upper :
forall e1 e2 n1,
  fv_eexp (open_eexp_wrt_eexp_rec n1 e2 e1) [<=] fv_eexp e2 `union` fv_eexp e1.
Proof.
pose proof fv_eexp_open_eexp_wrt_eexp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_eexp_open_eexp_wrt_eexp_rec_upper : lngen.

(* end hide *)

Lemma fv_eexp_open_eexp_wrt_eexp_upper :
forall e1 e2,
  fv_eexp (open_eexp_wrt_eexp e1 e2) [<=] fv_eexp e2 `union` fv_eexp e1.
Proof.
unfold open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve fv_eexp_open_eexp_wrt_eexp_upper : lngen.

(* begin hide *)

Lemma fv_eexp_subst_eexp_fresh_mutual :
(forall e1 e2 l1,
  l1 `notin` fv_eexp e1 ->
  fv_eexp (subst_eexp e2 l1 e1) [=] fv_eexp e1).
Proof.
apply_mutual_ind eexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_eexp_subst_eexp_fresh :
forall e1 e2 l1,
  l1 `notin` fv_eexp e1 ->
  fv_eexp (subst_eexp e2 l1 e1) [=] fv_eexp e1.
Proof.
pose proof fv_eexp_subst_eexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_eexp_subst_eexp_fresh : lngen.
Hint Rewrite fv_eexp_subst_eexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_eexp_subst_eexp_lower_mutual :
(forall e1 e2 l1,
  remove l1 (fv_eexp e1) [<=] fv_eexp (subst_eexp e2 l1 e1)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_eexp_subst_eexp_lower :
forall e1 e2 l1,
  remove l1 (fv_eexp e1) [<=] fv_eexp (subst_eexp e2 l1 e1).
Proof.
pose proof fv_eexp_subst_eexp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_eexp_subst_eexp_lower : lngen.

(* begin hide *)

Lemma fv_eexp_subst_eexp_notin_mutual :
(forall e1 e2 l1 l2,
  l2 `notin` fv_eexp e1 ->
  l2 `notin` fv_eexp e2 ->
  l2 `notin` fv_eexp (subst_eexp e2 l1 e1)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_eexp_subst_eexp_notin :
forall e1 e2 l1 l2,
  l2 `notin` fv_eexp e1 ->
  l2 `notin` fv_eexp e2 ->
  l2 `notin` fv_eexp (subst_eexp e2 l1 e1).
Proof.
pose proof fv_eexp_subst_eexp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_eexp_subst_eexp_notin : lngen.

(* begin hide *)

Lemma fv_eexp_subst_eexp_upper_mutual :
(forall e1 e2 l1,
  fv_eexp (subst_eexp e2 l1 e1) [<=] fv_eexp e2 `union` remove l1 (fv_eexp e1)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_eexp_subst_eexp_upper :
forall e1 e2 l1,
  fv_eexp (subst_eexp e2 l1 e1) [<=] fv_eexp e2 `union` remove l1 (fv_eexp e1).
Proof.
pose proof fv_eexp_subst_eexp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_eexp_subst_eexp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_eexp_close_eexp_wrt_eexp_rec_mutual :
(forall e2 e1 l1 l2 n1,
  degree_eexp_wrt_eexp n1 e1 ->
  l1 <> l2 ->
  l2 `notin` fv_eexp e1 ->
  subst_eexp e1 l1 (close_eexp_wrt_eexp_rec n1 l2 e2) = close_eexp_wrt_eexp_rec n1 l2 (subst_eexp e1 l1 e2)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_eexp_close_eexp_wrt_eexp_rec :
forall e2 e1 l1 l2 n1,
  degree_eexp_wrt_eexp n1 e1 ->
  l1 <> l2 ->
  l2 `notin` fv_eexp e1 ->
  subst_eexp e1 l1 (close_eexp_wrt_eexp_rec n1 l2 e2) = close_eexp_wrt_eexp_rec n1 l2 (subst_eexp e1 l1 e2).
Proof.
pose proof subst_eexp_close_eexp_wrt_eexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_eexp_close_eexp_wrt_eexp_rec : lngen.

Lemma subst_eexp_close_eexp_wrt_eexp :
forall e2 e1 l1 l2,
  lc_eexp e1 ->  l1 <> l2 ->
  l2 `notin` fv_eexp e1 ->
  subst_eexp e1 l1 (close_eexp_wrt_eexp l2 e2) = close_eexp_wrt_eexp l2 (subst_eexp e1 l1 e2).
Proof.
unfold close_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve subst_eexp_close_eexp_wrt_eexp : lngen.

(* begin hide *)

Lemma subst_eexp_degree_eexp_wrt_eexp_mutual :
(forall e1 e2 l1 n1,
  degree_eexp_wrt_eexp n1 e1 ->
  degree_eexp_wrt_eexp n1 e2 ->
  degree_eexp_wrt_eexp n1 (subst_eexp e2 l1 e1)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_eexp_degree_eexp_wrt_eexp :
forall e1 e2 l1 n1,
  degree_eexp_wrt_eexp n1 e1 ->
  degree_eexp_wrt_eexp n1 e2 ->
  degree_eexp_wrt_eexp n1 (subst_eexp e2 l1 e1).
Proof.
pose proof subst_eexp_degree_eexp_wrt_eexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_eexp_degree_eexp_wrt_eexp : lngen.

(* begin hide *)

Lemma subst_eexp_fresh_eq_mutual :
(forall e2 e1 l1,
  l1 `notin` fv_eexp e2 ->
  subst_eexp e1 l1 e2 = e2).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_eexp_fresh_eq :
forall e2 e1 l1,
  l1 `notin` fv_eexp e2 ->
  subst_eexp e1 l1 e2 = e2.
Proof.
pose proof subst_eexp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_eexp_fresh_eq : lngen.
Hint Rewrite subst_eexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_eexp_fresh_same_mutual :
(forall e2 e1 l1,
  l1 `notin` fv_eexp e1 ->
  l1 `notin` fv_eexp (subst_eexp e1 l1 e2)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_eexp_fresh_same :
forall e2 e1 l1,
  l1 `notin` fv_eexp e1 ->
  l1 `notin` fv_eexp (subst_eexp e1 l1 e2).
Proof.
pose proof subst_eexp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_eexp_fresh_same : lngen.

(* begin hide *)

Lemma subst_eexp_fresh_mutual :
(forall e2 e1 l1 l2,
  l1 `notin` fv_eexp e2 ->
  l1 `notin` fv_eexp e1 ->
  l1 `notin` fv_eexp (subst_eexp e1 l2 e2)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_eexp_fresh :
forall e2 e1 l1 l2,
  l1 `notin` fv_eexp e2 ->
  l1 `notin` fv_eexp e1 ->
  l1 `notin` fv_eexp (subst_eexp e1 l2 e2).
Proof.
pose proof subst_eexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_eexp_fresh : lngen.

Lemma subst_eexp_lc_eexp :
forall e1 e2 l1,
  lc_eexp e1 ->
  lc_eexp e2 ->
  lc_eexp (subst_eexp e2 l1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_eexp_lc_eexp : lngen.

(* begin hide *)

Lemma subst_eexp_open_eexp_wrt_eexp_rec_mutual :
(forall e3 e1 e2 l1 n1,
  lc_eexp e1 ->
  subst_eexp e1 l1 (open_eexp_wrt_eexp_rec n1 e2 e3) = open_eexp_wrt_eexp_rec n1 (subst_eexp e1 l1 e2) (subst_eexp e1 l1 e3)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_eexp_open_eexp_wrt_eexp_rec :
forall e3 e1 e2 l1 n1,
  lc_eexp e1 ->
  subst_eexp e1 l1 (open_eexp_wrt_eexp_rec n1 e2 e3) = open_eexp_wrt_eexp_rec n1 (subst_eexp e1 l1 e2) (subst_eexp e1 l1 e3).
Proof.
pose proof subst_eexp_open_eexp_wrt_eexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_eexp_open_eexp_wrt_eexp_rec : lngen.

(* end hide *)

Lemma subst_eexp_open_eexp_wrt_eexp :
forall e3 e1 e2 l1,
  lc_eexp e1 ->
  subst_eexp e1 l1 (open_eexp_wrt_eexp e3 e2) = open_eexp_wrt_eexp (subst_eexp e1 l1 e3) (subst_eexp e1 l1 e2).
Proof.
unfold open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve subst_eexp_open_eexp_wrt_eexp : lngen.

Lemma subst_eexp_open_eexp_wrt_eexp_var :
forall e2 e1 l1 l2,
  l1 <> l2 ->
  lc_eexp e1 ->
  open_eexp_wrt_eexp (subst_eexp e1 l1 e2) (ee_var_f l2) = subst_eexp e1 l1 (open_eexp_wrt_eexp e2 (ee_var_f l2)).
Proof.
intros; rewrite subst_eexp_open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve subst_eexp_open_eexp_wrt_eexp_var : lngen.

(* begin hide *)

Lemma subst_eexp_spec_rec_mutual :
(forall e1 e2 l1 n1,
  subst_eexp e2 l1 e1 = open_eexp_wrt_eexp_rec n1 e2 (close_eexp_wrt_eexp_rec n1 l1 e1)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_eexp_spec_rec :
forall e1 e2 l1 n1,
  subst_eexp e2 l1 e1 = open_eexp_wrt_eexp_rec n1 e2 (close_eexp_wrt_eexp_rec n1 l1 e1).
Proof.
pose proof subst_eexp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_eexp_spec_rec : lngen.

(* end hide *)

Lemma subst_eexp_spec :
forall e1 e2 l1,
  subst_eexp e2 l1 e1 = open_eexp_wrt_eexp (close_eexp_wrt_eexp l1 e1) e2.
Proof.
unfold close_eexp_wrt_eexp; unfold open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve subst_eexp_spec : lngen.

(* begin hide *)

Lemma subst_eexp_subst_eexp_mutual :
(forall e1 e2 e3 l2 l1,
  l2 `notin` fv_eexp e2 ->
  l2 <> l1 ->
  subst_eexp e2 l1 (subst_eexp e3 l2 e1) = subst_eexp (subst_eexp e2 l1 e3) l2 (subst_eexp e2 l1 e1)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_eexp_subst_eexp :
forall e1 e2 e3 l2 l1,
  l2 `notin` fv_eexp e2 ->
  l2 <> l1 ->
  subst_eexp e2 l1 (subst_eexp e3 l2 e1) = subst_eexp (subst_eexp e2 l1 e3) l2 (subst_eexp e2 l1 e1).
Proof.
pose proof subst_eexp_subst_eexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_eexp_subst_eexp : lngen.

(* begin hide *)

Lemma subst_eexp_close_eexp_wrt_eexp_rec_open_eexp_wrt_eexp_rec_mutual :
(forall e2 e1 l1 l2 n1,
  l2 `notin` fv_eexp e2 ->
  l2 `notin` fv_eexp e1 ->
  l2 <> l1 ->
  degree_eexp_wrt_eexp n1 e1 ->
  subst_eexp e1 l1 e2 = close_eexp_wrt_eexp_rec n1 l2 (subst_eexp e1 l1 (open_eexp_wrt_eexp_rec n1 (ee_var_f l2) e2))).
Proof.
apply_mutual_ind eexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_eexp_close_eexp_wrt_eexp_rec_open_eexp_wrt_eexp_rec :
forall e2 e1 l1 l2 n1,
  l2 `notin` fv_eexp e2 ->
  l2 `notin` fv_eexp e1 ->
  l2 <> l1 ->
  degree_eexp_wrt_eexp n1 e1 ->
  subst_eexp e1 l1 e2 = close_eexp_wrt_eexp_rec n1 l2 (subst_eexp e1 l1 (open_eexp_wrt_eexp_rec n1 (ee_var_f l2) e2)).
Proof.
pose proof subst_eexp_close_eexp_wrt_eexp_rec_open_eexp_wrt_eexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_eexp_close_eexp_wrt_eexp_rec_open_eexp_wrt_eexp_rec : lngen.

(* end hide *)

Lemma subst_eexp_close_eexp_wrt_eexp_open_eexp_wrt_eexp :
forall e2 e1 l1 l2,
  l2 `notin` fv_eexp e2 ->
  l2 `notin` fv_eexp e1 ->
  l2 <> l1 ->
  lc_eexp e1 ->
  subst_eexp e1 l1 e2 = close_eexp_wrt_eexp l2 (subst_eexp e1 l1 (open_eexp_wrt_eexp e2 (ee_var_f l2))).
Proof.
unfold close_eexp_wrt_eexp; unfold open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve subst_eexp_close_eexp_wrt_eexp_open_eexp_wrt_eexp : lngen.

Lemma subst_eexp_ee_abs :
forall x1 A1 e2 l2 b1 B1 e1 l1,
  lc_eexp e1 ->
  x1 `notin` fv_eexp e1 `union` fv_eexp e2 `union` singleton l1 ->
  subst_eexp e1 l1 (ee_abs A1 e2 l2 b1 B1) = ee_abs (A1) (close_eexp_wrt_eexp x1 (subst_eexp e1 l1 (open_eexp_wrt_eexp e2 (ee_var_f x1)))) (l2) (b1) (B1).
Proof.
default_simp.
Qed.

Hint Resolve subst_eexp_ee_abs : lngen.

(* begin hide *)

Lemma subst_eexp_intro_rec_mutual :
(forall e1 l1 e2 n1,
  l1 `notin` fv_eexp e1 ->
  open_eexp_wrt_eexp_rec n1 e2 e1 = subst_eexp e2 l1 (open_eexp_wrt_eexp_rec n1 (ee_var_f l1) e1)).
Proof.
apply_mutual_ind eexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_eexp_intro_rec :
forall e1 l1 e2 n1,
  l1 `notin` fv_eexp e1 ->
  open_eexp_wrt_eexp_rec n1 e2 e1 = subst_eexp e2 l1 (open_eexp_wrt_eexp_rec n1 (ee_var_f l1) e1).
Proof.
pose proof subst_eexp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_eexp_intro_rec : lngen.
Hint Rewrite subst_eexp_intro_rec using solve [auto] : lngen.

Lemma subst_eexp_intro :
forall l1 e1 e2,
  l1 `notin` fv_eexp e1 ->
  open_eexp_wrt_eexp e1 e2 = subst_eexp e2 l1 (open_eexp_wrt_eexp e1 (ee_var_f l1)).
Proof.
unfold open_eexp_wrt_eexp; default_simp.
Qed.

Hint Resolve subst_eexp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
