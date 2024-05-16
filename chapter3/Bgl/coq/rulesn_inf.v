Require Import Coq.Arith.Wf_nat.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export syntaxn_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme nexp_ind' := Induction for nexp Sort Prop.

Definition nexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  nexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9.

Scheme nexp_rec' := Induction for nexp Sort Set.

Definition nexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  nexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_nexp_wrt_nexp_rec (n1 : nat) (x1 : var) (e1 : nexp) {struct e1} : nexp :=
  match e1 with
    | ne_var_f x2 => if (x1 == x2) then (ne_var_b n1) else (ne_var_f x2)
    | ne_var_b n2 => if (lt_ge_dec n2 n1) then (ne_var_b n2) else (ne_var_b (S n2))
    | ne_lit i => ne_lit i
    | ne_abs e2 => ne_abs (close_nexp_wrt_nexp_rec (S n1) x1 e2)
    | ne_app e2 e3 => ne_app (close_nexp_wrt_nexp_rec n1 x1 e2) (close_nexp_wrt_nexp_rec n1 x1 e3)
    | ne_pro e2 e3 => ne_pro (close_nexp_wrt_nexp_rec n1 x1 e2) (close_nexp_wrt_nexp_rec n1 x1 e3)
    | ne_l e2  => ne_l (close_nexp_wrt_nexp_rec n1 x1 e2) 
    | ne_r e2  => ne_r (close_nexp_wrt_nexp_rec n1 x1 e2) 
  end.

Definition close_nexp_wrt_nexp x1 e1 := close_nexp_wrt_nexp_rec 0 x1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_nexp (e1 : nexp) {struct e1} : nat :=
  match e1 with
    | ne_var_f x1 => 1
    | ne_var_b n1 => 1
    | ne_lit i => 1
    | ne_abs e2 => 1 + (size_nexp e2)
    | ne_app e2 e3 => 1 + (size_nexp e2) + (size_nexp e3)
    | ne_pro e2 e3 => 1 + (size_nexp e2) + (size_nexp e3)
    | ne_l e2 => 1 + (size_nexp e2)
    | ne_r e2 => 1 + (size_nexp e2)
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_nexp_wrt_nexp : nat -> nexp -> Prop :=
  | degree_wrt_nexp_ne_var_f : forall n1 x1,
    degree_nexp_wrt_nexp n1 (ne_var_f x1)
  | degree_wrt_nexp_ne_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_nexp_wrt_nexp n1 (ne_var_b n2)
  | degree_wrt_nexp_ne_lit : forall n1 i ,
    degree_nexp_wrt_nexp n1 (ne_lit i )
  | degree_wrt_nexp_ne_abs : forall n1 e1,
    degree_nexp_wrt_nexp (S n1) e1 ->
    degree_nexp_wrt_nexp n1 (ne_abs e1)
  | degree_wrt_nexp_ne_app : forall n1 e1 e2,
    degree_nexp_wrt_nexp n1 e1 ->
    degree_nexp_wrt_nexp n1 e2 ->
    degree_nexp_wrt_nexp n1 (ne_app e1 e2)
  | degree_wrt_nexp_ne_pro : forall n1 e1 e2,
    degree_nexp_wrt_nexp n1 e1 ->
    degree_nexp_wrt_nexp n1 e2 ->
    degree_nexp_wrt_nexp n1 (ne_pro e1 e2)
  | degree_wrt_nexp_ne_l : forall n1 e1,
    degree_nexp_wrt_nexp n1 e1 ->
    degree_nexp_wrt_nexp n1 (ne_l e1 )
  | degree_wrt_nexp_ne_r : forall n1 e1,
    degree_nexp_wrt_nexp n1 e1 ->
    degree_nexp_wrt_nexp n1 (ne_r e1 )
.

Scheme degree_nexp_wrt_nexp_ind' := Induction for degree_nexp_wrt_nexp Sort Prop.

Definition degree_nexp_wrt_nexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  degree_nexp_wrt_nexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 .

Hint Constructors degree_nexp_wrt_nexp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_nexp : nexp -> Set :=
  | lc_set_ne_var_f : forall x1,
    lc_set_nexp (ne_var_f x1)
  | lc_set_ne_lit : forall i,
    lc_set_nexp (ne_lit i)
  | lc_set_ne_abs : forall e1,
    (forall x1 : var, lc_set_nexp (open_nexp_wrt_nexp e1 (ne_var_f x1))) ->
    lc_set_nexp (ne_abs e1)
  | lc_set_ne_app : forall e1 e2,
    lc_set_nexp e1 ->
    lc_set_nexp e2 ->
    lc_set_nexp (ne_app e1 e2)
    | lc_set_ne_pro : forall e1 e2,
    lc_set_nexp e1 ->
    lc_set_nexp e2 ->
    lc_set_nexp (ne_pro e1 e2)
    | lc_set_ne_l : forall e1 ,
    lc_set_nexp e1 ->
    lc_set_nexp (ne_l e1 )
    | lc_set_ne_r : forall e1 ,
    lc_set_nexp e1 ->
    lc_set_nexp (ne_r e1 )
    .

Scheme lc_nexp_ind' := Induction for lc_nexp Sort Prop.

Definition lc_nexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 =>
  lc_nexp_ind' H1 H2 H3 H4 H5 H6  H7 H8 H9 .

Scheme lc_set_nexp_ind' := Induction for lc_set_nexp Sort Prop.

Definition lc_set_nexp_mutind :=
  fun H1 H2 H3 H4 H5 H6  H7 H8 H9  =>
  lc_set_nexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 .

Scheme lc_set_nexp_rec' := Induction for lc_set_nexp Sort Set.

Definition lc_set_nexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6  H7 H8 H9 =>
  lc_set_nexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 .

Hint Constructors lc_nexp : core lngen.

Hint Constructors lc_set_nexp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_nexp_wrt_nexp e1 := forall x1, lc_nexp (open_nexp_wrt_nexp e1 (ne_var_f x1)).

Hint Unfold body_nexp_wrt_nexp : core.


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

Lemma size_nexp_min_mutual :
(forall e1, 1 <= size_nexp e1).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_nexp_min :
forall e1, 1 <= size_nexp e1.
Proof.
pose proof size_nexp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_nexp_min : lngen.

(* begin hide *)

Lemma size_nexp_close_nexp_wrt_nexp_rec_mutual :
(forall e1 x1 n1,
  size_nexp (close_nexp_wrt_nexp_rec n1 x1 e1) = size_nexp e1).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_nexp_close_nexp_wrt_nexp_rec :
forall e1 x1 n1,
  size_nexp (close_nexp_wrt_nexp_rec n1 x1 e1) = size_nexp e1.
Proof.
pose proof size_nexp_close_nexp_wrt_nexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_nexp_close_nexp_wrt_nexp_rec : lngen.
Hint Rewrite size_nexp_close_nexp_wrt_nexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_nexp_close_nexp_wrt_nexp :
forall e1 x1,
  size_nexp (close_nexp_wrt_nexp x1 e1) = size_nexp e1.
Proof.
unfold close_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve size_nexp_close_nexp_wrt_nexp : lngen.
Hint Rewrite size_nexp_close_nexp_wrt_nexp using solve [auto] : lngen.

(* begin hide *)

Lemma size_nexp_open_nexp_wrt_nexp_rec_mutual :
(forall e1 e2 n1,
  size_nexp e1 <= size_nexp (open_nexp_wrt_nexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_nexp_open_nexp_wrt_nexp_rec :
forall e1 e2 n1,
  size_nexp e1 <= size_nexp (open_nexp_wrt_nexp_rec n1 e2 e1).
Proof.
pose proof size_nexp_open_nexp_wrt_nexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_nexp_open_nexp_wrt_nexp_rec : lngen.

(* end hide *)

Lemma size_nexp_open_nexp_wrt_nexp :
forall e1 e2,
  size_nexp e1 <= size_nexp (open_nexp_wrt_nexp e1 e2).
Proof.
unfold open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve size_nexp_open_nexp_wrt_nexp : lngen.

(* begin hide *)

Lemma size_nexp_open_nexp_wrt_nexp_rec_var_mutual :
(forall e1 x1 n1,
  size_nexp (open_nexp_wrt_nexp_rec n1 (ne_var_f x1) e1) = size_nexp e1).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_nexp_open_nexp_wrt_nexp_rec_var :
forall e1 x1 n1,
  size_nexp (open_nexp_wrt_nexp_rec n1 (ne_var_f x1) e1) = size_nexp e1.
Proof.
pose proof size_nexp_open_nexp_wrt_nexp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_nexp_open_nexp_wrt_nexp_rec_var : lngen.
Hint Rewrite size_nexp_open_nexp_wrt_nexp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_nexp_open_nexp_wrt_nexp_var :
forall e1 x1,
  size_nexp (open_nexp_wrt_nexp e1 (ne_var_f x1)) = size_nexp e1.
Proof.
unfold open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve size_nexp_open_nexp_wrt_nexp_var : lngen.
Hint Rewrite size_nexp_open_nexp_wrt_nexp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_nexp_wrt_nexp_S_mutual :
(forall n1 e1,
  degree_nexp_wrt_nexp n1 e1 ->
  degree_nexp_wrt_nexp (S n1) e1).
Proof.
apply_mutual_ind degree_nexp_wrt_nexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_nexp_wrt_nexp_S :
forall n1 e1,
  degree_nexp_wrt_nexp n1 e1 ->
  degree_nexp_wrt_nexp (S n1) e1.
Proof.
pose proof degree_nexp_wrt_nexp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_nexp_wrt_nexp_S : lngen.

Lemma degree_nexp_wrt_nexp_O :
forall n1 e1,
  degree_nexp_wrt_nexp O e1 ->
  degree_nexp_wrt_nexp n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_nexp_wrt_nexp_O : lngen.

(* begin hide *)

Lemma degree_nexp_wrt_nexp_close_nexp_wrt_nexp_rec_mutual :
(forall e1 x1 n1,
  degree_nexp_wrt_nexp n1 e1 ->
  degree_nexp_wrt_nexp (S n1) (close_nexp_wrt_nexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_nexp_wrt_nexp_close_nexp_wrt_nexp_rec :
forall e1 x1 n1,
  degree_nexp_wrt_nexp n1 e1 ->
  degree_nexp_wrt_nexp (S n1) (close_nexp_wrt_nexp_rec n1 x1 e1).
Proof.
pose proof degree_nexp_wrt_nexp_close_nexp_wrt_nexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_nexp_wrt_nexp_close_nexp_wrt_nexp_rec : lngen.

(* end hide *)

Lemma degree_nexp_wrt_nexp_close_nexp_wrt_nexp :
forall e1 x1,
  degree_nexp_wrt_nexp 0 e1 ->
  degree_nexp_wrt_nexp 1 (close_nexp_wrt_nexp x1 e1).
Proof.
unfold close_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve degree_nexp_wrt_nexp_close_nexp_wrt_nexp : lngen.

(* begin hide *)

Lemma degree_nexp_wrt_nexp_close_nexp_wrt_nexp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_nexp_wrt_nexp (S n1) (close_nexp_wrt_nexp_rec n1 x1 e1) ->
  degree_nexp_wrt_nexp n1 e1).
Proof.
apply_mutual_ind nexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_nexp_wrt_nexp_close_nexp_wrt_nexp_rec_inv :
forall e1 x1 n1,
  degree_nexp_wrt_nexp (S n1) (close_nexp_wrt_nexp_rec n1 x1 e1) ->
  degree_nexp_wrt_nexp n1 e1.
Proof.
pose proof degree_nexp_wrt_nexp_close_nexp_wrt_nexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_nexp_wrt_nexp_close_nexp_wrt_nexp_rec_inv : lngen.

(* end hide *)

Lemma degree_nexp_wrt_nexp_close_nexp_wrt_nexp_inv :
forall e1 x1,
  degree_nexp_wrt_nexp 1 (close_nexp_wrt_nexp x1 e1) ->
  degree_nexp_wrt_nexp 0 e1.
Proof.
unfold close_nexp_wrt_nexp; eauto with lngen.
Qed.

Hint Immediate degree_nexp_wrt_nexp_close_nexp_wrt_nexp_inv : lngen.

(* begin hide *)

Lemma degree_nexp_wrt_nexp_open_nexp_wrt_nexp_rec_mutual :
(forall e1 e2 n1,
  degree_nexp_wrt_nexp (S n1) e1 ->
  degree_nexp_wrt_nexp n1 e2 ->
  degree_nexp_wrt_nexp n1 (open_nexp_wrt_nexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_nexp_wrt_nexp_open_nexp_wrt_nexp_rec :
forall e1 e2 n1,
  degree_nexp_wrt_nexp (S n1) e1 ->
  degree_nexp_wrt_nexp n1 e2 ->
  degree_nexp_wrt_nexp n1 (open_nexp_wrt_nexp_rec n1 e2 e1).
Proof.
pose proof degree_nexp_wrt_nexp_open_nexp_wrt_nexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_nexp_wrt_nexp_open_nexp_wrt_nexp_rec : lngen.

(* end hide *)

Lemma degree_nexp_wrt_nexp_open_nexp_wrt_nexp :
forall e1 e2,
  degree_nexp_wrt_nexp 1 e1 ->
  degree_nexp_wrt_nexp 0 e2 ->
  degree_nexp_wrt_nexp 0 (open_nexp_wrt_nexp e1 e2).
Proof.
unfold open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve degree_nexp_wrt_nexp_open_nexp_wrt_nexp : lngen.

(* begin hide *)

Lemma degree_nexp_wrt_nexp_open_nexp_wrt_nexp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_nexp_wrt_nexp n1 (open_nexp_wrt_nexp_rec n1 e2 e1) ->
  degree_nexp_wrt_nexp (S n1) e1).
Proof.
apply_mutual_ind nexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_nexp_wrt_nexp_open_nexp_wrt_nexp_rec_inv :
forall e1 e2 n1,
  degree_nexp_wrt_nexp n1 (open_nexp_wrt_nexp_rec n1 e2 e1) ->
  degree_nexp_wrt_nexp (S n1) e1.
Proof.
pose proof degree_nexp_wrt_nexp_open_nexp_wrt_nexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_nexp_wrt_nexp_open_nexp_wrt_nexp_rec_inv : lngen.

(* end hide *)

Lemma degree_nexp_wrt_nexp_open_nexp_wrt_nexp_inv :
forall e1 e2,
  degree_nexp_wrt_nexp 0 (open_nexp_wrt_nexp e1 e2) ->
  degree_nexp_wrt_nexp 1 e1.
Proof.
unfold open_nexp_wrt_nexp; eauto with lngen.
Qed.

Hint Immediate degree_nexp_wrt_nexp_open_nexp_wrt_nexp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_nexp_wrt_nexp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_nexp_wrt_nexp_rec n1 x1 e1 = close_nexp_wrt_nexp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind nexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_nexp_wrt_nexp_rec_inj :
forall e1 e2 x1 n1,
  close_nexp_wrt_nexp_rec n1 x1 e1 = close_nexp_wrt_nexp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_nexp_wrt_nexp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_nexp_wrt_nexp_rec_inj : lngen.

(* end hide *)

Lemma close_nexp_wrt_nexp_inj :
forall e1 e2 x1,
  close_nexp_wrt_nexp x1 e1 = close_nexp_wrt_nexp x1 e2 ->
  e1 = e2.
Proof.
unfold close_nexp_wrt_nexp; eauto with lngen.
Qed.

Hint Immediate close_nexp_wrt_nexp_inj : lngen.

(* begin hide *)

Lemma close_nexp_wrt_nexp_rec_open_nexp_wrt_nexp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fv_nexp e1 ->
  close_nexp_wrt_nexp_rec n1 x1 (open_nexp_wrt_nexp_rec n1 (ne_var_f x1) e1) = e1).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_nexp_wrt_nexp_rec_open_nexp_wrt_nexp_rec :
forall e1 x1 n1,
  x1 `notin` fv_nexp e1 ->
  close_nexp_wrt_nexp_rec n1 x1 (open_nexp_wrt_nexp_rec n1 (ne_var_f x1) e1) = e1.
Proof.
pose proof close_nexp_wrt_nexp_rec_open_nexp_wrt_nexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_nexp_wrt_nexp_rec_open_nexp_wrt_nexp_rec : lngen.
Hint Rewrite close_nexp_wrt_nexp_rec_open_nexp_wrt_nexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_nexp_wrt_nexp_open_nexp_wrt_nexp :
forall e1 x1,
  x1 `notin` fv_nexp e1 ->
  close_nexp_wrt_nexp x1 (open_nexp_wrt_nexp e1 (ne_var_f x1)) = e1.
Proof.
unfold close_nexp_wrt_nexp; unfold open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve close_nexp_wrt_nexp_open_nexp_wrt_nexp : lngen.
Hint Rewrite close_nexp_wrt_nexp_open_nexp_wrt_nexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_nexp_wrt_nexp_rec_close_nexp_wrt_nexp_rec_mutual :
(forall e1 x1 n1,
  open_nexp_wrt_nexp_rec n1 (ne_var_f x1) (close_nexp_wrt_nexp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_nexp_wrt_nexp_rec_close_nexp_wrt_nexp_rec :
forall e1 x1 n1,
  open_nexp_wrt_nexp_rec n1 (ne_var_f x1) (close_nexp_wrt_nexp_rec n1 x1 e1) = e1.
Proof.
pose proof open_nexp_wrt_nexp_rec_close_nexp_wrt_nexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_nexp_wrt_nexp_rec_close_nexp_wrt_nexp_rec : lngen.
Hint Rewrite open_nexp_wrt_nexp_rec_close_nexp_wrt_nexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_nexp_wrt_nexp_close_nexp_wrt_nexp :
forall e1 x1,
  open_nexp_wrt_nexp (close_nexp_wrt_nexp x1 e1) (ne_var_f x1) = e1.
Proof.
unfold close_nexp_wrt_nexp; unfold open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve open_nexp_wrt_nexp_close_nexp_wrt_nexp : lngen.
Hint Rewrite open_nexp_wrt_nexp_close_nexp_wrt_nexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_nexp_wrt_nexp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fv_nexp e2 ->
  x1 `notin` fv_nexp e1 ->
  open_nexp_wrt_nexp_rec n1 (ne_var_f x1) e2 = open_nexp_wrt_nexp_rec n1 (ne_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind nexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_nexp_wrt_nexp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_nexp e2 ->
  x1 `notin` fv_nexp e1 ->
  open_nexp_wrt_nexp_rec n1 (ne_var_f x1) e2 = open_nexp_wrt_nexp_rec n1 (ne_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_nexp_wrt_nexp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_nexp_wrt_nexp_rec_inj : lngen.

(* end hide *)

Lemma open_nexp_wrt_nexp_inj :
forall e2 e1 x1,
  x1 `notin` fv_nexp e2 ->
  x1 `notin` fv_nexp e1 ->
  open_nexp_wrt_nexp e2 (ne_var_f x1) = open_nexp_wrt_nexp e1 (ne_var_f x1) ->
  e2 = e1.
Proof.
unfold open_nexp_wrt_nexp; eauto with lngen.
Qed.

Hint Immediate open_nexp_wrt_nexp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_nexp_wrt_nexp_of_lc_nexp_mutual :
(forall e1,
  lc_nexp e1 ->
  degree_nexp_wrt_nexp 0 e1).
Proof.
apply_mutual_ind lc_nexp_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_nexp_wrt_nexp_of_lc_nexp :
forall e1,
  lc_nexp e1 ->
  degree_nexp_wrt_nexp 0 e1.
Proof.
pose proof degree_nexp_wrt_nexp_of_lc_nexp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_nexp_wrt_nexp_of_lc_nexp : lngen.

(* begin hide *)

Lemma lc_nexp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_nexp e1 = i1 ->
  degree_nexp_wrt_nexp 0 e1 ->
  lc_nexp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind nexp_mutind;
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

Lemma lc_nexp_of_degree :
forall e1,
  degree_nexp_wrt_nexp 0 e1 ->
  lc_nexp e1.
Proof.
intros e1; intros;
pose proof (lc_nexp_of_degree_size_mutual (size_nexp e1));
intuition eauto.
Qed.

Hint Resolve lc_nexp_of_degree : lngen.

Ltac nexp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_nexp_wrt_nexp_of_lc_nexp in J1; clear H
          end).

Lemma lc_ne_abs_exists :
forall x1 e1,
  lc_nexp (open_nexp_wrt_nexp e1 (ne_var_f x1)) ->
  lc_nexp (ne_abs e1).
Proof.
intros; nexp_lc_exists_tac; eauto with lngen.
Qed.

Hint Extern 1 (lc_nexp (ne_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_ne_abs_exists x1) : core.

Lemma lc_body_nexp_wrt_nexp :
forall e1 e2,
  body_nexp_wrt_nexp e1 ->
  lc_nexp e2 ->
  lc_nexp (open_nexp_wrt_nexp e1 e2).
Proof.
unfold body_nexp_wrt_nexp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
nexp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_nexp_wrt_nexp : lngen.

Lemma lc_body_ne_abs_1 :
forall e1,
  lc_nexp (ne_abs e1) ->
  body_nexp_wrt_nexp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_ne_abs_1 : lngen.

(* begin hide *)

Lemma lc_nexp_unique_mutual :
(forall e1 (proof2 proof3 : lc_nexp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_nexp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_nexp_unique :
forall e1 (proof2 proof3 : lc_nexp e1), proof2 = proof3.
Proof.
pose proof lc_nexp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_nexp_unique : lngen.

(* begin hide *)

Lemma lc_nexp_of_lc_set_nexp_mutual :
(forall e1, lc_set_nexp e1 -> lc_nexp e1).
Proof.
apply_mutual_ind lc_set_nexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_nexp_of_lc_set_nexp :
forall e1, lc_set_nexp e1 -> lc_nexp e1.
Proof.
pose proof lc_nexp_of_lc_set_nexp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_nexp_of_lc_set_nexp : lngen.

(* begin hide *)

Lemma lc_set_nexp_of_lc_nexp_size_mutual :
forall i1,
(forall e1,
  size_nexp e1 = i1 ->
  lc_nexp e1 ->
  lc_set_nexp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind nexp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_nexp_of_lc_nexp];
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

Lemma lc_set_nexp_of_lc_nexp :
forall e1,
  lc_nexp e1 ->
  lc_set_nexp e1.
Proof.
intros e1; intros;
pose proof (lc_set_nexp_of_lc_nexp_size_mutual (size_nexp e1));
intuition eauto.
Qed.

Hint Resolve lc_set_nexp_of_lc_nexp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_nexp_wrt_nexp_rec_degree_nexp_wrt_nexp_mutual :
(forall e1 x1 n1,
  degree_nexp_wrt_nexp n1 e1 ->
  x1 `notin` fv_nexp e1 ->
  close_nexp_wrt_nexp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_nexp_wrt_nexp_rec_degree_nexp_wrt_nexp :
forall e1 x1 n1,
  degree_nexp_wrt_nexp n1 e1 ->
  x1 `notin` fv_nexp e1 ->
  close_nexp_wrt_nexp_rec n1 x1 e1 = e1.
Proof.
pose proof close_nexp_wrt_nexp_rec_degree_nexp_wrt_nexp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_nexp_wrt_nexp_rec_degree_nexp_wrt_nexp : lngen.
Hint Rewrite close_nexp_wrt_nexp_rec_degree_nexp_wrt_nexp using solve [auto] : lngen.

(* end hide *)

Lemma close_nexp_wrt_nexp_lc_nexp :
forall e1 x1,
  lc_nexp e1 ->
  x1 `notin` fv_nexp e1 ->
  close_nexp_wrt_nexp x1 e1 = e1.
Proof.
unfold close_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve close_nexp_wrt_nexp_lc_nexp : lngen.
Hint Rewrite close_nexp_wrt_nexp_lc_nexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_nexp_wrt_nexp_rec_degree_nexp_wrt_nexp_mutual :
(forall e2 e1 n1,
  degree_nexp_wrt_nexp n1 e2 ->
  open_nexp_wrt_nexp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_nexp_wrt_nexp_rec_degree_nexp_wrt_nexp :
forall e2 e1 n1,
  degree_nexp_wrt_nexp n1 e2 ->
  open_nexp_wrt_nexp_rec n1 e1 e2 = e2.
Proof.
pose proof open_nexp_wrt_nexp_rec_degree_nexp_wrt_nexp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_nexp_wrt_nexp_rec_degree_nexp_wrt_nexp : lngen.
Hint Rewrite open_nexp_wrt_nexp_rec_degree_nexp_wrt_nexp using solve [auto] : lngen.

(* end hide *)

Lemma open_nexp_wrt_nexp_lc_nexp :
forall e2 e1,
  lc_nexp e2 ->
  open_nexp_wrt_nexp e2 e1 = e2.
Proof.
unfold open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve open_nexp_wrt_nexp_lc_nexp : lngen.
Hint Rewrite open_nexp_wrt_nexp_lc_nexp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_nexp_close_nexp_wrt_nexp_rec_mutual :
(forall e1 x1 n1,
  fv_nexp (close_nexp_wrt_nexp_rec n1 x1 e1) [=] remove x1 (fv_nexp e1)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_nexp_close_nexp_wrt_nexp_rec :
forall e1 x1 n1,
  fv_nexp (close_nexp_wrt_nexp_rec n1 x1 e1) [=] remove x1 (fv_nexp e1).
Proof.
pose proof fv_nexp_close_nexp_wrt_nexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_nexp_close_nexp_wrt_nexp_rec : lngen.
Hint Rewrite fv_nexp_close_nexp_wrt_nexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_nexp_close_nexp_wrt_nexp :
forall e1 x1,
  fv_nexp (close_nexp_wrt_nexp x1 e1) [=] remove x1 (fv_nexp e1).
Proof.
unfold close_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve fv_nexp_close_nexp_wrt_nexp : lngen.
Hint Rewrite fv_nexp_close_nexp_wrt_nexp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_nexp_open_nexp_wrt_nexp_rec_lower_mutual :
(forall e1 e2 n1,
  fv_nexp e1 [<=] fv_nexp (open_nexp_wrt_nexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_nexp_open_nexp_wrt_nexp_rec_lower :
forall e1 e2 n1,
  fv_nexp e1 [<=] fv_nexp (open_nexp_wrt_nexp_rec n1 e2 e1).
Proof.
pose proof fv_nexp_open_nexp_wrt_nexp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_nexp_open_nexp_wrt_nexp_rec_lower : lngen.

(* end hide *)

Lemma fv_nexp_open_nexp_wrt_nexp_lower :
forall e1 e2,
  fv_nexp e1 [<=] fv_nexp (open_nexp_wrt_nexp e1 e2).
Proof.
unfold open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve fv_nexp_open_nexp_wrt_nexp_lower : lngen.

(* begin hide *)

Lemma fv_nexp_open_nexp_wrt_nexp_rec_upper_mutual :
(forall e1 e2 n1,
  fv_nexp (open_nexp_wrt_nexp_rec n1 e2 e1) [<=] fv_nexp e2 `union` fv_nexp e1).
Proof.
apply_mutual_ind nexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_nexp_open_nexp_wrt_nexp_rec_upper :
forall e1 e2 n1,
  fv_nexp (open_nexp_wrt_nexp_rec n1 e2 e1) [<=] fv_nexp e2 `union` fv_nexp e1.
Proof.
pose proof fv_nexp_open_nexp_wrt_nexp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_nexp_open_nexp_wrt_nexp_rec_upper : lngen.

(* end hide *)

Lemma fv_nexp_open_nexp_wrt_nexp_upper :
forall e1 e2,
  fv_nexp (open_nexp_wrt_nexp e1 e2) [<=] fv_nexp e2 `union` fv_nexp e1.
Proof.
unfold open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve fv_nexp_open_nexp_wrt_nexp_upper : lngen.

(* begin hide *)

Lemma fv_nexp_subst_nexp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_nexp e1 ->
  fv_nexp (subst_nexp e2 x1 e1) [=] fv_nexp e1).
Proof.
apply_mutual_ind nexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_nexp_subst_nexp_fresh :
forall e1 e2 x1,
  x1 `notin` fv_nexp e1 ->
  fv_nexp (subst_nexp e2 x1 e1) [=] fv_nexp e1.
Proof.
pose proof fv_nexp_subst_nexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_nexp_subst_nexp_fresh : lngen.
Hint Rewrite fv_nexp_subst_nexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_nexp_subst_nexp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_nexp e1) [<=] fv_nexp (subst_nexp e2 x1 e1)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_nexp_subst_nexp_lower :
forall e1 e2 x1,
  remove x1 (fv_nexp e1) [<=] fv_nexp (subst_nexp e2 x1 e1).
Proof.
pose proof fv_nexp_subst_nexp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_nexp_subst_nexp_lower : lngen.

(* begin hide *)

Lemma fv_nexp_subst_nexp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_nexp e1 ->
  x2 `notin` fv_nexp e2 ->
  x2 `notin` fv_nexp (subst_nexp e2 x1 e1)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_nexp_subst_nexp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_nexp e1 ->
  x2 `notin` fv_nexp e2 ->
  x2 `notin` fv_nexp (subst_nexp e2 x1 e1).
Proof.
pose proof fv_nexp_subst_nexp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_nexp_subst_nexp_notin : lngen.

(* begin hide *)

Lemma fv_nexp_subst_nexp_upper_mutual :
(forall e1 e2 x1,
  fv_nexp (subst_nexp e2 x1 e1) [<=] fv_nexp e2 `union` remove x1 (fv_nexp e1)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_nexp_subst_nexp_upper :
forall e1 e2 x1,
  fv_nexp (subst_nexp e2 x1 e1) [<=] fv_nexp e2 `union` remove x1 (fv_nexp e1).
Proof.
pose proof fv_nexp_subst_nexp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_nexp_subst_nexp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_nexp_close_nexp_wrt_nexp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_nexp_wrt_nexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_nexp e1 ->
  subst_nexp e1 x1 (close_nexp_wrt_nexp_rec n1 x2 e2) = close_nexp_wrt_nexp_rec n1 x2 (subst_nexp e1 x1 e2)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_nexp_close_nexp_wrt_nexp_rec :
forall e2 e1 x1 x2 n1,
  degree_nexp_wrt_nexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_nexp e1 ->
  subst_nexp e1 x1 (close_nexp_wrt_nexp_rec n1 x2 e2) = close_nexp_wrt_nexp_rec n1 x2 (subst_nexp e1 x1 e2).
Proof.
pose proof subst_nexp_close_nexp_wrt_nexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_nexp_close_nexp_wrt_nexp_rec : lngen.

Lemma subst_nexp_close_nexp_wrt_nexp :
forall e2 e1 x1 x2,
  lc_nexp e1 ->  x1 <> x2 ->
  x2 `notin` fv_nexp e1 ->
  subst_nexp e1 x1 (close_nexp_wrt_nexp x2 e2) = close_nexp_wrt_nexp x2 (subst_nexp e1 x1 e2).
Proof.
unfold close_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve subst_nexp_close_nexp_wrt_nexp : lngen.

(* begin hide *)

Lemma subst_nexp_degree_nexp_wrt_nexp_mutual :
(forall e1 e2 x1 n1,
  degree_nexp_wrt_nexp n1 e1 ->
  degree_nexp_wrt_nexp n1 e2 ->
  degree_nexp_wrt_nexp n1 (subst_nexp e2 x1 e1)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_nexp_degree_nexp_wrt_nexp :
forall e1 e2 x1 n1,
  degree_nexp_wrt_nexp n1 e1 ->
  degree_nexp_wrt_nexp n1 e2 ->
  degree_nexp_wrt_nexp n1 (subst_nexp e2 x1 e1).
Proof.
pose proof subst_nexp_degree_nexp_wrt_nexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_nexp_degree_nexp_wrt_nexp : lngen.

(* begin hide *)

Lemma subst_nexp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_nexp e2 ->
  subst_nexp e1 x1 e2 = e2).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_nexp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_nexp e2 ->
  subst_nexp e1 x1 e2 = e2.
Proof.
pose proof subst_nexp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_nexp_fresh_eq : lngen.
Hint Rewrite subst_nexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_nexp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_nexp e1 ->
  x1 `notin` fv_nexp (subst_nexp e1 x1 e2)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_nexp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_nexp e1 ->
  x1 `notin` fv_nexp (subst_nexp e1 x1 e2).
Proof.
pose proof subst_nexp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_nexp_fresh_same : lngen.

(* begin hide *)

Lemma subst_nexp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_nexp e2 ->
  x1 `notin` fv_nexp e1 ->
  x1 `notin` fv_nexp (subst_nexp e1 x2 e2)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_nexp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_nexp e2 ->
  x1 `notin` fv_nexp e1 ->
  x1 `notin` fv_nexp (subst_nexp e1 x2 e2).
Proof.
pose proof subst_nexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_nexp_fresh : lngen.

Lemma subst_nexp_lc_nexp :
forall e1 e2 x1,
  lc_nexp e1 ->
  lc_nexp e2 ->
  lc_nexp (subst_nexp e2 x1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_nexp_lc_nexp : lngen.

(* begin hide *)

Lemma subst_nexp_open_nexp_wrt_nexp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_nexp e1 ->
  subst_nexp e1 x1 (open_nexp_wrt_nexp_rec n1 e2 e3) = open_nexp_wrt_nexp_rec n1 (subst_nexp e1 x1 e2) (subst_nexp e1 x1 e3)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_nexp_open_nexp_wrt_nexp_rec :
forall e3 e1 e2 x1 n1,
  lc_nexp e1 ->
  subst_nexp e1 x1 (open_nexp_wrt_nexp_rec n1 e2 e3) = open_nexp_wrt_nexp_rec n1 (subst_nexp e1 x1 e2) (subst_nexp e1 x1 e3).
Proof.
pose proof subst_nexp_open_nexp_wrt_nexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_nexp_open_nexp_wrt_nexp_rec : lngen.

(* end hide *)

Lemma subst_nexp_open_nexp_wrt_nexp :
forall e3 e1 e2 x1,
  lc_nexp e1 ->
  subst_nexp e1 x1 (open_nexp_wrt_nexp e3 e2) = open_nexp_wrt_nexp (subst_nexp e1 x1 e3) (subst_nexp e1 x1 e2).
Proof.
unfold open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve subst_nexp_open_nexp_wrt_nexp : lngen.

Lemma subst_nexp_open_nexp_wrt_nexp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_nexp e1 ->
  open_nexp_wrt_nexp (subst_nexp e1 x1 e2) (ne_var_f x2) = subst_nexp e1 x1 (open_nexp_wrt_nexp e2 (ne_var_f x2)).
Proof.
intros; rewrite subst_nexp_open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve subst_nexp_open_nexp_wrt_nexp_var : lngen.

(* begin hide *)

Lemma subst_nexp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_nexp e2 x1 e1 = open_nexp_wrt_nexp_rec n1 e2 (close_nexp_wrt_nexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_nexp_spec_rec :
forall e1 e2 x1 n1,
  subst_nexp e2 x1 e1 = open_nexp_wrt_nexp_rec n1 e2 (close_nexp_wrt_nexp_rec n1 x1 e1).
Proof.
pose proof subst_nexp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_nexp_spec_rec : lngen.

(* end hide *)

Lemma subst_nexp_spec :
forall e1 e2 x1,
  subst_nexp e2 x1 e1 = open_nexp_wrt_nexp (close_nexp_wrt_nexp x1 e1) e2.
Proof.
unfold close_nexp_wrt_nexp; unfold open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve subst_nexp_spec : lngen.

(* begin hide *)

Lemma subst_nexp_subst_nexp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_nexp e2 ->
  x2 <> x1 ->
  subst_nexp e2 x1 (subst_nexp e3 x2 e1) = subst_nexp (subst_nexp e2 x1 e3) x2 (subst_nexp e2 x1 e1)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_nexp_subst_nexp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_nexp e2 ->
  x2 <> x1 ->
  subst_nexp e2 x1 (subst_nexp e3 x2 e1) = subst_nexp (subst_nexp e2 x1 e3) x2 (subst_nexp e2 x1 e1).
Proof.
pose proof subst_nexp_subst_nexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_nexp_subst_nexp : lngen.

(* begin hide *)

Lemma subst_nexp_close_nexp_wrt_nexp_rec_open_nexp_wrt_nexp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_nexp e2 ->
  x2 `notin` fv_nexp e1 ->
  x2 <> x1 ->
  degree_nexp_wrt_nexp n1 e1 ->
  subst_nexp e1 x1 e2 = close_nexp_wrt_nexp_rec n1 x2 (subst_nexp e1 x1 (open_nexp_wrt_nexp_rec n1 (ne_var_f x2) e2))).
Proof.
apply_mutual_ind nexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_nexp_close_nexp_wrt_nexp_rec_open_nexp_wrt_nexp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_nexp e2 ->
  x2 `notin` fv_nexp e1 ->
  x2 <> x1 ->
  degree_nexp_wrt_nexp n1 e1 ->
  subst_nexp e1 x1 e2 = close_nexp_wrt_nexp_rec n1 x2 (subst_nexp e1 x1 (open_nexp_wrt_nexp_rec n1 (ne_var_f x2) e2)).
Proof.
pose proof subst_nexp_close_nexp_wrt_nexp_rec_open_nexp_wrt_nexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_nexp_close_nexp_wrt_nexp_rec_open_nexp_wrt_nexp_rec : lngen.

(* end hide *)

Lemma subst_nexp_close_nexp_wrt_nexp_open_nexp_wrt_nexp :
forall e2 e1 x1 x2,
  x2 `notin` fv_nexp e2 ->
  x2 `notin` fv_nexp e1 ->
  x2 <> x1 ->
  lc_nexp e1 ->
  subst_nexp e1 x1 e2 = close_nexp_wrt_nexp x2 (subst_nexp e1 x1 (open_nexp_wrt_nexp e2 (ne_var_f x2))).
Proof.
unfold close_nexp_wrt_nexp; unfold open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve subst_nexp_close_nexp_wrt_nexp_open_nexp_wrt_nexp : lngen.

Lemma subst_nexp_ne_abs :
forall x2 e2 e1 x1,
  lc_nexp e1 ->
  x2 `notin` fv_nexp e1 `union` fv_nexp e2 `union` singleton x1 ->
  subst_nexp e1 x1 (ne_abs e2) = ne_abs (close_nexp_wrt_nexp x2 (subst_nexp e1 x1 (open_nexp_wrt_nexp e2 (ne_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_nexp_ne_abs : lngen.

(* begin hide *)

Lemma subst_nexp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fv_nexp e1 ->
  open_nexp_wrt_nexp_rec n1 e2 e1 = subst_nexp e2 x1 (open_nexp_wrt_nexp_rec n1 (ne_var_f x1) e1)).
Proof.
apply_mutual_ind nexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_nexp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_nexp e1 ->
  open_nexp_wrt_nexp_rec n1 e2 e1 = subst_nexp e2 x1 (open_nexp_wrt_nexp_rec n1 (ne_var_f x1) e1).
Proof.
pose proof subst_nexp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_nexp_intro_rec : lngen.
Hint Rewrite subst_nexp_intro_rec using solve [auto] : lngen.

Lemma subst_nexp_intro :
forall x1 e1 e2,
  x1 `notin` fv_nexp e1 ->
  open_nexp_wrt_nexp e1 e2 = subst_nexp e2 x1 (open_nexp_wrt_nexp e1 (ne_var_f x1)).
Proof.
unfold open_nexp_wrt_nexp; default_simp.
Qed.

Hint Resolve subst_nexp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
