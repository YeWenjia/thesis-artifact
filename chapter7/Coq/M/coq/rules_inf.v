(* !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! *)
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Equality.

Require Export Metalib.Metatheory.
Require Export Metalib.LibLNgen.

Require Export syntax_ott.

(** NOTE: Auxiliary theorems are hidden in generated documentation.
    In general, there is a [_rec] version of every lemma involving
    [open] and [close]. *)


(* *********************************************************************** *)
(** * Induction principles for nonterminals *)

Scheme Typ_ind' := Induction for dtyp Sort Prop.

Definition Typ_mutind :=
  fun H1 H2 H3 H4 H5 H6 =>
  Typ_ind' H1 H2 H3 H4 H5 H6.

Scheme Typ_rec' := Induction for dtyp Sort Set.

Definition Typ_mutrec :=
  fun H1 H2 H3 H4 H5 H6 =>
  Typ_rec' H1 H2 H3 H4 H5 H6.

Scheme dtlist_ind' := Induction for dtlist Sort Prop.

Definition dtlist_mutind :=
  fun H1 H2 =>
  dtlist_ind' H1 H2.

Scheme dtlist_rec' := Induction for dtlist Sort Set.

Definition dtlist_mutrec :=
  fun H1 H2 =>
  dtlist_rec' H1 H2.

Scheme dexp_ind' := Induction for dexp Sort Prop.

Definition dexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  dexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme dexp_rec' := Induction for dexp Sort Set.

Definition dexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  dexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.


(* *********************************************************************** *)
(** * Close *)

Fixpoint close_dexp_wrt_dexp_rec (n1 : nat) (x1 : var) (e1 : dexp) {struct e1} : dexp :=
  match e1 with
    | de_var_f x2 => if (x1 == x2) then (de_var_b n1) else (de_var_f x2)
    | de_var_b n2 => if (lt_ge_dec n2 n1) then (de_var_b n2) else (de_var_b (S n2))
    | de_top => de_top
    | de_lit i1 => de_lit i1
    | de_abs e2 => de_abs (close_dexp_wrt_dexp_rec (S n1) x1 e2)
    | de_app e2 e3 => de_app (close_dexp_wrt_dexp_rec n1 x1 e2) (close_dexp_wrt_dexp_rec n1 x1 e3)
    | de_merge e2 e3 => de_merge (close_dexp_wrt_dexp_rec n1 x1 e2) (close_dexp_wrt_dexp_rec n1 x1 e3)
    | de_anno e2 A1 => de_anno (close_dexp_wrt_dexp_rec n1 x1 e2) A1
    | de_rcd l e => de_rcd l (close_dexp_wrt_dexp_rec n1 x1 e)
    | de_proj e l => de_proj (close_dexp_wrt_dexp_rec n1 x1 e) l
    | de_fixpoint e2 => de_fixpoint (close_dexp_wrt_dexp_rec (S n1) x1 e2)
  end.

Definition close_dexp_wrt_dexp x1 e1 := close_dexp_wrt_dexp_rec 0 x1 e1.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_dtyp (A1 : dtyp) {struct A1} : nat :=
  match A1 with
    | dt_int => 1
    | dt_top => 1
    | dt_bot => 1
    | dt_arrow A2 B1 => 1 + (size_dtyp A2) + (size_dtyp B1)
    | dt_and A2 B1 => 1 + (size_dtyp A2) + (size_dtyp B1)
    | dt_rcd l A => 1 + (size_dtyp A) 
  end.

Fixpoint size_dtlist (AA1 : dtlist) {struct AA1} : nat :=
  match AA1 with
    | ddt_empty => 1
    | ddt_consl AA2 A1 => 1 + (size_dtlist AA2) + (size_dtyp A1)
  end.

Fixpoint size_dexp (e1 : dexp) {struct e1} : nat :=
  match e1 with
    | de_var_f x1 => 1
    | de_var_b n1 => 1
    | de_top => 1
    | de_lit i1 => 1
    | de_abs e2 => 1  + (size_dexp e2) 
    | de_app e2 e3 => 1 + (size_dexp e2) + (size_dexp e3)
    | de_merge e2 e3 => 1 + (size_dexp e2) + (size_dexp e3)
    | de_anno e2 A1 => 1 + (size_dexp e2) + (size_dtyp A1)
    | de_rcd l e => 1 + (size_dexp e)
    | de_proj e l => 1 + (size_dexp e)
    | de_fixpoint e => 1 + (size_dexp e) 
  end.


(* *********************************************************************** *)
(** * Degree *)

(** These define only an upper bound, not a strict upper bound. *)

Inductive degree_dexp_wrt_dexp : nat -> dexp -> Prop :=
  | degree_wrt_dexp_de_var_f : forall n1 x1,
    degree_dexp_wrt_dexp n1 (de_var_f x1)
  | degree_wrt_dexp_de_var_b : forall n1 n2,
    lt n2 n1 ->
    degree_dexp_wrt_dexp n1 (de_var_b n2)
  | degree_wrt_dexp_de_top : forall n1,
    degree_dexp_wrt_dexp n1 (de_top)
  | degree_wrt_dexp_de_lit : forall n1 i1,
    degree_dexp_wrt_dexp n1 (de_lit i1)
  | degree_wrt_dexp_de_abs : forall n1 e1,
    degree_dexp_wrt_dexp (S n1) e1 ->
    degree_dexp_wrt_dexp n1 (de_abs e1)
  | degree_wrt_dexp_de_app : forall n1 e1 e2,
    degree_dexp_wrt_dexp n1 e1 ->
    degree_dexp_wrt_dexp n1 e2 ->
    degree_dexp_wrt_dexp n1 (de_app e1 e2)
  | degree_wrt_dexp_de_merge : forall n1 e1 e2,
    degree_dexp_wrt_dexp n1 e1 ->
    degree_dexp_wrt_dexp n1 e2 ->
    degree_dexp_wrt_dexp n1 (de_merge e1 e2)
  | degree_wrt_dexp_de_anno : forall n1 e1 A1,
    degree_dexp_wrt_dexp n1 e1 ->
    degree_dexp_wrt_dexp n1 (de_anno e1 A1)
  | degree_wrt_dexp_de_rcd : forall n1 e1 l,
    degree_dexp_wrt_dexp n1 e1 ->
    degree_dexp_wrt_dexp n1 (de_rcd l e1)
  | degree_wrt_dexp_de_proj : forall n1 e1 l,
    degree_dexp_wrt_dexp n1 e1 ->
    degree_dexp_wrt_dexp n1 (de_proj e1 l)
  | degree_wrt_dexp_de_fix : forall n1 e1,
    degree_dexp_wrt_dexp (S n1) e1 ->
    degree_dexp_wrt_dexp n1 (de_fixpoint e1).

Scheme degree_dexp_wrt_dexp_ind' := Induction for degree_dexp_wrt_dexp Sort Prop.

Definition degree_dexp_wrt_dexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  degree_dexp_wrt_dexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Hint Constructors degree_dexp_wrt_dexp : core lngen.


(* *********************************************************************** *)
(** * Local closure (version in [Set], induction principles) *)

Inductive lc_set_dexp : dexp -> Set :=
  | lc_set_de_var_f : forall x1,
    lc_set_dexp (de_var_f x1)
  | lc_set_de_top :
    lc_set_dexp (de_top)
  | lc_set_de_lit : forall i1,
    lc_set_dexp (de_lit i1)
  | lc_set_de_abs : forall e1,
    (forall x1 : var, lc_set_dexp (open_dexp_wrt_dexp e1 (de_var_f x1))) ->
    lc_set_dexp (de_abs e1)
  | lc_set_de_app : forall e1 e2,
    lc_set_dexp e1 ->
    lc_set_dexp e2 ->
    lc_set_dexp (de_app e1 e2)
  | lc_set_de_merge : forall e1 e2,
    lc_set_dexp e1 ->
    lc_set_dexp e2 ->
    lc_set_dexp (de_merge e1 e2)
  | lc_set_de_anno : forall e1 A1,
    lc_set_dexp e1 ->
    lc_set_dexp (de_anno e1 A1)
  | lc_set_de_rcd : forall e1 l,
    lc_set_dexp e1 ->
    lc_set_dexp (de_rcd l e1)
  | lc_set_de_proj : forall e1 l,
    lc_set_dexp e1 ->
    lc_set_dexp (de_proj e1 l)
  | lc_set_de_fix : forall e1,
    (forall x1 : var, lc_set_dexp (open_dexp_wrt_dexp e1 (de_var_f x1))) ->
    lc_set_dexp (de_fixpoint e1).

Scheme lc_dexp_ind' := Induction for lc_dexp Sort Prop.

Definition lc_dexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_dexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme lc_set_dexp_ind' := Induction for lc_set_dexp Sort Prop.

Definition lc_set_dexp_mutind :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_set_dexp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Scheme lc_set_dexp_rec' := Induction for lc_set_dexp Sort Set.

Definition lc_set_dexp_mutrec :=
  fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 =>
  lc_set_dexp_rec' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.

Hint Constructors lc_dexp : core lngen.

Hint Constructors lc_set_dexp : core lngen.


(* *********************************************************************** *)
(** * Body *)

Definition body_dexp_wrt_dexp e1 := forall x1, lc_dexp (open_dexp_wrt_dexp e1 (de_var_f x1)).

Hint Unfold body_dexp_wrt_dexp : core.


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

Lemma size_Typ_min_mutual :
(forall A1, 1 <= size_dtyp A1).
Proof.
apply_mutual_ind Typ_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_Typ_min :
forall A1, 1 <= size_dtyp A1.
Proof.
pose proof size_Typ_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_Typ_min : lngen.

(* begin hide *)

Lemma size_dtlist_min_mutual :
(forall AA1, 1 <= size_dtlist AA1).
Proof.
apply_mutual_ind dtlist_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_dtlist_min :
forall AA1, 1 <= size_dtlist AA1.
Proof.
pose proof size_dtlist_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dtlist_min : lngen.

(* begin hide *)

Lemma size_dexp_min_mutual :
(forall e1, 1 <= size_dexp e1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma size_dexp_min :
forall e1, 1 <= size_dexp e1.
Proof.
pose proof size_dexp_min_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dexp_min : lngen.

(* begin hide *)

Lemma size_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall e1 x1 n1,
  size_dexp (close_dexp_wrt_dexp_rec n1 x1 e1) = size_dexp e1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dexp_close_dexp_wrt_dexp_rec :
forall e1 x1 n1,
  size_dexp (close_dexp_wrt_dexp_rec n1 x1 e1) = size_dexp e1.
Proof.
pose proof size_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dexp_close_dexp_wrt_dexp_rec : lngen.
Hint Rewrite size_dexp_close_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma size_dexp_close_dexp_wrt_dexp :
forall e1 x1,
  size_dexp (close_dexp_wrt_dexp x1 e1) = size_dexp e1.
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve size_dexp_close_dexp_wrt_dexp : lngen.
Hint Rewrite size_dexp_close_dexp_wrt_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma size_dexp_open_dexp_wrt_dexp_rec_mutual :
(forall e1 e2 n1,
  size_dexp e1 <= size_dexp (open_dexp_wrt_dexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dexp_open_dexp_wrt_dexp_rec :
forall e1 e2 n1,
  size_dexp e1 <= size_dexp (open_dexp_wrt_dexp_rec n1 e2 e1).
Proof.
pose proof size_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dexp_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma size_dexp_open_dexp_wrt_dexp :
forall e1 e2,
  size_dexp e1 <= size_dexp (open_dexp_wrt_dexp e1 e2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve size_dexp_open_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma size_dexp_open_dexp_wrt_dexp_rec_var_mutual :
(forall e1 x1 n1,
  size_dexp (open_dexp_wrt_dexp_rec n1 (de_var_f x1) e1) = size_dexp e1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma size_dexp_open_dexp_wrt_dexp_rec_var :
forall e1 x1 n1,
  size_dexp (open_dexp_wrt_dexp_rec n1 (de_var_f x1) e1) = size_dexp e1.
Proof.
pose proof size_dexp_open_dexp_wrt_dexp_rec_var_mutual as H; intuition eauto.
Qed.

Hint Resolve size_dexp_open_dexp_wrt_dexp_rec_var : lngen.
Hint Rewrite size_dexp_open_dexp_wrt_dexp_rec_var using solve [auto] : lngen.

(* end hide *)

Lemma size_dexp_open_dexp_wrt_dexp_var :
forall e1 x1,
  size_dexp (open_dexp_wrt_dexp e1 (de_var_f x1)) = size_dexp e1.
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve size_dexp_open_dexp_wrt_dexp_var : lngen.
Hint Rewrite size_dexp_open_dexp_wrt_dexp_var using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [degree] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma degree_dexp_wrt_dexp_S_mutual :
(forall n1 e1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp (S n1) e1).
Proof.
apply_mutual_ind degree_dexp_wrt_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma degree_dexp_wrt_dexp_S :
forall n1 e1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp (S n1) e1.
Proof.
pose proof degree_dexp_wrt_dexp_S_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dexp_wrt_dexp_S : lngen.

Lemma degree_dexp_wrt_dexp_O :
forall n1 e1,
  degree_dexp_wrt_dexp O e1 ->
  degree_dexp_wrt_dexp n1 e1.
Proof.
induction n1; default_simp.
Qed.

Hint Resolve degree_dexp_wrt_dexp_O : lngen.

(* begin hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall e1 x1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp (S n1) (close_dexp_wrt_dexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec :
forall e1 x1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp (S n1) (close_dexp_wrt_dexp_rec n1 x1 e1).
Proof.
pose proof degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp :
forall e1 x1,
  degree_dexp_wrt_dexp 0 e1 ->
  degree_dexp_wrt_dexp 1 (close_dexp_wrt_dexp x1 e1).
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve degree_dexp_wrt_dexp_close_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv_mutual :
(forall e1 x1 n1,
  degree_dexp_wrt_dexp (S n1) (close_dexp_wrt_dexp_rec n1 x1 e1) ->
  degree_dexp_wrt_dexp n1 e1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv :
forall e1 x1 n1,
  degree_dexp_wrt_dexp (S n1) (close_dexp_wrt_dexp_rec n1 x1 e1) ->
  degree_dexp_wrt_dexp n1 e1.
Proof.
pose proof degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_dexp_wrt_dexp_close_dexp_wrt_dexp_rec_inv : lngen.

(* end hide *)

Lemma degree_dexp_wrt_dexp_close_dexp_wrt_dexp_inv :
forall e1 x1,
  degree_dexp_wrt_dexp 1 (close_dexp_wrt_dexp x1 e1) ->
  degree_dexp_wrt_dexp 0 e1.
Proof.
unfold close_dexp_wrt_dexp; eauto with lngen.
Qed.

Hint Immediate degree_dexp_wrt_dexp_close_dexp_wrt_dexp_inv : lngen.

(* begin hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_mutual :
(forall e1 e2 n1,
  degree_dexp_wrt_dexp (S n1) e1 ->
  degree_dexp_wrt_dexp n1 e2 ->
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec :
forall e1 e2 n1,
  degree_dexp_wrt_dexp (S n1) e1 ->
  degree_dexp_wrt_dexp n1 e2 ->
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dexp_rec n1 e2 e1).
Proof.
pose proof degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp :
forall e1 e2,
  degree_dexp_wrt_dexp 1 e1 ->
  degree_dexp_wrt_dexp 0 e2 ->
  degree_dexp_wrt_dexp 0 (open_dexp_wrt_dexp e1 e2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve degree_dexp_wrt_dexp_open_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv_mutual :
(forall e1 e2 n1,
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dexp_rec n1 e2 e1) ->
  degree_dexp_wrt_dexp (S n1) e1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv :
forall e1 e2 n1,
  degree_dexp_wrt_dexp n1 (open_dexp_wrt_dexp_rec n1 e2 e1) ->
  degree_dexp_wrt_dexp (S n1) e1.
Proof.
pose proof degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv_mutual as H; intuition eauto.
Qed.

Hint Immediate degree_dexp_wrt_dexp_open_dexp_wrt_dexp_rec_inv : lngen.

(* end hide *)

Lemma degree_dexp_wrt_dexp_open_dexp_wrt_dexp_inv :
forall e1 e2,
  degree_dexp_wrt_dexp 0 (open_dexp_wrt_dexp e1 e2) ->
  degree_dexp_wrt_dexp 1 e1.
Proof.
unfold open_dexp_wrt_dexp; eauto with lngen.
Qed.

Hint Immediate degree_dexp_wrt_dexp_open_dexp_wrt_dexp_inv : lngen.


(* *********************************************************************** *)
(** * Theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_inj_mutual :
(forall e1 e2 x1 n1,
  close_dexp_wrt_dexp_rec n1 x1 e1 = close_dexp_wrt_dexp_rec n1 x1 e2 ->
  e1 = e2).
Proof.
apply_mutual_ind dexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_inj :
forall e1 e2 x1 n1,
  close_dexp_wrt_dexp_rec n1 x1 e1 = close_dexp_wrt_dexp_rec n1 x1 e2 ->
  e1 = e2.
Proof.
pose proof close_dexp_wrt_dexp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate close_dexp_wrt_dexp_rec_inj : lngen.

(* end hide *)

Lemma close_dexp_wrt_dexp_inj :
forall e1 e2 x1,
  close_dexp_wrt_dexp x1 e1 = close_dexp_wrt_dexp x1 e2 ->
  e1 = e2.
Proof.
unfold close_dexp_wrt_dexp; eauto with lngen.
Qed.

Hint Immediate close_dexp_wrt_dexp_inj : lngen.

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual :
(forall e1 x1 n1,
  x1 `notin` fv_dexp e1 ->
  close_dexp_wrt_dexp_rec n1 x1 (open_dexp_wrt_dexp_rec n1 (de_var_f x1) e1) = e1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec :
forall e1 x1 n1,
  x1 `notin` fv_dexp e1 ->
  close_dexp_wrt_dexp_rec n1 x1 (open_dexp_wrt_dexp_rec n1 (de_var_f x1) e1) = e1.
Proof.
pose proof close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec : lngen.
Hint Rewrite close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma close_dexp_wrt_dexp_open_dexp_wrt_dexp :
forall e1 x1,
  x1 `notin` fv_dexp e1 ->
  close_dexp_wrt_dexp x1 (open_dexp_wrt_dexp e1 (de_var_f x1)) = e1.
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve close_dexp_wrt_dexp_open_dexp_wrt_dexp : lngen.
Hint Rewrite close_dexp_wrt_dexp_open_dexp_wrt_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec_mutual :
(forall e1 x1 n1,
  open_dexp_wrt_dexp_rec n1 (de_var_f x1) (close_dexp_wrt_dexp_rec n1 x1 e1) = e1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec :
forall e1 x1 n1,
  open_dexp_wrt_dexp_rec n1 (de_var_f x1) (close_dexp_wrt_dexp_rec n1 x1 e1) = e1.
Proof.
pose proof open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec : lngen.
Hint Rewrite open_dexp_wrt_dexp_rec_close_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma open_dexp_wrt_dexp_close_dexp_wrt_dexp :
forall e1 x1,
  open_dexp_wrt_dexp (close_dexp_wrt_dexp x1 e1) (de_var_f x1) = e1.
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve open_dexp_wrt_dexp_close_dexp_wrt_dexp : lngen.
Hint Rewrite open_dexp_wrt_dexp_close_dexp_wrt_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_inj_mutual :
(forall e2 e1 x1 n1,
  x1 `notin` fv_dexp e2 ->
  x1 `notin` fv_dexp e1 ->
  open_dexp_wrt_dexp_rec n1 (de_var_f x1) e2 = open_dexp_wrt_dexp_rec n1 (de_var_f x1) e1 ->
  e2 = e1).
Proof.
apply_mutual_ind dexp_mutind;
intros; match goal with
          | |- _ = ?term => destruct term
        end;
default_simp; eauto with lngen.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_inj :
forall e2 e1 x1 n1,
  x1 `notin` fv_dexp e2 ->
  x1 `notin` fv_dexp e1 ->
  open_dexp_wrt_dexp_rec n1 (de_var_f x1) e2 = open_dexp_wrt_dexp_rec n1 (de_var_f x1) e1 ->
  e2 = e1.
Proof.
pose proof open_dexp_wrt_dexp_rec_inj_mutual as H; intuition eauto.
Qed.

Hint Immediate open_dexp_wrt_dexp_rec_inj : lngen.

(* end hide *)

Lemma open_dexp_wrt_dexp_inj :
forall e2 e1 x1,
  x1 `notin` fv_dexp e2 ->
  x1 `notin` fv_dexp e1 ->
  open_dexp_wrt_dexp e2 (de_var_f x1) = open_dexp_wrt_dexp e1 (de_var_f x1) ->
  e2 = e1.
Proof.
unfold open_dexp_wrt_dexp; eauto with lngen.
Qed.

Hint Immediate open_dexp_wrt_dexp_inj : lngen.


(* *********************************************************************** *)
(** * Theorems about [lc] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma degree_dexp_wrt_dexp_of_lc_dexp_mutual :
(forall e1,
  lc_dexp e1 ->
  degree_dexp_wrt_dexp 0 e1).
Proof.
apply_mutual_ind lc_dexp_mutind;
intros;
let x1 := fresh "x1" in pick_fresh x1;
repeat (match goal with
          | H1 : _, H2 : _ |- _ => specialize H1 with H2
        end);
default_simp; eauto with lngen.
Qed.

(* end hide *)

Lemma degree_dexp_wrt_dexp_of_lc_dexp :
forall e1,
  lc_dexp e1 ->
  degree_dexp_wrt_dexp 0 e1.
Proof.
pose proof degree_dexp_wrt_dexp_of_lc_dexp_mutual as H; intuition eauto.
Qed.

Hint Resolve degree_dexp_wrt_dexp_of_lc_dexp : lngen.

(* begin hide *)

Lemma lc_dexp_of_degree_size_mutual :
forall i1,
(forall e1,
  size_dexp e1 = i1 ->
  degree_dexp_wrt_dexp 0 e1 ->
  lc_dexp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dexp_mutind;
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

Lemma lc_dexp_of_degree :
forall e1,
  degree_dexp_wrt_dexp 0 e1 ->
  lc_dexp e1.
Proof.
intros e1; intros;
pose proof (lc_dexp_of_degree_size_mutual (size_dexp e1));
intuition eauto.
Qed.

Hint Resolve lc_dexp_of_degree : lngen.

Ltac Typ_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac dtlist_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              fail 1
          end).

Ltac dexp_lc_exists_tac :=
  repeat (match goal with
            | H : _ |- _ =>
              let J1 := fresh in pose proof H as J1; apply degree_dexp_wrt_dexp_of_lc_dexp in J1; clear H
          end).

Lemma lc_de_abs_exists :
forall x1 e1,
  lc_dexp (open_dexp_wrt_dexp e1 (de_var_f x1)) ->
  lc_dexp (de_abs e1).
Proof.
intros; dexp_lc_exists_tac; eauto with lngen.
Qed.

Lemma lc_de_fix_exists :
forall x1 e1,
  lc_dexp (open_dexp_wrt_dexp e1 (de_var_f x1)) ->
  lc_dexp (de_fixpoint e1).
Proof.
intros; dexp_lc_exists_tac; eauto with lngen.
Qed.


Hint Extern 1 (lc_dexp (de_abs _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_de_abs_exists x1) : core.

Hint Extern 1 (lc_dexp (de_fixpoint _)) =>
  let x1 := fresh in
  pick_fresh x1;
  apply (lc_de_fix_exists x1) : core.

Lemma lc_body_dexp_wrt_dexp :
forall e1 e2,
  body_dexp_wrt_dexp e1 ->
  lc_dexp e2 ->
  lc_dexp (open_dexp_wrt_dexp e1 e2).
Proof.
unfold body_dexp_wrt_dexp;
default_simp;
let x1 := fresh "x" in
pick_fresh x1;
specialize_all x1;
dexp_lc_exists_tac;
eauto with lngen.
Qed.

Hint Resolve lc_body_dexp_wrt_dexp : lngen.

Lemma lc_body_de_abs_2 :
forall e1,
  lc_dexp (de_abs e1) ->
  body_dexp_wrt_dexp e1.
Proof.
default_simp.
Qed.

Lemma lc_body_de_fix_2 :
forall e1,
  lc_dexp (de_fixpoint e1) ->
  body_dexp_wrt_dexp e1.
Proof.
default_simp.
Qed.

Hint Resolve lc_body_de_abs_2 lc_body_de_fix_2: lngen.

(* begin hide *)

Lemma lc_dexp_unique_mutual :
(forall e1 (proof2 proof3 : lc_dexp e1), proof2 = proof3).
Proof.
apply_mutual_ind lc_dexp_mutind;
intros;
let proof1 := fresh "proof1" in
rename_last_into proof1; dependent destruction proof1;
f_equal; default_simp; auto using @functional_extensionality_dep with lngen.
Qed.

(* end hide *)

Lemma lc_dexp_unique :
forall e1 (proof2 proof3 : lc_dexp e1), proof2 = proof3.
Proof.
pose proof lc_dexp_unique_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_dexp_unique : lngen.

(* begin hide *)

Lemma lc_dexp_of_lc_set_dexp_mutual :
(forall e1, lc_set_dexp e1 -> lc_dexp e1).
Proof.
apply_mutual_ind lc_set_dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma lc_dexp_of_lc_set_dexp :
forall e1, lc_set_dexp e1 -> lc_dexp e1.
Proof.
pose proof lc_dexp_of_lc_set_dexp_mutual as H; intuition eauto.
Qed.

Hint Resolve lc_dexp_of_lc_set_dexp : lngen.

(* begin hide *)

Lemma lc_set_dexp_of_lc_dexp_size_mutual :
forall i1,
(forall e1,
  size_dexp e1 = i1 ->
  lc_dexp e1 ->
  lc_set_dexp e1).
Proof.
intros i1; pattern i1; apply lt_wf_rec;
clear i1; intros i1 H1;
apply_mutual_ind dexp_mutrec;
default_simp;
try solve [assert False by default_simp; tauto];
(* non-trivial cases *)
constructor; default_simp;
try first [apply lc_set_Typ_of_lc_dtyp
 | apply lc_set_dexp_of_lc_dexp];
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

Lemma lc_set_dexp_of_lc_dexp :
forall e1,
  lc_dexp e1 ->
  lc_set_dexp e1.
Proof.
intros e1; intros;
pose proof (lc_set_dexp_of_lc_dexp_size_mutual (size_dexp e1));
intuition eauto.
Qed.

Hint Resolve lc_set_dexp_of_lc_dexp : lngen.


(* *********************************************************************** *)
(** * More theorems about [open] and [close] *)

Ltac default_auto ::= auto with lngen; tauto.
Ltac default_autorewrite ::= fail.

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual :
(forall e1 x1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  x1 `notin` fv_dexp e1 ->
  close_dexp_wrt_dexp_rec n1 x1 e1 = e1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp :
forall e1 x1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  x1 `notin` fv_dexp e1 ->
  close_dexp_wrt_dexp_rec n1 x1 e1 = e1.
Proof.
pose proof close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

Hint Resolve close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp : lngen.
Hint Rewrite close_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp using solve [auto] : lngen.

(* end hide *)

Lemma close_dexp_wrt_dexp_lc_dexp :
forall e1 x1,
  lc_dexp e1 ->
  x1 `notin` fv_dexp e1 ->
  close_dexp_wrt_dexp x1 e1 = e1.
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve close_dexp_wrt_dexp_lc_dexp : lngen.
Hint Rewrite close_dexp_wrt_dexp_lc_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual :
(forall e2 e1 n1,
  degree_dexp_wrt_dexp n1 e2 ->
  open_dexp_wrt_dexp_rec n1 e1 e2 = e2).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp :
forall e2 e1 n1,
  degree_dexp_wrt_dexp n1 e2 ->
  open_dexp_wrt_dexp_rec n1 e1 e2 = e2.
Proof.
pose proof open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

Hint Resolve open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp : lngen.
Hint Rewrite open_dexp_wrt_dexp_rec_degree_dexp_wrt_dexp using solve [auto] : lngen.

(* end hide *)

Lemma open_dexp_wrt_dexp_lc_dexp :
forall e2 e1,
  lc_dexp e2 ->
  open_dexp_wrt_dexp e2 e1 = e2.
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve open_dexp_wrt_dexp_lc_dexp : lngen.
Hint Rewrite open_dexp_wrt_dexp_lc_dexp using solve [auto] : lngen.


(* *********************************************************************** *)
(** * Theorems about [fv] *)

Ltac default_auto ::= auto with set lngen; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma fv_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall e1 x1 n1,
  fv_dexp (close_dexp_wrt_dexp_rec n1 x1 e1) [=] remove x1 (fv_dexp e1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_dexp_close_dexp_wrt_dexp_rec :
forall e1 x1 n1,
  fv_dexp (close_dexp_wrt_dexp_rec n1 x1 e1) [=] remove x1 (fv_dexp e1).
Proof.
pose proof fv_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_close_dexp_wrt_dexp_rec : lngen.
Hint Rewrite fv_dexp_close_dexp_wrt_dexp_rec using solve [auto] : lngen.

(* end hide *)

Lemma fv_dexp_close_dexp_wrt_dexp :
forall e1 x1,
  fv_dexp (close_dexp_wrt_dexp x1 e1) [=] remove x1 (fv_dexp e1).
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve fv_dexp_close_dexp_wrt_dexp : lngen.
Hint Rewrite fv_dexp_close_dexp_wrt_dexp using solve [auto] : lngen.

(* begin hide *)

Lemma fv_dexp_open_dexp_wrt_dexp_rec_lower_mutual :
(forall e1 e2 n1,
  fv_dexp e1 [<=] fv_dexp (open_dexp_wrt_dexp_rec n1 e2 e1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_dexp_open_dexp_wrt_dexp_rec_lower :
forall e1 e2 n1,
  fv_dexp e1 [<=] fv_dexp (open_dexp_wrt_dexp_rec n1 e2 e1).
Proof.
pose proof fv_dexp_open_dexp_wrt_dexp_rec_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_open_dexp_wrt_dexp_rec_lower : lngen.

(* end hide *)

Lemma fv_dexp_open_dexp_wrt_dexp_lower :
forall e1 e2,
  fv_dexp e1 [<=] fv_dexp (open_dexp_wrt_dexp e1 e2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve fv_dexp_open_dexp_wrt_dexp_lower : lngen.

(* begin hide *)

Lemma fv_dexp_open_dexp_wrt_dexp_rec_upper_mutual :
(forall e1 e2 n1,
  fv_dexp (open_dexp_wrt_dexp_rec n1 e2 e1) [<=] fv_dexp e2 `union` fv_dexp e1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

(* begin hide *)

Lemma fv_dexp_open_dexp_wrt_dexp_rec_upper :
forall e1 e2 n1,
  fv_dexp (open_dexp_wrt_dexp_rec n1 e2 e1) [<=] fv_dexp e2 `union` fv_dexp e1.
Proof.
pose proof fv_dexp_open_dexp_wrt_dexp_rec_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_open_dexp_wrt_dexp_rec_upper : lngen.

(* end hide *)

Lemma fv_dexp_open_dexp_wrt_dexp_upper :
forall e1 e2,
  fv_dexp (open_dexp_wrt_dexp e1 e2) [<=] fv_dexp e2 `union` fv_dexp e1.
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve fv_dexp_open_dexp_wrt_dexp_upper : lngen.

(* begin hide *)

Lemma fv_dexp_subst_dexp_fresh_mutual :
(forall e1 e2 x1,
  x1 `notin` fv_dexp e1 ->
  fv_dexp (subst_dexp e2 x1 e1) [=] fv_dexp e1).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_dexp_subst_dexp_fresh :
forall e1 e2 x1,
  x1 `notin` fv_dexp e1 ->
  fv_dexp (subst_dexp e2 x1 e1) [=] fv_dexp e1.
Proof.
pose proof fv_dexp_subst_dexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_subst_dexp_fresh : lngen.
Hint Rewrite fv_dexp_subst_dexp_fresh using solve [auto] : lngen.

(* begin hide *)

Lemma fv_dexp_subst_dexp_lower_mutual :
(forall e1 e2 x1,
  remove x1 (fv_dexp e1) [<=] fv_dexp (subst_dexp e2 x1 e1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_dexp_subst_dexp_lower :
forall e1 e2 x1,
  remove x1 (fv_dexp e1) [<=] fv_dexp (subst_dexp e2 x1 e1).
Proof.
pose proof fv_dexp_subst_dexp_lower_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_subst_dexp_lower : lngen.

(* begin hide *)

Lemma fv_dexp_subst_dexp_notin_mutual :
(forall e1 e2 x1 x2,
  x2 `notin` fv_dexp e1 ->
  x2 `notin` fv_dexp e2 ->
  x2 `notin` fv_dexp (subst_dexp e2 x1 e1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_dexp_subst_dexp_notin :
forall e1 e2 x1 x2,
  x2 `notin` fv_dexp e1 ->
  x2 `notin` fv_dexp e2 ->
  x2 `notin` fv_dexp (subst_dexp e2 x1 e1).
Proof.
pose proof fv_dexp_subst_dexp_notin_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_subst_dexp_notin : lngen.

(* begin hide *)

Lemma fv_dexp_subst_dexp_upper_mutual :
(forall e1 e2 x1,
  fv_dexp (subst_dexp e2 x1 e1) [<=] fv_dexp e2 `union` remove x1 (fv_dexp e1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp; fsetdec.
Qed.

(* end hide *)

Lemma fv_dexp_subst_dexp_upper :
forall e1 e2 x1,
  fv_dexp (subst_dexp e2 x1 e1) [<=] fv_dexp e2 `union` remove x1 (fv_dexp e1).
Proof.
pose proof fv_dexp_subst_dexp_upper_mutual as H; intuition eauto.
Qed.

Hint Resolve fv_dexp_subst_dexp_upper : lngen.


(* *********************************************************************** *)
(** * Theorems about [subst] *)

Ltac default_auto ::= auto with lngen brute_force; tauto.
Ltac default_autorewrite ::= autorewrite with lngen.

(* begin hide *)

Lemma subst_dexp_close_dexp_wrt_dexp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_dexp e1 ->
  subst_dexp e1 x1 (close_dexp_wrt_dexp_rec n1 x2 e2) = close_dexp_wrt_dexp_rec n1 x2 (subst_dexp e1 x1 e2)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_close_dexp_wrt_dexp_rec :
forall e2 e1 x1 x2 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  x1 <> x2 ->
  x2 `notin` fv_dexp e1 ->
  subst_dexp e1 x1 (close_dexp_wrt_dexp_rec n1 x2 e2) = close_dexp_wrt_dexp_rec n1 x2 (subst_dexp e1 x1 e2).
Proof.
pose proof subst_dexp_close_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_close_dexp_wrt_dexp_rec : lngen.

Lemma subst_dexp_close_dexp_wrt_dexp :
forall e2 e1 x1 x2,
  lc_dexp e1 ->  x1 <> x2 ->
  x2 `notin` fv_dexp e1 ->
  subst_dexp e1 x1 (close_dexp_wrt_dexp x2 e2) = close_dexp_wrt_dexp x2 (subst_dexp e1 x1 e2).
Proof.
unfold close_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve subst_dexp_close_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma subst_dexp_degree_dexp_wrt_dexp_mutual :
(forall e1 e2 x1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp n1 e2 ->
  degree_dexp_wrt_dexp n1 (subst_dexp e2 x1 e1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_degree_dexp_wrt_dexp :
forall e1 e2 x1 n1,
  degree_dexp_wrt_dexp n1 e1 ->
  degree_dexp_wrt_dexp n1 e2 ->
  degree_dexp_wrt_dexp n1 (subst_dexp e2 x1 e1).
Proof.
pose proof subst_dexp_degree_dexp_wrt_dexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_degree_dexp_wrt_dexp : lngen.

(* begin hide *)

Lemma subst_dexp_fresh_eq_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_dexp e2 ->
  subst_dexp e1 x1 e2 = e2).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_fresh_eq :
forall e2 e1 x1,
  x1 `notin` fv_dexp e2 ->
  subst_dexp e1 x1 e2 = e2.
Proof.
pose proof subst_dexp_fresh_eq_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_fresh_eq : lngen.
Hint Rewrite subst_dexp_fresh_eq using solve [auto] : lngen.

(* begin hide *)

Lemma subst_dexp_fresh_same_mutual :
(forall e2 e1 x1,
  x1 `notin` fv_dexp e1 ->
  x1 `notin` fv_dexp (subst_dexp e1 x1 e2)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_fresh_same :
forall e2 e1 x1,
  x1 `notin` fv_dexp e1 ->
  x1 `notin` fv_dexp (subst_dexp e1 x1 e2).
Proof.
pose proof subst_dexp_fresh_same_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_fresh_same : lngen.

(* begin hide *)

Lemma subst_dexp_fresh_mutual :
(forall e2 e1 x1 x2,
  x1 `notin` fv_dexp e2 ->
  x1 `notin` fv_dexp e1 ->
  x1 `notin` fv_dexp (subst_dexp e1 x2 e2)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_fresh :
forall e2 e1 x1 x2,
  x1 `notin` fv_dexp e2 ->
  x1 `notin` fv_dexp e1 ->
  x1 `notin` fv_dexp (subst_dexp e1 x2 e2).
Proof.
pose proof subst_dexp_fresh_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_fresh : lngen.

Lemma subst_dexp_lc_dexp :
forall e1 e2 x1,
  lc_dexp e1 ->
  lc_dexp e2 ->
  lc_dexp (subst_dexp e2 x1 e1).
Proof.
default_simp.
Qed.

Hint Resolve subst_dexp_lc_dexp : lngen.

(* begin hide *)

Lemma subst_dexp_open_dexp_wrt_dexp_rec_mutual :
(forall e3 e1 e2 x1 n1,
  lc_dexp e1 ->
  subst_dexp e1 x1 (open_dexp_wrt_dexp_rec n1 e2 e3) = open_dexp_wrt_dexp_rec n1 (subst_dexp e1 x1 e2) (subst_dexp e1 x1 e3)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dexp_open_dexp_wrt_dexp_rec :
forall e3 e1 e2 x1 n1,
  lc_dexp e1 ->
  subst_dexp e1 x1 (open_dexp_wrt_dexp_rec n1 e2 e3) = open_dexp_wrt_dexp_rec n1 (subst_dexp e1 x1 e2) (subst_dexp e1 x1 e3).
Proof.
pose proof subst_dexp_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma subst_dexp_open_dexp_wrt_dexp :
forall e3 e1 e2 x1,
  lc_dexp e1 ->
  subst_dexp e1 x1 (open_dexp_wrt_dexp e3 e2) = open_dexp_wrt_dexp (subst_dexp e1 x1 e3) (subst_dexp e1 x1 e2).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve subst_dexp_open_dexp_wrt_dexp : lngen.

Lemma subst_dexp_open_dexp_wrt_dexp_var :
forall e2 e1 x1 x2,
  x1 <> x2 ->
  lc_dexp e1 ->
  open_dexp_wrt_dexp (subst_dexp e1 x1 e2) (de_var_f x2) = subst_dexp e1 x1 (open_dexp_wrt_dexp e2 (de_var_f x2)).
Proof.
intros; rewrite subst_dexp_open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve subst_dexp_open_dexp_wrt_dexp_var : lngen.

(* begin hide *)

Lemma subst_dexp_spec_rec_mutual :
(forall e1 e2 x1 n1,
  subst_dexp e2 x1 e1 = open_dexp_wrt_dexp_rec n1 e2 (close_dexp_wrt_dexp_rec n1 x1 e1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dexp_spec_rec :
forall e1 e2 x1 n1,
  subst_dexp e2 x1 e1 = open_dexp_wrt_dexp_rec n1 e2 (close_dexp_wrt_dexp_rec n1 x1 e1).
Proof.
pose proof subst_dexp_spec_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_spec_rec : lngen.

(* end hide *)

Lemma subst_dexp_spec :
forall e1 e2 x1,
  subst_dexp e2 x1 e1 = open_dexp_wrt_dexp (close_dexp_wrt_dexp x1 e1) e2.
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve subst_dexp_spec : lngen.

(* begin hide *)

Lemma subst_dexp_subst_dexp_mutual :
(forall e1 e2 e3 x2 x1,
  x2 `notin` fv_dexp e2 ->
  x2 <> x1 ->
  subst_dexp e2 x1 (subst_dexp e3 x2 e1) = subst_dexp (subst_dexp e2 x1 e3) x2 (subst_dexp e2 x1 e1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_subst_dexp :
forall e1 e2 e3 x2 x1,
  x2 `notin` fv_dexp e2 ->
  x2 <> x1 ->
  subst_dexp e2 x1 (subst_dexp e3 x2 e1) = subst_dexp (subst_dexp e2 x1 e3) x2 (subst_dexp e2 x1 e1).
Proof.
pose proof subst_dexp_subst_dexp_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_subst_dexp : lngen.

(* begin hide *)

Lemma subst_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual :
(forall e2 e1 x1 x2 n1,
  x2 `notin` fv_dexp e2 ->
  x2 `notin` fv_dexp e1 ->
  x2 <> x1 ->
  degree_dexp_wrt_dexp n1 e1 ->
  subst_dexp e1 x1 e2 = close_dexp_wrt_dexp_rec n1 x2 (subst_dexp e1 x1 (open_dexp_wrt_dexp_rec n1 (de_var_f x2) e2))).
Proof.
apply_mutual_ind dexp_mutrec;
default_simp.
Qed.

(* end hide *)

(* begin hide *)

Lemma subst_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec :
forall e2 e1 x1 x2 n1,
  x2 `notin` fv_dexp e2 ->
  x2 `notin` fv_dexp e1 ->
  x2 <> x1 ->
  degree_dexp_wrt_dexp n1 e1 ->
  subst_dexp e1 x1 e2 = close_dexp_wrt_dexp_rec n1 x2 (subst_dexp e1 x1 (open_dexp_wrt_dexp_rec n1 (de_var_f x2) e2)).
Proof.
pose proof subst_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_close_dexp_wrt_dexp_rec_open_dexp_wrt_dexp_rec : lngen.

(* end hide *)

Lemma subst_dexp_close_dexp_wrt_dexp_open_dexp_wrt_dexp :
forall e2 e1 x1 x2,
  x2 `notin` fv_dexp e2 ->
  x2 `notin` fv_dexp e1 ->
  x2 <> x1 ->
  lc_dexp e1 ->
  subst_dexp e1 x1 e2 = close_dexp_wrt_dexp x2 (subst_dexp e1 x1 (open_dexp_wrt_dexp e2 (de_var_f x2))).
Proof.
unfold close_dexp_wrt_dexp; unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve subst_dexp_close_dexp_wrt_dexp_open_dexp_wrt_dexp : lngen.

Lemma subst_dexp_de_abs :
forall x2 e2 e1 x1,
  lc_dexp e1 ->
  x2 `notin` fv_dexp e1 `union` fv_dexp e2 `union` singleton x1 ->
  subst_dexp e1 x1 (de_abs e2) = de_abs (close_dexp_wrt_dexp x2 (subst_dexp e1 x1 (open_dexp_wrt_dexp e2 (de_var_f x2)))).
Proof.
default_simp.
Qed.

Lemma subst_dexp_de_fix :
forall x2 e2 e1 x1,
  lc_dexp e1 ->
  x2 `notin` fv_dexp e1 `union` fv_dexp e2 `union` singleton x1 ->
  subst_dexp e1 x1 (de_fixpoint e2) = de_fixpoint (close_dexp_wrt_dexp x2 (subst_dexp e1 x1 (open_dexp_wrt_dexp e2 (de_var_f x2)))).
Proof.
default_simp.
Qed.

Hint Resolve subst_dexp_de_abs subst_dexp_de_fix: lngen.

(* begin hide *)

Lemma subst_dexp_intro_rec_mutual :
(forall e1 x1 e2 n1,
  x1 `notin` fv_dexp e1 ->
  open_dexp_wrt_dexp_rec n1 e2 e1 = subst_dexp e2 x1 (open_dexp_wrt_dexp_rec n1 (de_var_f x1) e1)).
Proof.
apply_mutual_ind dexp_mutind;
default_simp.
Qed.

(* end hide *)

Lemma subst_dexp_intro_rec :
forall e1 x1 e2 n1,
  x1 `notin` fv_dexp e1 ->
  open_dexp_wrt_dexp_rec n1 e2 e1 = subst_dexp e2 x1 (open_dexp_wrt_dexp_rec n1 (de_var_f x1) e1).
Proof.
pose proof subst_dexp_intro_rec_mutual as H; intuition eauto.
Qed.

Hint Resolve subst_dexp_intro_rec : lngen.
Hint Rewrite subst_dexp_intro_rec using solve [auto] : lngen.

Lemma subst_dexp_intro :
forall x1 e1 e2,
  x1 `notin` fv_dexp e1 ->
  open_dexp_wrt_dexp e1 e2 = subst_dexp e2 x1 (open_dexp_wrt_dexp e1 (de_var_f x1)).
Proof.
unfold open_dexp_wrt_dexp; default_simp.
Qed.

Hint Resolve subst_dexp_intro : lngen.


(* *********************************************************************** *)
(** * "Restore" tactics *)

Ltac default_auto ::= auto; tauto.
Ltac default_autorewrite ::= fail.
