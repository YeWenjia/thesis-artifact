Require Export Metalib.Metatheory.
Require Import Definitions.
Require Import LibTactics.
Require Export Metalib.LibLNgen.
Require Import String.


(** Computing free type variables in a type *)

Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | t_int       => {}
  | t_unit     => {}
  | t_bvar J      => {}
  | t_fvar X      => {{ X }}
  | t_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | t_all T1      => (fv_tt T1)
  | t_ref T1      => (fv_tt T1)
  end.

Fixpoint fv_te (e : exp) {struct e} : atoms :=
match e with
| e_bvar i       => {}
| e_fvar x       => {}
| e_lit i        => {}
| e_unit        => {}
| e_loc l        => {}
| e_abs A e1   => (fv_tt A) `union` (fv_te e1) 
| e_app e1 e2    => (fv_te e1) `union` (fv_te e2)
| e_anno e A     => (fv_te e) `union` (fv_tt A)
| e_tabs e     => (fv_te e) 
| e_tapp e A     => (fv_te e) `union` (fv_tt A)
| e_ref e     => (fv_te e)
| e_get e     => (fv_te e)
| e_set e1 e2    => (fv_te e1) `union` (fv_te e2)
end.

(** Computing free expr variables in a expr *)

Fixpoint fv_ee (e : exp) {struct e} : atoms :=
match e with
| e_bvar i       => {}
| e_fvar x       => {{ x }}
| e_lit i        => {}
| e_unit        => {}
| e_loc l        => {}
| e_abs A e1    => (fv_ee e1)
| e_app e1 e2    => (fv_ee e1) `union` (fv_ee e2)
| e_anno e A     => (fv_ee e)
| e_tabs e      => (fv_ee e)
| e_tapp e A     => (fv_ee e)
| e_ref e     => (fv_ee e)
| e_get e     => (fv_ee e)
| e_set e1 e2    => (fv_ee e1) `union` (fv_ee e2)
end.

(** Substitution for free type variables in types. *)

Fixpoint subst_tt (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | t_int         => t_int
  | t_unit         => t_unit
  | t_bvar J      => t_bvar J
  | t_fvar X      => if X == Z then U else (t_fvar X)
  | t_arrow T1 T2 => t_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | t_all T1      => t_all (subst_tt Z U T1)
  | t_ref T1      => t_ref (subst_tt Z U T1)
  end.

Fixpoint subst_te (z : var) (u : typ) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar i       => e_bvar i
  | e_fvar x       => e_fvar x
  | e_lit i        => e_lit i
  | e_unit         => e_unit
  | e_loc l        => e_loc l
  | e_abs A e1    => e_abs (subst_tt z u A) (subst_te z u e1) 
  | e_app e1 e2    => e_app (subst_te z u e1) (subst_te z u e2)
  | e_anno e A     => e_anno (subst_te z u e) (subst_tt z u A)
  | e_tabs e      => e_tabs (subst_te z u e) 
  | e_tapp e A     => e_tapp (subst_te z u e) (subst_tt z u A)
  | e_ref t1    => e_ref (subst_te z u t1)
  | e_get t1    => e_get (subst_te z u t1)
  | e_set t1 t2 => e_set (subst_te z u t1) (subst_te z u t2)
  end.


(** Substitution for free expr variables in exprs. *)

Fixpoint subst_ee (z : var) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar i       => e_bvar i
  | e_fvar x       => if x == z then u else (e_fvar x)
  | e_lit i        => e_lit i
  | e_unit         => e_unit
  | e_loc l        => e_loc l
  | e_abs A e1    => e_abs A (subst_ee z u e1) 
  | e_app e1 e2    => e_app (subst_ee z u e1) (subst_ee z u e2)
  | e_anno e A     => e_anno (subst_ee z u e) A
  | e_tabs e      => e_tabs (subst_ee z u e) 
  | e_tapp e A     => e_tapp (subst_ee z u e) A
  | e_ref t1    => e_ref (subst_ee z u t1)
  | e_get t1    => e_get (subst_ee z u t1)
  | e_set t1 t2 => e_set (subst_ee z u t1) (subst_ee z u t2)
  end.


Definition subst_tb (Z : var) (P : typ) (b : binding) : binding :=
  match b with
  | bind_tvar => bind_tvar
  | bind_typ T => bind_typ (subst_tt Z P T)
  end.


(* *********************************************************************** *)
(** * Size *)

Fixpoint size_typ (A1 : typ) {struct A1} : nat :=
match A1 with
  | t_fvar X1 => 1
  | t_bvar n1 => 1
  | t_int => 1
  | t_unit => 1
  | t_all A => 1 + (size_typ A) 
  | t_arrow A2 B1 => 1 + (size_typ A2) + (size_typ B1)
  | t_ref A => 1 + (size_typ A) 
end.


Fixpoint size_exp (e1 : exp) {struct e1} : nat :=
match e1 with
  | e_fvar x1 => 1
  | e_bvar n1 => 1
  | e_lit i1 => 1
  | e_unit => 1
  | e_abs A1 e2  => 1 + (size_typ A1) + (size_exp e2) 
  | e_app e2 e3 => 1 + (size_exp e2) + (size_exp e3)
  | e_anno e2 A1 => 1 + (size_exp e2) + (size_typ A1)
  | e_tabs e2  => 1 + (size_exp e2) 
  | e_tapp e2 A1 => 1 + (size_exp e2) + (size_typ A1)
  | e_loc l => 1 
  | e_ref e => 1 + (size_exp e)
  | e_get e => 1 + (size_exp e)
  | e_set e2 e3 => 1 + (size_exp e2) + (size_exp e3)
end.


(** Computing free type variables in a env *)

Fixpoint fv_tt_env (E : env) {struct E} : atoms :=
  match E with
  | nil                      => {}
  | cons (x, bind_typ t) E' => fv_tt t `union` fv_tt_env E'
  | cons (x, bind_tvar) E'  => fv_tt_env E'
  end.

Ltac gather_atoms ::=
let A := gather_atoms_with (fun x : atoms => x) in
let B := gather_atoms_with (fun x : atom => singleton x) in
let C := gather_atoms_with (fun x : exp => fv_te x) in
let D := gather_atoms_with (fun x : exp => fv_ee x) in
let E := gather_atoms_with (fun x : typ => fv_tt x) in
let F := gather_atoms_with (fun x : env => dom x) in
let G := gather_atoms_with(fun x : env => fv_tt_env x) in
constr:(A `union` B `union` C `union` D `union` E `union` F `union` G).


(* ********************************************************************** *)
(** ** Properties of type substitution in types *)


Lemma open_tt_rec_type_aux : forall T j V i U,
i <> j ->
open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
T = open_tt_rec i U T.
Proof with congruence || eauto.
induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
Case "typ_bvar".
  destruct (j === n)... destruct (i === n)...
Qed.


Lemma open_tt_rec_type : forall T U k,
type T ->
T = open_tt_rec k U T.
Proof with auto.
intros T U k Htyp. revert k.
induction Htyp; intros k; simpl; f_equal...
Case "typ_all".
  unfold open_tt in *.
  pick fresh X.
  apply (open_tt_rec_type_aux T2 0 (t_fvar X))...
Qed.


Lemma subst_tt_fresh : forall Z U T,
 Z `notin` fv_tt T ->
 T = subst_tt Z U T.
Proof with auto.
induction T; simpl; intro H; f_equal...
Case "typ_fvar".
  destruct (a == Z)...
  contradict H; fsetdec.
Qed.


Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
type P ->
subst_tt X P (open_tt_rec k T2 T1) =
  open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with auto.
intros T1 T2 X P k WP. revert k.
induction T1; intros k; simpl; f_equal...
-
  destruct (k === n); subst...
- 
 destruct (a == X); subst... apply open_tt_rec_type...
Qed.


Lemma subst_tt_open_tt : forall T1 T2 (X:atom) P,
type P ->
subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof with auto.
intros.
unfold open_tt.
apply subst_tt_open_tt_rec...
Qed.

Lemma subst_tt_open_tt_var : forall (X Y:atom) P T,
Y <> X ->
type P ->
open_tt (subst_tt X P T) Y = subst_tt X P (open_tt T Y).
Proof with congruence || auto.
intros X Y P T Neq Wu.
unfold open_tt.
rewrite subst_tt_open_tt_rec...
simpl.
destruct (Y == X)...
Qed.

Lemma subst_tt_intro_rec : forall X T2 U k,
X `notin` fv_tt T2 ->
open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (t_fvar X) T2).
Proof with congruence || auto.
induction T2; intros U k Fr; simpl in *; f_equal...
- destruct (k === n)... simpl. destruct (X == X)...
- destruct (a == X)... contradict Fr; fsetdec.
Qed.


Lemma subst_tt_intro : forall X T2 U,
  X `notin` fv_tt T2 ->
  open_tt T2 U = subst_tt X U (open_tt T2 (t_fvar X)).
Proof with auto.
  intros.
  unfold open_tt.
  apply subst_tt_intro_rec...
Qed.


(* ********************************************************************** *)
(** ** Properties of type substitution in expressions *)


Lemma open_te_rec_expr_aux : forall e j u i P ,
open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
e = open_te_rec i P e.
Proof with congruence || eauto.
induction e; intros j u i P H; simpl in *; inversion H; f_equal...
Qed.


Lemma open_te_rec_type_aux : forall e j Q i P,
i <> j ->
open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
e = open_te_rec i P e.
Proof.
induction e; intros j Q i P Neq Heq; simpl in *; inversion Heq;
  f_equal; eauto using open_tt_rec_type_aux.
Qed.


Lemma open_te_rec_expr : forall e U k,
expr e ->
e = open_te_rec k U e.
Proof.
intros e U k WF. revert k.
induction WF; intros k; simpl; f_equal; 
auto using open_tt_rec_type;
try solve [
  unfold open_ee in *; 
  pick fresh x;
  eapply open_te_rec_expr_aux with (j := 0) (u := e_fvar x);
  auto
| unfold open_te in *;
  pick fresh X;
  eapply open_te_rec_type_aux with (j := 0) (Q := t_fvar X);
  auto
].
Qed.


Lemma subst_te_open_te_rec : forall e T X U k,
type U ->
subst_te X U (open_te_rec k T e) =
  open_te_rec k (subst_tt X U T) (subst_te X U e).
Proof.
intros e T X U k WU. revert k.
induction e; intros k; simpl; f_equal; auto using subst_tt_open_tt_rec.
Qed.


Lemma subst_te_open_te_var : forall (X Y:atom) U e,
Y <> X ->
type U ->
open_te (subst_te X U e) Y = subst_te X U (open_te e Y).
Proof with congruence || auto.
intros X Y U e Neq WU.
unfold open_te.
rewrite subst_te_open_te_rec...
simpl.
destruct (Y == X)...
Qed.

Lemma subst_te_intro_rec : forall X e U k,
X `notin` fv_te e ->
open_te_rec k U e = subst_te X U (open_te_rec k (t_fvar X) e).
Proof.
induction e; intros U k Fr; simpl in *; f_equal;
  auto using subst_tt_intro_rec.
Qed.


Lemma subst_te_intro : forall X e U,
X `notin` fv_te e ->
open_te e U = subst_te X U (open_te e (t_fvar X)).
Proof with auto.
intros.
unfold open_te.
apply subst_te_intro_rec...
Qed.


Lemma subst_te_open_ee_rec : forall e1 e2 Z P k,
subst_te Z P (open_ee_rec k e2 e1) =
  open_ee_rec k (subst_te Z P e2) (subst_te Z P e1).
Proof with auto.
induction e1; intros e2 Z P k; simpl; f_equal...
Case "exp_bvar".
  destruct (k === n)...
Qed.

Lemma subst_te_open_ee : forall e1 e2 Z P,
subst_te Z P (open_ee e1 e2) = open_ee (subst_te Z P e1) (subst_te Z P e2).
Proof with auto.
intros.
unfold open_ee.
apply subst_te_open_ee_rec...
Qed.


Lemma subst_te_open_ee_var : forall Z (x:atom) P e,
open_ee (subst_te Z P e) x = subst_te Z P (open_ee e x).
Proof with auto.
intros.
rewrite subst_te_open_ee...
Qed.


(* ********************************************************************** *)
(** ** Properties of expression substitution in expressions *)


Lemma subst_ee_fresh : forall (x: atom) u e,
x `notin` fv_ee e ->
e = subst_ee x u e.
Proof with auto.
intros x u e; induction e; simpl; intro H; f_equal...
Case "exp_fvar".
  destruct (a==x)...
  contradict H; fsetdec.
Qed.


Lemma subst_ee_intro_rec : forall x e u k,
x `notin` fv_ee e ->
open_ee_rec k u e = subst_ee x u (open_ee_rec k (e_fvar x) e).
Proof with congruence || auto.
induction e; intros u k Fr; simpl in *; f_equal...
-
   destruct (k === n)... simpl. destruct (x == x)...
- 
  destruct (a == x)... contradict Fr; fsetdec.
Qed.


Lemma subst_ee_intro : forall x e u,
x `notin` fv_ee e ->
open_ee e u = subst_ee x u (open_ee e (e_fvar x)).
Proof with auto.
intros.
unfold open_ee.
apply subst_ee_intro_rec...
Qed.


Lemma open_ee_rec_expr_aux : forall e j v u i,
i <> j ->
open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
e = open_ee_rec i u e.
Proof with congruence || eauto.
induction e; intros j v u i Neq H; simpl in *; inversion H; f_equal...
Case "exp_bvar".
  destruct (j===n)... destruct (i===n)...
Qed.

Lemma open_ee_rec_type_aux : forall e j V u i,
open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
e = open_ee_rec i u e.
Proof.
induction e; intros j V u i H; simpl; inversion H; f_equal; eauto.
Qed.

Lemma open_ee_rec_expr : forall u e k,
expr e ->
e = open_ee_rec k u e.
Proof with auto.
intros u e k Hexpr. revert k.
induction Hexpr; intro k; simpl; f_equal; auto*;
try solve [
  unfold open_ee in *;
  pick fresh x;
  eapply open_ee_rec_expr_aux with (j := 0) (v := e_fvar x);
  auto
| unfold open_te in *;
  pick fresh X;
  eapply open_ee_rec_type_aux with (j := 0) (V := t_fvar X);
  auto
].
Qed.


Lemma subst_ee_open_ee_rec : forall e1 e2 x u k,
expr u ->
subst_ee x u (open_ee_rec k e2 e1) =
  open_ee_rec k (subst_ee x u e2) (subst_ee x u e1).
Proof with auto.
intros e1 e2 x u k WP. revert k.
induction e1; intros k; simpl; f_equal...
Case "exp_bvar".
  destruct (k === n); subst...
Case "exp_fvar".
  destruct (a == x); subst... apply open_ee_rec_expr...
Qed.

Lemma subst_ee_open_ee : forall e1 e2 x u,
expr u ->
subst_ee x u (open_ee e1 e2) =
  open_ee (subst_ee x u e1) (subst_ee x u e2).
Proof with auto.
intros.
unfold open_ee.
apply subst_ee_open_ee_rec...
Qed.


Lemma subst_ee_open_ee_var : forall x y u e, 
 y <> x -> 
 expr u ->
(subst_ee x u e) open_ee_var y = subst_ee x u (e open_ee_var y).
Proof with congruence || auto.
intros x y u e Neq Wu.
unfold open_ee.
rewrite subst_ee_open_ee_rec...
simpl.
destruct (y == x)...
Qed.


Lemma subst_ee_open_te_rec : forall e P z u k,
expr u ->
subst_ee z u (open_te_rec k P e) = open_te_rec k P (subst_ee z u e).
Proof with auto.
induction e; intros P z u k H; simpl; f_equal...
Case "exp_fvar".
  destruct (a == z)... apply open_te_rec_expr...
Qed.

Lemma subst_ee_open_te : forall e P z u,
expr u ->
subst_ee z u (open_te e P) = open_te (subst_ee z u e) P.
Proof with auto.
intros.
unfold open_te.
apply subst_ee_open_te_rec...
Qed.

Lemma subst_ee_open_te_var : forall z X u e,
expr u ->
open_te (subst_ee z u e) X = subst_ee z u (open_te e X).
Proof with auto.
intros z X u e H.
rewrite subst_ee_open_te...
Qed.


Scheme typ_ind' := Induction for typ Sort Prop.

Definition typ_mutind :=
fun H1 H2 H3 H4 H5 H6 H7 =>
typ_ind' H1 H2 H3 H4 H5 H6 H7.

Scheme exp_ind' := Induction for exp Sort Prop.

Definition exp_mutind :=
fun H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 =>
exp_ind' H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12.

Ltac default_auto ::= auto with arith lngen.


Lemma size_exp_open_exp_wrt_exp_rec_var_mutual :
(forall e1 x1 n1,
  size_typ (open_tt_rec n1 (t_fvar x1) e1) = size_typ e1).
Proof.
apply_mutual_ind typ_mutind;
default_simp.
Qed.

Lemma size_exp_open_exp_wrt_exp_rec_var :
forall e1 x1 n1,
  size_typ (open_tt_rec n1 (t_fvar x1) e1) = size_typ e1.
Proof.
pose proof size_exp_open_exp_wrt_exp_rec_var_mutual as H; intuition eauto.
Qed.


Lemma size_open_tt :
forall e1 x1,
  size_typ (open_tt e1 (t_fvar x1)) = size_typ e1.
Proof.
  unfold open_tt;intros. 
  rewrite size_exp_open_exp_wrt_exp_rec_var.
  reflexivity.
Qed.


Lemma fv_ee_open_ee_lower_aux : forall e1 n e2, (*3178*)
fv_ee e1 [<=] fv_ee (open_ee_rec n e2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.

Lemma fv_ee_open_te_lower_aux : forall e1 n e2, (*3178*)
fv_ee e1 [<=] fv_ee (open_te_rec n e2 e1).
Proof.
apply_mutual_ind exp_mutind;
default_simp; fsetdec.
Qed.



Lemma fv_tt_open_tt_lower_aux : forall A n B, (*3178*)
fv_tt A [<=] fv_tt (open_tt_rec n B A).
Proof.
apply_mutual_ind typ_mutind;
default_simp; fsetdec.
Qed.

Lemma fv_ee_open_ee_lower : forall e1 e2,
fv_ee e1 [<=] fv_ee (open_ee e1 e2).
Proof.
intros.
unfold open_ee.
apply* fv_ee_open_ee_lower_aux.
Qed.


Lemma fv_ee_open_te_lower :
forall e1 A1,
fv_ee e1 [<=] fv_ee (open_te e1 A1).
Proof.
intros.
unfold open_te; simpl; try fsetdec.
apply* fv_ee_open_te_lower_aux.
Qed.


Lemma fv_tt_open_tt_lower :
forall e1 A1,
fv_tt e1 [<=] fv_tt (open_tt e1 A1).
Proof.
intros.
unfold open_tt; simpl; try fsetdec.
apply* fv_tt_open_tt_lower_aux.
Qed.


Definition irred e mu mu': Prop := forall b, ~(step (e, mu) (b, mu')).

Lemma step_not_value: forall (v:exp) mu mu',
  value v -> irred v mu mu'.
Proof.
introv.
unfold irred.
inductions v; introv H;
inverts* H;
unfold not;intros;
try solve[inverts* H;
try solve[
destruct F; unfold fill in H0; inverts* H0];
try solve[inverts* H7];
try solve[inverts* H2;inverts H4]];
try solve[inverts* H;
try solve[
destruct F; unfold fill in H1; inverts* H1];
try solve[inverts* H0];
try solve[inverts* H2;inverts H4]].
Qed. 



(* Notation "Γ ⊢ E => A" := (typing Γ E Inf A) (at level 45).
Notation "Γ ⊢ E <= A" := (typing Γ E Chk A) (at level 45). *)
(* Notation "E |- A ~~ B" := (eq E A B) (at level 49). *)
(* Notation "A << B" := (tpre A B) (at level 45).
Notation "e1 <<< e2" := (epre e1 e2) (at level 45). *)

Notation "[ z ~> u ] e" := (subst_ee z u e) (at level 0).
Notation "t ^^ u"       := (open_ee t u) (at level 67).
Notation "e ^ x"        := (open_ee e (e_fvar x)).

Notation "v |-> A v'" := (TypedReduce v A v') (at level 68).
Notation "e ~-> r" := (step e r) (at level 68).

(* Notation "t ->* r" := (steps t r) (at level 68). 


Lemma star_one:
forall a b, step a (r_e b) -> steps a (r_e b).
Proof.
eauto using steps.
Qed.

Lemma star_trans:
forall a b, steps a (r_e b) -> forall c, steps b (r_e c) -> steps a (r_e c).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.

Lemma star_transb:
forall a b, steps a (r_e b) -> steps b r_blame -> steps a r_blame.
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.



Hint Resolve star_one star_trans star_transb: core. *)



(* *********************************************************************** *)
(** * #<a name="body"></a># Properties of [body_e] *)

(** The two kinds of facts we need about [body_e] are the following:
      - How to use it to derive that terms are locally closed.
      - How to derive it from the facts that terms are locally closed.

    Since we use it only in the context of [exp_let] and [exp_sum]
    (see the definition of reduction), those two constructors are the
    only ones we consider below. *)

  
  (* *********************************************************************** *)
  (** * #<a name="auto"></a># Automation *)
  
  (** We add as hints the fact that local closure is preserved under
      substitution.  This is part of our strategy for automatically
      discharging local-closure proof obligations. *)
  
  
  
  Hint Extern 1 (binds _ (?F (subst_tt ?X ?U ?T)) _) =>
    unsimpl (subst_tb X U (F T)) : core.
  