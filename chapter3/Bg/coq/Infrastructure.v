Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import syntax_ott
               rules_inf
               syntaxl_ott.

Require Import List. Import ListNotations.
Require Import Strings.String.


Definition irred e : Prop := forall b, ~(step e b).
Definition eirred e : Prop := forall b, ~(sstep e b).

Notation "Γ ⊢ E ⇒ A" := (Typing Γ E Inf A) (at level 45).
Notation "Γ ⊢ E ⇐ A" := (Typing Γ E Chk A) (at level 45).


Notation "[ z ~> u ] e" := (subst_exp u z e) (at level 0).
Notation "t ^^ u"       := (open_exp_wrt_exp t u) (at level 67).


Notation "v ~-> A v'" := (Cast v A v') (at level 68).


Notation "t ->** r" := (steps t r) (at level 68).


Lemma stars_one:
forall a b, step a (e_exp b) -> steps a (e_exp b).
Proof.
eauto using steps.
Qed.

Lemma stars_trans:
forall a b, steps a (e_exp b) -> forall c, steps b (e_exp c) -> steps a (e_exp c).
Proof.
  introv H.
  inductions H; eauto using steps.
Qed.


Hint Resolve stars_one stars_trans : core.


Notation "x '#' E" := (x \notin (dom E)) (at level 67) : env_scope.

Definition env := list (atom * exp).

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  let C := gather_atoms_with (fun x : list (var * typ) => dom x) in
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let E := gather_atoms_with (fun x : ctx => dom x) in
  let F := gather_atoms_with (fun x : env => dom x) in
  let G := gather_atoms_with (fun x : term => fv_term x) in
  let H := gather_atoms_with (fun x : eexp => fv_eexp x) in
  constr:(A `union` B `union` C `union` D `union` E `union` 
   F `union` G `union` H).



Lemma value_lc : forall v,
    value v -> lc_exp v.
Proof.
  intros v H.
  induction* H. 
Qed.



Lemma step_not_value: forall (v:exp),
    value v -> irred v.
Proof.
  introv.
  unfold irred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros;
  try solve[inverts* H;destruct E; unfold fill in H0; inverts* H0];
  try solve[inverts* H;destruct E; unfold fill in H0; inverts* H0;
  inverts* H3;destruct E; unfold fill in H; inverts* H];
  try solve[inverts* H3;destruct E; unfold fill in H; inverts* H].
Qed.



Lemma sstep_not_evalue: forall (v:eexp),
    evalue v -> eirred v.
Proof.
  introv.
  unfold eirred.
  inductions v; introv H;
  inverts* H;
  unfold not;intros;
  try solve[inverts* H;destruct E; unfold fill in H0; inverts* H0];
  try solve[inverts* H;destruct E; unfold fill in H0; inverts* H0;
  inverts* H3;destruct E; unfold fill in H; inverts* H];
  try solve[inverts* H3;destruct E; unfold fill in H; inverts* H].
Qed.