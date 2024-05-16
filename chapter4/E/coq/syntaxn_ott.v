(* generated by Ott 0.31, locally-nameless lngen from: ../ott/rules.ott *)
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
(** syntax *)

Inductive nexp : Set :=  (*r expressions *)
 | ne_var_b (_:nat) (*r variables *)
 | ne_var_f (x:var) (*r variables *)
 | ne_lit (i:nat): nexp (*r lit *)
 | ne_abs (e:nexp) (*r abstractions *)
 | ne_app (e1:nexp) (e2:nexp) (*r applications *)
 | ne_add
 | ne_addl (i:nat): nexp.

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_nexp_wrt_nexp_rec (k:nat) (e_5:nexp) (e__6:nexp) {struct e__6}: nexp :=
  match e__6 with
  | (ne_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => ne_var_b nat
        | inleft (right _) => e_5
        | inright _ => ne_var_b (nat - 1)
      end
  | (ne_var_f x) => ne_var_f x
  | ne_lit i => ne_lit i 
  | (ne_abs e) => ne_abs (open_nexp_wrt_nexp_rec (S k) e_5 e)
  | (ne_app e1 e2) => ne_app (open_nexp_wrt_nexp_rec k e_5 e1) (open_nexp_wrt_nexp_rec k e_5 e2)
  | ne_add => ne_add
  | ne_addl i => ne_addl i  
end.

Definition open_nexp_wrt_nexp e_5 e__6 := open_nexp_wrt_nexp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_nexp *)
Inductive lc_nexp : nexp -> Prop :=    (* defn lc_nexp *)
 | lc_ne_var_f : forall (x:var),
     (lc_nexp (ne_var_f x))
 | lc_ne_lit : forall i, 
     (lc_nexp (ne_lit i))
 | lc_ne_abs : forall (e:nexp),
      ( forall x , lc_nexp  ( open_nexp_wrt_nexp e (ne_var_f x) )  )  ->
     (lc_nexp (ne_abs e))
 | lc_ne_app : forall (e1 e2:nexp),
     (lc_nexp e1) ->
     (lc_nexp e2) ->
     (lc_nexp (ne_app e1 e2))
     | lc_ne_add :  
     (lc_nexp (ne_add))
     | lc_ne_addl : forall i, 
     (lc_nexp (ne_addl i))
.



(** free variables *)
Fixpoint fv_nexp (e_5:nexp) : vars :=
  match e_5 with
  | (ne_var_b nat) => {}
  | (ne_var_f x) => {{x}}
  | ne_lit i => {}
  | (ne_abs e) => (fv_nexp e)
  | (ne_app e1 e2) => (fv_nexp e1) \u (fv_nexp e2)
  | ne_add => {}
  | ne_addl i => {}
end.

(** substitutions *)
Fixpoint subst_nexp (e_5:nexp) (x5:var) (e__6:nexp) {struct e__6} : nexp :=
  match e__6 with
  | (ne_var_b nat) => ne_var_b nat
  | (ne_var_f x) => (if eq_var x x5 then e_5 else (ne_var_f x))
  | ne_lit i => ne_lit i 
  | (ne_abs e) => ne_abs (subst_nexp e_5 x5 e)
  | (ne_app e1 e2) => ne_app (subst_nexp e_5 x5 e1) (subst_nexp e_5 x5 e2)
  | ne_add => ne_add 
  | ne_addl i => ne_addl i 
end.


(** definitions *)


(** infrastructure *)
Hint Constructors lc_nexp : core.

