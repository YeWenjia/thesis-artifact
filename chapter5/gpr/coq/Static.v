
Require Import LibTactics.

Require Import Definitions.
Require Import Infrastructure.
Require Import Lemmas.
Require Import Determinism.
Require Import Soundness.
Require Import Lia.
Require Import rules_inf.


(** * STATIC *)


(* Inductive dexp : Set :=
  | de_bvar   : nat -> dexp
  | de_fvar   : var -> dexp
  | de_lit    : nat -> dexp
  | de_unit   : dexp
  | de_anno   : dexp -> typ -> dexp
  | de_app    : dexp -> dexp -> dexp
  | de_abs    : typ -> dexp  -> dexp 
  | de_tabs   : dexp -> dexp 
  | de_tapp   : dexp -> typ -> dexp
  | de_loc    : nat -> dexp
  | de_ref    : dexp -> dexp
  | de_get    : dexp -> dexp
  | de_set    : dexp -> dexp -> dexp
.


Fixpoint dopen_te_rec (k : nat) (f : typ) (e : dexp) {struct e} : dexp :=
  match e with
  | de_bvar i       => de_bvar i
  | de_fvar x       => de_fvar x
  | de_lit i        => de_lit i
  | de_unit        => de_unit
  | de_loc x      => de_loc x
  | de_app e1 e2    => de_app (dopen_te_rec k f e1) (dopen_te_rec k f e2)
  | de_abs A e1   => de_abs (open_tt_rec k f A) (dopen_te_rec k f e1) 
  | de_anno e1 A    => de_anno (dopen_te_rec k f e1) (open_tt_rec k f A) 
  | de_tabs e1     => de_tabs (dopen_te_rec (S k) f e1) 
  | de_tapp e1 A     => de_tapp (dopen_te_rec k f e1) (open_tt_rec k f A) 
  | de_ref e1     => de_ref (dopen_te_rec k f e1) 
  | de_get e1     => de_get (dopen_te_rec k f e1)
  | de_set e1 e2     => de_set (dopen_te_rec k f e1) (dopen_te_rec k f e2)
  end.

Fixpoint dopen_ee_rec (k : nat) (f : dexp) (e : dexp) {struct e} : dexp :=
  match e with
  | de_bvar i       => if k == i then f else (de_bvar i)
  | de_fvar x       => de_fvar x
  | de_loc x      => de_loc x
  | de_lit i        => de_lit i
  | de_unit        => de_unit
  | de_app e1 e2    => de_app (dopen_ee_rec k f e1) (dopen_ee_rec k f e2)
  | de_abs A e1   => de_abs A (dopen_ee_rec (S k) f e1)
  | de_anno e1 A    => de_anno (dopen_ee_rec k f e1) A 
  | de_tabs e1     => de_tabs (dopen_ee_rec k f e1) 
  | de_tapp e1 A     => de_tapp (dopen_ee_rec k f e1) A 
  | de_ref e1     => de_ref (dopen_ee_rec k f e1) 
  | de_get e1     => de_get (dopen_ee_rec k f e1)
  | de_set e1 e2     => de_set (dopen_ee_rec k f e1) (dopen_ee_rec k f e2)
  end.


Definition dopen_te e T := dopen_te_rec 0 T e.
Definition dopen_ee e1 e2 := dopen_ee_rec 0 e2 e1.


  Notation "t 'dopen_ee_var' x" := (dopen_ee t (de_fvar x)) (at level 67).

  Notation "t 'dopen_te_var' a" := (dopen_te t (t_fvar a)) (at level 67).
 *)




Inductive dtyp_static : typ -> Prop :=
  | dtyp_static_nat:
      dtyp_static t_int
  | dtyp_static_fvar: forall i,
      dtyp_static (t_fvar i)
  | dtyp_static_arrow: forall A B,
      dtyp_static A ->
      dtyp_static B ->
      dtyp_static (t_arrow A B)
  | dtyp_static_all: forall L A,
      (forall x, x \notin L -> dtyp_static (A open_tt_var x)) ->
      dtyp_static (t_all A)
  | dtyp_ref: forall A,
      dtyp_static A ->
      dtyp_static (t_ref A) 
   | dtyp_static_unit:
      dtyp_static t_unit
.

Inductive dterm_static : exp -> Prop :=
  | dterm_static_var: forall x,
      dterm_static (e_fvar x)
  | dterm_static_nat : forall i,
      dterm_static (e_lit i)
  | dterm_static_unit : 
      dterm_static e_unit
  | dterm_static_tabs : forall L e1,
      (forall x, x \notin L -> dterm_static (e1 open_te_var x)) ->
      dterm_static (e_tabs e1)
  | dterm_static_abs : forall L e1 ,
      (forall x, x \notin L -> dterm_static (e1 open_ee_var x)) ->
      dterm_static (e_abs e1)
  | dterm_static_app : forall e1 e2,
      dterm_static e1 ->
      dterm_static e2 ->
      dterm_static (e_app e1 e2)
  | dterm_static_tapp : forall e A,
      dterm_static e ->
      dtyp_static A ->
      dterm_static (e_tapp e A)
  | dterm_static_ref : forall e,
      dterm_static e ->
      dterm_static (e_ref e)
  | dterm_static_get : forall e,
      dterm_static e ->
      dterm_static (e_get e)
  | dterm_static_set : forall e1 e2,
      dterm_static e1 ->
      dterm_static e2 ->
      dterm_static (e_set e1 e2)
  | dterm_static_loc : forall i,
      dterm_static (e_loc i)
  | dterm_static_anno : forall e A,
      dterm_static e ->
      dtyp_static A ->
      dterm_static (e_anno e A)
  | dterm_static_pval : forall e A,
      dterm_static e ->
      dtyp_static A ->
      dterm_static (e_val e A)
  | dterm_static_rval : forall e,
      dterm_static e ->
      dterm_static (e_rval e)
.

Inductive denv_static : env -> Prop :=
  | denv_static_empty : denv_static empty
  | denv_static_typ : forall E x T,
      denv_static E ->
      dtyp_static T ->
      wf_typ E T ->
      x \notin dom E ->
      denv_static ( x ~: T ++ E)
  | denv_static_tvar : forall E x,
      denv_static E ->
      x \notin dom E ->
      denv_static (x ~tvar ++ E)
.


Inductive phi_static : phi -> Prop :=
  | phi_static_typ : forall E,
      (forall l,  l < length (E) -> 
      dtyp_static (store_Tlookup l E)) ->
      phi_static (E).



Inductive eq: env -> typ -> typ -> Prop :=  
  | eq_int : forall E,
      wf_env E ->
      eq E t_int t_int
  | eq_unit : forall E,
      wf_env E ->
      eq E t_unit t_unit
  | eq_var : forall E x,
      wf_env E ->
      wf_typ E (t_fvar x) ->
      eq E (t_fvar x) (t_fvar x)
  | eq_fun : forall E A1 A2 B1 B2,
      eq E B1 A1 ->
      eq E A2 B2 ->
      eq E (t_arrow A1 A2) (t_arrow B1 B2)
  | eq_all: forall L E A B ,
      (forall x, x \notin L ->
      eq (x ~tvar ++ E) (A open_tt_var x) (B open_tt_var x)) ->
      eq E (t_all A) (t_all B)
  | eq_ref : forall E A B,
      eq E A B ->
      eq E (t_ref A) (t_ref B)
.



Inductive styping : env -> phi -> exp -> dirflag -> typ -> Prop :=
  | styp_var : forall E P x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      styping E P (e_fvar x) Inf T
  | styp_nat : forall E P i,
      wf_env E ->
      styping E P (e_lit i) Inf (t_int)
  | styp_unit : forall E P,
      wf_env E ->
      styping E P e_unit Inf t_unit
  | styp_loc : forall E P l,
       wf_env E ->
      l < length P ->
      wf_typ E (store_Tlookup l P) ->
      styping E P (e_loc l) Inf (t_ref (store_Tlookup l P))
  | styp_app : forall E P e1 e2 A B,
      styping E P e1 Inf (t_arrow A B) ->
      styping E P e2 Chk A ->
      styping E P (e_app e1 e2) Inf B
  | styp_abs : forall L E P A B e,
      (forall x, x \notin L ->
            styping (x ~: A ++ E) P (e open_ee_var x) Chk B) ->
      styping E P (e_abs e) Chk (t_arrow A B)
  | styp_anno : forall E P e A,
     styping E P e Chk A ->
     styping E P (e_anno e A) Inf A
  | styp_tabs : forall L E P e A,
      ( forall a , a \notin  L  -> 
      styping  ( a ~tvar ++ E) P ( e open_te_var a )  Chk  ( A open_tt_var a )  )  ->
     styping E P (e_tabs e) Chk (t_all A)
  | styp_tapp : forall E P e A B,
      wf_typ E A ->
     styping E P e Inf (t_all B) ->
     styping E P (e_tapp e A) Inf  (open_tt B A )
  | styp_eq : forall E P e B A,
     eq E A B ->
     styping E P e Inf A ->
     styping E P e Chk B
  | styp_ref : forall E P e A,
     styping E P e Inf A ->
     styping E P (e_ref e) Inf (t_ref A)
  | styp_get : forall E P e A1,
     styping E P e Inf (t_ref A1) ->
     styping E P (e_get e) Inf A1
  | styp_set : forall E P e1 e2 A1,
     styping E P e1 Inf (t_ref A1) ->
     styping E P e2 Chk A1->
     styping E P (e_set e1 e2) Inf t_unit
  | styp_rt : forall E P (p:exp) A,
     wf_env E ->
     pvalue p ->
     typing nil P p Chk A ->
     tpre (dynamic_type p) A -> 
     styping E P (e_val p A) Inf A
  | styp_absv : forall L G P  (e e2:exp) A B,
     ( forall x , x \notin  L  -> 
     styping  (x ~ bind_typ A ++ G ) P (e open_ee_var x)  Chk B )  ->
     styping G P e2 Inf A ->
     styping G P (e_app (e_abs e) e2) Chk B
  | styp_rts : forall E P e2 l,
     l < length P ->
     styping E P e2 Inf (store_Tlookup l P) ->
     styping E P (e_set (e_rval (e_loc l)) e2) Inf t_unit
.

(* 
Inductive sstyping : env -> phi -> exp -> dirflag -> typ -> dexp -> Prop :=
  | sstyp_var : forall E P x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      sstyping E P (e_fvar x) Inf T (de_fvar x)
  | sstyp_nat : forall E P i,
      wf_env E ->
      sstyping E P (e_lit i) Inf (t_int) (de_lit i)
  | sstyp_unit : forall E P,
      wf_env E ->
      sstyping E P e_unit Inf t_unit de_unit
  | sstyp_loc : forall E P l,
       wf_env E ->
      l < length P ->
      wf_typ E (store_Tlookup l P) ->
      sstyping E P (e_loc l) Inf (t_ref (store_Tlookup l P)) (de_loc l)
  | sstyp_app : forall E P e1 e2 A B t1 t2,
      sstyping E P e1 Inf (t_arrow A B) t1 ->
      sstyping E P e2 Chk A t2 ->
      sstyping E P (e_app e1 e2) Inf B (de_app t1 t2)
  | sstyp_abs : forall L E P A B e t,
      (forall x, x \notin L ->
            sstyping (x ~: A ++ E) P (e open_ee_var x) Chk B (t dopen_ee_var x)) ->
      sstyping E P (e_abs A e B) Inf (t_arrow A B) (de_abs A t)
  | sstyp_anno : forall E P e A t,
     sstyping E P e Chk A t ->
     sstyping E P (e_anno e A) Inf A (de_anno t A)
  | sstyp_tabs : forall E P e A L t,
      ( forall a , a \notin  L  -> 
      sstyping  ( a ~tvar ++ E) P ( e open_te_var a )  Chk  ( A open_tt_var a )   ( t dopen_te_var a ))  ->
     sstyping E P (e_tabs e A) Inf (t_all A) (de_tabs t)
  | sstyp_tapp : forall E P e A B t,
      wf_typ E A ->
     sstyping E P e Inf (t_all B) t ->
     sstyping E P (e_tapp e A) Inf  (open_tt B A ) (de_tapp t A)
  | sstyp_eq : forall E P e B A t,
     eq E A B ->
     sstyping E P e Inf A t ->
     sstyping E P e Chk B t
  | sstyp_ref : forall E P e A t,
     sstyping E P e Inf A t ->
     sstyping E P (e_ref e) Inf (t_ref A) (de_ref t)
  | sstyp_get : forall E P e A1 t,
     sstyping E P e Inf (t_ref A1) t ->
     sstyping E P (e_get e) Inf A1 (de_get t)
  | sstyp_set : forall E P e1 e2 A1 t1 t2,
     sstyping E P e1 Inf (t_ref A1) t1 ->
     sstyping E P e2 Chk A1 t2 ->
     sstyping E P (e_set e1 e2) Inf t_unit (de_set t1 t2)
. *)


(* Inductive atyping : env -> phi -> dexp -> dirflag -> typ -> Prop :=
| atyp_var : forall E P x T,
    wf_env E ->
    binds x (bind_typ T) E ->
    atyping E P (de_fvar x) Inf T
| atyp_nat : forall E P i,
    wf_env E ->
    atyping E P (de_lit i)  Inf (t_int)
| atyp_unit : forall E P,
    wf_env E ->
    atyping E P de_unit  Inf t_unit
| atyp_loc : forall E P l,
    wf_env E ->
    l < length P ->
    wf_typ E (store_Tlookup l P) ->
    atyping E P (de_loc l)  Inf  (t_ref (store_Tlookup l P))
| atyp_app : forall E P e1 e2 A B,
    atyping E P e1 Inf (t_arrow A B) ->
    atyping E P e2 Chk  A ->
    atyping E P (de_app e1 e2)  Inf  B
| atyp_abs : forall L E P A B e,
    (forall x, x \notin L ->
            atyping (x ~: A ++ E) P (e dopen_ee_var x) Chk  B) ->
    atyping E P (de_abs A e)  Inf  (t_arrow A B)
| atyp_anno : forall E P e A,
    atyping E P e Chk A ->
    atyping E P (de_anno e A)  Inf  A
| atyp_tabs : forall E P e A L,
    ( forall a , a \notin  L  -> 
    atyping  ( a ~tvar ++ E) P ( e dopen_te_var a )  Chk  ( A open_tt_var a )  )  ->
    atyping E P (de_tabs e) Inf (t_all A)
| atyp_tapp : forall E P e A B,
    wf_typ E A ->
    atyping E P e  Inf  (t_all B) ->
    atyping E P (de_tapp e A)  Inf  (open_tt B A )
| atyp_ref : forall E P e A,
    atyping E P e Inf  A ->
    atyping E P (de_ref e) Inf (t_ref A)
| atyp_get : forall E P e A1,
    atyping E P e  Inf (t_ref A1) ->
    atyping E P (de_get e) Inf A1
| atyp_set : forall E P e1 e2 A1,
    atyping E P e1  Inf (t_ref A1) ->
    atyping E P e2 Chk A1->
    atyping E P (de_set e1 e2) Inf t_unit
| atyp_eq : forall E P e A B,
    atyping E P e Inf A ->
    eq E A B ->
    atyping E P e Chk B
. *)



(* 

Inductive aatyping : env -> phi -> dexp -> dirflag -> typ -> exp -> Prop :=
| aatyp_var : forall E P x T,
    wf_env E ->
    binds x (bind_typ T) E ->
    aatyping E P (de_fvar x) Inf T (e_fvar x)
| aatyp_nat : forall E P i,
    wf_env E ->
    aatyping E P (de_lit i)  Inf (t_int) (e_lit i)
| aatyp_unit : forall E P,
    wf_env E ->
    aatyping E P de_unit  Inf  t_unit e_unit
| aatyp_loc : forall E P l,
    wf_env E ->
    l < length P ->
    wf_typ E (store_Tlookup l P) ->
    aatyping E P (de_loc l) Inf (t_ref (store_Tlookup l P)) (e_loc l)
| aatyp_app : forall E P e1 e2 A B t1 t2,
    aatyping E P e1 Inf (t_arrow A B) t1 ->
    aatyping E P e2  Chk A t2 ->
    aatyping E P (de_app e1 e2) Inf B (e_app t1 t2)
| aatyp_abs : forall L E P A B e t,
    (forall x, x \notin L ->
            aatyping (x ~: A ++ E) P (e dopen_ee_var x)  Chk B (t open_ee_var x) ) ->
    aatyping E P (de_abs A e) Inf (t_arrow A B) (e_abs A t B)
| aatyp_anno : forall E P e A t,
    aatyping E P e  Chk A t ->
    aatyping E P (de_anno e A) Inf A (e_anno t A)
| aatyp_tabs : forall E P e A L t,
    ( forall a , a \notin  L  -> 
    aatyping  ( a ~tvar ++ E) P ( e dopen_te_var a )   Chk ( A open_tt_var a ) ( t open_te_var a ) )  ->
    aatyping E P (de_tabs e) Inf (t_all A) (e_tabs t A)
| aatyp_tapp : forall E P e A B t,
    wf_typ E A ->
    aatyping E P e Inf (t_all B) t ->
    aatyping E P (de_tapp e A)  Inf (open_tt B A ) (e_tapp t A) 
| aatyp_ref : forall E P e A t,
    aatyping E P e Inf A t ->
    aatyping E P (de_ref e) Inf (t_ref A) (e_ref t)
| aatyp_get : forall E P e A1 t,
    aatyping E P e Inf (t_ref A1) t ->
    aatyping E P (de_get e) Inf A1 (e_get t)
| aatyp_set : forall E P e1 e2 A1 t1 t2,
    aatyping E P e1 Inf (t_ref A1) t1 ->
    aatyping E P e2 Chk A1 t2 ->
    aatyping E P (de_set e1 e2) Inf t_unit (e_set t1 t2)
| aatyp_eq : forall E P e A t B,
    aatyping E P e Inf A t ->
    eq E A B ->
    aatyping E P e Chk B t
. *)



Inductive dstep : conf -> conf -> Prop :=    (* defn dstep *)
 | dstep_eval : forall mu mu' F e1 e2,
     wellformed F ->
     dstep (e1, mu) ((e2), mu') ->
     dstep ((fill F e1), mu) (((fill F e2)), mu')
 | dstep_beta : forall  e (v:exp) mu,
     sto_ok mu ->
     value v ->
     expr (e_abs e) ->
     dstep ((e_app (e_abs e)  v), mu) ((open_ee  e v ), mu)
 | dstep_app : forall A1 A2 B1 B2 C C1 C2 e (v v':exp) mu,
     sto_ok mu ->
     expr (e_abs e) ->
     pattern_abs C  (t_arrow C1 C2) ->
     dstep ((e_app (e_val  (e_anno (e_anno (e_abs e) (t_arrow A1 A2)) (t_arrow B1 B2))  C)  v), mu) (((e_anno (e_anno (e_anno  (e_app (e_abs e) (e_anno (e_anno (e_anno v C1) B1) A1) )  A2) B2) C2)), mu)
 | dstep_annov : forall (v:exp) (A:typ) r mu,
     sto_ok mu ->
     value v ->
     Castv (v, mu) A (r_e r) ->
     dstep ((e_anno v A), mu) (r, mu)
 | dstep_abs : forall e A0 A B mu,
      expr (e_abs e) ->
      pattern_abs A0  (t_arrow A B) ->
      dstep ((e_anno (e_abs e) A0), mu) (((e_val (e_anno (e_anno (e_abs e) (t_arrow A B)) (t_arrow A B)) A0)), mu)
 | dstep_tabs : forall e A0 A mu,
      expr (e_tabs e) ->
      pattern_all A0  (t_all A) ->
      dstep ((e_anno (e_tabs e) A0), mu) (((e_val (e_anno (e_anno (e_tabs e) (t_all A )) (t_all A )) A0)), mu)
 | dstep_lit : forall i mu,
      dstep ((e_lit i), mu) (((e_val (e_lit i) t_int)), mu)
 | dstep_unit : forall mu,
      dstep ((e_unit), mu) (((e_val (e_unit) t_unit)), mu)
 | dstep_loc : forall mu o,
      dstep ((e_loc o), mu) (((e_val (e_anno (e_loc o) (t_ref (dynamic_type (store_lookup o mu)))) (t_ref (dynamic_type (store_lookup o mu))))), mu)
 | dstep_tapp : forall (e:exp) A A1 A2 A3 B mu,
     expr (e_tabs e) ->
     pattern_all A (t_all A3) ->
     dstep ((e_tapp (e_val (e_anno  (e_anno (e_tabs e) (t_all A1)) (t_all A2)) A) B),mu) (((e_anno (e_anno (e_anno (open_te  e B ) (open_tt  A1 B )) (open_tt  A2 B)) (open_tt  A3 B))),mu)
 | dstep_setv : forall l v2 mu,
     sto_ok mu ->
     value v2 ->
     dstep ((e_set (e_rval (e_loc l)) v2), mu) ((e_unit), replace l v2 mu)
 | dstep_set : forall l A1 A A2 v2 mu,
     sto_ok mu ->
     pattern_ref A (t_ref A2) ->
     dstep ((e_set (e_val (e_anno (e_loc l) (t_ref A1)) A) v2), mu) (( (e_set (e_rval (e_loc l)) (e_anno (e_anno (e_anno v2 A2) A1) (dynamic_type (store_lookup l mu)) ))), mu)
 | dstep_new : forall (v:exp) mu,
     sto_ok mu ->
     value v ->
     dstep ((e_ref v), mu) (((e_loc (length mu))), (mu ++ v::nil))
 | dstep_get : forall l A C B mu,
     sto_ok mu ->
     pattern_ref C (t_ref B) ->
     dstep ((e_get (e_val (e_anno (e_loc l) (t_ref A)) C)), mu) (((e_anno (e_anno (store_lookup l mu) A) B)), mu)
.



(** Properties for static *)


Hint Constructors denv_static dterm_static dtyp_static styping eq dstep: core.


Lemma eq_type: forall A B x n,
 x `notin` (fv_tt A) ->
 x `notin` (fv_tt B) ->
 open_tt_rec n x A = open_tt_rec n x B ->
 A = B.
Proof.
  introv nt1 nt2 eq. 
  forwards*: open_typ_wrt_typ_rec_inj A B.
Qed.


Lemma eq_left: forall A B E,
 eq E A B ->
 A = B.
Proof.
  introv eq.
  inductions eq; eauto.
  - inverts* IHeq1.  inverts* IHeq2.
  - pick fresh x.
    forwards* h1: H0 x.
    forwards*: eq_type h1.
    inverts* H1.
  - inverts* IHeq. 
Qed.



Lemma eq_rel: forall E A,
dtyp_static A ->
 wf_typ E A ->
 wf_env E ->
 eq E A A.
Proof.
  introv sta ty ev.
  inductions ty; eauto; try solve[inverts sta].
  -
  inverts* sta.
  -
  inverts sta.
  pick fresh x.
  apply eq_all with (L := union L
  (union L0
     (union (fv_tt A)
        (union (dom E) (fv_tt_env E)))));intros.
  forwards: H2 x0; auto.
  -
  inverts* sta.
Qed.


Lemma eq_right: forall A B E,
dtyp_static A ->
 wf_env E ->
 wf_typ E A ->
 wf_typ E B ->
 A = B ->
 eq E A B.
Proof.
  introv sta ev wf1 wf2 eq.
  inverts* eq.
  apply eq_rel; auto.
Qed.

(* Lemma sstyping_atyping: forall e1 e2 G P dir A,
  sstyping G P e1 dir A e2 ->
  atyping G P e2 dir A.
Proof.
  introv typ.
  inductions typ; eauto.  
Qed.



Lemma aatyping_styping: forall dir e1 e2 G P A,
 aatyping G P e1 dir A e2 ->
 styping G P e2 dir A.
Proof.
  introv typ.
  inductions typ; eauto.
Qed. *)



Lemma dtyp_static_eq: forall E A B,
    dtyp_static A ->
    dtyp_static B ->
    consist E A B ->
    eq E A B.
Proof.
  introv ta tb con.
  inductions con; eauto; try solve[inverts ta];
  try solve[inverts tb];
  try solve[inverts ta;inverts tb].
  -
  inverts ta; inverts* tb.
  -
  inversions tb. inverts ta.
  pick fresh y and apply eq_all.
  forwards ~ : H3 y.
  -
  inverts ta. inverts* tb.
Qed. 



Lemma eq_consist: forall E A B,
    eq E A B ->
    consist E A B.
Proof.
  introv con.
  inductions con; eauto.
Qed. 


Lemma dtyp_static_dtype : forall A,
    dtyp_static A ->
    type A.
Proof.
  introv ty. inductions ty; simpls~.
Qed.


Hint Resolve dtyp_static_dtype : core.

Lemma dterm_static_dterm: forall e,
    dterm_static e ->
    expr e.
Proof.
  introv dm. inductions dm; eauto.
Qed.


(* typing1 *)
Lemma styping_typing : forall E P e dir A,
  styping E P e dir A ->
  typing E P e dir A.
Proof.
    introv typ.
    inductions typ;eauto.
    forwards*: eq_consist H.
Qed.



Lemma dmatch_static_ref : forall A A1,
    pattern_ref A A1 ->
    dtyp_static A ->
    dtyp_static A1 .
Proof.
  introv mat st. inductions mat; simpls~.
Qed.


Lemma dmatch_static_abs : forall A A1,
    pattern_abs A A1 ->
    dtyp_static A ->
    dtyp_static A1 .
Proof.
  introv mat st. inductions mat; simpls~.
Qed.

Lemma dmatch_static_all : forall A A1,
    pattern_all A A1 ->
    dtyp_static A ->
    dtyp_static A1 .
Proof.
  introv mat st. inductions mat; simpls~.
  inverts st.
Qed.


Lemma denv_static_dtyp: forall e x T,
    denv_static e ->
    binds x (bind_typ T) e ->
    dtyp_static T.
Proof.
  introv dm bd. inductions dm; try solve[inverts bd].
  -
  analyze_binds bd.
  inverts* BindsTacVal.
  -
  analyze_binds bd.
Qed.




Lemma static_open: forall e1 u1  x,
 dtyp_static e1 ->
 dtyp_static u1 ->
 type u1 ->
 dtyp_static (subst_tt u1 x e1).
Proof.
  introv ts1 ts2 typ1. gen u1 x.
  inductions ts1; intros; 
  simpl; eauto.
  -
  destruct (i == x); eauto.
  -
  pick fresh y and apply dtyp_static_all.
  rewrite tsubst_typ_open_typ_wrt_typ_var; eauto. 
Qed.




Definition Dtyping_static_preserve dir T := 
  match dir with 
  | Inf => dtyp_static T
  | Chk  => True
  end.




Lemma dtyping_static_preserve : forall E e P dir T,
    typing E P e dir T ->
    denv_static E ->
    dterm_static e ->
    phi_static P ->
    Dtyping_static_preserve dir T.
Proof.
  introv Hty Hen Htm Hpi.
  inductions Hty; auto; unfold Dtyping_static_preserve in *;simpl; auto;
  try solve[inverts* Htm].
  -
    forwards*: denv_static_dtyp H0.
  -
    inverts Hpi.
    forwards*: H2 l.
  -
    inverts Htm.
    forwards* h1: IHHty1 H2.
    forwards* h3: dmatch_static_abs H. inverts* h3.
  -
    inverts* Htm.
    forwards* h1: IHHty.
    inverts H0; try solve[inverts h1].
    inverts h1.
      pick fresh y.
      rewrite (tsubst_typ_intro y); eauto.
      forwards*: H1 y.
      forwards*: static_open H0 H4.
  -
    inverts Htm.
    forwards* h1: IHHty.
    forwards* h2: dmatch_static_ref h1.
    inverts* h2.
Qed.





(* typing2 *)
Lemma typing_styping : forall E P e dir A,
  dterm_static e ->
  denv_static E ->
  phi_static P ->
  dtyp_static A ->
  typing E P e dir A ->
   styping E P e dir A.
Proof.
  introv es vs ps ts typ.
  lets typ': typ.
  inductions typ;eauto; try solve[inverts es].
  -
    inverts es.
    forwards* h1: dtyping_static_preserve typ1.
    forwards* h2: dmatch_static_abs H.
    inverts* h2.
    forwards*: IHtyp1.
    forwards* h3: dtyping_static_preserve typ2.
    inverts* H; try solve[inverts h1].
  -
    inverts es.
    forwards h1: typing_regular typ'.
    destructs~ h1. 
    inverts H1; try solve[inverts ts].
    inverts ts.
    inverts H5.
    pick fresh x and apply styp_abs.
    forwards*: H x.
  -
    inverts* es.
  -
    inverts es.
    forwards h1: typing_regular typ'.
    destructs~ h1. 
    inverts H1; try solve[inverts ts].
    inverts ts.
    inverts H5.
    pick fresh x and apply styp_tabs.
    forwards*: H x.
  -
    inverts es.
    forwards* h1: dtyping_static_preserve typ.
    forwards* h2: dmatch_static_all H0.
    inverts* h2.
    forwards*: IHtyp.
    inverts* H0; try solve[inverts h1].
  -
    forwards* h1: dtyping_static_preserve typ.
    forwards*: dtyp_static_eq H.
  -
    inverts* es.
    inverts* ts.
  -
    inverts es.
    forwards* h1: dtyping_static_preserve typ.
    forwards* h2: dmatch_static_ref H.
    inverts* h2.
    forwards*: IHtyp.
    inverts* H; try solve[inverts h1].
  -
    inverts es.
    forwards* h1: dtyping_static_preserve typ1.
    forwards* h2: dmatch_static_ref H.
    inverts* h2.
    forwards*: IHtyp1.
    forwards* h3: dtyping_static_preserve typ2.
    inverts* H; try solve[inverts h1].
  -
    inverts es.
    forwards h3: dtyping_static_preserve typ; auto.
    inverts H3.
    forwards h2:IHtyp typ; auto.
    pick fresh y and apply styp_absv.
    forwards* h1: H y; auto.
    auto.
  -
    inverts es.
    forwards h3: dtyping_static_preserve typ; auto.
Qed.



Lemma  eq_sym: forall E t1 t2,
 eq E t1 t2 ->
 eq E t2 t1.
Proof.
  introv eq.
  inductions eq;intros; try solve[inductions eq0;eauto];eauto.
Qed.


Lemma  eq_static: forall E t1 t2,
 eq E t1 t2 ->
 dtyp_static t1 ->
 dtyp_static t2 .
Proof.
  introv eq sta. gen E t2.
  inductions sta;intros; try solve[inductions eq0;eauto];eauto.
  -
  inverts eq0.
  forwards*:  eq_sym H2.
  -
  inverts eq0.
  pick fresh x and apply dtyp_static_all;eauto.
Qed.


Lemma eq_refl: forall t e,
 wf_env e ->
 wf_typ e t ->
 dtyp_static t ->
 eq e t t.
Proof.
  introv we ev dt. gen e.
  inductions dt;intros;auto; try solve[inverts ev].
  -
    inverts* ev.
  -
  inverts ev.
  pick fresh y and apply eq_all;eauto.
  -
  inverts* ev.
Qed.




Lemma styping_chk: forall E e P A,
denv_static E ->
phi_static P ->
 dterm_static e ->
 styping E P e Inf A ->
 styping E P e Chk A.
Proof.
  introv es ps se typ.
  eapply styp_eq; eauto.
  forwards h2: styping_typing typ.
    forwards h1: dtyping_static_preserve h2; auto.
    unfold Dtyping_static_preserve in *.
    forwards*: eq_refl h1.
Qed.



Lemma fill_chk_chk: forall G e E P B,
 denv_static G ->
 phi_static P ->
 dterm_static e ->
 styping G P (fill E e) Chk B ->
 dtyp_static B ->
 (exists A, styping G P e Chk A) \/ exists l, e = (e_rval (e_loc l)).
Proof.
  introv es ps te typ st.
  destruct E; unfold fill in *; inverts* typ;
  try solve[inverts* H0].
  - inverts H0.
    forwards h2: styping_typing H5.
    forwards h1: dtyping_static_preserve h2; auto.
    unfold Dtyping_static_preserve in *.
    inverts h1.
    forwards*: styping_chk H5.
  -
     forwards*: styping_chk H4.
  -
    inverts H0.
    forwards*: styping_chk H6.
  -
    inverts H0.
    forwards*: styping_chk H4.
  -
    inverts H0.
    forwards*: styping_chk H5.
    right; eauto.
  -
    inverts* H0; auto.
    forwards*: styping_chk H6.
Qed.


Lemma fill_chk_chk2: forall G e E P B,
 denv_static G ->
 phi_static P ->
 dterm_static e ->
 styping G P (fill E e) Chk B ->
 (exists A, styping G P e Chk A) \/ exists l, e = (e_rval (e_loc l)).
Proof.
  introv es ps te typ.
  destruct E; unfold fill in *; inverts* typ;
  try solve[inverts* H0].
  - inverts H0.
    forwards h2: styping_typing H5.
    forwards h1: dtyping_static_preserve h2; auto.
    unfold Dtyping_static_preserve in *.
    inverts h1.
    forwards*: styping_chk H5.
  -
     forwards*: styping_chk H4.
  -
    inverts H0.
    forwards*: styping_chk H6.
  -
    inverts H0.
    forwards*: styping_chk H4.
  -
    inverts H0.
    forwards*: styping_chk H5.
    right; eauto.
  -
    inverts* H0; auto.
    forwards*: styping_chk H6.
Qed.


Lemma fill_static: forall F e,
  dterm_static (fill F e) ->
  dterm_static e.
Proof.
 introv dt.
  destruct F; unfold fill in *; auto;
  try solve[inverts dt; auto].
Qed.




Lemma eq_trans_size: forall E A B C n,
 size_typ A + size_typ B + size_typ C < n ->
 eq E A B ->
 eq E B C ->
 eq E A C.
Proof.
  introv sz eq1 eq2. gen E A B C.
  induction n;intros; 
  try solve[lia].
  inductions eq1;eauto.
  -
  inductions eq2;simpl in *;auto.
  forwards: IHn eq2_1 eq1_1. lia.
  forwards: IHn eq1_2 eq2_2. lia.
  auto.
  -
  inductions eq2;simpl in *;auto.
  pick fresh x and apply eq_all.
  forwards h1: H x; auto.
  forwards h2: H1 x; auto.
  forwards: IHn h1 h2.
  rewrite size_typ_open_typ_wrt_typ_var.
  rewrite size_typ_open_typ_wrt_typ_var.
  rewrite size_typ_open_typ_wrt_typ_var.
  lia.
  auto.
  -
  inductions eq2;simpl in *;auto.
  forwards: IHn eq1 eq2. lia.
  auto.
Qed.


Lemma eq_trans: forall E A B C,
 eq E A B ->
 eq E B C ->
 eq E A C.
Proof.
  introv eq1 eq2. 
  eapply eq_trans_size ;eauto.
Qed.



Lemma sprinciple_typ_inf: forall G P u A,
 value u -> 
 styping G P u Inf A -> 
 dynamic_type u = A.
Proof.
  introv val typ.
  inverts* val; try solve[inverts* typ].
Qed.


Definition dirred e mu mu': Prop := forall b, ~(dstep (e, mu) (b, mu')).

Lemma dstep_not_ires: forall (v:exp) mu mu',
  ires v -> dirred v mu mu'.
Proof.
introv.
unfold dirred.
inductions v; introv H;
inverts* H;
unfold not;intros;
try solve[
  inverts* H;
  try solve[
  destruct F; unfold fill in H0; inverts* H0];
  try solve[inverts* H7];
  try solve[inverts* H2;inverts H4]].
Qed. 

Lemma dstep_not_rv: forall l mu mu',
  dirred (e_rval (e_loc l)) mu mu'.
Proof.
  introv.
  unfold dirred.
  introv H;
  inverts* H;
  unfold not;intros;
  try solve[
    inverts* H;
    try solve[
    destruct F; unfold fill in H0; inverts* H0];
    try solve[inverts* H7];
    try solve[inverts* H2;inverts H4]].
    destruct F; unfold fill in H0; inverts* H0.
Qed. 


(* step1 *)

Theorem static_ddstep_dyn_chk : forall e e' B P mu mu',
  P |== mu ->
  phi_static P ->
 dterm_static e ->
 (* dtyp_static B -> *)
 styping nil P e Chk B ->
 dstep ( e, mu) ( e', mu') -> 
 step (e, mu) ((r_e e'), mu').
Proof.
 introv wel ps ts typ red. gen B P.
 inductions red; intros; eauto;
 try solve[forwards*:eq_consist  H1];
 try solve[forwards*: eq_consist H0].
 - 
   forwards h0 :  fill_static ts.
   forwards hh0: fill_chk_chk2 typ; auto. 
   inverts hh0 as hh0;
   try solve[inverts hh0 as hh0; forwards hhh1: dstep_not_rv red; auto;
   inverts hhh1; auto].
   inverts hh0.
   forwards* hh3: IHred H0.
Qed.


(* step2 *)

Lemma typing_c_rename : forall (x y : atom) E P e T1 T2,
  x `notin` fv_ee e -> y `notin` (dom E `union` fv_ee e) ->
  typing ((x , bind_typ T1) :: E) P (open_ee e (e_fvar x)) Inf T2 ->
  typing ((y , bind_typ T1) :: E) P (open_ee e (e_fvar y)) Inf T2.
Proof.
  introv Fr1 Fr2 H.
  destruct (x == y).
  -
    subst; eauto.
  -
    assert (J : uniq (((x , bind_typ T1) :: E))).
    forwards* h1: typing_regular H.
    assert (J' : uniq E).
      inversion J; eauto.
    rewrite (@subst_exp_intro x); eauto.
    rewrite_env (nil ++ ((y , bind_typ T1) :: E)).
    forwards* h1: typing_regular H.
    inverts h1 as h1 h2.
    inverts h1 as h1 h3.
    apply typing_subst_simpl_ee with (U := T1);
    simpl_env; auto.
      apply typing_weakening. eauto.
    apply wf_env_typ; eauto.
    assert(uniq (y ~: T1 ++ E)) as h4.
    eauto.
    forwards*: wf_typ_weaken_head h3 h4.
Qed.



Theorem static_stepd_dyn_chk : forall G e e' B P mu mu',
P |== mu ->
  phi_static P ->
  denv_static G ->
  dterm_static e ->
 (* dtyp_static B -> *)
 styping G P e Chk B ->
 step (e, mu) ((r_e e'), mu') ->
 dstep ( e, mu) ( e', mu').
Proof.
 introv wel ps envs es typ red. 
 gen G B P.
 inductions red; intros; eauto;
 try solve[forwards*:dtyp_static_eq  H1];
 try solve[forwards*: dtyp_static_eq H0].
 -
   forwards h0: fill_static es.
   forwards hh1: fill_chk_chk2 typ; auto.
   inverts hh1 as hh1;
   try solve[inverts hh1 as hh1; forwards hhh1: step_not_rv red; auto;
   inverts hhh1; auto].
   inverts hh1 as hh1.
   forwards* hh3: IHred hh1.
Qed.

