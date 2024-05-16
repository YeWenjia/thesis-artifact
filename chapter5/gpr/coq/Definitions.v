Require Export Metalib.Metatheory.

(** Syntax **)

Definition X : Set := var.
Definition termvar : Set := var.
Definition i : Set := nat.

Inductive typ : Set :=
  | t_int : typ
  | t_arrow : typ -> typ -> typ
  | t_dyn : typ
  | t_bvar  : nat -> typ
  | t_fvar  : var -> typ
  | t_all   : typ -> typ
  | t_ref   : typ -> typ
  | t_unit  : typ
.



Inductive exp : Set :=  (*r expressions *)
 | e_bvar (_:nat) (*r variable *)
 | e_fvar (x:var) (*r variable *)
 | e_unit : exp (*r  *)
 | e_lit (i5:i) (*r lit *)
 | e_abs (e:exp) (*r abstraction *)
 | e_app (e1:exp) (e2:exp) (*r application *)
 | e_ref (e1:exp) (*r  *)
 | e_loc (o:i) (*r  *)
 | e_anno (e:exp) (A:typ) (*r annotation *)
 | e_tabs (e:exp) (*r type abstraction *)
 | e_tapp (e:exp) (A:typ) (*r  *)
 | e_get (e:exp) (*r  *)
 | e_set (e1:exp) (e2:exp) (*r set *)
 | e_val (e:exp) (A:typ) (*r  *) 
 | e_rval (e:exp) 
.

Coercion t_bvar : nat >-> typ.
Coercion t_fvar : atom >-> typ.
Coercion e_bvar : nat >-> exp.
Coercion e_fvar : atom >-> exp.


Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

(** Opening up a type binder occuring in a type *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | t_int         => t_int
  | t_dyn     => t_dyn
  | (t_bvar nat)      => match lt_eq_lt_dec nat K with
                                | inleft (left _) => t_bvar nat
                                | inleft (right _) => U
                                | inright _ => t_bvar (nat - 1)
                            end
  | t_fvar X      => t_fvar X
  | t_arrow T1 T2 => t_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | t_all T       => t_all (open_tt_rec (S K) U T)
  | t_ref T1      => t_ref (open_tt_rec K U T1)
  | t_unit        => t_unit
  end.


Fixpoint open_te_rec (k : nat) (f : typ) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar i       => e_bvar i
  | e_fvar x       => e_fvar x
  | e_lit i        => e_lit i
  | e_unit        => e_unit
  | e_loc x      => e_loc x
  | e_app e1 e2    => e_app (open_te_rec k f e1) (open_te_rec k f e2)
  | e_abs e1   => e_abs  (open_te_rec k f e1) 
  | e_anno e1 A    => e_anno (open_te_rec k f e1) (open_tt_rec k f A) 
  | e_tabs e1     => e_tabs (open_te_rec (S k) f e1)  
  | e_tapp e1 A     => e_tapp (open_te_rec k f e1) (open_tt_rec k f A) 
  | e_ref e1     => e_ref (open_te_rec k f e1) 
  | e_get e1     => e_get (open_te_rec k f e1)
  | e_set e1 e2     => e_set (open_te_rec k f e1) (open_te_rec k f e2)
  | e_val e1 A    => e_val (open_te_rec k f e1) (open_tt_rec k f A) 
  | e_rval e1    => e_rval (open_te_rec k f e1)
  end.

(** Opening up a expr binder occuring in a expr *)

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp) {struct e} : exp :=
  match e with
  | (e_bvar nat) => 
                    match lt_eq_lt_dec nat k with
                        | inleft (left _) => e_bvar nat
                        | inleft (right _) => f
                        | inright _ => e_bvar (nat - 1)
                    end
  | e_fvar x       => e_fvar x
  | e_loc x      => e_loc x
  | e_lit i        => e_lit i
  | e_unit        => e_unit
  | e_app e1 e2    => e_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | e_abs e1   => e_abs (open_ee_rec (S k) f e1)
  | e_anno e1 A    => e_anno (open_ee_rec k f e1) A 
  | e_tabs e1     => e_tabs (open_ee_rec k f e1)
  | e_tapp e1 A     => e_tapp (open_ee_rec k f e1) A 
  | e_ref e1     => e_ref (open_ee_rec k f e1) 
  | e_get e1     => e_get (open_ee_rec k f e1)
  | e_set e1 e2     => e_set (open_ee_rec k f e1) (open_ee_rec k f e2)
  | e_val e1 A    => e_val (open_ee_rec k f e1) A 
  | e_rval e1    => e_rval (open_ee_rec k f e1)
  end.

Definition open_tt T U := open_tt_rec 0 U T.
Definition open_te e T := open_te_rec 0 T e.
Definition open_ee e1 e2 := open_ee_rec 0 e2 e1.

(** Notation for opening up binders with type or expr variables *)

Notation "T 'open_tt_var' X" := (open_tt T (t_fvar X)) (at level 67).

Notation "t 'open_ee_var' x" := (open_ee t (e_fvar x)) (at level 67).

Notation "t 'open_te_var' a" := (open_te t (t_fvar a)) (at level 67).

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_lit :
      type t_int
  | type_dyn :
      type t_dyn
  | type_unit :
      type t_unit
  | type_var : forall X,
      type (t_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (t_arrow T1 T2)
  | type_all : forall T2,
      (forall X, type (T2 open_tt_var X)) ->
      type (t_all T2)
  | type_ref : forall T,
      type T ->
      type (t_ref T)
.


Fixpoint fv_tt (T : typ) {struct T} : atoms :=
  match T with
  | t_int       => {}
  | t_dyn     => {}
  | t_unit     => {}
  | t_bvar J      => {}
  | t_fvar X      => {{ X }}
  | t_arrow T1 T2 => (fv_tt T1) `union` (fv_tt T2)
  | t_all T1      => (fv_tt T1)
  | t_ref T1      => (fv_tt T1)
  end.


Fixpoint subst_tt  (U : typ) (Z : var) (T : typ) {struct T} : typ :=
  match T with
  | t_int         => t_int
  | t_dyn         => t_dyn
  | t_unit         => t_unit
  | t_bvar J      => t_bvar J
  | t_fvar X      => if X == Z then U else (t_fvar X)
  | t_arrow T1 T2 => t_arrow (subst_tt  U Z T1) (subst_tt U Z T2)
  | t_all T1      => t_all (subst_tt U Z T1)
  | t_ref T1      => t_ref (subst_tt U Z T1)
  end.


  Fixpoint fv_te (e : exp) {struct e} : atoms :=
    match e with
    | e_bvar i       => {}
    | e_fvar x       => {}
    | e_lit i        => {}
    | e_unit        => {}
    | e_loc l        => {}
    | e_abs e1   =>  (fv_te e1) 
    | e_app e1 e2    => (fv_te e1) `union` (fv_te e2)
    | e_anno e A     => (fv_te e) `union` (fv_tt A)
    | e_tabs e     => (fv_te e) 
    | e_tapp e A     => (fv_te e) `union` (fv_tt A)
    | e_ref e     => (fv_te e)
    | e_get e     => (fv_te e)
    | e_set e1 e2    => (fv_te e1) `union` (fv_te e2)
    | e_val e A     => (fv_te e) `union` (fv_tt A)
    | e_rval e    => (fv_te e)
    end.
    
    (** Computing free expr variables in a expr *)
    
Fixpoint fv_ee (e : exp) {struct e} : atoms :=
    match e with
    | e_bvar i       => {}
    | e_fvar x       => {{ x }}
    | e_lit i        => {}
    | e_unit        => {}
    | e_loc l        => {}
    | e_abs e1   => (fv_ee e1)
    | e_app e1 e2    => (fv_ee e1) `union` (fv_ee e2)
    | e_anno e A     => (fv_ee e)
    | e_tabs e     => (fv_ee e)
    | e_tapp e A     => (fv_ee e)
    | e_ref e     => (fv_ee e)
    | e_get e     => (fv_ee e)
    | e_set e1 e2    => (fv_ee e1) `union` (fv_ee e2)
    | e_val e A     => (fv_ee e)
    | e_rval e     => (fv_ee e)
    end.
    
    (** Substitution for free type variables in types. *)
    
    
    
Fixpoint subst_te  (u : typ) (z : var) (e : exp) {struct e} : exp :=
    match e with
    | e_bvar i       => e_bvar i
    | e_fvar x       => e_fvar x
    | e_lit i        => e_lit i
    | e_unit         => e_unit
    | e_loc l        => e_loc l
    | e_abs e1   => e_abs (subst_te u z e1)
    | e_app e1 e2    => e_app (subst_te u z e1) (subst_te u z e2)
    | e_anno e A     => e_anno (subst_te u z e) (subst_tt u z A)
    | e_tabs e     => e_tabs (subst_te u z e)
    | e_tapp e A     => e_tapp (subst_te u z e) (subst_tt u z A)
    | e_ref t1    => e_ref (subst_te u z t1)
    | e_get t1    => e_get (subst_te u z t1)
    | e_set t1 t2 => e_set (subst_te u z t1) (subst_te u z t2)
    | e_val e A     => e_val (subst_te u z e) (subst_tt u z  A)
    | e_rval e     => e_rval (subst_te u z e)
    end.

    
    (** Substitution for free expr variables in exprs. *)
    
Fixpoint subst_ee (u : exp) (z : var) (e : exp) {struct e} : exp :=
    match e with
    | e_bvar i       => e_bvar i
    | e_fvar x       => if x == z then u else (e_fvar x)
    | e_lit i        => e_lit i
    | e_unit         => e_unit
    | e_loc l        => e_loc l
    | e_abs e1       => e_abs (subst_ee u z e1)
    | e_app e1 e2    => e_app (subst_ee u z e1) (subst_ee u z e2)
    | e_anno e A     => e_anno (subst_ee u z e) A
    | e_tabs e     => e_tabs (subst_ee u z e)
    | e_tapp e A     => e_tapp (subst_ee u z e) A
    | e_ref t1    => e_ref (subst_ee u z t1)
    | e_get t1    => e_get (subst_ee u z t1)
    | e_set t1 t2 => e_set (subst_ee u z t1) (subst_ee u z t2)
    | e_val e A     => e_val (subst_ee u z e) A
    | e_rval e     => e_rval (subst_ee u z e) 
end.
  

(** exprs as locally closed pre-exprs *)




Inductive expr : exp -> Prop :=    (* defn expr *)
 | lc_e_fvar_f : forall (x:termvar),
     (expr (e_fvar x))
 | lc_e_unit : 
     (expr e_unit)
 | lc_e_lit : forall (i5:i),
     (expr (e_lit i5))
 | lc_e_abs : forall (e:exp),
      ( forall x , expr  ( open_ee e (e_fvar x) )  )  ->
     (expr (e_abs e))
 | lc_e_app : forall (e1 e2:exp),
     (expr e1) ->
     (expr e2) ->
     (expr (e_app e1 e2))
 | lc_e_ref : forall (e1:exp),
     (expr e1) ->
     (expr (e_ref e1))
 | lc_e_loc : forall (o:i),
     (expr (e_loc o))
 | lc_e_anno : forall (e:exp) (A:typ),
     (expr e) ->
     (type A) ->
     (expr (e_anno e A))
 | lc_e_tabs : forall (e:exp),
      ( forall X5 , expr  ( open_te e (t_fvar X5) )  )  ->
     (expr (e_tabs e))
 | lc_e_tapp : forall (e:exp) (A:typ),
     (expr e) ->
     (type A) ->
     (expr (e_tapp e A))
 | lc_e_get : forall (e:exp),
     (expr e) ->
     (expr (e_get e))
 | lc_e_set : forall (e1 e2:exp),
     (expr e1) ->
     (expr e2) ->
     (expr (e_set e1 e2))
 | lc_e_val : forall (e:exp) (A:typ),
     (expr e) ->
     (type A) ->
     (expr (e_val e A))
 | lc_e_rval : forall (e:exp),
     (expr e) ->
     (expr (e_rval e)).

(** Environment is an associative list of bindings. *)

Inductive binding : Set :=
  | bind_tvar : binding 
  | bind_typ : typ -> binding
.

Notation env := (list (atom * binding)).
Notation empty := (@nil (atom * binding)).

Definition sto := list exp.
Definition phi := list typ.

Notation "x ~tvar" := (x ~ bind_tvar)
  (at level 23, left associativity) : env_scope.
Notation "x ~: T" := (x ~ bind_typ T)
  (at level 23, left associativity) : env_scope.


(** A type T is well formed under environment E *)

Inductive wf_typ : env -> typ -> Prop :=
  | wf_typ_int : forall E,
      wf_typ E t_int
  | wf_typ_unit : forall E,
      wf_typ E t_unit
  | wf_typ_dyn : forall E,
      wf_typ E t_dyn
  | wf_typ_var : forall E x,
      binds x bind_tvar E ->
      wf_typ E (t_fvar x)
  | wf_typ_arrow : forall E A1 A2,
      wf_typ E A1 ->
      wf_typ E A2 ->
      wf_typ E (t_arrow A1 A2)
  | wf_typ_all : forall L E A,
      (forall X, X \notin L ->
            wf_typ (X ~tvar ++ E) (A open_tt_var X)) ->
      wf_typ E (t_all A)
  | wf_typ_ref : forall E A,
      wf_typ E A ->
      wf_typ E (t_ref A)
.


Inductive wf_typs : env -> list typ -> Prop :=
 | wts_one: forall E t,
   wf_typ E t ->
   wf_typs E [t] 
 | wts_cons: forall E t ts,
   wf_typ E t ->
   wf_typs E ts ->
   wf_typs E (cons t ts)
.

(** A environment E is well-formed if it contains no duplicate bindings and well-foremd types *)

Inductive wf_env : env -> Prop :=
  | wf_env_empty :
      wf_env empty
  | wf_env_tvar : forall E x,
      wf_env E -> 
      x `notin` dom E -> 
      wf_env (x ~tvar ++ E)
  | wf_env_typ : forall E x A,
      wf_env E ->
      wf_typ E A -> 
      x `notin` dom E -> 
      wf_env (x ~: A ++ E)
.

(** Consistent *)

Inductive consist: env -> typ -> typ -> Prop :=  
  | consist_int : forall E,
      wf_env E ->
      consist E t_int t_int
  | consist_unit : forall E,
      wf_env E ->
      consist E t_unit t_unit
  | consist_var : forall E x,
      wf_env E ->
      wf_typ E (t_fvar x) ->
      consist E (t_fvar x) (t_fvar x)
  | consist_dyn_l : forall E A,
      wf_env E ->
      wf_typ E A ->
      consist E t_dyn A
  | consist_dyn_r : forall E A,
      wf_env E ->
      wf_typ E A ->
      consist E A t_dyn
  | consist_fun : forall E A1 A2 B1 B2,
      consist E B1 A1 ->
      consist E A2 B2 ->
      consist E (t_arrow A1 A2) (t_arrow B1 B2)
  | consist_all: forall L E A B ,
      (forall x, x \notin L ->
      consist (x ~tvar ++ E) (A open_tt_var x) (B open_tt_var x)) ->
      consist E (t_all A) (t_all B)
  | consist_ref : forall E A B,
      consist E A B ->
      consist E (t_ref A) (t_ref B)
.


Definition store_Tlookup (n:nat) (ST: phi) :=
  nth n ST t_unit.



(** Typing *)

Inductive pattern_abs : typ -> typ -> Prop :=    
 | pas_abs : forall A B, 
   pattern_abs (t_arrow A B) (t_arrow A B)
 | pas_dyn : 
   pattern_abs t_dyn (t_arrow t_dyn t_dyn).


Inductive pattern_ref : typ -> typ -> Prop :=    
 | pre_ref : forall A, 
   pattern_ref (t_ref A) (t_ref A)
 | pre_dyn : 
   pattern_ref t_dyn (t_ref t_dyn).


Inductive pattern_all : typ -> typ -> Prop :=    
 | pal_ref : forall B, 
   pattern_all (t_all B) (t_all B)
 | pal_dyn : 
   pattern_all t_dyn (t_all t_dyn).


Inductive tpre : typ -> typ -> Prop :=    
| tp_tvar : forall x,
    tpre (t_fvar x) (t_fvar x)
| tp_i : 
    tpre t_int t_int
| tp_all : forall L A B,
    (forall x, x \notin L ->
            tpre (A open_tt_var x) (B open_tt_var x)) ->
    tpre (t_all A) (t_all B)
| tp_dyn : forall (A:typ),
    type A ->
    tpre A t_dyn
| tp_abs : forall (A B C D:typ),
    tpre A C ->
    tpre B D ->
    tpre (t_arrow A B) (t_arrow C D)
| tp_unit : 
    tpre t_unit t_unit
| tp_ref : forall A B,
    tpre A B ->
    tpre (t_ref A) (t_ref B)
.


Inductive meet : typ -> typ -> typ -> Prop := 
  | me_unit : 
     meet t_unit t_unit t_unit    
  | me_var : forall x,
     meet (t_fvar x) (t_fvar x) (t_fvar x)    
  | me_int : 
     meet t_int t_int t_int 
  | me_arrow : forall A1 B1 A2 B2 A3 B3,
     meet A2 A1 A3 ->
     meet B1 B2 B3 ->
     meet (t_arrow A1 B1) (t_arrow A2 B2) (t_arrow A3 B3)
 | me_dynl : forall A,
     type A ->
     meet A t_dyn A 
 | me_dynr : forall A,
     type A ->
     meet t_dyn A A 
 | me_all: forall L A B C,
      (forall x, x \notin L ->
      meet (A open_tt_var x) (B open_tt_var x) (C open_tt_var x)) ->
      meet (t_all A) (t_all B) (t_all C)
 | me_ref: forall A B C,
      meet A  B C  ->
      meet (t_ref A) (t_ref B) (t_ref C)
.

Fixpoint dynamic_type (e : exp) : typ :=
match e with 
| (e_val e A) => A 
| (e_anno e A) => A 
| e_lit i => t_int 
| e_unit => t_unit 
| _ => t_dyn
end.



Inductive pvalue : exp -> Prop :=    (* defn ptype *)
| pv_unit : 
    pvalue e_unit
| pv_int : forall (i5:nat),
    pvalue (e_lit i5) 
| pv_arr : forall (A:typ) (e:exp) (B:typ) C D,
    expr (e_abs e) ->
    type (t_arrow A B) ->
    type (t_arrow C D) ->
    pvalue (e_anno (e_anno (e_abs e) (t_arrow A B)) (t_arrow C D))
| pv_all : forall (e:exp) A B,
    expr (e_tabs e) ->
    type (t_all A) ->
    type (t_all B) ->
    pvalue  (e_anno (e_anno (e_tabs e) (t_all A)) (t_all B))
| pv_loc : forall l A,
    type (t_ref A) ->
    pvalue  (e_anno (e_loc l) (t_ref A)).

Inductive typing : env -> phi -> exp -> dirflag -> typ -> Prop :=
  | typ_var : forall E P x T,
      wf_env E ->
      binds x (bind_typ T) E ->
      typing E P (e_fvar x) Inf T
  | typ_nat : forall E P i,
      wf_env E ->
      typing E P (e_lit i) Inf (t_int)
  | typ_unit : forall E P,
      wf_env E ->
      typing E P e_unit Inf t_unit
  | typ_loc : forall E P l,
       wf_env E ->
      l < length P ->
      wf_typ E (store_Tlookup l P) ->
      typing E P (e_loc l) Inf (t_ref (store_Tlookup l P))
  | typ_app : forall E P e1 e2 A1 A B,
      pattern_abs A1 (t_arrow A B) ->
      typing E P e1 Inf A1 ->
      typing E P e2 Chk A ->
      typing E P (e_app e1 e2) Inf B
  | typ_abs : forall L E P A A1 A2 e,
      (forall x, x \notin L ->
            typing (x ~ bind_typ A1 ++ E) P (e open_ee_var x) Chk A2) ->
      pattern_abs A (t_arrow A1 A2) ->
      typing E P (e_abs e) Chk A
  | typ_anno : forall E P e A,
     typing E P e Chk A ->
     typing E P (e_anno e A) Inf A
  | typ_tabs : forall L E P e A A1 ,
      ( forall a , a \notin  L  -> 
      typing  ( a ~tvar ++ E) P ( e open_te_var a )  Chk  ( A1 open_tt_var a )  )  ->
      pattern_all A (t_all A1) ->
     typing E P (e_tabs e) Chk A
  | typ_tapp : forall E P e A A1 B,
      wf_typ E A ->
     pattern_all A1 (t_all B) ->
     typing E P e Inf A1 ->
     typing E P (e_tapp e A) Inf  (open_tt B A )
  | typ_consist : forall E P e B A,
     consist E A B ->
     typing E P e Inf A ->
     typing E P e Chk B
  | typ_ref : forall E P e A,
     typing E P e Inf A ->
     typing E P (e_ref e) Inf (t_ref A)
  | typ_get : forall E P e A A1,
     pattern_ref A (t_ref A1) ->
     typing E P e Inf A ->
     typing E P (e_get e) Inf A1
  | typ_set : forall E P e1 e2 A A1,
     pattern_ref A (t_ref A1) ->
     typing E P e1 Inf A ->
     typing E P e2 Chk A1->
     typing E P (e_set e1 e2) Inf t_unit
  | typ_rt : forall E P (p:exp) A,
     wf_env E ->
     pvalue p ->
     typing nil P p Chk A ->
     tpre (dynamic_type p) A -> 
     typing E P (e_val p A) Inf A
  | typ_absv : forall L G P  (e e2:exp) A B,
     ( forall x , x \notin  L  -> 
     typing  (x ~ bind_typ A ++ G ) P (e open_ee_var x)  Chk B )  ->
     typing G P e2 Inf A ->
     typing G P (e_app (e_abs e) e2) Chk B
  | typ_rts : forall E P e2 l,
     l < length P ->
     typing E P e2 Inf (store_Tlookup l P) ->
     typing E P (e_set (e_rval (e_loc l)) e2) Inf t_unit
.



Definition store_lookup (n:nat) (st:sto) :=
  nth n st e_unit.



Inductive value : exp -> Prop :=    (* defn value *)
| v_anno : forall u A,
    pvalue u ->
    type A ->
    value (e_val u A).


Inductive sto_ok : sto -> Prop :=
  | sto_ok_empty : sto_ok nil
  | sto_ok_push : forall mu t,
      sto_ok mu -> value t -> 
      sto_ok (t :: mu).

Definition sto_typing P mu :=
     sto_ok mu /\
     length P = length mu /\
     (forall l, l < length mu -> 
      typing empty P (store_lookup l mu) Inf (store_Tlookup l P)).

Notation "P |== mu" := (sto_typing P mu) (at level 68).




Inductive res : Set :=  
 | r_e (e:exp)
 | r_blame.


Definition conf := (exp * sto)%type.
Definition confr := (res * sto)%type.



(* defns Casts *)
Inductive Cast : conf -> typ -> res -> Prop :=    (* defn Cast *)
 | Cast_lit : forall i (A:typ) (B:typ) mu,
     Cast ((e_lit i), mu)  A  (r_e (e_lit i))
 | Cast_unit : forall (A:typ) mu,
     Cast (e_unit, mu)  A  (r_e (e_unit))
 | Cast_abs : forall e A B C D mu, 
    consist nil (t_arrow A B) D ->
    Cast ((e_anno (e_anno (e_abs e) (t_arrow A B)) C), mu) D  (r_e (e_anno (e_anno (e_abs e) (t_arrow A B)) D))
 | Cast_absp : forall e A B C D mu, 
    not(consist nil (t_arrow A B) D) ->
    Cast ((e_anno (e_anno (e_abs e) (t_arrow A B)) C), mu) D  r_blame
 | Cast_tabs : forall e A B C mu, 
    consist nil (t_all A) C ->
    Cast ((e_anno (e_anno (e_tabs e) (t_all A)) B), mu) C (r_e (e_anno (e_anno (e_tabs e) (t_all A)) C))
 | Cast_tabsp : forall e A B C mu, 
    not(consist nil (t_all A) C) ->
    Cast ((e_anno (e_anno (e_tabs e) (t_all A)) B), mu) C  r_blame
 | Cast_loc : forall o A B mu, 
    consist nil (t_ref (dynamic_type (store_lookup o mu))) B ->
    Cast ((e_anno (e_loc o) A), mu) B  (r_e (e_anno (e_loc o) B))
 | Cast_locp : forall o A B mu, 
    not(consist nil (t_ref (dynamic_type (store_lookup o mu))) B) ->
    Cast ((e_anno (e_loc o) A), mu) B  r_blame
. 

Definition ltyp : Set := list typ.



Inductive Castv : conf -> typ -> res -> Prop :=    (* defn Casts *)
 | Castv_one : forall mu p A B C p',
     Cast (p, mu) B (r_e p') -> 
     meet (dynamic_type p) C B -> 
     Castv ((e_val p A),mu) C (r_e (e_val p' C))
 | Castv_onefail : forall mu p A B C,
     Cast (p, mu) B r_blame -> 
     meet (dynamic_type p) C B -> 
     Castv ((e_val p A),mu) C r_blame
 | Castv_onenot : forall mu p A C,
     not(consist nil (dynamic_type p) C) -> 
     Castv ((e_val p A),mu) C r_blame
.



Inductive ctx_item : Type :=
  | appCtxL : exp -> ctx_item
  | appCtxR : exp -> ctx_item
  | tappCtx : typ -> ctx_item
  | refCtx :  ctx_item
  | getCtx : ctx_item
  | setCtxL : exp -> ctx_item 
  | setCtxR : exp -> ctx_item 
  | annoCtx : typ -> ctx_item
.

Inductive wellformed : ctx_item -> Prop :=
     | wf_appCtxL : forall (e : exp),
                    expr e ->
                    wellformed (appCtxL e)
     | wf_appCtxR : forall (v : exp),
                    wellformed (appCtxR (e_abs v))
     | wf_tappCtx : forall A,
                    type A ->
                    wellformed (tappCtx A)
     | wf_setCtxL : forall e,
                    expr e ->
                    wellformed (setCtxL e)
     | wf_setCtxR : forall l,
                    wellformed (setCtxR (e_rval (e_loc l)))
     | wf_refCtx : 
                    wellformed refCtx
     | wf_getCtx : 
                    wellformed getCtx
     | wf_annoCtx : forall A,
                    type A ->
                    wellformed (annoCtx A)
.


Definition fill (E : ctx_item) (e : exp) : exp :=
     match E with
     | appCtxL e2 => e_app e e2
     | appCtxR v1 => e_app v1 e
     | tappCtx A => e_tapp e A
     | setCtxL e2 => e_set e e2
     | setCtxR v1 => e_set v1 e
     | refCtx => e_ref e
     | getCtx => e_get e
     | annoCtx A => e_anno e A
     end.


Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil => nil
  | h :: t =>
    match n with
    | O => x :: t
    | S n' => h :: replace n' x t
    end
  end.


Inductive ires : exp -> Prop := 
 | ires_f : forall e, 
   ires (e_abs e)
 | ires_t : forall e, 
   ires (e_tabs e).
 (* | ires_l : forall l,
   ires (e_loc l). *)


(* defns Reduces *)
Inductive step : conf -> confr -> Prop :=    (* defn step *)
 | step_eval : forall mu mu' F e1 e2,
     wellformed F ->
     step (e1, mu) ((r_e e2), mu') ->
     step ((fill F e1), mu) ((r_e (fill F e2)), mu')
  | step_blame : forall F e mu mu',
     wellformed F ->
     step (e, mu) (r_blame, mu') ->
     step ((fill F e), mu) (r_blame, mu')
  | step_beta : forall e v mu,
     sto_ok mu ->
     expr (e_abs e) ->
     value v ->
     step ((e_app (e_abs e)  v), mu) ((r_e (open_ee  e v)), mu)
  | step_app : forall A1 A2 B1 B2 C C1 C2 e v mu,
     sto_ok mu ->
     expr (e_abs e) ->
     pattern_abs C  (t_arrow C1 C2) ->
     step ((e_app (e_val  (e_anno (e_anno (e_abs e) (t_arrow A1 A2)) (t_arrow B1 B2))  C)  v), mu) ((r_e (e_anno (e_anno (e_anno  (e_app (e_abs e) (e_anno (e_anno (e_anno v C1) B1) A1) )  A2) B2) C2)), mu)
 | step_dynabs : forall p v mu,
     sto_ok mu ->
     not (consist nil (dynamic_type p) (t_arrow t_dyn t_dyn)) ->
     pvalue p ->
     step ((e_app ((e_val p t_dyn)) v), mu) (r_blame, mu)
 | step_annov : forall (v:exp) (A:typ) r mu,
     sto_ok mu ->
     value v ->
     Castv (v, mu) A r ->
     step ((e_anno v A), mu) (r, mu)
 | step_abs : forall e A0 A B mu,
      expr (e_abs e) ->
      pattern_abs A0  (t_arrow A B) ->
      step ((e_anno (e_abs e) A0), mu) ((r_e (e_val (e_anno (e_anno (e_abs e) (t_arrow A B)) (t_arrow A B)) A0)), mu)
 | step_tabs : forall e A0 A mu,
      expr (e_tabs e) ->
      pattern_all A0  (t_all A) ->
      step ((e_anno (e_tabs e) A0), mu) ((r_e (e_val (e_anno (e_anno (e_tabs e) (t_all A )) (t_all A )) A0)), mu)
 | step_lit : forall i mu,
      step ((e_lit i), mu) ((r_e (e_val (e_lit i) t_int)), mu)
 | step_unit : forall mu,
      step ((e_unit), mu) ((r_e (e_val (e_unit) t_unit)), mu)
 | step_loc : forall mu o A B,
      pattern_ref A B ->
      step ((e_loc o), mu) ((r_e (e_val (e_anno (e_loc o) (t_ref (dynamic_type (store_lookup o mu)))) (t_ref (dynamic_type (store_lookup o mu)))) ), mu)
 | step_tapp : forall (e:exp) A A1 A2 A3 B mu,
     expr (e_tabs e) ->
     pattern_all A (t_all A3) ->
     step ((e_tapp (e_val (e_anno  (e_anno (e_tabs e) (t_all A1)) (t_all A2)) A) B),mu) ((r_e (e_anno (e_anno (e_anno (open_te  e B ) (open_tt  A1 B )) (open_tt  A2 B)) (open_tt  A3 B))),mu)
 | step_dynfor : forall (u:exp) B mu,
     type B ->
     pvalue u ->
     not (consist nil (dynamic_type u) (t_all t_dyn)) ->
     step ((e_tapp  (e_val u t_dyn)  B),mu) (r_blame,mu)
 | step_setv : forall l v2 mu,
     sto_ok mu ->
     value v2 ->
     step ((e_set (e_rval (e_loc l)) v2), mu) ((r_e e_unit), replace l v2 mu)
 | step_set : forall l A1 A A2 v2 mu,
     sto_ok mu ->
     pattern_ref A (t_ref A2) ->
     step ((e_set (e_val (e_anno (e_loc l) (t_ref A1)) A) v2), mu) ((r_e (e_set (e_rval (e_loc l)) (e_anno (e_anno (e_anno v2 A2) A1) (dynamic_type (store_lookup l mu)) ))), mu)
 | step_dynset : forall u v2 mu,
     sto_ok mu ->
     pvalue u ->
     not (consist nil (dynamic_type u) (t_ref t_dyn)) ->
     step ((e_set (e_val u t_dyn) v2), mu) (r_blame, mu)
 | step_new : forall (v:exp) mu,
     sto_ok mu ->
     value v ->
     step ((e_ref v), mu) ((r_e (e_loc (length mu))), (mu ++ v::nil))
 | step_get : forall l A C B mu,
     sto_ok mu ->
     pattern_ref C (t_ref B) ->
     step ((e_get (e_val (e_anno (e_loc l) (t_ref A)) C)), mu) ((r_e (e_anno (e_anno (store_lookup l mu) A) B)), mu)
 | step_getd : forall u mu,
     sto_ok mu ->
     pvalue u ->
     not (consist nil (dynamic_type u) (t_ref t_dyn)) ->
     step ((e_get (e_val u t_dyn)), mu) (r_blame,mu)
.

Inductive extends : phi -> phi -> Prop :=
  | extends_nil : forall ST',
      extends ST' nil  
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).



Hint Constructors wf_typs ires tpre pattern_abs pattern_all pattern_ref type expr consist wf_typ wf_env typing meet pvalue value Cast Castv
wellformed step sto_ok extends : core.
