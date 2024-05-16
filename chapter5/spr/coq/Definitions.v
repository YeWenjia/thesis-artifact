Require Export Metalib.Metatheory.

(** Syntax **)

Inductive typ : Set :=
  | t_int : typ
  | t_arrow : typ -> typ -> typ
  | t_bvar  : nat -> typ
  | t_fvar  : var -> typ
  | t_all   : typ -> typ
  | t_ref   : typ -> typ
  | t_unit  : typ
.

Inductive exp : Set :=
  | e_bvar   : nat -> exp
  | e_fvar   : var -> exp
  | e_lit    : nat -> exp
  | e_unit   : exp
  | e_anno   : exp -> typ -> exp
  | e_app    : exp -> exp -> exp
  | e_abs    : typ -> exp  -> exp 
  | e_tabs   : exp -> exp 
  | e_tapp   : exp -> typ -> exp
  | e_loc    : nat -> exp
  | e_ref    : exp -> exp
  | e_get    : exp -> exp
  | e_set    : exp -> exp -> exp
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
  | t_bvar J      => if K == J then U else (t_bvar J)
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
  | e_abs A e1   => e_abs (open_tt_rec k f A) (open_te_rec k f e1) 
  | e_anno e1 A    => e_anno (open_te_rec k f e1) (open_tt_rec k f A) 
  | e_tabs e1     => e_tabs (open_te_rec (S k) f e1) 
  | e_tapp e1 A     => e_tapp (open_te_rec k f e1) (open_tt_rec k f A) 
  | e_ref e1     => e_ref (open_te_rec k f e1) 
  | e_get e1     => e_get (open_te_rec k f e1)
  | e_set e1 e2     => e_set (open_te_rec k f e1) (open_te_rec k f e2)
  end.

(** Opening up a expr binder occuring in a expr *)

Fixpoint open_ee_rec (k : nat) (f : exp) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar i       => if k == i then f else (e_bvar i)
  | e_fvar x       => e_fvar x
  | e_loc x      => e_loc x
  | e_lit i        => e_lit i
  | e_unit        => e_unit
  | e_app e1 e2    => e_app (open_ee_rec k f e1) (open_ee_rec k f e2)
  | e_abs A e1   => e_abs A (open_ee_rec (S k) f e1)
  | e_anno e1 A    => e_anno (open_ee_rec k f e1) A 
  | e_tabs e1     => e_tabs (open_ee_rec k f e1) 
  | e_tapp e1 A     => e_tapp (open_ee_rec k f e1) A 
  | e_ref e1     => e_ref (open_ee_rec k f e1) 
  | e_get e1     => e_get (open_ee_rec k f e1)
  | e_set e1 e2     => e_set (open_ee_rec k f e1) (open_ee_rec k f e2)
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
  | type_unit :
      type t_unit
  | type_var : forall X,
      type (t_fvar X)
  | type_arrow : forall T1 T2,
      type T1 ->
      type T2 ->
      type (t_arrow T1 T2)
  | type_all : forall L T2,
      (forall X, X \notin L -> type (T2 open_tt_var X)) ->
      type (t_all T2)
  | type_ref : forall T,
      type T ->
      type (t_ref T)
.

(** exprs as locally closed pre-exprs *)

Inductive expr : exp -> Prop :=
  | expr_var : forall x,
      expr (e_fvar x)
  | expr_nat : forall i,
      expr (e_lit i)
  | expr_unit : 
      expr e_unit
  | expr_abs : forall L e1 A,
      type A ->
      (forall x, x \notin L -> expr (e1 open_ee_var x)) ->
      expr (e_abs A e1)
  | expr_app : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (e_app e1 e2)
  | expr_tabs : forall L e,
      (forall x, x \notin L -> expr (e open_te_var x)) ->
      expr (e_tabs e)
  | expr_tapp : forall e A,
      expr e ->
      type A ->
      expr (e_tapp e A)
  | expr_anno : forall e A,
      expr e ->
      type A ->
      expr (e_anno e A)
  | expr_loc : forall l,
      expr (e_loc l)
  | expr_ref : forall e,
      expr e ->
      expr (e_ref e)
  | expr_get : forall e,
      expr e ->
      expr (e_get e)
  | expr_set : forall e1 e2,
      expr e1 ->
      expr e2 ->
      expr (e_set e1 e2)
.

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

(** eqent *)

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


Definition store_Tlookup (n:nat) (ST: phi) :=
  nth n ST t_unit.



(** Typing *)



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
| typ_app : forall E P e1 e2 A B,
    typing E P e1 Inf (t_arrow A B) ->
    typing E P e2 Chk A ->
    typing E P (e_app e1 e2) Inf B
| typ_abs : forall L E P A B e,
    (forall x, x \notin L ->
            typing (x ~: A ++ E) P (e open_ee_var x) Inf B) ->
    typing E P (e_abs A e) Inf (t_arrow A B)
| typ_anno : forall E P e A,
    typing E P e Chk A ->
    typing E P (e_anno e A) Inf A
| typ_tabs : forall E P e A L,
    ( forall a , a \notin  L  -> 
    typing  ( a ~tvar ++ E) P ( e open_te_var a )  Inf  ( A open_tt_var a )  )  ->
    typing E P (e_tabs e) Inf (t_all A)
| typ_tapp : forall E P e A B,
    wf_typ E A ->
    typing E P e Inf (t_all B) ->
    typing E P (e_tapp e A) Inf  (open_tt B A )
| typ_eq : forall E P e A,
    typing E P e Inf A ->
    typing E P e Chk A
| typ_ref : forall E P e A,
    typing E P e Inf A ->
    typing E P (e_ref e) Inf (t_ref A)
| typ_get : forall E P e A1,
    typing E P e Inf (t_ref A1) ->
    typing E P (e_get e) Inf A1
| typ_set : forall E P e1 e2 A1,
    typing E P e1 Inf (t_ref A1) ->
    typing E P e2 Chk A1->
    typing E P (e_set e1 e2) Inf t_unit
.


Inductive atyping : env -> phi -> exp -> typ -> Prop :=
| atyp_var : forall E P x T,
    wf_env E ->
    binds x (bind_typ T) E ->
    atyping E P (e_fvar x) T
| atyp_nat : forall E P i,
    wf_env E ->
    atyping E P (e_lit i) (t_int)
| atyp_unit : forall E P,
    wf_env E ->
    atyping E P e_unit t_unit
| atyp_loc : forall E P l,
    wf_env E ->
    l < length P ->
    wf_typ E (store_Tlookup l P) ->
    atyping E P (e_loc l) (t_ref (store_Tlookup l P))
| atyp_app : forall E P e1 e2 A B,
    atyping E P e1 (t_arrow A B) ->
    atyping E P e2 A ->
    atyping E P (e_app e1 e2) B
| atyp_abs : forall L E P A B e,
    (forall x, x \notin L ->
            atyping (x ~: A ++ E) P (e open_ee_var x) B) ->
    atyping E P (e_abs A e) (t_arrow A B)
| atyp_anno : forall E P e A,
    atyping E P e A ->
    atyping E P (e_anno e A) A
| atyp_tabs : forall E P e A L,
    ( forall a , a \notin  L  -> 
    atyping  ( a ~tvar ++ E) P ( e open_te_var a )   ( A open_tt_var a )  )  ->
    atyping E P (e_tabs e) (t_all A)
| atyp_tapp : forall E P e A B,
    wf_typ E A ->
    atyping E P e (t_all B) ->
    atyping E P (e_tapp e A)  (open_tt B A )
| atyp_ref : forall E P e A,
    atyping E P e A ->
    atyping E P (e_ref e) (t_ref A)
| atyp_get : forall E P e A1,
    atyping E P e (t_ref A1) ->
    atyping E P (e_get e) A1
| atyp_set : forall E P e1 e2 A1,
    atyping E P e1 (t_ref A1) ->
    atyping E P e2 A1->
    atyping E P (e_set e1 e2) t_unit
.


(* defns FLikes *)
Inductive FL : typ -> Prop :=    (* defn FL *)
 | fl_abs : forall A B, 
   FL (t_arrow A B). 


Fixpoint principle_type (e : exp) : typ :=
match e with 
| (e_anno e A) => A 
| _ => t_unit
end.


Definition store_lookup (n:nat) (st:sto) :=
  nth n st e_unit.


Inductive pvalue : exp -> Prop :=    (* defn ptype *)
| pv_unit : 
    pvalue e_unit
| pv_int : forall (i5:nat),
    pvalue (e_lit i5) 
| pv_arr : forall (A:typ) (e:exp),
    expr (e_abs A e) ->
    pvalue (e_abs A e)
| pv_all : forall (e:exp),
    expr (e_tabs e) ->
    pvalue  (e_tabs e)
| pv_loc : forall l,
    pvalue  (e_loc l).


Inductive value : exp -> Prop :=    (* defn value *)
| v_anno : forall u,
    pvalue u ->
    value u.


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


(* defns Principal *)
Inductive ptype : sto -> exp -> typ -> Prop :=    (* defn ptype *)
| pt_int : forall mu (i5:nat),
    ptype mu (e_lit i5) t_int
| pt_unit : forall mu,
    ptype mu e_unit t_unit
| pt_arr : forall mu (A:typ) (e:exp) (B:typ),
    expr (e_abs A e) ->
    ptype mu ( (e_abs A e ) )  (t_arrow A B)
| pt_loc : forall l A mu,
    principle_type (store_lookup l mu) = A ->
    ptype mu (e_loc l) (t_ref A) 
| pt_anno : forall (u:exp) (A:typ) mu,
    expr u ->
    ptype mu (e_anno u A) A
| pt_all : forall mu (e:exp) (A:typ),
    expr (e_tabs e) ->
    ptype mu (e_tabs e)  (t_all A).


Inductive svalue : exp -> Prop :=   
| sv_arr : forall (A:typ) (e:exp) ,
    expr (e_abs A e) ->
    svalue (e_abs A e)
.

Inductive ssvalue : exp -> Prop :=    (* defn ssvalue *)
| sv_int : forall (i5:nat),
    ssvalue (e_lit i5) 
| sv_all : forall (e:exp),
    expr (e_tabs e) ->
    ssvalue  (e_tabs e)
| sv_loc : forall l,
    ssvalue  (e_loc l)
| sv_unit : 
    ssvalue  (e_unit)
.


Inductive res : Set :=  
 | r_e (e:exp)
 | r_blame.


Definition conf := (exp * sto)%type.
Definition confr := (res * sto)%type.


(* defns TypedReduces *)
Inductive TypedReduce : conf -> typ -> confr -> Prop :=    (* defn TypedReduce *)
 | TReduce_sim : forall mu u A B C,
     pvalue u ->
     ptype mu u C ->
     eq  nil  C B ->
     TypedReduce ((e_anno u A),mu) B ((r_e (e_anno u B)),mu)
 | TReduce_nsim : forall (u:exp) (A B:typ) (C:typ) mu,
      pvalue u ->
     ptype mu u C ->
      not (  eq  nil  C B  )  ->
     TypedReduce ((e_anno u A),mu) B (r_blame,mu)
. 

Definition ltyp : Set := list typ.

(* defns MultiTypedReduces *)
Inductive TypeLists : conf -> ltyp -> confr -> Prop :=    (* defn TypeLists *)
 | TLists_nil : forall v mu,
     TypeLists (v,mu)  nil ((r_e v),mu)
 | TLists_baseb : forall (v:exp) (AA:ltyp) (A:typ) mu,
     TypedReduce (v,mu) A (r_blame,mu) ->
     TypeLists (v,mu)  (cons  A   AA ) (r_blame,mu)
 | TLists_cons : forall (v:exp) (AA:ltyp) (A:typ) (v':exp) r mu,
     TypedReduce (v,mu) A ((r_e v'),mu) ->
     TypeLists (v',mu) AA (r,mu) ->
     TypeLists (v,mu)  (cons A AA ) (r,mu)
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
                    value v ->
                    wellformed (appCtxR v)
     | wf_tappCtx : forall A,
                    type A ->
                    wellformed (tappCtx A)
     | wf_setCtxL : forall e,
                    expr e ->
                    wellformed (setCtxL e)
     | wf_setCtxR : forall e,
                    value e ->
                    wellformed (setCtxR e)
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

(* defns Reduces *)

Inductive step : conf -> conf -> Prop :=    (* defn step *)
 | step_eval : forall mu mu' F e1 e2,
     wellformed F ->
     step (e1, mu) ((e2), mu') ->
     step ((fill F e1), mu) (( (fill F e2)), mu')
  | step_beta : forall (A1:typ) (e:exp)  u mu,
     sto_ok mu ->
     value u ->
     expr (e_abs A1 e ) ->
     step ((e_app  (e_abs A1 e ) u), mu) ((open_ee  e u ), mu)
 | step_annov : forall u A1 mu,
     sto_ok mu ->
     value u ->
     step ((e_anno u A1), mu) (u, mu)
 | step_tap : forall (e:exp) (C:typ) mu,
     expr (e_tabs e) ->
     step ((e_tapp (e_tabs e) C),mu) ((open_te e C ),mu)
 | step_set : forall l mu u,
     sto_ok mu ->
     value u ->
     step (e_set (e_loc l) u , mu) ((e_unit), (replace l u mu))
 | step_new : forall (v:exp) mu,
     sto_ok mu ->
     value v ->
     step ((e_ref v), mu) (( (e_loc (length mu))), (mu ++ v::nil))
 | step_get : forall l mu,
     sto_ok mu ->
     step ((e_get (e_loc l)), mu) ((store_lookup l mu), mu)
.

Inductive extends : phi -> phi -> Prop :=
  | extends_nil : forall ST',
      extends ST' nil  
  | extends_cons : forall x ST' ST,
      extends ST' ST ->
      extends (x::ST') (x::ST).


Hint Constructors  atyping type expr eq wf_typ wf_env typing 
FL ptype pvalue value ssvalue svalue TypedReduce TypeLists 
wellformed step sto_ok extends : core.
