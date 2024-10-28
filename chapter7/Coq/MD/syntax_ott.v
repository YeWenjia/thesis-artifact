(* !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! *)
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
(** syntax *)
Definition i : Set := nat.



Inductive typ : Set :=  (*r types *)
 | t_int : typ (*r int *)
 | t_top : typ (*r top *)
 | t_bot : typ (*r bot *)
 | t_arrow (A:typ) (B:typ) (*r function types *)
 | t_and (A:typ) (B:typ) (*r intersection *)
 | t_dyn : typ (*r dynamic type *)
 | t_rcd (l:var) (A:typ) (*r record *).

(** This uses the locally nameless representation for terms and cofinite quantification in typing judgements. *)
Inductive exp : Set :=  (*r expressions *)
 | e_var_b (_:nat) (*r variables *)
 | e_var_f (x:var) (*r variables *)
 | e_top : exp (*r top *)
 | e_lit (i5:i) (*r lit *)
 | e_abs  (e:exp) (*r abstractions *)
 | e_app (e1:exp) (e2:exp) (*r applications *)
 | e_merge (e1:exp) (e2:exp) (*r merge *)
 | e_anno (e:exp) (A:typ) (*r annotation *)
 | e_rcd (l:var) (e:exp) (*r record *)
 | e_proj (e:exp) (l:var) (*r projection *)
 | e_fixpoint (e:exp).
 (* | e_value (e:exp) (A:typ). *)
 
 
Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.
 (* | Chkv : dirflag. *)

Definition ctx : Set := list ( atom * typ ).

Inductive st : Set :=  (*r input type or projection label *)
 | st_ty (A:typ).

Inductive tlist : Set :=  (*r list type *)
 | lt_empty : tlist
 | lt_consl (AA:tlist) (A:typ).

Definition ls : Set := list st.

(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => e_var_b nat
        | inleft (right _) => e_5
        | inright _ => e_var_b (nat - 1)
      end
  | (e_var_f x) => e_var_f x
  | e_top => e_top 
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (open_exp_wrt_exp_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_merge e1 e2) => e_merge (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_anno e A) => e_anno (open_exp_wrt_exp_rec k e_5 e) A
  | (e_rcd l e) => e_rcd l (open_exp_wrt_exp_rec k e_5 e)
  | (e_proj e l) => e_proj (open_exp_wrt_exp_rec k e_5 e) l
  (* | (e_value e A) => e_value (open_exp_wrt_exp_rec k e_5 e) A *)
  | (e_fixpoint e) => e_fixpoint (open_exp_wrt_exp_rec (S k) e_5 e)
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_top : 
     (lc_exp e_top)
 | lc_e_lit : forall (i5:i),
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (e:exp),
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs e))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_merge : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_merge e1 e2))
 | lc_e_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_anno e A))
 (* | lc_e_value : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_value e A)) *)
 | lc_e_rcd : forall l (e:exp),
     (lc_exp e) ->
     (lc_exp (e_rcd l e))
 | lc_e_proj : forall (e:exp) l,
     (lc_exp e) ->
     (lc_exp (e_proj e l))
 | lc_e_fixpoint : forall (e:exp),
     ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
    (lc_exp (e_fixpoint e))
.

     
(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | e_top => {}
  | (e_lit i5) => {}
  | (e_abs e) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_merge e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_anno e A) => (fv_exp e)
  (* | (e_value e A) => (fv_exp e) *)
  | (e_rcd l e) => (fv_exp e)
  | (e_proj e l) => (fv_exp e)
  | (e_fixpoint e) => (fv_exp e)
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | e_top => e_top 
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (subst_exp e_5 x5 e)
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_merge e1 e2) => e_merge (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_anno e A) => e_anno (subst_exp e_5 x5 e) A
  | (e_rcd l e) => e_rcd l (subst_exp e_5 x5 e)
  | (e_proj e l) => e_proj (subst_exp e_5 x5 e) l
  (* | (e_value e A) => e_value (subst_exp e_5 x5 e) A *)
  | (e_fixpoint e) => e_fixpoint (subst_exp e_5 x5 e)
end.


(* principal types for values*)
Fixpoint principal_type (v:exp) : typ :=
  match v with
  | e_top => t_top
  | (e_lit i5) => t_int
  | (e_anno e A) => A
  | (e_merge v1 v2) => t_and (principal_type v1) (principal_type v2)
  | (e_rcd l e) => (t_rcd l (principal_type e))
  | _ => t_dyn
  end.
  

(** definitions *)

(* defns sValues *)
Inductive fvalue : exp -> Prop :=    (* defn svalue *)
 | fval_abs : forall (e:exp) A B,
     lc_exp (e_abs e) ->
     fvalue  (e_anno (e_abs e) (t_arrow A B))
 | fval_vabs: forall f A B,
     fvalue f -> 
     fvalue (e_anno f (t_arrow A B)).



Inductive dynamic : typ -> Prop :=    (* defn static *)
 | dyn_d : 
     dynamic t_dyn
 | dyn_andl : forall A B,
     dynamic A -> 
     dynamic (t_and A B)
 | dyn_andr :forall A B,
     dynamic B -> 
     dynamic (t_and A B).

Inductive ddyn : typ -> Prop :=    (* defn static *)
 | dd_d : 
     ddyn t_dyn
 | dd_andl : forall A B,
     ddyn A -> 
     ddyn (t_and A B)
 | dd_andr :forall A B,
     ddyn B -> 
     ddyn (t_and A B).


Inductive botLike : typ -> Prop :=    (* defn static *)
 | btl_bot : 
     botLike t_bot
 | btl_andl : forall A B,
     botLike A -> 
     botLike (t_and A B)
 | btl_andr :forall A B,
     botLike B -> 
     botLike (t_and A B)
 | btl_rcd : forall l A,
     botLike A ->
     botLike (t_rcd l A).


(* defns pValues *)
Inductive pvalue : exp -> Prop :=    (* defn pvalue *)
| pval_i : forall i,
    pvalue (e_lit i)
| pval_t : 
    pvalue e_top
| pval_f : forall f,
    fvalue f ->
    pvalue f
| pval_merge : forall (e1 e2:exp),
    pvalue e1 ->
    pvalue e2 ->
    pvalue (e_merge e1 e2)
| pval_rcd : forall l (e:exp),
    pvalue e ->
    pvalue (e_rcd l e).



(* defns TopLikeType *)
Inductive topLike : typ -> Prop :=    (* defn topLike *)
 | TL_top : 
     topLike t_top
 | TL_dyn : 
     topLike t_dyn
 | TL_and : forall (A B:typ),
     topLike A ->
     topLike B ->
     topLike (t_and A B).





Inductive Value : exp -> Prop :=    (* defn pvalue *)
| Val_u : forall u,
    Uvalue u ->
    Value u
| Val_ud : forall u, 
    Uvalue u ->
    Value (e_anno u t_dyn) 
with Uvalue : exp -> Prop :=    
| Uval_i : forall i,
    Uvalue (e_lit i)
| Uval_t : 
    Uvalue e_top
| Uval_f : forall f,
    fvalue f ->
    Uvalue f
| Uval_merge : forall (e1 e2:exp),
    Value e1 ->
    Value e2 ->
    Uvalue (e_merge e1 e2)
| Uval_rcd : forall l (e:exp),
    Value e ->
    Uvalue (e_rcd l e)
.

(* Check Value_ind. *)

Inductive Ground: typ -> Prop :=    
| Ground_int : 
    Ground t_int
| Ground_top : 
   Ground t_top
| Ground_arr : 
    Ground (t_arrow t_dyn t_dyn)
| Ground_merge : 
    Ground (t_and t_dyn t_dyn)
| Ground_rcd : forall l, 
    Ground (t_rcd l t_dyn).


Inductive gvalue : exp -> Prop :=    (* defn pvalue *)
| gval_i : forall i,
    gvalue (e_lit i)
| gval_t : 
    gvalue e_top
| gval_abs : forall (e:exp),
     lc_exp (e_abs e) ->
     gvalue (e_anno (e_abs e) (t_arrow t_dyn t_dyn))
| gval_f : forall f,
    fvalue f ->
    gvalue (e_anno f (t_arrow t_dyn t_dyn))
| gval_merge : forall (e1 e2:exp),
    gvalue e1 ->
    gvalue e2 ->
    gvalue (e_merge (e_anno e1 t_dyn) (e_anno e2 t_dyn))
| gval_rcd : forall l (e:exp),
    gvalue e ->
    gvalue (e_rcd l (e_anno e t_dyn))
.


Inductive value : exp -> Prop :=    (* defn pvalue *)
| val_i : forall i,
    value (e_lit i)
| val_t : 
    value e_top
| val_f : forall f,
    fvalue f ->
    value f
| val_merge : forall (e1 e2:exp),
    value e1 ->
    value e2 ->
    value (e_merge e1 e2)
| val_rcd : forall l (e:exp),
    value e ->
    value (e_rcd l e)
| val_g : forall g,
    (* value g ->
    Ground (principal_type g) -> *)
    gvalue g ->
    value (e_anno g t_dyn)
.


Inductive svalue : exp -> Prop :=    
| sval_i : forall i,
    svalue (e_lit i)
| sval_t : 
    svalue e_top
| sval_f : forall f,
    fvalue f ->
    svalue f
| sval_rcd : forall l (e:exp),
    value e ->
    svalue (e_rcd l e).

Inductive uvalue : exp -> Prop :=    
| uval_i : forall i,
    uvalue (e_lit i)
| uval_t : 
    uvalue e_top
| uval_f : forall f,
    fvalue f ->
    uvalue f
| uval_merge : forall (e1 e2:exp),
    value e1 ->
    value e2 ->
    uvalue (e_merge e1 e2)
| uval_rcd : forall l (e:exp),
    value e ->
    uvalue (e_rcd l e).


(* defns statics *)
Inductive static : typ -> Prop :=    (* defn static *)
 | static_bot : 
     static t_bot
 | static_top : 
     static t_top
 | static_int : 
     static t_int
 | static_arrow : forall (A B:typ),
     static A ->
     static B ->
     static (t_arrow A B)
 | static_merge : forall (A B:typ),
     static A ->
     static B ->
     static (t_and A B)
 | static_rcd : forall l (A:typ),
     static A ->
     static (t_rcd l A).


(* defns OrdinaryType *)
Inductive ord : typ -> Prop :=    (* defn ord *)
| O_int : 
    ord t_int
| O_arrow : forall (A B:typ),
    ord (t_arrow A B)
| O_rcd : forall l (A:typ),
    ord (t_rcd l A).

Inductive oord : typ -> Prop :=    (* defn ord *)
| oO_top : 
    oord t_top
| oO_int : 
    oord t_int
| oO_arrow : forall (A B:typ),
    oord (t_arrow A B)
| oO_rcd : forall l (A:typ),
    oord (t_rcd l A).

(* defns Disjoint *)
Inductive disjoint : typ -> typ -> Prop :=    (* defn disjoint *)
 | D_topL : forall B,
     disjoint t_top B
 | D_topR : forall (A:typ),
     disjoint A t_top
 | D_dynL : forall B,
     disjoint t_dyn B
 | D_dynR : forall (A:typ),
     disjoint A t_dyn
 | D_andL : forall (A1 A2 B:typ),
     disjoint A1 B ->
     disjoint A2 B ->
     disjoint (t_and A1 A2) B
 | D_andR : forall (A B1 B2:typ),
     disjoint A B1 ->
     disjoint A B2 ->
     disjoint A (t_and B1 B2)
 | D_intArr : forall (A1 A2:typ),
     disjoint t_int (t_arrow A1 A2)
 | D_arrInt : forall (A1 A2:typ),
     disjoint (t_arrow A1 A2) t_int
 | D_rcdNeq : forall l1 (A:typ) l2 (B:typ),
      l1  <>  l2  ->
     disjoint (t_rcd l1 A) (t_rcd l2 B)
 | D_IntRcd : forall l (A:typ),
     disjoint t_int (t_rcd l A)
 | D_RcdInt : forall l (A:typ),
     disjoint (t_rcd l A) t_int
 | D_ArrRcd : forall (A1 A2:typ) l (A:typ),
     disjoint (t_arrow A1 A2) (t_rcd l A)
 | D_RcdArr : forall l (A A1 A2:typ),
     disjoint (t_rcd l A) (t_arrow A1 A2).


Inductive well : typ -> Prop :=    (* defn *)
 | wl_top : 
     well t_top
 | wl_int : 
     well t_int
 | wl_dyn : 
     well t_dyn
 | wl_arr : forall (A B:typ),
     well A ->
     well B -> 
     well (t_arrow A B)
 | wl_merge : forall (A B:typ),
     well A ->
     well B ->
     disjoint A B ->
     well (t_and A B)
 | wl_rcd : forall l (A:typ),
     well A ->
     well (t_rcd l A).

(* defns Subtyping *)
Inductive sub : typ -> typ -> Prop :=    (* defn sub *)
 | S_z : 
     sub t_int t_int
 | S_bot : forall (A:typ),
     sub t_bot A
 | S_top : forall (A:typ),
     static A ->
     sub A t_top
 | S_arr : forall (A1 A2 B1 B2:typ),
     sub B1 A1 ->
     sub A2 B2 ->
     sub (t_arrow A1 A2) (t_arrow B1 B2)
 | S_andl1 : forall (A1 A2 A3:typ),
     sub A1 A3 ->
     sub (t_and A1 A2) A3
 | S_andl2 : forall (A1 A2 A3:typ),
     sub A2 A3 ->
     sub (t_and A1 A2) A3
 | S_andr : forall (A1 A2 A3:typ),
     sub A1 A2 ->
     sub A1 A3 ->
     sub A1 (t_and A2 A3)
 | S_dyn : 
     sub t_dyn t_dyn
 | S_rcd : forall l (C D:typ),
     sub C D ->
     sub (t_rcd l C) (t_rcd l D).


(* defns CSubtyping *)
Inductive csub : typ -> typ -> Prop :=    (* defn csub *)
 | CS_z : 
     csub t_int t_int
 | CS_dynl : forall (A:typ),
     csub t_dyn A
 | CS_dynr : forall (A:typ),
     csub A t_dyn
 | CS_bot : forall A,
     csub t_bot A
 | CS_top : forall (A:typ),
     csub A t_top
 | CS_arr : forall (A1 A2 B1 B2:typ),
     csub B1 A1 ->
     csub A2 B2 ->
     csub (t_arrow A1 A2) (t_arrow B1 B2)
 | CS_andl1 : forall (A1 A2 A3:typ),
     csub A1 A3 ->
     csub (t_and A1 A2) A3
 | CS_andl2 : forall (A1 A2 A3:typ),
     csub A2 A3 ->
     csub (t_and A1 A2) A3
 | CS_andr : forall (A1 A2 A3:typ),
     csub A1 A2 ->
     csub A1 A3 ->
     csub A1 (t_and A2 A3)
 | CS_rcd : forall l (C D:typ),
     csub C D ->
     csub (t_rcd l C) (t_rcd l D).

(* defns Consistency *)
Inductive sim : typ -> typ -> Prop :=    (* defn sim *)
 | sim_i : 
     sim t_int t_int
 | sim_bot : 
     sim t_bot t_bot
 | sim_top : 
     sim t_top t_top
 | sim_arr : forall (A B C D:typ),
     sim A C ->
     sim B D ->
     sim (t_arrow A B) (t_arrow C D)
 | sim_dynl : forall (A:typ),
     sim t_dyn A
 | sim_dynr : forall (A:typ),
     sim A t_dyn
 | sim_merge : forall (A B C D:typ),
     sim A C ->
     sim B D ->
     sim (t_and A B) (t_and C D)
 | sim_rcd : forall l (C D:typ),
     sim C D ->
     sim (t_rcd l C) (t_rcd l D).

Inductive ctx_item : Type :=
     | annoCtx : typ -> ctx_item
     | appCtxL : exp -> ctx_item
     | appCtxR : exp -> ctx_item
     | mergeCtxL : exp -> ctx_item
     | mergeCtxR : exp -> ctx_item
     | rcdCtx : var ->  ctx_item
     | prjCtx : var ->  ctx_item.

Inductive wellformed : ctx_item -> Prop :=
     | wf_appCtxL : forall (e : exp),
                    lc_exp e ->
                    wellformed (appCtxL e)
     | wf_appCtxR : forall (e : exp),
                    lc_exp (e_abs e) ->
                    wellformed (appCtxR (e_abs e))
    | wf_mergeCtxL : forall (e : exp),
                    lc_exp e ->
                    wellformed (mergeCtxL e)
     | wf_mergeCtxR : forall (v : exp),
                    value v ->
                    wellformed (mergeCtxR v)
     | wf_rcdCtx : forall l,
                    wellformed (rcdCtx l)
     | wf_prjCtx : forall l,
                    wellformed (prjCtx l)
     | wf_annoCtx : forall A,
                    wellformed (annoCtx A).


Inductive ctx_itemn : Type :=
     | nannoCtx : typ -> ctx_itemn
     | nappCtxL : exp -> ctx_itemn
     | nmergeCtxL : exp -> ctx_itemn
     | nmergeCtxR : exp -> ctx_itemn
     | nrcdCtx : var ->  ctx_itemn
     | nprjCtx : var ->  ctx_itemn.

Inductive wellformedn : ctx_itemn -> Prop :=
     | wfn_appCtxL : forall (e : exp),
                    lc_exp e ->
                    wellformedn (nappCtxL e)
    | wfn_mergeCtxL : forall (e : exp),
                    lc_exp e ->
                    wellformedn (nmergeCtxL e)
     | wfn_mergeCtxR : forall (v : exp),
                    value v ->
                    wellformedn (nmergeCtxR v)
     | wfn_rcdCtx : forall l,
                    wellformedn (nrcdCtx l)
     | wfn_prjCtx : forall l,
                    wellformedn (nprjCtx l)
     | wfn_annoCtx : forall A,
                    wellformedn (nannoCtx A).

Definition filln (E : ctx_itemn) (e : exp) : exp :=
     match E with
     | nappCtxL e2 => e_app e e2
     | nmergeCtxL e2 => e_merge e e2
     | nmergeCtxR v1 => e_merge v1 e
     | nrcdCtx l => e_rcd l e  
     | nprjCtx l => e_proj e l  
     | nannoCtx A => e_anno e A  
     end.


Definition fill (E : ctx_item) (e : exp) : exp :=
     match E with
     | appCtxL e2 => e_app e e2
     | appCtxR v1 => e_app v1 e
     | mergeCtxL e2 => e_merge e e2
     | mergeCtxR v1 => e_merge v1 e
     | rcdCtx l => e_rcd l e  
     | prjCtx l => e_proj e l  
     | annoCtx A => e_anno e A  
     end.


Inductive err : Type :=
     | err_b : err
     | err_a : err.


Inductive res : Type :=
     | r_e  : exp -> res
     | r_blame : err -> res.

Inductive typin : typ -> typ -> Prop :=
| ti_int:
  typin t_int t_int
| ti_bot:
  typin t_bot t_bot
| ti_top: forall A,
  typin t_top A
| ti_arr: forall A B,
  typin (t_arrow A B) (t_arrow A B)
| ti_and: forall A B C,
  typin A C ->
  typin B C ->
  typin (t_and A B) C
| ti_andl: forall A B C,
  typin A B ->
  typin A (t_and B C)
| ti_andr: forall A B C,
  typin A C ->
  typin A (t_and B C)
| ti_rcd: forall A B l,
  typin A B ->
  typin (t_rcd l A) (t_rcd l B).


(* defns type precision *)
Inductive tpre : typ -> typ -> Prop :=    
| tp_bot : 
    tpre t_bot t_bot
| tp_top : 
    tpre t_top t_top
| tp_i : 
    tpre t_int t_int
| tp_dyn : forall (A:typ),
    tpre A t_dyn
| tp_abs : forall (A B C D:typ),
    tpre A C ->
    tpre B D ->
    tpre (t_arrow A B) (t_arrow C D)
| tp_and : forall (A B C D:typ),
    tpre A C ->
    tpre B D ->
    tpre (t_and A B) (t_and C D)
| tp_rcd : forall l (A B:typ),
    tpre A B ->
    tpre (t_rcd l A) (t_rcd l B).




(* defns SplitType *)
Inductive spl : typ -> typ -> typ -> Prop :=    (* defn spl *)
 | Sp_and : forall (A B:typ),
     spl  (t_and A B)  A  B.


Fixpoint const (A : typ) : typ := 
    match A with 
    | (t_arrow A1 A2) => (t_arrow t_dyn t_dyn)
    | (t_rcd l A1) => (t_rcd l t_dyn)
    | t_int => t_int
    | _ => A
    end. 


Inductive joina : res -> res -> res -> Prop := 
 | joa_eq : forall v, 
    joina (r_e v) (r_e v) (r_e v)
 | joa_v : forall v1 v2,
     not(v1 = v2) ->
    joina (r_e v1) (r_e v2) (r_blame err_a)
 | joa_bv : forall r2, 
    joina (r_blame err_b) r2 r2
 | joa_vb : forall r1, 
    joina r1 (r_blame err_b) r1
 | joa_al : forall r,
    joina (r_blame err_a) r (r_blame err_a)
  | joa_ar : forall r,
    joina r (r_blame err_a) (r_blame err_a)
.


Inductive joint : res -> res -> res -> Prop := 
 | jot_v : forall v1 v2, 
    joint (r_e v1) (r_e v2) (r_e (e_merge v1 v2))
 | jot_va : forall v1, 
    joint (r_e v1) (r_blame err_a) (r_blame err_a)
 | jot_av : forall v1, 
    joint (r_blame err_a) (r_e v1) (r_blame err_a)
 | jot_bl : forall r2,
    joint (r_blame err_b) r2 (r_blame err_b)
 | jot_br : forall r1,
    joint r1 (r_blame err_b) (r_blame err_b)
 | jot_aa : 
    joint (r_blame err_a) (r_blame err_a) (r_blame err_a)
.
 

Inductive Cast : exp -> typ -> res -> Prop :=    (* defn Cast *)
  | cast_top : forall v,
      lc_exp v ->
      Cast v t_top (r_e e_top)
  | cast_i : forall i ,
      Cast (e_lit i) t_int  (r_e (e_lit i))
  | cast_f : forall f (A B:typ),
      csub (principal_type f) (t_arrow A B) ->
      fvalue f ->
      Cast f (t_arrow A B)  (r_e (e_anno f (t_arrow A B)))
  | cast_dyna : forall u r A,
      ord A ->
      Cast u A r ->
      Cast (e_anno u t_dyn) A r
  | cast_rcd : forall v v' l (A:typ),
      Cast v A (r_e v') ->
      Cast (e_rcd l v) (t_rcd l A)  (r_e (e_rcd l v'))
  | cast_rcdp : forall v l (A:typ) b,
      Cast v A (r_blame b) ->
      Cast (e_rcd l v) (t_rcd l A)  (r_blame b)
 | cast_dd : forall v,
    lc_exp v ->
    Cast (e_anno v t_dyn) t_dyn (r_e (e_anno v t_dyn)) 
 | cast_sd : forall s s',
    svalue s ->
    Cast s (const (principal_type s)) (r_e s') ->
    Cast s t_dyn (r_e (e_anno s' t_dyn)) 
 | cast_merged : forall v1 v2 v1' v2',
    Cast v1 t_dyn (r_e v1') ->
    Cast v2 t_dyn (r_e v2') ->
    Cast (e_merge v1 v2) t_dyn (r_e (e_anno (e_merge v1' v2') t_dyn)) 
 | cast_blame : forall v A,
    lc_exp v ->
    not(csub (principal_type v)  A) ->
    Cast v A (r_blame err_b)
  | cast_merge : forall v1 v2 r1 r2 r3 (A:typ),
      ord A ->
      Cast v1 A  r1 ->
      Cast v2 A  r2 ->
      joina r1 r2 r3 ->
      Cast (e_merge v1 v2) A  r3
 | cast_and : forall v A B r1 r2 r3,
      Cast v A  r1 ->
      Cast v B  r2 ->
      joint r1 r2 r3 ->
      Cast v (t_and A B) r3 
 | cast_bot : forall v,
      lc_exp v ->
      (* csub (principal_type v) t_bot -> *)
      Cast v t_bot (r_blame err_b)
.


Inductive ityp : typ -> var -> Prop :=
 | it_r: forall t l,
    ityp (t_rcd l t) l
 | it_andl: forall t1 t2 l,
    ityp t1 l ->
    ityp (t_and t1 t2) l
 | it_andr: forall t1 t2 l,
    ityp t2 l ->
    ityp (t_and t1 t2) l.



Inductive inp : exp -> var -> Prop :=
 | ip_r: forall t l,
    inp (e_rcd l t) l
 | ip_andl: forall t1 t2 l,
    inp t1 l ->
    inp (e_merge t1 t2) l
 | ip_andr: forall t1 t2 l,
    inp t2 l ->
    inp (e_merge t1 t2) l.



Inductive get_ty : typ -> var -> typ -> Prop :=
 | g_r: forall t l,
    get_ty (t_rcd l t) l t
 | g_andl: forall t1 t2 t3 l ,
    get_ty t1 l t3 ->
    not(ityp t2 l) ->
    ityp t1 l ->
    get_ty (t_and t1 t2) l t3
 | g_andr: forall t1 t2 t3 l ,
    not(ityp t1 l) ->
    ityp t2 l ->
    get_ty t2 l t3 ->
    get_ty (t_and t1 t2) l t3
 | g_dyn: forall t l,
    not(ityp t l) -> 
    dynamic t ->
    get_ty t l t_dyn.


Inductive get_value : exp -> var -> exp -> Prop :=
 | gv_r: forall t l,
    get_value (e_rcd l t) l t 
 | gv_andl: forall t1 t2 t3 l ,
    get_value t1 l t3 ->
    get_value (e_merge t1 t2) l t3 
 | gv_andr: forall t1 t2 t3 l ,
    get_value t2 l t3 ->
    get_value (e_merge t1 t2) l t3.


Inductive proj : typ -> var -> typ -> Prop :=
 | pj_in: forall t l t2,
    get_ty t l t2 ->
    proj t l t2
 | pj_dyn: forall t l,
    not(ityp t l) -> 
    dynamic t ->
    proj t l t_dyn.

    
Fixpoint erase (e:exp) : exp :=
    match e with
    | e_anno p A => p
    | _ => e
    end.


Inductive iproj : exp -> var -> res -> Prop :=
 | ipj_pab: forall p l A,
    not(inp p l) ->
    pvalue p ->
    iproj (e_anno p A) l (r_blame err_b)
 | ipj_pa: forall v l B p,
    inp (erase v) l ->
    value v ->
    get_ty (principal_type v) l B ->
    get_value (erase v) l p ->
    iproj v l (r_e (e_anno p B))
.

Fixpoint toS (A : typ) : typ := 
    match A with 
    | t_dyn => t_top
    | (t_and A1 A2) => (t_and (toS A1) (toS A2))
    | _ => A
    end. 

(* Definition disjointSpecc A B :=
  forall C, ord C -> not(csub (toS A) C /\ csub (toS B) C). *)



Fixpoint change_typ (A: typ) : typ :=
  match A with
  | t_dyn => t_top
  | (t_arrow B C) => (t_arrow (change_typ B) (change_typ C))
  | (t_and B C) => (t_and (change_typ B) (change_typ C))
  | (t_rcd l B) => (t_rcd l (change_typ B))
  | _ => A
end.

Definition DisjointSpec A B :=
    exists A' B', static A' /\ static B' /\ tpre A' A 
    /\ tpre B' B /\
    (forall C, sub A' C -> sub B' C -> sub t_top C).


Definition disjointSpec A B :=
    forall C, csub (change_typ A) C -> csub (change_typ B) C -> csub t_top C.


Inductive dmatch : typ -> typ -> Prop :=
  | dmatch_arrow : forall A1 A2,
      dmatch (t_arrow A1 A2) (t_arrow A1 A2)
  | dmatch_unknown : 
      dmatch t_dyn (t_arrow t_dyn t_dyn)
.


Definition NotVal e := not (fvalue e) /\ not (exists g, gvalue g /\ e = (e_anno g t_dyn)).




(* defns Reductions *)
Inductive step : exp -> res -> Prop :=    (* defn step *)
 | step_eval E e1 e2 :
    wellformed E ->
    step e1 ( r_e e2 ) ->
    step (fill E e1) (r_e (fill E e2))
 | step_blame E e1 b : 
    wellformed E ->
    step e1 (r_blame b) ->
    step (fill E e1) (r_blame b)
 | Step_beta : forall (e:exp) v,
     lc_exp (e_abs e) ->
     value v ->
     step (e_app (e_abs e)  v)  (r_e (open_exp_wrt_exp  e v))
 | Step_app : forall e e2 A1 A2,
     fvalue (e_anno e (t_arrow A1 A2)) ->
     step (e_app (e_anno e (t_arrow A1 A2)) e2) (r_e (e_anno (e_app e (e_anno e2 A1)) A2))
 | Step_dyn : forall u1 e2,
     value (e_anno u1 t_dyn) ->
     step (e_app (e_anno u1 t_dyn) e2) (r_e (e_app (e_anno (e_anno u1 t_dyn) (t_arrow t_dyn t_dyn)) e2))
 | Step_annov : forall v (A:typ) r,
     value v ->
     Cast v A r ->
     NotVal (e_anno v A) ->
     step (e_anno v A) r
 | Step_proj : forall l A v v',
     value v ->
     get_ty (principal_type v) l A ->
     Cast v (t_rcd l A) (r_e (e_rcd l v')) ->
     step (e_proj v l) (r_e v')
 | Step_projp : forall l A v b,
     value v ->
     get_ty (principal_type v) l A ->
     Cast v (t_rcd l A) (r_blame b) ->
     step (e_proj v l) (r_blame b)
 | Step_fix : forall (A:typ) (e:exp),
     lc_exp (e_fixpoint e) ->
     step  (e_anno (e_fixpoint e) A)  (r_e (e_anno  (  (open_exp_wrt_exp  e  ( (e_anno (e_fixpoint e) A) )  )  )  A))
 | Step_abs : forall (e:exp),
     lc_exp (e_abs e) ->
     step (e_anno (e_abs e) t_dyn)  (r_e (e_anno (e_anno (e_abs e) (t_arrow t_dyn t_dyn)) t_dyn))
.



Inductive cbn : exp -> res -> Prop :=    (* defn cbn *)
 | cbn_eval E e1 e2 :
    wellformedn E ->
    cbn e1 ( r_e e2 ) ->
    cbn (filln E e1) (r_e (filln E e2))
 | cbn_blame E e1 b : 
    wellformedn E ->
    cbn e1 (r_blame b) ->
    cbn (filln E e1) (r_blame b)
 | cbn_beta : forall (e:exp) e2,
     lc_exp (e_abs e) ->
     lc_exp e2 ->
     cbn (e_app (e_abs e)  e2)  (r_e (open_exp_wrt_exp  e e2) )
 | cbn_abeta : forall f e2 A1 A2,
     lc_exp e2 ->
     fvalue (e_anno f (t_arrow A1 A2)) ->
     cbn (e_app (e_anno f (t_arrow A1 A2)) e2) (r_e (e_anno (e_app f (e_anno e2 A1)) A2))
 | cbn_dyn : forall u1 e2,
     lc_exp e2 ->
     value (e_anno u1 t_dyn) ->
     cbn (e_app (e_anno u1 t_dyn) e2) (r_e (e_app (e_anno (e_anno u1 t_dyn) (t_arrow t_dyn t_dyn)) e2))
 | cbn_annov : forall v (A:typ) r,
     value v ->
     Cast v A r ->
     NotVal (e_anno v A) ->
     cbn (e_anno v A) r
 | cbn_proj : forall l A v v',
     value v ->
     get_ty (principal_type v) l A ->
     Cast v (t_rcd l A) (r_e (e_rcd l v')) ->
     cbn (e_proj v l) (r_e v')
 | cbn_projp : forall l A v b,
     value v ->
     get_ty (principal_type v) l A ->
     Cast v (t_rcd l A) (r_blame b) ->
     cbn (e_proj v l) (r_blame b)
 | cbn_fix : forall (A:typ) (e:exp),
     lc_exp (e_fixpoint e) ->
     cbn  (e_anno (e_fixpoint e) A)  (r_e (e_anno  (  (open_exp_wrt_exp  e  ( (e_anno (e_fixpoint e) A) )  )  )  A))
 | cbn_abs : forall (e:exp),
     lc_exp (e_abs e) ->
     cbn (e_anno (e_abs e) t_dyn)  (r_e (e_anno (e_anno (e_abs e) (t_arrow t_dyn t_dyn)) t_dyn))
.


Inductive co: typ -> typ -> Prop := 
| co_bot:
  co t_bot t_bot
| co_boti:
  co t_int t_bot 
| co_ibot:
  co t_bot t_int  
| co_bota: forall A B,
  co (t_arrow A B) t_bot 
| co_abot: forall A B,
  co t_bot (t_arrow A B)
| co_rcdb: forall l t,
  co (t_rcd l t) t_bot
| co_brcd: forall l t,
  co t_bot (t_rcd l t)
| co_arr: forall A1 B1 A2 B2,
  co (t_arrow A1 B1) (t_arrow A2 B2)
| co_int:
  co t_int t_int
| co_rcd: forall l t1 t2,
  co (t_rcd l t1) (t_rcd l t2)
| co_andl: forall t1 t2 t3,
  co t1 t3 ->
  co (t_and t1 t2) t3
| co_andr: forall t1 t2 t3,
  co t2 t3 ->
  co (t_and t1 t2) t3
| co_ral: forall t1 t2 t3,
  co t1 t2 ->
  co t1 (t_and t2 t3)
| co_rar: forall t1 t2 t3,
  co t1 t3 ->
  co t1 (t_and t2 t3).



Inductive WF: ctx -> Prop :=    (* defn *)
 | WF_nil : 
     WF nil
 | WF_cons : forall x A G,
     well A ->
     WF G ->
     WF (cons ( x , A )  G ).


(* defns Typing *)
Inductive Typing : ctx -> exp -> dirflag -> typ -> Prop :=    (* defn Typing *)
 | Typ_top : forall (G:ctx),
      uniq  G  ->
     Typing G e_top Inf t_top
 | Typ_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     Typing G (e_lit i5) Inf t_int
 | Typ_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
      (* well A -> *)
     Typing G (e_var_f x) Inf A
 | Typ_abs : forall (L:vars) (G:ctx) A (A1:typ) (e:exp) (A2:typ),
      ( forall x , x \notin  L  -> Typing  (cons ( x , A1 )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk A2 )  ->
      well A1 ->
     dmatch A (t_arrow A1 A2) ->
     Typing G (e_abs e) Chk A
 | Typ_app : forall (G:ctx) (e1 e2:exp) (A A1 A2:typ),
     Typing G e1 Inf A ->
     Typing G e2 Chk A1 ->
     dmatch A (t_arrow A1 A2) ->
     Typing G (e_app e1 e2) Inf A2
 | Typ_merge : forall (G:ctx) (e1 e2:exp) (A B:typ),
     Typing G e1 Inf A ->
     Typing G e2 Inf B ->
      disjoint  A   B  ->
     Typing G (e_merge e1 e2) Inf (t_and A B)
 | Typ_anno : forall (G:ctx) (e:exp) (A:typ),
     Typing G e Chk A ->
     Typing G (e_anno e A) Inf A
 | Typ_proj : forall (G:ctx) (e:exp) l (A:typ) B,
     Typing G e Inf A ->
     get_ty A l B ->
     Typing G (e_proj e l) Inf B
 | Typ_rcd : forall (G:ctx) l (e:exp) (A:typ),
     Typing G e Inf A ->
     Typing G (e_rcd l e) Inf (t_rcd l A)
 | Typ_cs : forall (G:ctx) (e:exp) (B A:typ),
     Typing G e Inf A ->
     csub A B ->
     well B ->
     Typing G e Chk B
 | Typ_fix : forall (L:vars) (G:ctx) (A:typ) (e:exp),
      ( forall x , x \notin  L  -> Typing  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk A )  ->
      well A ->
     Typing G (e_fixpoint e) Chk A
 | Typ_rt : forall (L:vars) (G:ctx) (e e2: exp) (A B:typ),
     ( forall x , x \notin  L  -> Typing  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
     Typing G e2 Inf A ->
     Typing G (e_app (e_abs e) e2) Chk B
.



(* Inductive expin : exp -> exp -> Prop :=
| ei_lit : forall i,
  expin (e_lit i) (e_lit i)
| ei_top: forall p,
  expin e_top p
| ei_arr: forall e A B,
  expin (e_abs A e B) (e_abs A e B)
| ei_and: forall p1 p2 p3,
  expin p1 p3 ->
  expin p2 p3 ->
  expin (e_merge p1 p2) p3 
| ei_andl: forall p1 p2 p3,
  expin p1 p2 ->
  expin p1 (e_merge p2 p3)
| ei_andr: forall p1 p2 p3,
  expin p1 p3 ->
  expin p1 (e_merge p2 p3)
| ei_rcd: forall p1 p2 l,
  expin p1 p2 ->
  expin (e_rcd l p1) (e_rcd l p2). *)



Inductive precise : exp -> exp -> Prop :=  
 | precise_var : forall (x:var),
    precise (e_var_f x) (e_var_f x)
 | precise_t :
    precise e_top e_top
 | precise_i i:
    precise (e_lit i) (e_lit i) 
 | precise_abs : forall (e1 e2:exp) (L:vars),
     ( forall x , x \notin  L  -> 
      precise  ( open_exp_wrt_exp e1 (e_var_f x) )   ( open_exp_wrt_exp e2 (e_var_f x) )  )  ->
     precise (e_abs e1) (e_abs e2)
 | precise_app : forall (e1 e2 e1' e2':exp) ,
     precise e1 e1' ->
     precise e2 e2' ->
     precise (e_app e1 e2) (e_app e1' e2')
 | precise_anno : forall (A B:typ) (e1 e2:exp),
     tpre A B ->
     precise e1 e2 ->
     precise (e_anno e1 A) (e_anno e2 B)
 | precise_merge : forall (e1 e2 e3 e4:exp) ,
     precise e1 e3 ->
     precise e2 e4 ->
     precise (e_merge e1 e2) (e_merge e3 e4)
 | precise_rcd : forall l (e1 e2:exp),
     precise e1 e2 ->
     precise (e_rcd l e1) (e_rcd l e2)
 | precise_prj : forall l (e1 e2:exp),
     precise e1 e2 ->
     precise (e_proj e1 l) (e_proj e2 l)
 | precise_fix : forall (e1 e2:exp) (L:vars),
     ( forall x , x \notin  L  -> 
      precise  ( open_exp_wrt_exp e1 (e_var_f x) )   ( open_exp_wrt_exp e2 (e_var_f x) )  )  ->
      (* tpre A1 A2 -> *)
     precise (e_fixpoint e1) (e_fixpoint e2).



(* Inductive epre : ctx -> ctx -> exp -> exp -> typ -> typ Prop :=  
 | ep_var : forall G1 G2 (x:var) A B,
    tpre A B ->
    epre G1 G2 (e_var_f x) (e_var_f x) A B
 | ep_t : forall G1 G2,
    epre G1 G2 e_top e_top t_top t_top
 | ep_i i:forall G1 G2,
    epre G1 G2 (e_lit i) (e_lit i) t_int t_int
 | ep_abs : forall G1 G2 (e1 e2:exp) (L:vars) A1 A2 B1 B2,
     ( forall x , x \notin  L  -> 
      epre  ( open_exp_wrt_exp e1 (e_var_f x) )   ( open_exp_wrt_exp e2 (e_var_f x) )  )  ->
      tpre A1 A2 ->
      tpre B1 B2 ->
     epre G1 G2 (e_abs A1 e1 B1) (e_abs A2 e2 B2)
 | ep_app : forall (e1 e2 e1' e2':exp) G1 G2,
     epre G1 G2 e1 e1' ->
     epre G1 G2 e2 e2' ->
     epre G1 G2 (e_app e1 e2) (e_app e1' e2')
 | ep_anno : forall (A B:typ) (e1 e2:exp) G1 G2,
     tpre A B ->
     epre G1 G2 e1 e2 ->
     epre G1 G2 (e_anno e1 A) (e_anno e2 B)
 | ep_merge : forall (e1 e2 e3 e4:exp) G1 G2,
     epre G1 G2 e1 e3 A1 B1 ->
     epre G1 G2 e2 e4 A2 B2 ->
     epre G1 G2 (e_merge e1 e2) (e_merge e3 e4) (t_and A1 A2) (t_and B1 B2)
 | ep_rcd : forall l (e1 e2:exp) G1 G2,
     epre G1 G2 e1 e2 ->
     epre G1 G2 (e_rcd l e1) (e_rcd l e2)
 | ep_prj : forall l (e1 e2:exp) G1 G2,
     epre G1 G2 e1 e2 ->
     epre G1 G2 (e_proj e1 l) (e_proj e2 l) A B
 | ep_vd : forall v1 v2 v3 G1 G2 A B,
     value (e_anno v1 t_dyn) ->
     value (e_anno v2 t_dyn) ->
     expin v3 v2 ->
     epre nil nil v1 v3 A B ->
     epre G1 G2 (e_anno v1 t_dyn) (e_anno v2 t_dyn)
 | ep_v : forall v1 v2 v3 G1 G2 A B,
     value v1 ->
     value (e_anno v2 t_dyn) ->
     fv_exp v1 [<=] empty -> 
     fv_exp v2 [<=] empty -> 
     expin v3 v2 ->
     epre nil nil v1 v3 A B ->
     epre G1 G2 v1 (e_anno v2 t_dyn). *)


Inductive cpre : ctx -> ctx -> Prop :=
  | cp_nil: 
      cpre nil nil
  | cp_cons: forall E F x A1 A2,
      tpre A1 A2 ->
      cpre E F ->
      cpre (cons ( x , A1 )  E) (cons ( x , A2 )  F) 
.


Inductive steps : exp -> res -> Prop :=
  | step_refl e:
    steps e (r_e e)

  | step_n e t' e':   
    step e (r_e  e') ->
    steps e' (r_e t') ->
    steps e  (r_e  t')
  | step_nb e e':
    step e (r_e  e') ->
    steps e' (r_blame err_b) ->
    steps e  (r_blame err_b)

  | step_b e:
    step e (r_blame err_b) ->
    steps e (r_blame err_b).


(** infrastructure *)

Hint Constructors cbn wellformedn WF gvalue Ground svalue joina joint Value Uvalue precise uvalue dmatch botLike co get_value get_ty proj iproj ityp inp spl well steps wellformed fvalue topLike
ord oord value pvalue 
ddyn dynamic static disjoint sub csub sim typin  
(* epre  *)
tpre cpre
Cast step Typing lc_exp : core.

