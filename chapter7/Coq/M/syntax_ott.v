(* !!! WARNING: AUTO GENERATED. DO NOT MODIFY !!! *)
Require Import Bool.
Require Import Metalib.Metatheory.
(* Require Import List. *)
(** syntax *)
Definition i : Set := nat.

Inductive dtyp : Set :=  (*r dtypes *)
 | dt_int : dtyp (*r int *)
 | dt_top : dtyp (*r top *)
 | dt_bot : dtyp (*r bot *)
 | dt_arrow (A:dtyp) (B:dtyp) (*r function dtypes *)
 | dt_and (A:dtyp) (B:dtyp) (*r intersection *)
 | dt_rcd (l:var) (A:dtyp) (*r record *).

(** This uses the locally nameless representation for terms and cofinite quantification in typing judgements. *)
Inductive dexp : Set :=  (*r dexpdexpsions *)
 | de_var_b (_:nat) (*r variables *)
 | de_var_f (x:var) (*r variables *)
 | de_top : dexp (*r top *)
 | de_lit (i5:i) (*r lit *)
 | de_abs (e:dexp) (*r abstractions *)
 | de_app (e1:dexp) (e2:dexp) (*r applications *)
 | de_merge (e1:dexp) (e2:dexp) (*r merge *)
 | de_anno (e:dexp) (A:dtyp) (*r annotation *)
 | de_rcd (l:var) (e:dexp) (*r record *)
 | de_proj (e:dexp) (l:var) (*r projection *)
 | de_fixpoint (e:dexp).
 

Definition dctx : Set := list ( atom * dtyp ).

Inductive dtlist : Set :=  (*r list dtype *)
 | ddt_empty : dtlist
 | ddt_consl (AA:dtlist) (A:dtyp).

Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

(* dexpERIMENTAL *)
(** auxiliary functions on the new list dtypes *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
Fixpoint open_dexp_wrt_dexp_rec (k:nat) (de_5:dexp) (de__6:dexp) {struct de__6}: dexp :=
  match de__6 with
  | (de_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => de_var_b nat
        | inleft (right _) => de_5
        | inright _ => de_var_b (nat - 1)
      end
  | (de_var_f x) => de_var_f x
  | de_top => de_top 
  | (de_lit i5) => de_lit i5
  | (de_abs e) => de_abs (open_dexp_wrt_dexp_rec (S k) de_5 e)
  | (de_app e1 e2) => de_app (open_dexp_wrt_dexp_rec k de_5 e1) (open_dexp_wrt_dexp_rec k de_5 e2)
  | (de_merge e1 e2) => de_merge (open_dexp_wrt_dexp_rec k de_5 e1) (open_dexp_wrt_dexp_rec k de_5 e2)
  | (de_anno e A) => de_anno (open_dexp_wrt_dexp_rec k de_5 e) A
  | (de_rcd l e) => de_rcd l (open_dexp_wrt_dexp_rec k de_5 e)
  | (de_proj e l) => de_proj (open_dexp_wrt_dexp_rec k de_5 e) l
  | (de_fixpoint e) => de_fixpoint (open_dexp_wrt_dexp_rec (S k) de_5 e)
end.

Definition open_dexp_wrt_dexp de_5 de__6 := open_dexp_wrt_dexp_rec 0 de__6 de_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_dexp *)
Inductive lc_dexp : dexp -> Prop :=    (* defn lc_dexp *)
 | lc_de_var_f : forall (x:var),
     (lc_dexp (de_var_f x))
 | lc_de_top : 
     (lc_dexp de_top)
 | lc_de_lit : forall (i5:i),
     (lc_dexp (de_lit i5))
 | lc_de_abs : forall (e:dexp),
      ( forall x , lc_dexp  ( open_dexp_wrt_dexp e (de_var_f x) )  )  ->
     (lc_dexp (de_abs e))
 | lc_de_app : forall (e1 e2:dexp),
     (lc_dexp e1) ->
     (lc_dexp e2) ->
     (lc_dexp (de_app e1 e2))
 | lc_de_merge : forall (e1 e2:dexp),
     (lc_dexp e1) ->
     (lc_dexp e2) ->
     (lc_dexp (de_merge e1 e2))
 | lc_de_anno : forall (e:dexp) (A:dtyp),
     (lc_dexp e) ->
     (lc_dexp (de_anno e A))
 | lc_de_rcd : forall l (e:dexp),
     (lc_dexp e) ->
     (lc_dexp (de_rcd l e))
 | lc_de_proj : forall (e:dexp) l,
     (lc_dexp e) ->
     (lc_dexp (de_proj e l))
 | lc_de_fixpoint : forall (e:dexp),
     ( forall x , lc_dexp  ( open_dexp_wrt_dexp e (de_var_f x) )  )  ->
    (lc_dexp (de_fixpoint e))
.


     
(** free variables *)
Fixpoint fv_dexp (de_5:dexp) : vars :=
  match de_5 with
  | (de_var_b nat) => {}
  | (de_var_f x) => {{x}}
  | de_top => {}
  | (de_lit i5) => {}
  | (de_abs e) => (fv_dexp e)
  | (de_app e1 e2) => (fv_dexp e1) \u (fv_dexp e2)
  | (de_merge e1 e2) => (fv_dexp e1) \u (fv_dexp e2)
  | (de_anno e A) => (fv_dexp e)
  | (de_rcd l e) => (fv_dexp e)
  | (de_proj e l) => (fv_dexp e)
  | (de_fixpoint e) => (fv_dexp e)
end.

(** substitutions *)
Fixpoint subst_dexp (de_5:dexp) (x5:var) (de__6:dexp) {struct de__6} : dexp :=
  match de__6 with
  | (de_var_b nat) => de_var_b nat
  | (de_var_f x) => (if eq_var x x5 then de_5 else (de_var_f x))
  | de_top => de_top 
  | (de_lit i5) => de_lit i5
  | (de_abs e) => de_abs (subst_dexp de_5 x5 e)
  | (de_app e1 e2) => de_app (subst_dexp de_5 x5 e1) (subst_dexp de_5 x5 e2)
  | (de_merge e1 e2) => de_merge (subst_dexp de_5 x5 e1) (subst_dexp de_5 x5 e2)
  | (de_anno e A) => de_anno (subst_dexp de_5 x5 e) A
  | (de_rcd l e) => de_rcd l (subst_dexp de_5 x5 e)
  | (de_proj e l) => de_proj (subst_dexp de_5 x5 e) l
  | (de_fixpoint e) => de_fixpoint (subst_dexp de_5 x5 e)
end.


(* principal dtypes for values*)
Fixpoint principal_type (v:dexp) : dtyp :=
  match v with
  | de_top => dt_top
  | (de_lit i5) => dt_int
  | (de_anno e A) => A
  | (de_merge v1 v2) => dt_and (principal_type v1) (principal_type v2)
  | (de_rcd l e) => (dt_rcd l (principal_type e))
  | _ => dt_top
  end.
  

(** definitions *)





Inductive fvalue : dexp -> Prop :=    (* defn svalue *)
 | fval_abs : forall (A:dtyp) (e:dexp) (B:dtyp),
     lc_dexp (de_abs e) ->
     fvalue  (de_anno (de_abs e ) (dt_arrow A B) )
 | fval_vabs: forall f A B,
     fvalue f -> 
     fvalue (de_anno f (dt_arrow A B)).

Inductive value : dexp -> Prop :=    (* defn pvalue *)
| val_i : forall i,
    value (de_lit i)
| val_t : 
    value de_top
| val_f : forall f,
    fvalue f ->
    value f
| val_merge : forall (e1 e2:dexp),
    value e1 ->
    value e2 ->
    value (de_merge e1 e2)
| val_rcd : forall l (e:dexp),
    value e ->
    value (de_rcd l e).




(* defns TopLikedtype *)
Inductive topLike : dtyp -> Prop :=    (* defn topLike *)
 | dTL_top : 
     topLike dt_top
 | dTL_and : forall (A B:dtyp),
     topLike A ->
     topLike B ->
     topLike (dt_and A B).


(* defns BotLikedtype *)
Inductive botLike : dtyp -> Prop :=    (* defn botLike *)
 | BL_bot : 
     botLike dt_bot
 | BL_andl : forall (A B:dtyp),
     botLike A ->
     botLike (dt_and A B)
 | BL_andr : forall (A B:dtyp),
     botLike B ->
     botLike (dt_and A B).


     (* defns Ordinarydtype *)
Inductive ord : dtyp -> Prop :=    (* defn ord *)
| O_bot : 
    ord dt_bot
| O_int : 
    ord dt_int
| O_arrow : forall (A B:dtyp),
    ord (dt_arrow A B)
| O_rcd : forall l (A:dtyp),
    ord (dt_rcd l A).

Inductive oord : dtyp -> Prop :=    (* defn ord *)
| od_bot : 
    oord dt_bot
| od_top : 
    oord dt_top
| od_int : 
    oord dt_int
| od_arrow : forall (A B:dtyp),
    oord (dt_arrow A B)
| od_rcd : forall l (A:dtyp),
    oord (dt_rcd l A).

(* defns disjoint *)
Inductive disjoint : dtyp -> dtyp -> Prop :=    (* defn disjoint *)
 | DD_topL : forall B,
     disjoint dt_top B
 | DD_topR : forall (A:dtyp),
     disjoint A dt_top
 | DD_andL : forall (A1 A2 B:dtyp),
     disjoint A1 B ->
     disjoint A2 B ->
     disjoint (dt_and A1 A2) B
 | DD_andR : forall (A B1 B2:dtyp),
     disjoint A B1 ->
     disjoint A B2 ->
     disjoint A (dt_and B1 B2)
 | DD_intArr : forall (A1 A2:dtyp),
     disjoint dt_int (dt_arrow A1 A2)
 | DD_arrInt : forall (A1 A2:dtyp),
     disjoint (dt_arrow A1 A2) dt_int
 | DD_rcdNeq : forall l1 (A:dtyp) l2 (B:dtyp),
      l1  <>  l2  ->
     disjoint (dt_rcd l1 A) (dt_rcd l2 B)
 | DD_IntRcd : forall l (A:dtyp),
     disjoint dt_int (dt_rcd l A)
 | DD_RcdInt : forall l (A:dtyp),
     disjoint (dt_rcd l A) dt_int
 | DD_ArrRcd : forall (A1 A2:dtyp) l (A:dtyp),
     disjoint (dt_arrow A1 A2) (dt_rcd l A)
 | DD_RcdArr : forall l (A A1 A2:dtyp),
     disjoint (dt_rcd l A) (dt_arrow A1 A2).

(* defns subTyping *)
Inductive sub : dtyp -> dtyp -> Prop :=    (* defn sub *)
 | DS_z : 
     sub dt_int dt_int
 | DS_bot : forall A, 
     sub dt_bot A
 | DS_top : forall (A:dtyp),
     sub A dt_top
 | DS_arr : forall (A1 A2 B1 B2:dtyp),
     sub B1 A1 ->
     sub A2 B2 ->
     sub (dt_arrow A1 A2) (dt_arrow B1 B2)
 | DS_andl1 : forall (A1 A2 A3:dtyp),
     sub A1 A3 ->
     sub (dt_and A1 A2) A3
 | DS_andl2 : forall (A1 A2 A3:dtyp),
     sub A2 A3 ->
     sub (dt_and A1 A2) A3
 | DS_andr : forall (A1 A2 A3:dtyp),
     sub A1 A2 ->
     sub A1 A3 ->
     sub A1 (dt_and A2 A3)
 | DS_rcd : forall l (C D:dtyp),
     sub C D ->
     sub (dt_rcd l C) (dt_rcd l D).


Inductive ctx_item : Type :=
     | dappCtxL : dexp -> ctx_item
     | dappCtxR : dexp -> ctx_item
     | dmergeCtxL : dexp -> ctx_item
     | dmergeCtxR : dexp -> ctx_item
     | drcdCtx : var ->  ctx_item
     | dprjCtx : var ->  ctx_item
     | dannoCtx : dtyp ->  ctx_item.

Inductive wellformed : ctx_item -> Prop :=
     | dwf_appCtxL : forall (e : dexp),
                    lc_dexp e ->
                    wellformed (dappCtxL e)
     | dwf_appCtxR : forall (e : dexp),
                    lc_dexp (de_abs e) ->
                    wellformed (dappCtxR (de_abs e))
    | dwf_mergeCtxL : forall (e : dexp),
                    lc_dexp e ->
                    wellformed (dmergeCtxL e)
     | dwf_mergeCtxR : forall (v : dexp),
                    value v ->
                    wellformed (dmergeCtxR v)
     | dwf_rcdCtx : forall l,
                    wellformed (drcdCtx l)
     | dwf_prjCtx : forall l,
                    wellformed (dprjCtx l)
     | dwf_annoCtx : forall l,
                    wellformed (dannoCtx l).


Inductive ctx_itemn : Type :=
     | ndappCtxL : dexp -> ctx_itemn
     | ndmergeCtxL : dexp -> ctx_itemn
     | ndmergeCtxR : dexp -> ctx_itemn
     | ndrcdCtx : var ->  ctx_itemn
     | ndprjCtx : var ->  ctx_itemn
     | ndannoCtx : dtyp ->  ctx_itemn.

Inductive wellformedn : ctx_itemn -> Prop :=
     | ndwf_appCtxL : forall (e : dexp),
                    lc_dexp e ->
                    wellformedn (ndappCtxL e)
    | ndwf_mergeCtxL : forall (e : dexp),
                    lc_dexp e ->
                    wellformedn (ndmergeCtxL e)
     | ndwf_mergeCtxR : forall (v : dexp),
                    value v ->
                    wellformedn (ndmergeCtxR v)
     | ndwf_rcdCtx : forall l,
                    wellformedn (ndrcdCtx l)
     | ndwf_prjCtx : forall l,
                    wellformedn (ndprjCtx l)
     | ndwf_annoCtx : forall l,
                    wellformedn (ndannoCtx l).



Definition filln (E : ctx_itemn) (e : dexp) : dexp :=
     match E with
     | ndappCtxL e2 => de_app e e2
     | ndmergeCtxL e2 => de_merge e e2
     | ndmergeCtxR v1 => de_merge v1 e
     | ndrcdCtx l => de_rcd l e  
     | ndprjCtx l => de_proj e l  
     | ndannoCtx A => de_anno e A 
     end.


Definition fill (E : ctx_item) (e : dexp) : dexp :=
     match E with
     | dappCtxL e2 => de_app e e2
     | dappCtxR v1 => de_app v1 e
     | dmergeCtxL e2 => de_merge e e2
     | dmergeCtxR v1 => de_merge v1 e
     | drcdCtx l => de_rcd l e  
     | dprjCtx l => de_proj e l  
     | dannoCtx A => de_anno e A 
     end.




Inductive ityp : dtyp -> var -> Prop :=
 | idt_r: forall t l,
    ityp (dt_rcd l t) l
 | idt_andl: forall t1 t2 l,
    ityp t1 l ->
    ityp (dt_and t1 t2) l
 | idt_andr: forall t1 t2 l,
    ityp t2 l ->
    ityp (dt_and t1 t2) l.


Inductive inp : dexp -> var -> Prop :=
 | dip_r: forall t l,
    inp (de_rcd l t) l
 | dip_andl: forall t1 t2 l,
    inp t1 l ->
    inp (de_merge t1 t2) l
 | dip_andr: forall t1 t2 l,
    inp t2 l ->
    inp (de_merge t1 t2) l.



Inductive get_ty : dtyp -> var -> dtyp -> Prop :=
 | dg_r: forall t l,
    get_ty (dt_rcd l t) l t
 | dg_andl: forall t1 t2 t3 l ,
    get_ty t1 l t3 ->
    not(ityp t2 l) ->
    get_ty (dt_and t1 t2) l t3
 | g_andr: forall t1 t2 t3 l ,
    not(ityp t1 l) ->
    get_ty t2 l t3 ->
    get_ty (dt_and t1 t2) l t3.


Inductive get_value : dexp -> var -> dexp -> Prop :=
 | dgv_r: forall t l,
    get_value (de_rcd l t) l t 
 | dgv_andl: forall t1 t2 t3 l ,
    get_value t1 l t3 ->
    get_value (de_merge t1 t2) l t3 
 | dgv_andr: forall t1 t2 t3 l ,
    get_value t2 l t3 ->
    get_value (de_merge t1 t2) l t3.


Inductive proj : dtyp -> var -> dtyp -> Prop :=
 | dpj_in: forall t l t2,
    get_ty t l t2 ->
    proj t l t2.




Fixpoint erase (e:dexp) : dexp :=
  match e with
  | de_anno p A => p
  | _ => e
end.



Inductive Cast : dexp -> dtyp -> dexp -> Prop :=    (* defn Cast *)
  | cast_top : forall v,
      lc_dexp v ->
      Cast v dt_top (de_top)
  | cast_i : forall i ,
      Cast (de_lit i) dt_int  ((de_lit i))
  | cast_f : forall f (A B:dtyp),
      sub (principal_type f) (dt_arrow A B) ->
      fvalue f ->
      Cast f (dt_arrow A B)  ((de_anno f (dt_arrow A B)))
  | cast_rcd : forall v v' l (A:dtyp),
      Cast v A (v') ->
      Cast (de_rcd l v) (dt_rcd l A)  ((de_rcd l v'))
  | cast_mergel : forall v1 v2 r1 (A:dtyp),
      ord A ->
      Cast v1 A  r1 ->
      Cast (de_merge v1 v2) A  r1
  | cast_merger : forall (v1 v2:dexp) (A:dtyp) r2,
      ord A ->
      Cast v2 A  r2 ->
      Cast (de_merge v1 v2) A  r2
 | cast_and : forall v (A B:dtyp) v1 v2,
      Cast v A  (v1) ->
      Cast v B  (v2) ->
      Cast v (dt_and A B)  ((de_merge v1 v2))
.

Definition NotVal e := not (fvalue e).

(* defns Reductions *)
Inductive step : dexp -> dexp -> Prop :=    (* defn step *)
 | step_eval E e1 e2 :
    wellformed E ->
    step e1 (e2 ) ->
    step (fill E e1) (fill E e2)
 | step_beta : forall e v,
     lc_dexp (de_abs e) ->
     value v ->
     step (de_app (de_abs e)  v)  (open_dexp_wrt_dexp  e v)
 | step_abeta : forall A2 e e2 A1,
      fvalue  (de_anno e (dt_arrow A1 A2)) ->
     step (de_app (de_anno e (dt_arrow A1 A2)) e2) (de_anno (de_app e(de_anno e2 A1)) A2)
 | step_annov : forall v A v1,
     value v ->
     Cast v A v1 ->
     NotVal (de_anno v A) ->
     step (de_anno v A) v1
 | step_proj : forall l v v' A,
     value v ->
     get_ty (principal_type v) l A ->
     Cast v (dt_rcd l A) (de_rcd l v') ->
     step (de_proj v l) v'
 | step_fix : forall (A:dtyp) (e:dexp),
     lc_dexp (de_fixpoint e) ->
     step  ( de_anno (de_fixpoint e) A)  (de_anno  (  (open_dexp_wrt_dexp  e  (de_anno (de_fixpoint e) A)  )  )  A).


Inductive cbn : dexp -> dexp -> Prop :=    (* defn cbn *)
 | cbn_eval E e1 e2 :
    wellformedn E ->
    cbn e1 (e2 ) ->
    cbn (filln E e1) (filln E e2)
 | cbn_beta : forall e e2,
     lc_dexp (de_abs e) ->
     cbn (de_app (de_abs e)  e2)  (open_dexp_wrt_dexp  e e2)
 | cbn_abeta : forall A2 e e2 A1,
      fvalue  (de_anno e (dt_arrow A1 A2)) ->
     cbn (de_app (de_anno e (dt_arrow A1 A2)) e2) (de_anno (de_app e(de_anno e2 A1)) A2)
 | cbn_annov : forall v A v1,
     value v ->
     Cast v A v1 ->
     NotVal (de_anno v A) ->
     cbn (de_anno v A) v1
 | cbn_proj : forall l v v' A,
     value v ->
     get_ty (principal_type v) l A ->
     Cast v (dt_rcd l A) (de_rcd l v') ->
     cbn (de_proj v l) v'
 | cbn_fix : forall (A:dtyp) (e:dexp),
     lc_dexp (de_fixpoint e) ->
     cbn  (de_anno (de_fixpoint e) A )  (de_anno  (  (open_dexp_wrt_dexp  e  (de_anno (de_fixpoint e) A)  )  )  A).



Inductive co: dtyp -> dtyp -> Prop := 
| co_bot:
  co dt_bot dt_bot
| co_boti:
  co dt_int dt_bot 
| co_ibot:
  co dt_bot dt_int  
| co_bota: forall A B,
  co (dt_arrow A B) dt_bot 
| co_abot: forall A B,
  co dt_bot (dt_arrow A B)
| co_rcdb: forall l t,
  co (dt_rcd l t) dt_bot
| co_brcd: forall l t,
  co dt_bot (dt_rcd l t)
| co_arr: forall A1 B1 A2 B2,
  co (dt_arrow A1 B1) (dt_arrow A2 B2)
| co_int:
  co dt_int dt_int
| co_rcd: forall l t1 t2,
  co (dt_rcd l t1) (dt_rcd l t2)
| co_andl: forall t1 t2 t3,
  co t1 t3 ->
  co (dt_and t1 t2) t3
| co_andr: forall t1 t2 t3,
  co t2 t3 ->
  co (dt_and t1 t2) t3
| co_ral: forall t1 t2 t3,
  co t1 t2 ->
  co t1 (dt_and t2 t3)
| co_rar: forall t1 t2 t3,
  co t1 t3 ->
  co t1 (dt_and t2 t3).



Fixpoint toS (A : dtyp) : dtyp := 
    match A with 
    | (dt_and A1 A2) => (dt_and (toS A1) (toS A2))
    | (dt_rcd l A1) => (dt_rcd l (toS A1)) 
    | _ => A
    end. 


(* Definition disjointSpecc A B :=
  forall C, ord C -> not(sub A C /\ sub B C). *)


Definition disjointSpec A B :=
    forall C, sub A C -> sub B C -> sub dt_top C.

Inductive well : dtyp -> Prop :=    (* defn *)
 | wl_top : 
     well dt_top
 | wl_int : 
     well dt_int
 | wl_arr : forall A B,
     well A ->
     well B -> 
     well (dt_arrow A B)
 | wl_merge : forall A B,
     well A ->
     well B ->
     disjoint A B ->
     well (dt_and A B)
 | wl_rcd : forall l A,
     well A ->
     well (dt_rcd l A).


Inductive WF: dctx -> Prop :=    (* defn *)
 | WF_nil : 
     WF nil
 | WF_cons : forall x A G,
     well A ->
     WF G ->
     WF (cons ( x , A )  G ).


(* uniq G is to make sure we dont have repeat variables. *)
(* we use disjoint for disjointness because we have proved that it is equivalent 
to the relation using COST. *)
Inductive Typing : dctx -> dexp -> dirflag -> dtyp -> Prop :=    (* defn Typing *)
 | Typ_top : forall (G:dctx),
      uniq  G  ->
     Typing G de_top Inf dt_top
 | Typ_lit : forall (G:dctx) (i5:i),
      uniq  G  ->
     Typing G (de_lit i5) Inf dt_int
 | Typ_var : forall (G:dctx) (x:var) A,
      uniq  G  ->
      binds  x A G  ->
      (* well A -> *)
     Typing G (de_var_f x) Inf A
 | Typ_abs : forall (L:vars) (G:dctx) A e B,
      ( forall x , x \notin  L  -> Typing  (cons ( x , A )  G )   ( open_dexp_wrt_dexp e (de_var_f x) )  Chk B )  ->
      well A ->
      Typing G (de_abs e) Chk (dt_arrow A B)
 | Typ_app : forall (G:dctx) e1 e2 B A,
     Typing G e1 Inf (dt_arrow A B) ->
     Typing G e2 Chk A ->
     Typing G (de_app e1 e2) Inf B
 | Typ_merge : forall (G:dctx) e1 e2 A B,
     Typing G e1 Inf A ->
     Typing G e2 Inf B ->
     disjoint  A B  ->
     Typing G (de_merge e1 e2) Inf (dt_and A B)
 | Typ_anno : forall (G:dctx) e A,
     Typing G e Chk A ->
     Typing G (de_anno e A) Inf A
 | Typ_proj : forall (G:dctx) e l A B,
     Typing G e Inf A ->
     get_ty A l B ->
     Typing G (de_proj e l) Inf B
 | Typ_rcd : forall (G:dctx) l e A,
     Typing G e Inf A ->
     Typing G (de_rcd l e) Inf (dt_rcd l A)
 | Typ_sub : forall (G:dctx) e B A,
     Typing G e Inf A ->
     sub A B ->
     well B ->
     Typing G e Chk B
 | Typ_fix : forall (L:vars) (G:dctx) (A:dtyp) (e:dexp),
      ( forall x , x \notin  L  -> Typing  (cons ( x , A )  G )   ( open_dexp_wrt_dexp e (de_var_f x) )  Chk A )  ->
      well A ->
     Typing G (de_fixpoint e) Chk A
 | Typ_rt : forall (L:vars) (G:dctx) A e B e2,
     ( forall x , x \notin  L  -> Typing  (cons ( x , A )  G )   ( open_dexp_wrt_dexp e (de_var_f x) )  Chk B )  ->
     Typing G e2 Inf A ->
     Typing G (de_app (de_abs e) e2) Chk B.

(* 
Inductive steps : dexp -> dexp -> Prop :=
  | step_refl e:
    steps e (r_e e)

  | step_n e t' e':   
    step e (r_e  e') ->
    steps e' (r_e t') ->
    steps e  (r_e  t')
  | step_nb e e':
    step e (r_e  e') ->
    steps e' r_blame ->
    steps e  r_blame

  | step_b e:
    step e r_blame ->
    steps e r_blame. *)

(** infrastructure *)

Hint Constructors wellformedn cbn WF Cast well botLike co get_value get_ty proj ityp inp 
wellformed fvalue 
  topLike
ord oord value 
disjoint sub  step  Typing lc_dexp : core.

