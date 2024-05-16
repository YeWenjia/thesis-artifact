
Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
Require Import syntaxb_ott.


Inductive exp : Set :=  (*r expressions *)
 | e_var_b (_:nat) (*r variables *)
 | e_var_f (x:var) (*r variables *)
 | e_lit (i5:i) (*r lit *)
 | e_abs (A:typ) (e:exp) (B:typ) (*r abstractions *)
 | e_app (e1:exp) (e2:exp) (*r applications *)
 | e_anno (e:exp) (A:typ) (*r annotation *)
 | e_add : exp (*r addition *)
 | e_addl (i5:i) (*r addl *)
 | e_pro (e1:exp) (e2:exp)
 | e_l (e:exp) 
 | e_r (e:exp)
.

Inductive dirflag : Set :=  (*r checking direction *)
 | Inf : dirflag
 | Chk : dirflag.

Definition ctx : Set := list ( atom * typ ).

Definition ls : Set := list st.


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
  | (e_lit i5) => e_lit i5
  | (e_abs t1 e t2) => e_abs t1 (open_exp_wrt_exp_rec (S k) e_5 e) t2
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_anno e A) => e_anno (open_exp_wrt_exp_rec k e_5 e) A
  | e_add => e_add 
  | (e_addl i5) => e_addl i5
  | (e_pro e1 e2) => e_pro (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_l e) => e_l (open_exp_wrt_exp_rec k e_5 e) 
  | (e_r e) => e_r (open_exp_wrt_exp_rec k e_5 e) 
end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall (i5:i),
     (lc_exp (e_lit i5))
 | lc_e_abs : forall (e:exp) t1 t2,
      ( forall x , lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs t1 e t2))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_anno : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_anno e A))
 | lc_e_add : 
     (lc_exp e_add)
 | lc_e_addl : forall (i5:i),
     (lc_exp (e_addl i5))
 | lc_e_pro : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_pro e1 e2))
 | lc_e_l : forall (e:exp),
     (lc_exp e) ->
     (lc_exp (e_l e))
 | lc_e_r : forall (e :exp),
     (lc_exp e) ->
     (lc_exp (e_r e))
.




(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | (e_lit i5) => {}
  | (e_abs t1 e t2) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_anno e A) => (fv_exp e)
  | e_add => {}
  | (e_addl i5) => {}
  | (e_pro e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_l e) => (fv_exp e) 
  | (e_r e) => (fv_exp e) 
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if eq_var x x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_abs t1 e t2) => e_abs t1 (subst_exp e_5 x5 e) t2
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_anno e A) => e_anno (subst_exp e_5 x5 e) A
  | e_add => e_add 
  | (e_addl i5) => e_addl i5
  | (e_pro e1 e2) => e_pro (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_l e) => e_l (subst_exp e_5 x5 e)
  | (e_r e) => e_r (subst_exp e_5 x5 e)
end.


(* principal types for values*)
Fixpoint dynamic_type (v:exp) : typ :=
  match v with
  | (e_lit i5) => t_int
  | (e_anno e A) => A
  | (e_abs t1 e t2) => (t_arrow t1 t2)
  | (e_add) => (t_arrow t_int (t_arrow t_int t_int))
  | (e_addl i5) => (t_arrow t_int t_int)
  | (e_pro v1 v2) => (t_pro (dynamic_type v1) (dynamic_type v2))
  | _ => t_dyn
  end.



(* defns Values *)
Inductive value : exp -> Prop :=    (* defn value *)
 | value_lit : forall (i5:i),
     value (e_lit i5)
 | value_add : 
     value e_add
 | value_addl : forall (i5:i),
     value  ( (e_addl i5) ) 
 | value_abs : forall e t1 t2,
     lc_exp (e_abs t1 e t2) ->
     value (e_abs t1 e t2)
 | value_fanno : forall (v:exp) (A B C D:typ),
     value v ->
      (t_arrow C D)  =   (dynamic_type   ( v )  )   ->
     value (e_anno v (t_arrow A B))
 | value_dyn : forall (v:exp),
     Ground   (dynamic_type  v )   ->
     value v ->
     value  ( (e_anno v t_dyn) ) 
 | value_pro : forall (v1 v2:exp),
     value v1   ->
     value v2 ->
     value  ( (e_pro v1 v2) )
.





(* Definition FLike A := not (A = t_dyn) /\ not (A = (t_arrow t_dyn t_dyn)) /\ (sim A (t_arrow t_dyn t_dyn)). *)
Definition FLike A := not (A = t_dyn) /\ not (A = (t_arrow t_dyn t_dyn)) /\ (sim A (t_arrow t_dyn t_dyn)).

Inductive pattern : typ -> typ -> Prop :=    
 | pa_arr : forall A B,
     pattern (t_arrow A B) (t_arrow A B)
 | pa_dyn : 
     pattern t_dyn (t_arrow t_dyn t_dyn).


Inductive pattern_pro : typ -> typ -> Prop :=    
 | ppa_fun : forall A1 A2,
    pattern_pro (t_pro A1 A2) (t_pro A1 A2)
 | ppa_dyn : 
    pattern_pro t_dyn (t_pro t_dyn t_dyn).


(* defns Typing *)
Inductive Typing : ctx -> exp -> dirflag -> typ -> Prop :=    (* defn Typing *)
 | Typ_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     Typing G (e_lit i5) Inf t_int
 | Typ_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     Typing G (e_var_f x) Inf A
 | Typ_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ),
      ( forall x , x \notin  L  -> Typing  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
     Typing G (e_abs A e B) Inf (t_arrow A B)
 | Typ_app : forall (G:ctx) (e1 e2:exp) (A1 A2 A:typ),
    pattern A (t_arrow A1 A2) ->
    Typing G e1 Inf A ->
    Typing G e2 Chk A1 ->
    Typing G (e_app e1 e2) Inf A2
 | Typ_add : forall (G:ctx),
     uniq  G  ->
     Typing G e_add Inf (t_arrow t_int  (t_arrow t_int t_int) )
 | Typ_addl : forall (G:ctx) (i1:i),
     uniq  G  ->
     Typing G (e_addl i1) Inf (t_arrow t_int t_int)
 | Typ_anno : forall (G:ctx) (e:exp) (A:typ),
     Typing G e Chk A ->
     Typing G  ( (e_anno e A) )  Inf A
 | Typ_sim : forall (G:ctx) (e:exp) (B A:typ),
     Typing G e Inf A ->
     sim A B ->
     Typing G e Chk B
 | Typ_pro : forall (G:ctx) (e1 e2:exp) (A1 A2:typ),
     Typing G e1 Inf A1 ->
     Typing G e2 Inf A2 ->
     Typing G (e_pro e1 e2) Inf (t_pro A1 A2)
 | Typ_l : forall (G:ctx) (e:exp) (A A1 A2:typ),
     Typing G e Inf A ->
     pattern_pro A (t_pro A1 A2) ->
     Typing G (e_l e) Inf A1
 | Typ_r : forall (G:ctx) (e:exp) (A A1 A2:typ),
     Typing G e Inf A ->
     pattern_pro A (t_pro A1 A2) ->
     Typing G  (e_r e)  Inf A2
.


Inductive ttyping : ctx -> exp -> dirflag -> typ -> term -> Prop :=    (* defn Typing *)
 | ttyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     ttyping G (e_lit i5) Inf t_int (trm_lit i5)
 | ttyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     ttyping G (e_var_f x) Inf A (trm_var_f x)
 | ttyp_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ) (t:term),
      ( forall x , x \notin  L  -> ttyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B ( open_term_wrt_term t (trm_var_f x) ))  ->
     ttyping G (e_abs A e B) Inf (t_arrow A B) (trm_abs A t)
 | ttyp_app : forall (G:ctx) (e1 e2:exp) (B A:typ) (t1 t2:term),
     ttyping G e1 Inf (t_arrow A B) t1 ->
     ttyping G e2 Chk A t2 ->
     ttyping G (e_app e1 e2) Inf B (trm_app t1 t2)
 | ttyp_add : forall (G:ctx),
      uniq  G  ->
     ttyping G e_add Inf (t_arrow t_int  (t_arrow t_int t_int) ) trm_add
 | ttyp_addl : forall (G:ctx) (i1:i),
      uniq  G  ->
     ttyping G (e_addl i1) Inf (t_arrow t_int t_int) (trm_addl i1)
 | ttyp_anno : forall (G:ctx) (e:exp) (A:typ) (t:term),
     ttyping G e Chk A t ->
     ttyping G  ( (e_anno e A) )  Inf A t
 | ttyp_sim : forall (G:ctx) (e:exp) (B A:typ) (t:term),
     ttyping G e Inf A t ->
     sim A B ->
     ttyping G e Chk B (trm_cast t A B)
 | ttyp_appd : forall (G:ctx) (e1 e2:exp) (t1 t2:term),
     ttyping G e1 Inf t_dyn t1 ->
     ttyping G e2 Chk t_dyn t2 ->
     ttyping G (e_app e1 e2) Inf t_dyn (trm_app (trm_cast t1 t_dyn (t_arrow t_dyn t_dyn)) t2).


Inductive ctx_item : Type :=
     | appCtxL : exp -> ctx_item
     | appCtxR : exp -> ctx_item
     | annoCtx : typ -> ctx_item
     | proCtxL : exp -> ctx_item
     | proCtxR : exp -> ctx_item
     | lCtx : ctx_item
     | rCtx : ctx_item.


Inductive wellformed : ctx_item -> Prop :=
     | wf_appCtxL : forall (e : exp),
                   lc_exp e ->
                    wellformed (appCtxL e)
     | wf_appCtxR : forall (v : exp) A B,
                    dynamic_type v = (t_arrow A B) ->
                    value v ->
                    wellformed (appCtxR v)
     | wf_annoCtx : forall (A : typ),
                    wellformed (annoCtx A)
     | wf_proCtxL : forall (e : exp),
                    lc_exp e ->
                     wellformed (proCtxL e)
      | wf_proCtxR : forall (v : exp),
                     value v ->
                     wellformed (proCtxR v)
      | wf_lCtx : 
                     wellformed (lCtx)
      | wf_rCtx : 
                     wellformed (rCtx)
.
   

Definition fill (E : ctx_item) (e : exp) : exp :=
     match E with
     | appCtxL e2 => e_app e e2
     | appCtxR v1 => e_app v1 e
     | annoCtx A => e_anno e A
     | proCtxL e2 => e_pro e e2
     | proCtxR v1 => e_pro v1 e
     | lCtx => e_l e 
     | rCtx => e_r e 
     end.

   
Inductive res : Type :=
     | e_exp  : exp -> res
     | e_blame : res.    


Definition UG A B := sim A B /\ Ground B /\ not(A = B) /\ not(A = t_dyn).

(* defns Semantics *)
Inductive Cast : exp -> typ -> res -> Prop :=    (* defn Cast *)
 | Cast_abs: forall v A B C D,
   sim (t_arrow C D) (t_arrow A B) ->
   dynamic_type v = (t_arrow C D) ->
   Cast v (t_arrow A B) (e_exp (e_anno v (t_arrow A B)))
  | Cast_v : forall (v:exp),
   Ground(dynamic_type v) ->
   Cast v t_dyn (e_exp (e_anno v t_dyn))
 | Cast_lit : forall (i5:i),
     Cast (e_lit i5) t_int (e_exp (e_lit i5))
 | Cast_dd : forall (v:exp),
     lc_exp v ->
     Cast  ( (e_anno v t_dyn) )  t_dyn  (e_exp  (e_anno v t_dyn) ) 
 | Cast_anyd : forall (v:exp) B v',
      UG (dynamic_type v) B ->
      Cast v B (e_exp v') ->
     Cast v t_dyn  (e_exp (e_anno v' t_dyn) ) 
 | Cast_dyna : forall (v:exp) (A:typ) B r,
    UG A B ->
    Cast v A r ->
    Cast  ( (e_anno v t_dyn) )  A  r
 | Cast_vany : forall (v:exp),
   Cast (e_anno v t_dyn) (dynamic_type  v) (e_exp v)
 | Cast_blame : forall (v:exp) (A:typ),
      not (sim  (dynamic_type  v) A)  ->
     Cast (e_anno v t_dyn) A e_blame
 | Cast_pro : forall v1 v2 A B v1' v2',
     Cast v1 A (e_exp v1') ->
     Cast v2 B (e_exp v2') ->
     Cast (e_pro v1 v2) (t_pro A B) (e_exp (e_pro v1' v2'))
 | Cast_prol : forall v1 v2 A B r,
     Cast v1 A e_blame ->
     Cast v2 B r ->
     Cast (e_pro v1 v2) (t_pro A B) e_blame
 | Cast_pror : forall v1 v2 A B v1', 
     Cast v1 A (e_exp v1') ->
     Cast v2 B e_blame ->
     Cast (e_pro v1 v2) (t_pro A B) e_blame
.

  
Inductive step : exp -> res -> Prop :=    (* defn step *)
  | Step_eval E e1 e2 :
       wellformed E ->
       step e1 (e_exp e2 ) ->
      step (fill E e1) (e_exp (fill E e2))
  | Step_blame E e1:
      wellformed E ->
      step e1 e_blame ->
      step (fill E e1) e_blame
 | Step_beta : forall (A:typ) (e:exp) (B:typ) (v v' : exp),
    lc_exp (e_abs A e B) ->
    value v ->
    Cast v A (e_exp v') ->
    step (e_app (e_abs A e B) v)  (e_exp (e_anno (open_exp_wrt_exp  e v' ) B) )  
 | Step_betap : forall (v1:exp) (A B:typ) (v2 :exp),
    value v1  ->
    dynamic_type v1 = t_arrow A B ->
    Cast v2 A e_blame ->
    value v2 ->
    step (e_app v1 v2) e_blame
 | Step_annov : forall (v:exp) (A:typ) (v':res),
     value v ->
     Cast v A v' ->
     not (value (e_anno v A)) -> 
     step (e_anno v A) v'
 | Step_add : forall (v1:exp) (i1:i),
     value v1 ->
     Cast v1 t_int (e_exp (e_lit i1)) ->
     step (e_app e_add v1) (e_exp (e_addl i1))
 | Step_addl : forall (i1:i) (v2:exp) (i2:i),
     value v2 ->
     Cast v2 t_int (e_exp (e_lit i2)) ->
     step (e_app  ( (e_addl i1) )  v2)  (e_exp (e_lit ( i1  +  i2 )))
 | Step_abeta : forall (v1:exp) (C D:typ) (v2 v2':exp) A B,
     value v1  ->
     Cast v2 C (e_exp v2') ->
     value v2 ->
     dynamic_type v1 = t_arrow A B ->
     step (e_app (e_anno v1 (t_arrow C D))  v2) (e_exp (e_anno (e_app v1 v2') D))
 | Step_dyn : forall (v1:exp) (v2:exp),
    value  ( (e_anno v1 t_dyn) )  ->
    step (e_app (e_anno v1 t_dyn) v2) (e_exp (e_app (e_anno (e_anno v1 t_dyn) (t_arrow t_dyn t_dyn)) v2))
 | Step_ld : forall v, 
    value (e_anno v t_dyn) ->
    step (e_l (e_anno v t_dyn)) (e_exp (e_l (e_anno (e_anno v t_dyn) (t_pro t_dyn t_dyn))))
 | Step_rd : forall v, 
    value (e_anno v t_dyn) ->
    step (e_r (e_anno v t_dyn)) (e_exp (e_r (e_anno (e_anno v t_dyn) (t_pro t_dyn t_dyn))))
 | Step_l : forall v1 v2, 
    value v1 ->
    value v2 ->
    step (e_l (e_pro v1 v2)) (e_exp v1)
 | Step_r : forall v1 v2, 
    value v1 ->
    value v2 ->
    step (e_r (e_pro v1 v2)) (e_exp v2)
.


Inductive steps : exp -> res -> Prop :=
  | step_refl e:
    steps e (e_exp e)

  | step_n e t' e':   
    step e (e_exp e') ->
    steps e' (e_exp t') ->
    steps e  (e_exp t')

  | step_nb e e':
    step e (e_exp e') ->
    steps e' e_blame ->
    steps e  e_blame

  | step_b e:
    step e (e_blame) ->
    steps e (e_blame).

(** infrastructure *)
Hint Constructors pattern pattern_pro Ground value sim Cast step steps wellformed Typing ttyping lc_exp : core.

