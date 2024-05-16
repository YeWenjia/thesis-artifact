Require Import Bool.
Require Import Metalib.Metatheory.
Require Import List.
Require Import syntax_ott.
Require Import syntaxb_ott.



Inductive eexp : Set :=  (*r eexpressions *)
 | ee_var_b (_:nat) (*r variables *)
 | ee_var_f (x:var) (*r variables *)
 | ee_lit (i5:i) (*r lit *)
 | ee_abs (t1: typ) (e:eexp) (p:var) (b:bool) (t2: typ) (*r abstractions *)
 | ee_app (e1:eexp) (p:var) (b:bool) (e2:eexp) (*r applications *)
 | ee_anno (e:eexp) (p:var) (b:bool) (A:typ) (*r annotation *)
 | ee_add : eexp (*r addition *)
 | ee_addl (i5:i) (*r addl *)
 | ee_pro  (e1:eexp) (e2: eexp) : eexp
 | ee_l (e1:eexp) (p:var) (b:bool) : eexp
 | ee_r (e1:eexp) (p:var) (b:bool): eexp.


 Inductive dirflag2 : Set :=  (*r checking direction *)
 | Inf2 : dirflag2
 | Chk2 (p:var) (b:bool) (A:typ): dirflag2.


 Fixpoint open_eexp_wrt_eexp_rec (k:nat) (e_5:eexp) (e__6:eexp) {struct e__6}: eexp :=
  match e__6 with
  | (ee_var_b nat) => 
      match lt_eq_lt_dec nat k with
        | inleft (left _) => ee_var_b nat
        | inleft (right _) => e_5
        | inright _ => ee_var_b (nat - 1)
      end
  | (ee_var_f x) => ee_var_f x
  | (ee_lit i5) => ee_lit i5
  | (ee_abs t1 e l b t2) => ee_abs t1 (open_eexp_wrt_eexp_rec (S k) e_5 e) l b t2
  | (ee_app e1 p b e2) => ee_app (open_eexp_wrt_eexp_rec k e_5 e1) p b (open_eexp_wrt_eexp_rec k e_5 e2)
  | (ee_anno e p b A) => ee_anno (open_eexp_wrt_eexp_rec k e_5 e) p b A
  | ee_add => ee_add 
  | (ee_addl i5) => ee_addl i5
  | (ee_pro e1 e2) => ee_pro (open_eexp_wrt_eexp_rec k e_5 e1)  (open_eexp_wrt_eexp_rec k e_5 e2)
  | (ee_l e1 l b ) => ee_l (open_eexp_wrt_eexp_rec k e_5 e1) l b 
  | (ee_r e2 l b ) => ee_r (open_eexp_wrt_eexp_rec k e_5 e2) l b 
end.

Definition open_eexp_wrt_eexp e_5 e__6 := open_eexp_wrt_eexp_rec 0 e__6 e_5.



Inductive lc_eexp : eexp -> Prop :=    (* defn lc_eexp *)
 | lc_ee_var_f : forall (x:var),
     (lc_eexp (ee_var_f x))
 | lc_ee_lit : forall (i5:i),
     (lc_eexp (ee_lit i5))
 | lc_ee_abs : forall (e:eexp) l b t1 t2 ,
      ( forall x , lc_eexp  ( open_eexp_wrt_eexp e (ee_var_f x) )  )  ->
     (lc_eexp (ee_abs t1 e l b t2))
 | lc_ee_app : forall (e1 e2:eexp) p b ,
     (lc_eexp e1) ->
     (lc_eexp e2) ->
     (lc_eexp (ee_app e1 p b e2))
 | lc_ee_anno : forall (e:eexp)  (p:var) (A:typ) b,
     (lc_eexp e) ->
     (lc_eexp (ee_anno e p b A))
 | lc_ee_add : 
     (lc_eexp ee_add)
 | lc_ee_addl : forall (i5:i),
     (lc_eexp (ee_addl i5))
 | lc_ee_pro : forall (e1 e2:eexp) ,
     (lc_eexp e1) ->
     (lc_eexp e2) ->
     (lc_eexp (ee_pro e1 e2))
 | lc_ee_l : forall (e1:eexp) l b,
     (lc_eexp e1) ->
     (lc_eexp (ee_l e1 l b))
 | lc_ee_r : forall (e1:eexp) l b,
     (lc_eexp e1) ->
     (lc_eexp (ee_r e1 l b)).

(** free variables *)
Fixpoint fv_eexp (e_5:eexp) : vars :=
  match e_5 with
  | (ee_var_b nat) => {}
  | (ee_var_f x) => {{x}}
  | (ee_lit i5) => {}
  | (ee_abs t1 e l b t2) => (fv_eexp e)
  | (ee_app e1 p b e2) => (fv_eexp e1) \u (fv_eexp e2)
  | (ee_anno e p b A) => (fv_eexp e)
  | ee_add => {}
  | (ee_addl i5) => {}
  | (ee_pro e1 e2) => (fv_eexp e1) \u (fv_eexp e2)
  | (ee_l e1 l  b) => (fv_eexp e1)
  | (ee_r e1 l b) => (fv_eexp e1)
end.

(** substitutions *)
Fixpoint subst_eexp (ee_5:eexp) (x5:var) (e__6:eexp) {struct e__6} : eexp :=
  match e__6 with
  | (ee_var_b nat) => ee_var_b nat
  | (ee_var_f x) => (if eq_var x x5 then ee_5 else (ee_var_f x))
  | (ee_lit i5) => ee_lit i5
  | (ee_abs t1 e l b t2) => ee_abs t1 (subst_eexp ee_5 x5 e) l b t2
  | (ee_app e1 p b e2) => ee_app (subst_eexp ee_5 x5 e1) p b (subst_eexp ee_5 x5 e2)
  | (ee_anno e p b A) => ee_anno (subst_eexp ee_5 x5 e) p b A
  | ee_add => ee_add 
  | (ee_addl i5) => (ee_addl i5)
  | (ee_pro e1 e2) => ee_pro (subst_eexp ee_5 x5 e1) (subst_eexp ee_5 x5 e2)
  | (ee_l e1 l b ) => ee_l (subst_eexp ee_5 x5 e1) l b
  | (ee_r e1 l b) => ee_r (subst_eexp ee_5 x5 e1) l b 
end.


(* 
Fixpoint erase (e:eexp) : exp :=
  match e with
  | (ee_var_b nat) => 
                        e_var_b nat
  | (ee_var_f x) => (e_var_f x)
  | (ee_lit i5) => (e_lit i5)
  | (ee_anno e p b A) => (e_anno (erase e) A)
  | (ee_abs t1 e l b t2) => (e_abs t1 (erase e) t2)
  | (ee_add) => e_add
  | (ee_app e1 p b e2) => e_app (erase e1) (erase e2)
  | (ee_addl i5) => e_addl i5
  | (ee_pro e1 e2) => e_pro (erase e1) (erase e2)
  | (ee_l e1 l b) => e_l (erase e1) 
  | (ee_r e1 l b) => e_r (erase e1) 
  end. *)



Inductive erase : eexp -> exp -> Prop :=
  | er_x : forall x,
    erase (ee_var_f x) (e_var_f x)
  | er_i : forall i5,
    erase (ee_lit i5) (e_lit i5)
  | er_anno: forall e e' A p b,
    erase e e' ->
    erase (ee_anno e p b A) (e_anno e' A)
  | er_abs: forall L e e' t1 t2 l b ,
     (forall x, x \notin L -> erase (open_eexp_wrt_eexp e (ee_var_f x)) (open_exp_wrt_exp e' (e_var_f x))) -> 
     erase (ee_abs t1 e l b t2) (e_abs t1 e' t2)
  | er_add:
    erase (ee_add) e_add
  | er_app: forall e1 e2 p b e1' e2',
     erase e1 e1' ->
     erase e2 e2' ->
     erase (ee_app e1 p b e2) (e_app e1' e2')
  | er_addl: forall i5,
    erase (ee_addl i5) (e_addl i5)
  | er_pro: forall e1 e1' e2 e2',
    erase e1 e1' -> 
    erase e2 e2' ->
    erase (ee_pro e1 e2) (e_pro e1' e2')
  | er_l: forall e1 e1' l b,
    erase e1 e1' ->
    erase (ee_l e1 l b) (e_l e1') 
  | er_r: forall e1 e1' l b,
    erase e1 e1' ->
    erase (ee_r e1 l b) (e_r e1') 
.




Inductive TTyping : ctx -> eexp -> dirflag -> typ -> Prop :=    (* defn TTyping *)
 | TTyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     TTyping G (ee_lit i5) Inf t_int
 | TTyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     TTyping G (ee_var_f x) Inf A
 | TTyp_abs : forall (L:vars) (G:ctx) (A:typ) (e:eexp) (B:typ) l b,
      ( forall x , x \notin  L  -> TTyping  (cons ( x , A )  G )   ( open_eexp_wrt_eexp e (ee_var_f x) )  Chk B )  ->
     TTyping G (ee_abs A e l b B) Inf (t_arrow A B)
 | TTyp_app : forall (G:ctx) (e1 e2:eexp) (A1 A2 A:typ) l b,
     pattern A (t_arrow A1 A2) ->
     TTyping G e1 Inf A ->
     TTyping G e2 Chk A1 ->
     TTyping G (ee_app e1 l b e2) Inf A2
 | TTyp_anno : forall (G:ctx) (e:eexp) (p:var) b (A:typ),
     TTyping G e Chk A ->
     TTyping G  ( (ee_anno e p b A) )  Inf A
 | TTyp_sim : forall (G:ctx) (e:eexp) (B A:typ),
     TTyping G e Inf A ->
     sim A B ->
     TTyping G e Chk B
 | TTyp_add : forall (G:ctx),
     uniq  G  ->
     TTyping G ee_add Inf (t_arrow t_int  (t_arrow t_int t_int) )
 | TTyp_addl : forall (G:ctx) (i1:i),
     uniq  G  ->
     TTyping G (ee_addl i1) Inf (t_arrow t_int t_int)
 | TTyp_pro : forall (G:ctx) (e1 e2:eexp) (A1 A2:typ),
     TTyping G e1 Inf A1 ->
     TTyping G e2 Inf A2 ->
     TTyping G (ee_pro e1 e2) Inf (t_pro A1 A2)
 | TTyp_l : forall (G:ctx) (e:eexp) (A A1 A2:typ) l b,
     TTyping G e Inf A ->
     pattern_pro A (t_pro A1 A2) ->
     TTyping G (ee_l e l b) Inf A1
 | Typ_r : forall (G:ctx) (e:eexp) (A A1 A2:typ) l b,
     TTyping G e Inf A ->
     pattern_pro A (t_pro A1 A2) ->
     TTyping G  (ee_r e l b)  Inf A2.

Inductive rres : Type :=
     | ee_exp  : eexp -> rres
     | ee_blame : var -> bool -> rres.  

(* Fixpoint eraser (r:rres) : res :=
  match r with
  | (ee_exp e) => e_exp (erase e)
  | ee_blame l b => e_blame
  end. *)


Inductive eraser : rres -> res -> Prop :=
  | err_e : forall e e',
     erase e e' ->
     eraser (ee_exp e) (e_exp  e')
  |err_b: forall l b,
     eraser (ee_blame l b) (e_blame)
.


Inductive cctx_item : Type :=
     | eappCtxL : eexp -> var -> bool -> cctx_item
     | eappCtxR : eexp -> var -> bool -> cctx_item
     | eannoCtx : var -> bool -> typ -> cctx_item
     | eproCtxL : eexp  -> cctx_item
     | eproCtxR : eexp  -> cctx_item
     | elCtx :  var -> bool ->cctx_item
     | erCtx :  var -> bool ->cctx_item
     .

Fixpoint pdynamic_type (v:eexp) : typ :=
  match v with
  | (ee_lit i5) => t_int
  | (ee_anno e p b A) => A
  | (ee_abs t1 e l b t2) => (t_arrow t1 t2)
  | (ee_add) => (t_arrow t_int (t_arrow t_int t_int))
  | (ee_addl i5) => (t_arrow t_int t_int)
  | (ee_pro v1 v2) => (t_pro (pdynamic_type v1) (pdynamic_type v2))
  | _ => t_dyn
  end.

(* defns Values *)
Inductive evalue : eexp -> Prop :=    (* defn value *)
 | evalue_lit : forall (i5:i),
     evalue (ee_lit i5)
 | evalue_abs : forall e l b t1 t2,
     lc_eexp (ee_abs t1 e l b t2) ->
     evalue (ee_abs t1 e l b t2)
 | evalue_fanno : forall (v:eexp) (A B C D:typ) (p:var) b,
     evalue v ->
      (t_arrow C D)  =   (pdynamic_type   ( v )  )   ->
     evalue (ee_anno v p b (t_arrow A B))
 | evalue_dyn : forall (v:eexp) (p:var) b,
     Ground   (pdynamic_type  v )   ->
     evalue v ->
     evalue  ( (ee_anno v p b t_dyn) )
 | evalue_add : 
     evalue ee_add
 | evalue_addl : forall (i5:i),
     evalue  ( (ee_addl i5) )
 | evalue_pro : forall v1 v2,
     evalue v1 ->
     evalue v2 ->
     evalue  ( (ee_pro v1 v2) ).

   
Inductive wwellformed : cctx_item -> Prop :=
     | wwf_appCtxL : forall (e : eexp) p b,
                   lc_eexp e ->
                    wwellformed (eappCtxL e p b )
     | wwf_appCtxR : forall (v : eexp) p b A B,
                    pdynamic_type v = (t_arrow A B) ->
                    evalue v ->
                    wwellformed (eappCtxR v p b)
     | wwf_annoCtx : forall (A : typ)  (p:var) b,
                    wwellformed (eannoCtx p b A)
     | wwf_proCtxL : forall (e : eexp) ,
                    lc_eexp e ->
                     wwellformed (eproCtxL e )
     | wwf_proCtxR : forall (e : eexp) ,
                     evalue e ->
                      wwellformed (eproCtxR e )
     | wwf_lCtx : forall l b,
                     wwellformed (elCtx l b)
     | wwf_rCtx : forall l b,
                     wwellformed (erCtx l b).
   
Definition ffill (E : cctx_item) (e : eexp) : eexp :=
     match E with
     | eappCtxL e2 p b  => ee_app e p b e2
     | eappCtxR v1 p b => ee_app v1 p b e
     | eannoCtx p b A => ee_anno e p b A
     | eproCtxL e2   => ee_pro e e2
     | eproCtxR v1  => ee_pro v1 e
     | elCtx l b => ee_l e l b
     | erCtx  l b => ee_r e l b 
     end.



Inductive CCast : eexp -> var -> bool -> typ -> rres -> Prop :=    (* defn CCast *)
 | CCast_abs: forall v A B C D p b,
   sim (t_arrow C D) (t_arrow A B) ->
   pdynamic_type v = (t_arrow C D) ->
   CCast v p b (t_arrow A B) (ee_exp (ee_anno v p b (t_arrow A B)))
  | CCast_v : forall (v:eexp)  (p:var) b,
   Ground(pdynamic_type v) ->
   CCast v p b t_dyn (ee_exp (ee_anno v p b t_dyn))
 | CCast_lit : forall (i5:i) b (p:var),
     CCast (ee_lit i5) p b t_int (ee_exp (ee_lit i5))
 | CCast_dd : forall (v:eexp) (p:var) (q:var) b1 b2,
     lc_eexp v ->
     CCast  ( (ee_anno v q b1 t_dyn) ) p b2 t_dyn  (ee_exp  (ee_anno v q b1 t_dyn) ) 
 | CCast_anyd : forall (v:eexp) (p:var) b v' B,
      UG (pdynamic_type v) B ->
      CCast v p b B (ee_exp v') ->
     CCast v p b t_dyn  (ee_exp (ee_anno v' p b t_dyn) ) 
 | CCast_dyna : forall (v:eexp) (A:typ) (p:var) b1 b2 (q:var) B r,
     UG A B ->
     CCast v p b2 A r ->
    CCast  ( (ee_anno v q b1 t_dyn) ) p b2 A r
 | CCast_vany : forall (v:eexp) (p:var)  (q:var) b1 b2,
   CCast (ee_anno v q b1 t_dyn) p b2 (pdynamic_type  v) (ee_exp v)
 | CCast_blame : forall (v:eexp) (A:typ) (p:var) b1 b2 (q:var),
      not (sim (pdynamic_type  v ) A)  ->
     CCast (ee_anno v q b1 t_dyn) p b2 A (ee_blame p b2)
 | CCast_pro : forall v1 v2 A B v1' v2' p b,
     CCast v1 p b A (ee_exp v1') ->
     CCast v2 p b B (ee_exp v2') ->
     CCast (ee_pro v1 v2) p b (t_pro A B) (ee_exp (ee_pro v1' v2'))
 | CCast_prol : forall v1 v2 A B p b r,
     CCast v1 p b A (ee_blame p b) ->
     CCast v2 p b B r ->
     CCast (ee_pro v1 v2) p b (t_pro A B) (ee_blame p b)
 | CCast_pror : forall v1 v2 A B p b v1',
     CCast v1 p b A (ee_exp v1') ->
     CCast v2 p b B (ee_blame p b) ->
     CCast (ee_pro v1 v2) p b (t_pro A B) (ee_blame p b)
.




Inductive sstep : eexp -> rres -> Prop :=    (* defn step *)
  | sStep_eval E e1 e2 : 
       wwellformed E ->
       sstep e1 (ee_exp e2 ) ->
      sstep (ffill E e1) (ee_exp (ffill E e2))
  | sStep_blame E e1 l b:
      wwellformed E ->
      sstep e1 (ee_blame l b) ->
      sstep (ffill E e1) (ee_blame l b)
 | sStep_beta : forall (A:typ) (e:eexp) (B:typ) (v : eexp) l1 b1 l2 b2 v',
    lc_eexp (ee_abs A e l1 b1 B) ->
    evalue v ->
    CCast v l2 b2 A (ee_exp v') ->
    sstep (ee_app (ee_abs A e l1 b1 B) l2 b2 v)  (ee_exp (ee_anno  (  (open_eexp_wrt_eexp  e v' )  )  l1 b1 B) )
 | sStep_betap : forall (A:typ) (e:eexp) (B:typ) v1 v2 l1 b1,
    evalue  v1  ->
    evalue v2 ->
    pdynamic_type (v1) = (t_arrow A B) ->
    CCast v2 l1 b1 A (ee_blame l1 b1) ->
    sstep (ee_app v1 l1 b1 v2)  (ee_blame l1 b1)
 | sStep_annov : forall (v:eexp) (A:typ) (v':rres) (l:var) b,
     evalue v ->
     CCast v l b A v' ->
     not (evalue (ee_anno v l b A)) -> 
     sstep (ee_anno v l b A) v'
 | sStep_abeta : forall (v1:eexp) (A B:typ) (v2 :eexp) l1 b1 v2' l b C D,
     evalue  ( v1 )  ->
     evalue v1 ->
     evalue v2 ->     
     CCast v2 l b A (ee_exp v2') ->
     pdynamic_type (v1) = (t_arrow C D) ->
     sstep (ee_app (ee_anno v1 l1 b1 (t_arrow A B)) l b v2) (ee_exp (ee_anno (ee_app v1 l1 (negb b1) v2' ) l1 b1 B))
 | sStep_dyn : forall (v1:eexp) (v2:eexp) l1 b1 l2 b2 ,
    evalue  ( (ee_anno v1 l1 b1 t_dyn) )  ->
    lc_eexp v2 ->
    sstep (ee_app (ee_anno v1 l1 b1 t_dyn) l2 b2 v2) (ee_exp (ee_app (ee_anno (ee_anno v1 l1 b1 t_dyn) l2 b2 (t_arrow t_dyn t_dyn)) l2 b2 v2))
 | sStep_ld : forall v p b l2 b2, 
    evalue (ee_anno v p b t_dyn) ->
    sstep (ee_l (ee_anno v p b t_dyn) l2 b2) (ee_exp (ee_l (ee_anno (ee_anno v p b t_dyn) p b (t_pro t_dyn t_dyn)) l2 b2))
 | sStep_rd : forall v p b l2 b2, 
    evalue (ee_anno v p b  t_dyn) ->
    sstep (ee_r (ee_anno v p b t_dyn) l2 b2) (ee_exp (ee_r (ee_anno (ee_anno v p b t_dyn) l2 b2 (t_pro t_dyn t_dyn)) l2 b2))
 | sStep_l : forall v1 v2 l b, 
    evalue v1 ->
    evalue v2 ->
    sstep (ee_l (ee_pro v1 v2) l b) (ee_exp v1)
 | sStep_r : forall v1 v2 l b, 
    evalue v1 ->
    evalue v2 ->
    sstep (ee_r (ee_pro v1 v2) l b) (ee_exp v2)
 | sStep_add : forall (v1:eexp) (i1:i) l b,
     evalue v1 ->
     CCast v1 l b t_int (ee_exp (ee_lit i1)) ->
     sstep (ee_app ee_add l b v1) (ee_exp (ee_addl i1))
 | sStep_addl : forall (i1:i) (v2:eexp) (i2:i) l b,
     evalue v2 ->
     CCast v2 l b t_int (ee_exp (ee_lit i2)) ->
     sstep (ee_app  ( (ee_addl i1) ) l b  v2)  (ee_exp (ee_lit ( i1  +  i2 )))
.

Hint Constructors erase eraser sstep  wwellformed evalue TTyping lc_eexp CCast : core.