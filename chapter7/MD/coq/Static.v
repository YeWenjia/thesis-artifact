Require Import LibTactics.
Require Import syntax_ott
    rules_inf
    Infrastructure
    Key_Properties
    Typing
    Deterministic.


Inductive dtyp_static : typ -> Prop :=
 | dtyp_static_bot:
      dtyp_static t_bot
  | dtyp_static_top:
      dtyp_static t_top
  | dtyp_static_nat:
      dtyp_static t_int
  | dtyp_static_arrow: forall A B,
      dtyp_static A ->
      dtyp_static B ->
      dtyp_static (t_arrow A B)
  | dtyp_and: forall A B,
      dtyp_static A ->
      dtyp_static B ->
      dtyp_static (t_and A B)
  | dtyp_rcd: forall l A ,
      dtyp_static A ->
      dtyp_static (t_rcd l A)  
.

Inductive dexp_static : exp -> Prop :=
  | dexp_static_var: forall x,
      dexp_static (e_var_f x)
  | dexp_static_nat : forall i,
      dexp_static (e_lit i)
  | dexp_static_top : 
      dexp_static (e_top)
  | dexp_static_abs : forall L e1,
      (forall x, x \notin L -> dexp_static (open_exp_wrt_exp e1 (e_var_f x))) ->
      dexp_static (e_abs e1)
  | dexp_static_app : forall e1 e2,
      dexp_static e1 ->
      dexp_static e2 ->
      not(exists e, e1 = (e_abs e)) ->
      dexp_static (e_app e1 e2)
  | dexp_static_merge : forall e1 e2,
      dexp_static e1 ->
      dexp_static e2 ->
      dexp_static (e_merge e1 e2)
  | dexp_static_anno : forall e A,
      dexp_static e ->
      dtyp_static A ->
      dexp_static (e_anno e A)
  | dexp_static_rcd : forall l e,
      dexp_static e ->
      dexp_static (e_rcd l e)
  | dexp_static_proj : forall l e,
      dexp_static e ->
      dexp_static (e_proj e l)   
  | dexp_static_fix : forall e L,
     (forall x, x \notin L -> dexp_static (open_exp_wrt_exp e (e_var_f x))) ->
      dexp_static (e_fixpoint e) 
.


Inductive denv_static : ctx -> Prop :=
  | denv_static_empty : denv_static nil
  | denv_static_typ : forall E x T,
      denv_static E ->
      dtyp_static T ->
      denv_static ((x, T) :: E).


Inductive dsub : typ -> typ -> Prop :=    (* defn dsub *)
 | dS_z : 
     dsub t_int t_int
 | dS_top : forall (A:typ),
     dtyp_static A ->
     dsub A t_top
 | dS_bot : forall (A:typ),
     dtyp_static A ->
     dsub t_bot A
 | dS_arr : forall (A1 A2 B1 B2:typ),
     dsub B1 A1 ->
     dsub A2 B2 ->
     dsub (t_arrow A1 A2) (t_arrow B1 B2)
 | dS_andl1 : forall (A1 A2 A3:typ),
     dsub A1 A3 ->
     dtyp_static A2 ->
     dsub (t_and A1 A2) A3
 | dS_andl2 : forall (A1 A2 A3:typ),
     dsub A2 A3 ->
     dtyp_static A1 ->
     dsub (t_and A1 A2) A3
 | dS_andr : forall (A1 A2 A3:typ),
     dsub A1 A2 ->
     dsub A1 A3 ->
     dsub A1 (t_and A2 A3)
 | dS_rcd : forall l (C D:typ),
     dsub C D ->
     dsub (t_rcd l C) (t_rcd l D)
.


Inductive dtyping : ctx -> exp -> dirflag -> typ -> Prop :=    (* defn dtyping *)
 | dtyp_top : forall (G:ctx),
      uniq  G  ->
     dtyping G e_top Inf t_top
 | dtyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     dtyping G (e_lit i5) Inf t_int
 | dtyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
      dtyp_static A ->
      (* well A -> *)
     dtyping G (e_var_f x) Inf A
 | dtyp_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ),
      ( forall x , x \notin  L  -> dtyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
      dtyp_static A ->
      well A ->
      dtyping G (e_abs e) Chk (t_arrow A B)
 | dtyp_app : forall (G:ctx) (e1 e2:exp) (B A:typ),
     dtyping G e1 Inf (t_arrow A B) ->
     dtyping G e2 Chk A ->
     dtyping G (e_app e1 e2) Inf B
 | dtyp_merge : forall (G:ctx) (e1 e2:exp) (A B:typ),
     dtyping G e1 Inf A ->
     dtyping G e2 Inf B ->
     syntax_ott.disjoint  A B  ->
     dtyping G (e_merge e1 e2) Inf (t_and A B)
 | dtyp_anno : forall (G:ctx) (e:exp) (A:typ),
     dtyping G e Chk A ->
     dtyping G (e_anno e A) Inf A
 | dtyp_proj : forall (G:ctx) (e:exp) l (A:typ) B,
     dtyping G e Inf A ->
     get_ty A l B ->
     dtyping G (e_proj e l) Inf B
 | dtyp_rec : forall (G:ctx) l (e:exp) (A:typ),
     dtyping G e Inf A ->
     dtyping G (e_rcd l e) Inf (t_rcd l A)
 | dtyp_sub : forall (G:ctx) (e:exp) (B A:typ),
     dtyping G e Inf A ->
     dsub A B ->
     dtyp_static B ->
     well B ->
     dtyping G e Chk B
 | dtyp_fix : forall (L:vars) (G:ctx) (A:typ) (e:exp),
      ( forall x , x \notin  L  -> dtyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk A )  ->
      well A ->
     dtyping G (e_fixpoint e) Chk A.


(* defns Reductions *)
Inductive dstep : exp -> exp -> Prop :=    (* defn dstep *)
 | dstep_eval E e1 e2 :
    wellformed E ->
    dstep e1 (e2 ) ->
    dstep (fill E e1) (fill E e2)
 | dstep_beta : forall (A:typ) (e:exp) (B :typ) v,
     lc_exp (e_abs e) ->
     value v ->
     dstep (e_app (e_abs e)  v)  ((open_exp_wrt_exp  e v))
 | dStep_app : forall (A2:typ) e1 e2 A1,
      fvalue (e_anno e1 (t_arrow A1 A2)) ->
     dstep (e_app (e_anno e1 (t_arrow A1 A2)) e2) (e_anno (e_app e1 (e_anno e2 A1)) A2)
 | dstep_annov : forall v A v1,
     value v ->
     Cast v A (r_e v1) ->
     NotVal (e_anno v A) ->
     dstep (e_anno v A) v1
 | dstep_proj : forall l v v' A,
     value v ->
     get_ty (principal_type v) l A ->
     Cast v (t_rcd l A) (r_e (e_rcd l v')) ->
     dstep (e_proj v l) v'
 | dstep_fix : forall (A:typ) (e:exp),
     lc_exp (e_fixpoint e) ->
     dstep  (e_anno (e_fixpoint e) A)  (e_anno  (  (open_exp_wrt_exp  e  ( (e_anno (e_fixpoint e) A) )  )  )  A).


Hint Constructors dtyping dexp_static dtyp_static   denv_static  dsub dstep : core.


Lemma dtyping_weaken : forall G E F e dir T,
    dtyping (E ++ G) e dir T ->
    uniq (E ++ F ++ G) ->
    dtyping (E ++ F ++ G) e dir T.
Proof.
  introv Typ; gen F;
    inductions Typ; introv Ok; autos*.
    + (* abs *)
      pick fresh x and apply dtyp_abs; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
    + (* abs *)
      pick fresh x and apply dtyp_fix; eauto.
      rewrite_env (([(x, A)] ++ E) ++ F ++ G).
      apply~ H0.
      solve_uniq.
Qed.

Lemma dtyping_weakening : forall (E F : ctx) e dir T,
    dtyping E e dir T ->
    uniq (F ++ E) ->
    dtyping (F ++ E) e dir T.
Proof.
  intros.
  rewrite_env (nil ++ F ++ E).
  apply~ dtyping_weaken.
Qed.


Lemma dtyping_regular_1 : forall e G dir A,
    dtyping G e dir A -> lc_exp e.
Proof.
  intros e G dir A H.
  inductions H;
    eauto.
Qed.

Lemma toplike_dsub: forall A B,
 dsub A B ->
 topLike A ->
 topLike B.
Proof.
 introv dsub tl.
 inductions dsub; try solve[inverts* tl];eauto.
Qed.


(* Lemma topLike_dtyp_static: forall A,
 topLike A ->
 dtyp_static A.
Proof.
 introv tl.
 inductions tl; eauto.
Qed. *)


Lemma dsub_dtyp_static: forall A B,
 dsub A B ->
 dtyp_static A /\ dtyp_static B.
Proof.
 introv dsub.
 inductions dsub; eauto. 
 - destructs~ IHdsub1. destructs~ IHdsub2.
 - destructs~ IHdsub.
 - destructs~ IHdsub.
 - destructs~ IHdsub1. destructs~ IHdsub2.
 - destructs~ IHdsub.
Qed.


Lemma dsub_transtivity : forall B A,
      dsub A B -> forall C, dsub B C -> dsub A C.
Proof.
  induction B;
    intros;
    eauto;
    try solve [dependent induction H;
               eauto].
  - inductions H0; eauto.
    inductions H; eauto.
  - inductions H0; eauto.
  - inductions H; eauto.
  - 
    inductions H; eauto.
    inverts H.
    forwards*: dsub_dtyp_static H0.
    clear IHdsub1 IHdsub2.
    inductions H1;eauto.
    forwards*: dsub_dtyp_static H.
    forwards*: dsub_dtyp_static H0.
  - inductions H; eauto.
    forwards*: dsub_dtyp_static H0.
    clear IHdsub1 IHdsub2.
    inductions H1;eauto.
    forwards*: dsub_dtyp_static H0.
  - inductions H0; eauto. inverts H0.
  - inductions H; eauto. inverts H.
    forwards*: dsub_dtyp_static H0.
    inductions H0; eauto.
    forwards*: dsub_dtyp_static H.
Qed.

Lemma dyn_not_dtyp_static:forall A,
 dynamic A ->
 not(dtyp_static A).
Proof.
    introv dyn.
    inductions dyn; try solve[unfold not; intros nt;inverts* nt].
Qed.


Lemma get_ty_dtyp_static: forall t l t2,
 get_ty t l t2 ->
 dtyp_static t ->
 dtyp_static t2.
Proof.
 introv gt st.
 inductions gt;try solve[inverts* st].
 inductions st; try solve[inverts* H0].
Qed.


Lemma proj_dtyp_static: forall A l B,
 dtyp_static A ->
 proj A l B ->
 dtyp_static B.
Proof.
 introv ts pj.
 inductions pj;eauto.
 - forwards*: get_ty_dtyp_static H.
 - forwards*: dyn_not_dtyp_static H0.
Qed.


Lemma dtyping_regular : forall E e dir T,
    dtyping E e dir T ->
    dexp_static e /\ dtyp_static T.
Proof.
    introv typ.
    inductions typ; 
    try solve[destructs~ IHtyp1; destructs~ IHtyp2];
    try solve[destructs~ IHtyp];eauto.
    - split.
      pick fresh x and apply dexp_static_abs; eauto.
      forwards*: H0 x.
      pick fresh x.
      forwards*: H0 x.
      (* pick fresh x.
      forwards*: H0 x. *)
    - destructs~ IHtyp1. destructs~ IHtyp2. inverts* H0.
      assert(not(exists e', e1 = e_abs e')).
      unfold not;intros nt; inverts nt.
      inverts typ1.
      eauto.
    - destructs~ IHtyp. 
      forwards*: get_ty_dtyp_static H. 
    - split.
      apply dexp_static_fix with L; intros;eauto.
      forwards*: H0 x.
      pick fresh x.
      forwards*: H0 x.
Qed.


Lemma dsub_csub: forall A B,
 dsub A B ->
 csub A B.
Proof.
  introv dsub.
  inductions dsub; eauto.
Qed.


Lemma csub_dsub: forall A B,
 csub A B ->
 dtyp_static A ->
 dtyp_static B ->
 dsub A B.
Proof.
  introv csub st1 st2.
  inductions csub; eauto;
  try solve[inverts* st1];
  try solve[inverts* st2];
  try solve[inverts* st1; inverts* st2].
Qed.


Lemma static_exp_static_typ: forall e,
 value e ->
 dexp_static e ->
 dtyp_static (principal_type e).
Proof.
  introv pval de.
  inductions de; simpl;try solve[inverts* pval];eauto;
  try solve[inverts pval as h1; inverts* h1].
Qed.



Theorem static_dtyping_dyn : forall G e A dir,
 dexp_static e ->
 dtyp_static A ->
 dtyping G e dir A -> 
 Typing G e dir A.
Proof.
  introv es ts typ.
  inductions typ;eauto.
  - inverts ts. inverts es.
    pick fresh x and apply Typ_abs; auto.
  - forwards*: dtyping_regular typ1.
    destructs~ H.
    inverts H0.
    inverts* es.
  - inverts es. inverts ts.
    apply Typ_merge; eauto.
  - inverts* es. 
  - forwards*: dtyping_regular typ.
  - inverts es. inverts* ts.
  - forwards*: dtyping_regular typ.
    destructs~ H2.
    forwards*: dsub_csub H.
  - inverts es.
    pick fresh x and apply Typ_fix; auto.
Qed.


Lemma denv_static_dtyp: forall x A G,
 denv_static G ->
 binds x A G ->
 dtyp_static A.
Proof.
  introv denv bind.
  inductions denv; try solve[inverts* bind];eauto.
  inverts* bind.
  inverts* H0.
Qed.



Lemma Typ_static_exp_static_typ: forall G e A,
  denv_static G ->
  dexp_static e ->
  G ⊢ e ⇒ A ->
  dtyp_static A.
Proof.
 introv sen se typ.
 inductions typ; try solve[inverts* se].
 - forwards*: denv_static_dtyp H0.
 - inverts* se.
   forwards*: IHtyp1 H2. 
   inductions H0; try solve[inverts* H].
 - inverts* se.
   forwards*: IHtyp H1. 
   forwards*: get_ty_dtyp_static H.
Qed.


Lemma dtyp_static_not_ddyn: forall A,
 dtyp_static A ->
 not(ddyn A).
Proof.
  introv st.
  inductions st;
   try solve[unfold not; intros nt; inverts* nt].
Qed.



Definition static_Typing_dyn_aux G e dir A := 
   match e with 
    | (e_app (e_abs e) e2)  => True
    | _ => dtyping G e dir A
   end.



Theorem static_Typing_dyn : forall G e A dir,
 denv_static G ->
 dexp_static e ->
 dtyp_static A ->
 Typing G e dir A -> 
 dtyping G e dir A.
Proof.
  introv env es ts typ.
  inductions typ;eauto.
  - 
    inverts H2; try solve[inverts ts].
    inverts ts. inverts es.
    pick fresh x and apply dtyp_abs; auto.
  - 
    forwards*: Typing_regular_1 typ1.
    inverts* es.
    forwards*: Typ_static_exp_static_typ typ1.
    inverts* H1;inverts* H.
  - inverts es. inverts ts.
    apply dtyp_merge; eauto.
  - inverts* es. 
  -
    inverts es. 
    forwards*: Typ_static_exp_static_typ typ.
  - inverts es. inverts* ts.
  - 
    forwards*: Typ_static_exp_static_typ typ.
    forwards*: csub_dsub H.
  -  inverts es.
    pick fresh x and apply dtyp_fix; auto.
  -
    inverts es.
    exfalso; apply H5; eauto.
Qed.


Lemma dsub_refl: forall A,
 dtyp_static A ->
 dsub A A.
Proof.
  introv ts.
  inductions ts; eauto.
Qed.


Lemma fprincipal_dtype_g: forall G p A,
 fvalue p -> dtyping G p Inf A ->
(principal_type p) = A.
Proof.
  introv pval typ. gen A G.
  inductions pval; intros;try solve[inverts* typ].
Qed.

Lemma principal_dtype_g: forall G p A,
 value p -> dtyping G p Inf A ->
(principal_type p) = A.
Proof.
  introv pval typ. gen A G.
  inductions pval; intros;try solve[inverts* typ].
  -
  forwards*: fprincipal_dtype_g H.
  -
  inverts* typ. simpl.
  forwards*: IHpval1 H1.
  forwards*: IHpval2 H3.
  rewrite H. rewrite H0. reflexivity.
  -
  inverts typ.
  simpl.
  forwards*: IHpval H1.
  rewrite H.
  reflexivity.
Qed.



Lemma fill_chk_chk: forall G e E B,
 dtyping G (fill E e) Chk B ->
 dtyp_static B ->
 exists A, dtyping G e Chk A.
Proof.
  introv typ st.
  destruct E; unfold fill in *; inverts* typ;
  try solve[inverts* H].
  - inverts* H.
    forwards*: dtyping_regular H6.
  - inverts H.
    forwards*: dtyping_regular H5.
  - inverts H.
    forwards*: dtyping_regular H7.
  - inverts H.
    forwards*: dtyping_regular H5.
  - inverts H.
    forwards*: dtyping_regular H6.
Qed.



Theorem static_ddstep_dyn_chk : forall G e e' B,
 dexp_static e ->
 dtyp_static B ->
 dtyping G e Chk B ->
 dstep e e' -> 
 step e (r_e e').
Proof.
 introv es ts typ dstep. gen G B.
 inductions dstep; intros; eauto;
 try solve[forwards*: dsub_csub H1];
 try solve[forwards*: dsub_csub H0].
 - forwards*: dtyping_regular typ. inverts H0.
   forwards*: fill_chk_chk typ. inverts H0.
   forwards*: dtyping_regular H3.
Qed.




Theorem static_stepd_dyn_chk : forall G e e' B,
 dexp_static e ->
 dtyp_static B ->
 dtyping G e Chk B ->
 step e (r_e e') -> 
 dstep e e'.
Proof.
 introv es ts typ red. gen G B.
 inductions red;intros; eauto;
 try solve[forwards*: csub_dsub H1];
 try solve[forwards*: csub_dsub H0] . 
 - forwards*: dtyping_regular typ. inverts H0.
   forwards*: fill_chk_chk typ. inverts H0.
   forwards*: dtyping_regular H3.
 -
   inverts es as h1. inverts h1 as h1 h2.
   inverts h2.
 -
   inverts es as h1 h2.
   inverts h2.
Qed.