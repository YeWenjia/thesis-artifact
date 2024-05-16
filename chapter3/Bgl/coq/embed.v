Require Import syntax_ott.
Require Import syntaxb_ott.
Require Import syntaxn_ott.
Require Import rules_inf.
Require Import rulesn_inf.
Require Import Infrastructure.
Require Import Typing.
Require Import Deterministic.
Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import Lia.
Require Import Strings.String.

(* 
Fixpoint embed (e:nexp) : exp :=
  match e with
  | ne_var_b i => e_var_b i
  | ne_var_f x => e_var_f x
  | (ne_lit i5) => 
                   (e_anno (e_lit i5) t_dyn) 
  | (ne_app e1 e2) => e_app (embed (e1)) (embed(e2))
  | (ne_abs e) => (e_anno (e_abs t_dyn (embed(e)) t_dyn) t_dyn)
  end. *)


Inductive embed : nexp -> exp -> Prop := 
 | ed_x: forall x,
     embed (ne_var_f x) (e_var_f x)
 | ed_lit: forall i5 l b,
     embed (ne_lit i5) (e_anno (e_lit i5) l b t_dyn) 
 | ed_app: forall e1 e2 e1' e2' l b ,
     embed e1 e1' ->
     embed e2 e2' ->
     embed  (ne_app e1 e2) (e_app e1' l b e2')
 | ed_abs: forall L l b e e',
     ( forall x , x \notin  L  -> 
     embed (open_nexp_wrt_nexp e (ne_var_f x) ) (open_exp_wrt_exp e' (e_var_f x) ))  ->
     embed (ne_abs e) (e_anno (e_abs t_dyn e' l b t_dyn) l b t_dyn)
| ed_pro: forall e1 e2 e1' e2' l b,
     embed e1 e1' ->
     embed e2 e2' ->
     embed  (ne_pro e1 e2) (e_anno (e_pro e1'  e2') l b t_dyn)
| ed_l: forall e1 e1' l b ,
     embed e1 e1' ->
     embed  (ne_l e1) (e_l e1' l b)
| ed_r: forall e1 e1' l b,
     embed e1 e1' ->
     embed  (ne_r e1) (e_r e1' l b)
.



Inductive well_formed : ctx -> nexp -> Prop := 
 | wl_lit : forall (x:var) G i,
     uniq G ->
     well_formed G (ne_lit i)
 | wl_var : forall (x:var) G,
      uniq G ->
     binds  x t_dyn G  ->
     well_formed G (ne_var_f x) 
 | wl_abs : forall G e L,
   ( forall x , x \notin  L  -> 
    well_formed  (cons ( x , t_dyn )  G )  (open_nexp_wrt_nexp e (ne_var_f x) ))  ->
     well_formed G (ne_abs e) 
 | wl_app : forall G e1 e2,
    well_formed G e1 ->
    well_formed G e2 ->
    well_formed G (ne_app e1 e2)
    | wl_pro : forall G e1 e2,
    well_formed G e1 ->
    well_formed G e2 ->
    well_formed G (ne_pro e1 e2)
    | wl_l : forall G e1 ,
    well_formed G e1 ->
    well_formed G (ne_l e1 )
    | wl_r : forall G e1,
    well_formed G e1 ->
    well_formed G (ne_r e1)
.

Hint Constructors embed well_formed: core.




Lemma embed_lc: forall e1 e2,
 embed e1 e2 ->
 lc_exp e2.
Proof.
 introv ed.
 inductions ed; eauto. 
Qed.


Lemma embed_lc2: forall e1 e2,
 embed e1 e2 ->
 lc_nexp e1.
Proof.
 introv ed.
 inductions ed; eauto. 
Qed.



(* Lemma Typing_c_rename : forall (x y : atom) E e T1 T2,
  x `notin` fv_exp e -> y `notin` (dom E `union` fv_exp e) ->
  Typing ((x , T1) :: E) (open_exp_wrt_exp e (e_var_f x)) Inf T2 ->
  Typing ((y , T1) :: E) (open_exp_wrt_exp e (e_var_f y)) Inf T2.
Proof.
  intros x y E e T1 T2 Fr1 Fr2 H.
  destruct (x == y).
  Case "x = y".
    subst; eauto.
  Case "x <> y".
    assert (J : uniq (((x , T1) :: E))).
      eapply Typing_regular_2; eauto.
    assert (J' : uniq E).
      inversion J; eauto.
    rewrite (@subst_exp_intro x); eauto.
    rewrite_env (nil ++ ((y , T1) :: E)).
    apply Typing_subst_1 with (S := T1).
    simpl_env.
    SCase "(open x s) is well-typed".
      apply Typing_weaken. eauto. auto.
    SCase "y is well-typed". eauto.
Qed. *)




Lemma embed_notin : forall x e1 e2,
 embed e1 e2 ->
 x `notin` fv_nexp(e1) ->
 x `notin` fv_exp(e2).
Proof.
  introv ed ni.
  inductions ed; simpl in *; eauto.
  pick fresh y.
  forwards* h1: H0 y; eauto.
  forwards* h2: fv_nexp_open_nexp_wrt_nexp_upper e (ne_var_f y).
  assert(x `notin` union (fv_nexp (ne_var_f y)) (fv_nexp e)) as h3; simpl in *.
  fsetdec.
  eauto.
  forwards* h4: fv_exp_open_exp_wrt_exp_lower e' (e_var_f y).
Qed.




Lemma dynamic_typing_aux: forall G e e',
 well_formed G e ->
 embed e e' ->
 Typing G e' Inf t_dyn.
Proof.
    introv wl ed. gen G.
    inductions ed; intros;simpl in *; 
    try solve[inverts* H0];
    try solve[inverts* wl];
    try solve[simpl;eauto];eauto.
    -
      inverts* wl.
      eapply Typ_anno.
      eapply Typ_sim.
      pick fresh x and
       apply Typ_abs.
      forwards* h3: H0 x.
      auto.
    -
      inverts* wl.
      forwards* h1:IHed1.
Qed.


Lemma notin_openn: forall y e x ,
   y `notin` union (singleton x) (fv_nexp e) ->
   y `notin` fv_nexp(open_nexp_wrt_nexp e (ne_var_f x)).
Proof.
 introv h1.
 forwards* h2: fv_nexp_open_nexp_wrt_nexp_upper e (ne_var_f x).
Qed.

Lemma notin_open: forall y e x,
   y `notin` union (singleton x) (fv_exp e) ->
   y `notin` fv_exp(open_exp_wrt_exp e (e_var_f x)).
Proof.
 introv h1.
 forwards* h2: fv_exp_open_exp_wrt_exp_upper e (e_var_f x).
Qed.


Lemma embed_subst: forall e1 e2 x y,
 embed e1 e2 ->
 embed (subst_nexp (ne_var_f y) x e1) (subst_exp (e_var_f y) x e2).
Proof.
  introv ed.
  inductions ed; simpl in *; eauto.
  -
    destruct(x0 == x); try solve[inverts* e];eauto.
  -
    pick fresh xx and apply ed_abs.
    forwards* h1: H0 xx.
    rewrite subst_nexp_open_nexp_wrt_nexp_var; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; eauto.
Qed.



Lemma well_formed_exists: forall G e,
 well_formed G e ->
 exists e', embed e e'.
Proof.
  introv wf. 
  inductions wf; intros;try solve[exists*];
  try solve[inverts IHwf1; inverts* IHwf2];eauto.
  -
    pick fresh x.
    forwards* h1:H0.
    inverts h1 as h1.
    pick fresh l.
    exists (e_anno (e_abs t_dyn (close_exp_wrt_exp x x0 ) l true t_dyn) l true t_dyn).
    pick fresh y and apply ed_abs.
   forwards* h2:  embed_subst x y h1. 
   rewrite subst_exp_spec in h2.
   rewrite (@subst_nexp_intro x); auto.
  Unshelve.
  eapply label.
  apply true.
  apply label.
  apply true.
  apply label.
  apply true.
   -  forwards* h1: IHwf.
      inverts* h1.
      -  forwards* h1: IHwf.
      inverts* h1.
      Unshelve.
      eapply label.
      apply true.
      Unshelve.
      eapply label.
      apply true.
Qed.


Lemma dynamic_typing: forall G e,
 well_formed G e ->
 exists e', embed e e' /\ Typing G e' Inf t_dyn.
Proof.
  introv wf.
  forwards* h1: well_formed_exists wf.
  inverts h1 as h1.
  forwards*: dynamic_typing_aux wf h1.
Qed.





Inductive dtyp_static : typ -> Prop :=
  | dtyp_static_nat:
      dtyp_static t_int
  | dtyp_static_arrow: forall A B,
      dtyp_static A ->
      dtyp_static B ->
      dtyp_static (t_arrow A B)  
  | dtyp_static_pro: forall A B,
      dtyp_static A ->
      dtyp_static B ->
      dtyp_static (t_pro A B)  
.

Inductive dexp_static : exp -> Prop :=
  | dexp_static_var: forall x,
      dexp_static (e_var_f x)
  | dexp_static_nat : forall i,
      dexp_static (e_lit i)
  | dexp_static_abs : forall L e1 t1 t2 l b ,
      (forall x, x \notin L -> dexp_static (open_exp_wrt_exp e1 (e_var_f x))) ->
      dtyp_static t1 ->
      dtyp_static t2 ->
      dexp_static (e_abs t1 e1 l b t2)
  | dexp_static_app : forall e1 e2 l b,
      dexp_static e1 ->
      dexp_static e2 ->
      dexp_static (e_app e1 l b e2)  
  | dexp_static_anno : forall e A l b,
      dexp_static e ->
      dtyp_static A ->
      dexp_static (e_anno e l b A)
  | dexp_static_pro : forall e1 e2,
      dexp_static e1 ->
      dexp_static e2 ->
      dexp_static (e_pro e1 e2)  
  | dexp_static_l : forall e1 l b,
      dexp_static e1 ->
      dexp_static (e_l e1 l b)  
  | dexp_static_r : forall e1 l b,
      dexp_static e1 ->
      dexp_static (e_r e1 l b)
.


Inductive denv_static : ctx -> Prop :=
  | denv_static_empty : denv_static nil
  | denv_static_typ : forall E x T,
      denv_static E ->
      dtyp_static T ->
      denv_static ((x, T) :: E).


Inductive dsub : typ -> typ -> Prop :=    
 | dS_z : 
     dsub t_int t_int
 | dS_arr : forall (A1 A2 B1 B2:typ),
     dsub  A1 B1 ->
     dsub A2 B2 ->
     dsub (t_arrow A1 A2) (t_arrow B1 B2)
  | dS_pro : forall (A1 A2 B1 B2:typ),
     dsub  A1 B1->
     dsub A2 B2 ->
     dsub (t_pro A1 A2) (t_pro B1 B2)
.


Inductive dtyping : ctx -> exp -> dirflag -> typ -> Prop :=    (* defn dtyping *)
 | dtyp_lit : forall (G:ctx) (i5:i),
      uniq  G  ->
     dtyping G (e_lit i5) Inf t_int
 | dtyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
      dtyp_static A ->
     dtyping G (e_var_f x) Inf A
 | dtyp_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ) l b,
      ( forall x , x \notin  L  -> dtyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
      dtyp_static A ->
      dtyping G (e_abs A e l b B) Inf (t_arrow A B)
 | dtyp_app : forall (G:ctx) (e1 e2:exp) (B A:typ) l b ,
     dtyping G e1 Inf (t_arrow A B) ->
     dtyping G e2 Chk A ->
     dtyping G (e_app e1 l b e2) Inf B
 | dtyp_anno : forall (G:ctx) (e:exp) (A:typ) l b,
     dtyping G e Chk A ->
     dtyping G (e_anno e l b  A) Inf A
 | dtyp_sub : forall (G:ctx) (e:exp) (B A:typ),
     dtyping G e Inf A ->
     dsub A B ->
     dtyp_static B ->
     dtyping G e Chk B
 | dtyp_pro : forall (G:ctx) (e1 e2:exp) (A1 A2:typ),
     dtyping G e1 Inf A1 ->
     dtyping G e2 Inf A2 ->
     dtyping G (e_pro e1 e2) Inf (t_pro A1 A2)
 | dtyp_l : forall (G:ctx) (e1 :exp) (A1 :typ) l b A2,
     dtyping G e1 Inf (t_pro A1 A2) ->
     (* dtyp_static A2 -> *)
     dtyping G (e_l e1 l b) Inf A1
 | dtyp_r : forall (G:ctx) (e1 :exp) (A1 :typ) l b A2,
     dtyping G e1 Inf (t_pro A1 A2) ->
     (* dtyp_static A1 -> *)
     dtyping G (e_r e1 l b) Inf A2
.

Hint Constructors dtyping dexp_static dtyp_static   denv_static  dsub : core.


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


Lemma dsub_csub: forall A B,
 dsub A B ->
 sim A B.
Proof.
  introv dsub.
  inductions dsub; eauto.
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
      pick fresh x.
      forwards*: H0 x.
    - destructs~ IHtyp1. destructs~ IHtyp2. inverts* H0.
    -
       
     destructs~ IHtyp. inverts* H0.
    - destructs~ IHtyp. inverts* H0.
Qed.


Theorem static_dtyping_dyn : forall G e A dir,
 dexp_static e ->
 dtyp_static A ->
 dtyping G e dir A -> 
 Typing G e dir A.
Proof.
  introv es ts typ.
  inductions typ;eauto;
  try solve[inverts es;inverts ts; auto];
  try solve[inverts es; auto].
  - inverts ts. inverts es.
    pick fresh x and apply Typ_abs.
    forwards: H0 x; try solve[ eauto].
  -
    inverts* es.  
    forwards*: dtyping_regular typ1.
    destructs~ H. inverts* H0.
  - forwards*: dtyping_regular typ.
    inverts* H1.
    forwards*: IHtyp.
    eapply Typ_sim; eauto.
    forwards*: dsub_csub H.
  - 
    inverts es; auto.
    forwards* h1: dtyping_regular typ.
  -
    inverts es; auto.
    forwards* h1: dtyping_regular typ.
Qed.

Lemma csub_dsub: forall A B n,
 size_typ A + size_typ B < n ->
 sim A B ->
 dtyp_static A ->
 dtyp_static B ->
 dsub A B.
Proof.
  introv sz csub st1 st2. gen A B.
  inductions n; intros; try solve[lia].
  inductions csub; eauto;
  try solve[inverts* st1];
  try solve[inverts* st2];
  try solve[inverts* st1; inverts* st2].
  -
  inverts st1; inverts st2;simpl in *.
  forwards*: IHn csub2. lia.
  apply BA_AB in csub1.
  forwards*: IHn csub1. lia.
  -
  inverts st1; inverts st2;simpl in *.
  forwards*: IHn csub2. lia.
  (* apply BA_AB in csub1. *)
  forwards*: IHn csub1. lia.
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

Lemma pattern_static: forall A A1 A2,
 dtyp_static A ->
 pattern A (t_arrow A1 A2) ->
 dtyp_static A1 /\ dtyp_static A2.
Proof.
  introv dt pa.
  inverts* dt;inverts* pa.
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
 -
   inverts* se.
   forwards*: IHtyp1.
   forwards*: pattern_static H.
 -
   inverts* se.
   forwards* h1: IHtyp.
   inverts* h1; try solve[inverts H].
   inverts* H.
 -
   inverts* se.
   forwards* h1: IHtyp.
   inverts* h1; try solve[inverts H].
   inverts* H.
Qed.


Theorem static_Typing_dyn : forall dir G e A,
 denv_static G ->
 dexp_static e ->
 dtyp_static A ->
 Typing G e dir A -> 
 dtyping G e dir A.
Proof.
  introv env es ts typ.
  inductions typ;eauto;
  try solve[inverts ts];
  try solve[inverts es];
  try solve[inverts ts;inverts H3].
  - inverts ts. inverts es.  
    pick fresh x and apply dtyp_abs; auto.
  -
    inverts es. 
    forwards*: Typ_static_exp_static_typ typ1.
    forwards*: pattern_static H. inverts* H1.
    forwards*: IHtyp1.
    forwards*: IHtyp2.
    inverts* H. inverts* H0.
  -
    inductions typ; try solve[inverts* ts].
    inverts* es.
  -
    forwards*: Typ_static_exp_static_typ typ.
    forwards*: csub_dsub H.
  -
    inverts* es.
    inverts* ts.
  -
    inverts es.
    forwards* h1: Typ_static_exp_static_typ typ.
    forwards* h2: IHtyp.
    inverts* H; try solve[inverts h1].
  -
    inverts es.
    forwards* h1: Typ_static_exp_static_typ typ.
    forwards* h2: IHtyp.
    inverts* H; try solve[inverts h1].
Qed.