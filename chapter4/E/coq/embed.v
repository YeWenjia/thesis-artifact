Require Import syntax_ott.
Require Import syntaxn_ott.
Require Import rules_inf.
Require Import rulesn_inf.
Require Import Infrastructure.
Require Import Typing.
Require Import Deterministic.
Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import Omega.


Fixpoint embed (e:nexp) (b: bool): exp :=
  match e with
  | ne_var_b i => e_var_b i
  | ne_var_f x => e_var_f x
  | (ne_lit i5) => match b with
                   | true =>
                      (e_anno (e_lit i5) t_dyn) 
                   | false => (e_lit i5)
                    end
  | (ne_app e1 e2) => e_app (embed e1 true) (embed e2 false)
  | (ne_abs e) => match b with
                  | true => (e_anno (e_abs (embed(e) false)) t_dyn)
                  | false => (e_abs (embed(e) false))
                  end
  | (ne_add) => match b with
                   | true =>
                      (e_anno (e_add) t_dyn) 
                   | false => (e_add)
                    end
  | (ne_addl i5) => match b with
                   | true =>
                      (e_anno (e_addl i5) t_dyn) 
                   | false => (e_addl i5)
                    end
  end.



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
    | wl_add : forall G,
     uniq G ->
     well_formed G (ne_add)
     | wl_addl : forall G i,
     uniq G ->
     well_formed G (ne_addl i).


Lemma embed_open_gen: forall e1 x n m b,
 size_nexp e1 < n ->
 embed (open_nexp_wrt_nexp_rec m (ne_var_f x) e1) b = open_exp_wrt_exp_rec m  (e_var_f x) (embed e1 b).
Proof.
  introv sz. gen e1 x m. 
  inductions n; intros; try solve[omega].
  inductions e1;intros; try solve[unfold embed in *; eauto].
  -
    simpl; eauto.
    destruct(lt_eq_lt_dec n0 m); eauto.
    inverts* s.
  -
    destruct b; simpl; eauto.
  -
    destruct b.
    +
    assert(embed (ne_abs e1) true = (e_anno ((e_abs (embed e1 false)) ) t_dyn)).
    unfold embed; eauto.
    rewrite H.
    simpl; eauto.
    simpl in *.
    forwards*: IHn e1 x (S m). omega.
    rewrite H0; eauto.
    +
    assert(embed (ne_abs e1) false = (e_abs (embed e1 false))).
    unfold embed; eauto.
    rewrite H.
    simpl; eauto.
    simpl in *.
    forwards*: IHn e1 x (S m). omega.
    rewrite H0; eauto.
  -
    simpl in *.
    forwards*: IHn e1_1 x m. omega.
    forwards*: IHn e1_2 x m. omega.
    f_equal; eauto.
  -
    destruct b; simpl; eauto.
  -
    destruct b; simpl; eauto.
Qed.


Lemma embed_open: forall e1 x m b,
embed (open_nexp_wrt_nexp_rec m (ne_var_f x) e1) b = open_exp_wrt_exp_rec m  (e_var_f x) (embed e1 b).
Proof.
  introv.
  eapply embed_open_gen; eauto.
Qed.



Definition dynamic_typing_aux G e b  := 
   match b with 
    | true => Typing G (embed e b) Inf t_dyn 
    | _   => Typing G (embed e b) Chk t_dyn 
   end.

Lemma dynamic_typing: forall G e b,
 well_formed G e ->
 dynamic_typing_aux G e b.
Proof.
    introv wl. gen b.
    inductions wl; intros;simpl in *; eauto;unfold dynamic_typing_aux in *;
    destruct b; simpl in *; eauto.
    -
    apply Typ_anno; eauto.
    pick fresh x and apply Typ_abs; auto.
    apply pa_dyn.
    forwards* h1: H0 x false.
    unfold open_exp_wrt_exp in *.
    unfold open_nexp_wrt_nexp in *.
    rewrite <- embed_open; auto.
    -
    pick fresh x and apply Typ_abs; eauto.
    forwards*: H0 x false.
    unfold open_exp_wrt_exp in *.
    unfold open_nexp_wrt_nexp in *.
    rewrite <- embed_open;auto.
    -
      forwards* h1: IHwl1 true.
      forwards* h2: IHwl2 false.
    -
      forwards* h1: IHwl1 true.
      forwards* h2: IHwl2 false.
Qed.




(* 

Inductive dtyp_static : typ -> Prop :=
  | dtyp_static_nat:
      dtyp_static t_int
  | dtyp_static_arrow: forall A B,
      dtyp_static A ->
      dtyp_static B ->
      dtyp_static (t_arrow A B)  
.

Inductive dexp_static : exp -> Prop :=
  | dexp_static_var: forall x,
      dexp_static (e_var_f x)
  | dexp_static_nat : forall i,
      dexp_static (e_lit i)
  | dexp_static_abs : forall L e1 t1 t2,
      (forall x, x \notin L -> dexp_static (open_exp_wrt_exp e1 (e_var_f x))) ->
      dtyp_static t1 ->
      dtyp_static t2 ->
      dexp_static (e_abs t1 e1 t2)
  | dexp_static_app : forall e1 e2,
      dexp_static e1 ->
      dexp_static e2 ->
      dexp_static (e_app e1 e2)  
  | dexp_static_anno : forall e A,
      dexp_static e ->
      dtyp_static A ->
      dexp_static (e_anno e A)
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
     dsub B1 A1 ->
     dsub A2 B2 ->
     dsub (t_arrow A1 A2) (t_arrow B1 B2)
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
 | dtyp_abs : forall (L:vars) (G:ctx) (A:typ) (e:exp) (B:typ),
      ( forall x , x \notin  L  -> dtyping  (cons ( x , A )  G )   ( open_exp_wrt_exp e (e_var_f x) )  Chk B )  ->
      dtyp_static A ->
      dtyping G (e_abs A e B) Inf (t_arrow A B)
 | dtyp_app : forall (G:ctx) (e1 e2:exp) (B A:typ),
     dtyping G e1 Inf (t_arrow A B) ->
     dtyping G e2 Chk A ->
     dtyping G (e_app e1 e2) Inf B
 | dtyp_anno : forall (G:ctx) (e:exp) (A:typ),
     dtyping G e Chk A ->
     dtyping G (e_anno e A) Inf A
 | dtyp_sub : forall (G:ctx) (e:exp) (B A:typ),
     dtyping G e Inf A ->
     dsub A B ->
     dtyp_static B ->
     dtyping G e Chk B.

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
    pick fresh x and apply Typ_abs.
    forwards: H0 x; try solve[ eauto].
  -
    inverts* es.  
    forwards*: dtyping_regular typ1.
    destructs~ H. inverts* H0.
  - inverts* es. 
  - forwards*: dtyping_regular typ.
    inverts* H1.
    forwards*: IHtyp.
    eapply Typ_sim; eauto.
    forwards*: dsub_csub H.
Qed.

Lemma csub_dsub: forall A B n,
 size_typ A + size_typ B < n ->
 sim A B ->
 dtyp_static A ->
 dtyp_static B ->
 dsub A B.
Proof.
  introv sz csub st1 st2. gen A B.
  inductions n; intros; try solve[omega].
  inductions csub; eauto;
  try solve[inverts* st1];
  try solve[inverts* st2];
  try solve[inverts* st1; inverts* st2].
  inverts st1; inverts st2;simpl in *.
  forwards*: IHn csub2. omega.
  apply BA_AB in csub1.
  forwards*: IHn csub1. omega.
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
    invert* es.
  -
    forwards*: Typ_static_exp_static_typ typ.
    forwards*: csub_dsub H.
Qed.
 *)
