Require Import Bool.
Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Deterministic
        Type_Safety
        Typing
        Key_Properties
        Subtyping_inversion.
Require Import Lia.


Inductive ttyp : Set :=  
 | tt_nil : ttyp
 | tt_int : ttyp 
 | tt_arrow (A:ttyp) (B:ttyp) : ttyp
 | tt_dyn : ttyp 
 | tt_rcd (l:var) (A:ttyp) (B: ttyp)
 | tt_row (l:var) (A:ttyp) (B: ttyp).


 Fixpoint ssize_typ (A1 : ttyp) {struct A1} : nat :=
  match A1 with
    | tt_int => 1
    | tt_nil => 1
    | tt_arrow A2 B1 => 1 + (ssize_typ A2) + (ssize_typ B1)
    | tt_rcd l A B => 1 + (ssize_typ A) + (ssize_typ B)
    | tt_row l A B => 1 + (ssize_typ A) + (ssize_typ B)
    | tt_dyn => 1
  end.


Inductive rt_type : ttyp -> Prop :=
  | rt_nil :
      rt_type tt_nil
  | rt_rcd : forall i T1 T2,
      rt_type (tt_rcd i T1 T2).



Inductive rt_ty : ttyp -> Prop :=
  | rct_nil :
      rt_ty tt_nil
  | rct_rcd : forall i T1 T2,
      rt_ty T2 ->
      rt_ty (tt_rcd i T1 T2).


Inductive rw_type : ttyp -> Prop :=
  | rw_nil :
      rw_type tt_nil
  | rw_row : forall i T1 T2,
      rw_type (tt_row i T1 T2).


Inductive rw_ty : ttyp -> Prop :=
  | rcw_nil :
      rw_ty tt_nil
  | rcw_row : forall i T1 T2,
      rw_ty T2 ->
      rw_ty (tt_row i T1 T2).


Inductive record_ty : typ -> Prop :=
  (* | rcd_nil :
      record_ty t_top *)
  | rcd_rcd : forall i T,
      record_ty (t_rcd i T)
  | rcd_and : forall T1 T2,
      record_ty T1 ->
      record_ty T2 ->
      (* disjoint T1 T2 -> *)
      record_ty (t_and T1 T2).


Definition cctx : Set := list ( atom * ttyp ).


Inductive eexp : Set :=  (*r expressions *)
 | ee_var_b (_:nat) (*r variables *)
 | ee_var_f (x:var) (*r variables *)
 | ee_nil 
 | ee_lit (i5:nat) (*r lit *)
 | ee_abs (A:ttyp) (e:eexp)  (*r abstractions *)
 | ee_app (e1:eexp) (e2:eexp) (*r applications *)
 | ee_anno (e:eexp) (A:ttyp) (*r annotation *)
 | ee_rcd (l:var) (e:eexp) (e:eexp) (*r record *)
 | ee_proj (e:eexp) (l:var) (*r projection *).



Inductive rt_exp : eexp -> Prop :=
  | rt_e_nil :
      rt_exp ee_nil
  | rt_e_rcd : forall i e1 e2,
      rt_exp (ee_rcd i e1 e2).


Fixpoint collectLabel (T : ttyp) : atoms :=
  match T with
  | (tt_rcd i T1 T2) => {{i}} \u (collectLabel T2)
  | (tt_row i T1 T2) => {{i}} \u (collectLabel T2)
  | _ => {}
  end.



Fixpoint collectLabel2 (T : typ) : atoms :=
  match T with
  | (t_rcd i T1) => {{i}} 
  | (t_and T1 T2) => (collectLabel2 T1) \u (collectLabel2 T2)
  | _ => {}
  end.


Inductive type : ttyp -> Prop :=
| typ_nat : type tt_int
| type_arrow : forall A B,
    type A ->
    type B ->
    type (tt_arrow A B)
| type_nil :
    type tt_nil
| type_rcd : forall i T1 T2,
    type T1 ->
    type T2 ->
    rt_type T2 ->
    i `notin` (collectLabel T2) ->
    type (tt_rcd i T1 T2)
| type_row : forall i T1 T2,
    type T1 ->
    type T2 ->
    rw_type T2 ->
    i `notin` (collectLabel T2) ->
    type (tt_row i T1 T2).


Inductive rrecord : ttyp -> Prop :=
  | rrt_rcd : forall i T1 T2,
      type T1 ->
      i `notin` (collectLabel T2) ->
      rrecord T2 ->
      rrecord (tt_rcd i T1 T2).



Fixpoint Tlookup (i': var) (Tr:ttyp) : option ttyp :=
  match Tr with
  | (tt_rcd i T1 T2) =>
      if i == i' then Some T1 else Tlookup i' T2
  | (tt_row i T1 T2) =>
      if i == i' then Some T1 else Tlookup i' T2
  | _ => None
  end.



Inductive aproj : var -> ttyp -> ttyp -> Prop := 
 | apj_dyn : forall i,
    aproj i tt_dyn tt_dyn
 | apj_rcd :  forall T1 T2 Ti i i',
    Tlookup i' (tt_rcd i T1 T2) = Some Ti ->
    aproj i' (tt_rcd i T1 T2) Ti
 | apj_row :  forall T1 T2 Ti i i',
    Tlookup i' (tt_row i T1 T2) = Some Ti ->
    aproj i' (tt_row i T1 T2) Ti
 | apj_rowd :  forall T1 T2 i i',
    Tlookup i' (tt_row i T1 T2) = None ->
    aproj i' (tt_row i T1 T2) tt_dyn.


Inductive Acs : ttyp -> ttyp -> Prop :=
|  Acs_dynl: forall t,
    Acs tt_dyn t 
|  Acs_dynr: forall t,
    Acs t tt_dyn 
|  Acs_nat:
     Acs tt_int tt_int
|  Acs_arrow: forall A1 A2 B1 B2,
     Acs B1 A1 ->
     Acs A2 B2 ->
     Acs (tt_arrow A1 A2) (tt_arrow B1 B2)
|  Acs_rcd: forall A1 A2,
    rt_type A1 ->
    rt_type A2 ->
    type A1 -> type A2 ->
    collectLabel A2 [<=] collectLabel A1 ->
    (forall i t1 t2, i `in` collectLabel A2 -> Tlookup i A1 = Some t1 -> Tlookup i A2 = Some t2 -> Acs t1 t2) ->
    Acs A1 A2
|  Acs_rcdd: forall A1 A2,
    rw_type A1 ->
    rw_type A2 ->
    type A1 -> type A2 ->
    (exists i t1 t2, Tlookup i A1 = Some t1 /\ Tlookup i A2 = Some t2 /\ Acs t1 t2) ->
    Acs A1 A2
|  Acs_rcdr: forall A1 A2,
    rt_type A1 ->
    rw_type A2 ->
    type A1 -> type A2 ->
    collectLabel A2 [<=] collectLabel A1 ->
    (forall i t1 t2, i `in` collectLabel A2 -> Tlookup i A1 = Some t1 -> Tlookup i A2 = Some t2 -> Acs t1 t2) ->
    Acs A1 A2
|  Acs_rcddr: forall A1 A2,
    rw_type A1 ->
    rt_type A2 ->
    type A1 -> type A2 ->
    (exists i t1 t2, Tlookup i A1 = Some t1 /\ Tlookup i A2 = Some t2 /\ Acs t1 t2) ->
    Acs A1 A2
(* |  Acs_rcd: forall A1 A2,
    rw_type A1 ->
    rt_type A2 ->
    type A1 -> type A2 ->
    (exists i t1 t2, Tlookup i A1 = Some t1 /\  Tlookup i A2 = Some t2 /\ Acs t1 t2) ->
    Acs A1 A2 *)
(* |  Acs_row: forall A1 A2,
    rw_type A1 ->
    rw_type A2 ->
    type A1 -> type A2 ->
    (exists i t1 t2, Tlookup i A1 = Some t1 /\  Tlookup i A2 = Some t2 /\ Acs t1 t2) ->
    Acs A1 A2 *)
 (* |  Acs_rowr: forall i T1 T2 T3 T4,
    Acs T1 T3 ->
    Acs T2 T4 ->
    Acs  (tt_rcd i T1 T2) (tt_row i T3 T4)
| Acs_rcdd: forall i T1 T2 T3 T4,
    Acs T1 T3 ->
    Acs T2 T4 ->
    Acs  (tt_rcd i T1 T2) (tt_rcd i T3 T4)
 | Acs_nil: forall T1 T2 i,
    type (tt_rcd i T1 T2) ->
    Acs (tt_rcd i T1 T2) tt_nil
 | Acs_RcdPerm: forall T1 T2 i1 i2 T3,
    type (tt_rcd i1 T1 (tt_rcd i2 T2 T3)) ->
    i1 <> i2 ->
    Acs (tt_rcd i1 T1 (tt_rcd i2 T2 T3)) (tt_rcd i2 T2 (tt_rcd i1 T1 T3)) *)
.


(* EXPERIMENTAL *)
(** auxiliary functions on the new list types *)
(** library functions *)
(** subrules *)
(** arities *)
(** opening up abstractions *)
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
  | (ee_abs A e) => ee_abs A (open_eexp_wrt_eexp_rec (S k) e_5 e)
  | (ee_app e1 e2) => ee_app (open_eexp_wrt_eexp_rec k e_5 e1) (open_eexp_wrt_eexp_rec k e_5 e2)
  | (ee_anno e A) => ee_anno (open_eexp_wrt_eexp_rec k e_5 e) A
  |  ee_nil => ee_nil
  | (ee_rcd i e1 e2) => ee_rcd i (open_eexp_wrt_eexp_rec k e_5 e1) (open_eexp_wrt_eexp_rec k e_5 e2)
  | (ee_proj e i) => ee_proj (open_eexp_wrt_eexp_rec k e_5 e) i
end.

Definition open_eexp_wrt_eexp e_5 e__6 := open_eexp_wrt_eexp_rec 0 e__6 e_5.



Fixpoint transt (t:ttyp): typ :=
  match t with
  | tt_dyn => t_dyn
  | tt_int => t_int
  | tt_arrow t1 t2 => t_arrow (transt t1) (transt t2)
  | tt_nil  => t_top
  | (tt_rcd i t1 t2) => t_and (t_rcd i (transt t1)) (transt t2)
  | (tt_row i t1 t2) => t_and (t_and (t_rcd i (transt t1)) (transt t2)) t_dyn
end.



Fixpoint transg (G:cctx): ctx :=
  match G with
  | nil => nil
  | (cons ( x , A) G2) => (cons ( x , (transt A) ) (transg G2))
end.


Inductive Atyping : cctx -> eexp -> ttyp -> exp -> Prop :=    (* defn Typing *)
| Atyp_nil : forall (G:cctx) ,
   uniq  G  ->
   Atyping G (ee_nil) tt_nil (e_top)
 | Atyp_lit : forall (G:cctx) (i5:nat) ,
     uniq  G  ->
      Atyping G  (ee_lit i5) tt_int (e_lit i5)
 | Atyp_var : forall (G:cctx) (x:var) (A:ttyp) ,
      uniq  G  ->
      binds  x A G  ->
      type A ->
      Atyping G (ee_var_f x) A (e_var_f x)
 | Atyp_abs : forall (L:vars) (G:cctx) (A:ttyp) (e:eexp) (B:ttyp) t,
      ( forall x , x \notin  L  -> Atyping  (cons ( x , A )  G ) ( open_eexp_wrt_eexp e (ee_var_f x) ) B ( open_exp_wrt_exp t (e_var_f x) ) )  ->
      type A ->
      Atyping G (ee_abs A e) (tt_arrow A B) (e_anno (e_abs t) (t_arrow (transt A) (transt B)))
 | Atyp_app : forall (G:cctx) (e1 e2:eexp) (B A1 A2:ttyp) t1 t2,
     Atyping G  e1  (tt_arrow A1 B) t1 ->
     Atyping G  e2  A2 t2 ->
     Acs A2 A1 ->
     Atyping G (ee_app e1 e2) B (e_app t1 t2)
 | Atyp_asst : forall (G:cctx) (e:eexp) (A B:ttyp) t,
     Atyping G e A t->
     Acs A B ->
     type B ->
     Atyping G (ee_anno e B) B (e_anno t (transt B)) 
 | Atyp_proj : forall (G:cctx) (e:eexp) i (A:ttyp) B t,
     Atyping G e A t ->
     aproj i A B ->
     type B ->
     Atyping G (ee_proj e i) B (e_proj t i) 
 | Atyp_cons : forall G e1 e2 T1 T2 i t1 t2,
     Atyping G e1 T1 t1 ->
     Atyping G e2 T2 t2 ->
     rt_type T2 ->
     rt_exp e2 ->
     i `notin` (collectLabel T2) ->
     Atyping G (ee_rcd i e1 e2) (tt_rcd i T1 T2) (e_merge (e_rcd i t1) t2).


(** infrastructure *)

Hint Constructors Atyping Acs rt_type rt_ty rw_type rw_ty rt_exp type aproj record_ty rrecord: core.


Lemma union_empty: forall A i,
    union (singleton i) A [<=] empty -> False.
Proof with eauto.
  intros.
  unfold "[<=]" in H.
  eapply empty_iff...
Qed.


Lemma lookup_some: forall i T,
    i \in collectLabel T ->
    exists S, Tlookup i T = Some S.
Proof with auto.
  intros.
  induction T;simpl in *;try solve [apply empty_iff in H;destruct H]...
  - apply AtomSetImpl.union_1 in H...
  destruct H...
  apply KeySetFacts.singleton_iff in H.
  exists T1...
  destruct (l==i)...
  destruct n...
  apply IHT2 in H...
  destruct H.
  destruct (l==i)...
  exists T1...
  exists x...
  - apply AtomSetImpl.union_1 in H...
  destruct H...
  apply KeySetFacts.singleton_iff in H.
  exists T1...
  destruct (l==i)...
  destruct n...
  apply IHT2 in H...
  destruct H.
  destruct (l==i)...
  exists T1...
  exists x...
Qed.  


Lemma label_belong: forall i A B,
    Tlookup i A = Some B -> i \in collectLabel A.
Proof with auto.
  intros.
  inductions A;simpl in *;try solve [inversion H]...
  destruct (l==i)...
  apply IHA2 in H...
  destruct (l==i)...
  apply IHA2 in H...
Qed.


Lemma label_notbelongw: forall i A,
    Tlookup i A = None -> i `notin` collectLabel A.
Proof with auto.
  intros.
  inductions A;simpl in *;try solve [inverts* H]...
  destruct (l==i)...
  inverts* H...
  destruct (l==i)...
  inverts* H...
Qed.



Lemma notin_nityp_rcd: forall i t,
  i `notin` collectLabel t ->
  not(ityp (transt t) i).
Proof.
  introv nin.
  inductions t;try solve[unfold not; intros nt; inverts* nt].
  -
    simpl in *.
    forwards*: IHt2.
    destruct(i==l); simpl in *; eauto.
    unfold not; intros nt; inverts* nt.
    inverts* H3.
  -
    simpl in *.
    forwards*: IHt2.
    destruct(i==l); simpl in *; eauto.
    unfold not; intros nt; inverts* nt.
    inverts* H3. inverts* H4. inverts* H3. 
Qed.


Lemma in_ityp_rcd: forall i t,
  i `in` collectLabel t ->
  ityp (transt t) i.
Proof.
  introv nin.
  inductions t;try solve[unfold collectLabel; fsetdec].
  -
    simpl in *.
    destruct(i == l); try solve[inverts* e];eauto.
    assert(i `in` (collectLabel t2)).
    fsetdec.
    forwards*: IHt2.
  -
    simpl in *.
    destruct(i == l); try solve[inverts* e];eauto.
    assert(i `in` (collectLabel t2)).
    fsetdec.
    forwards*: IHt2.
Qed.

Lemma tlookup_get_ty: forall t1 t2 i,
 type t1 ->
 Tlookup i t1 = Some t2 ->
 get_ty (transt t1) i (transt t2).
Proof.
  introv ty tlp.
  inductions ty; simpl in *; try solve[inverts* tlp].
  -
    destruct(i0 == i); simpl in *; eauto.
    inverts* tlp. inverts* e.
    forwards*: notin_nityp_rcd H0.
    forwards*: IHty2.
    assert(not(ityp ((t_rcd i0 (transt T1))) i)).
    unfold not; intros nt; inverts* nt.
    forwards*: label_belong tlp.
    forwards*: in_ityp_rcd H3.
  -
    destruct(i0 == i); simpl in *; eauto.
    inverts* tlp. inverts* e.
    forwards*: notin_nityp_rcd H0.
    apply g_andl; eauto.
    unfold not; intros nt; inverts nt.
    forwards*: IHty2.
    assert(not(ityp ((t_rcd i0 (transt T1))) i)).
    unfold not; intros nt; inverts* nt.
    forwards*: label_belong tlp.
    forwards*: in_ityp_rcd H3.
    apply g_andl; eauto.
    unfold not; intros nt; inverts nt.
Qed.



Lemma atyp_rt_ty: forall G e t T,
  rt_exp e ->
  rt_type T ->
  Atyping G e T t ->
  rt_ty T.
Proof.
  introv rt re atyp.
  inductions atyp; intros; try solve[inverts* rt;inverts* re];eauto.
Qed.


Lemma Anotin_disjoint: forall i t1 t2,
   rt_ty t2 ->
   i `notin` collectLabel t2 ->
   disjoint (t_rcd i t1) (transt t2).
Proof.
  introv rt inin. gen i.
  inductions rt; intros; simpl in *;eauto. 
Qed.


Lemma Anotin_disjoint2: forall i t1 t2,
   rw_ty t2 ->
   i `notin` collectLabel t2 ->
   disjoint (t_rcd i t1) (transt t2).
Proof.
  introv rt inin. gen i.
  inductions rt; intros; simpl in *;eauto.
  apply D_andR; eauto.
Qed.


Lemma false_rewrite: forall i i0 T T1,
 i <> i0 ->
 (if i == i0 then Some T1 else Tlookup i0 T) = Tlookup i0 T.
Proof.
  introv neq.
  destruct(i == i0); simpl; eauto.
  exfalso; apply neq; eauto.
Qed.


Lemma rrecord_type:  forall A,
 rrecord A ->
 type A.
Proof.
  introv rcd.
  inductions rcd; eauto.
  inverts* rcd.
Qed.



Lemma rrecord_record_ty:  forall A,
 rrecord A ->
 record_ty (transt A).
Proof.
  introv rcd.
  inductions rcd; simpl in *;eauto.
Qed.

Lemma collectLabel2_collect: forall A,
 collectLabel A [=] collectLabel2 (transt A).
Proof.
  introv.
  inductions A; simpl  in *; try fsetdec.
Qed.


Lemma type_rt_ty: forall T,
  type T ->
  rt_type T->
  rt_ty T.
Proof.
  introv ty rt.
  inductions ty; eauto; try solve[inverts* rt].
Qed.


Lemma type_rw_ty: forall T,
  type T ->
  rw_type T->
  rw_ty T.
Proof.
  introv ty rt.
  inductions ty; eauto; try solve[inverts* rt].
Qed.


Lemma tlookup_sz: forall i t x,
  Tlookup i t = Some x ->
  ssize_typ x < ssize_typ t.
Proof.
  introv tl.
  inductions t; simpl in *; eauto; try solve[inverts tl]; try solve[lia].
  -
    destruct(l == i).
    +
    assert(t1 = x).
    inverts* tl.
    inverts* H.
    lia.
    +
    forwards*: IHt2 tl.
    lia.
  -
    destruct(l == i).
    +
    assert(t1 = x).
    inverts* tl.
    inverts* H.
    lia.
    +
    forwards*: IHt2 tl.
    lia.
Qed.




Lemma get_ty_csub_aux: forall t1 l t2 t3,
 ityp t1 l -> 
 get_ty t1 l t2 ->
 t2 <:~ t3 -> 
 t1 <:~ t_rcd l t3.
Proof.
  introv nin gt cs.
  inductions gt; eauto.
  -
    exfalso; apply H; eauto.
Qed.



Theorem Acs_CS_Soundness: forall t1 t2 n,
 ssize_typ t1 + ssize_typ t2 < n ->
 Acs t1 t2 -> (transt t1) <:~ (transt t2).
Proof.
 introv sz acs.
 gen t1 t2.
 inductions n; intros; try solve[lia].
 inverts acs; simpl in *; eauto.
 -
   forwards* h1: IHn H.
   lia.
   forwards* h2: IHn H0.
   lia.
 -
   gen t1.
   inductions H2; intros;simpl in *; try solve[inverts H0];eauto.
   assert(i `in` collectLabel t1) as h0.
   fsetdec.
   forwards* h1: lookup_some h0.
   inverts h1 as h1.
   forwards* h2: H5 i x T1.
   destruct(i == i); auto.
   exfalso; apply n0; auto.
   assert((collectLabel T2) [<=] collectLabel t1) as h3.
   fsetdec.
   assert(forall (i : atom) (t2 t3 : ttyp),
   i `in` (collectLabel T2) ->
   Tlookup i t1 = Some t2 ->
   Tlookup i T2 = Some t3 -> Acs t2 t3) as h4.
   introv h5 h6 h7.
   destruct(i == i0).
   inverts* e.
   forwards* h8: H5 i0.
   destruct(i == i0).
   inverts* e. auto.
   forwards* h9: IHtype2 h4.
   simpl in *; lia.
   forwards* h10: tlookup_get_ty h1.
   forwards* h11: tlookup_sz h1.
   forwards* h12:IHn h2.
   lia.
   apply CS_andr; auto.
   forwards*: in_ityp_rcd h0.
   forwards*: get_ty_csub_aux h10 h12.
  -
   inductions H; simpl in *; eauto.
   lets(i&tt1&tt2&none&lup&acs): H3.
   inverts* none.
  -
   inductions H2; intros;simpl in *; try solve[inverts H0];eauto.
   assert(i `in` collectLabel t1) as h0.
   fsetdec.
   forwards* h1: lookup_some h0.
   inverts h1 as h1.
   forwards* h2: H5 i x T1.
   destruct(i == i); auto.
   exfalso; apply n0; auto.
   assert((collectLabel T2) [<=] collectLabel t1) as h3.
   fsetdec.
   assert(forall (i : atom) (t2 t3 : ttyp),
   i `in` (collectLabel T2) ->
   Tlookup i t1 = Some t2 ->
   Tlookup i T2 = Some t3 -> Acs t2 t3) as h4.
   introv h5 h6 h7.
   destruct(i == i0).
   inverts* e.
   forwards* h8: H5 i0.
   destruct(i == i0).
   inverts* e. auto.
   forwards* h9: IHtype2 h4.
   simpl in *; lia.
   forwards* h10: tlookup_get_ty h1.
   forwards* h11: tlookup_sz h1.
   forwards* h12:IHn h2.
   lia.
   apply CS_andr; auto.
   forwards*: in_ityp_rcd h0.
   forwards*: get_ty_csub_aux h10 h12.
  -
   inductions H; simpl in *; eauto.
   lets(i&tt1&tt2&none&lup&acs): H3.
   inverts* none.
Qed.


Lemma Aproj_proj: forall i A B,
  type A ->
  aproj i A B ->
  get_ty (transt A) i (transt B).
Proof.
 introv ty apj .
 inductions apj;eauto;simpl.
 - apply g_dyn; eauto.
   unfold not; intros nt; inverts nt.
 -  
   forwards*: tlookup_get_ty H.
 -
   forwards*: tlookup_get_ty H.
 -
   forwards*: label_notbelongw H.
   forwards*: notin_nityp_rcd H0.
Qed. 



Lemma atyping_type: forall G e T t,
 Atyping G e T t ->
 type T.
Proof.
  introv atyp.
  inductions atyp; eauto.
  -
    pick fresh x.
    forwards*: H0.
  -
    inverts* IHatyp1.
Qed.


Lemma x_notin: forall x G,
 x # G ->
 x # transg G.
Proof.
  introv notin. gen x.
  inductions G; intros; eauto.
  destruct a. unfold transg.
  fold transg.
  forwards*: IHG x. 
Qed.


Lemma context_trans: forall G,
 uniq G -> uniq (transg G).
Proof.
  introv uq.
  inductions uq; simpl;eauto.
  forwards*:  x_notin H.
Qed.


Lemma bind_trans: forall x A G,
 binds x A G ->
 binds x (transt A) (transg G).
Proof.
  introv bind.
  inductions G; eauto.
  destruct a. simpl.
  inverts* bind.
  inverts* H.
Qed.




Lemma type_disjoint: forall A,
 type A ->
 well (transt A).
Proof.
  introv ty.
  inductions ty; simpl in *;eauto.
  -
    forwards* h1: Anotin_disjoint H0.
    forwards*: type_rt_ty H.
  -
    forwards* h1: Anotin_disjoint2 H0.
    forwards*: type_rw_ty H.
Qed.




Theorem AGT_Soundness: forall e t A G,
 Atyping G e A t -> Typing (transg G) t Inf (transt A).
Proof.
 introv atyp. 
 lets atyp': atyp.
 inductions atyp; simpl in *; eauto.
 - forwards*: context_trans H.
 - forwards*: context_trans H.
 - forwards*:  bind_trans H0.
   forwards*: context_trans H.
   (* forwards*: type_disjoint H1. *)
 -
   eapply Typ_anno; auto.
   pick fresh x and apply Typ_abs.
   forwards h1: H0 x; auto.
   eapply Typ_cs; eauto.
   forwards* h2: atyping_type atyp'.
   inverts h2.
   forwards*: type_disjoint H5.
   forwards* h2: atyping_type atyp'.
   inverts h2.
   forwards*: type_disjoint H4.
   eauto.
 -
   forwards*: IHatyp1.  forwards*: IHatyp2.
   forwards* h1: atyping_type atyp1.
   inverts h1.
   forwards* h2: atyping_type atyp2.
   apply Typ_app with (A := (t_arrow (transt A1) (transt B))) 
   (A1 :=(transt A1) ); eauto.
   forwards*: type_disjoint H4.
   forwards*: Acs_CS_Soundness H.
 -
    eapply Typ_anno; eauto.
    eapply Typ_cs; eauto.
    forwards*: Acs_CS_Soundness H.
    forwards*: type_disjoint H0.
 -
   eapply Typ_proj; eauto.
   forwards*: atyping_type atyp.
   forwards*: Aproj_proj H.
 - 
   eapply Typ_merge; eauto.
   forwards*: atyp_rt_ty atyp2.
   forwards*: Anotin_disjoint H1.
Qed.


Print Assumptions AGT_Soundness.