Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        syntaxb_ott
        rules_inf
        rulesb_inf
        Infrastructure
        Infrastructure_b
        Deterministic
        Typing_b
        Typing
        Type_Safety
        Lia
        ttyping.

Require Import List. Import ListNotations.
Require Import Strings.String.

(* Require Import lia. *)

Parameter label : atom.

Ltac size_ind_auto :=
  ( eapply_first_lt_hyp ;
    try reflexivity;
    try lia ;
    try eauto ).


(* aux both *)

Lemma principle_if: forall v A t,
    value v -> typing nil v Inf3 A t -> dynamic_type v = A.
Proof.
     introv H typ.
     inductions H; inverts* typ; eauto.
Qed.



Lemma Cast_value3: forall v A v' p b,
    value v -> Cast v p b A (e_exp v') -> value v'.
Proof with auto.
 introv val red.
 forwards*: Cast_value red.
Qed.




Lemma sim_refl: forall A,
 sim A A.
Proof.
  intros.
  inductions A; eauto.
Qed.


Lemma fillb_cast: forall v A p b B,
  (trm_cast v A p b B) = (fillb (castCtxb A p b B )  v).
Proof.
  introv.
  eauto.
Qed.


Lemma fillb_appl: forall e1 e2,
  (trm_app e1 e2) = (fillb (appCtxLb e2)  e1).
Proof.
  introv.
  eauto.
Qed.


Lemma fillb_appr: forall e1 e2,
  (trm_app e1 e2) = (fillb (appCtxRb e1)  e2).
Proof.
  introv.
  eauto.
Qed.



Lemma value_anno:forall v t l b,
 value(e_anno v l b t) ->
 value v.
Proof.
  introv val.
  inverts* val.
Qed.




Definition Deterministic_blame_Calculus := forall t r1 r2,
  bstep t r1 ->
  bstep t r2 ->
  r1 = r2.


(** typing complete *)




(** typing soundness *)

Definition typing_typing_aux G dir e A  := 
   match dir with 
    | Chk3 l b => Typing G e Chk A 
    | _   => Typing G e Inf A
   end.

Lemma typing_typing: forall G dir e  A t,
 typing G e dir A t ->
 typing_typing_aux G dir e A.
Proof.
  introv typ.
  inductions typ; unfold typing_typing_aux in *; intros; eauto.
Qed.


Lemma typing_typing1: forall G e t A B,
 typing G e Inf3 A t ->
 Typing G e Inf B ->
 A = B.
Proof.
  introv typ1 typ2. gen B.
  inductions typ1;intros; 
  try solve[inductions typ2; eauto].
  -
    inverts* typ2.
    forwards*: binds_unique H0 H4.
  -
    inverts typ2.
    forwards*: IHtyp1_1 H6.
    inverts* H. inverts* H3.
  -
    inverts typ2.
    forwards* h1: IHtyp1_1 H2.
    inverts* h1.
  -
    inverts typ2.
    forwards*: IHtyp1_1 H6.
    subst. inverts* H3.
Qed.



Lemma value_valueb2: forall e t A,
 btyping nil t A e -> value e ->
 valueb t.
Proof.
  introv typ val. gen A t.
  inductions val; intros;
  try solve[inverts* typ].
  -
    forwards*: btyping_regular_1 typ.
    inverts typ; eauto.
  -
    inverts typ. 
    forwards*: IHval.
    forwards* h1: btyping_typing H5.
    forwards* h2: principle_inf h1.
    rewrite h2 in *; eauto.
    inverts* H.
  -
    inverts typ. 
    forwards*: IHval.
    forwards* h1: btyping_typing H5.
    forwards* h2: principle_inf h1.
    rewrite h2 in *; eauto.
Qed.


Lemma valueb_value2: forall e t A,
 btyping nil t A e -> valueb t ->
 value e.
Proof.
  introv typ val. gen A e.
  inductions val; intros;
  try solve[inverts* typ].
  - 
    forwards* h1: btyping_regular_3 typ. inverts* typ.
  -
     inverts typ. 
    forwards*: IHval.
    forwards* h1: btyping_typing H7.
    forwards* h2: principle_inf h1.
  -
     inverts typ. 
    forwards*: IHval.
    forwards* h1: btyping_typing H8.
    forwards* h2: principle_inf h1.
    rewrite <- h2 in *; eauto.
Qed.





Lemma lc_lcb: forall E e t dir A,
 typing E e dir A t ->
 lc_exp e ->
 lc_term t.
Proof.
  introv typ H. 
  inductions typ;try solve[inverts* H];eauto. 
  -
    inverts H1. 
    pick fresh x.
    forwards*: H.
Qed.



Lemma value_valueb1: forall e t A,
 typing nil e Inf3 A t -> value e ->
 valueb t.
Proof.
  introv typ H. gen t A.
  inductions H; intros; 
  try solve [inverts* typ].
  - inverts typ. 
    pick fresh x.
    forwards*: H8.
    forwards*: lc_lcb H. 
  - inverts typ.
    forwards*: value_lc H.
    forwards*: lc_lcb H1.  
    inverts* H8. 
    forwards*: IHvalue.
    forwards* h1: principle_if H7.
    rewrite h1 in H0. inverts H0.
    eapply valueb_fanno; eauto.
  - inverts typ.
    forwards*: value_lc H0.
    forwards*: lc_lcb H8.
    inverts* H8.
    inverts* H2.
    forwards*: IHvalue.
    forwards* h1: principle_if H7.
    rewrite h1 in H.
    apply valueb_dyn; eauto.
Qed.





Lemma UG_sim_l: forall A B C,
  UG A B ->
  sim C A ->
  sim C B.
Proof.
  introv h1 h2.
  inverts h1 as h11 h12.
  inverts h12 as h12 h13.
  inverts h13 as h13 h14.
  inverts h12.
  -
    inverts h11.
    exfalso; apply h13; auto.
    exfalso; apply h14; auto.
  -
    inverts h11.
    inverts* h2.
    inverts* h2.
  -
    inverts h11.
    exfalso; apply h14; auto.
    inverts* h2.  
Qed.





Lemma ground_eq: forall A B ,
  Ground A ->
  Ground B ->
  sim A B ->
  A = B.
Proof.
  introv g1 g2 sb.
  inverts g1; inverts g2; inverts* sb.
Qed.


Lemma Casting_soundness: forall v t v' p b A,
  typing nil (e_anno v p b A) Inf3 A t->
  value v ->
  Cast v p b A (e_exp v') ->
  exists t', t ->* (t_term t') /\ typing nil v' Inf3 A t'.
Proof.
  introv  Typ val Red. gen t.
  inductions Red; intros;
  try solve[inverts Typ as typ;inverts* typ];
  try solve[inverts Typ as typ;inverts typ as typ;inverts typ].
  - 
    inverts Typ as typ.
    inverts typ as typ.
    inverts typ as typ.
    exists. split.
    apply star_one.
    apply bStep_lit; eauto. 
    apply typ_lit; eauto.
  - 
    inverts Typ as typ.
    inverts typ as typ.  
    forwards* h1: value_valueb1 val.
    inverts typ. 
    exists.
    splits.
    apply star_one.
    apply bStep_dd; eauto.
    eapply typ_anno; eauto.
  - 
    inverts Typ as typ. 
    inverts typ as typ.
    forwards* h1: principle_if typ.
    rewrite h1 in *.
    forwards* h3: UG_to_sim H.
    assert(typing [] v (Chk3 p b) B (trm_cast t0 p b A B)) as h4; auto.
    assert( typing [] (e_anno v p b B) Inf3 B (trm_cast t0 p b A B)) as h2; eauto.
    forwards* h6: value_valueb1 typ.
    forwards* h7: IHRed h2.
    lets(t'&h8&h9):h7.
    exists. split.
    eapply star_trans.
    apply star_one.
    eapply bStep_anyd;eauto.
    apply multi_red_cast.
    apply h8.
    apply typ_anno; eauto.
  - 
    inverts Typ as typ. 
    inverts val.
    forwards* h1: Cast_sim_aux Red.
    inverts typ as typ.
    inverts typ as typ.
    inverts typ as typ.
    forwards* h5: principle_if typ.
    rewrite h5 in *.
    assert( typing [] (e_anno v p b2 A) Inf3 A (trm_cast t p b2 A0 A)) as h6; eauto.
    forwards* h7: IHRed.
    lets(t'&h8&h9):h7.
    forwards* h10: value_valueb1 typ.
    forwards* h11: UG_sim_l H h1.
    forwards* h12:ug_ground_r H.
    forwards* h13: ground_eq h11.
    substs*.
    exists. split.
    eapply star_trans.
    apply star_one.
    apply bStep_dyna; auto.
    apply H.
    rewrite fillb_cast.
    eapply star_trans.
    apply star_one.
    apply Step_evalb; simpl in *;auto.
    simpl.
    apply h8.
    auto.
  -
    inverts val.
    inverts Typ as typ.
    inverts typ as typ.
    forwards* h1: value_valueb1 typ.
    inverts typ as typ.
    inverts typ as typ.
    forwards* h2: principle_if typ.
    rewrite h2 in *.
    forwards* h3: value_valueb1 typ.
Qed.



Lemma soundness_mul_one: forall e t e' A dir ,
  typing nil e dir A t->
  step e (e_exp e') ->
  exists t', t ->* (t_term t') /\ typing nil e' dir A t' .
Proof.
  introv Typ Red. gen A t dir.
  inductions Red; intros;
  try solve[inverts Typ as typ; inverts typ as typ;inverts typ].
  - (* fill do *)
    destruct E; unfold fill in *;
    try solve[inverts Typ as typ; inverts typ].
    + inverts Typ.
      *
      forwards*: IHRed H8. inverts H0. inverts H1.
      exists. split.
      apply multi_red_app2; eauto.
      inverts H.
      forwards*: lc_lcb H3.
      eapply typ_app; eauto.
      *
      inverts H0.
      --
      forwards* h1: IHRed H9. 
      lets(tt1&h2&h3): h1. 
      exists. split.
      apply star_trans with (b:= trm_cast (trm_app tt1 t2) l0 b0 A0 A).
      apply multi_red_cast; auto.
      apply multi_red_app2; auto.
      inverts H.
      forwards*: lc_lcb H2. 
      apply bstep_refl.
      eapply typ_sim; eauto.
      --
      forwards* h1: IHRed H9. 
      lets(tt1&h2&h3): h1. 
      exists. split.
      apply multi_red_cast.
      apply multi_red_app2.
      inverts H.
      forwards*: lc_lcb H2. 
      apply multi_red_cast.
      apply h2.
      eapply typ_sim; eauto.
      *
      forwards* h1: IHRed H8. 
      lets(tt1&h2&h3): h1. 
      exists. split.
      apply multi_red_app2.
      inverts H as h6.
      forwards*: lc_lcb h6.
      apply multi_red_cast.
      apply h2.
      eapply typ_appd; eauto.
    + 
      inverts Typ. 
      * inverts H as h1.
      forwards*: value_valueb1 H3.
      forwards* h2: IHRed H9. 
      lets(tt1&h5&h6): h2. 
      exists. split.
      forwards h8: multi_red_app H h5.
      apply h8.
      eapply typ_app; eauto.
      *
      inverts H. inverts H0.
      -- 
      forwards*: value_valueb1 H10.
      forwards* h1: IHRed H11. 
      lets(tt1&h2&h3): h1.  
      exists. split.
      apply multi_red_cast.
      forwards h6: multi_red_app H h2.
      apply h6.
      eapply typ_sim; eauto.
      --
      forwards* h1: principle_if H10.
      rewrite h1 in *.
      inverts* H4.
      *
      inverts H. 
      forwards* h1: principle_if H8.
      rewrite h1 in *.
      inverts* H2.
    + inverts Typ. 
      * forwards* h1: IHRed H8. 
        lets(tt1&h2&h3): h1. 
        exists. split.
        apply h2.
        apply typ_anno; eauto.
      * inverts H0.
        forwards* h1: IHRed H9. 
        lets(tt1&h2&h3): h1. 
        exists. split.
        apply multi_red_cast.
        apply h2.
        apply typ_sim;eauto.
    + inverts Typ.
      *
      inverts H0.
      forwards* h1: IHRed H5. 
      lets(tt1&h2&h3): h1. 
      exists. split.
      apply multi_red_cast.
      apply multi_red_app2; eauto.
      inverts H.
      forwards*: lc_lcb H6.
      apply typ_sim;eauto.
      *
      inverts H.
      forwards* h1: IHRed H3. 
      lets(tt1&h2&h3): h1. 
      exists. split.
      apply multi_red_app2; eauto.
      forwards*: lc_lcb H1.
      eapply typ_appv;eauto.
    +
      inverts Typ.
      *
      inverts H0.
      forwards* h1: IHRed H6. 
      lets(tt1&h2&h3): h1. 
      exists. split.
      apply multi_red_cast.
      apply multi_red_app.
      inverts H.   
      forwards*: value_valueb1 H5.
      apply h2.
      apply typ_sim;eauto.
      *
      forwards* h1: IHRed H7. 
      lets(tt1&h2&h3): h1. 
      exists. split.
      apply multi_red_app.
      inverts H.   
      forwards*: value_valueb1 H3.
      apply h2.
      eapply typ_appv;eauto.
  - (* beta *) 
    inverts* Typ.
    + 
      inverts H1.
      forwards*: value_valueb1 H7.
      forwards*: value_valueb1 H6.
      inverts H6.
      exists. split.
      eapply star_trans.
      apply multi_red_cast.
      apply star_one.
      apply bStep_beta; eauto.
      forwards*: lc_lcb H.
      apply bstep_refl.
      apply typ_sim; eauto.
      apply typ_anno; eauto.
      pick fresh y.
      forwards* h1: H15.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply typing_c_subst_simpl; auto.
      apply h1. auto.
    +
      forwards*: value_valueb1 H4.
      forwards*: value_valueb1 H8.
      inverts H4.
      exists. split.
      eapply star_trans.
      apply star_one.
      apply bStep_beta; eauto.
      forwards*: lc_lcb H.
      apply bstep_refl.
      apply typ_anno; eauto.
      pick fresh y.
      forwards* h1: H14.
      rewrite (subst_exp_intro y); auto.
      rewrite (subst_term_intro y); auto.
      eapply typing_c_subst_simpl; auto.
      apply h1. auto.
  - (* annov *) 
    inverts Typ.
    assert (typing nil (e_anno v l b A0) Inf3 A0 t).
    eauto.
    forwards*: Casting_soundness H0.
    inverts H2.
    assert (typing nil (e_anno v l b A1) Inf3 A1 t0).
    eauto.
    forwards* h1: Casting_soundness H0.
    lets(tt1&h2&h3): h1. 
    exists. split.
    apply multi_red_cast; eauto.
    apply typ_sim;eauto.
  - (* abeta *)  
    inverts Typ as typ typ0. 
    *
    inverts typ as typ1 typ2. 
    forwards*: value_valueb1 typ1.
    forwards*: value_valueb1 typ2.
    inverts typ1 as typ1. inverts typ1 as typ1.
    forwards* h1: principle_if typ1.
    rewrite h1 in *. subst.
    inverts H12. 
    exists. split.
    apply multi_red_cast.
    apply star_one. 
    apply bStep_abeta; eauto. 
    apply typ_sim; eauto.
    apply typ_anno; eauto. 
    * 
    inverts typ as typ.
    inverts typ as typ1.
    forwards* h1: value_valueb1 typ0.
    forwards* h2: value_valueb1 typ1.
    forwards* h3: principle_if typ1.
    rewrite h3 in *. subst.
    inverts H10. 
    exists. split.
    apply star_one. 
    apply bStep_abeta; eauto. 
    apply typ_anno; eauto.
  -  (* equal *)  
    inverts Typ.
    +
    forwards* h1: principle_if H11. 
    rewrite h1 in *. inverts H1.
    assert(typing nil (e_anno v2 l b A) Inf3 A t2).
    apply typ_anno; auto. 
    forwards* h2: Casting_soundness H2.
    lets(tt1& h5& h6): h2.
    forwards*:  Cast_value2 H2.
    forwards*: value_valueb1 H11.
    exists. splits.
    apply multi_red_app; eauto.
    eapply typ_appv; eauto.
    +
    inverts H3 as typ1 typ2.
    *
    forwards* h1: principle_if typ1. 
    rewrite h1 in *. inverts H1.
    forwards*: value_valueb1 typ1.
    assert(typing nil (e_anno v2 l b A) Inf3 A t2).
    apply typ_anno; auto. 
    forwards* h2: Casting_soundness H2.
    lets(tt1&h5&h6): h2.
    forwards*:  Cast_value2 H2.
    exists. splits.
    apply multi_red_cast.
    apply multi_red_app; eauto.
    eapply typ_sim; eauto.
    *
    forwards* h2: principle_if typ1. rewrite h2 in *. inverts H1.
    +
    forwards* h1: principle_if H11. rewrite h1 in *. inverts H1.
  -
    inverts Typ; try solve[inverts* H9].
    +
    inverts H1; try solve[inverts H10].
    forwards* h1: value_valueb1 H10.
    exists. splits.
    eapply bstep_refl.
    eapply typ_sim; eauto.
    +
    forwards* h1: value_valueb1 H9.
    exists. splits.
    eapply bstep_refl.
    eapply typ_app; eauto.
  - (* add *)
    inverts Typ.
    +
    inverts H. inverts H4. inverts H5.
    exists. splits.
    apply multi_red_cast.
    apply star_one; eauto.
    eapply typ_sim; eauto.
    +
    inverts H2. inverts H6.
    exists. splits.
    apply star_one; eauto.
    eapply typ_addl; eauto.
  - (* addli *)
    inverts Typ.
    +
    inverts H. inverts H4. inverts H5.
    exists. splits.
    apply multi_red_cast.
    apply star_one; eauto.
    eapply typ_sim; eauto.
    +
    inverts H2. inverts H6.
    exists. splits.
    apply star_one; eauto.
    eapply typ_lit; eauto.
Qed.


Theorem soundness: forall e t v1 A,
  typing nil e Inf3 A t->
  e ->** (e_exp v1) ->
  value v1 ->
  exists t', t ->* (t_term t') /\ valueb t' /\ typing nil v1 Inf3 A t' .
Proof.
  introv typ red val. gen A t.
  inductions red;intros.
  -
  forwards*: value_valueb1 val.
  -
  forwards*: soundness_mul_one H.
  inverts H0. inverts H1.
  forwards*: IHred H2.
  inverts* H1. 
Qed.



Lemma ground_dyn: forall A B, 
 UG A B ->
 B = (t_arrow t_dyn t_dyn) \/ B = (t_pro t_dyn t_dyn).
Proof.
  introv h1.
  inverts h1 as h1 h2.
  inverts h2 as h2 h3.
  inverts h3 as h3 h4.
  inverts* h2.
  inverts* h1.
Qed.

Lemma UG_inf: forall A B,
 UG A B ->
 B = (t_arrow t_dyn t_dyn) /\ (exists t1 t2, A = (t_arrow t1 t2)) \/
 B = (t_pro t_dyn t_dyn) /\ (exists t1 t2, A = (t_pro t1 t2)).
Proof.
 introv ug.
 inverts ug as  h1 h2.
 inverts h2 as h2 h3.
 inverts h3 as h3 h4.
 inverts h2;inverts* h1.
Qed.


Lemma UG_inf_arr: forall A B t v,
 valueb t ->
 btyping [] t A v ->
 UG A B ->
 B = (t_arrow t_dyn t_dyn) /\ (exists t1 t2, A = (t_arrow t1 t2)).
Proof.
 introv val typ ug.
 inverts ug as  h1 h2.
 inverts h2 as h2 h3.
 inverts h3 as h3 h4.
 inverts h2;inverts* h1.
 inverts val; try solve[inverts typ].
Qed.



Lemma UG_inf_arr2: forall A B t v,
 value v ->
 typing [] v Inf3 A t ->
 UG A B ->
 B = (t_arrow t_dyn t_dyn) /\ (exists t1 t2, A = (t_arrow t1 t2)).
Proof.
 introv val typ ug.
 inverts ug as  h1 h2.
 inverts h2 as h2 h3.
 inverts h3 as h3 h4.
 inverts h2;inverts* h1.
 inverts val; try solve[inverts typ].
Qed.



Lemma UG_inf_arr_r: forall A B t v,
 valueb t ->
 btyping [] t B v ->
 UG A B ->
 B = (t_arrow t_dyn t_dyn) /\ (exists t1 t2, A = (t_arrow t1 t2)).
Proof.
 introv val typ ug.
 inverts ug as  h1 h2.
 inverts h2 as h2 h3.
 inverts h3 as h3 h4.
 inverts h2;inverts* h1.
 inverts val; try solve[inverts typ].
Qed.


Lemma UG_inf_arr_r2: forall A B t v,
 value v ->
 typing [] v Inf3 B t ->
 UG A B ->
 B = (t_arrow t_dyn t_dyn) /\ (exists t1 t2, A = (t_arrow t1 t2)).
Proof.
 introv val typ ug.
 inverts ug as  h1 h2.
 inverts h2 as h2 h3.
 inverts h3 as h3 h4.
 inverts h2;inverts* h1.
 inverts val; try solve[inverts typ].
Qed.


Lemma not_sim_neq: forall A B,
 not (sim A B) ->
 not( A = B).
Proof.
 introv h1.
 unfold not;intros nt.
 inverts* nt.
Qed.




Lemma Cast_completeness: forall v t B A t' l b ,
  btyping nil t B v ->
  valueb t ->
  bstep (trm_cast t l b B A) (t_term t') ->
  (exists  n t2 v',  bbsteps t' (t_term t2) n /\ Cast v l b A (e_exp v') /\
  btyping nil t2 A v' /\ 0<=n <= 1) \/ (bstep t' (t_blame l b) /\ (Cast v l b A (e_blame l b))).
Proof.
  introv typ val red.
  forwards* h1: valueb_value2 val.
  inductions red; try solve[inverts* typ].
  - (* fillb *)
    destruct E; unfold fillb; inverts x;
    try forwards*: bstep_not_value red.
  -
    inverts* typ; inverts h1.
    left. 
    exists.
    splits*.
  -
     inverts* typ; inverts h1.
     left. 
    exists.
    splits*.
  -
    forwards* h2: UG_inf_arr typ.
    inverts h2 as h2 h3.
    lets(t1&t2&h4):h2.
    substs*.
    forwards* h5:btyping_typing typ.
    forwards* h6: principle_inf h5.
    rewrite <- h6 in *.
    left.
    exists. splits. 
    apply bbstep_refl.
    eapply Cast_anyd.
    apply H0.
    eauto.
    eapply btyp_cast; eauto.
    eapply btyp_cast; eauto.
    rewrite h6; auto.
    lia.
    lia.
  -
    inverts typ as typ; try solve[inverts H].
    inverts val as h2 h3.
    inverts H as h4 h5.
    forwards* h8: ug_ground_r H0.
    forwards* h6:sim_decidable A0 B0.
    inverts h6 as h6.
    +
      forwards* h7: ground_eq h6.
      subst*.
      forwards* h9: UG_inf_arr_r typ.
      inverts h9 as h9.
      lets(t1&t2&h11):h9.
      subst.
      inverts h1 as h1' h1''.
      forwards* h12:btyping_typing typ.
      forwards* h13: principle_inf h12.
      left.
      exists. splits.
      eapply sstar_one.
      rewrite fillb_cast.
      apply Step_evalb;eauto.
      eapply Cast_dyna; simpl;eauto.
      eapply btyp_cast; eauto.
      lia. lia.
    +
      forwards* h9: not_sim_neq h6.
      inverts h1 as h1 h1'.
      forwards* h12:btyping_typing typ.
      forwards* h13: principle_inf h12.
      right. rewrite fillb_cast.
      rewrite fillb_cast.
      splits.
      apply Step_blameb;eauto.
      simpl.
      eapply bStep_vanyp;eauto.
      eapply Cast_blame.
      rewrite h13.
      unfold not;intros nt.
      forwards*: UG_sim_l H0 nt.
  -
    inverts* typ. 
    forwards* h2:btyping_typing H8. 
    forwards*: valueb_value2 H8.
    forwards* h3: principle_inf h2.
    rewrite <- h3.
    left. exists. splits*.
    rewrite h3; auto.
Qed.




Theorem completeness_gen_ns: forall e t t' A n,
 size_exp e + size_term t < n ->
  btyping nil t A e ->
  bstep t (t_term t') ->
  (exists e' t'' n, bbsteps t' (t_term t'') n /\ steps e (e_exp e') /\ btyping nil t'' A e' /\ 0<=n<=1) \/
  exists l b, (bstep t' (t_blame l b)) /\ steps e (e_blame l b).
Proof.
  introv sz Typ Red. gen e t t' A.
  induction n; intros; try lia.
  lets Red': Red.
  inductions Red; intros.
  - clear IHRed.
     destruct E; unfold fillb in *; simpl in *.
    +
    forwards h1: btyping_typing Typ.
    forwards* lc: Typing_regular_1 h1.
    inverts Typ; simpl in *.
    inverts h1; simpl in *.
    forwards* h2: IHn Red H3. simpl in *; lia.
    inverts H.
    inverts* h2.
    *
    lets(vv1&tt2&nn1&rred2&rred1&typ2&ssz): H.
    inverts lc.
    left.
    exists. splits.
    eapply mmulti_red_app2.
    auto.
    apply rred2.
    apply multi_rred_appv2.
    auto. apply rred1.
    eapply btyp_app; eauto.
    lia.
    lia.
    *
    lets(ll1&bb1&rred1&rred2):H.
    right. exists.
    splits.
    rewrite fillb_appl.
    apply Step_blameb;eauto.
    eapply multi_bblame_appv2;eauto.
    inverts* lc.
    +
    inverts Typ. inverts H.
    forwards* h1: valueb_value2 H3.
    forwards* h2: IHn Red H6. simpl in *; lia.
    inverts h2.
    *
    lets(vv1&tt2&nn1&rred2&rred1&typ2&ssz): H.
    left.
    exists. splits.
    eapply mmulti_red_app.
    auto.
    apply rred2.
    apply multi_rred_appv.
    auto. apply rred1.
    eapply btyp_app; eauto.
    lia.
    lia.
    *
    lets(ll1&bb1&rred1&rred2):H.
    right. exists.
    splits.
    rewrite fillb_appr.
    apply Step_blameb;eauto.
    eapply multi_bblame_appv;eauto.
    +
     forwards* lc: btyping_regular_3 Typ.
     inverts Typ; simpl in *.
     inverts lc.
     forwards* h1: IHn Red H8. simpl in *; lia.
     inverts h1.
     lets(vv1&tt2&nn1&rred2&rred1&typ2&ssz): H0.
     left.
     exists. splits.
     apply mmulti_red_cast.
     apply rred2. 
     apply multi_rred_anno.
     apply rred1.
     eapply btyp_cast; eauto.
     lia.
     lia.
     lets(ll1&bb1&rred1&rred2):H0.
     right. exists.
     splits.
     rewrite fillb_cast.
     apply Step_blameb;eauto.
     eapply multi_bblame_anno;eauto.
  -
    forwards* lc: btyping_regular_3 Typ.
    inverts Typ. inverts H4.
    forwards* h1: valueb_value2 H7.
    inverts lc. inverts H3.
    pick fresh x.
    forwards* h3: H9 x.
    left.
    exists. splits.
    eapply bbstep_refl.
    eapply stars_one.
    eapply Step_beta.
    auto.
    auto.
    rewrite (subst_term_intro x);eauto.
    rewrite (subst_exp_intro x);eauto.
    assert((e_anno [x ~> e2] (e ^^ e_var_f x) l0 b A0) = ([x ~> e2](e_anno (e ^^ e_var_f x) l0 b A0))) as h2.
    simpl; reflexivity.
    rewrite h2 in *.
    eapply btyping_c_subst_simpl;eauto.
    lia. lia.
  -
    inverts Typ.
    forwards* h1: valueb_value2 H7.
    forwards*: Cast_completeness H7 Red'.
    inverts H.
    ++
    lets(nn1&tt2&vv1&rred2&rred1&typ1&ssz): H0.
    inverts* H7.
    inverts* rred1.
    left.
    exists. splits.
    eapply bbstep_refl.
    apply stars_one.
    apply Step_annov; eauto.
    unfold not;intros nt;inverts* nt.
    auto.
    lia. lia.
    ++
    lets(rred1&rred2):H0.
    forwards*: bstep_not_value rred1.
  -
    inverts Typ. inverts H4.
    inverts H. 
    forwards* h1: valueb_value2 H12.
    forwards* h3: valueb_value2 H7.
    forwards* h4: btyping_typing H12.
    forwards* h5: principle_inf h4.
    inverts H13.
    left.
    exists. splits.
    eapply bbstep_refl.
    eapply stars_one.
    eapply Step_abeta;eauto.
    eapply btyp_cast;eauto.
    lia. lia.
  -
    inverts Typ.
    forwards* h1: valueb_value2 H8.
    forwards* h2: Cast_completeness H8 Red'.
    inverts h2.
    ++
    lets(nn1&tt2&vv1&rred2&rred1&typ1&ssz): H0.
    forwards* h3: value_decidable (e_anno e0 p b t_dyn).
    inverts h3.
    +
    forwards* h4: value_cast_keep2 rred1. inverts h4.
    left.
    exists. splits.
    apply rred2.
    apply step_refl.
    auto.
    lia.
    lia.
    +
    left.
    exists. splits.
    apply rred2.
    apply stars_one.
    apply Step_annov; eauto.
    auto.
    lia.
    lia.
    ++
    lets(rred1&rred2):H0.
    forwards*: bstep_not_value rred1.
  -
    inverts Typ as typp1 typp2.
    forwards* h1: valueb_value2 typp1.
    forwards* hh1: Cast_completeness typp1 Red'.
    inverts hh1 as hh1.
    ++
    lets(nn1&tt2&vv1&rred2&rred1&typ1&ssz): hh1.
    forwards* h2: value_decidable (e_anno e0 p b t_dyn).
    inverts h2.
    +
    forwards* h3: value_cast_keep2 rred1. inverts h3.
    left.
    exists. splits.
    apply rred2.
    apply step_refl.
    auto.
    lia.
    lia.
    +
    left.
    exists. splits.
    apply rred2.
    apply stars_one.
    apply Step_annov; eauto.
    auto.
    lia.
    lia.
    ++
    lets(rred1&rred2):hh1.
    forwards hh2: cast_dyn_not_fail rred2;auto.
    inverts hh2 as hh2;inverts hh2.
  -
    inverts Typ as typp1 typp2.
    forwards* h1: valueb_value2 typp1.
    forwards* hh1: Cast_completeness typp1 Red'.
    inverts hh1 as hh1.
    ++
    lets(nn1&tt2&vv1&rred2&rred1&typ1&ssz): hh1.
    forwards* h2: value_decidable (e_anno e0 p b A0).
    inverts h2.
    +
    forwards* h3: value_cast_keep2 rred1. inverts h3.
    left.
    exists. splits.
    apply rred2.
    apply step_refl.
    auto.
    lia.
    lia.
    +
    left.
    exists. splits.
    apply rred2.
    apply stars_one.
    apply Step_annov; eauto.
    auto.
    lia.
    lia.
    ++
    inverts typp1; try solve[inverts H].
    lets(rred1&rred2):hh1.
    right. exists.
    splits*.
    eapply step_b;eauto.
    eapply Step_annov;eauto.
    unfold not;intros nt;inverts nt as nt1 nt2; 
    try solve[inverts nt2];
    try solve[inverts nt1]. 
  -
    inverts Typ.
    forwards* h1: valueb_value2 H9.
    forwards*: Cast_completeness H9 Red'.
    inverts H1.
    ++
    lets(nn1&tt2&vv1&rred2&rred1&typ1&ssz): H2.
    forwards* h2: value_decidable (e_anno e0 p b2 A0).
    inverts h2.
    +
    forwards* h3: value_cast_keep2 rred1. inverts h3.
    left.
    exists. splits.
    apply rred2.
    apply step_refl.
    auto.
    lia.
    lia.
    +
    left.
    exists. splits.
    apply rred2.
    apply stars_one.
    apply Step_annov; eauto.
    auto.
    lia.
    lia.
    ++
    lets(rred1&rred2):H2.
    forwards*: bstep_not_value rred1.
  -
    inverts Typ. inverts H2. inverts* H5.
    left. exists. splits.
    eapply bbstep_refl.
    eapply stars_one;eauto.
    eapply btyp_addl;eauto.
    lia. lia.
  -
    inverts Typ. inverts H2. inverts* H5.
    left. exists. splits.
    eapply bbstep_refl.
    eapply stars_one;eauto.
    eapply btyp_lit;eauto.
    lia. lia.
Qed.




Theorem completeness_gen_n: forall e t t' A n n1,
  Deterministic_blame_Calculus ->
  n < n1 ->
  btyping nil t A e ->
  bbsteps t (t_term t') n ->
  valueb t' ->
  exists e', (steps e (e_exp e')) /\ btyping nil t' A e' /\ value e'.
Proof.
  introv dd sz typ red val. gen t t' A e n.
  inductions n1; intros; try solve[lia].
  inverts* red.
  -
  forwards*: valueb_value2 typ.
  -
  forwards*: completeness_gen_ns H0.
  inverts* H.
  +
  lets(ee1 &ee2&nn2& rred1&rred2&typ1&ssz): H1.
  inverts H2.
  *
  inverts* rred1.
  forwards*: valueb_value2 typ1.
  forwards*: bstep_not_value H2.
  *
  destruct nn2.
  ++
  inverts* rred1.
  assert(bbsteps ee2 (t_term t') (1+n)).
  eapply bbstep_n;eauto.
  forwards*: IHn1 H.
  lia.
  inverts* H2. 
  ++
  assert(nn2 = 0).
  lia.
  rewrite H in *.
  inverts* rred1.
  inverts* H8.
  forwards* h1: dd H3 H7.
  inverts* h1.
  forwards*: IHn1 H5.
  lia.
  inverts* H2. 
  +
  inverts* H1.
  inverts* H.
  inverts* H1.
  inverts* H2.
  forwards*: bstep_not_value H.
  forwards*: dd H H4.
  inverts* H1.
Qed.




Lemma bsteps_bbsteps: forall t r,
 bsteps t r ->
 exists n, bbsteps t r n.
Proof.
  introv red.
  inductions red; eauto.
  inverts* IHred.
  inverts* IHred.
Qed.



Lemma bbsteps_bsteps: forall t r n,
 bbsteps t r n ->
 bsteps t r.
Proof.
  introv red.
  inductions red; eauto.
Qed.


Theorem completeness: forall e t t' A,
  Deterministic_blame_Calculus ->
  btyping nil t A e ->
  bsteps t (t_term t') ->
  valueb t' ->
  exists e', (steps e (e_exp e')) /\ btyping nil t' A e' /\ value e'.
Proof.
  introv dd typ red val.
  forwards* h1: bsteps_bbsteps red.
  inverts* h1.
  eapply completeness_gen_n;eauto.
Qed.



(*********************    trying   typing completeness  *************)



Lemma valueb_value_typ: forall e t A,
 typing nil e Inf3 A t -> valueb t ->
 value e.
Proof.
  introv typ H. gen A e.
  inductions H; intros;
  try solve[inverts typ as typ;inverts* typ].
  -
    forwards*: typing_regular_1 typ.
    inverts* typ.
    inverts* H1.
  -
    inverts typ as typ.
    inverts typ as typ.
    forwards* h1: principle_if typ.
  -
    inverts typ as typ.
    inverts typ as typ.
    forwards* h1: principle_if typ.
    forwards* h2: IHvalueb.
    rewrite <- h1 in *; eauto.
Qed.


Lemma value_valueb_typ: forall e t A,
 typing nil e Inf3 A t -> value e ->
 valueb t.
Proof.
  introv typ H. gen A t.
  inductions H; intros;
  try solve[inverts typ as typ;inverts* typ].
  -
    forwards*: typing_regular_3 typ.
    inverts typ as typ.
    eauto.
  -
    inverts typ as typ.
    inverts typ as typ.
    forwards* h1: principle_if typ.
    rewrite h1 in *. subst*.
  -
    inverts typ as typ.
    inverts typ as typ.
    forwards* h1: principle_if typ.
    rewrite h1 in *. subst*.
Qed.


Lemma typing_Cast_completeness: forall v t B A t' l b ,
  typing nil v Inf3 B t ->
  valueb t ->
  bstep (trm_cast t l b B A) (t_term t') ->
  (exists  n t2 v',  bbsteps t' (t_term t2) n /\ Cast v l b A (e_exp v') /\
  typing nil v' Inf3 A t2 /\ 0<=n <= 1) \/ (bstep t' (t_blame l b) /\ (Cast v l b A (e_blame l b))).
Proof.
  introv typ val red.
  forwards* h1: valueb_value_typ val.
  inductions red; try solve[inverts typ].
  -
    destruct E; unfold fillb; inverts x;
    try forwards*: bstep_not_value red.
  -
    inverts typ as typ; try solve[inverts typ]. 
    left. exists*. 
  -
    left.
    exists.
    splits*.
    forwards* h2: principle_if typ.
    inverts h1; inverts* h2.
  -
    forwards* hh1: UG_inf H0.
    inverts hh1 as hh1.
    +
    inverts hh1 as hh1 hh2.
    inverts hh1 as hh1.
    inverts hh1 as hh1. 
    forwards* h2: principle_if typ.
    left.
    exists. splits*.
    eapply Cast_anyd.
    rewrite h2.
    apply H0.
    eauto.
    eapply typ_anno; eauto.
    +
    inverts hh1 as hh1 hh2.
    inverts hh1 as hh1.
    inverts hh1 as hh1.
    inverts h1;inverts* typ. 
  -
    inverts h1 as h1 h2; try solve[inverts typ].
    inverts typ as typ.
    inverts typ as typ.
    forwards* h8: ug_ground_r H0.
    inverts val as val1 val2.
    forwards* h6:sim_decidable A0 B0.
    inverts h6 as h6.
    +
      forwards* h7: ground_eq h6.
      subst*.
      forwards* h9: UG_inf_arr_r2 typ.
      inverts h9 as h9.
      lets(t1&t2&h11):h9.
      subst.
      forwards* h13: principle_if typ.
      left.
      exists. splits.
      eapply sstar_one.
      rewrite fillb_cast.
      apply Step_evalb;eauto.
      eapply Cast_dyna; simpl;eauto.
      simpl.
      eapply typ_anno; eauto.
      lia. lia.
    +
      forwards* h9: not_sim_neq h6.
      (* inverts h1 as h1 h1'. *)
      (* forwards* h12:btyping_typing typ. *)
      forwards* h13: principle_if typ.
      right. rewrite fillb_cast.
      rewrite fillb_cast.
      splits.
      apply Step_blameb;eauto.
      simpl.
      eapply bStep_vanyp;eauto.
      eapply Cast_blame.
      rewrite h13.
      unfold not;intros nt.
      forwards*: UG_sim_l H0 nt.
  -
    inverts typ as typ.
    inverts typ as typ.
    forwards* h2: valueb_value_typ typ.
    forwards* h3: principle_if typ.
    rewrite <- h3.
    left.
    exists. splits*.
    rewrite h3; auto.
Qed.


Lemma value_cast_keep3: forall v A l b t,
 typing nil (e_anno v l b A) Inf3 A t ->
 value (e_anno v l b A) ->
 Cast v l b A (e_exp (e_anno v l b A)).
Proof.
 introv typ val.
 inverts* val; simpl in *; eauto.
 inverts typ as typ. inverts typ as typ.
 inverts H1; inverts* typ; inverts H4.
Qed.


Theorem typing_completeness_gen: forall e t t' A n,
 size_exp e + size_term t < n ->
  typing nil e Inf3 A t ->
  bstep t (t_term t') ->
  (exists e' t'' n, bbsteps t' (t_term t'') n /\ steps e (e_exp e') /\ typing nil e' Inf3 A t'' /\ 0<=n<=1) \/
  exists l b, (bstep t' (t_blame l b)) /\ steps e (e_blame l b).
Proof.
  introv sz Typ Red. gen e t t' A.
  induction n; intros; try lia.
  lets Red': Red.
  inductions Red; intros; try solve[inverts Typ].
  -
    clear IHRed.
    destruct E; simpl in * ;  try solve[inverts Typ].
    +
      inverts Typ as h1 h2; try solve[inverts h1].
      *
        forwards* lc1: typing_regular_3 h2.
        forwards* lc2: typing_regular_1 h2.
        forwards* h3: IHn Red h1. simpl in *; lia.
        inverts h3 as h3.
        --
          lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): h3.
          left.
          exists. splits.
          apply mmulti_red_app2.
          auto. apply rred2.
          apply multi_rred_app2.
          auto. apply rred1.
          eapply typ_app; eauto.
          lia. lia.
        --
          lets(ll&bb&rred1&rred2): h3.
          right. exists.
          splits.
          rewrite fillb_appl.
          apply Step_blameb; auto.
          apply rred1.
          apply multi_bblame_app2.
          auto. auto.
      *
        forwards* h3: IHn Red h1. simpl in *; lia.
        forwards* lc1:typing_regular_3 h2. 
        forwards* lc2:typing_regular_1 h2. 
        inverts h3 as h3.
        --
          lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): h3.
          left.
          exists. splits.
          apply mmulti_red_app2.
          auto. apply rred2.
          apply multi_rred_appv2.
          auto. apply rred1.
          eapply typ_appv; eauto.
          lia. lia.
        --
          lets(ll&bb&rred1&rred2): h3.
          right. exists.
          splits.
          rewrite fillb_appl.
          apply Step_blameb; auto.
          apply rred1.
          apply multi_bblame_appv2.
          auto. auto.
      *
        inverts H as lc1.
        forwards* lc2: typing_regular_1 h1.
        destruct(value_decidable e0) as [h3 | h4]; auto.
        --
          lets red: Red.
          forwards* h5: value_valueb_typ h1.
          inverts Red;
          try solve[
            destruct E; unfold fillb in *; inverts* H;
            forwards*: bstep_not_value H2
          ];
          try solve[forwards h0: UG_not_ground H5; exfalso; apply h0; auto].
          inverts h1 as h1. inverts h1 as h1.
          forwards* h6: typing_Cast_completeness red.
          forwards* lc3: typing_regular_1 h2.
          forwards* h8: valueb_value_typ h1.
          forwards* h7: principle_if h1.
          inverts h6 as h6.
          ++
            lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): h6.
            left.
            exists. splits.
            apply mmulti_red_app2.
            auto.
            apply rred2.
            eapply stars_trans.
            apply stars_one.
            apply Step_dyn; eauto.
            rewrite fill_app.
            apply stars_one.
            apply Step_eval; eauto.
            apply Step_annov; eauto.
            unfold not;intros nt;inverts nt as nt1 nt2. inverts nt2.
            unfold fill.
            eapply typ_app; eauto.
            lia. lia.
          ++
            lets(rred1&rred2): h6.
            right. exists.
            splits.
            rewrite fillb_appl.
            apply Step_blameb; auto.
            apply rred1.
            eapply stars_transb.
            apply stars_one.
            apply Step_dyn;eauto.
            apply step_b.
            rewrite fill_appl.
            eapply Step_blame;eauto.
            eapply Step_annov;eauto.
            unfold not;intros nt;inverts nt as nt1 nt2. inverts nt2.
        --
          assert(not (valueb t1)).
          unfold not;intros nt.
          forwards* h5: valueb_value_typ h1.
          forwards* lc3: typing_regular_1 h2.
          forwards* lc4: typing_regular_3 h2.
          inverts* Red;
          try solve[ destruct E; unfold fillb in *;
          inverts* H0].
          ++
            destruct E; unfold fillb in *;
            inverts* H0.
            forwards* h5: IHn H3. simpl in *;lia.
            inverts h5 as h5.
            ---
               lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): h5.
               left.
               exists. splits.
               apply mmulti_red_app2.
               auto.
               apply mmulti_red_cast.
               apply rred2.
               apply multi_rred_app2. auto.
               apply rred1.
               eapply typ_appd; eauto.
               lia. lia.
            ---
               lets(ll&bb&rred1&rred2): h5.
               right. exists.
               splits.
               rewrite fillb_appl.
               apply Step_blameb; auto.
               rewrite fillb_cast.
               apply Step_blameb; auto.
               apply rred1.
               apply multi_bblame_app2.
               auto. auto.
          ++
            exfalso; apply H; eauto.
    +
      inverts Typ as h1 h2; try solve[inverts h1]; simpl in *.
      *
        inverts h2 as h2; simpl in *.
        forwards* lc: typing_regular_1 h2.
        destruct(value_decidable e3); auto.
        --
          forwards* h3: value_valueb_typ h2.
          forwards* h4: typing_Cast_completeness h2 Red.
          inverts h4 as h4.
          ++
            lets(nn1&vv1&vv2&rred2&rred1&ttyp2&sz1): h4.
            inverts H as h5.
            forwards* h6: valueb_value_typ h1.
            forwards* h7: Cast_value rred1.
            forwards* h8: principle_if h1.
            left.
            exists. splits.
            apply mmulti_red_app. auto.
            apply rred2.
            apply stars_one.
            eapply Step_app; simpl;eauto.
            eapply typ_appv; eauto.
            lia. lia.
          ++
            lets(h5&h6):h4.
            inverts H.
            forwards* h7: valueb_value_typ h1.
            forwards* h8: principle_if h1.
            right. exists.
            splits.
            rewrite fillb_appr.
            apply Step_blameb; auto.
            apply h5.
            apply step_b.
            eapply Step_betap;eauto.
        --
          assert(not (valueb t0)).
          unfold not;intros nt.
          forwards* h3: valueb_value_typ h2.
          inverts* Red;
          try solve[ destruct E; unfold fillb in *;
          inverts* H2];
          try solve[exfalso; apply H1; eauto].
          destruct E; unfold fillb in H2; inverts H2.
          forwards* h4: IHn H5.
          simpl; lia.
          inverts h4 as h4.
          ++
            lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): h4.
            inverts H.
            forwards* h5: valueb_value_typ h1.
            forwards* h6: principle_if h1.
            left.
            exists. splits.
            apply mmulti_red_app.
            auto.
            apply mmulti_red_cast.
            apply rred2.
            eapply multi_rred_app.
            apply h6.
            auto. 
            apply rred1.
            eapply typ_app; eauto.
            lia. lia.
          ++
            lets(ll&bb&rred1&rred2): h4.
            inverts H.
            forwards* h5: valueb_value_typ h1.
            forwards* h6: principle_if h1.
            right. exists.
            splits.
            rewrite fillb_appr.
            apply Step_blameb; auto.
            apply Step_blameb; auto.
            apply rred1.
            eapply multi_bblame_app; simpl.
            apply h6.
            auto. auto.
      *
        inverts H as h3.
        forwards* h4: valueb_value_typ h1.
        forwards* h5: IHn Red. simpl in *; lia. 
        inverts h5 as h5.
        --
           lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): h5.
           forwards* h6: typing_typing h2.
           simpl in *.
           forwards* h7: preservation_multi_step rred1.
           forwards* h8:typing_typing1 h6.
           subst.
           left.
           exists. splits.
           apply mmulti_red_app.
           auto.
           apply rred2.
           eapply multi_rred_appv.
           auto.
           apply rred1.
           eapply typ_appv; eauto.
           lia. lia.
        --
          lets(ll&bb&rred1&rred2): h5.
          right. exists.
          splits.
          rewrite fillb_appr.
          apply Step_blameb; auto.
          apply rred1.
          apply multi_bblame_appv.
          auto.
          auto. 
      *
        inverts H as h3.
        inverts* h3.
    +
      inverts Typ as h1; try solve[inverts h1].
      inverts h1 as h1.
      forwards* h2: IHn h1.
      simpl in *; lia.
      inverts h2 as h2.
      *
        lets(vv1&vv2&nn1&rred2&rred1&ttyp2&sz1): h2.
        left.
        exists. splits.
        apply mmulti_red_cast.
        apply rred2.
        apply multi_rred_anno.
        apply rred1.
        eapply typ_anno; eauto.
        lia. lia.
      *
        lets(ll&bb&rred1&rred2): h2.
        right. exists.
        splits.
        rewrite fillb_cast.
        apply Step_blameb; auto.
        apply rred1.
        apply multi_bblame_anno.
        auto. 
  -
    inverts Typ as h1 h2; try solve[inverts h1].
    +
      forwards* lc: typing_regular_1 h1.
      inverts h1 as h1; try solve[inverts h1].
      inverts h2 as h2.
      assert(valueb t0) as h3.
      inverts* H0.
      assert(typing [] (e_anno e2 l0 b A) Inf3 A (trm_cast t0 l0 b A1 A)) as h5.
      auto.
      forwards* h4: valueb_value_typ h5.
      forwards* h6: value_cast_keep3 h4.
      assert(value e2) as h7.
      inverts* h4.
      left.
      exists. splits.
      apply bbstep_refl.
      eapply stars_trans.
      apply stars_one.
      eapply Step_app; simpl;eauto.
      apply stars_one.
      eapply Step_beta; simpl;eauto.
      unfold open_term_wrt_term; simpl.
      assert((open_term_wrt_term_rec 0 (trm_cast t0 l0 b A1 A) t) = (open_term_wrt_term t (trm_cast t0 l0 b A1 A))) as h8; eauto.
      rewrite h8.
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      rewrite (subst_term_intro y); eauto.
      forwards* h9: h1 y.
      eapply typ_anno; eauto.
      eapply typing_c_subst_simpl; eauto.
      lia. lia.
    +
      forwards* lc: typing_regular_1 h1.
      inverts h1 as h1; try solve[inverts h1].
      forwards* h3: valueb_value_typ h2.
      left.
      exists. splits.
      apply bbstep_refl.
      apply stars_one.
      apply Step_beta; eauto.
      unfold open_term_wrt_term; simpl.
      assert((open_term_wrt_term_rec 0 v t) = (open_term_wrt_term t v)) as h4; eauto.
      rewrite h4.
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      rewrite (subst_term_intro y); eauto.
      forwards*: h1 y.
      inverts H1.
      eapply typ_anno; eauto.
      eapply typing_c_subst_simpl; eauto.
      lia. lia.
  -
    forwards lc: typing_regular_1 Typ.
    inverts Typ as typ. 
    inverts typ as typ.
    inverts typ as typ; try solve[inverts* typ].
    left.
    exists.
    splits.
    apply bbstep_refl.
    apply stars_one.
    apply Step_annov; eauto.
    unfold not;intros nt. inverts nt.
    auto.
    lia. lia.
  -
    forwards lc: typing_regular_1 Typ.
    inverts Typ as typ; try solve[inverts* typ]. 
    +
      inverts typ as typ. 
      inverts H7 as h1.
      forwards* h2: valueb_value_typ h1.
      inverts* H0.
      assert(typing [] (e_anno e2 l0 b0 A1) Inf3 A1 (trm_cast t l0 b0 A2 A1)) as h3; auto. 
      forwards* h4: valueb_value_typ h3.
      forwards* h5: value_cast_keep3 h4.
      inverts typ as typ.
      inverts H.
      forwards* h7: valueb_value_typ typ.
      forwards* h6: principle_if typ. 
      inverts H14.
      left.
      exists. splits.
      apply bbstep_refl.
      eapply stars_trans.
      apply stars_one.
      eapply Step_app; simpl;eauto.
      apply stars_one.
      eapply Step_abeta; eauto.
      eapply typ_anno; eauto.
      lia. lia.
    +
      forwards* h1: valueb_value_typ typ.
      forwards* h2: valueb_value_typ H7.
      inverts typ as typ.
      inverts typ as typ.
      inverts H.
      inverts h1. 
      inverts lc as lc1 lc2.  
      forwards* h3: principle_if typ.
      rewrite h3 in *. 
      inverts H8.
      inverts H14.
      left.
      exists. splits.
      apply bbstep_refl.
      apply stars_one.
      eapply Step_abeta; eauto.
      eapply typ_anno; eauto.
      lia. lia.
  -
    inverts Typ as typ.
    inverts typ as typ.
    forwards* h1: typing_Cast_completeness typ Red'.
    inverts h1 as h1.
    +
      lets(nn1&tt1&vv1&rred1&rred2&ttyp1&eq1): h1.
      forwards* h2: typing_regular_1 typ.
      forwards* h3: valueb_value_typ typ.
      inverts h3; inverts* typ.
      left.
      exists. splits.
      apply rred1.
      apply stars_one.
      apply Step_annov; eauto.
      unfold not;intros nt;inverts* nt.
      inverts H4.
      auto.
      lia. lia.
    +
      lets(rred1&rred2):h1.
      forwards*: valueb_value_typ typ.
      forwards* h2: cast_dyn_not_fail rred2.
      inverts h2 as h2. 
      inverts h2.
  -
    inverts Typ as h1.
    inverts h1 as h1.
    forwards* h2: valueb_value_typ H.
    forwards* h3: typing_Cast_completeness h1 Red'.
    inverts h3 as h3; eauto.
    +
      lets(nn1&tt1&vv1&h4&h5&h6&h7):h3.
      forwards* h8: typing_regular_1 h1.
      forwards* h9: valueb_value_typ h1.
      forwards* h10: value_decidable (e_anno e0 p b t_dyn).
      inverts h10 as h10.
      *
        forwards* h11: value_cast_keep2 h5. inverts h11.
        inverts h6 as h6.
        inverts h6 as h6.
        left.
        exists. splits.
        apply h4.
        apply step_refl.
        apply typ_anno;auto.
        lia.
        lia.
      *
        left.
        exists. splits.
        apply h4.
        apply stars_one.
        apply Step_annov; eauto.
        auto.
        lia. lia.
    +
      lets(h4&h5):h3.
      forwards* h6: cast_dyn_not_fail h5.
      inverts h6 as h6; inverts h6.
  -
    inverts Typ as typ.
    inverts typ as typ.
    forwards* h1: typing_Cast_completeness Red'.
    inverts h1 as h1.
    +
      lets(nn1&tt1&vv1&rred1&rred2&ttyp1&eq1): h1.
      forwards* h2: typing_regular_1 typ.
      forwards* h3: valueb_value_typ typ.
      forwards* h4: value_decidable (e_anno e0 p b A).
      inverts h4 as h4.
      *
        forwards* h5: value_cast_keep2 rred2. inverts h5.
        inverts ttyp1 as ttyp1.
        left.
        exists. splits.
        apply rred1.
        apply step_refl.
        apply typ_anno;auto.
        lia. lia.
      *
        left.
        exists. splits.
        apply rred1.
        apply stars_one.
        apply Step_annov; eauto.
        auto.
        lia. lia.
    +
      forwards* h2: valueb_value_typ typ.
      lets(rred1&rred2):h1.
      lets rred1': rred1.
      right. 
      exists.
      splits.
      apply rred1'.
      apply step_b.
      apply Step_annov; eauto.
      unfold not;intros nt.
      forwards* h5: value_cast_keep2 rred2. 
      inverts h5.
  -
    inverts Typ as typ.
    inverts typ as typ.
    inverts typ as typ.
    forwards* h2: typing_Cast_completeness Red'.
    inverts h2 as h2.
    *
      lets(nn1&tt1&vv1&rred1&rred2&ttyp1&eq1): h2.
      forwards* h3: typing_regular_1 typ.
      inverts typ as typ.
      forwards* h1: valueb_value_typ typ.
      forwards* h4: principle_if typ.
      rewrite <- h4 in *.
      left.
      exists. splits.
      apply rred1.
      apply stars_one.
      apply Step_annov; eauto.
      unfold not;intros nt; inverts* nt.
      inverts H6. inverts H3.
      auto.
      lia. lia.
    *
      inverts typ as typ.
      forwards* h3: valueb_value_typ typ.
      lets(rred1&rred2):h2.
      forwards* h4: principle_if typ.
      rewrite <- h4 in *.
      right. 
      exists.
      splits.
      apply rred1.
      apply step_b.
      apply Step_annov; eauto.
      unfold not;intros nt; inverts* nt.
      inverts H6. inverts H3.
  -
    inverts Typ as typ; try solve[inverts typ]. 
    +
      inverts typ as typ; try solve[inverts typ]. 
      inverts typ as typ; try solve[inverts typ]. 
      inverts H5.
    +
      inverts typ as typ; try solve[inverts typ]. 
      inverts* H5; try solve[inverts* H].
      left. exists.
      splits.
      apply bbstep_refl.
      apply stars_one; eauto.
      apply typ_addl; eauto.
      lia. lia.
  -
    inverts Typ as typ; try solve[inverts typ]. 
    +
      inverts typ as typ; try solve[inverts typ]. 
      inverts typ as typ; try solve[inverts typ]. 
      inverts H5.
    +
      inverts typ as typ; try solve[inverts typ]. 
      inverts* H5; try solve[inverts* H].
      left. exists.
      splits.
      apply bbstep_refl.
      apply stars_one; eauto.
      apply typ_lit; eauto.
      lia. lia.
Qed.




Theorem typing_completeness_gens: forall e t t' A n n1,
  Deterministic_blame_Calculus ->
  n < n1 ->
  typing nil e Inf3 A t ->
  bbsteps t (t_term t') n ->
  valueb t' ->
  exists e', (steps e (e_exp e')) /\ typing nil e' Inf3 A t' /\ value e'.
Proof.
  introv dd sz typ red val. gen t t' A e n.
  inductions n1; intros; try solve[lia].
  inverts* red.
  -
    forwards*: valueb_value_typ typ.
  -
    forwards* h1: typing_completeness_gen H0.
    inverts h1 as h1.
    +
      lets(ee1 &ee2&nn2& rred1&rred2&typ1&ssz): h1.
      inverts H2.
      *
        inverts* rred1.
        forwards*: valueb_value_typ typ1.
        forwards*: bstep_not_value H1.
      *
        destruct nn2.
        --
          inverts* rred1.
          assert(bbsteps ee2 (t_term t') (1+n)).
          eapply bbstep_n;eauto.
          forwards*: IHn1 H.
          lia.
          inverts* H2. 
        --
          assert(nn2 = 0).
          lia.
          rewrite H in *.
          inverts* rred1.
          inverts* H7.
          forwards* h2: dd H1 H6.
          inverts* h2.
          forwards*: IHn1 H4.
          lia.
          inverts* H2. 
    +
      lets(ll1&bb1&h2&h3): h1.
      inverts* H2.
      *
      forwards*: bstep_not_value h2.
      *
      forwards* h4: dd h2 H1.
      inverts* h4.
Qed.



Theorem typing_completeness: forall e t t' A,
  Deterministic_blame_Calculus ->
  typing nil e Inf3 A t ->
  bsteps t (t_term t') ->
  valueb t' ->
  exists e', (steps e (e_exp e')) /\ typing nil e' Inf3 A t' /\ value e'.
Proof.
  introv dd typ red val.
  forwards* h1: bsteps_bbsteps red.
  inverts* h1.
  eapply typing_completeness_gens;eauto.
Qed.




(************************  typing trying soundness     *)


Lemma typing_Casting_soundness: forall v t v' p b A,
  btyping nil t A (e_anno v p b A)->
  value v ->
  Cast v p b A (e_exp v') ->
  exists t', t ->* (t_term t') /\ btyping nil t' A v'.
Proof.
  introv  Typ val Red. gen t.
  inductions Red; intros.
  - 
    inverts Typ as h1 h2.
    inverts* h2.
  - inverts Typ as h1 h2.
    forwards*: value_lc val.
  - inverts Typ as h1 h2.
    inverts h1.
    exists. split.
    apply star_one; eauto.
    apply btyp_lit; eauto.
  - inverts Typ as typ1 h1.
    inverts typ1 as typ1 h2.  
    forwards* h3: value_valueb2 val.
    exists.
    splits.
    apply star_one;eauto.
    eapply btyp_cast; eauto.
  - 
    inverts Typ as typ h0. 
    forwards* h00: btyping_typing typ. 
    forwards* h1: principle_inf h00.
    rewrite h1 in *.
    forwards* h6: value_valueb2 typ.
    forwards* h7: IHRed (trm_cast t0 p b A B).
    forwards* h8: UG_to_sim H.
    lets(t'&h9&h10):h7.
    exists. split.
    eapply star_trans.
    apply star_one.
    eauto.
    apply multi_red_cast.
    apply h9.
    eapply btyp_cast; eauto.
  - 
    inverts Typ as typ h0. 
    inverts val as val1 val2.
    inverts typ as typ.
    forwards* h5: value_valueb2 typ.
    forwards* h6: btyping_typing typ.
    forwards* h7: principle_inf h6.
    forwards* h8: Cast_sim_aux Red.
    rewrite h7 in *.
    forwards* h9: UG_sim_l H h8.
    forwards* h10: ug_ground_r H.
    forwards* hh: ground_eq h9.
    rewrite hh in *.
    forwards* h11: IHRed.
    lets(t'&h12&h13): h11.
    exists. split.
    eapply star_trans.
    apply star_one.
    apply bStep_dyna; auto.
    apply H.
    eapply star_trans.
    rewrite fillb_cast.
    apply star_one.
    apply Step_evalb; simpl in *;auto.
    simpl.
    apply h12.
    auto.
  -
    inverts val.
    inverts Typ as typ.
    inverts typ as typ.
    forwards* h1: value_valueb2 typ.
    forwards* h4: btyping_typing typ.
    forwards* h2: principle_inf h4.
    rewrite h2 in *; eauto.
  - inverts Typ as typ.
  inverts typ as typ.
Qed.


Lemma typing_soundness_gen: forall e t e' A ,
  btyping nil t A e->
  step e (e_exp e') ->
  exists t', t ->* (t_term t') /\ btyping nil t' A e' .
Proof.
  introv Typ Red. gen A t.
  inductions Red; intros; try solve[inverts* Typ].
  -
    destruct E; unfold fill in *; inverts Typ as typ1 typ2.
    +
      forwards* h1: IHRed typ1.
      lets(ee1&h2&h3): h1.
      exists. splits.
      apply multi_red_cast.
      apply h2.
      eapply btyp_cast; eauto.
    +
      forwards* h1: IHRed typ1.
      lets(ee1&h2&h3): h1.
      forwards* lc: btyping_regular_1 typ2.
      exists. splits.
      apply multi_red_app2.
      auto.
      apply h2.
      eapply btyp_app; eauto.
    +
      inverts H.
      forwards* val2: value_valueb2 typ1.
      forwards* h1: IHRed typ2.
      lets(tt1& h2& h3): h1.
      exists. splits.
      apply multi_red_app.
      auto.
      apply h2.
      eapply btyp_app; eauto.
  -
    inverts Typ as typ typ2.
    forwards* lc1: btyping_regular_1 typ. 
    inverts typ as typ.
    forwards* h1: value_valueb2 typ2.
    exists. splits.
    apply star_one.
    apply bStep_beta; eauto.
    pick fresh y.
    rewrite (subst_exp_intro y); eauto.
    rewrite (subst_term_intro y); eauto.
    forwards* h2: typ y.
    forwards* h3: btyping_c_subst_simpl h2 typ2.
  -
    lets typ: Typ.
    inverts Typ.
    forwards* h1: typing_Casting_soundness H0. 
  -
    inverts Typ as typ1 typ2.
    inverts typ1 as typ1.
    forwards* h1: value_valueb2 typ1.
    forwards* h2: value_valueb2 typ2.
    forwards* h3: btyping_typing typ1.
    forwards* h4: principle_inf h3.
    rewrite h4 in *. subst*.
    inverts H12.
    exists. splits.
    apply star_one.
    apply bStep_abeta; eauto.
    apply btyp_cast; eauto.
  -
    inverts Typ as typ1 typ2.
    inverts typ1 as typ1.
    inverts typ2 as typ2.
    exists. splits.
    apply star_one;eauto.
    apply btyp_addl; eauto.
  -
    inverts Typ as typ1 typ2.
    inverts typ1 as typ1.
    inverts typ2 as typ2.
    exists. splits.
    apply star_one;eauto.
    apply btyp_lit; eauto.
Qed.



Theorem typing_soundness: forall e t v1 A,
  btyping nil t A e->
  e ->** (e_exp v1) ->
  value v1 ->
  exists t', t ->* (t_term t') /\ valueb t' /\ btyping nil t' A v1 .
Proof.
  introv typ red val. gen A t.
  inductions red;intros.
  -
  forwards*: value_valueb2 val.
  -
  forwards*: typing_soundness_gen H.
  inverts H0. inverts H1.
  forwards*: IHred H2.
  inverts* H1. 
Qed.


























