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
        ttyping
        soundness_completeness.

Require Import List. Import ListNotations.
(* Require Import Arith lia. *)
Require Import Strings.String.

Require Import Lia.

Ltac size_ind_auto :=
  ( eapply_first_lt_hyp ;
    try reflexivity;
    try lia ;
    try eauto ).



Lemma eq_type: forall A,
 (A = t_dyn) \/ ~(A = t_dyn).
Proof.
  introv.
  inductions A;
  try solve[left;
  reflexivity];
  try solve[right;
  unfold not; intros H; 
  inverts* H].
Qed.

Lemma BA_AB: forall B A,
  sim A B -> sim B A.
Proof.
  introv H.
  induction* H.
Qed.


Lemma principle_if: forall v A t,
 value v -> typing nil v Inf3 A t -> dynamic_type v = A.
Proof.
  introv H typ.
  inductions H; inverts* typ; eauto.
Qed.



Lemma fillb_cast: forall v p b A B,
  (trm_cast v p b A B) = (fillb (castCtxb p b A B)  v).
Proof.
  introv.
  eauto.
Qed.



Lemma sim_refl: forall A,
 sim A A.
Proof.
  intros.
  inductions A; eauto.
Qed.


Lemma Cast_soundness_blame: forall v t p b A,
  typing nil (e_anno v p b A) Inf3 A t->
  value v ->
  Cast v p b A (e_blame p b) ->
  t ->* (t_blame p b) .
Proof.
  introv Typ val Red. gen t.
  inductions Red; intros.
  -
    inverts Typ as typ. inverts typ as typ.
    inverts typ as typ.
    inverts typ as typ.
    inverts val as val1 val2.
    forwards* h1: principle_if typ.
    forwards* h2: Cast_sim_aux Red.
    rewrite h1 in *.
    forwards* h3: IHRed.
    forwards* h4: value_valueb_typ typ.
    forwards* h5: UG_sim_l H h2.
    forwards* h7: ug_ground_r H.
    forwards* h6: ground_eq h5.
    rewrite h6 in *.
    eapply bstep_nb.
    eapply bStep_dyna; eauto.
    eapply bstep_nb.
    rewrite fillb_cast.
    apply Step_evalb.
    auto.
    apply bStep_vany; eauto.
    simpl.
    auto.
  -
    inverts Typ as typ.
    inverts typ as typ.
    inverts typ as typ.
    inverts typ as typ.
    inverts val as val1 val2.
    forwards* h1: principle_if typ.
    rewrite h1 in *.
    forwards* h2: UG_decidable A.
    inverts h2 as h2.
    +
      inverts h2 as h2.
      forwards* h3: ug_ground_r h2.
      forwards* h4: UG_to_sim h2.
      assert(not(A0 = x)) as h5.
      unfold not;intros nt.
      rewrite nt  in *.
      apply H; eauto.
      forwards* h0: value_valueb_typ typ.
      eapply bstep_nb.
      apply bStep_dyna; eauto.
      apply bstep_b.
      rewrite fillb_cast.
      apply Step_blameb; auto.
    +
      forwards* h0: value_valueb_typ typ.
      apply bstep_b.
      apply bStep_vanyp; auto.
      *
      forwards* h3: Ground_decidable A.
      inverts h3 as h3;auto.
      exfalso.
      destruct A; try solve[exfalso; apply h3; auto].
      --
      forwards* h4: h2 (t_arrow t_dyn t_dyn).
      apply h4.
      unfold UG; splits*;
      try solve[unfold not;intros nt;inverts nt];
      try solve[unfold not;intros nt;inverts nt as nt;inverts nt].
      unfold not;intros nt;inverts nt as nt.
      apply h3; auto.
      --
      exfalso; apply H; auto.
      --
      forwards* h4: h2 (t_pro t_dyn t_dyn).
      apply h4.
      unfold UG; splits*;
      try solve[unfold not;intros nt;inverts nt];
      try solve[unfold not;intros nt;inverts nt as nt;inverts nt].
      unfold not;intros nt;inverts nt as nt.
      apply h3; auto.
      *
      unfold not;intros nt.
      substs*.
  -
    inverts Typ as typ.
    inverts typ as typ.
    inverts typ as typ.
  -
    inverts Typ as typ.
    inverts typ as typ.
    inverts typ as typ.
Qed.



Lemma Soundness_blame_one: forall e t dir p b A,
  typing nil e dir A t->
  step e (e_blame p b) ->
  t ->* (t_blame p b).
Proof.
  introv Typ J. gen A dir t.
  inductions J; intros.
  - destruct E; unfold fill in *;
    try solve[inverts Typ as typ; 
    inverts typ as typ].
    + inverts Typ.
      * forwards*: IHJ H8. 
      apply multi_blame_app2; eauto.
      forwards*: typing_regular_3 H9.
      * 
      inverts H0.
      ++
      forwards*: IHJ H9.
      apply multi_blame_cast; eauto.     
      apply multi_blame_app2; eauto.
      forwards*: typing_regular_3 H10.
      ++
      forwards*: typing_regular_3 H10.
      forwards*: IHJ H9.
      apply multi_blame_cast; eauto.     
      apply multi_blame_app2; eauto. 
      *
      forwards*: typing_regular_3 H9.
      forwards*: IHJ H8.
      apply multi_blame_app2; eauto.
    + 
      inverts Typ.
      *
      forwards*: typing_regular_1 H9. 
      forwards*: IHJ H9. 
      apply multi_blame_app; eauto.
      inverts H.
      forwards*: value_valueb1 H8.
      *
      inverts H0.
      -- 
      forwards*: typing_regular_1 H10.
      forwards*: IHJ H10. 
      inverts H.
      forwards*: value_valueb1 H9.
      apply multi_blame_cast; eauto.      
      apply multi_blame_app; eauto.
      --
      inverts H.
      forwards*: principle_if H9.
      rewrite H in *. inverts H3.
      *
      inverts H.
      forwards*: principle_if H8.
      rewrite H in *. inverts H2. 
    + 
      forwards*: typing_regular_1 Typ. inverts H0.
      inverts Typ; try solve[forwards*: step_not_value J].
      forwards*: IHJ H9.
      inverts H0; try solve[forwards*: step_not_value J].
      forwards*: IHJ H10.
      apply multi_blame_cast; eauto.
    +
      inverts Typ.
      *
      inverts H0.
      forwards*: IHJ H5.
      apply multi_blame_cast; eauto.     
      apply multi_blame_app2; eauto.
      forwards*: typing_regular_3 H6.
      *
      forwards* h1: typing_regular_3 H7.
      forwards* h2: IHJ H3.
      apply multi_blame_app2; eauto.
    +
      inverts Typ.
      *
      inverts H0.
      forwards*: IHJ H6.
      apply multi_blame_cast; eauto.     
      apply multi_blame_app; eauto.
      inverts H.
      forwards*: value_valueb1 H5.
      *
      forwards*: IHJ H7.    
      apply multi_blame_app; eauto.
      inverts H.
      forwards*: value_valueb1 H3.  
  - 
    inverts Typ.
    + 
      forwards* h1: principle_if H11.
      rewrite h1 in *. inverts H1.
      forwards*: Cast_soundness_blame H2.
      apply multi_blame_app; eauto.
      forwards*: value_valueb1 H11.
    + inverts H3.
      *
      forwards* h1: principle_if H12.
      rewrite h1 in *. inverts H1.
      forwards*: Cast_soundness_blame H2.
      apply multi_blame_cast; eauto.      
      apply multi_blame_app; eauto.
      forwards*: value_valueb1 H.
      *
      forwards* h1: principle_if H12.
      rewrite h1 in *. inverts H1.    
    +
      forwards* h1: principle_if H11.
      rewrite h1 in *. inverts H1.
  - 
    inverts Typ as typ. 
    *
    forwards* h1: cast_label H0.
    inverts h1 as h1.
    forwards*: Cast_soundness_blame H0.
    *
    inverts typ as typ.
    --
    lets H0':H0.
    forwards* h1: cast_label H0.
    inverts h1 as h1.
    forwards*: Cast_soundness_blame H0'.
    apply multi_blame_cast; eauto.          
Qed.




Theorem soundness_blame: forall e t A dir l b ,
  typing nil e dir A t->
  e ->** e_blame l b ->
  t ->* t_blame l b .
Proof.
  introv typ red. gen dir A t.
  inductions red;intros.
  -
  forwards*: soundness_mul_one H.
  inverts H0. inverts H1. 
  forwards*: IHred H2.
  -
  forwards*: Soundness_blame_one typ H.
Qed.




Lemma Cast_completeness_blame: forall v t B A l b ,
  btyping nil t B v ->
  valueb t ->
  bstep (trm_cast t l b B A) (t_blame l b) ->
  Cast v l b A  (e_blame l b).
Proof.
  introv typ val red.
  forwards* h1: valueb_value2 val.
  inductions red; try solve[inverts* typ].
  -
    destruct E; unfold fillb; inverts x;
    try forwards*: bstep_not_value red.
  -
    inverts typ as typ; inverts h1 as hh1 hh2.
    forwards* h2: btyping_typing typ.
    forwards* h3: principle_inf h2.
    rewrite <- h3 in *. 
    eapply Cast_blame;eauto.
    unfold not;intros nt.
    forwards* h4: ground_eq nt.
Qed.



Theorem completeness_blame_gen: forall e t A n l b,
  size_exp e + size_term t < n ->
  btyping nil t A e ->
  bstep t (t_blame l b) ->
  steps e (e_blame l b).
Proof.
  introv sz Typ Red. gen e t A.
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
    inverts lc.
    apply multi_bblame_appv2.
    auto. apply h2.
    +
    inverts Typ. inverts H.
    forwards* h1: valueb_value2 H3.
    forwards* h2: IHn Red H6. simpl in *; lia.
    apply multi_bblame_appv.
    auto. apply h2.
    +
     forwards* lc: btyping_regular_3 Typ.
     inverts Typ; simpl in *.
     inverts lc.
     forwards* h1: IHn Red H8. simpl in *; lia.
     apply multi_bblame_anno.
     apply h1.
  -
    inverts Typ.
    forwards* h1: valueb_value2 H11.
    forwards* h2: Cast_completeness_blame H11 Red'.
    forwards* h3: value_decidable (e_anno e0 l b A0).
    inverts h3.
    +
    forwards* h4: value_cast_keep2 h2. inverts h4.
    +
    apply step_b.
    apply Step_annov; eauto.
Qed.


Theorem completeness_blame_gens: forall e t A n n1 l b,
  Deterministic_blame_Calculus ->
  n < n1 ->
  btyping nil t A e ->
  bbsteps t (t_blame l b) n ->
  steps e (e_blame l b).
Proof.
  introv dd sz typ red. gen t l b A e n.
  inductions n1; intros; try solve[lia].
  inverts* red.
  -
  forwards*: completeness_gen_ns H2.
  inverts* H.
  +
  lets(ee1 &ee2&nn2& rred1&rred2&ttyp1&ssz): H0.
  destruct(nn2).
  inverts* rred1.
  *
  forwards* h1: IHn1 H4.
  lia.
  *
  assert(n =0).
  lia.
  rewrite H in *.
  inverts* rred1.
  inverts* H7.
  assert(bbsteps ee2 (t_blame l b) (n0-1)).
  inverts H4.
  forwards* h1: dd H6 H7. inverts h1.
  simpl;eauto.
  assert(n2-0 = n2). lia.
  rewrite H1;eauto.
  forwards* h2: dd H6 H8.
  inverts* h2.
  forwards*: IHn1 H1.
  lia.
  +
  inverts* H0. inverts* H. inverts* H0.
  inverts* H4.
  forwards* h2: dd H H6.
  inverts* h2.
  forwards* h2: dd H H7.
  inverts* h2.
  -
  forwards*:  completeness_blame_gen H3.
Qed.


Theorem completeness_blame: forall e t A l b,
  Deterministic_blame_Calculus ->
  btyping nil t A e ->
  bsteps t (t_blame l b) ->
  steps e (e_blame l b).
Proof.
  introv dd typ red.
  forwards*: bsteps_bbsteps red.
  inverts* H.
  eapply completeness_blame_gens; eauto.
Qed.


Theorem multi_progress : forall e dir T,
    Typing nil e dir T ->
    exists r, steps e r.
Proof.
  introv typ.
  forwards*: Progress typ.
Qed.


(****** typing complete blame *******************************************************)



Lemma typing_Cast_completeb: forall v t B A l b ,
  typing nil v Inf3 B t ->
  valueb t ->
  bstep (trm_cast t l b B A) (t_blame l b) ->
  Cast v l b A  (e_blame l b).
Proof.
  introv typ val red.
  forwards* h1: valueb_value_typ val.
  inductions red; try solve[inverts* typ].
  -
    destruct E; unfold fillb; inverts x;
    try forwards*: bstep_not_value red.
  -
    inverts typ as typ; inverts h1 as h1 h2.
    inverts typ as typ.
    forwards* h3: principle_if typ.
    rewrite <- h3 in *. 
    eapply Cast_blame;eauto.
    unfold not;intros nt.
    forwards*: ground_eq nt.
Qed.


Theorem typing_completeb_gen: forall e t A n l b,
  size_exp e + size_term t < n ->
  typing nil e Inf3 A t ->
  bstep t (t_blame l b) ->
  steps e (e_blame l b).
Proof.
  introv sz Typ Red. gen e t A.
  induction n; intros; try lia.
  lets Red': Red.
  inductions Red; intros.
  - clear IHRed.
    destruct E; unfold fillb in *; simpl in *.
    +
      forwards h1: typing_regular_1 Typ.
      inverts Typ as typ; simpl in *; try solve[inverts typ].
      *
        inverts h1 as lc1 lc2.
        forwards* h2: IHn Red.
        simpl in *; lia.
        apply multi_bblame_app2.
        auto. apply h2.
      *
        inverts h1 as lc1 lc2.
        forwards* h2: IHn Red.
        simpl in *; lia.
        apply multi_bblame_appv2.
        auto. apply h2.
      *
        forwards* lc: typing_regular_1 typ.
        destruct(value_decidable e0); auto.
        --
          assert(l1 = l /\ b0 = b) as h3.
          inverts* Red; try solve[
            destruct E; unfold fillb in *; inverts* H1;
            forwards*: value_valueb_typ typ;forwards*: bstep_not_value H5
          ].
          lets(h4&h5): h3.
          subst.
          forwards*: value_valueb_typ typ.
          forwards* h5: typing_Cast_completeb Red.
          inverts H0; try solve[inverts typ].
          inverts h1 as h6 h7.
          eapply stars_transb.
          apply stars_one.
          apply Step_dyn; eauto.
          apply step_b.
          rewrite fill_appl.
          apply Step_blame; auto.
          eapply Step_annov; eauto.
          unfold not;intros nt;inverts* nt.
          inverts* H10.
        --
          assert(not(valueb t1)) as h3.
          unfold not;intros nt.
          forwards*: valueb_value_typ typ.
          inverts* Red.
          ++
            inverts h1 as lc1 lc2.
            destruct E; unfold fillb in *; inverts* H1.
            forwards* h5: IHn H5. simpl in *; lia.
            eapply multi_bblame_app2.
            auto.
            auto. 
          ++
            exfalso; apply h3; eauto.   
    +
      inverts Typ as typ1 typ2; try solve[inverts typ1]. 
      *
        inverts H as h0.
        forwards* h1: valueb_value_typ typ1.
        inverts typ2 as typ2.
        forwards* lc1: typing_regular_1 typ2.
        destruct(value_decidable e2); auto.
        --
          assert(l1 = l /\ b0 = b) as h3.
          inverts* Red; try solve[
            destruct E; unfold fillb in *; inverts* H0;
            forwards*: value_valueb_typ typ2;forwards*: bstep_not_value H4
          ].
          forwards*: value_valueb_typ typ2.
          lets(h7&h8): h3.
          inverts h7. inverts h8.
          forwards* h5: typing_Cast_completeb Red.
          forwards* h6: principle_if typ1.
        --
          assert(not(valueb t0)) as h3.
          unfold not;intros nt.
          forwards*: valueb_value_typ typ2.
          inverts* Red.
          ++
            destruct E; unfold fillb in *; inverts* H0.
            forwards* h4: principle_if typ1.
            forwards* h5: IHn H4. simpl in *; lia.
            eapply multi_bblame_app.
            apply h4.
            auto. apply h5.
          ++
            exfalso; apply h3; eauto.          
      *
        inverts H.
        forwards* h1: valueb_value_typ typ1.
        forwards* h2: IHn Red. simpl in *; lia.
        apply multi_bblame_appv.
        auto. apply h2.
      *
        inverts H as h1.
        inverts* h1.
    +
      forwards* lc: typing_regular_1 Typ.
      inverts Typ as typ; simpl in *; try solve[inverts typ].
      inverts lc.
      inverts typ as typ.
      forwards* h1: IHn Red typ. simpl in *; lia.
      apply multi_bblame_anno.
      apply h1.
  -
    inverts Typ as typ.
    inverts typ as typ.
    forwards* h1: valueb_value_typ typ.
    forwards* h2: typing_Cast_completeb typ Red'.
    forwards* h3: value_decidable (e_anno e0 l b B).
    inverts h3.
    +
      forwards* h4: value_cast_keep2 h2. inverts h4.
    +
      apply step_b.
      apply Step_annov; eauto.
Qed.


Theorem typing_completeb_gens: forall e t A n n1 l b,
  Deterministic_blame_Calculus ->
  n < n1 ->
  typing nil e Inf3 A t ->
  bbsteps t (t_blame l b) n ->
  steps e (e_blame l b).
Proof.
  introv dd sz typ red. gen t l b A e n.
  inductions n1; intros; try solve[lia].
  inverts* red.
  -
    forwards* h1: typing_completeness_gen H2.
    inverts h1 as h1.
    +
      lets(ee1 &ee2&nn2& rred1&rred2&ttyp1&ssz): h1.
      destruct(nn2).
      inverts rred1 as h2.
      *
        forwards* h3: IHn1 H4.
        lia.
      *
        assert(n =0).
        lia.
        rewrite H in *.
        inverts* rred1.
        inverts* H6.
        assert(bbsteps ee2 (t_blame l b) (n0-1)).
        inverts H4.
        forwards* h3: dd H5 H6. inverts h3.
        simpl;eauto.
        assert(n2-0 = n2). lia.
        rewrite H0;eauto.
        forwards* h2: dd H5 H7.
        inverts* h2.
        forwards*: IHn1 H0.
        lia.
    +
      lets(ll1&bb1&h2&h3): h1.
      inverts H4 as h4 h5.
      forwards* h6: dd h2 h4.
      inverts* h6.
      forwards* h7: dd h2 h4.
      inverts* h7.
  -
    forwards*: typing_completeb_gen H3.
Qed.


Theorem typing_completeb: forall e t A l b,
  Deterministic_blame_Calculus ->
  typing nil e Inf3 A t ->
  bsteps t (t_blame l b) ->
  steps e (e_blame l b).
Proof.
  introv dd typ red.
  forwards*: bsteps_bbsteps red.
  inverts* H.
  eapply typing_completeb_gens; eauto.
Qed.


(****** typing soundness blame *******************************************************)



Lemma typing_Cast_soundb: forall v t p b A,
  btyping nil t A (e_anno v p b A) ->
  value v ->
  Cast v p b A (e_blame p b) ->
  t ->* (t_blame p b) .
Proof.
  introv Typ val Red. gen t.
  inductions Red; intros.
  -
    inverts Typ as typ.
    inverts typ as typ.
    inverts val as h2 val.
    forwards* h3: btyping_typing typ.
    forwards* h4: principle_inf h3.
    forwards*h5: value_valueb2 typ.
    forwards* h6: Cast_sim_aux Red.
    rewrite h4 in *.
    forwards* h7: UG_sim_l H h6.
    forwards* h8: UG_to_sim H.
    forwards* h9: ug_ground_r H.
    forwards*h10: ground_eq h7.
    rewrite h10 in *.
    forwards* h1: IHRed.
    eapply bstep_nb.
    eapply bStep_dyna; eauto.
    eapply bstep_nb.
    rewrite fillb_cast.
    apply Step_evalb.
    auto.
    apply bStep_vany; eauto.
    simpl.
    auto.
  -
    inverts Typ as typ.
    inverts typ as typ.
    forwards* h1: btyping_regular_1 typ.
    inverts val as h2 val.
    forwards* h3: btyping_typing typ.
    forwards* h4: principle_inf h3.
    rewrite h4 in *.
    forwards* hh2: UG_decidable A.
    inverts hh2 as hh2.
    +
      inverts hh2 as hh2.
      forwards* hh3: ug_ground_r hh2.
      forwards* hh4: UG_to_sim hh2.
      assert(not(A1 = x)) as hh5.
      unfold not;intros nt.
      rewrite nt  in *.
      apply H; eauto.
      forwards* hh0: value_valueb2 typ.
      eapply bstep_nb.
      apply bStep_dyna; eauto.
      apply bstep_b.
      rewrite fillb_cast.
      apply Step_blameb; auto.
    +
      forwards* h0: value_valueb2 typ.
      apply bstep_b.
      apply bStep_vanyp; auto.
      *
      forwards* hh3: Ground_decidable A.
      inverts hh3 as hh3;auto.
      exfalso.
      destruct A; try solve[exfalso; apply hh3; auto].
      --
      forwards* hh4: hh2 (t_arrow t_dyn t_dyn).
      apply hh4.
      unfold UG; splits*;
      try solve[unfold not;intros nt;inverts nt];
      try solve[unfold not;intros nt;inverts nt as nt;inverts nt].
      unfold not;intros nt;inverts nt as nt.
      apply hh3; auto.
      --
      exfalso; apply H; auto.
      --
      forwards* hh4: hh2 (t_pro t_dyn t_dyn).
      apply hh4.
      unfold UG; splits*;
      try solve[unfold not;intros nt;inverts nt];
      try solve[unfold not;intros nt;inverts nt as nt;inverts nt].
      unfold not;intros nt;inverts nt as nt.
      apply hh3; auto.
      *
      unfold not;intros nt.
      substs*.
  -
    inverts Typ as typ.
    inverts typ as typ.
  -
    inverts Typ as typ.
    inverts typ as typ.
Qed.



Lemma typing_soundb_gen: forall e t p b A,
  btyping nil t A e->
  step e (e_blame p b) ->
  t ->* (t_blame p b).
Proof.
  introv Typ J. gen A t.
  inductions J; intros; try solve[inverts Typ].
  - destruct E; unfold fill in *; try solve[inverts Typ].
    + 
      inverts Typ as typ h1.
      forwards*: IHJ typ. 
      apply multi_blame_cast; eauto.
    +
      inverts Typ as typ1 typ2.
      forwards* h1: IHJ typ1.
      apply multi_blame_app2; eauto.
      forwards*: btyping_regular_1 typ2.
    +
      inverts Typ as typ1 typ2.
      inverts H as h1.
      forwards* h2: value_valueb2 typ1.
      apply multi_blame_app; eauto.
  - 
    inverts Typ as typ h1. 
    lets H0':H0.
    forwards*h0: cast_label H0.
    inverts h0.
    forwards*: typing_Cast_soundb H0'. 
Qed.


Theorem typing_soundb: forall e t A l b ,
  btyping nil t A e ->
  e ->** e_blame l b ->
  t ->* t_blame l b .
Proof.
  introv typ red. gen A t.
  inductions red;intros.
  -
  forwards* h1: typing_soundness_gen H.
  lets(tt1& h2& h3): h1.
  forwards*: IHred h3.
  -
  forwards*: typing_soundb_gen typ H.
Qed.



(************  diverge    **********)


Definition convergeb e := (exists v, bsteps e (t_term v) /\ valueb v) \/ exists l b, bsteps e (t_blame l b).


Definition converge e := (exists v, steps e (e_exp v) /\ value v) \/ exists l b, steps e (e_blame l b).


Lemma not_converge_diverge: forall e,
 not (converge e) ->
 diverge e.
Proof.
  introv.
  unfold diverge; intros;eauto.
Qed.


Lemma divergesl: forall e t A,
 Deterministic_blame_Calculus ->
 typing nil e Inf3 A t-> 
 diverge e ->
 divergeb t.
Proof.
  introv dd typ con.
  unfold diverge in *.
  unfold divergeb in *.
  unfold not; intros h1.
  inverts h1 as h1.
  -
    lets(tt1&h2&h3): h1.
    apply con.
    left.
    forwards* h4: typing_completeness h2.
    lets(ee1&h5&h6&h7):h4.
    eauto.
  -
    lets(ll1&bb1&h2): h1.
    forwards*: typing_completeb h2.
Qed. 


Lemma divergesr: forall e t A,
 btyping nil t  A e-> 
 divergeb t ->
 diverge e.
Proof.
  introv typ con.
  unfold diverge in *.
  unfold divergeb in *.
  unfold not; intros h1.
  inverts h1 as h1.
  -
    lets(tt1&h2&h3): h1.
    apply con.
    left.
    forwards* h4: typing_soundness h2.
    lets(ee1&h5&h6&h7):h4.
    eauto.
  -
    lets(ll1&bb1&h2): h1.
    forwards*: typing_soundb h2.
Qed. 