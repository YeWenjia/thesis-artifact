Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Deterministic
        Typing.

Require Import List. Import ListNotations.
Require Import Arith Omega.
Require Import Strings.String.


Lemma pval_decidable: forall s,
 lc_exp s -> pval s \/ not (pval s).
Proof.
  introv lc.
  inductions lc; 
  try solve [right; unfold not; intros nt; inverts nt];
  try solve[left*].
  -
    inverts IHlc.
    inverts* H;right; unfold not; intros nt; inverts nt.
    inductions lc;
    try solve [right; unfold not; intros nt; inverts nt];
    try solve[left*].
    inductions lc;
    try solve [right; unfold not; intros nt; inverts nt];
    try solve[left*].
    induction A0; try solve [right; unfold not; intros nt; inverts nt];
    try solve[left*].
    induction A; try solve [right; unfold not; intros nt; inverts nt];
    try solve[left*].
  -
    inverts IHlc1;
    try solve[try solve [right; unfold not; intros nt; inverts nt];
    try solve[left*]];
    try solve[inverts IHlc2;
    try solve[try solve [right; unfold not; intros nt; inverts nt];
    try solve[left*]]
    ];
    try solve[
    inverts IHlc2;
    try solve[right; unfold not; intros nt; inverts* nt];
    try solve[left*]].
Qed.



Lemma value_decidable: forall v,
   lc_exp v -> value v \/ not (value v).
Proof.
  introv lc. inductions v; eauto;
  try solve [right; unfold not; intros nt; inverts nt].
  - inverts lc. 
    forwards*: pval_decidable H0.
    inverts* H;
      try solve [right; unfold not; intros nt; inverts* nt];
      inductions v; eauto;
      try solve[left*].
Qed.





(* 
Lemma erase_prv2: forall e A,
value e ->
Typing nil e Inf A -> 
exists B, Typing nil (erase e) Inf B.
Proof.
  introv val typ.
  inverts* val; simpl in *; eauto.
  inverts typ. inverts* H2.
Qed. *)


Hint Resolve sim_refl : core.



Lemma Cast_preservation: forall p A v' B,
    pval p -> Cast p A (Expr v') -> meet (dynamic_type p) B A -> 
    Typing nil p Chk A -> Typing nil (e_val v' B) Inf B.
Proof with auto.
  introv Val Red mt Typ.
  lets Red': Red. gen B.
  inductions Red;intros;try solve[inverts* Val]; 
  lets Lc : Typing_regular_1 Typ;
  try solve [constructor*]; simpl in *.
  -
    inverts Typ as h1 h2.
    inverts h1; simpl in *.
    forwards* h3: meet_sim mt.
    lets(h4&h5&h6):h3.
    inverts* h4.
  -
    inverts Typ as h1 h2.
    inverts h1 as h1; simpl in *.
    inverts h1 as h1.
    inverts h1 as h1.
    forwards* h3: meet_sim mt.
    lets(h4&h5&h6):h3.
    forwards* h7: meet_more_precise mt.
    lets(h8&h9):h7.
    inverts Val as val.
    inverts* h8.
    forwards* h10:sim_sym h6. 
    eapply Typ_val; eauto.
  -
    inverts Val as h1 h2.
    inverts Typ as h3 h4.
    inverts h3 as h5 h6.
    inverts h4 as h7 h8.
    inverts mt as h9 h10.
    +
    forwards* h11: IHRed1 h9.
    forwards* h12: IHRed2 h10.
    inverts* h11.
    inverts* h12.
    inverts H4; try solve[inverts H2].
    inverts H9; try solve[inverts H7].
    forwards* h13: principle_inf H.
    forwards* h14: principle_inf H4.
    rewrite h13 in *.
    rewrite h14 in *.
    eapply Typ_val; simpl;eauto.
    rewrite h13 in *.
    rewrite h14 in *.
    eauto.
    +
    forwards* h13: principle_inf h5.
    forwards* h14: principle_inf h6.
    (* inverts mt.  *)
    forwards* h11: IHRed1.
    forwards* h12: IHRed2.
    inverts h11.
    inverts H4; try solve[inverts H2].
    inverts h12.
    inverts H9; try solve[inverts H7].
    eapply Typ_val; simpl;eauto.
  -
    forwards* h3: meet_sim mt.
    lets(h4&h5&h6):h3.
    forwards* h7: meet_more_precise  mt.
    eapply Typ_val; simpl;eauto.
    inverts h7 as h7 h8.
    inverts h7 as h7 h9.
    inverts h7 as h7.
    inverts h9 as h9 h10; eauto.
    inverts*h9.
    inverts* h10.
  -
    forwards* h3: meet_sim mt.
    lets(h4&h5&h6):h3.
    forwards* h7: meet_more_precise  mt.
    eapply Typ_val; simpl;eauto.
    inverts h7 as h7 h8.
    inverts h7 as h7 h9.
    inverts h7 as h7.
    inverts h9 as h9 h10; eauto.
Qed.



Theorem preservation : forall e e' dir A,
    Typing nil e dir A ->
    step e (Expr e') ->
    Typing nil e' dir A.
Proof.
  introv Typ. gen e'.
  lets Typ' : Typ.
  inductions Typ;
    try solve [introv J; inverts* J]; introv J.
  - (* i *)
    inverts J.
    apply Typ_val; eauto.
    destruct E; unfold simpl_fill in H0; inverts H0.
  - (* x *)
    inverts H0.
  - (* lambda *)
    inverts J.
    destruct E; unfold simpl_fill in *; inverts H2.
  - (* typing_app *)
    inverts* J;try solve[inverts Typ1].
    + destruct E; unfold simpl_fill in *; inverts H0.
      forwards*: IHTyp1 Typ1.
      forwards*: IHTyp2 Typ2.
    +
      inverts Typ1 as h1 h2.
      forwards* h3: pattern_abs_uniq H H4.
      inverts h3.
      inverts H8 as h4 h5; try solve[inverts h2].
      forwards*h6: principle_fval h4.
      rewrite h6 in *.
      inverts* H5.
      inverts* H.
      inverts* h5.
      eapply Typ_anno;eauto.
      eapply Typ_sim;eauto.
       eapply Typ_anno;eauto.
      eapply Typ_sim;eauto.
      (* inverts Typ1.
      inverts H7 as h1.
      inverts h1 as h1.
      inverts h1 as h1.
      inverts h1 as h1.
      forwards* h2: pattern_abs_uniq H H4.
      inverts h2.
      inverts H6.
      inverts H.
      *
      inverts H1.
      inverts h1 as h1 h2; try solve[inverts h1].
      inverts h1.
      eapply Typ_anno; eauto.
      eapply Typ_sim; eauto.
      eapply Typ_anno; eauto.
      eapply Typ_sim; eauto.
      eapply Typ_anno; eauto.
      eapply Typ_absv with (L := 
      ( union L (union (fv_exp e2) (fv_exp e))));intros; eauto.
      eapply Typ_anno; eauto.
      *
      inverts H1.
      inverts h1 as h1 h2; try solve[inverts h1].
      inverts h1.
      eapply Typ_anno; eauto.
      eapply Typ_sim with (A := C2); auto.
      eapply Typ_anno; eauto.
      eapply Typ_sim; eauto.
      eapply Typ_anno; eauto.
      eapply Typ_absv with (L := 
      ( union L (union (fv_exp e2) (fv_exp e))));intros; eauto.
      eapply Typ_anno; eauto.
    +
      inverts Typ1 as h2 h3 h4 h5.
      forwards* h1:pattern_abs_uniq H H1.
      inverts h1 as h1; simpl in *.
      inverts* H.
      inverts* H1.
      inverts* h5.
      inverts h4 as h41 h42.
      inverts h41 as h41.
      inverts h42 as h42 h43.
      eapply Typ_val; simpl in *;eauto.
    +
      inverts Typ1 as h2 h3 h4 h5.
      forwards* h1:pattern_abs_uniq H H1.
      inverts h1 as h1; simpl in *.
      inverts* H.
      inverts* H1.
      inverts* h5.
      inverts h4 as h41 h42.
      inverts h41 as h41.
      inverts h42 as h42 h43.
      eapply Typ_val; simpl in *;eauto. *)
  - (* typing_anno *)
    inverts* J.
    +
      inverts H3.
      *
      inverts Typ as h1 typ; try solve[inverts h1].
      inverts h1.
      eapply Typ_val; eauto.
      *
      inverts Typ as h1 typ; try solve[inverts h1].
      inverts h1.
      eapply Typ_val; eauto.
      eapply Typ_sim; eauto.
    +
      destruct E; unfold simpl_fill in *; inverts H.
      forwards*: IHTyp.
    + 
      forwards* h1: meet_more_precise H3.
      inverts h1.
      forwards* h2: tpre_sim H.
      inverts Typ as typ.
      inverts typ.
      inverts H10; try solve[inverts H8].
      forwards* h3: principle_inf H1.
      rewrite h3 in *.
      eapply sim_sym in h2.
      rewrite <- h3 in *.
      forwards* h5: Cast_preservation H2 H3. 
  - (* pro *)
    inverts* J.
    +
    inverts Typ1. inverts Typ2.
    forwards* h1:tpre_sim H7.
    forwards* h2:tpre_sim H11.
    inverts H6 as typ1; try solve[inverts H4].
    inverts H10 as typ2; try solve[inverts H8].
    forwards* h3: principle_inf typ1.
    forwards* h4: principle_inf typ2.
    eapply Typ_val; simpl in *;eauto.
    +
    destruct E; unfold simpl_fill in *; inverts H.
    forwards*: IHTyp1 Typ1.
    forwards*: IHTyp2 Typ2.
  - (* projl *)
    inverts* J.
    +
      destruct E; unfold simpl_fill in *; inverts H0.
      forwards*: IHTyp Typ.
    +
      inverts Typ;simpl in *.
      forwards* h1: pattern_pro_uniq H H2. inverts* h1.
      inverts H.
      *
      inverts H2.
      inverts* H8.
      inverts* H.
      inverts H9.
      forwards* h2: principle_inf H8.
      forwards* h3: principle_inf H10.
      rewrite h2 in *.
      rewrite h3 in *.
      inverts* H0.
      rewrite <- h2 in H7; eauto.
      *
      inverts H8. inverts H.
      eapply Typ_val; eauto.
  - (* projr *)
    inverts* J.
    +
      destruct E; unfold simpl_fill in *; inverts H0.
      forwards*: IHTyp Typ.
    +
      inverts Typ;simpl in *.
      forwards* h1: pattern_pro_uniq H H2. inverts* h1.
      inverts H.
      *
      inverts H2.
      inverts* H8.
      inverts* H.
      inverts H9.
      forwards* h2: principle_inf H8.
      forwards* h3: principle_inf H10.
      rewrite h2 in *.
      rewrite h3 in *.
      inverts* H0.
      rewrite <- h3 in H12; eauto.
      *
      inverts H8. inverts H.
      eapply Typ_val; eauto.
  - (* val *)
    forwards*: step_not_value J.
  - (* nbeta *)
    inverts* J.
    +
      destruct E; unfold simpl_fill in *; inverts H1.
      *
        forwards*: step_not_abs H4.
      *
        forwards*: IHTyp Typ.
    +
      pick fresh x. forwards*: H x.
      rewrite (subst_exp_intro x); eauto.
      eapply typing_c_subst_simpl; eauto.
  -
    inverts J as h1 h2 h3;eauto.
    +
      destruct E; unfold simpl_fill in *; inverts h3.
  -
    inverts J as h1 h2 h3;eauto.
    +
      destruct E; unfold simpl_fill in *; inverts h3.
  - (* |f| e *)
    inverts J as h1 h2 h3;eauto;
    try solve[inverts* Typ1].
    +
      destruct E; unfold simpl_fill in *; inverts h3.
      forwards*: step_not_fvalue h2.
      inverts* h1.
    +
      inverts Typ1 as h4 h5.
      inverts h4 as h6 h7.
      inverts h6 as h6 h8.
      inverts h6 as h9 h10 ; try solve[inverts h9].
      inverts* h9.
      inverts h7; eauto.
      eapply Typ_anno; eauto.
      eapply Typ_sim; eauto.
      eapply Typ_anno; eauto.
      eapply Typ_absv; eauto.
Qed.


Theorem preservation_multi_step : forall e e' dir  T,
    Typing nil e dir T ->
    e ->* (Expr e') ->
    Typing nil e' dir T.
Proof.
  introv Typ Red.
  inductions Red; eauto.
  lets*: preservation Typ.
Qed.


Lemma Cast_progress: forall p A A',
    pval p -> Typing [] p Chk A' -> 
    meet (dynamic_type p) A A' -> exists r, Cast p A' r.
Proof.
  introv Val Typ mt. gen A A'.
  inductions Val; intros; simpl in *; eauto.
  -
    destruct(sim_decidable (t_arrow A1 B1) A'); eauto.
  -
    inverts Typ as typ h3.
    inverts typ as h1 h2.
    inverts h3.
    +
    forwards* h8: meet_sim mt.
    lets(h9&h10&h11):h8.
    inverts h9.
    * 
    inverts mt as h4 h5.
    *
    inverts mt as h4 h5.
    +
    forwards* h8: meet_sim mt.
    lets(h9&h10&h11):h8.
    inverts h9.
    * 
    inverts mt as h4 h5.
    forwards* h6: IHVal1 t_dyn (dynamic_type u1).
    forwards* h7: IHVal2 t_dyn (dynamic_type u2).
    inverts h6 as h6.
    inverts h7 as h7.
    destruct x; eauto.
    destruct x0; eauto.
    (* forwards* h12: Cast_preservation h6.
    forwards* h13: Cast_preservation h7.
    forwards* h14: Cast_prv_value h6.
    forwards* h15: Cast_prv_value h7.
    inverts h14; inverts h12.
    inverts h15; inverts* h13. *)
    *
    inverts mt as h4 h5.
    forwards* h6: IHVal1  h4.
    forwards* h7: IHVal2  h5.
    inverts h6 as h6.
    inverts h7 as h7.
    destruct x; eauto.
    destruct x0; eauto.
    (* forwards* h12: Cast_preservation h6.
    forwards* h13: Cast_preservation h7.
    forwards* h16: meet_more_precise h4.
    forwards* h17: meet_more_precise h5.
    lets(h18&h19): h16.
    lets(h20&h21): h17.
    forwards* h14: Cast_prv_value h6.
    forwards* h15: Cast_prv_value h7.
    inverts h14; inverts h12.
    inverts h15; inverts* h13. *)
Qed.
  



Theorem progress_dir : forall e dir T,
    Typing nil e dir T ->
    value e \/ (exists r, step e r) \/ (exists e', e  = (e_abs e')).
Proof.
  introv Typ. lets Typ': Typ.
  inductions Typ; 
      lets Lc  : Typing_regular_1 Typ';
      try solve [left*];
      try solve [right*].
  - (** "var" *)
    inverts* H0.
  - (* app *)
    right. inverts Lc. 
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp1.
    lets* [Val2 | [[e2' Red2] | abs2]]: IHTyp2.
    +
      inverts Val1 as val1.
      destruct(sim_decidable (dynamic_type p) (t_arrow t_dyn t_dyn)); eauto.
      assert(fval p) as h1;
      try solve[inverts val1;inverts H0; auto]; eauto.
      inverts* Typ1.
      inverts H8;try solve[inverts H6].
      forwards*: principle_fval H1.
      inverts h1; inverts* H1; eauto.
    +
      inverts Val1 as val1.
      destruct(sim_decidable (dynamic_type p) (t_arrow t_dyn t_dyn)); eauto.
      assert(fval p) as h1;
      try solve[inverts val1;inverts H0; auto]; eauto.
      inverts* Typ1.
      inverts H8;try solve[inverts H6].
      forwards*: principle_fval H1.
      inverts h1; inverts* H1; eauto.
    +
      inverts abs2 as h1.
      inverts Val1 as val1.
      destruct(sim_decidable (dynamic_type p) (t_arrow t_dyn t_dyn)); eauto.
      assert(fval p) as h1;
      try solve[inverts val1;inverts H0; auto]; eauto.
      inverts* Typ1.
      inverts H8;try solve[inverts H6].
      forwards*: principle_fval H1.
      inverts h1; inverts* H1; eauto.
    +
      rewrite sfill_appl. 
      destruct e1'. 
      * 
      left. exists.
      apply Step_eval; eauto.
      *
      left. 
      exists. apply Step_blame; eauto.
    +
     inverts abs1.
     inverts Typ1.
  - (** anno *)
    inverts* Lc.
    destruct~ IHTyp as [ Val | [[t' Red] | abs]].
    + (* e_anno v A *)
      inverts Val as val.
      inverts Typ as typ.
      inverts typ.
      destruct(sim_decidable (dynamic_type p) A); eauto.
      forwards* h1: meet_progress H.
      lets(tt1& h2): h1.
      inverts H6; try solve[inverts val].
      forwards* h7: principle_inf H2.
      forwards* h4: meet_more_precise h2.
      lets(h5&h6):h4.
      forwards* h8: tpre_sim h5.
      apply sim_sym in h8.
      rewrite h7 in h8.
      forwards* h3: Cast_progress h2.
      inverts* h3.
      destruct x; eauto.
    + 
      rewrite sfill_anno. 
      destruct t'; eauto.
    +
      inverts* abs.
      inverts* Typ.
      inverts* H.
  - (* chk *)
    forwards*: IHTyp.
  - (* pro *)
    inverts Lc.
    lets* [Val1 | [[e1' Red1]| abs1]]: IHTyp1.
    lets* [Val2 | [[e2' Red2]| abs2]]: IHTyp2.
    +
    inverts Val1.
    inverts* Val2.
    +
    rewrite sfill_pror. 
    right. left. destruct e2'; eauto.
    +
    inverts abs2; inverts Typ2. 
    +
    rewrite sfill_prol. 
    right. left.
    destruct e1'; eauto.
    +
    inverts abs1; inverts Typ1. 
  - (* projl *)
    inverts* Lc.
    destruct~ IHTyp as [ Val | [[t' Red] | abs]].
    +
    inverts Val.
    inverts Typ.
    destruct(sim_decidable (dynamic_type p) (t_pro t_dyn t_dyn)); eauto.
    inverts H5; inverts* H2.
    +
    right.
    rewrite sfill_l. destruct t'. left. exists.
    apply Step_eval; eauto. left. exists. apply Step_blame; eauto.
    +
    inverts abs; inverts Typ.
  - (* projr *)
    inverts* Lc.
    destruct~ IHTyp as [ Val | [[t' Red] | abs]].
    +
    inverts Val.
    inverts Typ.
    destruct(sim_decidable (dynamic_type p) (t_pro t_dyn t_dyn)); eauto.
    inverts H5; inverts* H2.
    +
    right.
    rewrite sfill_r. destruct t'. left. exists.
    apply Step_eval; eauto. left. exists. apply Step_blame; eauto.
    +
    inverts abs; inverts Typ.
  -
    inverts Lc as lc1 lc2.
    forwards* h1: IHTyp.
    inverts h1 as h2; eauto.
    inverts h2 as h2.
    lets (ee&h3): h2.
    rewrite sfill_appr. destruct ee; eauto.
    inverts h2; inverts Typ.
  -
    inverts* H; inverts Typ1.
    +
    lets* [Val2 | [[e2' Red2] | abs2]]: IHTyp2.
    *
      inverts* Val2; inverts Typ2.
      inverts H; simpl in *;try solve[inverts* H7].
    *
      right.
      rewrite sfill_appr.
      destruct e2'. 
      --
      left.
      exists.
      apply Step_eval; eauto.
      --
      left. 
      exists. apply Step_blame; eauto.
    *
      inverts* abs2.
      inverts Typ2.
      +
      lets* [Val2 | [[e2' Red2] | abs2]]: IHTyp2.
      *
        inverts* Val2; inverts Typ2.
        inverts H; simpl in *;try solve[inverts* H7].
      *
        right.
        rewrite sfill_appr.
        destruct e2'. 
        --
        left.
        exists.
        apply Step_eval; eauto.
        --
        left. 
        exists. apply Step_blame; eauto.
      *
        inverts* abs2.
        inverts Typ2.
Qed.


Theorem Progress : forall e T,
  Typing nil e Inf T ->
  value e \/ (exists r, step e r).
Proof.
  introv Typ.
  forwards* h1: progress_dir Typ.
  inverts h1 as h1; eauto.
  inverts h1 as h1; eauto.
  inverts h1;inverts* Typ.
Qed.

