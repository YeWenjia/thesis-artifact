Require Import LibTactics.
Require Import Metalib.Metatheory.

Require Import
        syntax_ott
        rules_inf
        Infrastructure
        Typing
        Key_Properties  
        Deterministic
        Subtyping_inversion.

Require Import List. Import ListNotations.
Require Import Strings.String.
Require Import Lia.





Lemma fvalue_decidable:forall f,
 lc_dexp f -> fvalue f \/ not(fvalue f).
Proof.
  introv lc.
  inductions lc;
  try solve[right; unfold not; intros nt; inverts* nt; inverts* H];
  try solve [left*].
  inverts IHlc as h1; try solve[right; unfold not; intros nt; inverts* nt; inverts* H].
  destruct A; try solve[left*];
  try solve[right; unfold not; intros nt; inverts* nt; inverts* H].
  inductions lc;
  try solve[right; unfold not; intros nt; inverts* nt; inverts* H];
  try solve [left*].
  destruct A; try solve[left*];
  try solve[right; unfold not; intros nt; inverts* nt; inverts* H].
Qed.


Lemma lambda_decidable: forall e,
 (exists e', e = (de_abs e')) \/ not(exists e', e = (de_abs e')).
Proof.
 introv.
 destruct e; try solve[left; exists*];
 try solve[right;unfold not;intros nt;inverts nt as h0; inverts h0].
Qed.

Lemma value_decidable_gen: forall v n,
   size_dexp v < n ->
  lc_dexp v -> value v \/ not (value v).
Proof.
  introv sz. gen v.
  inductions n; intros;try solve[lia].
  inductions H;
  try solve[right; unfold not; intros nt; inverts* nt;inverts* H1];
  try solve[right; unfold not; intros nt; inverts* nt;inverts* H];
  try solve[right; unfold not; intros nt; inverts* nt;inverts* H0];
  try solve [left*].
  -
    forwards* h1: IHn e1. simpl in *;lia.
    forwards* h2: IHn e2. simpl in *;lia.
    inverts h1 as h1;
    try solve[right; unfold not;intros nt;inverts* nt];
    try solve[right; unfold not;intros nt;inverts* nt;inverts H1].
    +
      inverts h2 as h2;
      try solve[left*];
      try solve[right; unfold not;intros nt;inverts* nt];
      try solve[right; unfold not;intros nt;inverts* nt;inverts H1].
  -
    forwards* h1: IHn e. simpl in *;lia.
     inverts h1 as h1;
     try solve[right; unfold not;intros nt;inverts* nt];
     try solve[right; unfold not;intros nt;inverts* nt;inverts* H0].
     forwards* h2: fvalue_decidable e.
     inverts h2 as h2.
     +
     destruct A;
     try solve[right; unfold not;intros nt;inverts* nt;inverts* H0];
     try solve[left*].
     +
     inverts* h1;try solve[left*];
       try solve[ right; unfold not;intros nt;inverts* nt;inverts* H0];
       try solve[ right; unfold not;intros nt;inverts* nt;inverts* H1];
       try solve[ right; unfold not;intros nt;inverts* nt;inverts* H2].
    +
      destruct A; try solve[right; unfold not;intros nt;inverts nt as h3;inverts* h3; inverts h1 as h1;
        inverts h1].
        destruct(lambda_decidable e).
        inverts* H0.
        right.
        unfold not;intros nt; inverts nt as h0; inverts h0.
        apply H0; exists*.
        apply h1; eauto.
  -
    forwards* h1: IHn e.
    simpl in *; lia.
    inverts h1 as h1; try solve[left*];
    try solve[right; unfold not;intros nt;inverts* nt;inverts* H0].
Qed.



Lemma value_decidable: forall v,
   lc_dexp v -> value v \/ not (value v).
Proof.
  introv lc.
  eapply  value_decidable_gen; eauto.
Qed.


Lemma danno_same_typ: forall p t1 t2,
 Typing nil (de_anno p t1) Inf t2 ->
 t1 = t2.
Proof.
  introv typ.
  inverts* typ.
Qed.



Lemma ityp_decidable: forall t l,
 ityp t l \/ not(ityp t l).
Proof.
  introv. gen l.
  inductions t; intros; try solve[right; unfold not; intros nt; inverts* nt];eauto.
  forwards*: IHt1 l. forwards*: IHt2 l.
  inverts* H.
  inverts* H0.
  right; unfold not; intros nt; inverts* nt.
  destruct(l == l0); try solve[inverts* e];eauto.
  right; unfold not; intros nt; inverts* nt.
Qed.



Hint Resolve sub_reflexivity : core.





Lemma get_ty_well: forall A l B,
 well A ->
 get_ty A l B ->
 well B.
Proof.
  introv well gt.
  inductions gt; try solve[inverts* well]; eauto.
Qed.


Lemma value_not_bot: forall v t, 
  value v ->
  [] ⊢ v ⇒ t ->
  not (sub t dt_bot).
Proof.
  introv val typ.
  gen t.
  inductions val; intros;try solve[inverts* typ; unfold not; intros nt;inverts* nt]; eauto.
  forwards* h1: fvalue_ftype H.
  lets(t1&t2&h3): h1.
  forwards* h2: fprincipal_inf typ.
  rewrite h2 in *. subst.
   unfold not; intros nt;inverts* nt.
Qed.



Lemma Cast_preservation_gen: forall v' v A B n,
    size_dexp v + size_dtyp A < n ->
    well A ->
    value v -> Typing nil v Chk B -> 
    Cast v A (v') -> Typing nil v' Inf A.
Proof.
  introv sz Well Val Typ Red. gen v A B v'.
  inductions n; intros; try solve[lia].
  inductions Red; intros;try solve[inverts Typ]; auto.
  - (* f *)
    inverts Typ as h1;
    try solve[
      inverts Val as h2; inverts h2
    ].
    +
    forwards h2: fprincipal_inf h1; auto.
    rewrite h2 in *.
    eapply Typ_anno; eauto.
  - (* rcd *)
    inverts Well. inverts Val as h1; try solve[inverts h1].
    inverts Typ as h3. inverts h3 as h3.
    forwards* h2: IHn Red. 
    simpl in *; lia.
  - (* mergel *)
    inverts Val as h1; try solve[inverts h1].
    inverts Typ as h2. inverts h2 as h3 h4.
    forwards* h5: IHn Red.
    simpl in *; lia.
  - (* mergel *)
    inverts Val as h1; try solve[inverts h1].
    inverts Typ as h2. inverts h2 as h3 h4.
    forwards* h5: IHn Red.
    simpl in *; lia.
  - (* and *)
    inverts Well.
    forwards h1: IHn Typ Red1; auto.
    simpl in *; lia.
    forwards h2: IHn Typ Red2; auto.
    simpl in *; lia.
Qed.



Lemma Cast_preservation: forall v' v A B,
    well A ->
    value v -> Typing nil v Chk B -> 
    Cast v A v' -> Typing nil v' Inf A.
Proof.
  introv Well Val Typ Red.
  eapply Cast_preservation_gen;eauto.
Qed.



Lemma Cast_progress_gen: forall n v A,
    size_dexp v + size_dtyp A < n ->
    value v -> Typing nil v Chk A ->
    exists r, Cast v A r.
Proof.
  introv sz Val Typ. gen v A.
  inductions n; intros; try solve[lia].
  inverts Typ as h1 h3; try solve[inverts Val as h0;inverts h0].
  forwards* h2: principal_inf h1.
  inductions A; intros;
  try solve[forwards*: value_lc Val].
  -
    inverts Val; simpl in *; try solve[inverts h1; inverts h3]; eauto.
    +
      forwards* h7: fvalue_ftype H.
      lets(tt1&tt2&h8):h7.
      rewrite h8 in *. subst.
      inverts h3. 
    +
      inverts h2.
      inverts h1 as h4 h5; simpl in *.
      inverts h3 as h3.
      *
      forwards* h6: IHn e1 dt_int.
      simpl in *; lia.
      lets (r1&h7):h6.
      eauto.
      *
      forwards* h6: IHn e2 dt_int.
      simpl in *; lia.
      lets (r1&h7):h6.
      eauto.
  (* -
    forwards*: value_lc Val. *)
  -
    forwards*: value_not_bot h1 h3.
  -
    inverts Val; simpl in *; try solve[inverts h1; inverts h3]; eauto.
    +
      forwards* h7: fvalue_ftype H.
      lets(tt1&tt2&h8):h7.
      rewrite h8 in *. subst.
      rewrite <- h8 in *.
      eauto.
    +
      inverts h2.
      inverts h1 as h4 h5; simpl in *.
      inverts h3 as h3.
      *
      forwards* h6: IHn e1 (dt_arrow A1 A2).
      simpl in *; lia.
      lets (r1&h7):h6.
      eauto.
      *
      forwards* h6: IHn e2 (dt_arrow A1 A2).
      simpl in *; lia.
      lets (r1&h7):h6.
      eauto.
  -
    forwards* h6: principal_inf h1.
    rewrite h2 in *.
    forwards* h8: dand_inversion h3.
    inverts h8 as h8 h9.
    inverts H1.
    forwards* h5: IHn v A1.
    simpl in *; lia.
    lets (r1&h7):h5.
    forwards* h10: IHn v A2.
    simpl in *; lia.
    lets (r2&h11):h10.
    eauto.
  -
    inverts Val; simpl in *; try solve[inverts h1; inverts h3]; eauto.
    +
      forwards* h7: fvalue_ftype H.
      lets(tt1&tt2&h8):h7.
      rewrite h8 in *. subst.
      inverts h3.
    +
      inverts h2.
      inverts h1 as h4 h5; simpl in *.
      inverts h3 as h3.
      *
      forwards* h6: IHn e1 (dt_rcd l A).
      simpl in *; lia.
      lets (r1&h7):h6.
      eauto.
      *
      forwards* h6: IHn e2 (dt_rcd l A).
      simpl in *; lia.
      lets (r1&h7):h6.
      eauto.
    +
     inverts h1 as h1.
     inverts h3 as h3.
     inverts TEMP0 as h4.
     inverts H1.
     forwards* h6: IHn e A.
      simpl in *; lia.
      lets (r1&h7):h6.
      eauto.
Qed.


Lemma Cast_progress: forall v A ,
    value v -> Typing nil v Chk A ->
    exists r, Cast v A r.
Proof.
  introv Val Typ.
  eapply Cast_progress_gen; eauto.
Qed.


(* we rely on for some lemmas JMeq.JMeq_eq : forall (A : Type) (x y : A), JMeq.JMeq x y -> x = y but it is safe. *)
Theorem preservation : forall e e' dir A,
    Typing nil e dir A -> 
    step e e' -> 
    Typing nil e' dir A.
Proof.
  introv Typ. 
  gen e'.
  lets Typ' : Typ.
  inductions Typ;
    try solve [introv J; forwards*: step_not_value J];
    try solve [introv J; inverts* J;
    destruct E; unfold fill in *; inverts* H0]; introv J;
    try solve[inverts* H0].
  - (* lam *)
    forwards* h1: Typing_regular_1 Typ'.
    forwards*: step_not_abs J.
  - (* app *)
    inverts* J; try solve[inverts Typ1];
    try solve[inverts H2 as h0;inverts h0].
    + 
      destruct E; unfold fill in *; inverts H.
      forwards*: IHTyp1 Typ1.
      forwards*: IHTyp2 Typ2.
    +
      inverts Typ1 as h1. 
      inverts h1 as h2; try solve[inverts H2 as h0;inverts h0].
      *
      apply Typ_anno; eauto.
      *
      inverts H2; try solve[inverts h2].
      forwards* h8: fvalue_ftype H3.
      lets(t1&t2&h9): h8.
      forwards* h10: principal_inf h2.
      rewrite h10 in *. subst.
      inverts H0.
      inverts H1.
      forwards* h11: Typing_well h2. inverts h11.
      eapply Typ_anno; auto.
      eapply Typ_sub with (A := t2); eauto.
  - (* anno *)
    inverts* J; try solve[inverts H1].
    + destruct E; unfold fill in *; inverts H.
      forwards*: IHTyp Typ.
    +
      forwards* h1: Typing_well Typ.
      forwards* h2: Cast_preservation H2.
    +
       inverts Typ as h1 h2 h3;
       try solve[inverts h1]. 
      pick fresh y.
      rewrite (subst_dexp_intro y); eauto.
      eapply Typ_anno; auto.
      eapply typing_c_subst_simpl; eauto.
  - (* proj *)
    inverts* J; try solve[inverts H2].
    + destruct E; unfold fill in *; inverts H0.
      forwards*: IHTyp Typ.
    + 
      forwards* h1: principal_inf Typ.
      rewrite h1 in *. 
      forwards* h2: get_ty_uniq H H3.
      inverts h2.
      forwards* h4: Typing_well Typ.
      forwards* h5: get_ty_well H. 
      forwards* h3: Cast_preservation H5.
      inverts* h3.
  - (* rcd *) 
    inverts* J; try solve[inverts H1].
    + destruct E; unfold fill in *; inverts H.
      forwards*: IHTyp Typ.
  -
    inverts* J; try solve[inverts H2].
    + destruct E; unfold fill in *; inverts H2.
  -
    inverts* J; try solve[inverts H1].
    + destruct E; unfold fill in *; inverts H1;
      try solve[forwards*: step_not_abs H3].
      forwards*: IHTyp Typ.
    +
      pick fresh y.
      rewrite (subst_dexp_intro y); eauto.
      forwards*: H. 
      eapply typing_c_subst_simpl; eauto.
Qed.



Theorem preservation_cbn : forall e e' dir A,
    Typing nil e dir A -> 
    cbn e e' -> 
    Typing nil e' dir A.
Proof.
  introv Typ. 
  gen e'.
  lets Typ' : Typ.
  inductions Typ;
    try solve [introv J; forwards*: nstep_not_value J];
    try solve [introv J; inverts* J;
    destruct E; unfold filln in *; inverts* H0]; introv J;
    try solve[inverts* H0].
  - (* lam *)
    forwards* h1: Typing_regular_1 Typ'.
    forwards*: nstep_not_abs J.
  - (* app *)
    inverts* J; try solve[inverts Typ1].
    + 
      destruct E; unfold filln in *; inverts H.
      forwards*: IHTyp1 Typ1.
    +
      inverts Typ1 as h1. 
      inverts h1 as h2; try solve[inverts H2 as h0;inverts h0].
      *
      apply Typ_anno; eauto.
      *
      inverts H2; try solve[inverts h2].
      forwards* h8: fvalue_ftype H3.
      lets(t1&t2&h9): h8.
      forwards* h10: principal_inf h2.
      rewrite h10 in *. subst.
      inverts H0.
      inverts H1.
      forwards* h11: Typing_well h2. inverts h11.
      eapply Typ_anno; auto.
      eapply Typ_sub with (A := t2); eauto.
  - (* anno *)
    inverts* J; try solve[inverts H1 as h0;inverts h0].
    + destruct E; unfold filln in *; inverts H.
      forwards*: IHTyp Typ.
    +
      forwards* h1: Typing_well Typ.
      forwards* h2: Cast_preservation H2.
    +
       inverts Typ as h1 h2 h3;
       try solve[inverts h1]. 
      pick fresh y.
      rewrite (subst_dexp_intro y); eauto.
      eapply Typ_anno; auto.
      eapply typing_c_subst_simpl; eauto.
  - (* proj *)
    inverts* J; try solve[inverts H2].
    + destruct E; unfold filln in *; inverts H0.
      forwards*: IHTyp Typ.
    + 
      forwards* h1: principal_inf Typ.
      rewrite h1 in *. 
      forwards* h2: get_ty_uniq H H3.
      inverts h2.
      forwards* h4: Typing_well Typ.
      forwards* h5: get_ty_well H. 
      forwards* h3: Cast_preservation H5.
      inverts* h3.
  - (* rcd *) 
    inverts* J; try solve[inverts H1].
    + destruct E; unfold filln in *; inverts H.
      forwards*: IHTyp Typ.
  -
    inverts* J; try solve[inverts H2 as h0;inverts h0].
    + destruct E; unfold fill in *; inverts H2.
  -
    inverts* J; try solve[inverts H1].
    + destruct E; unfold filln in *; inverts H1;
      try solve[forwards*: nstep_not_abs H3].
    +
      pick fresh y.
      rewrite (subst_dexp_intro y); eauto.
      forwards*: H. 
      eapply typing_c_subst_simpl; eauto.
Qed.



Lemma Cast_rcd_prv: forall v l A v',
 Cast v (dt_rcd l A) v' ->
 exists v1, v' = (de_rcd l v1).
Proof.
  introv Red.
  inductions Red; eauto.
Qed.




Lemma fill_appl : forall e1 e2,
  (de_app e1 e2) = (fill (dappCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_appr : forall e1 e2,
  (de_app e1 e2) = (fill (dappCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma fill_mergel : forall e1 e2,
  (de_merge e1 e2) = (fill (dmergeCtxL e2) e1).
Proof.
  intros. eauto.
Qed.


Lemma fill_merger : forall e1 e2,
  (de_merge e1 e2) = (fill (dmergeCtxR e1) e2).
Proof.
  intros. eauto.
Qed.



Lemma fill_rcd : forall l e,
  (de_rcd l e) = (fill (drcdCtx l) e).
Proof.
  intros. eauto.
Qed.


Lemma fill_proj : forall l e,
  (de_proj e l) = (fill (dprjCtx l) e).
Proof.
  intros. eauto.
Qed.


Lemma fill_anno : forall A e,
  (de_anno e A) = (fill (dannoCtx A) e).
Proof.
  intros. eauto.
Qed.


Lemma get_ty_sub: forall A l B,
  get_ty A l B ->
  sub A (dt_rcd l B).
Proof.
  introv gv.
  inductions gv; eauto.
Qed.



Theorem progress_dir : forall e dir A,
    Typing nil e dir A ->
    value e \/ (exists r, step e r) \/ (exists e', e  = (de_abs e') \/ (exists e', e  = (de_fixpoint e'))).
Proof. 
  introv Typ.
  lets Typ': Typ.
  inductions Typ;
    lets Lc  : Typing_regular_1 Typ';
    try solve [inverts Heqflg];
    subst;
    try solve [left*];
    try solve [right*].
  - Case "var".
    invert H0.
  - Case "app".
    right. inverts Lc.
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp1.
    lets* [Val2 | [[e2' Red2] | abs2]]: IHTyp2.
    + 
        inverts Val1 as h1;inverts Typ1 as h2; inverts h1.
        --
        left*.
        --
        left*.
    + 
      left.
      forwards* h1: lambda_decidable e1.
      inverts h1 as h1.
      inverts h1 as h1; try solve[inverts Val1 as h0;inverts h0].
      inverts Val1; try solve[
        inverts Typ1; inverts H
      ].
      *
        inverts* H.
    +
      left.
      forwards* h1: lambda_decidable e1.
      inverts h1 as h1.
      inverts h1 as h1; try solve[inverts Val1 as h0;inverts h0].
      inverts Val1; try solve[
        inverts Typ1; inverts H
      ].
      *
        inverts* H.
    +
      left. 
      rewrite fill_appl.   exists.
      apply step_eval; eauto. 
    +
      inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ1];
      try solve[inverts abs1; inverts Typ1].
  - Case "merge".
    inverts Lc.
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp1.
    lets* [Val2 | [[e2' Red2] | abs2]]: IHTyp2.
    + right. left.
      rewrite fill_merger.   exists.
      apply step_eval; eauto. 
    +
      inverts abs2 as abs2.
      inverts abs2 as abs2;
      try solve[
      inverts Typ2];
      try solve[inverts abs2; inverts Typ2].
    + right. left.
      rewrite fill_mergel. exists.
      apply step_eval; eauto. 
    +
      inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ1];
      try solve[inverts abs1; inverts Typ1].
  - Case "anno".
    inverts Lc.
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp.
    +
      forwards* h0: value_decidable (de_anno e A).
      inverts* h0.
      forwards* h1: Typing_well Typ.
      forwards* h2: Cast_progress A Typ.
      inverts h2 as h2; eauto.
      assert(NotVal (de_anno e A)) as hh0.
      unfold NotVal.
      unfold not;intros nt.
      inverts* nt.
      right. left. exists*.
    + 
      right. left. rewrite fill_anno.  exists.
      apply step_eval; eauto. 
    +
      inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ as h1 h2 h3;eauto;
      try solve[inverts* h3];
      try solve[inverts h1]].
      inverts abs1 as abs1.
      right.
      left*.
  - 
    inverts Lc. 
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp. 
    +
      forwards* h1: principal_inf Typ.
      rewrite <- h1 in *.
      forwards* h2: Typing_well Typ.
      forwards* h3: get_ty_well H.
      forwards h0: get_ty_sub H.
      forwards* h4: Cast_progress e (dt_rcd l B).
      inverts h4 as h4.
      forwards* h5: Cast_rcd_prv h4.
      lets(vv1&h6): h5.
      inverts* h6.
    +
      right.
      left.
      rewrite fill_proj.  exists.
      apply step_eval; eauto. 
    +
      inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ];
      try solve[inverts abs1; inverts Typ].
  - (* rcd *)
    inverts Lc. 
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp. 
    +
      right. left.
      rewrite fill_rcd.   exists.
      apply step_eval; eauto. 
    +
      inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ];
      try solve[inverts abs1; inverts Typ].
  - Case "subsumption".
    destruct~ IHTyp.
  -
    inverts Lc. 
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp.
   +
     right. left. 
      rewrite fill_appr.    exists.
      apply step_eval; eauto. 
   +
     inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ];
      try solve[inverts abs1; inverts Typ].
      Unshelve. eauto.
Qed.




Theorem Progress : forall e A,
    Typing nil e Inf A ->
    value e \/ (exists r, step e r).
Proof. 
  introv Typ.
  forwards* h1: Typing_chk Typ.
  inverts h1 as h1.
  forwards* h2:progress_dir h1.
  inverts h2 as h2; eauto.
  inverts h2 as h2; eauto.
  inverts h2 as h2; eauto.
  inverts h2 as h2; eauto.
  inverts Typ.
  inverts h2 as h2; eauto.
  inverts Typ.
Qed.




Lemma filln_appl : forall e1 e2,
  (de_app e1 e2) = (filln (ndappCtxL e2) e1).
Proof.
  intros. eauto.
Qed.


Lemma filln_mergel : forall e1 e2,
  (de_merge e1 e2) = (filln (ndmergeCtxL e2) e1).
Proof.
  intros. eauto.
Qed.


Lemma filln_merger : forall e1 e2,
  (de_merge e1 e2) = (filln (ndmergeCtxR e1) e2).
Proof.
  intros. eauto.
Qed.



Lemma filln_rcd : forall l e,
  (de_rcd l e) = (filln (ndrcdCtx l) e).
Proof.
  intros. eauto.
Qed.


Lemma filln_proj : forall l e,
  (de_proj e l) = (filln (ndprjCtx l) e).
Proof.
  intros. eauto.
Qed.


Lemma filln_anno : forall A e,
  (de_anno e A) = (filln (ndannoCtx A) e).
Proof.
  intros. eauto.
Qed.



Theorem progress_dir_cbn : forall e dir A,
    Typing nil e dir A ->
    value e \/ (exists r, cbn e r) \/ (exists e', e  = (de_abs e') \/ (exists e', e  = (de_fixpoint e'))).
Proof. 
  introv Typ.
  lets Typ': Typ.
  inductions Typ;
    lets Lc  : Typing_regular_1 Typ';
    try solve [inverts Heqflg];
    subst;
    try solve [left*];
    try solve [right*].
  - Case "var".
    invert H0.
  - Case "app".
    right. inverts Lc.
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp1.
    lets* [Val2 | [[e2' Red2] | abs2]]: IHTyp2.
    + 
        inverts Val1 as h1;inverts Typ1 as h2; inverts h1.
        --
        left*.
        --
        left*.
    + 
      left.
      forwards* h1: lambda_decidable e1.
      inverts h1 as h1.
      inverts h1 as h1; try solve[inverts Val1 as h0;inverts h0].
      inverts Val1; try solve[
        inverts Typ1; inverts H
      ].
      *
        inverts* H.
    +
      left.
      forwards* h1: lambda_decidable e1.
      inverts h1 as h1.
      inverts h1 as h1; try solve[inverts Val1 as h0;inverts h0].
      inverts Val1; try solve[
        inverts Typ1; inverts H
      ].
      *
        inverts* H.
    +
      left. 
      rewrite filln_appl.   exists.
      apply cbn_eval; eauto. 
    +
      inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ1];
      try solve[inverts abs1; inverts Typ1].
  - Case "merge".
    inverts Lc.
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp1.
    lets* [Val2 | [[e2' Red2] | abs2]]: IHTyp2.
    + right. left.
      rewrite filln_merger.   exists.
      apply cbn_eval; eauto. 
    +
      inverts abs2 as abs2.
      inverts abs2 as abs2;
      try solve[
      inverts Typ2];
      try solve[inverts abs2; inverts Typ2].
    + right. left.
      rewrite filln_mergel. exists.
      apply cbn_eval; eauto. 
    +
      inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ1];
      try solve[inverts abs1; inverts Typ1].
  - Case "anno".
    inverts Lc.
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp.
    +
      forwards* h0: value_decidable (de_anno e A).
      inverts* h0.
      forwards* h1: Typing_well Typ.
      forwards* h2: Cast_progress A Typ.
      inverts h2 as h2; eauto.
      assert(NotVal (de_anno e A)) as hh0.
      unfold NotVal.
      unfold not;intros nt.
      inverts* nt.
      right. left. exists*.
    + 
      right. left. rewrite filln_anno.  exists.
      apply cbn_eval; eauto. 
    +
      inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ as h1 h2 h3;eauto;
      try solve[inverts* h3];
      try solve[inverts h1]].
      inverts abs1 as abs1.
      right.
      left*.
  - 
    inverts Lc. 
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp. 
    +
      forwards* h1: principal_inf Typ.
      rewrite <- h1 in *.
      forwards* h2: Typing_well Typ.
      forwards* h3: get_ty_well H.
      forwards h0: get_ty_sub H.
      forwards* h4: Cast_progress e (dt_rcd l B).
      inverts h4 as h4.
      forwards* h5: Cast_rcd_prv h4.
      lets(vv1&h6): h5.
      inverts* h6.
    +
      right.
      left.
      rewrite filln_proj.  exists.
      apply cbn_eval; eauto. 
    +
      inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ];
      try solve[inverts abs1; inverts Typ].
  - (* rcd *)
    inverts Lc. 
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp. 
    +
      right. left.
      rewrite filln_rcd.   exists.
      apply cbn_eval; eauto. 
    +
      inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ];
      try solve[inverts abs1; inverts Typ].
  - Case "subsumption".
    destruct~ IHTyp.
  -
    inverts Lc. 
    lets* [Val1 | [[e1' Red1] | abs1]]: IHTyp.
    Unshelve. eauto.
Qed.


Theorem Progress_cbn : forall e A,
    Typing nil e Inf A ->
    value e \/ (exists r, cbn e r).
Proof. 
  introv Typ.
  forwards* h1: Typing_chk Typ.
  inverts h1 as h1.
  forwards* h2:progress_dir_cbn h1.
  inverts h2 as h2; eauto.
  inverts h2 as h2; eauto.
  inverts h2 as h2; eauto.
  inverts h2 as h2; eauto.
  inverts Typ.
  inverts h2 as h2; eauto.
  inverts Typ.
Qed.



Print Assumptions Cast_unique.
Print Assumptions Cast_preservation.
Print Assumptions Cast_progress.
Print Assumptions principal_inf.
Print Assumptions step_unique.
Print Assumptions preservation.
Print Assumptions Progress.