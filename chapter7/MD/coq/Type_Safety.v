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
Require Import Lia.
Require Import Strings.String.



Lemma dyn_decidable : forall A,
    dynamic A \/ ~dynamic A.
Proof.
  induction A; try solve[right; unfold not; intros nt; invert* nt]; 
  try solve[left*].
  - destruct IHA1.
    + left*.
    + destruct IHA2.
      * left*.
      * right;
        unfold not;
        intros nt;
        inverts* nt.
Qed.   


Lemma lambda_decidable: forall e,
 (exists e', e = (e_abs e')) \/ not(exists e', e = (e_abs e')).
Proof.
 introv.
 destruct e; try solve[left; exists*];
 try solve[right;unfold not;intros nt;inverts nt as h0; inverts h0].
Qed.


Lemma fvalue_decidable:forall f,
 lc_exp f -> fvalue f \/ not(fvalue f).
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


Lemma ground_decidable: forall t,
 Ground t \/ not(Ground t).
Proof.
  introv.
  inductions t; try solve[
    right; unfold not;intros nt;inverts* nt
  ];eauto.
  -
    destruct(eq_type t1).
    +
      destruct(eq_type t2).
      *
      subst*.
      *
      right;unfold not;intros nt;inverts* nt.
    +
      right;unfold not;intros nt;inverts* nt.
  -
    destruct(eq_type t1).
    +
      destruct(eq_type t2).
      *
      subst*.
      *
      right;unfold not;intros nt;inverts* nt.
    +
      right;unfold not;intros nt;inverts* nt.
  -
    destruct(eq_type t).
    +
      subst*.
    +
      right;unfold not;intros nt;inverts* nt.
Qed.





Lemma value_not_ground: forall v,
 value v ->
 not(Ground (principal_type v)) ->
 not(gvalue v).
Proof.
  introv h1 h2.
  inductions h1; simpl in *;try solve[inverts* h2];
  try solve[exfalso; apply h2; auto];
  try solve[unfold not;intros nt;inverts nt].
  -
    forwards* h5: fvalue_ftype H.
    lets(t1&t2&h6): h5.
    rewrite h6 in *.
    unfold not;intros nt;inverts nt as h3; simpl in *;
    try solve[inverts H].
    inverts* h6.
    inverts* h6.
  -
  unfold not;intros nt;inverts nt as h3; simpl in *.
  exfalso; apply h2; auto.
  -
  unfold not;intros nt;inverts nt as h3; simpl in *.
  exfalso; apply h2; auto.
Qed.

Lemma value_decidable_gen: forall v n,
   size_exp v < n ->
  lc_exp v -> value v \/ not (value v).
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
       destruct(ground_decidable (principal_type e)).
       forwards* hh1: value_ground h1.
       forwards* hh1: value_not_ground h1.
       right; unfold not;intros nt;inverts nt as h3;inverts* h3.
     +
       destruct A; try solve[right; unfold not;intros nt;inverts nt as h3;inverts* h3].
       *
         right; unfold not;intros nt;inverts nt as h3;inverts* h3.
         inverts h1 as h1.
         inverts h1.
       *
       destruct(ground_decidable (principal_type e));
       eauto.
       forwards* hh1: value_ground h1.
       forwards* hh1: value_not_ground h1.
       right; unfold not;intros nt;inverts nt as h3;inverts* h3.
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
   lc_exp v -> value v \/ not (value v).
Proof.
  introv lc.
  eapply  value_decidable_gen; eauto.
Qed.



Lemma anno_same_typ: forall p t1 t2,
 Typing nil (e_anno p t1) Inf t2 ->
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

Hint Resolve csub_reflexivity : core.


Lemma get_ty_well: forall A l B,
 well A ->
 get_ty A l B ->
 well B.
Proof.
  introv well gt.
  inductions gt; try solve[inverts* well]; eauto.
Qed.



Lemma Cast_preservation_gen: forall v' v A B n,
    size_exp v + size_typ A < n ->
    well A ->
    value v -> Typing nil v Chk B -> 
    Cast v A (r_e v') -> Typing nil v' Inf A.
Proof.
  introv sz Well Val Typ Red. gen v A B v'.
  inductions n; intros; try solve[lia].
  inductions Red; intros;try solve[inverts Typ]; auto.
  - (* f *)
    inverts Typ as h1; try solve[inverts Val as h2; inverts h2].
    +
    forwards h2: fprincipal_inf h1; auto.
    rewrite h2 in *.
    eapply Typ_anno; eauto.
  - (* u:dyn *)
    inverts Typ as h1. inverts h1 as h1. 
    inverts h1 as h1; try solve[inverts Val as h3; try solve[inverts h3]].
    inverts Val as h3; try solve[inverts h3].
    forwards hh1:gvalue_value h3.
    forwards* h2: IHn Red.
    simpl in *; lia.
  - (* rcd *)
    inverts Well. inverts Val as h1; try solve[inverts h1].
    inverts Typ as h3. inverts h3 as h3.
    forwards* h2: IHn Red. 
    simpl in *; lia.
  - (* vdyn *)
    inverts Typ as h1. inverts h1 as h1.
    eapply Typ_anno; auto.
  - (* s dyn *)
    inverts Typ as h1; try solve[inverts Val as h0;inverts h0].
    inverts H; simpl in *; try solve[inverts Red];
    try solve[inverts H0].
    + inverts* Red.
    + inverts* Red.
    + forwards h2: fvalue_ftype H0; auto.
      lets(t1&t2&h3): h2.
      rewrite h3 in *.
      simpl in *.
      inverts Red; try solve[inverts H0].
      eapply Typ_anno; eauto.
      eapply Typ_cs with (A := (t_arrow t_dyn t_dyn)); auto.
      eapply Typ_anno; eauto.
      forwards h4: principal_inf h1; auto.
      rewrite h3 in *; subst.
      eapply Typ_cs with (A := (t_arrow t1 t2)); auto.
    + inverts Red.
      inverts h1 as h1.
      forwards* h2: IHn H3.
      simpl in *; lia.
  - (* merge dyn *) 
    inverts Val as h1; try solve[inverts h1].
    inverts Typ as h2. inverts h2 as h3 h4.
    forwards h5: Typing_Chk h3; auto.
    forwards h6: Typing_Chk h4; auto.
    forwards h7: IHn h5 Red1 ; auto.
    simpl in *; lia.
    forwards h8: IHn h6 Red2 ; auto.
    simpl in *; lia.
    eapply Typ_anno; eauto.
  - (* v1 v2*)
    inverts Val as h1; try solve[inverts h1].
    inverts Typ as h2. inverts h2 as h3 h4.
    inverts H0.
    +
    forwards* h2: IHn Red1. 
    simpl in *; lia.
    +
    forwards* h2: IHn Red2. 
    simpl in *; lia.
    +
    forwards* h2: IHn Red1. 
    simpl in *; lia.
   - (* v *)
      inverts Well.
      inverts H.
      forwards h1: IHn Typ Red1; auto.
      simpl in *; lia.
      forwards h2: IHn Typ Red2; auto.
      simpl in *; lia.
Qed.


Lemma Cast_preservation: forall v' v A B,
    well A ->
    value v -> Typing nil v Chk B -> 
    Cast v A (r_e v') -> Typing nil v' Inf A.
Proof.
  introv Well Val Typ Red.
  eapply Cast_preservation_gen;eauto.
Qed.


Lemma Cast_progress_gen: forall n v A B,
    size_exp v + size_typ A < n ->
    value v -> Typing nil v Chk B ->
    exists r, Cast v A r.
Proof.
  introv sz Val Typ. gen v A B.
  inductions n; intros; try solve[lia].
  forwards* h1: csub_decidable (principal_type v) A.
  inverts h1 as h1 h2.
  inverts h1 as h3 h4.
  -
    inverts Typ as h5; try solve[inverts Val as h0;inverts h0].
    forwards* h6: principal_inf h5.
    rewrite h6 in *. 
    inductions A; intros;
    try solve[forwards*: value_lc Val].
    +
      inverts Val; simpl in *; try solve[inverts h5; inverts h3]; eauto.
      *
        forwards* h7: fvalue_ftype H.
        lets(tt1&tt2&h8):h7.
        rewrite h8 in *. subst.
        inverts h3. 
      *
        inverts h6.
        inverts h5 as h5 h6; simpl in *.
        forwards* h7: IHn e1 t_int.
        simpl in *; lia.
        forwards* h8: IHn e2 t_int.
        simpl in *; lia.
        lets (r1&h9):h7.
        lets (r2&h10):h8.
        forwards* h11: joina_progress r1 r2.
        inverts h11 as h11.
        exists*.
      *
        inverts h5 as h5.
        inverts h5 as h5; try solve[
          inverts H as h0;inverts h0
        ].
        forwards* : gvalue_value H.
        forwards* hh1: IHn g t_int.
        simpl in *; lia.
        lets(rr1& hh3): hh1.
        exists*.
    +
      inverts Val; simpl in *; try solve[inverts h5; inverts h3]; eauto.
      *
      rewrite <- h6 in h3; exists*.
      *
      inverts h6.
      inverts h5 as h5 h6; simpl in *.
      forwards* h7: IHn e1 (t_arrow A1 A2).
      simpl in *; lia.
      forwards* h8: IHn e2 (t_arrow A1 A2).
      simpl in *; lia.
      lets (r1&h9):h7.
      lets (r2&h10):h8.
      forwards* h11: joina_progress r1 r2.
      inverts h11 as h11.
      exists*.
      *
      inverts h5 as h5.
      inverts h5 as h5;
      try solve[
          inverts H as h0;inverts h0
        ].
      forwards* : gvalue_value H.
      forwards* hh1: IHn g (t_arrow A1 A2).
      simpl in *; lia.
      lets(rr1& hh3): hh1.
      exists*.
    +
      forwards* h7:IHn v A1.
      simpl in *; lia.
      forwards* h8:IHn v A2.
      simpl in *; lia.
      lets(rr1&h9): h7.
      lets(rr2&h10): h8.
      forwards* h11: joint_progress rr1 rr2.
      inverts h11 as h11.
      exists*.
    +
      destruct (eq_type A0).
      *
       subst.
       assert(exists v', v = (e_anno v' t_dyn)) as hh2.
       inverts Val;inverts* H.
       inverts H2; inverts* H4.
       inverts hh2 as hh2.
       forwards* hh3: value_lc Val.
       inverts hh3 as hh3.
       exists*.
      *
        rewrite <- h6 in *.
        forwards* hh1: value_lc Val.
        assert(svalue v \/ exists v1 v2, v = (e_merge v1 v2)) as h7.
        inverts* Val.
        inverts h7 as h7.
        --
          inverts h7.
          ++
          assert(Cast (e_lit i) (const(principal_type (e_lit i))) (r_e (e_lit i))) as h8.
          simpl in *;eauto.
          exists*.
          ++
          assert(Cast (e_top) (const(principal_type (e_top))) (r_e (e_top))) as h8.
          simpl in *;eauto.
          exists*.
          ++
          forwards* h9: fvalue_ftype H2.
          lets(t1&t2&h10): h9.
          assert(Cast (v) (const(principal_type (v))) (r_e (e_anno v (t_arrow t_dyn t_dyn)))) as h8.
          rewrite h10.
          simpl in *.
          eapply cast_f; eauto.
          rewrite h10; eauto.
          exists*.
          ++
          inverts h5 as h5.
          forwards* h9: IHn e t_dyn.
          simpl in *; lia.
          inverts h9 as h9.
          assert(exists e', x = (r_e e')) as h11.
          inverts* h9; try solve[inverts H3];
          try solve[exfalso; apply H4; eauto].
          inverts h11 as h11.
          assert(Cast (e_rcd l0 e) (const(principal_type (e_rcd l0 e))) (r_e (e_rcd l0 x0))) as h10.
          simpl in *; eauto.
          exists*.        
        --
        lets(v1&v2&h8):h7.
        subst.
        inverts Val as h8; try solve[inverts* h8];
        simpl in *.
        inverts h5 as h9 h10.
        forwards* h11: IHn v1 t_dyn.
        simpl in *; lia.
        forwards* h12: IHn v2 t_dyn.
        simpl in *; lia.
        lets(r1&h13): h11.
        lets(r2&h14): h12.
        assert(exists v1', r1 = (r_e v1')) as h15.
        inverts* h13; try solve[inverts H2];
        try solve[exfalso; apply H3; eauto].
        assert(exists v2', r2 = (r_e v2')) as h16.
        inverts* h14; try solve[inverts H2];
        try solve[exfalso; apply H3; eauto].
        inverts h15.
        inverts* h16.
    +
      inverts Val; simpl in *; try solve[ inverts H;inverts h5; inverts h3]; 
      try solve[inverts h5; inverts h3]; eauto.
      *
      inverts h6.
      inverts h5 as h5 h6; simpl in *.
      forwards* h7: IHn e1 (t_rcd l A).
      simpl in *; lia.
      forwards* h8: IHn e2 (t_rcd l A).
      simpl in *; lia.
      lets (r1&h9):h7.
      lets (r2&h10):h8.
      forwards* h11: joina_progress r1 r2.
      inverts h11 as h11.
      exists*.
      *
      inverts h6; inverts h3.
      inverts h5 as h5.
      forwards* hh1: IHn e A.
      simpl in *; lia.
      lets(rr1&hh2): hh1.
      destruct rr1; eauto.
      *
      inverts h5 as h5.
      inverts h5 as h5;try solve[
        inverts H as h0;inverts h0
      ].
      forwards* : gvalue_value H.
      forwards* hh1: IHn g (t_rcd l A).
      simpl in *; lia.
      lets(rr1& hh3): hh1.
      exists*.
  - 
    forwards*: value_lc Val.
Qed.



Lemma Cast_progress: forall v A B,
    value v -> Typing nil v Chk B ->
    exists r, Cast v A r.
Proof.
  introv Val Typ.
  eapply Cast_progress_gen; eauto.
Qed.


Theorem preservation : forall e e' dir A,
    Typing nil e dir A -> 
    step e (r_e e') -> 
    Typing nil e' dir A.
Proof.
  introv Typ. 
  gen e'.
  lets Typ' : Typ.
  inductions Typ;
    try solve [introv J; forwards*: step_not_value J];
    try solve [introv J; forwards*: step_not_abs J];
    try solve [introv J; inverts* J;
    destruct E; unfold fill in *; inverts* H0]; introv J.
  - (* app *)
    inverts* J; try solve[inverts H2];
    try solve[inverts Typ1];
    try solve[inverts H1 as h0;inverts h0 as h0;inverts h0].
    + 
      destruct E; unfold fill in *; inverts H0.
      forwards*: IHTyp1 Typ1.
      forwards*: IHTyp2 Typ2.
    +
      inverts Typ1 as h1. 
      inverts* H.
      inverts h1 as h2; try solve[inverts H1 as h0;inverts h0].
      *
      inverts H2.
      apply Typ_anno; eauto.
      *
      inverts H1; try solve[inverts h2].
      forwards* h8: fvalue_ftype H3.
      lets(t1&t2&h9): h8.
      forwards* h10: principal_inf h2.
      rewrite h10 in *. subst.
      inverts H0.
      inverts H2.
      forwards* h11: Typing_well h2. inverts h11.
      assert(dmatch (t_arrow t1 t2) (t_arrow t1 t2)); eauto.
      eapply Typ_anno; auto.
      eapply Typ_cs with (A := t2); eauto.
    +
      inverts Typ1 as h1.
      inverts H.
      eapply Typ_app; eauto.
  - (* anno *)
    inverts* J; try solve[inverts H1].
    + destruct E; unfold fill in *; inverts H.
      forwards*: IHTyp Typ.
    +
      forwards* h1: Typing_well Typ.
      forwards* h2: Cast_preservation H2.
    +
      inverts Typ as h1 h2 h3;try solve[inverts h1].
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      eapply Typ_anno; eauto. 
      eapply typing_c_subst_simpl; eauto.
    +
       inverts Typ as h1 h2 h3; try solve[inverts h1].
       inverts* h3.
  - (* proj *)
    inverts* J; try solve[inverts H2].
    + destruct E; unfold fill in *; inverts H0.
      forwards*: IHTyp Typ.
    + 
      forwards* h1: principal_inf Typ.
      rewrite h1 in *. 
      forwards* h2: get_ty_uniq H H4.
      inverts h2.
      forwards* h4: Typing_well Typ.
      forwards* h5: get_ty_well H. 
      forwards* h3: Cast_preservation H5.
      inverts* h3.
  - (* rcd *) 
    inverts* J; try solve[inverts H1].
    + destruct E; unfold fill in *; inverts H.
      forwards*: IHTyp Typ.
  - (* fix *)
    inverts* J; try solve[inverts H2].
    + destruct E; unfold fill in *; inverts H2.
  -
    inverts* J; try solve[inverts H1].
    + destruct E; unfold fill in *; inverts H1;
      try solve[forwards*: step_not_abs H4].
      forwards*: IHTyp Typ.
    +
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      forwards*: H. 
      eapply typing_c_subst_simpl; eauto.
Qed.




Theorem preservation_cbn : forall e e' dir A,
    Typing nil e dir A -> 
    cbn e (r_e e') -> 
    Typing nil e' dir A.
Proof.
  introv Typ. 
  gen e'.
  lets Typ' : Typ.
  inductions Typ;
    try solve [introv J; forwards*: nstep_not_value J];
    try solve [introv J; inverts* J;
    destruct E; unfold filln in *; inverts* H0]; introv J.
  - (* lam *)
    forwards* h1: Typing_regular_1 Typ'.
    forwards*: nstep_not_abs J.
  - (* app *)
    inverts* J; try solve[inverts H2];
    try solve[inverts Typ1].
    + 
      destruct E; unfold fill in *; inverts H0.
      forwards*: IHTyp1 Typ1.
      simpl.
      eauto.
    +
      inverts Typ1 as h1. 
      inverts* H.
      inverts h1 as h2; try solve[inverts H1 as h0;inverts h0];
      try solve[inverts H4 as h0;inverts h0].
      *
      inverts H1.
      apply Typ_anno; eauto.
      *
      inverts H4; try solve[inverts h2].
      forwards* h8: fvalue_ftype H2.
      lets(t1&t2&h9): h8.
      forwards* h10: principal_inf h2.
      rewrite h10 in *. subst.
      inverts H0.
      inverts H1.
      forwards* h11: Typing_well h2. inverts h11.
      assert(dmatch (t_arrow t1 t2) (t_arrow t1 t2)); eauto.
      eapply Typ_anno; auto.
      eapply Typ_cs with (A := t2); eauto.
    +
      inverts Typ1 as h1.
      inverts H.
      eapply Typ_app; eauto.
  - (* anno *)
    inverts* J; try solve[inverts H1].
    + destruct E; unfold fill in *; inverts H.
      forwards*: IHTyp Typ.
      simpl; eauto.
    +
      forwards* h1: Typing_well Typ.
      forwards* h2: Cast_preservation H2.
    +
      inverts Typ as h1 h2 h3;try solve[inverts h1].
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      eapply Typ_anno; eauto. 
      eapply typing_c_subst_simpl; eauto.
    +
      inverts Typ as h1 h2 h3.
      inverts* h3.
      inverts h1.
  - (* proj *)
    inverts* J; try solve[inverts H2].
    + destruct E; unfold fill in *; inverts H0.
      forwards*: IHTyp Typ.
      simpl; eauto.
    + 
      forwards* h1: principal_inf Typ.
      rewrite h1 in *. 
      forwards* h2: get_ty_uniq H H4.
      inverts h2.
      forwards* h4: Typing_well Typ.
      forwards* h5: get_ty_well H. 
      forwards* h3: Cast_preservation H5.
      inverts* h3.
  - (* rcd *) 
    inverts* J; try solve[inverts H1].
    + destruct E; unfold fill in *; inverts H.
      forwards*: IHTyp Typ.
      simpl; eauto.
  - (* fix *)
    inverts* J; try solve[inverts H2].
    + destruct E; unfold fill in *; inverts H2.
  -
    inverts* J; try solve[inverts H1].
    + destruct E; unfold fill in *; inverts H1;
      try solve[forwards*: nstep_not_abs H4].
    +
      pick fresh y.
      rewrite (subst_exp_intro y); eauto.
      forwards*: H. 
      eapply typing_c_subst_simpl; eauto.
Qed.



Theorem preservation_multi_step : forall e e' dir  T,
    Typing nil e dir T ->
    e ->* (r_e e') -> 
    Typing nil e' dir T.
Proof.
  introv Typ.
  inductions dir;intros;eauto;
  try solve[inductions H; eauto;
  lets*: preservation Typ].
Qed.




Lemma fill_appl : forall e1 e2,
  (e_app e1 e2) = (fill (appCtxL e2) e1).
Proof.
  intros. eauto.
Qed.

Lemma fill_appr : forall e1 e2,
  (e_app e1 e2) = (fill (appCtxR e1) e2).
Proof.
  intros. eauto.
Qed.

Lemma fill_mergel : forall e1 e2,
  (e_merge e1 e2) = (fill (mergeCtxL e2) e1).
Proof.
  intros. eauto.
Qed.


Lemma fill_merger : forall e1 e2,
  (e_merge e1 e2) = (fill (mergeCtxR e1) e2).
Proof.
  intros. eauto.
Qed.



Lemma fill_rcd : forall l e,
  (e_rcd l e) = (fill (rcdCtx l) e).
Proof.
  intros. eauto.
Qed.


Lemma fill_proj : forall l e,
  (e_proj e l) = (fill (prjCtx l) e).
Proof.
  intros. eauto.
Qed.


Lemma fill_anno : forall A e,
  (e_anno e A) = (fill (annoCtx A) e).
Proof.
  intros. eauto.
Qed.



Lemma Cast_rcd_prv: forall v l A v',
 Cast v (t_rcd l A) (r_e v') ->
 exists v1, v' = (e_rcd l v1).
Proof.
  introv Red.
  inductions Red; eauto.
  inverts* H0.
Qed.



Lemma value_cast_arr: forall v v' A B,
 value v ->
 Cast v (t_arrow A B) (r_e v') ->
 exists v'', v' = (e_anno v'' (t_arrow A B)).
Proof.
  introv val cas.
  inductions cas; simpl in *;try solve[inverts val as h1; inverts* h1]; eauto.
  -
    inverts* H0;
    try solve[inverts val as h1; inverts* h1].
Qed.



Theorem progress_dir : forall e dir A,
    Typing nil e dir A ->
    value e \/ (exists r, step e r) \/ (exists e', e  = (e_abs e') \/ (exists e', e  = (e_fixpoint e'))).
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
      inverts H.
      *
        inverts Val1 as h1;inverts Typ1 as h2; inverts h1.
        --
        left*.
        --
        left*.
      *
        assert(dmatch t_dyn (t_arrow t_dyn t_dyn)); auto.
        assert(exists e1', e1 = (e_anno e1' t_dyn)) as h1.
        inverts Val1 as h2; inverts Typ1;try solve[inverts* h2]; eauto.
        inverts h1.
        assert(value x) as h3.
        inverts Val1 as h4; try solve[inverts h4]; eauto.
        forwards* : gvalue_value h4.
        inverts Typ1 as h5.
        eauto.
    + 
      left.
      forwards* h1: lambda_decidable e1.
      inverts h1 as h1.
      inverts h1 as h1; try solve[inverts Val1 as h0;inverts h0].
      inverts Val1; try solve[
        inverts Typ1; inverts H
      ].
      *
        inverts* H0.
      *
        eauto.
    +
      left.
      forwards* h1: lambda_decidable e1.
      inverts h1 as h1.
      inverts h1 as h1; try solve[inverts Val1 as h0;inverts h0].
      inverts Val1; try solve[
        inverts Typ1; inverts H
      ].
      *
        inverts* H0.
      *
        eauto.
    +
      left. 
      rewrite fill_appl.   destruct e1'. exists.
      apply step_eval; eauto. exists. apply step_blame; eauto.
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
      rewrite fill_merger.  destruct e2'. exists.
      apply step_eval; eauto. exists. apply step_blame; eauto.
    +
      inverts abs2 as abs2.
      inverts abs2 as abs2;
      try solve[
      inverts Typ2];
      try solve[inverts abs2; inverts Typ2].
    + right. left.
      rewrite fill_mergel.  destruct e1'. exists.
      apply step_eval; eauto. exists. apply step_blame; eauto.
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
      forwards* h0: value_decidable (e_anno e A).
      inverts* h0.
      forwards* h1: Typing_well Typ.
      forwards* h2: Cast_progress A Typ.
      inverts h2 as h2; eauto.
      assert(NotVal (e_anno e A)) as hh0.
      unfold NotVal; splits*.
      unfold not;intros nt.
      lets(g&hh1&hh2): nt.
      inverts* hh2.
      right. left. exists*.
    + 
      right. left. rewrite fill_anno.  destruct e1'. exists.
      apply step_eval; eauto. exists. apply step_blame; eauto.
    +
      inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ as h1 h2 h3;
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
      forwards* h4: Cast_progress e (t_rcd l B).
      inverts h4 as h4.
      destruct x; eauto. 
      forwards* h5: Cast_rcd_prv h4.
      lets(vv1&h6): h5.
      inverts* h6.
    +
      right.
      left.
      rewrite fill_proj.  destruct e1'. exists.
      apply step_eval; eauto. exists. apply step_blame; eauto.
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
      rewrite fill_rcd.  destruct e1'. exists.
      apply step_eval; eauto. exists. apply step_blame; eauto.
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
      rewrite fill_appr.   destruct e1'. exists.
      apply step_eval; eauto. exists. apply step_blame; eauto.
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
  forwards* h1: Typing_Chk Typ.
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
  (e_app e1 e2) = (filln (nappCtxL e2) e1).
Proof.
  intros. eauto.
Qed.


Lemma filln_mergel : forall e1 e2,
  (e_merge e1 e2) = (filln (nmergeCtxL e2) e1).
Proof.
  intros. eauto.
Qed.


Lemma filln_merger : forall e1 e2,
  (e_merge e1 e2) = (filln (nmergeCtxR e1) e2).
Proof.
  intros. eauto.
Qed.



Lemma filln_rcd : forall l e,
  (e_rcd l e) = (filln (nrcdCtx l) e).
Proof.
  intros. eauto.
Qed.


Lemma filln_proj : forall l e,
  (e_proj e l) = (filln (nprjCtx l) e).
Proof.
  intros. eauto.
Qed.


Lemma filln_anno : forall A e,
  (e_anno e A) = (filln (nannoCtx A) e).
Proof.
  intros. eauto.
Qed.




Theorem progress_dir_cbn : forall e dir A,
    Typing nil e dir A ->
    value e \/ (exists r, cbn e r) \/  (exists e', e  = (e_abs e') \/ (exists e', e  = (e_fixpoint e'))).
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
      inverts H.
      *
        inverts Val1 as h1;inverts Typ1 as h2; inverts h1.
        --
        left*.
        --
        left*.
      *
        assert(dmatch t_dyn (t_arrow t_dyn t_dyn)); auto.
        assert(exists e1', e1 = (e_anno e1' t_dyn)) as h1.
        inverts Val1 as h2; inverts Typ1;try solve[inverts* h2]; eauto.
        inverts h1.
        assert(value x) as h3.
        inverts Val1 as h4; try solve[inverts h4]; eauto.
        forwards* : gvalue_value h4.
        inverts Typ1 as h5.
        eauto.
    + 
      left.
      forwards* h1: lambda_decidable e1.
      inverts h1 as h1.
      inverts h1 as h1; try solve[inverts Val1 as h0;inverts h0].
      inverts Val1; try solve[
        inverts Typ1; inverts H
      ].
      *
        inverts* H0.
      *
        eauto.
    +
      left.
      forwards* h1: lambda_decidable e1.
      inverts h1 as h1.
      inverts h1 as h1; try solve[inverts Val1 as h0;inverts h0].
      inverts Val1; try solve[
        inverts Typ1; inverts H
      ].
      *
        inverts* H0.
      *
        eauto.
    +
      left. 
      rewrite filln_appl.   destruct e1'. exists.
      apply cbn_eval; eauto. exists. apply cbn_blame; eauto.
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
      rewrite filln_merger.  destruct e2'. exists.
      apply cbn_eval; eauto. exists. apply cbn_blame; eauto.
    +
      inverts abs2 as abs2.
      inverts abs2 as abs2;
      try solve[
      inverts Typ2];
      try solve[inverts abs2; inverts Typ2].
    + right. left.
      rewrite filln_mergel.  destruct e1'. exists.
      apply cbn_eval; eauto. exists. apply cbn_blame; eauto.
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
      forwards* h0: value_decidable (e_anno e A).
      inverts* h0.
      forwards* h1: Typing_well Typ.
      forwards* h2: Cast_progress A Typ.
      inverts h2 as h2; eauto.
      assert(NotVal (e_anno e A)) as hh0.
      unfold NotVal; splits*.
      unfold not;intros nt.
      lets(g&hh1&hh2): nt.
      inverts* hh2.
      right. left. exists*.
    + 
      right. left. rewrite filln_anno.  destruct e1'. exists.
      apply cbn_eval; eauto. exists. apply cbn_blame; eauto.
    +
      inverts abs1 as abs1.
      inverts abs1 as abs1;
      try solve[
      inverts Typ as h1 h2 h3;
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
      forwards* h4: Cast_progress e (t_rcd l B).
      inverts h4 as h4.
      destruct x; eauto. 
      forwards* h5: Cast_rcd_prv h4.
      lets(vv1&h6): h5.
      inverts* h6.
    +
      right.
      left.
      rewrite filln_proj.  destruct e1'. exists.
      apply cbn_eval; eauto. exists. apply cbn_blame; eauto.
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
      rewrite filln_rcd.  destruct e1'. exists.
      apply cbn_eval; eauto. exists. apply cbn_blame; eauto.
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
    value e \/ exists r, cbn e r.
Proof. 
  introv Typ.
  forwards* h1: Typing_Chk Typ.
  forwards* h2:progress_dir_cbn h1.
  inverts h2 as h2; eauto.
  inverts h2 as h2; eauto.
  inverts h2 as h2; eauto.
  inverts h2 as h2; eauto.
  inverts Typ.
  inverts h2 as h2; eauto.
  inverts Typ.
Qed.

(* examples*)

Lemma example_1: 
 steps (e_app (e_anno (e_merge (e_anno (e_lit 1) t_dyn) (e_anno (e_anno (e_abs (e_anno (e_var_b 0) t_int)) (t_arrow t_dyn t_dyn)) t_dyn)) t_dyn) (e_merge (e_lit 1) (e_top)))  (r_e (e_anno (e_lit 1) t_dyn)).
Proof.
  introv.
  assert(lc_exp (e_abs (e_anno (e_var_b 0) t_int))) as h0.
  apply lc_e_abs;intros;eauto.
  unfold open_exp_wrt_exp; simpl; eauto.

  eapply step_n.
  apply Step_dyn.
  eapply val_g.
  apply gval_merge; eauto.


  eapply step_n.
  rewrite fill_appl.
  apply step_eval; eauto.
  apply Step_annov; eauto.
  apply cast_dyna; eauto.
  eapply cast_merge.
  auto.
  apply cast_dyna; eauto.
  apply cast_blame; simpl; eauto.
  unfold not;intros nt;inverts nt.
  apply cast_dyna; eauto.
  eauto.
  unfold NotVal; splits*.
  unfold not; intros nt;inverts nt as nt;inverts nt.
  unfold not; intros nt;inverts nt as nt;inverts nt as nt1 nt2.
  inverts* nt2.

  simpl.
  eapply step_n.
  apply Step_app.
  apply fval_vabs; eauto.
  
  eapply step_n.
  rewrite fill_anno.
  apply step_eval.
  auto.
  apply Step_app.
  apply fval_abs; eauto.

  eapply step_n.
  rewrite fill_anno.
  apply step_eval; auto.
  apply step_eval; auto.
  rewrite fill_appr.
  apply step_eval; eauto.
  rewrite fill_anno.
  apply step_eval; auto.
  apply Step_annov; eauto.
  unfold NotVal; splits*.
  unfold not; intros nt;inverts nt as nt;inverts nt.
  unfold not; intros nt;inverts nt as nt;inverts nt as nt1 nt2.
  inverts* nt2. inverts* nt1.
  
  simpl.
  eapply step_n.
  rewrite fill_anno.
  rewrite fill_anno.
  rewrite fill_appr.
  apply step_eval; auto.
  apply step_eval; auto.
  apply step_eval; auto.
  apply Step_annov; eauto.
  unfold NotVal; splits*.
  unfold not; intros nt;inverts nt as nt;inverts nt.
  unfold not; intros nt;inverts nt as nt;inverts nt as nt1 nt2.
  inverts* nt2. inverts* nt1.
  
  simpl.
  eapply step_n.
  rewrite fill_anno.
  rewrite fill_anno.
  apply step_eval; auto.
  unfold open_exp_wrt_exp; simpl.

  eapply step_n.
  rewrite fill_anno.
  rewrite fill_anno.
  apply step_eval; auto.
  apply step_eval; auto.
  apply Step_annov; eauto.
  apply cast_dyna; eauto.
  eapply cast_merge.
  auto.
  apply cast_dyna; eauto.
  apply cast_dyna; eauto.
  apply cast_blame; simpl; eauto.
  unfold not;intros nt;inverts nt.
  eauto.
  unfold NotVal; splits*.
  unfold not; intros nt;inverts nt as nt;inverts nt.
  unfold not; intros nt;inverts nt as nt;inverts nt as nt1 nt2.
  inverts* nt2.

  simpl.
  eapply step_n.
  apply Step_annov; eauto.
  unfold NotVal; splits*.
  unfold not; intros nt;inverts nt as nt;inverts nt.
  unfold not; intros nt;inverts nt as nt;inverts nt as nt1 nt2.
  inverts* nt2.
  inverts* nt1.
  apply step_refl.
Qed.
