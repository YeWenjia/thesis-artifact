Require Import Bool.
Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import List.
Require Import syntax_ott.
Require Import rules_inf.
Require Import syntaxb_ott.
Require Import syntaxl_ott.
Require Import rulesl_inf.
Require Import Infrastructure.
Require Import Typing.
Require Import Lia.


Lemma TTyping_regular_1 : forall e G dir A,
    TTyping G e dir A -> lc_eexp e.
Proof.
  intros e G dir A H.
  induction H;
    eauto.
Qed.

Lemma erase_subst: forall e1 e2 x y,
 erase e1 e2 ->
 erase (subst_eexp (ee_var_f y) x e1) (subst_exp (e_var_f y) x e2).
Proof.
  introv ed.
  inductions ed; simpl in *; eauto.
  -
    destruct(x0 == x); try solve[inverts* e];eauto.
  -
    apply er_abs with (L := union L
    (union (singleton x)
       (union (singleton y)
          (union (singleton l)
             (union (fv_exp e') (fv_eexp e))))));intros.
    forwards* h1: H0 x0.
    rewrite subst_eexp_open_eexp_wrt_eexp_var; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; eauto.
Qed.



Lemma erase_exists: forall e,
 lc_eexp e ->
 exists e', erase e e'.
Proof.
  introv wf. 
  inductions wf; intros;try solve[exists*];
  try solve[inverts* IHwf];
  try solve[inverts IHwf1; inverts* IHwf2];eauto.
  -
    pick fresh x.
    forwards* h1:H0 x.
    inverts h1 as h1.
    exists (e_abs t1 (close_exp_wrt_exp x x0) t2).
    pick fresh y and apply er_abs.
   forwards* h2:  erase_subst x y h1. 
   rewrite subst_exp_spec in h2.
   rewrite (@subst_eexp_intro x); auto.
Qed.



Lemma erase_exists_r: forall e,
 lc_exp e ->
 exists e', erase e' e.
Proof.
  introv wf. 
  inductions wf; intros;try solve[exists*];
  try solve[inverts* IHwf];
  try solve[inverts IHwf1; inverts* IHwf2];eauto.
  -
    pick fresh x.
    forwards* h1:H0 x.
    inverts h1 as h1.
    pick fresh l.
    exists (ee_abs t1 (close_eexp_wrt_eexp x x0) l true t2).
    pick fresh y and apply er_abs.
   forwards* h2:  erase_subst x y h1. 
   rewrite subst_eexp_spec in h2.
   rewrite (@subst_exp_intro x); auto.
   Unshelve.
   pick fresh l.
   apply l.
   apply true.
   pick fresh l.
   apply l.
   apply true.
   pick fresh l.
   apply l.
   apply true.
   pick fresh l.
   apply l.
   apply true.
Qed.




Theorem bgl_to_bg_typing_aux: forall G e e' dir A, 
 TTyping G e dir A ->
 erase e e' ->
 Typing G e' dir A.
Proof.
 introv typ er. gen G A dir.
 inductions er; intros;try solve[inverts typ as h1 h2 h3; try solve[inverts* h1]; try solve[inverts h1 as h1; inverts h1]].
 -
    inverts typ as h1 h2.
    +
    pick fresh x and apply Typ_abs.
    forwards* h3: H0 x.
    +
    inverts h1 as h1.
    eapply Typ_sim.
    pick fresh x and apply Typ_abs.
    forwards* h3: H0 x.
    auto.
Qed.



Theorem bg_to_bgl_typing_aux: forall G e e' dir A, 
 Typing G e dir A ->
  erase e' e ->
  TTyping G e' dir A.
Proof.
  introv typ er. gen G A dir.
  inductions er; intros;try solve[inverts typ as h1 h2 h3; try solve[inverts* h1]; try solve[inverts h1 as h1; inverts h1]].
  -
    inverts typ as h1 h2.
    +
    pick fresh x and apply TTyp_abs.
    forwards* h3: H0 x.
    +
    inverts h1 as h1.
    eapply TTyp_sim.
    pick fresh x and apply TTyp_abs.
    forwards* h3: H0 x.
    auto.
Qed.

Theorem bg_to_bgl_typing: forall G e dir A, 
 Typing G e dir A ->
 exists e', erase e' e /\
 TTyping G e' dir A.
Proof.
  introv typ.
  forwards* h3: Typing_regular_1 typ.
  forwards* h2: erase_exists_r h3.
  inverts h2 as h2.
  forwards* h1:bg_to_bgl_typing_aux typ.
Qed.


Theorem bgl_to_bg_typing: forall G e dir A, 
 TTyping G e dir A ->
 exists e', erase e e' /\
 Typing G e' dir A.
Proof.
 introv typ.
 forwards* h3: TTyping_regular_1 typ.
 forwards* h2: erase_exists h3.
  inverts h2 as h2.
 forwards* h1:bgl_to_bg_typing_aux typ.
Qed.



Lemma erase_lc1: forall v1 v2,
 erase v2 v1 ->
 lc_eexp v2.
Proof.
  introv er.
  inductions er;eauto.
Qed.

Lemma erase_lc2: forall v1 v2,
 erase v2 v1 ->
 lc_exp v1.
Proof.
  introv er.
  inductions er;eauto.
Qed.


Lemma erase_subst2: forall e1 e2 x y1 y2,
 erase e1 e2 ->
 erase y1 y2 ->
 erase (subst_eexp y1 x e1) (subst_exp y2 x e2).
Proof.
  introv ed ed2.
  inductions ed; simpl in *; eauto.
  -
    destruct(x0 == x); try solve[inverts* e];eauto.
  -
    forwards* h1: erase_lc1 ed2.
    forwards* h2: erase_lc2 ed2.
    pick fresh xx and apply er_abs; eauto.
    forwards* h3: H0 xx.
    rewrite subst_eexp_open_eexp_wrt_eexp_var; eauto.
    rewrite subst_exp_open_exp_wrt_exp_var; eauto.
Qed.


Lemma erase_dtyp: forall v1 v2,
 erase v1 v2 ->
 pdynamic_type v1 = dynamic_type v2.
Proof.
  introv er.
  inductions er; simpl in *; eauto.
  rewrite IHer1.
  rewrite IHer2.
  auto.
Qed.


Lemma erase_value2: forall v1 v2,
 value v1 ->
 erase v2 v1 ->
 evalue v2.
Proof.
  introv val er.
  lets er': er.
  inductions er; try solve[inverts* val];eauto.
  -
    inverts val as h1 h2; eauto.
    +
    forwards* h3: erase_dtyp er.
    rewrite <- h3 in *.
    eauto.
    +
    forwards* h3: erase_dtyp er.
    rewrite <- h3 in *.
    eauto.
  -
    forwards*: erase_lc1 er'.   
Qed.


Lemma erase_value: forall v1 v2,
 evalue v2 ->
 erase v2 v1 ->
 value v1.
Proof.
  introv val er.
  lets er': er.
  inductions er; try solve[inverts* val];eauto.
  -
    inverts val as h1 h2; eauto.
    +
    forwards* h3: erase_dtyp er.
    rewrite h3 in *.
    eauto.
    +
    forwards* h3: erase_dtyp er.
    rewrite h3 in *.
    eauto.
  -
    forwards*: erase_lc2 er'.   
Qed.


Theorem bgl_to_bg_casting: forall e e2 r A l b, 
 CCast e l b A r ->
 erase e e2 ->
 exists r2, Cast e2 A r2 /\ eraser r r2.
Proof.
  introv red er. gen e2.
  inductions red; intros;simpl in *; 
  try solve[inverts* er];eauto;
  try solve[forwards* h1: erase_dtyp er;rewrite h1 in *; exists*];
  try solve[forwards* h1: erase_lc2 er; inverts* er; try solve[inverts* h1;exists*]];
  try solve[inverts er as h1;
  forwards* h2: erase_dtyp h1;rewrite h2 in *;
  exists*].
  -
    forwards* h1: erase_dtyp er;rewrite h1 in *.
    forwards* h2: IHred er.
    lets(rr&h3&h4):h2.
    inverts h4 as h4.
    exists*.
  -
    inverts er as h1 h2.
    forwards* h3: IHred.
    lets(rr&hh3&hh4):h3.
    exists*.
  -
    inverts er as h1 h2.
    forwards* h3: IHred1 h1.
    forwards* h4: IHred2 h2.
    lets(rr1&hh3&hh4):h3.
    lets(rr2&hh5&hh6):h4.
    inverts hh4 as hh4.
    inverts hh6 as hh6.
    exists*.
  -
    inverts er as h1 h2.
    forwards* h3: IHred1 h1.
    forwards* h4: IHred2 h2.
    lets(rr1&hh3&hh4):h3.
    lets(rr2&hh5&hh6):h4.
    inverts hh4 as hh4.
    exists*.
  -
    inverts er as h1 h2.
    forwards* h3: IHred1 h1.
    forwards* h4: IHred2 h2.
    lets(rr1&hh3&hh4):h3.
    lets(rr2&hh5&hh6):h4.
    inverts hh4 as hh4.
    inverts hh6 as hh6.
    exists*.
Qed.

Lemma cast_label: forall v A l b l2 b2,
    CCast v l b A (ee_blame l2 b2) ->
    l = l2 /\ b = b2.
Proof.
   introv red.
   inductions red; try solve[unfold not; intros nt;inverts nt];
   try solve[inverts* val];eauto;
   try solve[exfalso; apply H; auto].
Qed.



Theorem bg_to_bgl_casting: forall  l b e e2 r A, 
 Cast e A r ->
 erase e2 e ->
 exists r2, CCast e2 l b A r2 /\ eraser r2 r.
Proof.
  introv red er. gen e2 l b.
  inductions red; intros;simpl in *; 
  try solve[inverts* er];eauto;
  try solve[forwards* h1: erase_dtyp er;rewrite <- h1 in *; exists*];
  try solve[forwards* h1: erase_lc1 er; inverts* er; try solve[inverts* h1;exists*]];
  try solve[inverts er as h1;
  forwards* h2: erase_dtyp h1;rewrite <- h2 in *;
  exists*].
  -
    forwards* h1: erase_dtyp er;rewrite <- h1 in *.
    forwards* h2: IHred er.
    lets(rr&h3&h4):h2.
    inverts h4 as h4.
    exists*.
  -
    inverts er as h1 h2.
    forwards* h3: IHred.
    lets(rr&hh3&hh4):h3.
    exists*.
  -
    inverts er as h1 h2.
    forwards* h3: IHred1 h1.
    forwards* h4: IHred2 h2.
    lets(rr1&hh3&hh4):h3.
    lets(rr2&hh5&hh6):h4.
    inverts hh4 as hh4.
    inverts hh6 as hh6.
    exists*.
  -
    inverts er as h1 h2.
    forwards* h3: IHred1 h1 l b.
    forwards* h4: IHred2 h2 l b.
    lets(rr1&hh3&hh4):h3.
    lets(rr2&hh5&hh6):h4.
    inverts hh4 as hh4.
    forwards* hh7: cast_label hh3.
    inverts hh7 as hh7.
    exists*.
  -
    inverts er as h1 h2.
    forwards* h3: IHred1 h1 l b.
    forwards* h4: IHred2 h2 l b.
    lets(rr1&hh3&hh4):h3.
    lets(rr2&hh5&hh6):h4.
    inverts hh4 as hh4.
    inverts hh6 as hh6.
    forwards* hh7: cast_label hh5.
    inverts hh7 as hh7.
    exists*.
Qed.


Theorem bgl_to_bg_aux: forall e e2 r, 
 sstep e r ->
 erase e e2 ->
 exists r2, step e2 r2 /\ eraser r r2.
Proof.
   introv red er.
   lets err: er. gen r.
   inductions er; intros;simpl in *; try solve[inverts* red];
   try solve[forwards*: sstep_not_evalue red];
   try solve[forwards*: erase_lc1 err; forwards*: sstep_not_evalue red];eauto.
   -
     inverts red as h1 h2 h3; eauto;
     try solve[destruct E; unfold ffill in *;inverts h3].
   -
     inverts red as h1 h2 h3; eauto;
     try solve[destruct E; unfold ffill in *;inverts h3].
     +
        destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
        try solve[inverts* h1;forwards*: sstep_not_evalue h2];eauto.
        assert(fill ((annoCtx A)) (e') = e_anno (e') A) as h01; eauto.
        rewrite <- h01.
        forwards* h4: IHer er.
        lets(ee3&h5&h6):h4.
        inverts h6 as h6.
        exists. split.
        apply Step_eval; auto.
        apply h5.
        simpl; auto.
      +
        destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
        try solve[inverts* h1;forwards*: sstep_not_evalue h2];eauto.
        assert(fill ((annoCtx A)) (e') = e_anno (e') A) as h01; eauto.
        rewrite <- h01.
        forwards* h4: IHer er.
        lets(ee3&h5&h6):h4.
        inverts h6 as h6.
        exists. split.
        apply Step_blame; auto.
        simpl; auto.
      +
        forwards* h5: erase_value er.
        forwards* h4: bgl_to_bg_casting  h2.
        lets(ee3&h6&h7):h4.
        assert(not(value (e_anno e' A))) as hh8.
        unfold not;intros nt.
        forwards* hh9: erase_value2 nt.
        exists*.
   -
     forwards* hh1: erase_lc2 er2.
     inverts red as h1 h2 h3; eauto;
     try solve[].
     +
        destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
        try solve[inverts* h1;forwards*: sstep_not_evalue h2];eauto.
        *
          assert(fill ((appCtxL (e2'))) (e1') = e_app (e1') (e2')) as h01; eauto.
          rewrite <- h01.
          forwards* h4: IHer1 er1.
          lets(ee3&h5&h6):h4.
          inverts h6 as h6.
          exists. split.
          apply Step_eval; auto.
          apply h5.
          simpl; auto.
        *
          inverts h1 as h1 h4.
          forwards* h5: erase_value h4.
          forwards* h6:erase_dtyp er1.
          rewrite h6 in *.
          forwards* h7:IHer2 er2.
          lets(ee3&hh5&hh6):h7.
          inverts hh6 as hh6.
          assert(fill ((appCtxR (e1'))) (e2') = e_app e1' (e2')) as h01; eauto.
          rewrite <- h01.
          exists. split.
          apply Step_eval; auto.
          eauto.
          apply hh5.
          simpl; auto.
     +
      destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
      try solve[inverts* h1;forwards*: sstep_not_evalue h2];eauto.
      *
        assert(fill ((appCtxL (e2'))) (e1') = e_app (e1') (e2')) as h01; eauto.
        rewrite <- h01.
        forwards* h4: IHer1 er1.
        lets(ee3&h5&h6):h4.
        inverts h6 as h6.
        exists. split.
        apply Step_blame; auto.
        simpl; auto.
      *
        inverts h1 as h1 h4.
        forwards* h5: erase_value h4.
        forwards* h6:erase_dtyp er1.
        rewrite h6 in *.
        forwards* h7:IHer2 er2.
        lets(ee3&hh5&hh6):h7.
        inverts hh6 as hh6.
        assert(fill ((appCtxR (e1'))) (e2') = e_app e1' (e2')) as h01; eauto.
        rewrite <- h01.
        exists. split.
        apply Step_blame; auto.
        eauto.
        simpl; auto.
     +
       forwards* h4:erase_lc2 er1.
       inverts er1 as er1.
       forwards* h5:erase_value h2.
      forwards* hy4: bgl_to_bg_casting  h3.
      lets(ee3&hy6&hy7):hy4.
      inverts hy7 as hy7.
      pick fresh y.
      rewrite (@subst_eexp_intro y); eauto.
      forwards* hy8: er1 y.
      forwards*: erase_subst2 hy8 hy7.
      exists.
      splits*.
      rewrite (@subst_exp_intro y); eauto.
     +
       
       forwards* h4:erase_dtyp er1.
       forwards* h5:erase_value h2.
       forwards* h6:erase_value h3.
       rewrite h4 in *.
       forwards* hy4: bgl_to_bg_casting H7.
       lets(ee3&hy6&hy7):hy4.
       inverts hy7 as hy7.
       exists*.
     +
       forwards* h4:erase_dtyp er1.
       forwards* h5:erase_value h3.
       inverts er1 as er1.
       forwards* h6:erase_value h2.
       simpl in *.
       forwards* h7:erase_dtyp er1.
       rewrite h7 in *.
       forwards* hy4: bgl_to_bg_casting  H7.
       lets(ee3&hy6&hy7):hy4.
       inverts hy7 as hy7.
       exists*.
     +
       forwards* h4: erase_value er1.
       inverts er1 as er1; eauto.
       exists.
       splits*.
     +
       inverts er1 as er1.
       forwards* h4: erase_value er2.
       forwards* hy4: bgl_to_bg_casting  h2.
       lets(ee3&hy6&hy7):hy4.
       inverts hy7 as hy7.
       inverts hy7 as hy7.
       exists*.
     +
       inverts er1 as er1.
       forwards* h4: erase_value er2.
       forwards* hy4: bgl_to_bg_casting  h2.
       lets(ee3&hy6&hy7):hy4.
       inverts hy7 as hy7.
       inverts hy7 as hy7.
       exists*.
   -
      forwards* hh1: erase_lc2 er2.
      inverts red as h1 h2 h3; eauto;
      try solve[].
      +
          destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
          try solve[inverts* h1;forwards*: sstep_not_evalue h2];eauto.
          *
            assert(fill ((proCtxL (e2'))) (e1') = e_pro (e1') (e2')) as h01; eauto.
            rewrite <- h01.
            forwards* h4: IHer1 er1.
            lets(ee3&h5&h6):h4.
            inverts h6 as h6.
            exists. split.
            apply Step_eval; auto.
            apply h5.
            simpl; auto.
          *
            inverts h1 as h1 h4.
            forwards* h5: erase_value h1.
            forwards* h7:IHer2 er2.
            lets(ee3&hh5&hh6):h7.
            inverts hh6 as hh6.
            assert(fill ((proCtxR (e1'))) (e2') = e_pro e1' (e2')) as h01; eauto.
            rewrite <- h01.
            exists. split.
            apply Step_eval; auto.
            eauto.
            simpl; auto.
      +
        destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
        try solve[inverts* h1;forwards*: sstep_not_evalue h2];eauto.
        *
          assert(fill ((proCtxL (e2'))) (e1') = e_pro (e1') (e2')) as h01; eauto.
          rewrite <- h01.
          forwards* h4: IHer1 er1.
          lets(ee3&h5&h6):h4.
          inverts h6 as h6.
          exists. split.
          apply Step_blame; auto.
          simpl; auto.
        *
          inverts h1 as h1 h4.
          forwards* h5: erase_value h1.
          forwards* h7:IHer2 er2.
          lets(ee3&hh5&hh6):h7.
          inverts hh6 as hh6.
          assert(fill ((proCtxR (e1'))) (e2') = e_pro e1' (e2')) as h01; eauto.
          rewrite <- h01.
          exists. split.
          apply Step_blame; auto.
          eauto.
   -
     inverts red as h1 h2 h3; eauto;
     try solve[].
     +
        destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
        try solve[inverts* h1;forwards*: sstep_not_evalue h2];eauto.
        assert(fill ((lCtx)) (e1') = e_l (e1')) as h01; eauto.
        rewrite <- h01.
        forwards* h4: IHer er.
        lets(ee3&h5&h6):h4.
        inverts h6 as h6.
        exists. split.
        apply Step_eval; auto.
        apply h5.
        simpl; auto.
      +
        destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
        try solve[inverts* h1;forwards*: sstep_not_evalue h2];eauto.
        assert(fill ((lCtx)) (e1') = e_l (e1')) as h01; eauto.
        rewrite <- h01.
        forwards* h4: IHer er.
        lets(ee3&h5&h6):h4.
        inverts h6 as h6.
        exists. split.
        apply Step_blame; auto.
        simpl; auto.
      +
        forwards* h5: erase_value h1.
        inverts er as er; eauto.
        exists*.
      +
         inverts er as er1 er2; eauto.
        forwards* h5: erase_value er1.
        forwards* h6: erase_value er2.
   -
     inverts red as h1 h2 h3; eauto;
     try solve[].
     +
        destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
        try solve[inverts* h1;forwards*: sstep_not_evalue h2];eauto.
        assert(fill ((rCtx)) (e1') = e_r (e1')) as h01; eauto.
        rewrite <- h01.
        forwards* h4: IHer er.
        lets(ee3&h5&h6):h4.
        inverts h6 as h6.
        exists. split.
        apply Step_eval; auto.
        apply h5.
        simpl; auto.
      +
        destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
        try solve[inverts* h1;forwards*: sstep_not_evalue h2];eauto.
        assert(fill ((rCtx)) (e1') = e_r (e1')) as h01; eauto.
        rewrite <- h01.
        forwards* h4: IHer er.
        lets(ee3&h5&h6):h4.
        inverts h6 as h6.
        exists. split.
        apply Step_blame; auto.
        simpl; auto.
     +
       forwards* h5: erase_value h1.
       inverts er as er; eauto.
       exists*.
     +
        inverts er as er1 er2; eauto.
       forwards* h5: erase_value er1.
       forwards* h6: erase_value er2.
Qed.





Theorem bg_to_bgl_aux: forall e e2 r, 
 step e r ->
 erase e2 e ->
 exists r2, sstep e2 r2 /\ eraser r2 r.
Proof.
introv red er.
lets err: er. gen r.
inductions er; intros;simpl in *; try solve[inverts* red];
try solve[forwards*: step_not_value red];
try solve[forwards*: erase_lc2 err; forwards*: step_not_value red];eauto.
-
  inverts red as h1 h2 h3; eauto;
  try solve[destruct E; unfold fill in *;inverts h3].
-
  inverts red as h1 h2 h3; eauto;
  try solve[destruct E; unfold fill in *;inverts h3].
  +
     destruct E; unfold fill in *; simpl in *; inverts h3 as h3;
     try solve[inverts* h1;forwards*: step_not_value h2];eauto.
     assert(ffill ((eannoCtx p b A)) (e) = ee_anno (e) p b A) as h01; eauto.
     rewrite <- h01.
     forwards* h4: IHer er.
     lets(ee3&h5&h6):h4.
     inverts h6 as h6.
     exists. split.
     apply sStep_eval; auto.
     apply h5.
     simpl; auto.
   +
     destruct E; unfold fill in *; simpl in *; inverts h3 as h3;
     try solve[inverts* h1;forwards*: step_not_value h2];eauto.
     assert(ffill ((eannoCtx p b A)) (e) = ee_anno (e) p b A) as h01; eauto.
     rewrite <- h01.
     forwards* h4: IHer er.
     lets(ee3&h5&h6):h4.
     inverts h6 as h6.
     exists. split.
     apply sStep_blame; auto.
     apply h5.
     simpl; auto.
   +
     forwards* h5: erase_value2 er.
     forwards* h4: bg_to_bgl_casting p b h2.
     lets(ee3&h6&h7):h4.
     assert(not(evalue (ee_anno e p b A))) as hh8.
     unfold not;intros nt.
     forwards* hh9: erase_value nt.
     exists*.
-
  forwards* hh1: erase_lc1 er2.
  inverts red as h1 h2 h3; eauto;
  try solve[].
  +
     destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
     try solve[inverts* h1;forwards*: step_not_value h2];eauto.
     *
       assert(ffill ((eappCtxL (e2) p b)) (e1) = ee_app (e1) p b (e2)) as h01; eauto.
       rewrite <- h01.
       forwards* h4: IHer1 er1.
       lets(ee3&h5&h6):h4.
       inverts h6 as h6.
       exists. split.
       apply sStep_eval; auto.
       eauto.
       simpl; auto.
     *
       inverts h1 as h1 h4.
       forwards* h5: erase_value2 h4.
       forwards* h6:erase_dtyp er1.
       rewrite <- h6 in *.
       forwards* h7:IHer2 er2.
       lets(ee3&hh5&hh6):h7.
       inverts hh6 as hh6.
       assert(ffill ((eappCtxR (e1) p b)) (e2) = ee_app e1 p b (e2)) as h01; eauto.
       rewrite <- h01.
       exists. split.
       apply sStep_eval; auto.
       eauto.
       apply hh5.
       simpl; auto.
  +
   destruct E; unfold fill in *; simpl in *; inverts h3 as h3;
   try solve[inverts* h1;forwards*: step_not_value h2];eauto.
   *
     assert(ffill ((eappCtxL (e2) p b)) (e1) = ee_app (e1) p b (e2)) as h01; eauto.
     rewrite <- h01.
     forwards* h4: IHer1 er1.
     lets(ee3&h5&h6):h4.
     inverts h6 as h6.
     exists. split.
     apply sStep_blame; auto.
     apply h5.
     simpl; auto.
   *
     inverts h1 as h1 h4.
     forwards* h5: erase_value2 h4.
     forwards* h6:erase_dtyp er1.
     rewrite <- h6 in *.
     forwards* h7:IHer2 er2.
     lets(ee3&hh5&hh6):h7.
     inverts hh6 as hh6.
     assert(ffill ((eappCtxR (e1) p b)) (e2) = ee_app e1 p b (e2)) as h01; eauto.
     rewrite <- h01.
     exists. split.
     apply sStep_blame; auto.
     eauto.
     apply hh5.
     simpl; auto.
  +
    forwards* h4:erase_lc1 er1.
    inverts er1 as er1.
    forwards* h5:erase_value2 h2.

    forwards* hy4: bg_to_bgl_casting p b h3.
    lets(ee3&hy6&hy7):hy4.
    inverts hy7 as hy7.
    pick fresh y.
    rewrite (@subst_exp_intro y); eauto.
    forwards* hy8: er1 y.
    forwards*: erase_subst2 hy8 hy7.
    exists.
    splits*.
    rewrite (@subst_eexp_intro y); eauto.
  + 
    forwards* h4:erase_dtyp er1.
    forwards* h5:erase_value2 h1.
    forwards* h6:erase_value2 H5.
    rewrite <- h4 in *.
    forwards* hy4: bg_to_bgl_casting p b h3.
    lets(ee3&hy6&hy7):hy4.
    inverts hy7 as hy7.
    forwards* hy8: cast_label hy6.
    inverts* hy8.
  +
    inverts er1 as er1.
    forwards* h4: erase_value2 er2.
    forwards* hy4: bg_to_bgl_casting p b h2.
    lets(ee3&hy6&hy7):hy4.
    inverts hy7 as hy7.
    inverts hy7 as hy7.
    exists*.
  +
    inverts er1 as er1.
    forwards* h4: erase_value2 er2.
    forwards* hy4: bg_to_bgl_casting  h2.
    lets(ee3&hy6&hy7):hy4.
    inverts hy7 as hy7.
    inverts hy7 as hy7.
    exists*.
  +
    forwards* h4:erase_dtyp er1.
    inverts er1 as er1.
    forwards* h5:erase_value2 h1.
    simpl in *.
    forwards* h7:erase_dtyp er1.
    forwards* h8: erase_value2 er2.
    rewrite <- h7 in *.
    forwards* hy4: bg_to_bgl_casting p b h2.
    lets(ee3&hy6&hy7):hy4.
    inverts hy7 as hy7.
    exists*.
  +
    forwards* h4: erase_value2 er1.
    inverts er1 as er1; eauto.
    exists.
    splits*.
-
   forwards* hh1: erase_lc1 er2.
   inverts red as h1 h2 h3; eauto;
   try solve[].
   +
       destruct E; unfold fill in *; simpl in *; inverts h3 as h3;
       try solve[inverts* h1;forwards*: step_not_value h2];eauto.
       *
         assert(ffill ((eproCtxL (e2))) (e1) = ee_pro (e1) (e2)) as h01; eauto.
         rewrite <- h01.
         forwards* h4: IHer1 er1.
         lets(ee3&h5&h6):h4.
         inverts h6 as h6.
         exists. split.
         apply sStep_eval; auto.
         apply h5.
         simpl; auto.
       *
         inverts h1 as h1 h4.
         forwards* h5: erase_value2 h1.
         forwards* h7:IHer2 er2.
         lets(ee3&hh5&hh6):h7.
         inverts hh6 as hh6.
         assert(ffill ((eproCtxR (e1))) (e2) = ee_pro (e1) (e2)) as h01; eauto.
         rewrite <- h01.
         exists. split.
         apply sStep_eval; auto.
         apply hh5.
         eauto.
         simpl; auto.
   +
     destruct E; unfold fill in *; simpl in *; inverts h3 as h3;
     try solve[inverts* h1;forwards*: step_not_value h2];eauto.
     *
       assert(ffill ((eproCtxL (e2))) (e1) = ee_pro (e1) (e2)) as h01; eauto.
       rewrite <- h01.
       forwards* h4: IHer1 er1.
       lets(ee3&h5&h6):h4.
       inverts h6 as h6.
       exists. split.
       apply sStep_blame; auto.
       apply h5.
       simpl; auto.
     *
       inverts h1 as h1 h4.
       forwards* h5: erase_value2 h1.
       forwards* h7:IHer2 er2.
       lets(ee3&hh5&hh6):h7.
       inverts hh6 as hh6.
       assert(ffill ((eproCtxR (e1))) (e2) = ee_pro e1 (e2)) as h01; eauto.
       rewrite <- h01.
       exists. split.
       apply sStep_blame; auto.
       apply hh5.
       eauto.
-
  inverts red as h1 h2 h3; eauto;
  try solve[].
  +
     destruct E; unfold fill in *; simpl in *; inverts h3 as h3;
     try solve[inverts* h1;forwards*: step_not_value h2];eauto.
     assert(ffill ((elCtx l b)) (e1) = ee_l (e1) l b) as h01; eauto.
     rewrite <- h01.
     forwards* h4: IHer er.
     lets(ee3&h5&h6):h4.
     inverts h6 as h6.
     exists. split.
     apply sStep_eval; auto.
     apply h5.
     simpl; auto.
   +
     destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
     try solve[inverts* h1;forwards*: sstep_not_evalue h2];eauto.
     assert(ffill ((elCtx l b)) (e1) = ee_l (e1) l b) as h01; eauto.
     rewrite <- h01.
     forwards* h4: IHer er.
     lets(ee3&h5&h6):h4.
     inverts h6 as h6.
     exists. split.
     apply sStep_blame; auto.
     apply h5.
     simpl; auto.
   +
     forwards* h5: erase_value2 h1.
     inverts er as er; eauto.
     exists*.
   +
      inverts er as er1 er2; eauto.
     forwards* h5: erase_value2 er1.
     forwards* h6: erase_value2 er2.
-
  inverts red as h1 h2 h3; eauto;
  try solve[].
  +
     destruct E; unfold fill in *; simpl in *; inverts h3 as h3;
     try solve[inverts* h1;forwards*: step_not_value h2];eauto.
     assert(ffill ((erCtx l b)) (e1) = ee_r (e1) l b) as h01; eauto.
     rewrite <- h01.
     forwards* h4: IHer er.
     lets(ee3&h5&h6):h4.
     inverts h6 as h6.
     exists. split.
     apply sStep_eval; auto.
     apply h5.
     simpl; auto.
   +
     destruct E; unfold ffill in *; simpl in *; inverts h3 as h3;
     try solve[inverts* h1;forwards*: sstep_not_evalue h2];eauto.
     assert(ffill ((erCtx l b)) (e1) = ee_r (e1) l b) as h01; eauto.
     rewrite <- h01.
     forwards* h4: IHer er.
     lets(ee3&h5&h6):h4.
     inverts h6 as h6.
     exists. split.
     apply sStep_blame; auto.
     apply h5.
     simpl; auto.
  +
    forwards* h5: erase_value2 h1.
    inverts er as er; eauto.
    exists*.
  +
     inverts er as er1 er2; eauto.
    forwards* h5: erase_value2 er1.
    forwards* h6: erase_value2 er2.
Qed.


Theorem bg_to_bgl: forall e r, 
 lc_exp e ->
 step e r ->
 exists e2 r2, erase e2 e /\ sstep e2 r2 /\ eraser r2 r.
Proof.
 introv lc red.
 forwards* h1: erase_exists_r lc.
 inverts h1 as h1.
 forwards* h2: bg_to_bgl_aux red h1.
 inverts h2 as h2.
 inverts h2 as h2; eauto.
Qed.


Theorem bgl_to_bg: forall e r, 
 lc_eexp e ->
 sstep e r ->
 exists e2 r2, erase e e2 /\ step e2 r2 /\ eraser r r2.
Proof.
 introv lc red.
 forwards* h1: erase_exists lc.
 inverts h1 as h1.
 forwards* h2: bgl_to_bg_aux red h1.
 inverts h2 as h2.
 inverts h2 as h2; eauto.
Qed.

