Require Import LibTactics.
Require Import Metalib.Metatheory.
Require Import Logic. Import Decidable.
Require Import
        Definitions
        Lemmas
        Infrastructure
        Soundness.




Lemma meet_unique: forall A B C1 C2,
 meet A B C1 ->
 meet A B C2 ->
 C1 = C2.
Proof.
 introv me1 me2. gen C2.
 inductions me1; intros;try solve[inductions me2;eauto].
 -
    inverts me2 as h1 h2;eauto.
    forwards*: IHme1_1 h1.
    forwards*: IHme1_2 h2.
    subst*.
 -
    inverts me2 as h1 h2;eauto.
    pick fresh y.
    forwards* h3: h1.
    forwards* h4: H0 h3.
    fequal.
    forwards*: eq_type h4.
 -
    inverts me2 as h1 h2;eauto.
    forwards*: IHme1 h1.
    fequal; auto.
Qed.



Lemma Cast_unique: forall P v mu r1 r2 A B,
    P |== mu -> pvalue v -> typing nil P v Chk B -> Cast (v, mu) A r1 -> Cast (v, mu) A r2 -> r1 = r2.
Proof.
  introv ok pval Typ R1 R2.
  gen r2 B.
  lets R1': R1.
  induction R1; introv R2;
  introv Typ;
    try solve [inverts* R2].
Qed.


Lemma meet_sim2: forall E A B C,
  wf_env E ->
  wf_typ E A ->
  wf_typ E B ->
  meet A B C ->
  consist E A B.
Proof.
 introv wf wf1 wf2 mt. gen E.
 inductions mt;intros; 
 try solve[eauto];
 try solve[forwards* h1: IHmt1; try solve[inverts wf1; inverts wf2;auto]];
 try solve[forwards* h1: IHmt; try solve[inverts wf1; inverts wf2;auto]].
 -
   inverts wf1 as wf1.
   inverts wf2 as wf2.
   pick fresh x and apply consist_all; eauto;
   forwards*: H0 (x ~tvar ++ E);
   try solve[
   apply wf_env_tvar; eauto];
   try solve[forwards*: wf1 x];
   try solve[forwards*: wf2 x];
   try solve[forwards*: wf3 x].
Qed.



Lemma  Casts_unique1: forall v r1 r2 A B P mu ,
    P |== mu -> value v -> typing nil P v Chk B ->  Castv (v,mu) A r1 ->  Castv (v,mu) A r2 -> wf_typ nil A -> r1 = r2.
Proof.
  introv ok val Typ R1 R2 wf1.
  gen r2 B.
  lets R1': R1.
  inverts R1; introv R2;
  introv Typ;
    try solve [inverts* R2];
    try solve [inverts H5].
  - 
    inverts R2 as h1 h2; try solve[inverts h2]; auto.
    +
      forwards* h0: meet_unique H4 h2.
      inverts h0.
      inverts val as val1 val2.
      inverts Typ as typ1 typ2.
      inverts typ2 as typ2 typ3.
      forwards: Cast_unique H1 h1; eauto.
      congruence.
    +
      forwards* h0: meet_unique H4 h2.
      inverts h0.
      inverts val as val1 val2.
      inverts Typ as typ1 typ2.
      inverts typ2 as typ2 typ3.
      forwards: Cast_unique H1 h1; eauto.
      congruence.
    +
      inverts val as h3 h4 h5.
      inverts Typ as h6 h7 .
      inverts h7 as h7 h8 h9 h10.
      inverts h9 as h9 h11; try solve[inverts h8].
      forwards h2: pvalue_wf h11; auto.
      forwards*h12: meet_sim2 H4.
  -
    inverts R2 as h1 h2; try solve[inverts h2];auto.
    +
      forwards* h0: meet_unique H4 h2.
      inverts h0.
      inverts val as val1 val2.
      inverts Typ as typ1 typ2.
      inverts typ2 as typ2 typ3.
      forwards: Cast_unique H1 h1; eauto.
      congruence.
  -
    inverts R2 as h1 h2; try solve[inverts h2]; auto.
    +
      inverts val as h3 h4 h5.
      inverts Typ as h6 h7 .
      inverts h7 as h7 h8 h9 h10.
      inverts h9 as h9 h11; try solve[inverts h8].
      forwards h13: pvalue_wf h11; auto.
      forwards*h12: meet_sim2 h2.
Qed.



Lemma typing_chk: forall E e P A,
 typing E P e Inf A ->
 typing E P e Chk A.
Proof.
  introv typ.
  eapply typ_consist; eauto.
Qed.


Lemma typing_chk2: forall E e P A,
 typing E P e Inf A ->
 exists B, typing E P e Chk B /\ consist E A B.
Proof.
  introv typ.
  exists A. splits.
  eapply typ_consist; auto.
  eapply consist_refl;eauto.
Qed.




Lemma fill_eq: forall mu E0 e0 E e1 r1 r2 mu1 mu2,
  fill E0 e0 = fill E e1 ->
  step (e0, mu) (r1,mu1) ->
  step (e1, mu) (r2,mu2) ->
  wellformed E ->
  wellformed E0 ->
  E = E0 /\ e0 = e1.
Proof.
  introv eq red1 red2 wf1 wf2. gen mu mu1 mu2 E e0 e1 r1 r2.
  inductions E0; unfold fill in *;  intros;
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf1;
  forwards*: step_not_value red1];
  try solve[inductions E; unfold fill in *; inverts* eq];
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf2;
  forwards*: step_not_value red2];
  try solve[inductions E; unfold fill in *; inverts* eq;
  try solve[
  inverts wf2;
  forwards*: step_not_ires red2];
  try solve[
  inverts wf1;
  forwards*: step_not_ires red1]
  ];
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf1;
  forwards*: step_not_rv red1];
  try solve[inductions E; unfold fill in *; inverts* eq;
  inverts wf2;
  forwards*: step_not_rv red2]
  .
Qed.



Lemma fill_chk: forall F e dir P A,
 typing empty P (fill F e) dir A ->
 exists B, typing empty P e Chk B \/ exists f, e = e_rval (e_loc f).
Proof.
  introv typ.
  destruct F; unfold fill in *;inverts typ as h1 h2 h3; eauto;
  try solve[forwards*: typing_chk h2];
  try solve[inverts h2 as h2 h3 h4; 
  try solve[forwards*: typing_chk h3]; auto];
  try solve[
    inverts h2 as h2 h3 h4; 
  try solve[forwards*: typing_chk h4]; auto
  ];
  try solve[
    inverts h2 as h2 h3 h4; 
  try solve[forwards*: typing_chk h2]; auto
  ];
  try solve[
    inverts h2 as h2 h3; exists*  
  ].
  Unshelve.
  apply t_dyn.
  apply t_dyn.
Qed.



Theorem step_unique: forall P mu A e r1 r2,
   P |== mu -> typing nil P e Chk A -> step (e, mu) r1 -> step (e, mu) r2 -> r1 = r2.
Proof.
  introv well Typ Red1.
  gen P A r2.
  lets Red1' : Red1.
  inductions Red1; 
    introv well Typ Red2.
  - (* fill *)
    inverts* Red2; 
    try solve[ destruct F; unfold fill in *; inverts* H0;
    try solve[forwards hh1: step_not_value Red1; auto; 
    inverts* hh1];
    try solve[forwards* hh1: step_not_rv Red1]
    ];
    try solve[
      forwards* h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts* H0;
      try solve[forwards*: step_not_value Red1];
      inverts h3 as h31 h32;
      inverts h31 as h31 h33;
      inverts h31 as h31 h34;
      inverts h31 as h31 h35;
      try solve[
      forwards*: step_not_value Red1];
      try solve[
        inverts* H
      ]
    ];
    try solve[
    destruct F; unfold fill in *; inverts* H0;
      try solve[forwards*: step_not_value Red1];
      try solve[forwards*: step_not_ires Red1];
      try solve[inverts H]
    ];
    try solve[
    destruct F; unfold fill in *; inverts* H1  
    ].
    + forwards* h: fill_eq H0.
      destruct h. subst. 
      forwards* h1: fill_chk Typ. inverts h1 as h1.
      inverts h1 as h1 hh1.
      forwards* h2: IHRed1 Red1. congruence.
      inverts h1 as h1.
      forwards*: step_not_rv H4.
    + forwards* h: fill_eq H0.
      destruct h. subst. 
      forwards* h1: fill_chk Typ. inverts h1 as h1.
      inverts h1 as h1 hh1.
      forwards* h2: IHRed1 Red1. congruence.
      inverts h1 as h1.
      forwards*: step_not_rv H4.
  - (* fill *)
    inverts Red2;
    try solve[ destruct F; unfold fill in *; inverts H0;
    try solve[
    forwards hh1: step_not_rv Red1; inverts hh1; auto];
    try solve[
    forwards hh1: step_not_value Red1; auto; inverts hh1; auto]];
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts H0;
      try solve[forwards: step_not_value Red1; auto];
      inverts h3 as h31 h32;
      inverts h31 as h31 h33;
      inverts h31 as h31 h34;
      inverts h31 as h31 h35;
      try solve[
      forwards h0: step_not_value Red1; auto; inverts h0];
      try solve[inverts H]
    ];
    try solve[
      destruct F; unfold fill in *; inverts H0;
      try solve[forwards h0: step_not_value Red1; auto;inverts h0];
      try solve[forwards h0: step_not_ires Red1;auto;inverts h0];
      try solve[inverts H]
    ];
    try solve[
    destruct F; unfold fill in *; inverts H1  
    ].
    + 
      forwards* h: fill_eq H0.
      destruct h. subst. 
      forwards* h1: fill_chk Typ. inverts h1 as h1.
      inverts h1 as h1 h11.
      *
      forwards* h2: IHRed1 Red1. congruence.
      *
      inverts h1 as h1.
      forwards*: step_not_rv H4.
    + forwards* h: fill_eq H0.
      destruct h. subst. 
      forwards* h1: fill_chk Typ. inverts h1 as h1.
      inverts h1 as h1 h11.
      *
      forwards* h2: IHRed1 Red1.
      *
      inverts h1 as h1.
      forwards*: step_not_rv H4.
  - (* beta *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts hh3;
      try solve[forwards hh0: step_not_ires hh2; auto; inverts hh0];
      try solve[forwards hh0: step_not_value hh2; auto; inverts hh0]
      ];
    try solve[
      inverts hh3; inverts H0
    ]; auto.
  - (* app *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
    lets(h2&h3&h4): h1;
    inverts h3 as hh5 hh6;
    inverts hh5 as hh5 hh7;
    inverts hh5 as hh5 hh8;
    inverts hh5 as hh5 hh9;
    destruct F; unfold fill in *; inverts hh3;
    try solve[forwards hh0: step_not_ires hh2; auto; inverts hh0];
    try solve[forwards hh0: step_not_value hh2; auto; inverts hh0];
    try solve[inverts* hh1]
      ];
    try solve[
      inverts hh3; inverts H0
    ]; auto.
    +
    forwards h1: pattern_abs_uniq H1 hh3.
    inverts h1 as h1; eauto.
    +
    inverts Typ as hh10 hh11.
    inverts hh11 as hh12 hh13 hh14.
    inverts hh13 as hh13 hh15 hh16 hh17.
    inverts hh16 as hh16 hh18.
    simpl in *.
    forwards h1: typing_regular hh18; 
    lets(h2&h3&h4): h1.
    inverts hh18 as hh18.
    inverts h1 as hh19 hh20.
    inverts hh20 as hh20 hh21.
    inverts hh21.
    exfalso; apply hh2; eauto.
  - (* absdyn *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts hh3;
      try solve[forwards hh0: step_not_value hh2; auto; inverts hh0];
      try solve[inverts* hh1]
    ];
    try solve[
      inverts hh3; inverts H0
    ]; auto.
    +
      simpl in *.
      inverts Typ as h1 h2.
      inverts h2 as h2 h4 h5.
      forwards* h3: typing_regular h4.
      inverts h3 as h3 h6.
      inverts h6 as h6 h7.
      inverts h4 as h8 h9 h10.
      inverts h10 as h10 h11.
      forwards* h12: typing_regular h11.
      inverts h12 as h12 h13.
      inverts h13 as h13 h14.
      inverts h11 as h11.
      inverts h14.
      exfalso; apply H0; eauto.
  - (* annov *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts hh3;
      try solve[forwards*: step_not_value hh2; auto];
      try solve[forwards*: step_not_ires hh2]];
    try solve[
      inverts H0
    ]; auto.
    +
    inverts Typ as h1 h2.
    forwards* h3: typing_regular h2.
    inverts h3 as h3 h6.
    inverts h6 as h6 h7.
    inverts h2 as h2.
    forwards*: Casts_unique1 H1 hh3.
    congruence.
  - (* abs *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts hh3;
      try solve[forwards*: step_not_value hh2; auto];
      try solve[forwards*: step_not_ires hh2]];
    try solve[
      inverts hh2
    ]; auto.
    forwards* h23: pattern_abs_uniq H0 hh2.
    inverts* h23.
  - (* tabs *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts hh3;
      try solve[forwards*: step_not_value hh2; auto];
      try solve[forwards*: step_not_ires hh2]];
    try solve[
      inverts hh2
    ]; auto.
    forwards* h23: pattern_all_uniq H0 hh2.
    inverts* h23.
  - (* lit *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts hh3;
      try solve[forwards*: step_not_value hh2; auto];
      try solve[forwards*: step_not_ires hh2]];
    try solve[
      inverts hh2
    ]; auto.
  - (* unit *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts hh3;
      try solve[forwards*: step_not_value hh2; auto];
      try solve[forwards*: step_not_ires hh2]];
    try solve[
      inverts hh2
    ]; auto.
  - (* o *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts hh3;
      try solve[forwards*: step_not_value hh2; auto];
      try solve[forwards*: step_not_ires hh2]];
    try solve[
      inverts hh2
    ]; auto.
  - (* tapp *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
    forwards h1: typing_regular Typ; 
    lets(h2&h3&h4): h1;
    destruct F; unfold fill in *; inverts hh3;
    try solve[forwards: step_not_value Red1; auto];
    inverts h3 as h31 h32;
    inverts h31 as h31 h33;
    inverts h31 as h31 h34;
    inverts h31 as h31 h35;
    forwards h0: step_not_value hh2; auto; inverts h0];
    try solve[
      inverts hh3; inverts H0
    ].
    +
      forwards* h1: pattern_all_uniq H0 hh2.
      inverts* h1.
    +
      simpl in *.
      inverts Typ as h1 h2.
      inverts h2 as h2 h4 h5.
      forwards* h3: typing_regular h5.
      inverts h3 as h3 h6.
      inverts h6 as h6 h7.
      inverts h5 as h8 h9 h10.
      inverts h10 as h10 h11.
      forwards* h12: typing_regular h11.
      inverts h12 as h12 h13.
      inverts h13 as h13 h14.
      inverts h11 as h11.
      inverts h14 as h14.
      exfalso; apply hh3; eauto.
  - (* tappd *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
    forwards h1: typing_regular Typ; 
    lets(h2&h3&h4): h1;
    destruct F; unfold fill in *; inverts hh3;
    try solve[forwards: step_not_value Red1; auto];
    inverts h3 as h31 h32;
    inverts h31 as h31 h33;
    inverts h31 as h31 h34;
    forwards h0: step_not_value hh2; auto; inverts h0];
    try solve[
      inverts hh3; inverts H0
    ];auto.
    +
      simpl in *.
      inverts Typ as h1 h2.
      inverts h2 as h2 h4 h5.
      forwards* h3: typing_regular h5.
      inverts h3 as h3 h6.
      inverts h6 as h6 h7.
      inverts h5 as h8 h9 h10.
      inverts h10 as h10 h11.
      forwards* h12: typing_regular h11.
      inverts h12 as h12 h13.
      inverts h13 as h13 h14.
      inverts h11 as h11.
      inverts h14 as h14.
      exfalso; apply H1; eauto.
  - (* setv *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts hh3;
      try solve[forwards h0: step_not_value hh2; auto;
      inverts h0];
      try solve[forwards h0: step_not_rv hh2; auto;
      inverts h0
      ]
    ];auto.
  - (* set *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts hh3;
      inverts h3 as h31 h32;
      inverts h31 as h31 h33;
      inverts h31 as h31 h34;
      try solve[forwards h0: step_not_value hh2; auto;
      inverts h0];
      try solve[forwards h0: step_not_rv hh2; auto;
      inverts h0
      ];
      try solve[inverts hh1]
    ];auto;
    try solve[forwards* h1: pattern_ref_uniq H0 hh2;
    inverts* h1].
    +
      inverts Typ as h1 h2.
      inverts h2 as h2 h4 h5.
      forwards* h3: typing_regular h4.
      inverts h3 as h3 h6.
      inverts h6 as h6 h7.
      inverts h4 as h8 h9 h10.
      inverts h10 as h10 h11.
      forwards* h12: typing_regular h11.
      inverts h12 as h12 h13.
      inverts h13 as h13 h14.
      inverts h11 as h11.
      inverts h14.
      simpl in *; exfalso;apply hh3; eauto.
  - (* setd *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      inverts h3 as h31 h32;
      inverts h31 as h31 h33;
      destruct F; unfold fill in *; inverts hh3;
      try solve[forwards hh0: step_not_value hh2; auto;
      inverts hh0];
      try solve[inverts hh1]
    ];
    try solve[
      inverts hh3; inverts H0
    ]; auto.
    +
      simpl in *.
      inverts Typ as h1 h2.
      inverts h2 as h2 h4 h5.
      forwards* h3: typing_regular h4.
      inverts h3 as h3 h6.
      inverts h6 as h6 h7.
      inverts h4 as h8 h9 h10.
      inverts h10 as h10 h11.
      forwards* h12: typing_regular h11.
      inverts h12 as h12 h13.
      inverts h13 as h13 h14.
      inverts h11 as h11.
      inverts h14.
      exfalso; apply H1; eauto.   
  - (* ref *)
   inverts Red2 as hh1 hh2 hh3;
    try solve[
      forwards h1: typing_regular Typ; 
      lets(h2&h3&h4): h1;
      destruct F; unfold fill in *; inverts hh3;
      try solve[forwards*: step_not_value hh2; auto];
      try solve[forwards*: step_not_ires hh2]];
    try solve[
      inverts hh2
    ]; auto.
  - (* get *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
    forwards h1: typing_regular Typ; 
    lets(h2&h3&h4): h1;
    destruct F; unfold fill in *; inverts hh3;
    try solve[forwards: step_not_value Red1; auto];
    inverts h3 as h31 h32;
    inverts h31 as h31 h33;
    inverts h31 as h31 h34;
    inverts h31 as h31 h35;
    forwards h0: step_not_value hh2; auto; inverts h0];
    try solve[
      inverts hh3; inverts H0
    ]; auto.
    +
      forwards* h1: pattern_ref_uniq H0 hh2.
      inverts* h1.
    +
    simpl in *.
    inverts Typ as h1 h2.
    inverts h2 as h2 h3.
    inverts h3 as h3 h4 h5.
    inverts h5 as h5 h6.
    forwards* h7: typing_regular h6.
    inverts h7 as h7 h8.
    inverts h8 as h8 h9.
    inverts h6 as h6.
    inverts h9.
    exfalso; apply hh3; auto.
  - (* getd *)
    inverts Red2 as hh1 hh2 hh3;
    try solve[
    forwards h1: typing_regular Typ; 
    lets(h2&h3&h4): h1;
    destruct F; unfold fill in *; inverts hh3;
    try solve[forwards: step_not_value Red1; auto];
    inverts h3 as h31 h32;
    inverts h31 as h31 h33;
    inverts h31 as h31 h34;
    forwards h0: step_not_value hh2; auto; inverts h0];
    try solve[
      inverts hh3; inverts H0
    ]; auto.
    +
    simpl in *.
    inverts Typ as h1 h2.
    inverts h2 as h2 h3.
    inverts h3 as h3 h4 h5.
    inverts h5 as h5 h6.
    forwards* h7: typing_regular h6.
    inverts h7 as h7 h8.
    inverts h8 as h8 h9.
    inverts h6 as h6.
    inverts h9.
    exfalso; apply H1; auto.
Qed.