(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Loebian Obstacle           *)
(*                                                                            *)
(*     Part 9 of 11. Code patterns and the substitution rows of a code.       *)
(*                                                                            *)
(*     Author: Charles C. Norton                                              *)
(*     License: MIT                                                           *)
(*                                                                            *)
(******************************************************************************)

From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import Setoid Morphisms Ring Ring_theory.
Import ListNotations.

From Provability Require Import Calculus ArithSyntax ArithSemantics ArithInternal ArithTransfer
  ArithMerge ArithDerivability ArithRows.
Open Scope fo_scope.

(** ** The tables the row constructions extend.

    [FOtabB]: a fresh one-row table, [FOtabS]: one table extended by a
    row, [FOtabJ]: two merged tables extended by a row. *)

Definition FOtabB : FOtab :=
  mkTab (FOVar 141) (FOVar 142) (FOVar 143) (FOVar 144) (FOVar 145) (FOVar 146)
    (FOVar 147) (FOVar 148) (FOVar 149) (FOVar 150) (FOSucc FOZero).
Definition FOtabS : FOtab :=
  mkTab (FOVar 141) (FOVar 142) (FOVar 143) (FOVar 144) (FOVar 145) (FOVar 146)
    (FOVar 147) (FOVar 148) (FOVar 149) (FOVar 150) (FOSucc (FOVar 140)).
Definition FOtabJ : FOtab :=
  mkTab (FOVar 182) (FOVar 183) (FOVar 184) (FOVar 185) (FOVar 186) (FOVar 187)
    (FOVar 188) (FOVar 189) (FOVar 190) (FOVar 191) (FOSucc (tlen FOtabM)).

Ltac tab_avoid ::=
  try unfold FOtabB; try unfold FOtabS; try unfold FOtabJ; try unfold FOtabM;
  try unfold FOtab_terms; try unfold FOtabv; try unfold FOtabx; try unfold FOtab0;
  cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app]; avoid_tms.

Ltac disp0 := unfold FODISPCASES; apply FOPrH_or_intro_l;
  apply FOPrH_and_intro; [apply FOPrH_refl|].
Ltac disp1 := unfold FODISPCASES; apply FOPrH_or_intro_r; apply FOPrH_or_intro_l;
  apply FOPrH_and_intro; [apply FOPrH_refl|].
Ltac disp2 := unfold FODISPCASES; do 2 apply FOPrH_or_intro_r; apply FOPrH_or_intro_l;
  apply FOPrH_and_intro; [apply FOPrH_refl|].
Ltac disp3 := unfold FODISPCASES; do 3 apply FOPrH_or_intro_r; apply FOPrH_or_intro_l;
  apply FOPrH_and_intro; [apply FOPrH_refl|].
Ltac disp4 := unfold FODISPCASES; do 4 apply FOPrH_or_intro_r; apply FOPrH_or_intro_l;
  apply FOPrH_and_intro; [apply FOPrH_refl|].
Ltac alt1 := apply FOPrH_or_intro_l.
Ltac alt2 := apply FOPrH_or_intro_r; apply FOPrH_or_intro_l.
Ltac alt3 := do 2 apply FOPrH_or_intro_r; apply FOPrH_or_intro_l.
Ltac alt4 := do 3 apply FOPrH_or_intro_r; apply FOPrH_or_intro_l.
Ltac alt5 := do 4 apply FOPrH_or_intro_r.

(** ** A row from rows of one table holding three given rows. *)

Lemma FOPrH_tab_step3 : forall n G tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r''
    tgn a1n a2n a3n rn,
  FOctx_avoid G 2 500 ->
  FOtms_avoid [tg; a1; a2; a3; r; tg'; a1'; a2'; a3'; r'; tg''; a1''; a2''; a3''; r'';
               tgn; a1n; a2n; a3n; rn] 2 500 ->
  FOPrH n G (FOTBLEX3 tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'') ->
  (forall G', (forall X, In X G -> In X G') ->
     FOPrH n G' (FOlookupT 28 FOtabS tg a1 a2 a3 r) ->
     FOPrH n G' (FOlookupT 28 FOtabS tg' a1' a2' a3' r') ->
     FOPrH n G' (FOlookupT 28 FOtabS tg'' a1'' a2'' a3'' r'') ->
     FOPrH n G' (FODISPCASES (FOVar 141) (FOVar 142) (FOVar 143) (FOVar 144) (FOVar 145)
                   (FOVar 146) (FOVar 147) (FOVar 148) (FOVar 149) (FOVar 150)
                   (FOSucc (FOVar 140)) tgn a1n a2n a3n rn)) ->
  FOPrH n G (FOTBLEX tgn a1n a2n a3n rn).
Proof.
  intros n G tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' tgn a1n a2n a3n rn
    HG Hav HE HP.
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex3_elim n G tg a1 a2 a3 r tg' a1' a2' a3' r'
                              tg'' a1'' a2'' a3'' r'' 130 _ _ _ _ _ _ _ _) HE);
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (K : FOPrH n G1 (FOAnd (FOTBLVALID 18 (tct (FOtabv 130)) (tdt (FOtabv 130))
                   (tc1 (FOtabv 130)) (td1 (FOtabv 130)) (tc2 (FOtabv 130)) (td2 (FOtabv 130))
                   (tc3 (FOtabv 130)) (td3 (FOtabv 130)) (tcr (FOtabv 130)) (tdr (FOtabv 130))
                   (tlen (FOtabv 130)))
                 (FOAnd (FOlookupT 28 (FOtabv 130) tg a1 a2 a3 r)
                 (FOAnd (FOlookupT 28 (FOtabv 130) tg' a1' a2' a3' r')
                        (FOlookupT 28 (FOtabv 130) tg'' a1'' a2'' a3'' r''))))) by apply FOPrH_last;
    assert (HGinc : forall X, In X G -> In X G1)
      by (intros X HX; apply in_or_app; left; exact HX)
  end.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ K)) as K1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ K))) as K2.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ K))) as K3.
  apply (FOPrH_row_new n _ (FOtabv 130) tgn a1n a2n a3n rn 141 _);
    [ exact (FOPrH_and_l _ _ _ _ K)
    | intros G' Hinc HA1 HA2 Hm;
      refine (HP G' (fun X HX => Hinc X (HGinc X HX)) _ _ _);
      [ refine (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n G' 28 (FOtabv 130) _ tg a1 a2 a3 r Hm
                                    ltac:(lia) _ _ _ _)
                  (FOPrH_weaken n _ G' _ Hinc K1));
        [ intros w ? ?; apply HA1; lia | exact HA2 | tab_side | tab_side ]
      | refine (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n G' 28 (FOtabv 130) _ tg' a1' a2' a3' r'
                                    Hm ltac:(lia) _ _ _ _)
                  (FOPrH_weaken n _ G' _ Hinc K2));
        [ intros w ? ?; apply HA1; lia | exact HA2 | tab_side | tab_side ]
      | refine (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n G' 28 (FOtabv 130) _ tg'' a1'' a2'' a3''
                                    r'' Hm ltac:(lia) _ _ _ _)
                  (FOPrH_weaken n _ G' _ Hinc K3));
        [ intros w ? ?; apply HA1; lia | exact HA2 | tab_side | tab_side ] ]
    | tab_side .. |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (N : FOPrH n Gc (FOTBLNEW (FOtabv 130) (FOtabx 141 (FOSucc (tlen (FOtabv 130))))
                              tgn a1n a2n a3n rn)) by apply FOPrH_last
  end.
  unfold FOTBLNEW in N.
  apply (FOPrH_tblex_intro n _ (FOtabx 141 (FOSucc (tlen (FOtabv 130)))) tgn a1n a2n a3n rn
           (FOPrH_and_l _ _ _ _ N) (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ N))).
  tab_side.
Qed.

(** ** Occurrence rows (tag [0]): [(0, w, tc, 0, r)], [r] the occurrence
    of the variable [w] in the term coded by [tc]. *)

Lemma FOPrH_N0_var_eq : forall n G w tc y,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; tc; y] 2 500 ->
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FOEq y w) ->
  FOPrH n G (FOTBLEX FOZero w tc FOZero (FOnumeral 1)).
Proof.
  intros n G w tc y HG Hav Hc E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp0. exact (FOPrH_step0_var_eq n G FOtabB w tc y Hc E ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N0_var_ne : forall n G w tc y,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; tc; y] 2 500 ->
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FONeg (FOEq y w)) ->
  FOPrH n G (FOTBLEX FOZero w tc FOZero FOZero).
Proof.
  intros n G w tc y HG Hav Hc E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp0. exact (FOPrH_step0_var_ne n G FOtabB w tc y Hc E ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N0_zero : forall n G w tc,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; tc] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero tc) ->
  FOPrH n G (FOTBLEX FOZero w tc FOZero FOZero).
Proof.
  intros n G w tc HG Hav Hc.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  apply FOPrH_case0_zero. exact Hc.
Qed.

Lemma FOPrH_N0_succ : forall n G w t tc r,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; t; tc; r] 2 500 ->
  FOPrH n G (FOTBLEX FOZero w t FOZero r) -> FOPrH n G (FOcpairF (FOnumeral 2) t tc) ->
  FOPrH n G (FOTBLEX FOZero w tc FOZero r).
Proof.
  intros n G w t tc r HG Hav HE HC.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  apply (FOPrH_case0_succ n G' _ _ _ _ _ _ _ _ _ _ _ w t tc r);
    [ apply (FOPrH_lookup_rebase _ _ 28 52);
      [exact HL | lia | lia | lia | lia | lia | tab_side | tab_side]
    | exact (FOPrH_weaken n G G' _ Hinc HC) | tab_side | tab_side ].
Qed.

Lemma FOPrH_N0_bin_one : forall n G w tc k p a b,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [w; tc; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX FOZero w a FOZero (FOnumeral 1)) ->
  FOPrH n G (FOcpairF (FOnumeral k) p tc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX FOZero w tc FOZero (FOnumeral 1)).
Proof.
  intros n G w tc k p a b Hk HG Hav HE Hc Hp.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  disp0. unfold FOSTEP0.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_stepbin_one n G' FOtabS w tc _ 0 p a b Hc' Hp' HL
             ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N0_bin_zero : forall n G w tc r k p a b,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [w; tc; r; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX FOZero w a FOZero FOZero) ->
  FOPrH n G (FOTBLEX FOZero w b FOZero r) ->
  FOPrH n G (FOcpairF (FOnumeral k) p tc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX FOZero w tc FOZero r).
Proof.
  intros n G w tc r k p a b Hk HG Hav Ha Hb Hc Hp.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  disp0. unfold FOSTEP0.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_stepbin_zero n G' FOtabJ w tc r _ 0 p a b Hc' Hp' La Lb
             ltac:(tab_side) ltac:(tab_side)).
Qed.

(** ** Free-occurrence rows (tag [1]): [(1, w, pc, 0, r)]. *)

Lemma FOPrH_N1_eq_one : forall n G w pc p a b,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX FOZero w a FOZero (FOnumeral 1)) ->
  FOPrH n G (FOcpairF FOZero p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero (FOnumeral 1)).
Proof.
  intros n G w pc p a b HG Hav HE Hc Hp.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  disp1. unfold FOSTEP1. alt1.
  exact (FOPrH_stepbin_one n G' FOtabS w pc 0 0 p a b Hc' Hp' HL
           ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N1_eq_zero : forall n G w pc r p a b,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc; r; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX FOZero w a FOZero FOZero) ->
  FOPrH n G (FOTBLEX FOZero w b FOZero r) ->
  FOPrH n G (FOcpairF FOZero p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero r).
Proof.
  intros n G w pc r p a b HG Hav Ha Hb Hc Hp.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  disp1. unfold FOSTEP1. alt1.
  exact (FOPrH_stepbin_zero n G' FOtabJ w pc r 0 0 p a b Hc' Hp' La Lb
           ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N1_false : forall n G w pc,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero pc) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero FOZero).
Proof.
  intros n G w pc HG Hav Hc.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp1. apply FOPrH_step1_false. exact Hc.
Qed.

Lemma FOPrH_N1_impl_one : forall n G w pc p a b,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w a FOZero (FOnumeral 1)) ->
  FOPrH n G (FOcpairF (FOnumeral 2) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero (FOnumeral 1)).
Proof.
  intros n G w pc p a b HG Hav HE Hc Hp.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  disp1. unfold FOSTEP1. alt3.
  exact (FOPrH_stepbin_one n G' FOtabS w pc 2 1 p a b Hc' Hp' HL
           ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N1_impl_zero : forall n G w pc r p a b,
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc; r; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w a FOZero FOZero) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w b FOZero r) ->
  FOPrH n G (FOcpairF (FOnumeral 2) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero r).
Proof.
  intros n G w pc r p a b HG Hav Ha Hb Hc Hp.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  disp1. unfold FOSTEP1. alt3.
  exact (FOPrH_stepbin_zero n G' FOtabJ w pc r 2 1 p a b Hc' Hp' La Lb
           ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N1_quant_eq : forall n G w pc k p y bb,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc; p; y; bb] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FOEq y w) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero FOZero).
Proof.
  intros n G w pc k p y bb Hk HG Hav Hc Hp E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp1. unfold FOSTEP1.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_quant0_eq n G FOtabB w pc _ 1 p y bb Hc Hp E
             ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N1_quant_ne : forall n G w pc r k p y bb,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [w; pc; r; p; y; bb] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w bb FOZero r) ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y w)) ->
  FOPrH n G (FOTBLEX (FOnumeral 1) w pc FOZero r).
Proof.
  intros n G w pc r k p y bb Hk HG Hav HE Hc Hp E.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc'.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp'.
  pose proof (FOPrH_weaken n G G' _ Hinc E) as E'.
  disp1. unfold FOSTEP1.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_quant0_ne n G' FOtabS w pc r _ 1 p y bb Hc' Hp' E' HL
             ltac:(tab_side) ltac:(tab_side)).
Qed.

(** ** Substitution rows into terms (tag [2]): [(2, X, s, tc, r)]. *)

Lemma FOPrH_N2_var_eq : forall n G X s tc y,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; tc; y] 2 500 ->
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FOEq y X) ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s tc s).
Proof.
  intros n G X s tc y HG Hav Hc E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp2. exact (FOPrH_step2_var_eq n G FOtabB X s tc y Hc E ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N2_var_ne : forall n G X s tc y,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; tc; y] 2 500 ->
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FONeg (FOEq y X)) ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s tc tc).
Proof.
  intros n G X s tc y HG Hav Hc E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp2. exact (FOPrH_step2_var_ne n G FOtabB X s tc y Hc E ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N2_zero : forall n G X s tc,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; tc] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero tc) ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s tc tc).
Proof.
  intros n G X s tc HG Hav Hc.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  apply FOPrH_case2_zero. exact Hc.
Qed.

Lemma FOPrH_N2_succ : forall n G X s t t' tc r,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; t; t'; tc; r] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s t t') ->
  FOPrH n G (FOcpairF (FOnumeral 2) t tc) -> FOPrH n G (FOcpairF (FOnumeral 2) t' r) ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s tc r).
Proof.
  intros n G X s t t' tc r HG Hav HE HC HC'.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  apply (FOPrH_case2_succ n G' _ _ _ _ _ _ _ _ _ _ _ X s t t' tc r);
    [ apply (FOPrH_lookup_rebase _ _ 28 54);
      [exact HL | lia | lia | lia | lia | lia | tab_side | tab_side]
    | exact (FOPrH_weaken n G G' _ Hinc HC) | exact (FOPrH_weaken n G G' _ Hinc HC')
    | tab_side | tab_side ].
Qed.

Lemma FOPrH_N2_bin : forall n G X s tc r k p a b a' b' p',
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; tc; r; p; a; b; a'; b'; p'] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s a a') ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s b b') ->
  FOPrH n G (FOcpairF (FOnumeral k) p tc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOcpairF a' b' p') -> FOPrH n G (FOcpairF (FOnumeral k) p' r) ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s tc r).
Proof.
  intros n G X s tc r k p a b a' b' p' Hk HG Hav Ha Hb Hc Hp Hp' Hr.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp') as Hp2.
  pose proof (FOPrH_weaken n G G' _ Hinc Hr) as Hr1.
  disp2. unfold FOSTEP2.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_substbin_intro n G' FOtabJ X s tc r _ 2 _ p a b a' b' p' Hc1 Hp1 La Lb
             Hp2 Hr1 ltac:(tab_side) ltac:(tab_side)).
Qed.

(** ** Substitution rows into formulas (tag [3]): [(3, X, s, pc, r)]. *)

Lemma FOPrH_N3_eq : forall n G X s pc r p a b a' b' p',
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; r; p; a; b; a'; b'; p'] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s a a') ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s b b') ->
  FOPrH n G (FOcpairF FOZero p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOcpairF a' b' p') -> FOPrH n G (FOcpairF FOZero p' r) ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s pc r).
Proof.
  intros n G X s pc r p a b a' b' p' HG Hav Ha Hb Hc Hp Hp' Hr.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp') as Hp2.
  pose proof (FOPrH_weaken n G G' _ Hinc Hr) as Hr1.
  disp3. unfold FOSTEP3. alt1.
  exact (FOPrH_substbin_intro n G' FOtabJ X s pc r 0 2 0 p a b a' b' p' Hc1 Hp1 La Lb
           Hp2 Hr1 ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N3_false : forall n G X s pc,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero pc) ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s pc pc).
Proof.
  intros n G X s pc HG Hav Hc.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp3. apply FOPrH_step3_false. exact Hc.
Qed.

Lemma FOPrH_N3_impl : forall n G X s pc r p a b a' b' p',
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; r; p; a; b; a'; b'; p'] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s a a') ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s b b') ->
  FOPrH n G (FOcpairF (FOnumeral 2) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOcpairF a' b' p') -> FOPrH n G (FOcpairF (FOnumeral 2) p' r) ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s pc r).
Proof.
  intros n G X s pc r p a b a' b' p' HG Hav Ha Hb Hc Hp Hp' Hr.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp') as Hp2.
  pose proof (FOPrH_weaken n G G' _ Hinc Hr) as Hr1.
  disp3. unfold FOSTEP3. alt3.
  exact (FOPrH_substbin_intro n G' FOtabJ X s pc r 2 3 2 p a b a' b' p' Hc1 Hp1 La Lb
           Hp2 Hr1 ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N3_quant_eq : forall n G X s pc k p y bb,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; p; y; bb] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FOEq y X) ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s pc pc).
Proof.
  intros n G X s pc k p y bb Hk HG Hav Hc Hp E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp3. unfold FOSTEP3.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_substquant_eq n G FOtabB X s pc _ p y bb Hc Hp E
             ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N3_quant_ne : forall n G X s pc r k p y bb bb' p',
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; r; p; y; bb; bb'; p'] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s bb bb') ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y X)) ->
  FOPrH n G (FOcpairF y bb' p') -> FOPrH n G (FOcpairF (FOnumeral k) p' r) ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s pc r).
Proof.
  intros n G X s pc r k p y bb bb' p' Hk HG Hav HE Hc Hp E Hp' Hr.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  pose proof (FOPrH_weaken n G G' _ Hinc E) as E1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp') as Hp2.
  pose proof (FOPrH_weaken n G G' _ Hinc Hr) as Hr1.
  disp3. unfold FOSTEP3.
  destruct Hk as [->| ->]; [alt4 | alt5].
  - exact (FOPrH_substquant_ne n G' FOtabS X s pc r 3 p y bb bb' p' ltac:(lia) Hc1 Hp1 E1 HL
             Hp2 Hr1 ltac:(tab_side) ltac:(tab_side)).
  - exact (FOPrH_substquant_ne n G' FOtabS X s pc r 4 p y bb bb' p' ltac:(lia) Hc1 Hp1 E1 HL
             Hp2 Hr1 ltac:(tab_side) ltac:(tab_side)).
Qed.

(** ** Capture-test rows (tag [4]): [(4, X, s, pc, r)], [r = 1] when [s]
    is free for [X] in the formula coded by [pc]. *)

Lemma FOPrH_N4_eq : forall n G X s pc p,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; p] 2 500 ->
  FOPrH n G (FOcpairF FOZero p pc) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s pc (FOnumeral 1)).
Proof.
  intros n G X s pc p HG Hav Hc.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp4. exact (FOPrH_step4_eq n G FOtabB X s pc p Hc ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N4_false : forall n G X s pc,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero pc) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s pc (FOnumeral 1)).
Proof.
  intros n G X s pc HG Hav Hc.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp4. apply FOPrH_step4_false. exact Hc.
Qed.

Lemma FOPrH_N4_impl : forall n G X s pc r p a b,
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; r; p; a; b] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s a (FOnumeral 1)) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s b r) ->
  FOPrH n G (FOcpairF (FOnumeral 2) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s pc r).
Proof.
  intros n G X s pc r p a b HG Hav Ha Hb Hc Hp.
  refine (FOPrH_tblex_join n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ Ha Hb _); [tab_side|].
  intros G' Hinc La Lb.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  disp4. unfold FOSTEP4. alt3.
  exact (FOPrH_subokbin_one n G' FOtabJ X s pc r p a b Hc1 Hp1 La Lb
           ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N4_quant_eq : forall n G X s pc k p y bb,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; p; y; bb] 2 500 ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FOEq y X) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s pc (FOnumeral 1)).
Proof.
  intros n G X s pc k p y bb Hk HG Hav Hc Hp E.
  apply FOPrH_tab_base; [exact HG | tab_side |].
  disp4. unfold FOSTEP4.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_subokquant_eq n G FOtabB X s pc _ p y bb Hc Hp E
             ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N4_quant_nf : forall n G X s pc k p y bb,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; p; y; bb] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 1) X bb FOZero FOZero) ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y X)) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s pc (FOnumeral 1)).
Proof.
  intros n G X s pc k p y bb Hk HG Hav HE Hc Hp E.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  pose proof (FOPrH_weaken n G G' _ Hinc E) as E1.
  disp4. unfold FOSTEP4.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_subokquant_nf n G' FOtabS X s pc _ p y bb Hc1 Hp1 E1 HL
             ltac:(tab_side) ltac:(tab_side)).
Qed.

Lemma FOPrH_N4_quant_fr : forall n G X s pc r k p y bb,
  k = 3 \/ k = 4 ->
  FOctx_avoid G 2 500 -> FOtms_avoid [X; s; pc; r; p; y; bb] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 1) X bb FOZero (FOnumeral 1)) ->
  FOPrH n G (FOTBLEX FOZero y s FOZero FOZero) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s bb r) ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y X)) ->
  FOPrH n G (FOTBLEX (FOnumeral 4) X s pc r).
Proof.
  intros n G X s pc r k p y bb Hk HG Hav H1 H0 H4 Hc Hp E.
  assert (H3 : FOPrH n G (FOTBLEX3 (FOnumeral 1) X bb FOZero (FOnumeral 1)
                            FOZero y s FOZero FOZero (FOnumeral 4) X s bb r)).
  { refine (FOPrH_tblex_join3 n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ H1 H0 H4). tab_side. }
  refine (FOPrH_tab_step3 n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HG _ H3 _);
    [tab_side|].
  intros G' Hinc L1 L0 L4.
  pose proof (FOPrH_weaken n G G' _ Hinc Hc) as Hc1.
  pose proof (FOPrH_weaken n G G' _ Hinc Hp) as Hp1.
  pose proof (FOPrH_weaken n G G' _ Hinc E) as E1.
  disp4. unfold FOSTEP4.
  destruct Hk as [->| ->]; [alt4 | alt5];
    exact (FOPrH_subokquant_fr n G' FOtabS X s pc r _ p y bb Hc1 Hp1 E1 L1 L0 L4
             ltac:(tab_side) ltac:(tab_side)).
Qed.

(** ** Code patterns of terms and formulas.

    [cpat_tm rho t], [cpat_f rho A]: the code of [t], [A] with every
    free variable [y] that [rho] maps to [Some i] left as slot [i];
    a binder hides its variable from [rho]. *)

Definition rho_hide (y : nat) (rho : nat -> option nat) : nat -> option nat :=
  fun z => if Nat.eqb z y then None else rho z.

Fixpoint cpat_tm (rho : nat -> option nat) (t : FOTerm) : CPat :=
  match t with
  | FOVar y => match rho y with Some i => CVarP i | None => tVarP (CLit y) end
  | FOZero => tZeroP
  | FOSucc a => tSuccP (cpat_tm rho a)
  | FOPlus a b => tPlusP (cpat_tm rho a) (cpat_tm rho b)
  | FOMult a b => tMultP (cpat_tm rho a) (cpat_tm rho b)
  end.

Fixpoint cpat_f (rho : nat -> option nat) (A : FOFormula) : CPat :=
  match A with
  | FOEq a b => pEqP (cpat_tm rho a) (cpat_tm rho b)
  | FOFalseF => pFlsP
  | FOImplF B C => pImpP (cpat_f rho B) (cpat_f rho C)
  | FOForall y B => pAllP (CLit y) (cpat_f (rho_hide y rho) B)
  | FOExists y B => pExP (CLit y) (cpat_f (rho_hide y rho) B)
  end.

Lemma cpat_tm_ext : forall t rho rho', (forall z, rho z = rho' z) ->
  cpat_tm rho t = cpat_tm rho' t.
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros rho rho' H; cbn [cpat_tm].
  - rewrite H. reflexivity.
  - reflexivity.
  - rewrite (IH rho rho' H). reflexivity.
  - rewrite (IHa rho rho' H), (IHb rho rho' H). reflexivity.
  - rewrite (IHa rho rho' H), (IHb rho rho' H). reflexivity.
Qed.

Lemma rho_hide_ext : forall y rho rho', (forall z, rho z = rho' z) ->
  forall z, rho_hide y rho z = rho_hide y rho' z.
Proof. intros y rho rho' H z. unfold rho_hide. destruct (Nat.eqb z y); [reflexivity | apply H]. Qed.

Lemma cpat_f_ext : forall A rho rho', (forall z, rho z = rho' z) ->
  cpat_f rho A = cpat_f rho' A.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros rho rho' H; cbn [cpat_f].
  - rewrite (cpat_tm_ext a rho rho' H), (cpat_tm_ext b rho rho' H). reflexivity.
  - reflexivity.
  - rewrite (IHB rho rho' H), (IHC rho rho' H). reflexivity.
  - rewrite (IHB _ _ (rho_hide_ext y rho rho' H)). reflexivity.
  - rewrite (IHB _ _ (rho_hide_ext y rho rho' H)). reflexivity.
Qed.

Lemma cpat_tm_closed_sem : forall t rho sigma, (forall z, rho z = None) ->
  cpat_sem sigma (cpat_tm rho t) = FOcode_tm t.
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros rho sigma H;
    cbn [cpat_tm cpat_sem FOcode_tm tVarP tZeroP tSuccP tPlusP tMultP].
  - rewrite H. reflexivity.
  - reflexivity.
  - rewrite IH by exact H. reflexivity.
  - rewrite IHa, IHb by exact H. reflexivity.
  - rewrite IHa, IHb by exact H. reflexivity.
Qed.

Lemma cpat_f_closed_sem : forall A rho sigma, (forall z, rho z = None) ->
  cpat_sem sigma (cpat_f rho A) = FOcode_f A.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros rho sigma H;
    cbn [cpat_f cpat_sem FOcode_f pEqP pFlsP pImpP pAllP pExP].
  - rewrite !cpat_tm_closed_sem by exact H. reflexivity.
  - reflexivity.
  - rewrite IHB, IHC by exact H. reflexivity.
  - rewrite IHB; [reflexivity|]. intros z. unfold rho_hide. destruct (Nat.eqb z y); auto.
  - rewrite IHB; [reflexivity|]. intros z. unfold rho_hide. destruct (Nat.eqb z y); auto.
Qed.

(** ** Pairing: congruence and functionality. *)

Lemma FOPrH_cpairF_cong : forall n G a b c a' b' c',
  FOPrH n G (FOEq a a') -> FOPrH n G (FOEq b b') -> FOPrH n G (FOEq c c') ->
  FOPrH n G (FOcpairF a b c) -> FOPrH n G (FOcpairF a' b' c').
Proof.
  intros n G a b c a' b' c' E1 E2 E3 H. unfold FOcpairF in *.
  pose proof (FOPrH_congPlus _ _ _ _ _ _ E1 E2) as Eab.
  pose proof (FOPrH_congMult _ _ _ _ _ _ Eab (FOPrH_congS _ _ _ _ Eab)) as Em.
  pose proof (FOPrH_congPlus _ _ _ _ _ _ Em (FOPrH_congPlus _ _ _ _ _ _ E2 E2)) as Er.
  pose proof (FOPrH_congPlus _ _ _ _ _ _ E3 E3) as Ec.
  exact (FOPrH_eq_trans _ _ _ _ _ (FOPrH_eq_sym _ _ _ _ Ec) (FOPrH_eq_trans _ _ _ _ _ H Er)).
Qed.

Lemma FOPrH_cpair_fun : forall n G a b c c',
  FOtms_avoid [c; c'] 440 442 ->
  FOPrH n G (FOcpairF a b c) -> FOPrH n G (FOcpairF a b c') -> FOPrH n G (FOEq c c').
Proof.
  intros n G a b c c' Hav H1 H2.
  assert (E : FOPrH n G (FOEq (FOPlus c c) (FOPlus c' c'))).
  { unfold FOcpairF in H1, H2. exact (FOPrH_eq_trans _ _ _ _ _ H1 (FOPrH_eq_sym _ _ _ _ H2)). }
  assert (Vc : FOtm_avoid c 440 442) by avoid_tm.
  assert (Vc' : FOtm_avoid c' 440 442) by avoid_tm.
  pose proof (FOPrH_thm n G _ (FOPr_double_inj n)) as D.
  apply (FOPrH_inst n G 440 c) in D;
    [| cbn [FOsubst_ok FOfree_in FOin_tm orb negb andb Nat.eqb];
       rewrite (Vc 441 ltac:(lia) ltac:(lia)); reflexivity].
  cbn [FOsubst_f FOsubst_t Nat.eqb] in D.
  apply (FOPrH_inst n G 441 c') in D; [|cbn [FOsubst_ok]; reflexivity].
  cbn [FOsubst_f FOsubst_t Nat.eqb] in D.
  rewrite (FOsubst_t_not_in c 441 c' (Vc 441 ltac:(lia) ltac:(lia))) in D.
  exact (FOPrH_mp _ _ _ _ D E).
Qed.

(** ** Pattern nodes decomposed at their own bound variables.

    The two witnesses of a pair node at base [B] are named by the
    variables [B] and [B + 2] that bind them; the sub-patterns sit at
    higher bases, so the names stay out of every region still to be
    decomposed. *)

Lemma FOPrH_patf_pair_elim_self : forall n G B env a b d C,
  FOPrH n G (FOPATF B env (CPair a b) d) ->
  500 <= B ->
  FOctx_avoid G B (B + cpat_span (CPair a b)) ->
  (forall w, B <= w -> w < B + cpat_span (CPair a b) -> FOfree_in w C = false) ->
  FOtms_avoid (d :: env) B (B + cpat_span (CPair a b)) ->
  FOPrH n (G ++ [FOAnd (FOcpairF (FOVar B) (FOVar (B + 2)) d)
                   (FOAnd (FOPATF (B + 4) env a (FOVar B))
                          (FOPATF (B + 4 + 4 * cpat_pairs a) env b (FOVar (B + 2))))]) C ->
  FOPrH n G C.
Proof.
  intros n G B env a b d C H HB HG HC Hav H0.
  pose proof (cpat_span_le a) as Ha. cbn [cpat_span] in HG, HC, Hav.
  assert (Hd : FOtm_avoid d B (B + (4 + 4 * cpat_pairs a + cpat_span b)))
    by (apply Hav; left; reflexivity).
  cbn [FOPATF] in H. rewrite FOBexC_ltv in H.
  refine (FOPrH_ex_elim n G B _ C (HG B ltac:(lia) ltac:(lia)) (HC B ltac:(lia) ltac:(lia))
            H _).
  lazymatch goal with |- FOPrH _ (_ ++ [?X]) _ =>
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G X)) as H1 end.
  rewrite FOBexC_ltv in H1.
  refine (FOPrH_ex_elim n _ (B + 2) _ C _ (HC (B + 2) ltac:(lia) ltac:(lia)) H1 _).
  { apply FOfree_ctx_app_inv; [apply HG; lia|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
    rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    - apply FOfree_in_ltv; [lia|]. rewrite FOin_tm_succ_eq. apply Hd; lia.
    - try rewrite FOBexC_ltv. apply FOfree_in_ex_self. }
  refine (FOPrH_cut _ _ _ C (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _)) _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
  - apply in_or_app. left. apply in_or_app. left. apply in_or_app. left. exact HX.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_patf_succ_elim_self : forall n G B env q d C,
  FOPrH n G (FOPATF B env (CSuccP q) d) ->
  500 <= B ->
  FOctx_avoid G B (B + cpat_span (CSuccP q)) ->
  (forall w, B <= w -> w < B + cpat_span (CSuccP q) -> FOfree_in w C = false) ->
  FOtms_avoid (d :: env) B (B + cpat_span (CSuccP q)) ->
  FOPrH n (G ++ [FOAnd (FOEq d (FOSucc (FOVar B))) (FOPATF (B + 2) env q (FOVar B))]) C ->
  FOPrH n G C.
Proof.
  intros n G B env q d C H HB HG HC Hav H0.
  cbn [cpat_span] in HG, HC, Hav.
  cbn [FOPATF] in H. rewrite FOBexC_ltv in H.
  refine (FOPrH_ex_elim n G B _ C (HG B ltac:(lia) ltac:(lia)) (HC B ltac:(lia) ltac:(lia))
            H _).
  refine (FOPrH_cut _ _ _ C (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _)) _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
  - apply in_or_app. left. apply in_or_app. left. exact HX.
  - apply in_or_app. right. left. reflexivity.
Qed.

(** A pair node whose left component is a literal. *)

Lemma FOPrH_patf_lit_elim : forall n G B env k q d C,
  FOPrH n G (FOPATF B env (CPair (CLit k) q) d) ->
  500 <= B ->
  FOctx_avoid G B (B + cpat_span (CPair (CLit k) q)) ->
  (forall w, B <= w -> w < B + cpat_span (CPair (CLit k) q) -> FOfree_in w C = false) ->
  FOtms_avoid (d :: env) B (B + cpat_span (CPair (CLit k) q)) ->
  FOPrH n (G ++ [FOcpairF (FOnumeral k) (FOVar (B + 2)) d;
                 FOPATF (B + 4) env q (FOVar (B + 2))]) C ->
  FOPrH n G C.
Proof.
  intros n G B env k q d C H HB HG HC Hav H0.
  apply (FOPrH_patf_pair_elim_self n G B env (CLit k) q d C H HB HG HC Hav).
  replace (B + 4 + 4 * cpat_pairs (CLit k)) with (B + 4) by (cbn [cpat_pairs]; lia).
  lazymatch goal with |- FOPrH _ (_ ++ [?X]) _ => pose proof (FOPrH_last n G X) as HX end.
  cbn [FOPATF] in HX.
  pose proof (FOPrH_and_l _ _ _ _ HX) as Hc.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HX)) as Ek.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HX)) as Hq.
  pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ Ek (FOPrH_refl _ _ _) (FOPrH_refl _ _ _) Hc)
    as Hc'.
  refine (FOPrH_cut _ _ _ C Hc' _).
  refine (FOPrH_cut _ _ _ C (FOPrH_weak_app _ _ _ _ Hq) _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros Y HY. apply in_app_or in HY. destruct HY as [HY|[<-|[<-|[]]]].
  - apply in_or_app. left. apply in_or_app. left. apply in_or_app. left. exact HY.
  - apply in_or_app. left. apply in_or_app. right. left. reflexivity.
  - apply in_or_app. right. left. reflexivity.
Qed.

(** ** Avoidance for sublists. *)

Lemma FOtms_avoid_incl : forall L L' lo hi lo' hi',
  FOtms_avoid L' lo hi -> (forall t, In t L -> In t L') -> lo <= lo' -> hi' <= hi ->
  FOtms_avoid L lo' hi'.
Proof.
  intros L L' lo hi lo' hi' H Hinc H1 H2 t Ht.
  exact (FOtm_avoid_sub t lo hi lo' hi' (H t (Hinc t Ht)) H1 H2).
Qed.

Ltac avoid_tms ::=
  lazymatch goal with
  | |- FOtms_avoid (_ ++ _) _ _ => apply FOtms_avoid_app; avoid_tms
  | |- FOtms_avoid (_ :: _) _ _ => apply FOtms_avoid_cons; [avoid_tm | avoid_tms]
  | |- FOtms_avoid [] _ _ => apply FOtms_avoid_nil
  | |- FOtms_avoid (FOtab_terms ?T) ?lo ?hi =>
      match goal with
      | H : FOtms_avoid ?L ?lo' ?hi' |- _ =>
          apply (FOtms_avoid_sub _ lo' hi' lo hi); [|lia|lia];
          intros u Hu; apply H; simpl in Hu |- *; tauto
      end
  | |- FOtms_avoid ?L ?lo ?hi =>
      match goal with
      | H : FOtms_avoid ?L' ?lo' ?hi' |- _ =>
          apply (FOtms_avoid_incl L L' lo' hi' lo hi H);
          [ let t := fresh "t" in let Ht := fresh "Ht" in
            intros t Ht; clear -Ht; cbn [In] in *; repeat rewrite in_app_iff in *;
            cbn [In] in *; tauto
          | nat_fast | nat_fast]
      end
  end.

(** ** Introduction of a successor node. *)

Lemma FOPrH_patf_succ_intro : forall n G B env q d u,
  FOPrH n G (FOEq d (FOSucc u)) -> FOPrH n G (FOPATF (B + 2) env q u) ->
  500 <= B ->
  FOtms_avoid (d :: u :: env) B (B + cpat_span (CSuccP q)) ->
  FOtms_avoid [d; u] 420 500 ->
  FOPrH n G (FOPATF B env (CSuccP q) d).
Proof.
  intros n G B env q d u E Hq HB Hav Hav2.
  cbn [cpat_span] in Hav. cbn [FOPATF].
  apply (FOPrH_bex_intro_t _ _ B d u); [lia | lia | avoid_tm | avoid_tm | avoid_tm
    | avoid_tm | | | ].
  - apply (FOPrH_le_of_eq n G (FOSucc u) d FOZero); [|avoid_tms].
    exact (FOPrH_eq_trans _ _ _ _ _ (FOPrH_Q_plus_zero _ _ _) (FOPrH_eq_sym _ _ _ _ E)).
  - apply FOsubst_ok_and; [apply FOsubst_ok_eq|]. apply FOsubst_ok_PATF.
    apply (FOtm_avoid_sub u B (B + (2 + cpat_span q)));
      [apply Hav; right; left; reflexivity | lia | lia].
  - rewrite FOsubst_f_and, FOsubst_f_eq, FOsubst_t_succ, FOsubst_t_var_eq'.
    rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
    rewrite (FOsubst_t_not_in d B _ (Hav d (or_introl eq_refl) B ltac:(lia) ltac:(lia))).
    rewrite (FOsubst_map_avoid B u env)
      by (intros t Ht; apply (Hav t); [right; right; exact Ht | lia | lia]).
    apply FOPrH_and_intro; [exact E | exact Hq].
Qed.

(** ** Codes matching a pattern are equal. *)

Lemma FOPrH_patf_unique : forall p n G B B' env d d',
  FOPrH n G (FOPATF B env p d) -> FOPrH n G (FOPATF B' env p d') ->
  500 <= B -> 500 <= B' -> B + cpat_span p <= B' \/ B' + cpat_span p <= B ->
  FOctx_avoid G B (B + cpat_span p) -> FOctx_avoid G B' (B' + cpat_span p) ->
  FOtms_avoid (d :: d' :: env) B (B + cpat_span p) ->
  FOtms_avoid (d :: d' :: env) B' (B' + cpat_span p) ->
  FOtms_avoid [d; d'] 440 442 ->
  FOPrH n G (FOEq d d').
Proof.
  induction p as [k|i|q IH|a IHa b IHb];
    intros n G B B' env d d' H H' HB HB' Hdis HG HG' Hav Hav' Hd.
  - cbn [FOPATF] in H, H'. exact (FOPrH_eq_trans _ _ _ _ _ H (FOPrH_eq_sym _ _ _ _ H')).
  - cbn [FOPATF] in H, H'. exact (FOPrH_eq_trans _ _ _ _ _ H (FOPrH_eq_sym _ _ _ _ H')).
  - cbn [cpat_span] in Hdis, HG, HG', Hav, Hav'.
    apply (FOPrH_patf_succ_elim_self n G B env q d _ H HB);
      [cbn [cpat_span]; exact HG | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    apply (FOPrH_patf_succ_elim_self n _ B' env q d' _ (FOPrH_weak_app _ _ _ _ H') HB');
      [cbn [cpat_span]; ctx_list | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    lazymatch goal with |- FOPrH _ ((?G0 ++ [?X]) ++ [?X']) _ =>
      pose proof (FOPrH_weak_app _ _ [X'] _ (FOPrH_last n G0 X)) as HX;
      pose proof (FOPrH_last n (G0 ++ [X]) X') as HX'
    end.
    pose proof (IH n _ (B + 2) (B' + 2) env (FOVar B) (FOVar B')
                  (FOPrH_and_r _ _ _ _ HX) (FOPrH_and_r _ _ _ _ HX')
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as E.
    exact (FOPrH_eq_trans _ _ _ _ _ (FOPrH_and_l _ _ _ _ HX)
             (FOPrH_eq_trans _ _ _ _ _ (FOPrH_congS _ _ _ _ E)
                (FOPrH_eq_sym _ _ _ _ (FOPrH_and_l _ _ _ _ HX')))).
  - pose proof (cpat_span_le a) as Hsa. cbn [cpat_span] in Hdis, HG, HG', Hav, Hav'.
    apply (FOPrH_patf_pair_elim_self n G B env a b d _ H HB);
      [cbn [cpat_span]; exact HG | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    apply (FOPrH_patf_pair_elim_self n _ B' env a b d' _ (FOPrH_weak_app _ _ _ _ H') HB');
      [cbn [cpat_span]; ctx_list | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    lazymatch goal with |- FOPrH _ ((?G0 ++ [?X]) ++ [?X']) _ =>
      pose proof (FOPrH_weak_app _ _ [X'] _ (FOPrH_last n G0 X)) as HX;
      pose proof (FOPrH_last n (G0 ++ [X]) X') as HX'
    end.
    pose proof (IHa n _ (B + 4) (B' + 4) env (FOVar B) (FOVar B')
                  (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HX))
                  (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HX'))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Ea.
    pose proof (IHb n _ (B + 4 + 4 * cpat_pairs a) (B' + 4 + 4 * cpat_pairs a) env
                  (FOVar (B + 2)) (FOVar (B' + 2))
                  (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HX))
                  (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HX'))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Eb.
    pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ Ea Eb (FOPrH_refl _ _ _)
                  (FOPrH_and_l _ _ _ _ HX)) as Hc.
    exact (FOPrH_cpair_fun n _ (FOVar B') (FOVar (B' + 2)) d d' ltac:(avoid_tms) Hc
             (FOPrH_and_l _ _ _ _ HX')).
Qed.

(** ** A pattern fact moved to another base. *)

Lemma FOPrH_patf_rebase : forall p n G B B' env d,
  FOPrH n G (FOPATF B env p d) ->
  500 <= B -> 500 <= B' -> B + cpat_span p <= B' \/ B' + cpat_span p <= B ->
  FOctx_avoid G B (B + cpat_span p) ->
  FOtms_avoid (d :: env) B (B + cpat_span p) ->
  FOtms_avoid (d :: env) B' (B' + cpat_span p) ->
  FOtms_avoid (d :: env) 420 500 ->
  FOPrH n G (FOPATF B' env p d).
Proof.
  induction p as [k|i|q IH|a IHa b IHb]; intros n G B B' env d H HB HB' Hdis HG Hav Hav' Hav2.
  - exact H.
  - exact H.
  - cbn [cpat_span] in Hdis, HG, Hav, Hav'.
    apply (FOPrH_patf_succ_elim_self n G B env q d _ H HB);
      [cbn [cpat_span]; exact HG | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G0 ++ [?X]) _ => pose proof (FOPrH_last n G0 X) as HX end.
    pose proof (IH n _ (B + 2) (B' + 2) env (FOVar B) (FOPrH_and_r _ _ _ _ HX)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hq.
    apply (FOPrH_patf_succ_intro n _ B' env q d (FOVar B) (FOPrH_and_l _ _ _ _ HX) Hq HB');
      [cbn [cpat_span]; avoid_tms | avoid_tms].
  - pose proof (cpat_span_le a) as Hsa. cbn [cpat_span] in Hdis, HG, Hav, Hav'.
    apply (FOPrH_patf_pair_elim_self n G B env a b d _ H HB);
      [cbn [cpat_span]; exact HG | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G0 ++ [?X]) _ => pose proof (FOPrH_last n G0 X) as HX end.
    pose proof (IHa n _ (B + 4) (B' + 4) env (FOVar B)
                  (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HX))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Ha.
    pose proof (IHb n _ (B + 4 + 4 * cpat_pairs a) (B' + 4 + 4 * cpat_pairs a) env
                  (FOVar (B + 2)) (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HX))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hb.
    apply (FOPrH_patf_pair_intro n _ B' env a b d (FOVar B) (FOVar (B + 2))
             (FOPrH_and_l _ _ _ _ HX) Ha Hb ltac:(lia));
      [cbn [cpat_span]; avoid_tms | avoid_tms].
Qed.

(** ** Every pattern has a code.

    The code is named [z]; the recursion names the component codes
    [z + 1] and [z + 2], all below the pattern's base. *)

Lemma FOPrH_patf_total : forall p n G B env z,
  1000 <= z -> z + 3 <= B ->
  FOctx_avoid G z (z + 3) -> FOctx_avoid G 420 500 ->
  FOtms_avoid env B (B + cpat_span p) -> FOtms_avoid env z (z + 3) ->
  FOtms_avoid env 420 500 ->
  FOPrH n G (FOExists z (FOPATF B env p (FOVar z))).
Proof.
  induction p as [k|i|q IH|a IHa b IHb]; intros n G B env z Hz HzB HG HG2 Hav Havz Hav2.
  - apply (FOPrH_ex_intro _ _ z (FOnumeral k)); [cbn [FOPATF]; apply FOsubst_ok_eq|].
    cbn [FOPATF]. rewrite FOsubst_f_eq, FOsubst_t_var_eq', FOsubst_t_numeral.
    apply FOPrH_refl.
  - apply (FOPrH_ex_intro _ _ z (nth i env FOZero)); [cbn [FOPATF]; apply FOsubst_ok_eq|].
    cbn [FOPATF]. rewrite FOsubst_f_eq, FOsubst_t_var_eq'.
    rewrite FOsubst_t_not_in; [apply FOPrH_refl|].
    destruct (nth_in_or_default i env FOZero) as [Hin| ->]; [|reflexivity].
    apply (Havz _ Hin); lia.
  - cbn [cpat_span] in Hav.
    pose proof (IH n G (B + 2) env z Hz ltac:(lia) HG HG2 ltac:(avoid_tms) Havz Hav2) as Hq.
    refine (FOPrH_exe n G z (z + 1) _ _ Hq _ _ _ _ _);
      [apply HG; lia | free_fm | free_fm | apply FOsubst_ok_PATF; avoid_tm |].
    rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
    rewrite (FOsubst_map_avoid z _ env) by (intros t Ht; apply (Havz t Ht); lia).
    apply (FOPrH_ex_intro _ _ z (FOSucc (FOVar (z + 1))));
      [apply FOsubst_ok_PATF; cbn [cpat_span]; avoid_tm|].
    rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
    rewrite (FOsubst_map_avoid z _ env) by (intros t Ht; apply (Havz t Ht); lia).
    apply (FOPrH_patf_succ_intro n _ B env q (FOSucc (FOVar (z + 1))) (FOVar (z + 1)));
      [apply FOPrH_refl | apply FOPrH_last | lia | cbn [cpat_span]; avoid_tms | avoid_tms].
  - pose proof (cpat_span_le a) as Hsa. cbn [cpat_span] in Hav.
    pose proof (IHa n G (B + 4) env z Hz ltac:(lia) HG HG2 ltac:(avoid_tms) Havz Hav2) as Ha.
    pose proof (IHb n G (B + 4 + 4 * cpat_pairs a) env z Hz ltac:(lia) HG HG2 ltac:(avoid_tms)
                  Havz Hav2) as Hb.
    refine (FOPrH_exe n G z (z + 1) _ _ Ha _ _ _ _ _);
      [apply HG; lia | free_fm | free_fm | apply FOsubst_ok_PATF; avoid_tm |].
    rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
    rewrite (FOsubst_map_avoid z _ env) by (intros t Ht; apply (Havz t Ht); lia).
    refine (FOPrH_exe n _ z (z + 2) _ _ (FOPrH_weak_app _ _ _ _ Hb) _ _ _ _ _);
      [free_ctx | free_fm | free_fm | apply FOsubst_ok_PATF; avoid_tm |].
    rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
    rewrite (FOsubst_map_avoid z _ env) by (intros t Ht; apply (Havz t Ht); lia).
    apply (FOPrH_cpair_elim_hi n _ (FOVar (z + 1)) (FOVar (z + 2)) z);
      [ctx_list | avoid_tms | lia | free_ctx | free_fm | avoid_tms |].
    apply (FOPrH_ex_intro _ _ z (FOVar z)); [apply FOsubst_ok_var_self|].
    rewrite FOsubst_f_id.
    apply (FOPrH_patf_pair_intro n _ B env a b (FOVar z) (FOVar (z + 1)) (FOVar (z + 2)));
      [apply FOPrH_last | wk_in | wk_in | lia | cbn [cpat_span]; avoid_tms | avoid_tms].
Qed.


(** ** Rows rewritten along equations of their last two fields. *)

Lemma FOPrH_tblex_cong : forall n G tg a1 a2 a3 r a3' r',
  FOPrH n G (FOTBLEX tg a1 a2 a3 r) ->
  FOPrH n G (FOEq a3 a3') -> FOPrH n G (FOEq r r') ->
  FOtms_avoid [tg; a1; a2; a3; r; a3'; r'] 2 1000 ->
  FOPrH n G (FOTBLEX tg a1 a2 a3' r').
Proof.
  intros n G tg a1 a2 a3 r a3' r' H E1 E2 Hav.
  assert (K1 : forall t, FOtm_avoid t 2 1000 ->
             FOsubst_f 999 t (FOTBLEX tg a1 a2 (FOVar 999) r) = FOTBLEX tg a1 a2 t r).
  { intros t Ht. rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq'.
    rewrite !(FOsubst_t_not_in _ 999 t) by fr_tm. reflexivity. }
  assert (K2 : forall t, FOtm_avoid t 2 1000 ->
             FOsubst_f 999 t (FOTBLEX tg a1 a2 a3' (FOVar 999)) = FOTBLEX tg a1 a2 a3' t).
  { intros t Ht. rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq'.
    rewrite !(FOsubst_t_not_in _ 999 t) by fr_tm. reflexivity. }
  assert (V3 : FOtm_avoid a3 2 1000) by avoid_tm.
  assert (V3' : FOtm_avoid a3' 2 1000) by avoid_tm.
  assert (Vr : FOtm_avoid r 2 1000) by avoid_tm.
  assert (Vr' : FOtm_avoid r' 2 1000) by avoid_tm.
  pose proof (FOPrH_leibniz n G 999 a3 a3' (FOTBLEX tg a1 a2 (FOVar 999) r)
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm]) E1) as L1.
  rewrite (K1 a3 V3), (K1 a3' V3') in L1. specialize (L1 H).
  pose proof (FOPrH_leibniz n G 999 r r' (FOTBLEX tg a1 a2 a3' (FOVar 999))
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm]) E2) as L2.
  rewrite (K2 r Vr), (K2 r' Vr') in L2. exact (L2 L1).
Qed.

(** ** The rows a numeral code carries. *)

Lemma FOPrH_numr_row2 : forall n G w m X s,
  FOPrH n G (FONUMR w m) -> FOtms_avoid [m; X; s] 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s m m).
Proof.
  intros n G w m X s H Hav.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ H)) as H2.
  apply (FOPrH_inst n G 802 X) in H2;
    [| apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_TBLEX; [lia | avoid_tm]].
  rewrite FOsubst_f_all_ne, FOsubst_f_TBLEX in H2 by lia.
  rewrite FOsubst_t_var_eq', FOsubst_t_var_ne, FOsubst_t_numeral in H2 by lia.
  rewrite (FOsubst_t_not_in m 802 X) in H2 by fr_tm.
  apply (FOPrH_inst n G 803 s) in H2; [| apply FOsubst_ok_TBLEX; [lia | avoid_tm]].
  rewrite FOsubst_f_TBLEX in H2 by lia.
  rewrite FOsubst_t_var_eq', FOsubst_t_numeral in H2.
  rewrite (FOsubst_t_not_in X 803 s), (FOsubst_t_not_in m 803 s) in H2 by fr_tm.
  exact H2.
Qed.

Lemma FOPrH_numr_row0 : forall n G w m y,
  FOPrH n G (FONUMR w m) -> FOtms_avoid [m; y] 2 1000 ->
  FOPrH n G (FOTBLEX FOZero y m FOZero FOZero).
Proof.
  intros n G w m y H Hav.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ H)) as H0.
  apply (FOPrH_inst n G 804 y) in H0; [| apply FOsubst_ok_TBLEX; [lia | avoid_tm]].
  rewrite FOsubst_f_TBLEX in H0 by lia.
  rewrite FOsubst_t_var_eq', FOsubst_t_zero in H0.
  rewrite (FOsubst_t_not_in m 804 y) in H0 by fr_tm.
  exact H0.
Qed.

(** ** Pattern nodes of the code shapes. *)

Lemma FOPrH_patf_leaf_elim : forall n G B env k y d C,
  FOPrH n G (FOPATF B env (CPair (CLit k) (CLit y)) d) ->
  500 <= B -> FOctx_avoid G B (B + 4) ->
  (forall w, B <= w -> w < B + 4 -> FOfree_in w C = false) ->
  FOtms_avoid (d :: env) B (B + 4) ->
  FOPrH n (G ++ [FOcpairF (FOnumeral k) (FOnumeral y) d]) C ->
  FOPrH n G C.
Proof.
  intros n G B env k y d C H HB HG HC Hav H0.
  apply (FOPrH_patf_lit_elim n G B env k (CLit y) d C H HB HG HC Hav).
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (H1 : FOPrH n G1 (FOcpairF (FOnumeral k) (FOVar (B + 2)) d)) by wk_in;
    assert (H2 : FOPrH n G1 (FOEq (FOVar (B + 2)) (FOnumeral y))) by wk_in
  end.
  refine (FOPrH_cut _ _ _ C (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ (FOPrH_refl _ _ _) H2
                                (FOPrH_refl _ _ _) H1) _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros Y HY. apply in_app_or in HY. destruct HY as [HY|[<-|[]]].
  - apply in_or_app. left. apply in_or_app. left. exact HY.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_patf_bin_elim : forall n G B env k P Q d C,
  FOPrH n G (FOPATF B env (CPair (CLit k) (CPair P Q)) d) ->
  500 <= B -> FOctx_avoid G B (B + cpat_span (CPair (CLit k) (CPair P Q))) ->
  (forall w, B <= w -> w < B + cpat_span (CPair (CLit k) (CPair P Q)) ->
     FOfree_in w C = false) ->
  FOtms_avoid (d :: env) B (B + cpat_span (CPair (CLit k) (CPair P Q))) ->
  FOPrH n (G ++ [FOcpairF (FOnumeral k) (FOVar (B + 2)) d;
                 FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2));
                 FOPATF (B + 8) env P (FOVar (B + 4));
                 FOPATF (B + 8 + 4 * cpat_pairs P) env Q (FOVar (B + 6))]) C ->
  FOPrH n G C.
Proof.
  intros n G B env k P Q d C H HB HG HC Hav H0.
  pose proof (cpat_span_le P) as HsP.
  apply (FOPrH_patf_lit_elim n G B env k (CPair P Q) d C H HB HG HC Hav).
  cbn [cpat_span cpat_pairs] in HG, HC, Hav.
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (H1 : FOPrH n G1 (FOPATF (B + 4) env (CPair P Q) (FOVar (B + 2)))) by wk_in
  end.
  apply (FOPrH_patf_pair_elim_self n _ (B + 4) env P Q (FOVar (B + 2)) C H1 ltac:(lia));
    [cbn [cpat_span]; ctx_list | intros w Hw1 Hw2; cbn [cpat_span] in Hw2; apply HC; lia
    | cbn [cpat_span]; avoid_tms |].
  replace (B + 4 + 4) with (B + 8) by lia.
  replace (B + 4 + 2) with (B + 6) by lia.
  replace (B + 8 + 4 * cpat_pairs P) with (B + 8 + 4 * cpat_pairs P) by lia.
  lazymatch goal with |- FOPrH _ (?G2 ++ [?X]) _ =>
    pose proof (FOPrH_last n G2 X) as HX
  end.
  refine (FOPrH_cut _ _ _ C (FOPrH_and_l _ _ _ _ HX) _).
  refine (FOPrH_cut _ _ _ C (FOPrH_weak_app _ _ _ _
            (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HX))) _).
  refine (FOPrH_cut _ _ _ C (FOPrH_weak_app _ _ _ _ (FOPrH_weak_app _ _ _ _
            (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HX)))) _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros Y HY. rewrite <- !app_assoc in *. cbn [app] in *.
  apply in_app_or in HY. destruct HY as [HY|HY]; [apply in_or_app; left; exact HY|].
  apply in_or_app. right. cbn [In] in HY |- *. tauto.
Qed.

Lemma FOPrH_patf_quant_elim : forall n G B env k y P d C,
  FOPrH n G (FOPATF B env (CPair (CLit k) (CPair (CLit y) P)) d) ->
  500 <= B -> FOctx_avoid G B (B + cpat_span (CPair (CLit k) (CPair (CLit y) P))) ->
  (forall w, B <= w -> w < B + cpat_span (CPair (CLit k) (CPair (CLit y) P)) ->
     FOfree_in w C = false) ->
  FOtms_avoid (d :: env) B (B + cpat_span (CPair (CLit k) (CPair (CLit y) P))) ->
  FOPrH n (G ++ [FOcpairF (FOnumeral k) (FOVar (B + 2)) d;
                 FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2));
                 FOPATF (B + 8) env P (FOVar (B + 6))]) C ->
  FOPrH n G C.
Proof.
  intros n G B env k y P d C H HB HG HC Hav H0.
  apply (FOPrH_patf_lit_elim n G B env k (CPair (CLit y) P) d C H HB HG HC Hav).
  cbn [cpat_span cpat_pairs] in HG, HC, Hav.
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (H1 : FOPrH n G1 (FOPATF (B + 4) env (CPair (CLit y) P) (FOVar (B + 2)))) by wk_in
  end.
  apply (FOPrH_patf_lit_elim n _ (B + 4) env y P (FOVar (B + 2)) C H1 ltac:(lia));
    [cbn [cpat_span cpat_pairs]; ctx_list
    | intros w Hw1 Hw2; cbn [cpat_span cpat_pairs] in Hw2; apply HC; lia
    | cbn [cpat_span cpat_pairs]; avoid_tms |].
  replace (B + 4 + 4) with (B + 8) by lia.
  replace (B + 4 + 2) with (B + 6) by lia.
  refine (FOPrH_weaken n _ _ C _ H0).
  intros Y HY. rewrite <- !app_assoc in *. cbn [app] in *.
  apply in_app_or in HY. destruct HY as [HY|HY]; [apply in_or_app; left; exact HY|].
  apply in_or_app. right. cbn [In] in HY |- *. tauto.
Qed.

(** ** Substitution rows for the code of a term.

    [ox = Some x]: the row substitutes the code [s] (a new slot [j] of
    the target) for the variable [x]; [ox = None]: the row substitutes
    at a variable [X] above every variable of the code, and source and
    target coincide.  [Xb] bounds the source code from above; every
    literal variable [y] below [Xb] other than [x] differs from [X]. *)

Definition rho_sub (ox : option nat) (j : nat) (rho : nat -> option nat) : nat -> option nat :=
  match ox with
  | Some x => fun z => if Nat.eqb z x then Some j else rho z
  | None => rho
  end.

Definition ox_eq (ox : option nat) (y : nat) : bool :=
  match ox with Some x => Nat.eqb y x | None => false end.

Lemma rho_sub_hide : forall ox j rho y, ox_eq ox y = false ->
  forall z, rho_sub ox j (rho_hide y rho) z = rho_hide y (rho_sub ox j rho) z.
Proof.
  intros [x|] j rho y H z; cbn [rho_sub ox_eq] in *; unfold rho_hide; [|reflexivity].
  destruct (Nat.eqb z y) eqn:Ezy; destruct (Nat.eqb z x) eqn:Ezx; try reflexivity.
  apply Nat.eqb_eq in Ezy, Ezx. subst. rewrite Nat.eqb_refl in H. discriminate.
Qed.

Lemma rho_hide_sub_self : forall x j rho z,
  rho_hide x (rho_sub (Some x) j rho) z = rho_hide x rho z.
Proof.
  intros x j rho z. unfold rho_hide, rho_sub. destruct (Nat.eqb_spec z x); reflexivity.
Qed.

Definition RowEnv (ox : option nat) (X Xb s : FOTerm) (env env' : list FOTerm) (j : nat)
  : Prop :=
  (forall i, i < length env -> nth i env' FOZero = nth i env FOZero) /\
  (match ox with Some _ => nth j env' FOZero = s | None => True end) /\
  (match ox with Some x => X = FOnumeral x | None => True end) /\
  FOtms_avoid (X :: Xb :: s :: env ++ env') 2 1000.

Definition RowCtx (n : nat) (ox : option nat) (X Xb : FOTerm) (env : list FOTerm)
    (G : list FOFormula) : Prop :=
  FOctx_avoid G 2 1000 /\
  (forall i, i < length env -> exists w, FOPrH n G (FONUMR w (nth i env FOZero))) /\
  (forall G' y, (forall Y, In Y G -> In Y G') ->
     FOPrH n G' (FOle (FOSucc (FOnumeral y)) Xb) -> ox_eq ox y = false ->
     FOPrH n G' (FONeg (FOEq (FOnumeral y) X))).

Lemma RowCtx_ext : forall n ox X Xb env G L,
  RowCtx n ox X Xb env G -> FOctx_avoid L 2 1000 -> RowCtx n ox X Xb env (G ++ L).
Proof.
  intros n ox X Xb env G L [H1 [H2 H3]] HL. split; [|split].
  - intros w ? ?. apply FOfree_ctx_app_inv; [apply H1 | apply HL]; lia.
  - intros i Hi. destruct (H2 i Hi) as [w Hw]. exists w. apply FOPrH_weak_app. exact Hw.
  - intros G' y Hinc. apply H3. intros Y HY. apply Hinc. apply in_or_app. left. exact HY.
Qed.

Lemma FOPrH_le_below : forall n G u a Xb,
  FOPrH n G (FOle u a) -> FOPrH n G (FOle (FOSucc a) Xb) ->
  FOtms_avoid [u; a; Xb] 2 1000 -> FOPrH n G (FOle (FOSucc u) Xb).
Proof.
  intros n G u a Xb H1 H2 Hav.
  apply (FOPrH_le_trans n G (FOSucc u) (FOSucc a) Xb); [| exact H2 | avoid_tms].
  apply FOPrH_le_succ_of_le; [exact H1 | avoid_tms].
Qed.

Ltac rows_ctx := ctx_list.

Lemma FOPrH_rows_tm : forall n ox X Xb s env env' j t G rho B B' a c,
  RowEnv ox X Xb s env env' j -> RowCtx n ox X Xb env G ->
  (forall z i, rho z = Some i -> i < length env) ->
  match ox with Some x => rho x = None | None => True end ->
  FOPrH n G (FOPATF B env (cpat_tm rho t) a) ->
  FOPrH n G (FOPATF B' env' (cpat_tm (rho_sub ox j rho) t) c) ->
  FOPrH n G (FOle (FOSucc a) Xb) ->
  1000 <= B -> 1000 <= B' ->
  B + cpat_span (cpat_tm rho t) <= B' \/ B' + cpat_span (cpat_tm (rho_sub ox j rho) t) <= B ->
  FOctx_avoid G B (B + cpat_span (cpat_tm rho t)) ->
  FOctx_avoid G B' (B' + cpat_span (cpat_tm (rho_sub ox j rho) t)) ->
  FOtms_avoid (a :: c :: X :: Xb :: s :: env ++ env') B (B + cpat_span (cpat_tm rho t)) ->
  FOtms_avoid (a :: c :: X :: Xb :: s :: env ++ env') B'
    (B' + cpat_span (cpat_tm (rho_sub ox j rho) t)) ->
  FOtms_avoid [a; c] 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) X s a c).
Proof.
  intros n ox X Xb s env env' j t.
  induction t as [y| |u IH|u IHu w IHw|u IHu w IHw];
    intros G rho B B' a c HE HC Hrho Hrx Ha Hc Hb HB HB' Hdis HGs HGt Havs Havt Hac;
    pose proof HE as [Henv [Hj [HX Hlo]]]; pose proof HC as [HG [Hslot Hlit]].
  - (* a variable *)
    cbn [cpat_tm] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    destruct (rho y) as [i|] eqn:Ey.
    + assert (Et : rho_sub ox j rho y = Some i).
      { destruct ox as [x|]; cbn [rho_sub]; [|exact Ey].
        destruct (Nat.eqb_spec y x) as [->|Hne]; [rewrite Hrx in Ey; discriminate | exact Ey]. }
      rewrite Et in Hc. cbn [FOPATF] in Ha, Hc.
      rewrite (Henv i (Hrho y i Ey)) in Hc.
      destruct (Hslot i (Hrho y i Ey)) as [wv Hw].
      assert (Vi : FOtms_avoid [nth i env FOZero] 2 1000).
      { apply FOtms_avoid_cons; [|apply FOtms_avoid_nil]. apply Hlo.
        right. right. right. apply in_or_app. left. apply nth_In. exact (Hrho y i Ey). }
      pose proof (FOPrH_numr_row2 n G wv (nth i env FOZero) X s Hw ltac:(avoid_tms)) as R.
      exact (FOPrH_tblex_cong n G _ _ _ _ _ _ _ R (FOPrH_eq_sym _ _ _ _ Ha)
               (FOPrH_eq_sym _ _ _ _ Hc) ltac:(avoid_tms)).
    + cbn [cpat_span cpat_pairs tVarP] in Hdis, HGs, Havs.
      apply (FOPrH_patf_leaf_elim n G B env 0 y a _ Ha ltac:(lia) HGs);
        [intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm | avoid_tms |].
      lazymatch goal with |- FOPrH _ ?G1 _ =>
        assert (Hca : FOPrH n G1 (FOcpairF (FOnumeral 0) (FOnumeral y) a)) by apply FOPrH_last;
        assert (HC1 : RowCtx n ox X Xb env G1) by (apply RowCtx_ext; [exact HC | ctx_list])
      end.
      pose proof HC1 as [HG1 _].
      destruct (ox_eq ox y) eqn:Eo.
      * destruct ox as [x|]; cbn [ox_eq] in Eo; [|discriminate].
        apply Nat.eqb_eq in Eo. subst y.
        cbn [rho_sub] in Hc. rewrite Nat.eqb_refl in Hc. cbn [FOPATF] in Hc.
        rewrite Hj in Hc. subst X.
        pose proof (FOPrH_N2_var_eq n _ (FOnumeral x) s a (FOnumeral x)
                      ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Hca
                      (FOPrH_refl _ _ _)) as R.
        exact (FOPrH_tblex_cong n _ _ _ _ _ _ _ _ R (FOPrH_refl _ _ _)
                 (FOPrH_eq_sym _ _ _ _ (FOPrH_weak_app _ _ _ _ Hc)) ltac:(avoid_tms)).
      * assert (Et : rho_sub ox j rho y = None).
        { destruct ox as [x|]; cbn [rho_sub ox_eq] in *; [|exact Ey].
          rewrite Eo. exact Ey. }
        rewrite Et in Hc, HGt, Havt, Hdis. cbn beta iota in Hc, HGt, Havt, Hdis.
        cbn [cpat_span cpat_pairs tVarP] in Hdis, HGt, Havt.
        apply (FOPrH_patf_leaf_elim n _ B' env' 0 y c _ (FOPrH_weak_app _ _ _ _ Hc)
                 ltac:(lia));
          [ctx_list | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm | avoid_tms |].
        lazymatch goal with |- FOPrH _ ?G2 _ =>
          assert (Hcc : FOPrH n G2 (FOcpairF (FOnumeral 0) (FOnumeral y) c)) by apply FOPrH_last;
          assert (Hca2 : FOPrH n G2 (FOcpairF (FOnumeral 0) (FOnumeral y) a)) by wk_in;
          assert (HC2 : RowCtx n ox X Xb env G2) by (apply RowCtx_ext; [exact HC1 | ctx_list]);
          assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb
        end.
        pose proof (FOPrH_cpair_fun n _ _ _ a c ltac:(avoid_tms) Hca2 Hcc) as Eac.
        destruct (FOPrH_cpair_le_cf n _ (FOnumeral 0) (FOnumeral y) a ltac:(avoid_tms) Hca2)
          as [_ Hya].
        pose proof (FOPrH_le_below n _ _ _ _ Hya Hb2 ltac:(avoid_tms)) as Hyb.
        destruct HC2 as [HG2 [_ Hlit2]].
        pose proof (Hlit2 _ y (fun Y HY => HY) Hyb Eo) as Hne.
        pose proof (FOPrH_N2_var_ne n _ X s a (FOnumeral y) ltac:(intros w1 ? ?; apply HG2; lia)
                      ltac:(avoid_tms) Hca2 Hne) as R.
        exact (FOPrH_tblex_cong n _ _ _ _ _ _ _ _ R (FOPrH_refl _ _ _) Eac ltac:(avoid_tms)).
  - (* zero *)
    cbn [cpat_tm] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    cbn [cpat_span cpat_pairs tZeroP] in Hdis, HGs, HGt, Havs, Havt.
    apply (FOPrH_patf_leaf_elim n G B env 1 0 a _ Ha ltac:(lia) HGs);
      [intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm | avoid_tms |].
    apply (FOPrH_patf_leaf_elim n _ B' env' 1 0 c _ (FOPrH_weak_app _ _ _ _ Hc)
             ltac:(lia));
      [ctx_list | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm | avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hcc : FOPrH n G2 (FOcpairF (FOnumeral 1) (FOnumeral 0) c)) by apply FOPrH_last;
      assert (Hca : FOPrH n G2 (FOcpairF (FOnumeral 1) (FOnumeral 0) a)) by wk_in;
      assert (HG2 : FOctx_avoid G2 2 1000) by ctx_list
    end.
    pose proof (FOPrH_cpair_fun n _ _ _ a c ltac:(avoid_tms) Hca Hcc) as Eac.
    pose proof (FOPrH_N2_zero n _ X s a ltac:(intros w1 ? ?; apply HG2; lia)
                  ltac:(avoid_tms) Hca) as R.
    exact (FOPrH_tblex_cong n _ _ _ _ _ _ _ _ R (FOPrH_refl _ _ _) Eac ltac:(avoid_tms)).
  - (* successor *)
    cbn [cpat_tm tSuccP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in Hdis, HGs, HGt, Havs, Havt.
    apply (FOPrH_patf_lit_elim n G B env 2 _ a _ Ha ltac:(lia));
      [cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; exact HGs | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm
      | cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; avoid_tms |].
    apply (FOPrH_patf_lit_elim n _ B' env' 2 _ c _ (FOPrH_weak_app _ _ _ _ Hc) ltac:(lia));
      [cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; ctx_list | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm
      | cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hca : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G2 (FOPATF (B + 4) env (cpat_tm rho u) (FOVar (B + 2)))) by wk_in;
      assert (Hcc : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar (B' + 2)) c)) by wk_in;
      assert (Hpc : FOPrH n G2 (FOPATF (B' + 4) env' (cpat_tm (rho_sub ox j rho) u)
                                  (FOVar (B' + 2)))) by wk_in;
      assert (HC2 : RowCtx n ox X Xb env G2)
        by (apply RowCtx_ext; [apply RowCtx_ext; [exact HC | ctx_list] | ctx_list]);
      assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb;
      assert (HG2 : FOctx_avoid G2 2 1000) by (destruct HC2; tauto)
    end.
    destruct (FOPrH_cpair_le_cf n _ (FOnumeral 2) (FOVar (B + 2)) a ltac:(avoid_tms) Hca)
      as [_ Hua].
    pose proof (IH _ rho (B + 4) (B' + 4) (FOVar (B + 2)) (FOVar (B' + 2)) HE HC2 Hrho Hrx
                  Hpa Hpc (FOPrH_le_below n _ _ _ _ Hua Hb2 ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as R.
    exact (FOPrH_N2_succ n _ X s (FOVar (B + 2)) (FOVar (B' + 2)) a c
             ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) R Hca Hcc).
  - (* sum *)
    cbn [cpat_tm tPlusP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    pose proof (cpat_span_le (cpat_tm rho u)) as Hsu.
    pose proof (cpat_span_le (cpat_tm (rho_sub ox j rho) u)) as Hsu'.
    cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in Hdis, HGs, HGt, Havs, Havt.
    apply (FOPrH_patf_bin_elim n G B env 3 _ _ a _ Ha ltac:(lia));
      [cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; exact HGs | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm
      | cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; avoid_tms |].
    apply (FOPrH_patf_bin_elim n _ B' env' 3 _ _ c _ (FOPrH_weak_app _ _ _ _ Hc) ltac:(lia));
      [cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; ctx_list | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm
      | cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hka : FOPrH n G2 (FOcpairF (FOnumeral 3) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G2 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G2 (FOPATF (B + 8) env (cpat_tm rho u) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G2 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) env
                                  (cpat_tm rho w) (FOVar (B + 6)))) by wk_in;
      assert (Hkc : FOPrH n G2 (FOcpairF (FOnumeral 3) (FOVar (B' + 2)) c)) by wk_in;
      assert (Hpc : FOPrH n G2 (FOcpairF (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2))))
        by wk_in;
      assert (Huc : FOPrH n G2 (FOPATF (B' + 8) env' (cpat_tm (rho_sub ox j rho) u)
                                  (FOVar (B' + 4)))) by wk_in;
      assert (Hwc : FOPrH n G2 (FOPATF (B' + 8 + 4 * cpat_pairs (cpat_tm (rho_sub ox j rho) u))
                                  env' (cpat_tm (rho_sub ox j rho) w) (FOVar (B' + 6)))) by wk_in;
      assert (HC2 : RowCtx n ox X Xb env G2)
        by (apply RowCtx_ext; [apply RowCtx_ext; [exact HC | ctx_list] | ctx_list]);
      assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb;
      assert (HG2 : FOctx_avoid G2 2 1000) by (destruct HC2; tauto)
    end.
    destruct (FOPrH_cpair_le_cf n _ (FOnumeral 3) (FOVar (B + 2)) a ltac:(avoid_tms) Hka)
      as [_ Hpa'].
    destruct (FOPrH_cpair_le_cf n _ (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))
                ltac:(avoid_tms) Hpa) as [Hup Hwp].
    pose proof (FOPrH_le_below n _ _ _ _ Hpa' Hb2 ltac:(avoid_tms)) as Hpb.
    pose proof (IHu _ rho (B + 8) (B' + 8) (FOVar (B + 4)) (FOVar (B' + 4)) HE HC2 Hrho Hrx
                  Hua Huc (FOPrH_le_below n _ _ _ _ Hup Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    pose proof (IHw _ rho (B + 8 + 4 * cpat_pairs (cpat_tm rho u))
                  (B' + 8 + 4 * cpat_pairs (cpat_tm (rho_sub ox j rho) u))
                  (FOVar (B + 6)) (FOVar (B' + 6)) HE HC2 Hrho Hrx
                  Hwa Hwc (FOPrH_le_below n _ _ _ _ Hwp Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
    exact (FOPrH_N2_bin n _ X s a c 3 (FOVar (B + 2)) (FOVar (B + 4)) (FOVar (B + 6))
             (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2)) ltac:(lia)
             ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) Ru Rw Hka Hpa Hpc Hkc).
  - (* product *)
    cbn [cpat_tm tMultP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    pose proof (cpat_span_le (cpat_tm rho u)) as Hsu.
    pose proof (cpat_span_le (cpat_tm (rho_sub ox j rho) u)) as Hsu'.
    cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in Hdis, HGs, HGt, Havs, Havt.
    apply (FOPrH_patf_bin_elim n G B env 4 _ _ a _ Ha ltac:(lia));
      [cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; exact HGs | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm
      | cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; avoid_tms |].
    apply (FOPrH_patf_bin_elim n _ B' env' 4 _ _ c _ (FOPrH_weak_app _ _ _ _ Hc) ltac:(lia));
      [cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; ctx_list | intros w1 H1 H2; cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP] in H2; free_fm
      | cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP pAllP pExP]; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hka : FOPrH n G2 (FOcpairF (FOnumeral 4) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G2 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G2 (FOPATF (B + 8) env (cpat_tm rho u) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G2 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) env
                                  (cpat_tm rho w) (FOVar (B + 6)))) by wk_in;
      assert (Hkc : FOPrH n G2 (FOcpairF (FOnumeral 4) (FOVar (B' + 2)) c)) by wk_in;
      assert (Hpc : FOPrH n G2 (FOcpairF (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2))))
        by wk_in;
      assert (Huc : FOPrH n G2 (FOPATF (B' + 8) env' (cpat_tm (rho_sub ox j rho) u)
                                  (FOVar (B' + 4)))) by wk_in;
      assert (Hwc : FOPrH n G2 (FOPATF (B' + 8 + 4 * cpat_pairs (cpat_tm (rho_sub ox j rho) u))
                                  env' (cpat_tm (rho_sub ox j rho) w) (FOVar (B' + 6)))) by wk_in;
      assert (HC2 : RowCtx n ox X Xb env G2)
        by (apply RowCtx_ext; [apply RowCtx_ext; [exact HC | ctx_list] | ctx_list]);
      assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb;
      assert (HG2 : FOctx_avoid G2 2 1000) by (destruct HC2; tauto)
    end.
    destruct (FOPrH_cpair_le_cf n _ (FOnumeral 4) (FOVar (B + 2)) a ltac:(avoid_tms) Hka)
      as [_ Hpa'].
    destruct (FOPrH_cpair_le_cf n _ (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))
                ltac:(avoid_tms) Hpa) as [Hup Hwp].
    pose proof (FOPrH_le_below n _ _ _ _ Hpa' Hb2 ltac:(avoid_tms)) as Hpb.
    pose proof (IHu _ rho (B + 8) (B' + 8) (FOVar (B + 4)) (FOVar (B' + 4)) HE HC2 Hrho Hrx
                  Hua Huc (FOPrH_le_below n _ _ _ _ Hup Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    pose proof (IHw _ rho (B + 8 + 4 * cpat_pairs (cpat_tm rho u))
                  (B' + 8 + 4 * cpat_pairs (cpat_tm (rho_sub ox j rho) u))
                  (FOVar (B + 6)) (FOVar (B' + 6)) HE HC2 Hrho Hrx
                  Hwa Hwc (FOPrH_le_below n _ _ _ _ Hwp Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
    exact (FOPrH_N2_bin n _ X s a c 4 (FOVar (B + 2)) (FOVar (B + 4)) (FOVar (B + 6))
             (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2)) ltac:(lia)
             ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) Ru Rw Hka Hpa Hpc Hkc).
Qed.

(** ** Slots of the code patterns. *)

Lemma cpat_tm_slots : forall t rho s, cpat_occurs s (cpat_tm rho t) = true ->
  exists z, rho z = Some s.
Proof.
  induction t as [y| |u IH|u IHu w IHw|u IHu w IHw]; intros rho s H;
    cbn [cpat_tm cpat_occurs tVarP tZeroP tSuccP tPlusP tMultP orb] in H.
  - destruct (rho y) as [i|] eqn:Ey; cbn [cpat_occurs orb] in H; [|discriminate].
    apply Nat.eqb_eq in H. subst i. exists y. exact Ey.
  - discriminate.
  - exact (IH rho s H).
  - apply Bool.orb_true_iff in H. destruct H as [H|H]; [exact (IHu rho s H) | exact (IHw rho s H)].
  - apply Bool.orb_true_iff in H. destruct H as [H|H]; [exact (IHu rho s H) | exact (IHw rho s H)].
Qed.

Lemma cpat_f_slots : forall A rho s, cpat_occurs s (cpat_f rho A) = true ->
  exists z, rho z = Some s.
Proof.
  induction A as [u w| |P IHP Q IHQ|y P IHP|y P IHP]; intros rho s H;
    cbn [cpat_f cpat_occurs pEqP pFlsP pImpP pAllP pExP orb] in H.
  - apply Bool.orb_true_iff in H. destruct H as [H|H];
      [exact (cpat_tm_slots u rho s H) | exact (cpat_tm_slots w rho s H)].
  - discriminate.
  - apply Bool.orb_true_iff in H. destruct H as [H|H]; [exact (IHP rho s H) | exact (IHQ rho s H)].
  - destruct (IHP _ s H) as [z Hz]. unfold rho_hide in Hz.
    destruct (Nat.eqb z y); [discriminate | exists z; exact Hz].
  - destruct (IHP _ s H) as [z Hz]. unfold rho_hide in Hz.
    destruct (Nat.eqb z y); [discriminate | exists z; exact Hz].
Qed.

Lemma FOPATF_env_eq : forall p B env env' d,
  (forall s, cpat_occurs s p = true -> nth s env' FOZero = nth s env FOZero) ->
  FOPATF B env' p d = FOPATF B env p d.
Proof.
  induction p as [k|i|q IH|a IHa b IHb]; intros B env env' d H;
    cbn [FOPATF cpat_occurs] in *.
  - reflexivity.
  - rewrite H; [reflexivity|]. apply Nat.eqb_refl.
  - rewrite (IH (B + 2) env env' (FOVar B)); [reflexivity|]. exact H.
  - rewrite (IHa (B + 4) env env' (FOVar B)), (IHb (B + 4 + 4 * cpat_pairs a) env env' (FOVar (B + 2)));
      [reflexivity| |]; intros s Hs; apply H; rewrite Hs;
      first [reflexivity | apply Bool.orb_true_r].
Qed.

Ltac span_g := cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP
                      pAllP pExP].
Ltac span_h H := cbn [cpat_span cpat_pairs tVarP tZeroP tSuccP tPlusP tMultP pEqP pFlsP pImpP
                        pAllP pExP] in H.
Ltac span_std H1 H2 H3 H4 H5 := span_h H1; span_h H2; span_h H3; span_h H4; span_h H5.

(** ** Substitution rows for the code of a formula. *)

Lemma FOPrH_rows_f : forall n ox X Xb s env env' j A G rho B B' a c,
  RowEnv ox X Xb s env env' j -> RowCtx n ox X Xb env G ->
  (forall z i, rho z = Some i -> i < length env) ->
  match ox with Some x => rho x = None | None => True end ->
  FOPrH n G (FOPATF B env (cpat_f rho A) a) ->
  FOPrH n G (FOPATF B' env' (cpat_f (rho_sub ox j rho) A) c) ->
  FOPrH n G (FOle (FOSucc a) Xb) ->
  1000 <= B -> 1000 <= B' ->
  B + cpat_span (cpat_f rho A) <= B' \/ B' + cpat_span (cpat_f (rho_sub ox j rho) A) <= B ->
  FOctx_avoid G B (B + cpat_span (cpat_f rho A)) ->
  FOctx_avoid G B' (B' + cpat_span (cpat_f (rho_sub ox j rho) A)) ->
  FOtms_avoid (a :: c :: X :: Xb :: s :: env ++ env') B (B + cpat_span (cpat_f rho A)) ->
  FOtms_avoid (a :: c :: X :: Xb :: s :: env ++ env') B'
    (B' + cpat_span (cpat_f (rho_sub ox j rho) A)) ->
  FOtms_avoid [a; c] 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X s a c).
Proof.
  intros n ox X Xb s env env' j A.
  induction A as [u w| |P IHP Q IHQ|y P IHP|y P IHP];
    intros G rho B B' a c HE HC Hrho Hrx Ha Hc Hb HB HB' Hdis HGs HGt Havs Havt Hac;
    pose proof HE as [Henv [Hj [HX Hlo]]]; pose proof HC as [HG [Hslot Hlit]].
  - (* equation *)
    cbn [cpat_f pEqP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    pose proof (cpat_span_le (cpat_tm rho u)) as Hsu.
    pose proof (cpat_span_le (cpat_tm (rho_sub ox j rho) u)) as Hsu'.
    span_std Hdis HGs HGt Havs Havt.
    apply (FOPrH_patf_bin_elim n G B env 0 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    apply (FOPrH_patf_bin_elim n _ B' env' 0 _ _ c _ (FOPrH_weak_app _ _ _ _ Hc) ltac:(lia));
      [span_g; ctx_list | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hka : FOPrH n G2 (FOcpairF (FOnumeral 0) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G2 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G2 (FOPATF (B + 8) env (cpat_tm rho u) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G2 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) env
                                  (cpat_tm rho w) (FOVar (B + 6)))) by wk_in;
      assert (Hkc : FOPrH n G2 (FOcpairF (FOnumeral 0) (FOVar (B' + 2)) c)) by wk_in;
      assert (Hpc : FOPrH n G2 (FOcpairF (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2))))
        by wk_in;
      assert (Huc : FOPrH n G2 (FOPATF (B' + 8) env' (cpat_tm (rho_sub ox j rho) u)
                                  (FOVar (B' + 4)))) by wk_in;
      assert (Hwc : FOPrH n G2 (FOPATF (B' + 8 + 4 * cpat_pairs (cpat_tm (rho_sub ox j rho) u))
                                  env' (cpat_tm (rho_sub ox j rho) w) (FOVar (B' + 6)))) by wk_in;
      assert (HC2 : RowCtx n ox X Xb env G2)
        by (apply RowCtx_ext; [apply RowCtx_ext; [exact HC | ctx_list] | ctx_list]);
      assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb;
      assert (HG2 : FOctx_avoid G2 2 1000) by (destruct HC2; tauto)
    end.
    destruct (FOPrH_cpair_le_cf n _ (FOnumeral 0) (FOVar (B + 2)) a ltac:(avoid_tms) Hka)
      as [_ Hpa'].
    destruct (FOPrH_cpair_le_cf n _ (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))
                ltac:(avoid_tms) Hpa) as [Hup Hwp].
    pose proof (FOPrH_le_below n _ _ _ _ Hpa' Hb2 ltac:(avoid_tms)) as Hpb.
    pose proof (FOPrH_rows_tm n ox X Xb s env env' j u _ rho (B + 8) (B' + 8) (FOVar (B + 4))
                  (FOVar (B' + 4)) HE HC2 Hrho Hrx
                  Hua Huc (FOPrH_le_below n _ _ _ _ Hup Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    pose proof (FOPrH_rows_tm n ox X Xb s env env' j w _ rho
                  (B + 8 + 4 * cpat_pairs (cpat_tm rho u))
                  (B' + 8 + 4 * cpat_pairs (cpat_tm (rho_sub ox j rho) u))
                  (FOVar (B + 6)) (FOVar (B' + 6)) HE HC2 Hrho Hrx
                  Hwa Hwc (FOPrH_le_below n _ _ _ _ Hwp Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
    exact (FOPrH_N3_eq n _ X s a c (FOVar (B + 2)) (FOVar (B + 4)) (FOVar (B + 6))
             (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2))
             ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) Ru Rw Hka Hpa Hpc Hkc).
  - (* falsum *)
    cbn [cpat_f] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    span_std Hdis HGs HGt Havs Havt.
    apply (FOPrH_patf_leaf_elim n G B env 1 0 a _ Ha ltac:(lia) HGs);
      [intros w1 H1 H2; free_fm | avoid_tms |].
    apply (FOPrH_patf_leaf_elim n _ B' env' 1 0 c _ (FOPrH_weak_app _ _ _ _ Hc) ltac:(lia));
      [ctx_list | intros w1 H1 H2; free_fm | avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hcc : FOPrH n G2 (FOcpairF (FOnumeral 1) (FOnumeral 0) c)) by apply FOPrH_last;
      assert (Hca : FOPrH n G2 (FOcpairF (FOnumeral 1) (FOnumeral 0) a)) by wk_in;
      assert (HG2 : FOctx_avoid G2 2 1000) by ctx_list
    end.
    pose proof (FOPrH_cpair_fun n _ _ _ a c ltac:(avoid_tms) Hca Hcc) as Eac.
    pose proof (FOPrH_N3_false n _ X s a ltac:(intros w1 ? ?; apply HG2; lia)
                  ltac:(avoid_tms) Hca) as R.
    exact (FOPrH_tblex_cong n _ _ _ _ _ _ _ _ R (FOPrH_refl _ _ _) Eac ltac:(avoid_tms)).
  - (* implication *)
    cbn [cpat_f pImpP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    pose proof (cpat_span_le (cpat_f rho P)) as Hsu.
    pose proof (cpat_span_le (cpat_f (rho_sub ox j rho) P)) as Hsu'.
    span_std Hdis HGs HGt Havs Havt.
    apply (FOPrH_patf_bin_elim n G B env 2 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    apply (FOPrH_patf_bin_elim n _ B' env' 2 _ _ c _ (FOPrH_weak_app _ _ _ _ Hc) ltac:(lia));
      [span_g; ctx_list | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G2 _ =>
      assert (Hka : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G2 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G2 (FOPATF (B + 8) env (cpat_f rho P) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G2 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_f rho P)) env
                                  (cpat_f rho Q) (FOVar (B + 6)))) by wk_in;
      assert (Hkc : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar (B' + 2)) c)) by wk_in;
      assert (Hpc : FOPrH n G2 (FOcpairF (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2))))
        by wk_in;
      assert (Huc : FOPrH n G2 (FOPATF (B' + 8) env' (cpat_f (rho_sub ox j rho) P)
                                  (FOVar (B' + 4)))) by wk_in;
      assert (Hwc : FOPrH n G2 (FOPATF (B' + 8 + 4 * cpat_pairs (cpat_f (rho_sub ox j rho) P))
                                  env' (cpat_f (rho_sub ox j rho) Q) (FOVar (B' + 6)))) by wk_in;
      assert (HC2 : RowCtx n ox X Xb env G2)
        by (apply RowCtx_ext; [apply RowCtx_ext; [exact HC | ctx_list] | ctx_list]);
      assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb;
      assert (HG2 : FOctx_avoid G2 2 1000) by (destruct HC2; tauto)
    end.
    destruct (FOPrH_cpair_le_cf n _ (FOnumeral 2) (FOVar (B + 2)) a ltac:(avoid_tms) Hka)
      as [_ Hpa'].
    destruct (FOPrH_cpair_le_cf n _ (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))
                ltac:(avoid_tms) Hpa) as [Hup Hwp].
    pose proof (FOPrH_le_below n _ _ _ _ Hpa' Hb2 ltac:(avoid_tms)) as Hpb.
    pose proof (IHP _ rho (B + 8) (B' + 8) (FOVar (B + 4)) (FOVar (B' + 4)) HE HC2 Hrho Hrx
                  Hua Huc (FOPrH_le_below n _ _ _ _ Hup Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    pose proof (IHQ _ rho (B + 8 + 4 * cpat_pairs (cpat_f rho P))
                  (B' + 8 + 4 * cpat_pairs (cpat_f (rho_sub ox j rho) P))
                  (FOVar (B + 6)) (FOVar (B' + 6)) HE HC2 Hrho Hrx
                  Hwa Hwc (FOPrH_le_below n _ _ _ _ Hwp Hpb ltac:(avoid_tms))
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
    exact (FOPrH_N3_impl n _ X s a c (FOVar (B + 2)) (FOVar (B + 4)) (FOVar (B + 6))
             (FOVar (B' + 4)) (FOVar (B' + 6)) (FOVar (B' + 2))
             ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) Ru Rw Hka Hpa Hpc Hkc).
  - (* universal *)
    cbn [cpat_f pAllP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    pose proof (cpat_span_le (cpat_f (rho_hide y rho) P)) as Hsu.
    destruct (ox_eq ox y) eqn:Eo.
    + destruct ox as [x|]; cbn [ox_eq] in Eo; [|discriminate].
      apply Nat.eqb_eq in Eo. subst y. subst X.
      assert (Ep : cpat_f (rho_hide x (rho_sub (Some x) j rho)) P = cpat_f (rho_hide x rho) P)
        by (apply cpat_f_ext; apply rho_hide_sub_self).
      rewrite Ep in Hc, HGt, Havt, Hdis.
      assert (Ee : FOPATF B' env' (pAllP (CLit x) (cpat_f (rho_hide x rho) P)) c
                 = FOPATF B' env (pAllP (CLit x) (cpat_f (rho_hide x rho) P)) c).
      { apply FOPATF_env_eq. intros s0 Hs0. cbn [pAllP cpat_occurs orb] in Hs0.
        destruct (cpat_f_slots P _ s0 Hs0) as [z Hz]. unfold rho_hide in Hz.
        destruct (Nat.eqb z x); [discriminate|]. apply Henv. exact (Hrho z s0 Hz). }
      rewrite Ee in Hc.
      span_std Hdis HGs HGt Havs Havt.
      pose proof (FOPrH_patf_unique _ n G B B' env a c Ha Hc ltac:(lia) ltac:(lia)
                    ltac:(span_g; lia) ltac:(span_g; exact HGs) ltac:(span_g; exact HGt)
                    ltac:(span_g; avoid_tms) ltac:(span_g; avoid_tms) ltac:(avoid_tms)) as Eac.
      apply (FOPrH_patf_quant_elim n G B env 3 x _ a _ Ha ltac:(lia));
        [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
      lazymatch goal with |- FOPrH _ ?G1 _ =>
        assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 3) (FOVar (B + 2)) a)) by wk_in;
        assert (Hya : FOPrH n G1 (FOcpairF (FOnumeral x) (FOVar (B + 6)) (FOVar (B + 2))))
          by wk_in;
        assert (Eac1 : FOPrH n G1 (FOEq a c)) by wk Eac;
        assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
      end.
      pose proof (FOPrH_N3_quant_eq n _ (FOnumeral x) s a 3 (FOVar (B + 2)) (FOnumeral x)
                    (FOVar (B + 6)) (or_introl eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
                    ltac:(avoid_tms) Hka Hya (FOPrH_refl _ _ _)) as R.
      exact (FOPrH_tblex_cong n _ _ _ _ _ _ _ _ R (FOPrH_refl _ _ _) Eac1 ltac:(avoid_tms)).
    + assert (Ep : cpat_f (rho_hide y (rho_sub ox j rho)) P
                   = cpat_f (rho_sub ox j (rho_hide y rho)) P).
      { apply cpat_f_ext. intros z. symmetry. apply rho_sub_hide. exact Eo. }
      rewrite Ep in Hc, HGt, Havt, Hdis.
      pose proof (cpat_span_le (cpat_f (rho_sub ox j (rho_hide y rho)) P)) as Hsu'.
      span_std Hdis HGs HGt Havs Havt.
      apply (FOPrH_patf_quant_elim n G B env 3 y _ a _ Ha ltac:(lia));
        [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
      apply (FOPrH_patf_quant_elim n _ B' env' 3 y _ c _ (FOPrH_weak_app _ _ _ _ Hc)
               ltac:(lia));
        [span_g; ctx_list | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
      lazymatch goal with |- FOPrH _ ?G2 _ =>
        assert (Hka : FOPrH n G2 (FOcpairF (FOnumeral 3) (FOVar (B + 2)) a)) by wk_in;
        assert (Hya : FOPrH n G2 (FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))))
          by wk_in;
        assert (Hpa : FOPrH n G2 (FOPATF (B + 8) env (cpat_f (rho_hide y rho) P)
                                    (FOVar (B + 6)))) by wk_in;
        assert (Hkc : FOPrH n G2 (FOcpairF (FOnumeral 3) (FOVar (B' + 2)) c)) by wk_in;
        assert (Hyc : FOPrH n G2 (FOcpairF (FOnumeral y) (FOVar (B' + 6)) (FOVar (B' + 2))))
          by wk_in;
        assert (Hpc : FOPrH n G2 (FOPATF (B' + 8) env' (cpat_f (rho_sub ox j (rho_hide y rho)) P)
                                    (FOVar (B' + 6)))) by wk_in;
        assert (HC2 : RowCtx n ox X Xb env G2)
          by (apply RowCtx_ext; [apply RowCtx_ext; [exact HC | ctx_list] | ctx_list]);
        assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb;
        assert (HG2 : FOctx_avoid G2 2 1000) by (destruct HC2; tauto)
      end.
      destruct (FOPrH_cpair_le_cf n _ (FOnumeral 3) (FOVar (B + 2)) a ltac:(avoid_tms) Hka)
        as [_ Hpa'].
      destruct (FOPrH_cpair_le_cf n _ (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))
                  ltac:(avoid_tms) Hya) as [Hyp Hbp].
      pose proof (FOPrH_le_below n _ _ _ _ Hpa' Hb2 ltac:(avoid_tms)) as Hpb.
      assert (Hrho' : forall z i, rho_hide y rho z = Some i -> i < length env).
      { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z y); [discriminate|].
        exact (Hrho z i Hz). }
      assert (Hrx' : match ox with Some x => rho_hide y rho x = None | None => True end).
      { destruct ox as [x|]; [|exact I]. unfold rho_hide. destruct (Nat.eqb x y);
          [reflexivity | exact Hrx]. }
      pose proof (IHP _ (rho_hide y rho) (B + 8) (B' + 8) (FOVar (B + 6)) (FOVar (B' + 6)) HE
                    HC2 Hrho' Hrx' Hpa Hpc (FOPrH_le_below n _ _ _ _ Hbp Hpb ltac:(avoid_tms))
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                    ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as R.
      destruct HC2 as [_ [_ Hlit2]].
      pose proof (Hlit2 _ y (fun Y HY => HY) (FOPrH_le_below n _ _ _ _ Hyp Hpb ltac:(avoid_tms))
                    Eo) as Hne.
      exact (FOPrH_N3_quant_ne n _ X s a c 3 (FOVar (B + 2)) (FOnumeral y) (FOVar (B + 6))
               (FOVar (B' + 6)) (FOVar (B' + 2)) (or_introl eq_refl)
               ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) R Hka Hya Hne Hyc Hkc).
  - (* existential *)
    cbn [cpat_f pExP] in Ha, Hc, Hdis, HGs, HGt, Havs, Havt.
    pose proof (cpat_span_le (cpat_f (rho_hide y rho) P)) as Hsu.
    destruct (ox_eq ox y) eqn:Eo.
    + destruct ox as [x|]; cbn [ox_eq] in Eo; [|discriminate].
      apply Nat.eqb_eq in Eo. subst y. subst X.
      assert (Ep : cpat_f (rho_hide x (rho_sub (Some x) j rho)) P = cpat_f (rho_hide x rho) P)
        by (apply cpat_f_ext; apply rho_hide_sub_self).
      rewrite Ep in Hc, HGt, Havt, Hdis.
      assert (Ee : FOPATF B' env' (pExP (CLit x) (cpat_f (rho_hide x rho) P)) c
                 = FOPATF B' env (pExP (CLit x) (cpat_f (rho_hide x rho) P)) c).
      { apply FOPATF_env_eq. intros s0 Hs0. cbn [pExP cpat_occurs orb] in Hs0.
        destruct (cpat_f_slots P _ s0 Hs0) as [z Hz]. unfold rho_hide in Hz.
        destruct (Nat.eqb z x); [discriminate|]. apply Henv. exact (Hrho z s0 Hz). }
      rewrite Ee in Hc.
      span_std Hdis HGs HGt Havs Havt.
      pose proof (FOPrH_patf_unique _ n G B B' env a c Ha Hc ltac:(lia) ltac:(lia)
                    ltac:(span_g; lia) ltac:(span_g; exact HGs) ltac:(span_g; exact HGt)
                    ltac:(span_g; avoid_tms) ltac:(span_g; avoid_tms) ltac:(avoid_tms)) as Eac.
      apply (FOPrH_patf_quant_elim n G B env 4 x _ a _ Ha ltac:(lia));
        [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
      lazymatch goal with |- FOPrH _ ?G1 _ =>
        assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 4) (FOVar (B + 2)) a)) by wk_in;
        assert (Hya : FOPrH n G1 (FOcpairF (FOnumeral x) (FOVar (B + 6)) (FOVar (B + 2))))
          by wk_in;
        assert (Eac1 : FOPrH n G1 (FOEq a c)) by wk Eac;
        assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
      end.
      pose proof (FOPrH_N3_quant_eq n _ (FOnumeral x) s a 4 (FOVar (B + 2)) (FOnumeral x)
                    (FOVar (B + 6)) (or_intror eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
                    ltac:(avoid_tms) Hka Hya (FOPrH_refl _ _ _)) as R.
      exact (FOPrH_tblex_cong n _ _ _ _ _ _ _ _ R (FOPrH_refl _ _ _) Eac1 ltac:(avoid_tms)).
    + assert (Ep : cpat_f (rho_hide y (rho_sub ox j rho)) P
                   = cpat_f (rho_sub ox j (rho_hide y rho)) P).
      { apply cpat_f_ext. intros z. symmetry. apply rho_sub_hide. exact Eo. }
      rewrite Ep in Hc, HGt, Havt, Hdis.
      pose proof (cpat_span_le (cpat_f (rho_sub ox j (rho_hide y rho)) P)) as Hsu'.
      span_std Hdis HGs HGt Havs Havt.
      apply (FOPrH_patf_quant_elim n G B env 4 y _ a _ Ha ltac:(lia));
        [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
      apply (FOPrH_patf_quant_elim n _ B' env' 4 y _ c _ (FOPrH_weak_app _ _ _ _ Hc)
               ltac:(lia));
        [span_g; ctx_list | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
      lazymatch goal with |- FOPrH _ ?G2 _ =>
        assert (Hka : FOPrH n G2 (FOcpairF (FOnumeral 4) (FOVar (B + 2)) a)) by wk_in;
        assert (Hya : FOPrH n G2 (FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))))
          by wk_in;
        assert (Hpa : FOPrH n G2 (FOPATF (B + 8) env (cpat_f (rho_hide y rho) P)
                                    (FOVar (B + 6)))) by wk_in;
        assert (Hkc : FOPrH n G2 (FOcpairF (FOnumeral 4) (FOVar (B' + 2)) c)) by wk_in;
        assert (Hyc : FOPrH n G2 (FOcpairF (FOnumeral y) (FOVar (B' + 6)) (FOVar (B' + 2))))
          by wk_in;
        assert (Hpc : FOPrH n G2 (FOPATF (B' + 8) env' (cpat_f (rho_sub ox j (rho_hide y rho)) P)
                                    (FOVar (B' + 6)))) by wk_in;
        assert (HC2 : RowCtx n ox X Xb env G2)
          by (apply RowCtx_ext; [apply RowCtx_ext; [exact HC | ctx_list] | ctx_list]);
        assert (Hb2 : FOPrH n G2 (FOle (FOSucc a) Xb)) by wk Hb;
        assert (HG2 : FOctx_avoid G2 2 1000) by (destruct HC2; tauto)
      end.
      destruct (FOPrH_cpair_le_cf n _ (FOnumeral 4) (FOVar (B + 2)) a ltac:(avoid_tms) Hka)
        as [_ Hpa'].
      destruct (FOPrH_cpair_le_cf n _ (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))
                  ltac:(avoid_tms) Hya) as [Hyp Hbp].
      pose proof (FOPrH_le_below n _ _ _ _ Hpa' Hb2 ltac:(avoid_tms)) as Hpb.
      assert (Hrho' : forall z i, rho_hide y rho z = Some i -> i < length env).
      { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z y); [discriminate|].
        exact (Hrho z i Hz). }
      assert (Hrx' : match ox with Some x => rho_hide y rho x = None | None => True end).
      { destruct ox as [x|]; [|exact I]. unfold rho_hide. destruct (Nat.eqb x y);
          [reflexivity | exact Hrx]. }
      pose proof (IHP _ (rho_hide y rho) (B + 8) (B' + 8) (FOVar (B + 6)) (FOVar (B' + 6)) HE
                    HC2 Hrho' Hrx' Hpa Hpc (FOPrH_le_below n _ _ _ _ Hbp Hpb ltac:(avoid_tms))
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(ctx_list) ltac:(ctx_list)
                    ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as R.
      destruct HC2 as [_ [_ Hlit2]].
      pose proof (Hlit2 _ y (fun Y HY => HY) (FOPrH_le_below n _ _ _ _ Hyp Hpb ltac:(avoid_tms))
                    Eo) as Hne.
      exact (FOPrH_N3_quant_ne n _ X s a c 4 (FOVar (B + 2)) (FOnumeral y) (FOVar (B + 6))
               (FOVar (B' + 6)) (FOVar (B' + 2)) (or_intror eq_refl)
               ltac:(intros w1 ? ?; apply HG2; lia) ltac:(avoid_tms) R Hka Hya Hne Hyc Hkc).
Qed.

(** ** Occurrence of a variable in the literal part of a pattern. *)

Fixpoint lit_occ_tm (rho : nat -> option nat) (x : nat) (t : FOTerm) : bool :=
  match t with
  | FOVar y => match rho y with Some _ => false | None => Nat.eqb y x end
  | FOZero => false
  | FOSucc u => lit_occ_tm rho x u
  | FOPlus u w => lit_occ_tm rho x u || lit_occ_tm rho x w
  | FOMult u w => lit_occ_tm rho x u || lit_occ_tm rho x w
  end.

Fixpoint lit_free_f (rho : nat -> option nat) (x : nat) (A : FOFormula) : bool :=
  match A with
  | FOEq u w => lit_occ_tm rho x u || lit_occ_tm rho x w
  | FOFalseF => false
  | FOImplF P Q => lit_free_f rho x P || lit_free_f rho x Q
  | FOForall y P => if Nat.eqb y x then false else lit_free_f (rho_hide y rho) x P
  | FOExists y P => if Nat.eqb y x then false else lit_free_f (rho_hide y rho) x P
  end.

Notation bnum b := (FOnumeral (if b then 1 else 0)).

(** ** Closed facts about numerals. *)

Lemma FOPrH_num_neq : forall n G y x, y <> x ->
  FOPrH n G (FONeg (FOEq (FOnumeral y) (FOnumeral x))).
Proof.
  intros n G y x H. apply FOPrH_empty. apply FOPrH_true_closed.
  - apply FOs1_d0. apply FOd0_impl; [apply FOd0_eq | apply FOd0_false].
  - intros v. unfold FONeg. cbn [FOfree_in]. rewrite !FOin_tm_numeral. reflexivity.
  - unfold FONeg. cbn [FOsat]. rewrite !FOeval_numeral. exact H.
Qed.

(** ** A row rewritten along an equation of its third field. *)

Lemma FOPrH_tblex_cong_a2 : forall n G tg a1 a2 a3 r a2',
  FOPrH n G (FOTBLEX tg a1 a2 a3 r) -> FOPrH n G (FOEq a2 a2') ->
  FOtms_avoid [tg; a1; a2; a3; r; a2'] 2 1000 ->
  FOPrH n G (FOTBLEX tg a1 a2' a3 r).
Proof.
  intros n G tg a1 a2 a3 r a2' H E Hav.
  assert (K : forall t, FOtm_avoid t 2 1000 ->
             FOsubst_f 999 t (FOTBLEX tg a1 (FOVar 999) a3 r) = FOTBLEX tg a1 t a3 r).
  { intros t Ht. rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq'.
    rewrite !(FOsubst_t_not_in _ 999 t) by fr_tm. reflexivity. }
  assert (V2 : FOtm_avoid a2 2 1000) by avoid_tm.
  assert (V2' : FOtm_avoid a2' 2 1000) by avoid_tm.
  pose proof (FOPrH_leibniz n G 999 a2 a2' (FOTBLEX tg a1 (FOVar 999) a3 r)
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm]) E) as L.
  rewrite (K a2 V2), (K a2' V2') in L. exact (L H).
Qed.

(** ** Contexts carrying the rows of the slot codes. *)

Definition SlotCtx (n : nat) (env : list FOTerm) (G : list FOFormula) : Prop :=
  FOctx_avoid G 2 1000 /\
  (forall i, i < length env -> exists w, FOPrH n G (FONUMR w (nth i env FOZero))).

Lemma SlotCtx_ext : forall n env G L,
  SlotCtx n env G -> FOctx_avoid L 2 1000 -> SlotCtx n env (G ++ L).
Proof.
  intros n env G L [H1 H2] HL. split.
  - intros w ? ?. apply FOfree_ctx_app_inv; [apply H1 | apply HL]; lia.
  - intros i Hi. destruct (H2 i Hi) as [w Hw]. exists w. apply FOPrH_weak_app. exact Hw.
Qed.

(** ** Occurrence rows for the code of a term (tag [0]). *)

Lemma FOPrH_occ_tm : forall n x t G rho env B a,
  SlotCtx n env G -> (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FOPATF B env (cpat_tm rho t) a) ->
  1000 <= B -> FOctx_avoid G B (B + cpat_span (cpat_tm rho t)) ->
  FOtms_avoid (a :: env) B (B + cpat_span (cpat_tm rho t)) ->
  FOtms_avoid (a :: env) 2 1000 ->
  FOPrH n G (FOTBLEX FOZero (FOnumeral x) a FOZero (bnum (lit_occ_tm rho x t))).
Proof.
  intros n x t.
  induction t as [y| |u IH|u IHu w IHw|u IHu w IHw];
    intros G rho env B a HS Hrho Ha HB HGs Havs Hlo; pose proof HS as [HG Hslot].
  - cbn [cpat_tm lit_occ_tm] in *.
    destruct (rho y) as [i|] eqn:Ey.
    + cbn [FOPATF] in Ha. destruct (Hslot i (Hrho y i Ey)) as [wv Hw].
      assert (Vi : FOtms_avoid [nth i env FOZero] 2 1000).
      { apply FOtms_avoid_cons; [|apply FOtms_avoid_nil]. apply Hlo.
        right. apply nth_In. exact (Hrho y i Ey). }
      pose proof (FOPrH_numr_row0 n G wv (nth i env FOZero) (FOnumeral x) Hw ltac:(avoid_tms))
        as R.
      exact (FOPrH_tblex_cong_a2 n G _ _ _ _ _ _ R (FOPrH_eq_sym _ _ _ _ Ha) ltac:(avoid_tms)).
    + span_h HGs. span_h Havs.
      apply (FOPrH_patf_leaf_elim n G B env 0 y a _ Ha ltac:(lia) HGs);
        [intros w1 H1 H2; free_fm | avoid_tms |].
      lazymatch goal with |- FOPrH _ ?G1 _ =>
        assert (Hca : FOPrH n G1 (FOcpairF (FOnumeral 0) (FOnumeral y) a)) by apply FOPrH_last;
        assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
      end.
      destruct (Nat.eqb_spec y x) as [->|Hne].
      * exact (FOPrH_N0_var_eq n _ (FOnumeral x) a (FOnumeral x)
                 ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Hca (FOPrH_refl _ _ _)).
      * exact (FOPrH_N0_var_ne n _ (FOnumeral x) a (FOnumeral y)
                 ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Hca
                 (FOPrH_num_neq n _ y x Hne)).
  - cbn [cpat_tm lit_occ_tm] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_leaf_elim n G B env 1 0 a _ Ha ltac:(lia) HGs);
      [intros w1 H1 H2; free_fm | avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hca : FOPrH n G1 (FOcpairF (FOnumeral 1) (FOnumeral 0) a)) by apply FOPrH_last;
      assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
    end.
    exact (FOPrH_N0_zero n _ (FOnumeral x) a ltac:(intros w1 ? ?; apply HG1; lia)
             ltac:(avoid_tms) Hca).
  - cbn [cpat_tm lit_occ_tm tSuccP] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_lit_elim n G B env 2 _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hca : FOPrH n G1 (FOcpairF (FOnumeral 2) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G1 (FOPATF (B + 4) env (cpat_tm rho u) (FOVar (B + 2)))) by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    pose proof (IH _ rho env (B + 4) (FOVar (B + 2)) HS1 Hrho Hpa ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms)) as R.
    exact (FOPrH_N0_succ n _ (FOnumeral x) (FOVar (B + 2)) a (bnum (lit_occ_tm rho x u))
             ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) R Hca).
  - cbn [cpat_tm lit_occ_tm tPlusP] in *.
    pose proof (cpat_span_le (cpat_tm rho u)) as Hsu.
    span_h HGs. span_h Havs.
    apply (FOPrH_patf_bin_elim n G B env 3 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 3) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G1 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G1 (FOPATF (B + 8) env (cpat_tm rho u) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G1 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) env
                                  (cpat_tm rho w) (FOVar (B + 6)))) by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    pose proof (IHu _ rho env (B + 8) (FOVar (B + 4)) HS1 Hrho Hua ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    destruct (lit_occ_tm rho x u) eqn:Eu; cbn [orb].
    + exact (FOPrH_N0_bin_one n _ (FOnumeral x) a 3 (FOVar (B + 2)) (FOVar (B + 4))
               (FOVar (B + 6)) (or_introl eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Ru Hka Hpa).
    + pose proof (IHw _ rho env (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) (FOVar (B + 6)) HS1
                    Hrho Hwa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
      exact (FOPrH_N0_bin_zero n _ (FOnumeral x) a (bnum (lit_occ_tm rho x w)) 3
               (FOVar (B + 2)) (FOVar (B + 4))
               (FOVar (B + 6)) (or_introl eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Ru Rw Hka Hpa).
  - cbn [cpat_tm lit_occ_tm tMultP] in *.
    pose proof (cpat_span_le (cpat_tm rho u)) as Hsu.
    span_h HGs. span_h Havs.
    apply (FOPrH_patf_bin_elim n G B env 4 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 4) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G1 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G1 (FOPATF (B + 8) env (cpat_tm rho u) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G1 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) env
                                  (cpat_tm rho w) (FOVar (B + 6)))) by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    pose proof (IHu _ rho env (B + 8) (FOVar (B + 4)) HS1 Hrho Hua ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    destruct (lit_occ_tm rho x u) eqn:Eu; cbn [orb].
    + exact (FOPrH_N0_bin_one n _ (FOnumeral x) a 4 (FOVar (B + 2)) (FOVar (B + 4))
               (FOVar (B + 6)) (or_intror eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Ru Hka Hpa).
    + pose proof (IHw _ rho env (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) (FOVar (B + 6)) HS1
                    Hrho Hwa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
      exact (FOPrH_N0_bin_zero n _ (FOnumeral x) a (bnum (lit_occ_tm rho x w)) 4
               (FOVar (B + 2)) (FOVar (B + 4))
               (FOVar (B + 6)) (or_intror eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Ru Rw Hka Hpa).
Qed.

(** ** Free-occurrence rows for the code of a formula (tag [1]). *)

Lemma FOPrH_free_f : forall n x A G rho env B a,
  SlotCtx n env G -> (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FOPATF B env (cpat_f rho A) a) ->
  1000 <= B -> FOctx_avoid G B (B + cpat_span (cpat_f rho A)) ->
  FOtms_avoid (a :: env) B (B + cpat_span (cpat_f rho A)) ->
  FOtms_avoid (a :: env) 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 1) (FOnumeral x) a FOZero (bnum (lit_free_f rho x A))).
Proof.
  intros n x A.
  induction A as [u w| |P IHP Q IHQ|y P IHP|y P IHP];
    intros G rho env B a HS Hrho Ha HB HGs Havs Hlo; pose proof HS as [HG Hslot].
  - cbn [cpat_f lit_free_f pEqP] in *.
    pose proof (cpat_span_le (cpat_tm rho u)) as Hsu.
    span_h HGs. span_h Havs.
    apply (FOPrH_patf_bin_elim n G B env 0 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 0) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G1 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G1 (FOPATF (B + 8) env (cpat_tm rho u) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G1 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_tm rho u)) env
                                  (cpat_tm rho w) (FOVar (B + 6)))) by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    pose proof (FOPrH_occ_tm n x u _ rho env (B + 8) (FOVar (B + 4)) HS1 Hrho Hua ltac:(lia)
                  ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    destruct (lit_occ_tm rho x u) eqn:Eu; cbn [orb].
    + exact (FOPrH_N1_eq_one n _ (FOnumeral x) a (FOVar (B + 2)) (FOVar (B + 4))
               (FOVar (B + 6)) ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Ru Hka Hpa).
    + pose proof (FOPrH_occ_tm n x w _ rho env (B + 8 + 4 * cpat_pairs (cpat_tm rho u))
                    (FOVar (B + 6)) HS1 Hrho Hwa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms)
                    ltac:(avoid_tms)) as Rw.
      exact (FOPrH_N1_eq_zero n _ (FOnumeral x) a (bnum (lit_occ_tm rho x w)) (FOVar (B + 2))
               (FOVar (B + 4)) (FOVar (B + 6)) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Ru Rw Hka Hpa).
  - cbn [cpat_f lit_free_f] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_leaf_elim n G B env 1 0 a _ Ha ltac:(lia) HGs);
      [intros w1 H1 H2; free_fm | avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hca : FOPrH n G1 (FOcpairF (FOnumeral 1) (FOnumeral 0) a)) by apply FOPrH_last;
      assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
    end.
    exact (FOPrH_N1_false n _ (FOnumeral x) a ltac:(intros w1 ? ?; apply HG1; lia)
             ltac:(avoid_tms) Hca).
  - cbn [cpat_f lit_free_f pImpP] in *.
    pose proof (cpat_span_le (cpat_f rho P)) as Hsu.
    span_h HGs. span_h Havs.
    apply (FOPrH_patf_bin_elim n G B env 2 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 2) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G1 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G1 (FOPATF (B + 8) env (cpat_f rho P) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G1 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_f rho P)) env
                                  (cpat_f rho Q) (FOVar (B + 6)))) by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    pose proof (IHP _ rho env (B + 8) (FOVar (B + 4)) HS1 Hrho Hua ltac:(lia) ltac:(ctx_list)
                  ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    destruct (lit_free_f rho x P) eqn:Eu; cbn [orb].
    + exact (FOPrH_N1_impl_one n _ (FOnumeral x) a (FOVar (B + 2)) (FOVar (B + 4))
               (FOVar (B + 6)) ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Ru Hka Hpa).
    + pose proof (IHQ _ rho env (B + 8 + 4 * cpat_pairs (cpat_f rho P)) (FOVar (B + 6)) HS1
                    Hrho Hwa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Rw.
      exact (FOPrH_N1_impl_zero n _ (FOnumeral x) a (bnum (lit_free_f rho x Q)) (FOVar (B + 2))
               (FOVar (B + 4)) (FOVar (B + 6)) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Ru Rw Hka Hpa).
  - cbn [cpat_f lit_free_f pAllP] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_quant_elim n G B env 3 y _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 3) (FOVar (B + 2)) a)) by wk_in;
      assert (Hya : FOPrH n G1 (FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hpa : FOPrH n G1 (FOPATF (B + 8) env (cpat_f (rho_hide y rho) P) (FOVar (B + 6))))
        by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    destruct (Nat.eqb_spec y x) as [->|Hne].
    + exact (FOPrH_N1_quant_eq n _ (FOnumeral x) a 3 (FOVar (B + 2)) (FOnumeral x)
               (FOVar (B + 6)) (or_introl eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Hka Hya (FOPrH_refl _ _ _)).
    + assert (Hrho' : forall z i, rho_hide y rho z = Some i -> i < length env).
      { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z y); [discriminate|].
        exact (Hrho z i Hz). }
      pose proof (IHP _ (rho_hide y rho) env (B + 8) (FOVar (B + 6)) HS1 Hrho' Hpa ltac:(lia)
                    ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as R.
      exact (FOPrH_N1_quant_ne n _ (FOnumeral x) a (bnum (lit_free_f (rho_hide y rho) x P)) 3
               (FOVar (B + 2)) (FOnumeral y) (FOVar (B + 6)) (or_introl eq_refl)
               ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) R Hka Hya
               (FOPrH_num_neq n _ y x Hne)).
  - cbn [cpat_f lit_free_f pExP] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_quant_elim n G B env 4 y _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 4) (FOVar (B + 2)) a)) by wk_in;
      assert (Hya : FOPrH n G1 (FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hpa : FOPrH n G1 (FOPATF (B + 8) env (cpat_f (rho_hide y rho) P) (FOVar (B + 6))))
        by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    destruct (Nat.eqb_spec y x) as [->|Hne].
    + exact (FOPrH_N1_quant_eq n _ (FOnumeral x) a 4 (FOVar (B + 2)) (FOnumeral x)
               (FOVar (B + 6)) (or_intror eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Hka Hya (FOPrH_refl _ _ _)).
    + assert (Hrho' : forall z i, rho_hide y rho z = Some i -> i < length env).
      { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z y); [discriminate|].
        exact (Hrho z i Hz). }
      pose proof (IHP _ (rho_hide y rho) env (B + 8) (FOVar (B + 6)) HS1 Hrho' Hpa ltac:(lia)
                    ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as R.
      exact (FOPrH_N1_quant_ne n _ (FOnumeral x) a (bnum (lit_free_f (rho_hide y rho) x P)) 4
               (FOVar (B + 2)) (FOnumeral y) (FOVar (B + 6)) (or_intror eq_refl)
               ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) R Hka Hya
               (FOPrH_num_neq n _ y x Hne)).
Qed.

(** ** Capture-test rows (tag [4]) for the substitution of a numeral code.

    A numeral code [m] contains no variable, so it is free for every
    variable in every formula: the row value is [1]. *)

Lemma FOPrH_cap_f : forall n x m A G rho env B a,
  SlotCtx n env G -> (exists w, FOPrH n G (FONUMR w m)) ->
  (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FOPATF B env (cpat_f rho A) a) ->
  1000 <= B -> FOctx_avoid G B (B + cpat_span (cpat_f rho A)) ->
  FOtms_avoid (a :: m :: env) B (B + cpat_span (cpat_f rho A)) ->
  FOtms_avoid (a :: m :: env) 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 4) (FOnumeral x) m a (FOnumeral 1)).
Proof.
  intros n x m A.
  induction A as [u w| |P IHP Q IHQ|y P IHP|y P IHP];
    intros G rho env B a HS [wm Hm] Hrho Ha HB HGs Havs Hlo; pose proof HS as [HG Hslot].
  - cbn [cpat_f pEqP] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_lit_elim n G B env 0 _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 0) (FOVar (B + 2)) a)) by wk_in;
      assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
    end.
    exact (FOPrH_N4_eq n _ (FOnumeral x) m a (FOVar (B + 2))
             ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Hka).
  - cbn [cpat_f] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_leaf_elim n G B env 1 0 a _ Ha ltac:(lia) HGs);
      [intros w1 H1 H2; free_fm | avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hca : FOPrH n G1 (FOcpairF (FOnumeral 1) (FOnumeral 0) a)) by apply FOPrH_last;
      assert (HG1 : FOctx_avoid G1 2 1000) by ctx_list
    end.
    exact (FOPrH_N4_false n _ (FOnumeral x) m a ltac:(intros w1 ? ?; apply HG1; lia)
             ltac:(avoid_tms) Hca).
  - cbn [cpat_f pImpP] in *.
    pose proof (cpat_span_le (cpat_f rho P)) as Hsu.
    span_h HGs. span_h Havs.
    apply (FOPrH_patf_bin_elim n G B env 2 _ _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 2) (FOVar (B + 2)) a)) by wk_in;
      assert (Hpa : FOPrH n G1 (FOcpairF (FOVar (B + 4)) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hua : FOPrH n G1 (FOPATF (B + 8) env (cpat_f rho P) (FOVar (B + 4)))) by wk_in;
      assert (Hwa : FOPrH n G1 (FOPATF (B + 8 + 4 * cpat_pairs (cpat_f rho P)) env
                                  (cpat_f rho Q) (FOVar (B + 6)))) by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (Hm1 : FOPrH n G1 (FONUMR wm m)) by wk Hm;
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    pose proof (IHP _ rho env (B + 8) (FOVar (B + 4)) HS1 (ex_intro _ wm Hm1) Hrho Hua
                  ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Ru.
    pose proof (IHQ _ rho env (B + 8 + 4 * cpat_pairs (cpat_f rho P)) (FOVar (B + 6)) HS1
                  (ex_intro _ wm Hm1) Hrho Hwa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms)
                  ltac:(avoid_tms)) as Rw.
    exact (FOPrH_N4_impl n _ (FOnumeral x) m a (FOnumeral 1) (FOVar (B + 2)) (FOVar (B + 4))
             (FOVar (B + 6)) ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms)
             Ru Rw Hka Hpa).
  - cbn [cpat_f pAllP] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_quant_elim n G B env 3 y _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 3) (FOVar (B + 2)) a)) by wk_in;
      assert (Hya : FOPrH n G1 (FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hpa : FOPrH n G1 (FOPATF (B + 8) env (cpat_f (rho_hide y rho) P) (FOVar (B + 6))))
        by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (Hm1 : FOPrH n G1 (FONUMR wm m)) by wk Hm;
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    destruct (Nat.eqb_spec y x) as [->|Hne].
    + exact (FOPrH_N4_quant_eq n _ (FOnumeral x) m a 3 (FOVar (B + 2)) (FOnumeral x)
               (FOVar (B + 6)) (or_introl eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Hka Hya (FOPrH_refl _ _ _)).
    + assert (Hrho' : forall z i, rho_hide y rho z = Some i -> i < length env).
      { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z y); [discriminate|].
        exact (Hrho z i Hz). }
      assert (Vm : FOtms_avoid [m] 2 1000) by avoid_tms.
      pose proof (FOPrH_free_f n x P _ (rho_hide y rho) env (B + 8) (FOVar (B + 6)) HS1 Hrho'
                    Hpa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Rf.
      destruct (lit_free_f (rho_hide y rho) x P) eqn:Ef.
      * pose proof (FOPrH_numr_row0 n _ wm m (FOnumeral y) Hm1 ltac:(avoid_tms)) as R0.
        pose proof (IHP _ (rho_hide y rho) env (B + 8) (FOVar (B + 6)) HS1 (ex_intro _ wm Hm1)
                      Hrho' Hpa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms))
          as R4.
        exact (FOPrH_N4_quant_fr n _ (FOnumeral x) m a (FOnumeral 1) 3 (FOVar (B + 2))
                 (FOnumeral y) (FOVar (B + 6)) (or_introl eq_refl)
                 ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Rf R0 R4 Hka Hya
                 (FOPrH_num_neq n _ y x Hne)).
      * exact (FOPrH_N4_quant_nf n _ (FOnumeral x) m a 3 (FOVar (B + 2)) (FOnumeral y)
                 (FOVar (B + 6)) (or_introl eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
                 ltac:(avoid_tms) Rf Hka Hya (FOPrH_num_neq n _ y x Hne)).
  - cbn [cpat_f pExP] in *. span_h HGs. span_h Havs.
    apply (FOPrH_patf_quant_elim n G B env 4 y _ a _ Ha ltac:(lia));
      [span_g; exact HGs | intros w1 H1 H2; span_h H2; free_fm | span_g; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (Hka : FOPrH n G1 (FOcpairF (FOnumeral 4) (FOVar (B + 2)) a)) by wk_in;
      assert (Hya : FOPrH n G1 (FOcpairF (FOnumeral y) (FOVar (B + 6)) (FOVar (B + 2))))
        by wk_in;
      assert (Hpa : FOPrH n G1 (FOPATF (B + 8) env (cpat_f (rho_hide y rho) P) (FOVar (B + 6))))
        by wk_in;
      assert (HS1 : SlotCtx n env G1) by (apply SlotCtx_ext; [exact HS | ctx_list]);
      assert (Hm1 : FOPrH n G1 (FONUMR wm m)) by wk Hm;
      assert (HG1 : FOctx_avoid G1 2 1000) by (destruct HS1; tauto)
    end.
    destruct (Nat.eqb_spec y x) as [->|Hne].
    + exact (FOPrH_N4_quant_eq n _ (FOnumeral x) m a 4 (FOVar (B + 2)) (FOnumeral x)
               (FOVar (B + 6)) (or_intror eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
               ltac:(avoid_tms) Hka Hya (FOPrH_refl _ _ _)).
    + assert (Hrho' : forall z i, rho_hide y rho z = Some i -> i < length env).
      { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z y); [discriminate|].
        exact (Hrho z i Hz). }
      assert (Vm : FOtms_avoid [m] 2 1000) by avoid_tms.
      pose proof (FOPrH_free_f n x P _ (rho_hide y rho) env (B + 8) (FOVar (B + 6)) HS1 Hrho'
                    Hpa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms)) as Rf.
      destruct (lit_free_f (rho_hide y rho) x P) eqn:Ef.
      * pose proof (FOPrH_numr_row0 n _ wm m (FOnumeral y) Hm1 ltac:(avoid_tms)) as R0.
        pose proof (IHP _ (rho_hide y rho) env (B + 8) (FOVar (B + 6)) HS1 (ex_intro _ wm Hm1)
                      Hrho' Hpa ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms))
          as R4.
        exact (FOPrH_N4_quant_fr n _ (FOnumeral x) m a (FOnumeral 1) 4 (FOVar (B + 2))
                 (FOnumeral y) (FOVar (B + 6)) (or_intror eq_refl)
                 ltac:(intros w1 ? ?; apply HG1; lia) ltac:(avoid_tms) Rf R0 R4 Hka Hya
                 (FOPrH_num_neq n _ y x Hne)).
      * exact (FOPrH_N4_quant_nf n _ (FOnumeral x) m a 4 (FOVar (B + 2)) (FOnumeral y)
                 (FOVar (B + 6)) (or_intror eq_refl) ltac:(intros w1 ? ?; apply HG1; lia)
                 ltac:(avoid_tms) Rf Hka Hya (FOPrH_num_neq n _ y x Hne)).
Qed.

(** ** The provability matrix with the template code fixed.

    [FOPRu cores u0 c]: the matrix at target [c] with the template
    code [u0] substituted for variable [0]; for [u0] the code of the
    level template this is the provability sentence at [c]. *)

Definition FOPRu (cores : list nat) (u0 : nat) (c : FOTerm) : FOFormula :=
  FOsubst_f 0 (FOnumeral u0) (FOPRMATx cores c).

Lemma FOPrH_fix0 : forall n G u0 A,
  FOfree_ctx 0 G -> FOPrH n G A -> FOPrH n G (FOsubst_f 0 (FOnumeral u0) A).
Proof.
  intros n G u0 A HG H.
  apply (FOPrH_inst n G 0 (FOnumeral u0)); [|apply FOsubst_ok_numeral].
  apply FOPrH_all_intro; [exact HG | exact H].
Qed.

Lemma FOPrH_mpu : forall n G cores u0 a b c,
  FOctx_avoid G 0 500 ->
  FOPrH n G (FOPATF 52 [b; c] cpatImpl01 a) -> FOPrH n G (FOGUARDB c) ->
  FOtms_avoid [a; b; c] 1 500 ->
  FOPrH n G (FOPRu cores u0 a) -> FOPrH n G (FOPRu cores u0 b) ->
  FOPrH n G (FOPRu cores u0 c).
Proof.
  intros n G cores u0 a b c HG HP HB Hav Ha Hb.
  pose proof (FOPrH_D2_gen n G cores a b c ltac:(intros w ? ?; apply HG; lia) HP HB Hav) as H.
  pose proof (FOPrH_fix0 n G u0 _ ltac:(apply HG; lia) H) as H'.
  rewrite !FOsubst_f_impl in H'.
  exact (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ H' Ha) Hb).
Qed.

(** ** A strict bound separates. *)

Lemma FOPrH_le_neq : forall n G t u,
  FOPrH n G (FOle (FOSucc t) u) -> FOctx_avoid G 498 499 -> FOtms_avoid [t; u] 498 499 ->
  FOPrH n G (FONeg (FOEq t u)).
Proof.
  intros n G t u H HG Hav. unfold FONeg. apply FOPrH_intro.
  unfold FOle in H.
  refine (FOPrH_ex_elim _ _ 498 _ FOFalseF _ _ (FOPrH_weak_app _ _ _ _ H) _);
    [free_ctx | reflexivity |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (E1 : FOPrH n Gc (FOEq (FOPlus (FOSucc t) (FOVar 498)) u)) by apply FOPrH_last;
    assert (E2 : FOPrH n Gc (FOEq t u)) by wk_in
  end.
  apply (FOPrH_add_succ_absurd n _ t (FOVar 498)).
  apply (FOPrH_eq_trans _ _ _ (FOPlus (FOSucc t) (FOVar 498)) _);
    [apply FOPrH_ring; fo_ring|].
  exact (FOPrH_eq_trans _ _ _ _ _ E1 (FOPrH_eq_sym _ _ _ _ E2)).
Qed.

(** ** Every pattern code carries its guard. *)

Lemma FOPrH_guard_code : forall n G A rho env B e,
  SlotCtx n env G -> (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FOPATF B env (cpat_f rho A) e) ->
  1000 <= B ->
  FOctx_avoid G B (B + 2 * cpat_span (cpat_f rho A)) ->
  FOtms_avoid (e :: env) B (B + 2 * cpat_span (cpat_f rho A)) ->
  FOtms_avoid (e :: env) 2 1000 ->
  FOPrH n G (FOGUARDB e).
Proof.
  intros n G A rho env B e HS Hrho H HB HG Hav Hlo.
  pose proof HS as [HG2 Hslot].
  pose proof (FOPrH_patf_rebase _ n G B (B + cpat_span (cpat_f rho A)) env e H ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(intros w ? ?; apply HG; lia) ltac:(avoid_tms)
                ltac:(avoid_tms) ltac:(avoid_tms)) as H'.
  assert (Hlit : forall G' y, (forall Y, In Y G -> In Y G') ->
            FOPrH n G' (FOle (FOSucc (FOnumeral y)) (FOSucc e)) -> ox_eq None y = false ->
            FOPrH n G' (FONeg (FOEq (FOnumeral y) (FOSucc e)))).
  { intros G' y Hinc Hle _.
    (* the context [G'] may carry any variable: argue in the empty context *)
    refine (FOPrH_mp _ _ _ _ _ Hle). apply FOPrH_empty. apply FOPrH_intro.
    apply FOPrH_le_neq; [apply FOPrH_last | ctx_list | avoid_tms]. }
  assert (HE : RowEnv None (FOSucc e) (FOSucc e) FOZero env env 0).
  { split; [reflexivity|]. split; [exact I|]. split; [exact I|]. avoid_tms. }
  assert (HC : RowCtx n None (FOSucc e) (FOSucc e) env G).
  { split; [exact HG2|]. split; [exact Hslot | exact Hlit]. }
  pose proof (FOPrH_rows_f n None (FOSucc e) (FOSucc e) FOZero env env 0 A G rho B
                (B + cpat_span (cpat_f rho A)) e e HE HC Hrho I H H'
                (FOPrH_le_refl n G (FOSucc e) ltac:(avoid_tm)) HB ltac:(lia)
                ltac:(cbn [rho_sub]; lia)
                ltac:(intros w ? ?; apply HG; lia)
                ltac:(intros w ? ?; apply HG; cbn [rho_sub] in *; lia)
                ltac:(avoid_tms) ltac:(cbn [rho_sub]; avoid_tms) ltac:(avoid_tms)) as R.
  exact (FOPrH_guard_of_row n G e e ltac:(intros w ? ?; apply HG2; lia) ltac:(avoid_tms) R).
Qed.

(** ** Freshness of the provability matrix with the template fixed. *)

Lemma FOfree_in_PRu : forall cores u0 w c,
  18 <= w -> FOtms_avoid [c] w (S w) -> FOfree_in w (FOPRu cores u0 c) = false.
Proof.
  intros cores u0 w c Hw Hav. unfold FOPRu.
  rewrite FOsubst_f_num, FOfree_in_subst_num.
  destruct (Nat.eqb w 0); [reflexivity|]. apply FOfree_in_PRMATx; [exact Hw | exact Hav].
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (FOPRu _ _ _) = false => apply FOfree_in_PRu; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOTBLEX3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_TBLEX3_any; [nat_fast | avoid_tms]
  | |- FOfree_in ?w (FOBexC ?v _ _) = false =>
      first [ constr_eq w v; apply FOfree_in_FOBexC_self
            | rewrite FOBexC_ltv; free_fm ]
  | |- FOfree_in _ (FOJUSTCK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOJUSTCK_free
  | |- FOfree_in _ (FOGUARDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOGUARDC_free
  | |- FOfree_in _ (FONUMR _ _) = false => unfold FONUMR; free_fm
  | |- FOfree_in _ (FOTBLEX _ _ _ _ _) = false =>
      apply FOfree_in_TBLEX_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOM3F _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_M3F_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOFTRACK _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_FTRACK_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOJTRACK _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_JTRACK_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOPATF _ _ _ _) = false =>
      apply FOfree_in_PATF_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOGUARDB _) = false =>
      apply FOfree_in_GUARDB_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOTEXT _ _ _ _ _ _ _) = false => unfold FOTEXT; free_fm
  | |- FOfree_in _ (FOTBLNEW _ _ _ _ _ _ _) = false => unfold FOTBLNEW; free_fm
  | |- FOfree_in _ (FOINCL _ _) = false =>
      apply FOfree_in_INCL_any; [nat_fast | avoid_tms]
  | |- _ => free_fm_core
  end.

(** ** Slot contexts extended by one numeral code. *)

Lemma SlotCtx_snoc : forall n env G m w,
  SlotCtx n env G -> FOPrH n G (FONUMR w m) -> SlotCtx n (env ++ [m]) G.
Proof.
  intros n env G m w [HG Hs] Hm. split; [exact HG|]. intros i Hi.
  rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.lt_ge_cases i (length env)) as [Hlt|Hge].
  - rewrite app_nth1 by exact Hlt. exact (Hs i Hlt).
  - assert (Ei : i = length env) by lia. subst i.
    rewrite app_nth2 by lia. rewrite Nat.sub_diag. exists w. exact Hm.
Qed.

Lemma rho_sub_hide_self : forall x j rho z,
  rho_sub (Some x) j (rho_hide x rho) z = rho_sub (Some x) j rho z.
Proof.
  intros x j rho z. unfold rho_sub, rho_hide. destruct (Nat.eqb z x); reflexivity.
Qed.

(** ** Guard rows below an arbitrary bound. *)

Lemma FOPrH_guard_rows : forall n G A rho env B e X,
  SlotCtx n env G -> (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FOPATF B env (cpat_f rho A) e) ->
  FOPrH n G (FOle (FOSucc e) X) ->
  1000 <= B ->
  FOctx_avoid G B (B + 2 * cpat_span (cpat_f rho A)) ->
  FOtms_avoid (e :: X :: env) B (B + 2 * cpat_span (cpat_f rho A)) ->
  FOtms_avoid (e :: X :: env) 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 3) X FOZero e e).
Proof.
  intros n G A rho env B e X HS Hrho H Hle HB HG Hav Hlo.
  pose proof HS as [HG2 Hslot].
  pose proof (FOPrH_patf_rebase _ n G B (B + cpat_span (cpat_f rho A)) env e H ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(intros w ? ?; apply HG; lia) ltac:(avoid_tms)
                ltac:(avoid_tms) ltac:(avoid_tms)) as H'.
  assert (Hlit : forall G' y, (forall Y, In Y G -> In Y G') ->
            FOPrH n G' (FOle (FOSucc (FOnumeral y)) X) -> ox_eq None y = false ->
            FOPrH n G' (FONeg (FOEq (FOnumeral y) X))).
  { intros G' y Hinc Hy _.
    refine (FOPrH_mp _ _ _ _ _ Hy). apply FOPrH_empty. apply FOPrH_intro.
    apply FOPrH_le_neq; [apply FOPrH_last | ctx_list | avoid_tms]. }
  assert (HE : RowEnv None X X FOZero env env 0).
  { split; [reflexivity|]. split; [exact I|]. split; [exact I|]. avoid_tms. }
  assert (HC : RowCtx n None X X env G).
  { split; [exact HG2|]. split; [exact Hslot | exact Hlit]. }
  exact (FOPrH_rows_f n None X X FOZero env env 0 A G rho B
           (B + cpat_span (cpat_f rho A)) e e HE HC Hrho I H H' Hle HB ltac:(lia)
           ltac:(cbn [rho_sub]; lia)
           ltac:(intros w ? ?; apply HG; lia)
           ltac:(intros w ? ?; apply HG; cbn [rho_sub] in *; lia)
           ltac:(avoid_tms) ltac:(cbn [rho_sub]; avoid_tms) ltac:(avoid_tms)).
Qed.

(** ** The small rule patterns built from pairing facts. *)

Lemma FOPrH_patf_impl01 : forall n G a b c q,
  FOPrH n G (FOcpairF (FOnumeral 2) q a) -> FOPrH n G (FOcpairF b c q) ->
  FOtms_avoid [a; b; c; q] 44 80 -> FOtms_avoid [a; b; c; q] 420 500 ->
  FOPrH n G (FOPATF 52 [b; c] cpatImpl01 a).
Proof.
  intros n G a b c q Ha Hq Hav Hav2. unfold cpatImpl01, pImpP.
  apply (FOPrH_patf_pair_intro_lo n G 52 [b; c] (CLit 2) (CPair (CVarP 0) (CVarP 1)) a
           (FOnumeral 2) q Ha (FOPrH_patf_lit _ _ _ _ _)).
  - apply (FOPrH_patf_pair_intro_lo n G 56 [b; c] (CVarP 0) (CVarP 1) q b c Hq
             (FOPrH_patf_slot _ _ _ _ 0) (FOPrH_patf_slot _ _ _ _ 1));
      [lia | vm_compute; lia | cbn [cpat_span cpat_pairs]; avoid_tms | avoid_tms].
  - lia.
  - vm_compute; lia.
  - cbn [cpat_span cpat_pairs]; avoid_tms.
  - avoid_tms.
Qed.

Lemma FOPrH_patf_allelim : forall n G x a c d q d0 p,
  FOPrH n G (FOcpairF (FOnumeral 2) q d) -> FOPrH n G (FOcpairF d0 c q) ->
  FOPrH n G (FOcpairF (FOnumeral 3) p d0) -> FOPrH n G (FOcpairF x a p) ->
  FOtms_avoid [x; a; c; d; q; d0; p] 44 80 -> FOtms_avoid [x; a; c; d; q; d0; p] 420 500 ->
  FOPrH n G (FOPATF 44 [x; a; c] cpatAllElim d).
Proof.
  intros n G x a c d q d0 p Hd Hq Hd0 Hp Hav Hav2. unfold cpatAllElim, pImpP, pAllP.
  apply (FOPrH_patf_pair_intro_lo n G 44 [x; a; c] (CLit 2)
           (CPair (CPair (CLit 3) (CPair (CVarP 0) (CVarP 1))) (CVarP 2)) d (FOnumeral 2) q Hd
           (FOPrH_patf_lit _ _ _ _ _));
    [| lia | vm_compute; lia | cbn [cpat_span cpat_pairs]; avoid_tms | avoid_tms].
  apply (FOPrH_patf_pair_intro_lo n G 48 [x; a; c] (CPair (CLit 3) (CPair (CVarP 0) (CVarP 1)))
           (CVarP 2) q d0 c Hq);
    [| exact (FOPrH_patf_slot _ _ _ _ 2) | lia | vm_compute; lia
     | cbn [cpat_span cpat_pairs]; avoid_tms | avoid_tms].
  apply (FOPrH_patf_pair_intro_lo n G 52 [x; a; c] (CLit 3) (CPair (CVarP 0) (CVarP 1)) d0
           (FOnumeral 3) p Hd0 (FOPrH_patf_lit _ _ _ _ _));
    [| lia | vm_compute; lia | cbn [cpat_span cpat_pairs]; avoid_tms | avoid_tms].
  exact (FOPrH_patf_pair_intro_lo n G 56 [x; a; c] (CVarP 0) (CVarP 1) p x a Hp
           (FOPrH_patf_slot _ _ _ _ 0) (FOPrH_patf_slot _ _ _ _ 1) ltac:(lia)
           ltac:(vm_compute; lia) ltac:(cbn [cpat_span cpat_pairs]; avoid_tms)
           ltac:(avoid_tms)).
Qed.

(** ** Pattern facts have no free variable below their base other than
    those of their terms. *)

Lemma FOfree_in_PATF_lo : forall p w B env d,
  w < B -> FOtms_avoid (d :: env) w (S w) -> FOfree_in w (FOPATF B env p d) = false.
Proof.
  induction p as [k|i|q IH|a IHa b IHb]; intros w B env d Hw Hav; cbn [FOPATF].
  - cbn [FOfree_in]. rewrite (Hav d (or_introl eq_refl) w ltac:(lia) ltac:(lia)).
    rewrite FOin_tm_numeral. reflexivity.
  - cbn [FOfree_in]. rewrite (Hav d (or_introl eq_refl) w ltac:(lia) ltac:(lia)).
    destruct (nth_in_or_default i env FOZero) as [Hin| ->].
    + rewrite (Hav _ (or_intror Hin) w ltac:(lia) ltac:(lia)). reflexivity.
    + reflexivity.
  - rewrite FOBexC_ltv, FOfree_in_FOExists_neq by lia.
    rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    + apply FOfree_in_ltv; [lia | apply (Hav d (or_introl eq_refl)); lia].
    + rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
      * cbn [FOfree_in FOin_tm]. rewrite (Hav d (or_introl eq_refl) w ltac:(lia) ltac:(lia)).
        cbn [orb]. apply Nat.eqb_neq. lia.
      * apply IH; [lia|]. intros t Ht. destruct Ht as [<-|Ht].
        -- apply FOtm_avoid_var. lia.
        -- apply Hav. right. exact Ht.
  - rewrite FOBexC_ltv, FOfree_in_FOExists_neq by lia.
    rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    + apply FOfree_in_ltv; [lia|]. rewrite FOin_tm_succ_eq.
      apply (Hav d (or_introl eq_refl)); lia.
    + rewrite FOBexC_ltv, FOfree_in_FOExists_neq by lia.
      rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
      * apply FOfree_in_ltv; [lia|]. rewrite FOin_tm_succ_eq.
        apply (Hav d (or_introl eq_refl)); lia.
      * rewrite !FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
        -- rewrite FOfree_in_FOcpairF. cbn [FOin_tm].
           rewrite (Hav d (or_introl eq_refl) w ltac:(lia) ltac:(lia)).
           rewrite (proj2 (Nat.eqb_neq B w) ltac:(lia)),
             (proj2 (Nat.eqb_neq (B + 2) w) ltac:(lia)). reflexivity.
        -- apply Bool.orb_false_iff. split.
           ++ apply IHa; [lia|]. intros t Ht. destruct Ht as [<-|Ht].
              ** apply FOtm_avoid_var. lia.
              ** apply Hav. right. exact Ht.
           ++ apply IHb; [lia|]. intros t Ht. destruct Ht as [<-|Ht].
              ** apply FOtm_avoid_var. lia.
              ** apply Hav. right. exact Ht.
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (FOPRu _ _ _) = false => apply FOfree_in_PRu; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOTBLEX3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_TBLEX3_any; [nat_fast | avoid_tms]
  | |- FOfree_in ?w (FOBexC ?v _ _) = false =>
      first [ constr_eq w v; apply FOfree_in_FOBexC_self
            | rewrite FOBexC_ltv; free_fm ]
  | |- FOfree_in _ (FOJUSTCK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOJUSTCK_free
  | |- FOfree_in _ (FOGUARDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOGUARDC_free
  | |- FOfree_in _ (FONUMR _ _) = false => unfold FONUMR; free_fm
  | |- FOfree_in _ (FOTBLEX _ _ _ _ _) = false =>
      apply FOfree_in_TBLEX_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOM3F _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_M3F_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOFTRACK _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_FTRACK_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOJTRACK _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_JTRACK_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOPATF _ _ _ _) = false =>
      first [ apply FOfree_in_PATF_any; [nat_fast | avoid_tms]
            | apply FOfree_in_PATF_lo; [nat_fast | avoid_tms] ]
  | |- FOfree_in _ (FOGUARDB _) = false =>
      apply FOfree_in_GUARDB_any; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FOTEXT _ _ _ _ _ _ _) = false => unfold FOTEXT; free_fm
  | |- FOfree_in _ (FOTBLNEW _ _ _ _ _ _ _) = false => unfold FOTBLNEW; free_fm
  | |- FOfree_in _ (FOINCL _ _) = false =>
      apply FOfree_in_INCL_any; [nat_fast | avoid_tms]
  | |- _ => free_fm_core
  end.

(** ** Instantiation inside the provability predicate.

    From the provability of the code [d0] of [forall x th] (with slot
    map [rho] over [env]) follows the provability of the code [c] of
    [th] with [x] turned into a new slot holding the numeral code [m]:
    a one-line universal-elimination derivation of [d0 -> c], whose
    substitution, capture and guard rows are built by the row
    recursions, followed by internal modus ponens.  The names [N],
    [N + 1], [N + 2] hold the pairing codes of the implication and the
    payload. *)

Lemma FOPrH_inst_code : forall n G cores u0 x th rho env m wm B0 d0 B1 c N,
  SlotCtx n env G ->
  (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FONUMR wm m) ->
  FOPrH n G (FOPATF B0 env (cpat_f rho (FOForall x th)) d0) ->
  FOPrH n G (FOPATF B1 (env ++ [m]) (cpat_f (rho_sub (Some x) (length env) rho) th) c) ->
  FOPrH n G (FOPRu cores u0 d0) ->
  FOctx_avoid G 0 1000 ->
  1000 <= N -> FOctx_avoid G N (N + 3) ->
  N + 3 <= B0 ->
  B0 + 2 * cpat_span (cpat_f rho (FOForall x th)) <= B1 ->
  FOctx_avoid G B0 (B0 + 2 * cpat_span (cpat_f rho (FOForall x th))) ->
  FOctx_avoid G B1 (B1 + 2 * cpat_span (cpat_f (rho_sub (Some x) (length env) rho) th)) ->
  FOtms_avoid (d0 :: c :: m :: env) 0 1000 ->
  FOtms_avoid (d0 :: c :: m :: env) N (N + 3) ->
  FOtms_avoid (d0 :: c :: m :: env) B0 (B0 + 2 * cpat_span (cpat_f rho (FOForall x th))) ->
  FOtms_avoid (d0 :: c :: m :: env) B1
    (B1 + 2 * cpat_span (cpat_f (rho_sub (Some x) (length env) rho) th)) ->
  FOPrH n G (FOPRu cores u0 c).
Proof.
  intros n G cores u0 x th rho env m wm B0 d0 B1 c N HS Hrho Hm Hd0 Hc Hpr HG0 HN HGN HNB
    HB01 HGB0 HGB1 Hlo HavN Hav0 Hav1.
  assert (Hsp : cpat_span (cpat_f rho (FOForall x th))
                = 8 + cpat_span (cpat_f (rho_hide x rho) th)).
  { cbn [cpat_f pAllP cpat_span cpat_pairs]. lia. }
  rewrite Hsp in HB01, HGB0, Hav0.
  (* the pairing codes of the implication [d0 -> c] *)
  apply (FOPrH_cpair_elim_hi n G d0 c N);
    [intros w ? ?; apply HG0; lia | avoid_tms | lia | apply HGN; lia | free_fm | avoid_tms |].
  apply (FOPrH_cpair_elim_hi n _ (FOnumeral 2) (FOVar N) (N + 1));
    [ctx_list | avoid_tms | lia | free_ctx | free_fm | avoid_tms |].
  lazymatch goal with |- FOPrH _ ?G2 _ =>
    assert (Hq : FOPrH n G2 (FOcpairF d0 c (FOVar N))) by wk_in;
    assert (Hd : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar N) (FOVar (N + 1))))
      by apply FOPrH_last;
    assert (HS2 : SlotCtx n env G2) by (apply SlotCtx_ext; [apply SlotCtx_ext;
                                          [exact HS | ctx_list] | ctx_list]);
    assert (Hm2 : FOPrH n G2 (FONUMR wm m)) by wk Hm;
    assert (Hd02 : FOPrH n G2 (FOPATF B0 env (cpat_f rho (FOForall x th)) d0)) by wk Hd0;
    assert (Hc2 : FOPrH n G2 (FOPATF B1 (env ++ [m])
                               (cpat_f (rho_sub (Some x) (length env) rho) th) c)) by wk Hc;
    assert (Hpr2 : FOPrH n G2 (FOPRu cores u0 d0)) by wk Hpr;
    assert (HG02 : FOctx_avoid G2 0 1000) by ctx_list;
    assert (HGB02 : FOctx_avoid G2 B0
                      (B0 + 2 * (8 + cpat_span (cpat_f (rho_hide x rho) th)))) by ctx_list;
    assert (HGB12 : FOctx_avoid G2 B1
                      (B1 + 2 * cpat_span (cpat_f (rho_sub (Some x) (length env) rho) th)))
      by ctx_list;
    assert (HGN2 : FOctx_avoid G2 (N + 2) (N + 3)) by ctx_list
  end.
  destruct (FOPrH_cpair_le_cf n _ d0 c (FOVar N) ltac:(avoid_tms) Hq) as [Ld0q Lcq].
  destruct (FOPrH_cpair_le_cf n _ (FOnumeral 2) (FOVar N) (FOVar (N + 1)) ltac:(avoid_tms) Hd)
    as [_ Lqd].
  pose proof (FOPrH_le_trans n _ d0 (FOVar N) (FOVar (N + 1)) Ld0q Lqd ltac:(avoid_tms)) as Ld0d.
  pose proof (FOPrH_le_trans n _ c (FOVar N) (FOVar (N + 1)) Lcq Lqd ltac:(avoid_tms)) as Lcd.
  pose proof (FOPrH_le_succ_of_le n _ d0 (FOVar (N + 1)) Ld0d ltac:(avoid_tms)) as Sd0.
  pose proof (FOPrH_le_succ_of_le n _ c (FOVar (N + 1)) Lcd ltac:(avoid_tms)) as Sc.
  (* guard rows of the implication code *)
  pose proof (FOPrH_guard_rows n _ (FOForall x th) rho env B0 d0 (FOSucc (FOVar (N + 1)))
                HS2 Hrho Hd02 Sd0 ltac:(lia) ltac:(rewrite Hsp; exact HGB02)
                ltac:(rewrite Hsp; avoid_tms) ltac:(avoid_tms)) as R0.
  pose proof (SlotCtx_snoc n env _ m wm HS2 Hm2) as HS2'.
  assert (Hrc : forall z i, rho_sub (Some x) (length env) rho z = Some i ->
                  i < length (env ++ [m])).
  { intros z i Hz. unfold rho_sub in Hz. rewrite length_app. cbn [length].
    destruct (Nat.eqb z x); [injection Hz as <-; lia | pose proof (Hrho z i Hz); lia]. }
  pose proof (FOPrH_guard_rows n _ th (rho_sub (Some x) (length env) rho) (env ++ [m]) B1 c
                (FOSucc (FOVar (N + 1))) HS2' Hrc Hc2 Sc ltac:(lia) HGB12 ltac:(avoid_tms)
                ltac:(avoid_tms)) as Rc.
  pose proof (FOPrH_N3_impl n _ (FOSucc (FOVar (N + 1))) FOZero (FOVar (N + 1)) (FOVar (N + 1))
                (FOVar N) d0 c d0 c (FOVar N) ltac:(intros w ? ?; apply HG02; lia)
                ltac:(avoid_tms) R0 Rc Hd Hq Hq Hd) as Rd.
  pose proof (FOPrH_guard_code n _ th (rho_sub (Some x) (length env) rho) (env ++ [m]) B1 c
                HS2' Hrc Hc2 ltac:(lia) HGB12 ltac:(avoid_tms) ltac:(avoid_tms)) as Gc.
  (* the body of the universal *)
  apply (FOPrH_patf_quant_elim n _ B0 env 3 x (cpat_f (rho_hide x rho) th) d0 _ Hd02 ltac:(lia));
    [cbn [cpat_span cpat_pairs]; intros w ? ?; apply HGB02; lia
    | intros w ? ?; cbn [cpat_span cpat_pairs] in *; free_fm
    | cbn [cpat_span cpat_pairs]; avoid_tms |].
  lazymatch goal with |- FOPrH _ ?G3 _ =>
    assert (Hk0 : FOPrH n G3 (FOcpairF (FOnumeral 3) (FOVar (B0 + 2)) d0)) by wk_in;
    assert (Hx0 : FOPrH n G3 (FOcpairF (FOnumeral x) (FOVar (B0 + 6)) (FOVar (B0 + 2))))
      by wk_in;
    assert (Hb0 : FOPrH n G3 (FOPATF (B0 + 8) env (cpat_f (rho_hide x rho) th)
                                (FOVar (B0 + 6)))) by wk_in;
    assert (HS3 : SlotCtx n env G3) by (apply SlotCtx_ext; [exact HS2 | ctx_list]);
    assert (Hm3 : FOPrH n G3 (FONUMR wm m)) by wk Hm2;
    assert (Hc3 : FOPrH n G3 (FOPATF B1 (env ++ [m])
                               (cpat_f (rho_sub (Some x) (length env) (rho_hide x rho)) th) c))
      by (rewrite (cpat_f_ext th _ _ (rho_sub_hide_self x (length env) rho)); wk Hc2);
    assert (Rd3 : FOPrH n G3 (FOTBLEX (FOnumeral 3) (FOSucc (FOVar (N + 1))) FOZero
                                (FOVar (N + 1)) (FOVar (N + 1)))) by wk Rd;
    assert (Gc3 : FOPrH n G3 (FOGUARDB c)) by wk Gc;
    assert (Hpr3 : FOPrH n G3 (FOPRu cores u0 d0)) by wk Hpr2;
    assert (Hq3 : FOPrH n G3 (FOcpairF d0 c (FOVar N))) by wk Hq;
    assert (Hd3 : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar N) (FOVar (N + 1)))) by wk Hd;
    assert (Ld0d3 : FOPrH n G3 (FOle d0 (FOVar (N + 1)))) by wk Ld0d;
    assert (Lcd3 : FOPrH n G3 (FOle c (FOVar (N + 1)))) by wk Lcd;
    assert (HG03 : FOctx_avoid G3 0 1000) by ctx_list;
    assert (HGB13 : FOctx_avoid G3 B1
                      (B1 + 2 * cpat_span (cpat_f (rho_sub (Some x) (length env) rho) th)))
      by ctx_list;
    assert (HGb3 : FOctx_avoid G3 (B0 + 8) (B0 + 8 + cpat_span (cpat_f (rho_hide x rho) th)))
      by ctx_list;
    assert (HGN3 : FOctx_avoid G3 (N + 2) (N + 3)) by ctx_list
  end.
  destruct (FOPrH_cpair_le_cf n _ (FOnumeral 3) (FOVar (B0 + 2)) d0 ltac:(avoid_tms) Hk0)
    as [_ Lp0].
  destruct (FOPrH_cpair_le_cf n _ (FOnumeral x) (FOVar (B0 + 6)) (FOVar (B0 + 2))
              ltac:(avoid_tms) Hx0) as [_ Lap].
  pose proof (FOPrH_le_trans n _ (FOVar (B0 + 6)) (FOVar (B0 + 2)) d0 Lap Lp0 ltac:(avoid_tms))
    as La0.
  pose proof (FOPrH_le_succ_of_le n _ (FOVar (B0 + 6)) d0 La0 ltac:(avoid_tms)) as Sa0.
  (* substitution and capture rows *)
  assert (HE : RowEnv (Some x) (FOnumeral x) (FOSucc d0) m env (env ++ [m]) (length env)).
  { split; [intros i Hi; apply app_nth1; exact Hi|].
    split; [rewrite app_nth2 by lia; rewrite Nat.sub_diag; reflexivity|].
    split; [reflexivity | avoid_tms]. }
  lazymatch goal with |- FOPrH _ ?G3 _ =>
    assert (HC : RowCtx n (Some x) (FOnumeral x) (FOSucc d0) env G3)
      by (split; [intros w ? ?; apply HG03; lia|]; split; [destruct HS3 as [_ Hs3]; exact Hs3|];
          intros G' y _ _ Hne; apply FOPrH_num_neq; cbn [ox_eq] in Hne;
          apply Nat.eqb_neq; exact Hne)
  end.
  assert (Hrho' : forall z i, rho_hide x rho z = Some i -> i < length env).
  { intros z i Hz. unfold rho_hide in Hz. destruct (Nat.eqb z x); [discriminate|].
    exact (Hrho z i Hz). }
  assert (Hrx : rho_hide x rho x = None) by (unfold rho_hide; rewrite Nat.eqb_refl; reflexivity).
  pose proof (FOPrH_rows_f n (Some x) (FOnumeral x) (FOSucc d0) m env (env ++ [m]) (length env)
                th _ (rho_hide x rho) (B0 + 8) B1 (FOVar (B0 + 6)) c HE HC Hrho' Hrx Hb0 Hc3 Sa0
                ltac:(lia) ltac:(lia)
                ltac:(left; rewrite (cpat_f_ext th _ _ (rho_sub_hide_self x (length env) rho))
                           in *; lia)
                HGb3
                ltac:(rewrite (cpat_f_ext th _ _ (rho_sub_hide_self x (length env) rho));
                      intros w ? ?; apply HGB13; lia)
                ltac:(avoid_tms)
                ltac:(rewrite (cpat_f_ext th _ _ (rho_sub_hide_self x (length env) rho));
                      avoid_tms)
                ltac:(avoid_tms)) as R3.
  pose proof (FOPrH_cap_f n x m th _ (rho_hide x rho) env (B0 + 8) (FOVar (B0 + 6)) HS3
                (ex_intro _ wm Hm3) Hrho' Hb0 ltac:(lia) HGb3 ltac:(avoid_tms)
                ltac:(avoid_tms)) as R4.
  pose proof (FOPrH_tblex_join3 n _ (FOnumeral 3) (FOSucc (FOVar (N + 1))) FOZero (FOVar (N + 1))
                (FOVar (N + 1)) (FOnumeral 4) (FOnumeral x) m (FOVar (B0 + 6)) (FOnumeral 1)
                (FOnumeral 3) (FOnumeral x) m (FOVar (B0 + 6)) c
                ltac:(intros w ? ?; apply HG03; lia) ltac:(avoid_tms) Rd3 R4 R3) as H3.
  (* the payload and the one-line derivation *)
  apply (FOPrH_cpair_elim_hi n _ (FOnumeral x) m (N + 2));
    [ctx_list | avoid_tms | lia | apply HGN3; lia | free_fm | avoid_tms |].
  pose proof (FOPrH_le_trans n _ (FOVar (B0 + 6)) d0 (FOVar (N + 1)) La0 Ld0d3 ltac:(avoid_tms))
    as Lad.
  lazymatch goal with |- FOPrH _ ?G4 _ =>
    assert (Hpl : FOPrH n G4 (FOcpairF (FOnumeral x) m (FOVar (N + 2)))) by apply FOPrH_last;
    assert (HG04 : FOctx_avoid G4 0 1000) by ctx_list;
    pose proof (FOPrH_patf_allelim n G4 (FOnumeral x) (FOVar (B0 + 6)) c (FOVar (N + 1))
                  (FOVar N) d0 (FOVar (B0 + 2)) (FOPrH_weak_app _ _ _ _ Hd3)
                  (FOPrH_weak_app _ _ _ _ Hq3) (FOPrH_weak_app _ _ _ _ Hk0)
                  (FOPrH_weak_app _ _ _ _ Hx0) ltac:(avoid_tms) ltac:(avoid_tms)) as HP44;
    pose proof (FOPrH_subst_line n G4 cores (FOVar (N + 1)) cpatAllElim 2 (FOVar (N + 2))
                  (FOVar (N + 1)) (FOnumeral x) m (FOVar (B0 + 6)) c
                  (or_introl (conj eq_refl eq_refl)) ltac:(intros w ? ?; apply HG04; lia)
                  ltac:(avoid_tms) (FOPrH_weak_app _ _ _ _ H3) Hpl
                  (FOPrH_weak_app _ _ _ _ Lad) (FOPrH_weak_app _ _ _ _ Lcd3) HP44) as Hline;
    pose proof (FOPrH_fix0 n G4 u0 _ ltac:(apply HG04; lia) Hline) as Hdu;
    pose proof (FOPrH_patf_impl01 n G4 (FOVar (N + 1)) d0 c (FOVar N)
                  (FOPrH_weak_app _ _ _ _ Hd3) (FOPrH_weak_app _ _ _ _ Hq3)
                  ltac:(avoid_tms) ltac:(avoid_tms)) as HP52;
    exact (FOPrH_mpu n G4 cores u0 (FOVar (N + 1)) d0 c ltac:(intros w ? ?; apply HG04; lia)
             HP52 (FOPrH_weak_app _ _ _ _ Gc3) ltac:(avoid_tms) Hdu
             (FOPrH_weak_app _ _ _ _ Hpr3))
  end.
Qed.

(** ** Entries of a term list. *)

Lemma FOtm_avoid_nth : forall s env lo hi,
  FOtms_avoid env lo hi -> FOtm_avoid (nth s env FOZero) lo hi.
Proof.
  intros s env lo hi H. destruct (nth_in_or_default s env FOZero) as [Hin| ->];
    [exact (H _ Hin) | apply FOtm_avoid_zero].
Qed.

Ltac avoid_tm ::=
  lazymatch goal with
  | |- FOtm_avoid (nth _ _ _) _ _ => apply FOtm_avoid_nth; avoid_tms
  | |- FOtm_avoid (FOnumeral _) _ _ => apply FOtm_avoid_numeral
  | |- FOtm_avoid FOZero _ _ => apply FOtm_avoid_zero
  | |- FOtm_avoid (FOSucc _) _ _ => apply FOtm_avoid_succ; avoid_tm
  | |- FOtm_avoid (FOPlus _ _) _ _ => apply FOtm_avoid_plus; avoid_tm
  | |- FOtm_avoid (FOMult _ _) _ _ => apply FOtm_avoid_mult; avoid_tm
  | |- FOtm_avoid (FOVar _) _ _ =>
      first [ apply FOtm_avoid_var_b; vm_compute; reflexivity
            | apply FOtm_avoid_var; lia ]
  | |- FOtm_avoid ?t ?lo ?hi =>
      match goal with
      | H : FOtms_avoid ?L ?lo' ?hi' |- _ =>
          apply (FOtm_avoid_sub t lo' hi' lo hi); [apply H; in_list | nat_fast | nat_fast]
      end
  end.

Ltac fr_tm ::=
  lazymatch goal with
  | |- FOin_tm ?w (nth _ _ _) = false =>
      apply (FOtm_avoid_nth _ _ w (S w)); [avoid_tms | lia | lia]
  | |- FOin_tm _ (FOVar _) = false => apply FOin_tm_var_ne; nat_fast
  | |- FOin_tm _ (FOnumeral _) = false => apply FOin_tm_numeral
  | |- FOin_tm _ FOZero = false => reflexivity
  | |- FOin_tm _ (FOSucc _) = false => rewrite FOin_tm_succ_eq; fr_tm
  | |- FOin_tm _ (FOPlus _ _) = false =>
      rewrite FOin_tm_plus_eq; apply Bool.orb_false_iff; split; fr_tm
  | |- FOin_tm _ (FOMult _ _) = false =>
      rewrite FOin_tm_mult_eq; apply Bool.orb_false_iff; split; fr_tm
  | |- FOin_tm ?w ?t = false =>
      match goal with H : FOtms_avoid ?L ?lo ?hi |- _ =>
        apply (H t ltac:(in_list) w); nat_fast end
  end.

(** ** Patterns with the same code.

    [CPrel G env env' p p']: the patterns [p] over [env] and [p'] over
    [env'] have the same code, slot by slot: equal slot values, a slot
    whose value codes [0] against the pattern of [0], a slot whose
    value codes a successor against the successor pattern of a slot. *)

Inductive CPrel (n : nat) (G : list FOFormula) (env env' : list FOTerm) : CPat -> CPat -> Prop :=
  | cpr_lit : forall k, CPrel n G env env' (CLit k) (CLit k)
  | cpr_slot : forall s s',
      FOPrH n G (FOEq (nth s env FOZero) (nth s' env' FOZero)) ->
      CPrel n G env env' (CVarP s) (CVarP s')
  | cpr_zero_l : forall s,
      FOPrH n G (FOcpairF (FOnumeral 1) FOZero (nth s env FOZero)) ->
      CPrel n G env env' (CVarP s) tZeroP
  | cpr_zero_r : forall s',
      FOPrH n G (FOcpairF (FOnumeral 1) FOZero (nth s' env' FOZero)) ->
      CPrel n G env env' tZeroP (CVarP s')
  | cpr_succ_l : forall s s',
      FOPrH n G (FOcpairF (FOnumeral 2) (nth s' env' FOZero) (nth s env FOZero)) ->
      CPrel n G env env' (CVarP s) (tSuccP (CVarP s'))
  | cpr_succ_r : forall s s',
      FOPrH n G (FOcpairF (FOnumeral 2) (nth s env FOZero) (nth s' env' FOZero)) ->
      CPrel n G env env' (tSuccP (CVarP s)) (CVarP s')
  | cpr_csucc : forall a a', CPrel n G env env' a a' ->
      CPrel n G env env' (CSuccP a) (CSuccP a')
  | cpr_pair : forall a b a' b', CPrel n G env env' a a' -> CPrel n G env env' b b' ->
      CPrel n G env env' (CPair a b) (CPair a' b').

Lemma CPrel_weaken : forall n G G' env env' p p',
  (forall X, In X G -> In X G') -> CPrel n G env env' p p' -> CPrel n G' env env' p p'.
Proof.
  intros n G G' env env' p p' Hinc H.
  induction H; constructor; try assumption; exact (FOPrH_weaken n G G' _ Hinc H).
Qed.

Lemma CPrel_refl : forall n G env p, (forall s, cpat_occurs s p = true -> True) ->
  CPrel n G env env p p.
Proof.
  intros n G env p _. induction p as [k|s|q IH|a IHa b IHb].
  - constructor.
  - constructor. apply FOPrH_refl.
  - constructor. exact IH.
  - constructor; assumption.
Qed.

Lemma cpat_span_tZeroP : cpat_span tZeroP = 4.
Proof. reflexivity. Qed.

Lemma cpat_span_tSuccP_slot : forall s, cpat_span (tSuccP (CVarP s)) = 4.
Proof. reflexivity. Qed.

(** ** Pattern facts converted along [CPrel]. *)

Lemma FOPrH_patf_conv : forall n G env env' p p',
  CPrel n G env env' p p' ->
  forall G' B B' d, (forall X, In X G -> In X G') ->
  FOPrH n G' (FOPATF B' env' p' d) ->
  500 <= B -> 500 <= B' -> B + cpat_span p <= B' \/ B' + cpat_span p' <= B ->
  FOctx_avoid G' B' (B' + cpat_span p') ->
  FOtms_avoid (d :: env ++ env') B (B + cpat_span p) ->
  FOtms_avoid (d :: env ++ env') B' (B' + cpat_span p') ->
  FOtms_avoid (d :: env ++ env') 420 500 ->
  FOPrH n G' (FOPATF B env p d).
Proof.
  intros n G env env' p p' HR.
  induction HR as [k|s s' E|s E|s' E|s s' E|s s' E|a a' HR IH|a b a' b' HRa IHa HRb IHb];
    intros G' B B' d Hinc H HB HB' Hdis HG Hav Hav' Hlo.
  - exact H.
  - cbn [FOPATF] in H |- *.
    exact (FOPrH_eq_trans _ _ _ _ _ H (FOPrH_eq_sym _ _ _ _ (FOPrH_weaken n G G' _ Hinc E))).
  - cbn [FOPATF]. unfold tZeroP in *. cbn [cpat_span cpat_pairs] in *.
    apply (FOPrH_patf_leaf_elim n G' B' env' 1 0 d _ H ltac:(lia) HG);
      [intros w ? ?; free_fm | avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
      exact (FOPrH_cpair_fun n (G1 ++ [X]) _ _ d (nth s env FOZero) ltac:(avoid_tms)
               (FOPrH_last n G1 X)
               (FOPrH_weak_app _ _ _ _ (FOPrH_weaken n G G' _ Hinc E)))
    end.
  - cbn [FOPATF] in H. unfold tZeroP in *. cbn [cpat_span cpat_pairs] in *.
    pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ (FOPrH_refl _ _ _) (FOPrH_refl _ _ _)
                  (FOPrH_eq_sym _ _ _ _ H) (FOPrH_weaken n G G' _ Hinc E)) as Hc.
    apply (FOPrH_patf_pair_intro n G' B env (CLit 1) (CLit 0) d (FOnumeral 1) FOZero Hc
             (FOPrH_patf_lit _ _ _ _ _) (FOPrH_patf_lit _ _ _ _ 0) HB);
      [cbn [cpat_span cpat_pairs] in Hav |- *; avoid_tms | avoid_tms].
  - cbn [FOPATF]. unfold tSuccP in *. cbn [cpat_span cpat_pairs] in *.
    apply (FOPrH_patf_lit_elim n G' B' env' 2 (CVarP s') d _ H ltac:(lia) HG);
      [intros w ? ?; cbn [cpat_span cpat_pairs] in *; free_fm
      | cbn [cpat_span cpat_pairs]; avoid_tms |].
    lazymatch goal with |- FOPrH _ ?G1 _ =>
      assert (H1 : FOPrH n G1 (FOcpairF (FOnumeral 2) (FOVar (B' + 2)) d)) by wk_in;
      assert (H2 : FOPrH n G1 (FOEq (FOVar (B' + 2)) (nth s' env' FOZero))) by wk_in;
      pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ (FOPrH_refl _ _ _) H2 (FOPrH_refl _ _ _) H1)
        as H3;
      exact (FOPrH_cpair_fun n G1 _ _ d (nth s env FOZero) ltac:(avoid_tms) H3
               (FOPrH_weak_app _ _ _ _ (FOPrH_weaken n G G' _ Hinc E)))
    end.
  - cbn [FOPATF] in H. unfold tSuccP in *. cbn [cpat_span cpat_pairs] in *.
    pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ (FOPrH_refl _ _ _) (FOPrH_refl _ _ _)
                  (FOPrH_eq_sym _ _ _ _ H) (FOPrH_weaken n G G' _ Hinc E)) as Hc.
    apply (FOPrH_patf_pair_intro n G' B env (CLit 2) (CVarP s) d (FOnumeral 2)
             (nth s env FOZero) Hc (FOPrH_patf_lit _ _ _ _ _) (FOPrH_patf_slot _ _ _ _ s) HB);
      [cbn [cpat_span cpat_pairs] in Hav |- *; avoid_tms | avoid_tms].
  - cbn [cpat_span] in Hdis, HG, Hav, Hav'.
    apply (FOPrH_patf_succ_elim_self n G' B' env' a' d _ H HB');
      [cbn [cpat_span]; exact HG | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G0 ++ [?X]) _ => pose proof (FOPrH_last n G0 X) as HX end.
    pose proof (IH _ (B + 2) (B' + 2) (FOVar B')
                  (fun X HX0 => in_or_app _ _ _ (or_introl (Hinc X HX0)))
                  (FOPrH_and_r _ _ _ _ HX) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms))
      as Hq.
    exact (FOPrH_patf_succ_intro n _ B env a d (FOVar B') (FOPrH_and_l _ _ _ _ HX) Hq HB
             ltac:(cbn [cpat_span]; avoid_tms) ltac:(avoid_tms)).
  - pose proof (cpat_span_le a) as Hsa. pose proof (cpat_span_le a') as Hsa'.
    cbn [cpat_span] in Hdis, HG, Hav, Hav'.
    apply (FOPrH_patf_pair_elim_self n G' B' env' a' b' d _ H HB');
      [cbn [cpat_span]; exact HG | intros w H1 H2; cbn [cpat_span] in H2; free_fm
      | cbn [cpat_span]; avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G0 ++ [?X]) _ => pose proof (FOPrH_last n G0 X) as HX end.
    assert (Hinc' : forall X, In X G -> In X (G' ++ [FOAnd (FOcpairF (FOVar B') (FOVar (B' + 2)) d)
                   (FOAnd (FOPATF (B' + 4) env' a' (FOVar B'))
                      (FOPATF (B' + 4 + 4 * cpat_pairs a') env' b' (FOVar (B' + 2))))]))
      by (intros X HX0; apply in_or_app; left; exact (Hinc X HX0)).
    pose proof (IHa _ (B + 4) (B' + 4) (FOVar B') Hinc'
                  (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ HX)) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms))
      as Ha.
    pose proof (IHb _ (B + 4 + 4 * cpat_pairs a) (B' + 4 + 4 * cpat_pairs a') (FOVar (B' + 2))
                  Hinc' (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ HX)) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(ctx_list) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms))
      as Hb.
    exact (FOPrH_patf_pair_intro n _ B env a b d (FOVar B') (FOVar (B' + 2))
             (FOPrH_and_l _ _ _ _ HX) Ha Hb HB ltac:(cbn [cpat_span]; avoid_tms)
             ltac:(avoid_tms)).
Qed.
