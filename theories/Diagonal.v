(******************************************************************************)
(*                                                                            *)
(*                            Provability Verified                            *)
(*                                                                            *)
(*     Part 12 of 12. Inverting closed substitution rows inside T_0.          *)
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

From Provability Require Import Modal Syntax Semantics Internal Transfer Merge
  Derivability Rows Patterns Instances Sigma1.
Open Scope fo_scope.

(** ** Closed pairing facts. *)

Lemma FOPrH_cpair_true : forall n G a b,
  FOPrH n G (FOcpairF (FOnumeral a) (FOnumeral b) (FOnumeral (cpair a b))).
Proof.
  intros n G a b. apply FOPrH_empty. apply FOPrH_true_closed.
  - apply FOs1_d0. apply FOdelta0_FOcpairF.
  - intros v. rewrite FOfree_in_FOcpairF, !FOin_tm_numeral. reflexivity.
  - apply (proj2 (FOsat_FOcpairF _ _ _ _)). rewrite !FOeval_numeral. reflexivity.
Qed.

Lemma FOPrH_cpair_value : forall n G a b r,
  FOtms_avoid [r] 440 442 ->
  FOPrH n G (FOcpairF (FOnumeral a) (FOnumeral b) r) ->
  FOPrH n G (FOEq r (FOnumeral (cpair a b))).
Proof.
  intros n G a b r Hr H.
  exact (FOPrH_cpair_fun n G _ _ r (FOnumeral (cpair a b)) ltac:(avoid_tms) H
           (FOPrH_cpair_true n G a b)).
Qed.

Lemma FOPrH_cpair_closed : forall n G a b a0 b0,
  FOtms_avoid [a; b] 440 445 ->
  FOPrH n G (FOcpairF a b (FOnumeral (cpair a0 b0))) ->
  FOPrH n G (FOAnd (FOEq a (FOnumeral a0)) (FOEq b (FOnumeral b0))).
Proof.
  intros n G a b a0 b0 Hav H.
  pose proof (FOPrH_thm n G _ (FOPr_cpair_inj n)) as D.
  apply (FOPrH_inst n G 440 a) in D;
    [| repeat (apply FOsubst_ok_all; [fr_tm|]); apply FOsubst_ok_impl; [apply FOsubst_ok_eq|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_eq | apply FOsubst_ok_and; apply FOsubst_ok_eq]].
  rewrite !FOsubst_f_all_ne, !FOsubst_f_impl, !FOsubst_f_cpairF, FOsubst_f_and, !FOsubst_f_eq
    in D by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in D by lia.
  apply (FOPrH_inst n G 441 b) in D;
    [| repeat (apply FOsubst_ok_all; [fr_tm|]); apply FOsubst_ok_impl; [apply FOsubst_ok_eq|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_eq | apply FOsubst_ok_and; apply FOsubst_ok_eq]].
  rewrite !FOsubst_f_all_ne, !FOsubst_f_impl, !FOsubst_f_cpairF, FOsubst_f_and, !FOsubst_f_eq
    in D by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in D by lia.
  rewrite (FOsubst_t_not_in a 441 b) in D by fr_tm.
  apply (FOPrH_inst n G 442 (FOnumeral a0)) in D; [|apply FOsubst_ok_numeral].
  rewrite !FOsubst_f_all_ne, !FOsubst_f_impl, !FOsubst_f_cpairF, FOsubst_f_and, !FOsubst_f_eq
    in D by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in D by lia.
  rewrite (FOsubst_t_not_in a 442 _), (FOsubst_t_not_in b 442 _) in D by fr_tm.
  apply (FOPrH_inst n G 443 (FOnumeral b0)) in D; [|apply FOsubst_ok_numeral].
  rewrite !FOsubst_f_all_ne, !FOsubst_f_impl, !FOsubst_f_cpairF, FOsubst_f_and, !FOsubst_f_eq
    in D by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in D by lia.
  rewrite (FOsubst_t_not_in a 443 _), (FOsubst_t_not_in b 443 _), FOsubst_t_numeral in D
    by fr_tm.
  apply (FOPrH_inst n G 444 (FOnumeral (cpair a0 b0))) in D; [|apply FOsubst_ok_numeral].
  rewrite !FOsubst_f_impl, !FOsubst_f_cpairF, FOsubst_f_and, !FOsubst_f_eq in D.
  rewrite FOsubst_t_var_eq' in D.
  rewrite (FOsubst_t_not_in a 444 _), (FOsubst_t_not_in b 444 _), !FOsubst_t_numeral in D
    by fr_tm.
  exact (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ D H) (FOPrH_cpair_true n G a0 b0)).
Qed.

Lemma FOPrH_cpair_tag_ne : forall n G k b a0 b0,
  k <> a0 -> FOtms_avoid [b] 440 445 ->
  FOPrH n G (FOcpairF (FOnumeral k) b (FOnumeral (cpair a0 b0))) -> FOPrH n G FOFalseF.
Proof.
  intros n G k b a0 b0 Hk Hb H.
  pose proof (FOPrH_and_l _ _ _ _
                (FOPrH_cpair_closed n G (FOnumeral k) b a0 b0 ltac:(avoid_tms) H)) as E.
  exact (FOPrH_mp _ _ _ _ (FOPrH_num_neq n G k a0 Hk) E).
Qed.

(** ** The step clause of a row with a known tag. *)

Ltac disp_kill2 t k :=
  apply FOPrH_efq;
  exact (FOPrH_mp _ _ _ _ (FOPrH_num_neq _ _ t k ltac:(lia))
           (FOPrH_and_l _ _ _ _ (FOPrH_last _ _ _))).

Lemma FOPrH_disp_tag2 : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r,
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 2) a1 a2 a3 r) ->
  FOPrH n G (FOSTEP2 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r).
Proof.
  intros n G ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r H. unfold FODISPCASES in H.
  refine (FOPrH_or_elim _ _ _ _ _ H _ _); [disp_kill2 2 0|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill2 2 1|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _);
    [exact (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _))|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill2 2 3|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill2 2 4 | disp_kill2 2 5].
Qed.

Lemma FOPrH_disp_tag3 : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r,
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 3) a1 a2 a3 r) ->
  FOPrH n G (FOSTEP3 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r).
Proof.
  intros n G ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r H. unfold FODISPCASES in H.
  refine (FOPrH_or_elim _ _ _ _ _ H _ _); [disp_kill2 3 0|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill2 3 1|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill2 3 2|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _);
    [exact (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _))|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill2 3 4 | disp_kill2 3 5].
Qed.

(** ** A lookup in the inverted table gives a row. *)

Lemma FOPrH_lookup_tblex : forall n G B tg a1 a2 a3 r,
  FOPrH n G (FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
               (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)) ->
  FOPrH n G (FOlookup B (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
               (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
               tg a1 a2 a3 r) ->
  50 <= B -> B + 22 <= 120 ->
  FOtms_avoid [tg; a1; a2; a3; r] B (B + 22) -> FOtms_avoid [tg; a1; a2; a3; r] 2 122 ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r).
Proof.
  intros n G B tg a1 a2 a3 r HV HL HB1 HB2 Hav1 Hav2.
  pose proof (FOPrH_lookup_rebase n G B 28 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HL ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms))
    as L28.
  exact (FOPrH_tblex_intro n G (FOtabv 122) tg a1 a2 a3 r HV L28
           ltac:(unfold FOtabv, FOtab_terms;
                 cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen Nat.add app];
                 avoid_tms)).
Qed.

Ltac ok_fast_leaf V ::=
  lazymatch goal with
  | |- FOsubst_ok _ _ (FOBexC _ _ _) = true => unfold FOBexC; ok_fast V
  | |- FOsubst_ok _ _ (FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = true =>
      apply FOsubst_ok_lookup; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  | |- FOsubst_ok _ _ (FOROWAG _ _ _ _ _ _) = true =>
      apply FOsubst_ok_ROWAG; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  | |- FOsubst_ok _ _ (FOcpairF _ _ _) = true => apply FOsubst_ok_cpairF
  | |- FOsubst_ok _ _ (FOSHIFTC _ _ _ _) = true =>
      apply FOsubst_ok_SHIFTC; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  | |- FOsubst_ok _ _ (FOSHIFTMP _ _ _) = true =>
      apply FOsubst_ok_SHIFTMP; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  | |- FOsubst_ok _ _ (FOSHROW _ _ _ _ _ _ _) = true =>
      apply FOsubst_ok_SHROW; refine (FOtm_avoid_sub _ _ _ _ _ V _ _); lia
  end.

(** ** Bounded existentials in a context. *)

Lemma FOPrH_bexc_elim : forall n G v t A C,
  FOfree_ctx v G -> FOfree_in v C = false ->
  FOPrH n G (FOBexC v t A) -> FOPrH n (G ++ [A]) C -> FOPrH n G C.
Proof.
  intros n G v t A C HG HC H H0. unfold FOBexC in H.
  refine (FOPrH_ex_elim n G v _ C HG HC H _).
  refine (FOPrH_cut _ _ A C (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _)) _).
  refine (FOPrH_weaken n (G ++ [A]) _ C _ H0).
  intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
  - apply in_or_app. left. apply in_or_app. left. exact HX.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_bexc_rename : forall n G v t A w A' C,
  FOfree_ctx w G -> FOfree_in w C = false -> FOfree_in w A = false -> FOin_tm w t = false ->
  w <> v -> w <> S v -> FOsubst_ok v (FOVar w) A = true -> FOsubst_f v (FOVar w) A = A' ->
  FOPrH n G (FOBexC v t A) -> FOPrH n (G ++ [A']) C -> FOPrH n G C.
Proof.
  intros n G v t A w A' C HG HC HA Ht Hwv HwS Hok HA' H H0. unfold FOBexC in H.
  refine (FOPrH_exe n G v w _ C H HG HC _ _ _).
  - rewrite fv_and. apply Bool.orb_false_iff. split; [|exact HA].
    cbn [FOfree_in]. destruct (Nat.eqb_spec (S v) w) as [E|E]; [lia|].
    cbn [FOin_tm]. rewrite (proj2 (Nat.eqb_neq v w) ltac:(lia)),
      (proj2 (Nat.eqb_neq (S v) w) ltac:(lia)), Ht. reflexivity.
  - apply FOsubst_ok_and; [|exact Hok].
    apply FOsubst_ok_ex; [apply FOin_tm_var_ne; lia | apply FOsubst_ok_eq].
  - rewrite FOsubst_f_and, HA'.
    refine (FOPrH_cut _ _ A' C (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _)) _).
    refine (FOPrH_weaken n (G ++ [A']) _ C _ H0).
    intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
    + apply in_or_app. left. apply in_or_app. left. exact HX.
    + apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_cont1 : forall n G G' X C,
  (forall Z, In Z G -> In Z G') -> FOPrH n G' X -> FOPrH n (G ++ [X]) C -> FOPrH n G' C.
Proof.
  intros n G G' X C Hinc HX H.
  refine (FOPrH_cut _ _ X C HX _). refine (FOPrH_weaken n (G ++ [X]) _ C _ H).
  intros Z HZ. apply in_app_or in HZ. destruct HZ as [HZ|[<-|[]]].
  - apply in_or_app. left. exact (Hinc Z HZ).
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_cont_list : forall n G G' L C,
  (forall Z, In Z G -> In Z G') -> (forall X, In X L -> FOPrH n G' X) ->
  FOPrH n (G ++ L) C -> FOPrH n G' C.
Proof.
  intros n G G' L. revert G G'. induction L as [|X L IH]; intros G G' C Hinc HL H.
  - rewrite app_nil_r in H. exact (FOPrH_weaken n G G' C Hinc H).
  - refine (FOPrH_cut _ _ X C (HL X (or_introl eq_refl)) _).
    apply (IH (G ++ [X]) (G' ++ [X])).
    + intros Z HZ. apply in_app_or in HZ. destruct HZ as [HZ|[<-|[]]].
      * apply in_or_app. left. exact (Hinc Z HZ).
      * apply in_or_app. right. left. reflexivity.
    + intros Y HY. apply FOPrH_weak_app. exact (HL Y (or_intror HY)).
    + rewrite <- app_assoc. exact H.
Qed.

(** ** A tag in the first position of a pair that cannot hold. *)

Lemma FOPrH_kill_bexc : forall n G k X a0 b0 C,
  k <> a0 -> FOfree_ctx 50 G -> FOfree_in 50 C = false ->
  FOPrH n G (FOBexC 50 (FOSucc (FOnumeral (cpair a0 b0)))
               (FOAnd (FOcpairF (FOnumeral k) (FOVar 50) (FOnumeral (cpair a0 b0))) X)) ->
  FOPrH n G C.
Proof.
  intros n G k X a0 b0 C Hk HG HC H.
  refine (FOPrH_bexc_elim n G 50 _ _ C HG HC H _). apply FOPrH_efq.
  exact (FOPrH_cpair_tag_ne n _ k (FOVar 50) a0 b0 Hk ltac:(avoid_tms)
           (FOPrH_and_l _ _ _ _ (FOPrH_last _ _ _))).
Qed.

Lemma FOPrH_kill_zero : forall n G a0 b0 r C, a0 <> 1 ->
  FOPrH n G (FOAnd (FOcpairF (FOnumeral 1) FOZero (FOnumeral (cpair a0 b0)))
               (FOEq r (FOnumeral (cpair a0 b0)))) ->
  FOPrH n G C.
Proof.
  intros n G a0 b0 r C Ha H. apply FOPrH_efq.
  exact (FOPrH_cpair_tag_ne n G 1 FOZero a0 b0 ltac:(lia) ltac:(avoid_tms)
           (FOPrH_and_l _ _ _ _ H)).
Qed.

(** ** A lookup whose source field is a variable equal to a numeral. *)

Lemma FOPrH_lookup_a3_num : forall n G B tg a1 a2 v r m,
  2 <= v -> v < B -> (v < 122 \/ 133 <= v) ->
  FOtms_avoid [tg; a1; a2; r] v (S v) ->
  FOPrH n G (FOEq (FOVar v) (FOnumeral m)) ->
  FOPrH n G (FOlookup B (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
               (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
               tg a1 a2 (FOVar v) r) ->
  FOPrH n G (FOlookup B (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
               (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
               tg a1 a2 (FOnumeral m) r).
Proof.
  intros n G B tg a1 a2 v r m Hv HvB Hvt Hav E H.
  set (L := FOlookup B (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
              (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
              tg a1 a2 (FOVar v) r).
  assert (E1 : FOsubst_f v (FOVar v) L = L) by apply FOsubst_f_id.
  assert (E2 : FOsubst_f v (FOnumeral m) L =
               FOlookup B (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                 (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                 tg a1 a2 (FOnumeral m) r).
  { unfold L. rewrite FOsubst_f_lookup by lia. rewrite FOsubst_t_var_eq'.
    rewrite !FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in tg v _), (FOsubst_t_not_in a1 v _), (FOsubst_t_not_in a2 v _),
      (FOsubst_t_not_in r v _) by fr_tm.
    reflexivity. }
  rewrite <- E2. apply (FOPrH_leibniz n G v (FOVar v) (FOnumeral m) L);
    [apply FOsubst_ok_var_self | apply FOsubst_ok_numeral | exact E | rewrite E1; exact H].
Qed.

(** ** The substitution step at a pair node, inverted at a closed source. *)

Lemma FOPrH_SB_real : forall n G x s k lk rt a b c w1 w2 q C,
  FOctx_avoid G 2 122 -> FOtms_avoid [c] 2 1000 ->
  (forall v, 2 <= v -> v < 122 -> FOfree_in v C = false) ->
  1000 <= w1 -> 1000 <= w2 -> 1000 <= q -> w1 <> w2 -> w1 <> q -> w2 <> q ->
  FOfree_ctx w1 G -> FOfree_ctx w2 G -> FOfree_ctx q G ->
  FOfree_in w1 C = false -> FOfree_in w2 C = false -> FOfree_in q C = false ->
  FOtms_avoid [c] w1 (S w1) -> FOtms_avoid [c] w2 (S w2) -> FOtms_avoid [c] q (S q) ->
  FOPrH n G (FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
               (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)) ->
  FOPrH n G (FOSTEP_substbin 50 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
               (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
               (FOnumeral x) (FOnumeral s) (FOnumeral (cpair k (cpair a b))) c k lk rt) ->
  FOPrH n (G ++ [FOTBLEX (FOnumeral lk) (FOnumeral x) (FOnumeral s) (FOnumeral a) (FOVar w1);
                 FOTBLEX (FOnumeral lk) (FOnumeral x) (FOnumeral s) (FOnumeral b) (FOVar w2);
                 FOcpairF (FOVar w1) (FOVar w2) (FOVar q);
                 FOcpairF (FOnumeral rt) (FOVar q) c]) C ->
  FOPrH n G C.
Proof.
  intros n G x s k lk rt a b c w1 w2 q C HG Hc HCv Hw1 Hw2 Hq H12 H1q H2q HG1 HG2 HGq
    HC1 HC2 HCq Hc1 Hc2 Hcq HV H H0.
  unfold FOSTEP_substbin in H. cbn [Nat.add] in H.
  refine (FOPrH_bexc_elim n G 50 _ _ C ltac:(apply HG; lia) ltac:(apply HCv; lia) H _).
  lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as K50;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as R50
  end.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_cpair_closed n _ (FOnumeral k) (FOVar 50) k
                                     (cpair a b) ltac:(avoid_tms) K50)) as E50.
  refine (FOPrH_bexc_elim n _ 52 _ _ C _ _ R50 _); [free_ctx | apply HCv; lia |].
  refine (FOPrH_bexc_elim n _ 54 _ _ C _ _ (FOPrH_last _ _ _) _); [free_ctx | apply HCv; lia |].
  lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as K54;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as R54;
    assert (E50b : FOPrH n (G1 ++ [X]) (FOEq (FOVar 50) (FOnumeral (cpair a b)))) by wk E50
  end.
  pose proof (FOPrH_cpairF_cong _ _ _ _ _ (FOVar 52) (FOVar 54) (FOnumeral (cpair a b))
                (FOPrH_refl _ _ _) (FOPrH_refl _ _ _) E50b K54) as K54b.
  pose proof (FOPrH_cpair_closed _ _ (FOVar 52) (FOVar 54) a b ltac:(avoid_tms) K54b) as D54.
  pose proof (FOPrH_and_l _ _ _ _ D54) as E52. pose proof (FOPrH_and_r _ _ _ _ D54) as E54.
  assert (V1 : FOtm_avoid (FOVar w1) 2 1000) by (apply FOtm_avoid_var; lia).
  assert (V2 : FOtm_avoid (FOVar w2) 2 1000) by (apply FOtm_avoid_var; lia).
  assert (Vq : FOtm_avoid (FOVar q) 2 1000) by (apply FOtm_avoid_var; lia).
  refine (FOPrH_bexc_rename n _ 56 _ _ w1
            (FOBexC 58 (FOSucc c)
               (FOAnd (FOlookup 60 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                         (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131)
                         (FOVar 132) (FOnumeral lk) (FOnumeral x) (FOnumeral s) (FOVar 52)
                         (FOVar w1))
               (FOAnd (FOlookup 82 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                         (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131)
                         (FOVar 132) (FOnumeral lk) (FOnumeral x) (FOnumeral s) (FOVar 54)
                         (FOVar 58))
                      (FOBexC 104 (FOSucc c)
                         (FOAnd (FOcpairF (FOVar w1) (FOVar 58) (FOVar 104))
                                (FOcpairF (FOnumeral rt) (FOVar 104) c))))))
            C _ HC1 _ _ _ _ _ _ R54 _);
    [free_ctx | free_fm | fr_tm | lia | lia | ok_fast V1
    | autorewrite with fosubst; rewrite ?FOsubst_t_var_eq'; subst_avoid_h Hc; reflexivity |].
  refine (FOPrH_bexc_rename n _ 58 _ _ w2
            (FOAnd (FOlookup 60 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                      (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131)
                      (FOVar 132) (FOnumeral lk) (FOnumeral x) (FOnumeral s) (FOVar 52)
                      (FOVar w1))
            (FOAnd (FOlookup 82 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                      (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131)
                      (FOVar 132) (FOnumeral lk) (FOnumeral x) (FOnumeral s) (FOVar 54)
                      (FOVar w2))
                   (FOBexC 104 (FOSucc c)
                      (FOAnd (FOcpairF (FOVar w1) (FOVar w2) (FOVar 104))
                             (FOcpairF (FOnumeral rt) (FOVar 104) c)))))
            C _ HC2 _ _ _ _ _ _ (FOPrH_last _ _ _) _);
    [free_ctx | free_fm | fr_tm | lia | lia | ok_fast V2
    | autorewrite with fosubst; rewrite ?FOsubst_t_var_eq'; subst_avoid_h Hc; reflexivity |].
  lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as L1;
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X))) as L2;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X))) as B104
  end.
  refine (FOPrH_bexc_rename n _ 104 _ _ q
            (FOAnd (FOcpairF (FOVar w1) (FOVar w2) (FOVar q))
                   (FOcpairF (FOnumeral rt) (FOVar q) c))
            C _ HCq _ _ _ _ _ _ B104 _);
    [free_ctx | free_fm | fr_tm | lia | lia | ok_fast Vq
    | autorewrite with fosubst; rewrite ?FOsubst_t_var_eq'; subst_avoid_h Hc; reflexivity |].
  lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as P1;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as P2;
    assert (HVb : FOPrH n (G1 ++ [X]) (FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124)
                    (FOVar 125) (FOVar 126) (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130)
                    (FOVar 131) (FOVar 132))) by wk HV;
    assert (L1b : FOPrH n (G1 ++ [X]) (FOlookup 60 (FOVar 122) (FOVar 123) (FOVar 124)
                    (FOVar 125) (FOVar 126) (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130)
                    (FOVar 131) (FOVar 132) (FOnumeral lk) (FOnumeral x) (FOnumeral s)
                    (FOVar 52) (FOVar w1))) by wk L1;
    assert (L2b : FOPrH n (G1 ++ [X]) (FOlookup 82 (FOVar 122) (FOVar 123) (FOVar 124)
                    (FOVar 125) (FOVar 126) (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130)
                    (FOVar 131) (FOVar 132) (FOnumeral lk) (FOnumeral x) (FOnumeral s)
                    (FOVar 54) (FOVar w2))) by wk L2;
    assert (E52b : FOPrH n (G1 ++ [X]) (FOEq (FOVar 52) (FOnumeral a))) by wk E52;
    assert (E54b : FOPrH n (G1 ++ [X]) (FOEq (FOVar 54) (FOnumeral b))) by wk E54
  end.
  pose proof (FOPrH_lookup_a3_num n _ 60 (FOnumeral lk) (FOnumeral x) (FOnumeral s) 52
                (FOVar w1) a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(avoid_tms) E52b L1b) as L1c.
  pose proof (FOPrH_lookup_a3_num n _ 82 (FOnumeral lk) (FOnumeral x) (FOnumeral s) 54
                (FOVar w2) b ltac:(lia) ltac:(lia) ltac:(lia) ltac:(avoid_tms) E54b L2b) as L2c.
  pose proof (FOPrH_lookup_tblex n _ 60 (FOnumeral lk) (FOnumeral x) (FOnumeral s)
                (FOnumeral a) (FOVar w1) HVb L1c
                ltac:(lia) ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms)) as T1.
  pose proof (FOPrH_lookup_tblex n _ 82 (FOnumeral lk) (FOnumeral x) (FOnumeral s)
                (FOnumeral b) (FOVar w2) HVb L2c
                ltac:(lia) ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms)) as T2.
  refine (FOPrH_cont_list n G _ _ C _ _ H0).
  - intros Z HZ. repeat (apply in_or_app; left). exact HZ.
  - intros Y [<-|[<-|[<-|[<-|[]]]]]; assumption.
Qed.
