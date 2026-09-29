(******************************************************************************)
(*                                                                            *)
(*                            Provability Verified                            *)
(*                                                                            *)
(*     Part 12 of 12. The diagonal lemma and Loeb's theorem inside T_0.       *)
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

(** ** Disjuncts refuted in the empty context. *)

Lemma FOPrH_or_kl : forall n G A B,
  FOPrH n G (FOOr A B) -> FOPrH n [] (FONeg A) -> FOPrH n G B.
Proof.
  intros n G A B H K. exact (FOPrH_mp _ _ _ _ H (FOPrH_empty _ _ _ K)).
Qed.

Lemma FOPrH_or_kr : forall n G A B,
  FOPrH n G (FOOr A B) -> FOPrH n [] (FONeg B) -> FOPrH n G A.
Proof.
  intros n G A B H K.
  refine (FOPrH_or_elim _ _ _ _ _ H (FOPrH_last _ _ _) _).
  apply FOPrH_efq. exact (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ K) (FOPrH_last _ _ _)).
Qed.

Lemma FOPr_neg_or : forall n A B,
  FOPrH n [] (FONeg A) -> FOPrH n [] (FONeg B) -> FOPrH n [] (FONeg (FOOr A B)).
Proof.
  intros n A B HA HB. apply FOPrH_intro.
  exact (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ HB) (FOPrH_or_kl _ _ _ _ (FOPrH_last _ _ _) HA)).
Qed.

Lemma FOPr_kill_bexc : forall n k X a0 b0, k <> a0 ->
  FOPrH n [] (FONeg (FOBexC 50 (FOSucc (FOnumeral (cpair a0 b0)))
                       (FOAnd (FOcpairF (FOnumeral k) (FOVar 50) (FOnumeral (cpair a0 b0))) X))).
Proof.
  intros n k X a0 b0 Hk. apply FOPrH_intro.
  refine (FOPrH_kill_bexc n _ k X a0 b0 FOFalseF Hk _ eq_refl (FOPrH_last _ _ _)).
  apply FOfree_ctx_app_inv; [apply FOfree_ctx_nil|].
  apply FOfree_ctx_cons; [apply FOfree_in_FOBexC_self | apply FOfree_ctx_nil].
Qed.

Lemma FOPr_kill_zero : forall n a0 b0 r, a0 <> 1 ->
  FOPrH n [] (FONeg (FOAnd (FOcpairF (FOnumeral 1) FOZero (FOnumeral (cpair a0 b0)))
                            (FOEq r (FOnumeral (cpair a0 b0))))).
Proof.
  intros n a0 b0 r Ha. apply FOPrH_intro.
  exact (FOPrH_kill_zero n _ a0 b0 r FOFalseF Ha (FOPrH_last _ _ _)).
Qed.

Ltac kill_d :=
  lazymatch goal with
  | |- FOPrH _ [] (FONeg (FOOr _ _)) => apply FOPr_neg_or; kill_d
  | |- FOPrH _ [] (FONeg (FOAnd (FOcpairF (FOnumeral 1) FOZero _) _)) =>
      apply FOPr_kill_zero; lia
  | |- _ => first [ apply (FOPr_kill_bexc _ 0); lia | apply FOPr_kill_bexc; lia ]
  end.

(** ** Small context and equation helpers. *)

Lemma FOPrH_app2 : forall n G A B,
  FOPrH n (G ++ [A; B]) A /\ FOPrH n (G ++ [A; B]) B.
Proof.
  intros n G A B. split; apply FOPrH_assum; apply in_or_app; right; cbn [In]; auto.
Qed.

Lemma FOPrH_app3 : forall n G A B C,
  FOPrH n (G ++ [A; B; C]) A /\ FOPrH n (G ++ [A; B; C]) B /\ FOPrH n (G ++ [A; B; C]) C.
Proof.
  intros n G A B C. repeat split; apply FOPrH_assum; apply in_or_app; right; cbn [In]; auto.
Qed.

Lemma FOPrH_app4 : forall n G A B C D,
  FOPrH n (G ++ [A; B; C; D]) A /\ FOPrH n (G ++ [A; B; C; D]) B /\
  FOPrH n (G ++ [A; B; C; D]) C /\ FOPrH n (G ++ [A; B; C; D]) D.
Proof.
  intros n G A B C D. repeat split; apply FOPrH_assum; apply in_or_app; right; cbn [In]; auto.
Qed.

Lemma FOPrH_cpair_num2 : forall n G u v r a b,
  FOtms_avoid [r] 440 442 ->
  FOPrH n G (FOEq u (FOnumeral a)) -> FOPrH n G (FOEq v (FOnumeral b)) ->
  FOPrH n G (FOcpairF u v r) -> FOPrH n G (FOEq r (FOnumeral (cpair a b))).
Proof.
  intros n G u v r a b Hr Eu Ev H.
  exact (FOPrH_cpair_value n G a b r Hr
           (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ Eu Ev (FOPrH_refl _ _ _) H)).
Qed.

Lemma FOfree_in_eq_var_num : forall u w k, u <> w ->
  FOfree_in u (FOEq (FOVar w) (FOnumeral k)) = false.
Proof.
  intros u w k H. cbn [FOfree_in FOin_tm]. rewrite FOin_tm_numeral.
  destruct (Nat.eqb_spec u w); [lia|]. destruct (Nat.eqb_spec w u); [lia|]. reflexivity.
Qed.

(** ** The quantifier step at a closed source. *)

Lemma FOPrH_SQ_same : forall n G x s k b c C,
  FOctx_avoid G 2 122 -> FOtms_avoid [c] 2 1000 ->
  (forall v, 2 <= v -> v < 122 -> FOfree_in v C = false) ->
  FOPrH n G (FOSTEP_substquant 50 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
               (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
               (FOnumeral x) (FOnumeral s) (FOnumeral (cpair k (cpair x b))) c k) ->
  FOPrH n (G ++ [FOEq c (FOnumeral (cpair k (cpair x b)))]) C ->
  FOPrH n G C.
Proof.
  intros n G x s k b c C HG Hc HCv H H0.
  unfold FOSTEP_substquant in H. cbn [Nat.add] in H.
  refine (FOPrH_bexc_elim n G 50 _ _ C ltac:(apply HG; lia) ltac:(apply HCv; lia) H _).
  lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as K50;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as R50
  end.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_cpair_closed n _ (FOnumeral k) (FOVar 50) k
                                     (cpair x b) ltac:(avoid_tms) K50)) as E50.
  refine (FOPrH_bexc_elim n _ 52 _ _ C _ _ R50 _); [free_ctx | apply HCv; lia |].
  refine (FOPrH_bexc_elim n _ 54 _ _ C _ _ (FOPrH_last _ _ _) _); [free_ctx | apply HCv; lia |].
  lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as K54;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as R54;
    assert (E50b : FOPrH n (G1 ++ [X]) (FOEq (FOVar 50) (FOnumeral (cpair x b)))) by wk E50
  end.
  pose proof (FOPrH_cpairF_cong _ _ _ _ _ (FOVar 52) (FOVar 54) (FOnumeral (cpair x b))
                (FOPrH_refl _ _ _) (FOPrH_refl _ _ _) E50b K54) as K54b.
  pose proof (FOPrH_cpair_closed _ _ (FOVar 52) (FOVar 54) x b ltac:(avoid_tms) K54b) as D54.
  pose proof (FOPrH_and_l _ _ _ _ D54) as E52.
  refine (FOPrH_or_elim _ _ _ _ _ R54 _ _).
  - refine (FOPrH_cont1 _ _ _ _ C _ (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _)) H0).
    intros Z HZ. repeat (apply in_or_app; left). exact HZ.
  - apply FOPrH_efq.
    exact (FOPrH_mp _ _ _ _ (FOPrH_and_l _ _ _ _ (FOPrH_last _ _ _))
             (FOPrH_weak_app _ _ _ _ E52)).
Qed.

Lemma FOPrH_SQ_real : forall n G x s k y b c w1 q C,
  y <> x ->
  FOctx_avoid G 2 122 -> FOtms_avoid [c] 2 1000 ->
  (forall v, 2 <= v -> v < 122 -> FOfree_in v C = false) ->
  1000 <= w1 -> 1000 <= q -> w1 <> q ->
  FOfree_ctx w1 G -> FOfree_ctx q G ->
  FOfree_in w1 C = false -> FOfree_in q C = false ->
  FOtms_avoid [c] w1 (S w1) -> FOtms_avoid [c] q (S q) ->
  FOPrH n G (FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
               (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)) ->
  FOPrH n G (FOSTEP_substquant 50 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
               (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
               (FOnumeral x) (FOnumeral s) (FOnumeral (cpair k (cpair y b))) c k) ->
  FOPrH n (G ++ [FOTBLEX (FOnumeral 3) (FOnumeral x) (FOnumeral s) (FOnumeral b) (FOVar w1);
                 FOcpairF (FOnumeral y) (FOVar w1) (FOVar q);
                 FOcpairF (FOnumeral k) (FOVar q) c]) C ->
  FOPrH n G C.
Proof.
  intros n G x s k y b c w1 q C Hyx HG Hc HCv Hw1 Hq H1q HG1 HGq HC1 HCq Hc1 Hcq HV H H0.
  unfold FOSTEP_substquant in H. cbn [Nat.add] in H.
  refine (FOPrH_bexc_elim n G 50 _ _ C ltac:(apply HG; lia) ltac:(apply HCv; lia) H _).
  lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as K50;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as R50
  end.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_cpair_closed n _ (FOnumeral k) (FOVar 50) k
                                     (cpair y b) ltac:(avoid_tms) K50)) as E50.
  refine (FOPrH_bexc_elim n _ 52 _ _ C _ _ R50 _); [free_ctx | apply HCv; lia |].
  refine (FOPrH_bexc_elim n _ 54 _ _ C _ _ (FOPrH_last _ _ _) _); [free_ctx | apply HCv; lia |].
  lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as K54;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as R54;
    assert (E50b : FOPrH n (G1 ++ [X]) (FOEq (FOVar 50) (FOnumeral (cpair y b)))) by wk E50
  end.
  pose proof (FOPrH_cpairF_cong _ _ _ _ _ (FOVar 52) (FOVar 54) (FOnumeral (cpair y b))
                (FOPrH_refl _ _ _) (FOPrH_refl _ _ _) E50b K54) as K54b.
  pose proof (FOPrH_cpair_closed _ _ (FOVar 52) (FOVar 54) y b ltac:(avoid_tms) K54b) as D54.
  pose proof (FOPrH_and_l _ _ _ _ D54) as E52. pose proof (FOPrH_and_r _ _ _ _ D54) as E54.
  assert (V1 : FOtm_avoid (FOVar w1) 2 1000) by (apply FOtm_avoid_var; lia).
  assert (Vq : FOtm_avoid (FOVar q) 2 1000) by (apply FOtm_avoid_var; lia).
  refine (FOPrH_or_elim _ _ _ _ _ R54 _ _).
  - apply FOPrH_efq.
    exact (FOPrH_mp _ _ _ _ (FOPrH_num_neq _ _ y x Hyx)
             (FOPrH_eq_trans _ _ _ _ _ (FOPrH_eq_sym _ _ _ _ (FOPrH_weak_app _ _ _ _ E52))
                (FOPrH_and_l _ _ _ _ (FOPrH_last _ _ _)))).
  - lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
      pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as B56
    end.
    refine (FOPrH_bexc_rename n _ 56 _ _ w1
              (FOAnd (FOlookup 58 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                        (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131)
                        (FOVar 132) (FOnumeral 3) (FOnumeral x) (FOnumeral s) (FOVar 54)
                        (FOVar w1))
                     (FOBexC 80 (FOSucc c)
                        (FOAnd (FOcpairF (FOVar 52) (FOVar w1) (FOVar 80))
                               (FOcpairF (FOnumeral k) (FOVar 80) c))))
              C _ HC1 _ _ _ _ _ _ B56 _);
      [free_ctx | free_fm | fr_tm | lia | lia | ok_fast V1
      | autorewrite with fosubst; rewrite ?FOsubst_t_var_eq'; subst_avoid_h Hc; reflexivity |].
    lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
      pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as L1;
      pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as B80
    end.
    refine (FOPrH_bexc_rename n _ 80 _ _ q
              (FOAnd (FOcpairF (FOVar 52) (FOVar w1) (FOVar q))
                     (FOcpairF (FOnumeral k) (FOVar q) c))
              C _ HCq _ _ _ _ _ _ B80 _);
      [free_ctx | free_fm | fr_tm | lia | lia | ok_fast Vq
      | autorewrite with fosubst; rewrite ?FOsubst_t_var_eq'; subst_avoid_h Hc; reflexivity |].
    lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
      pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as P1;
      pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as P2;
      assert (HVb : FOPrH n (G1 ++ [X]) (FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124)
                      (FOVar 125) (FOVar 126) (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130)
                      (FOVar 131) (FOVar 132))) by wk HV;
      assert (L1b : FOPrH n (G1 ++ [X]) (FOlookup 58 (FOVar 122) (FOVar 123) (FOVar 124)
                      (FOVar 125) (FOVar 126) (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130)
                      (FOVar 131) (FOVar 132) (FOnumeral 3) (FOnumeral x) (FOnumeral s)
                      (FOVar 54) (FOVar w1))) by wk L1;
      assert (E52b : FOPrH n (G1 ++ [X]) (FOEq (FOVar 52) (FOnumeral y))) by wk E52;
      assert (E54b : FOPrH n (G1 ++ [X]) (FOEq (FOVar 54) (FOnumeral b))) by wk E54
    end.
    pose proof (FOPrH_lookup_a3_num n _ 58 (FOnumeral 3) (FOnumeral x) (FOnumeral s) 54
                  (FOVar w1) b ltac:(lia) ltac:(lia) ltac:(lia) ltac:(avoid_tms) E54b L1b) as L1c.
    pose proof (FOPrH_lookup_tblex n _ 58 (FOnumeral 3) (FOnumeral x) (FOnumeral s)
                  (FOnumeral b) (FOVar w1) HVb L1c
                  ltac:(lia) ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms)) as T1.
    pose proof (FOPrH_cpairF_cong _ _ _ _ _ (FOnumeral y) (FOVar w1) (FOVar q)
                  E52b (FOPrH_refl _ _ _) (FOPrH_refl _ _ _) P1) as P1b.
    refine (FOPrH_cont_list n G _ _ C _ _ H0).
    + intros Z HZ. repeat (apply in_or_app; left). exact HZ.
    + intros Y [<-|[<-|[<-|[]]]]; assumption.
Qed.

(** ** The variable and successor steps of a term row at a closed source. *)

Lemma FOPrH_ST2_var : forall n G x s v c C,
  FOctx_avoid G 2 122 -> FOtms_avoid [c] 2 1000 ->
  (forall u, 2 <= u -> u < 122 -> FOfree_in u C = false) ->
  FOPrH n G (FOBexC 50 (FOSucc (FOnumeral (cpair 0 v)))
               (FOAnd (FOcpairF FOZero (FOVar 50) (FOnumeral (cpair 0 v)))
                  (FOOr (FOAnd (FOEq (FOVar 50) (FOnumeral x)) (FOEq c (FOnumeral s)))
                        (FOAnd (FONeg (FOEq (FOVar 50) (FOnumeral x)))
                               (FOEq c (FOnumeral (cpair 0 v))))))) ->
  FOPrH n (G ++ [FOEq c (FOnumeral (if Nat.eqb v x then s else cpair 0 v))]) C ->
  FOPrH n G C.
Proof.
  intros n G x s v c C HG Hc HCv H H0.
  refine (FOPrH_bexc_elim n G 50 _ _ C ltac:(apply HG; lia) ltac:(apply HCv; lia) H _).
  lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as K50;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as R50
  end.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_cpair_closed n _ FOZero (FOVar 50) 0 v
                                     ltac:(avoid_tms) K50)) as E50.
  destruct (Nat.eqb_spec v x) as [Evx|Hvx].
  - subst v. try rewrite Nat.eqb_refl in H0.
    refine (FOPrH_or_elim _ _ _ _ _ R50 _ _).
    + refine (FOPrH_cont1 _ _ _ _ C _ (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _)) H0).
      intros Z HZ. repeat (apply in_or_app; left). exact HZ.
    + apply FOPrH_efq.
      exact (FOPrH_mp _ _ _ _ (FOPrH_and_l _ _ _ _ (FOPrH_last _ _ _))
               (FOPrH_weak_app _ _ _ _ E50)).
  - try rewrite (proj2 (Nat.eqb_neq v x) Hvx) in H0.
    refine (FOPrH_or_elim _ _ _ _ _ R50 _ _).
    + apply FOPrH_efq.
      exact (FOPrH_mp _ _ _ _ (FOPrH_num_neq _ _ v x Hvx)
               (FOPrH_eq_trans _ _ _ _ _ (FOPrH_eq_sym _ _ _ _ (FOPrH_weak_app _ _ _ _ E50))
                  (FOPrH_and_l _ _ _ _ (FOPrH_last _ _ _)))).
    + refine (FOPrH_cont1 _ _ _ _ C _ (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _)) H0).
      intros Z HZ. repeat (apply in_or_app; left). exact HZ.
Qed.

Lemma FOPrH_ST2_succ : forall n G x s a c w1 C,
  FOctx_avoid G 2 122 -> FOtms_avoid [c] 2 1000 ->
  (forall u, 2 <= u -> u < 122 -> FOfree_in u C = false) ->
  1000 <= w1 -> FOfree_ctx w1 G -> FOfree_in w1 C = false -> FOtms_avoid [c] w1 (S w1) ->
  FOPrH n G (FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
               (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)) ->
  FOPrH n G (FOBexC 50 (FOSucc (FOnumeral (cpair 2 a)))
               (FOAnd (FOcpairF (FOnumeral 2) (FOVar 50) (FOnumeral (cpair 2 a)))
                  (FOBexC 52 c
                     (FOAnd (FOlookup 54 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125)
                               (FOVar 126) (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130)
                               (FOVar 131) (FOVar 132) (FOnumeral 2) (FOnumeral x)
                               (FOnumeral s) (FOVar 50) (FOVar 52))
                            (FOcpairF (FOnumeral 2) (FOVar 52) c))))) ->
  FOPrH n (G ++ [FOTBLEX (FOnumeral 2) (FOnumeral x) (FOnumeral s) (FOnumeral a) (FOVar w1);
                 FOcpairF (FOnumeral 2) (FOVar w1) c]) C ->
  FOPrH n G C.
Proof.
  intros n G x s a c w1 C HG Hc HCv Hw1 HG1 HC1 Hc1 HV H H0.
  refine (FOPrH_bexc_elim n G 50 _ _ C ltac:(apply HG; lia) ltac:(apply HCv; lia) H _).
  lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as K50;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as R50
  end.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_cpair_closed n _ (FOnumeral 2) (FOVar 50) 2 a
                                     ltac:(avoid_tms) K50)) as E50.
  assert (V1 : FOtm_avoid (FOVar w1) 2 1000) by (apply FOtm_avoid_var; lia).
  refine (FOPrH_bexc_rename n _ 52 _ _ w1
            (FOAnd (FOlookup 54 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                      (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131)
                      (FOVar 132) (FOnumeral 2) (FOnumeral x) (FOnumeral s) (FOVar 50)
                      (FOVar w1))
                   (FOcpairF (FOnumeral 2) (FOVar w1) c))
            C _ HC1 _ _ _ _ _ _ R50 _);
    [free_ctx | free_fm | fr_tm | lia | lia | ok_fast V1
    | autorewrite with fosubst; rewrite ?FOsubst_t_var_eq'; subst_avoid_h Hc; reflexivity |].
  lazymatch goal with |- FOPrH _ (?G1 ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G1 X)) as L1;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G1 X)) as P1;
    assert (HVb : FOPrH n (G1 ++ [X]) (FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124)
                    (FOVar 125) (FOVar 126) (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130)
                    (FOVar 131) (FOVar 132))) by wk HV;
    assert (E50b : FOPrH n (G1 ++ [X]) (FOEq (FOVar 50) (FOnumeral a))) by wk E50
  end.
  pose proof (FOPrH_lookup_a3_num n _ 54 (FOnumeral 2) (FOnumeral x) (FOnumeral s) 50
                (FOVar w1) a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(avoid_tms) E50b L1) as L1c.
  pose proof (FOPrH_lookup_tblex n _ 54 (FOnumeral 2) (FOnumeral x) (FOnumeral s)
                (FOnumeral a) (FOVar w1) HVb L1c
                ltac:(lia) ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms)) as T1.
  refine (FOPrH_cont_list n G _ _ C _ _ H0).
  - intros Z HZ. repeat (apply in_or_app; left). exact HZ.
  - intros Y [<-|[<-|[]]]; assumption.
Qed.

(** ** Substitution on codes.

    [subc_t x sc t] and [subc_f x sc A]: the code of [t] and of [A] with
    the number [sc] in place of the code of the variable [x], computed
    the way the substitution rows compute it. *)

Fixpoint subc_t (x sc : nat) (t : FOTerm) : nat :=
  match t with
  | FOVar v => if Nat.eqb v x then sc else cpair 0 v
  | FOZero => cpair 1 0
  | FOSucc a => cpair 2 (subc_t x sc a)
  | FOPlus a b => cpair 3 (cpair (subc_t x sc a) (subc_t x sc b))
  | FOMult a b => cpair 4 (cpair (subc_t x sc a) (subc_t x sc b))
  end.

Fixpoint subc_f (x sc : nat) (A : FOFormula) : nat :=
  match A with
  | FOEq a b => cpair 0 (cpair (subc_t x sc a) (subc_t x sc b))
  | FOFalseF => cpair 1 0
  | FOImplF B C => cpair 2 (cpair (subc_f x sc B) (subc_f x sc C))
  | FOForall y B =>
      if Nat.eqb y x then cpair 3 (cpair y (FOcode_f B)) else cpair 3 (cpair y (subc_f x sc B))
  | FOExists y B =>
      if Nat.eqb y x then cpair 4 (cpair y (FOcode_f B)) else cpair 4 (cpair y (subc_f x sc B))
  end.

Lemma subc_t_code : forall x s t, subc_t x (FOcode_tm s) t = FOcode_tm (FOsubst_t x s t).
Proof.
  intros x s t.
  induction t as [v| |a IHa|a IHa b IHb|a IHa b IHb]; cbn [subc_t FOsubst_t FOcode_tm].
  - destruct (Nat.eqb v x); reflexivity.
  - reflexivity.
  - rewrite IHa. reflexivity.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
Qed.

Lemma subc_f_code : forall x s A, subc_f x (FOcode_tm s) A = FOcode_f (FOsubst_f x s A).
Proof.
  intros x s A.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; cbn [subc_f FOsubst_f FOcode_f].
  - rewrite !subc_t_code. reflexivity.
  - reflexivity.
  - rewrite IHB, IHC. reflexivity.
  - destruct (Nat.eqb y x); cbn [FOcode_f]; [reflexivity | rewrite IHB; reflexivity].
  - destruct (Nat.eqb y x); cbn [FOcode_f]; [reflexivity | rewrite IHB; reflexivity].
Qed.

(** ** Term substitution rows at a closed source are functional. *)

Lemma FOPr_row2_fun : forall t n x sc w, 1000 <= w ->
  FOPrH n [] (FOImplF (FOTBLEX (FOnumeral 2) (FOnumeral x) (FOnumeral sc)
                         (FOnumeral (FOcode_tm t)) (FOVar w))
                      (FOEq (FOVar w) (FOnumeral (subc_t x sc t)))).
Proof.
  induction t as [v| |a IHa|a IHa b IHb|a IHa b IHb]; intros n x sc w Hw;
    apply FOPrH_intro; cbn [app FOcode_tm subc_t];
    lazymatch goal with |- FOPrH _ [FOTBLEX ?tg ?a1 ?a2 ?a3 ?r] ?C =>
      refine (FOPrH_tblex_inv n [FOTBLEX tg a1 a2 a3 r] tg a1 a2 a3 r C _ _ _
                (FOPrH_assum n [FOTBLEX tg a1 a2 a3 r] (FOTBLEX tg a1 a2 a3 r)
                   (or_introl eq_refl)) _);
        [ctx_list | avoid_tms | intros u ? ?; apply FOfree_in_eq_var_num; lia |]
    end;
    lazymatch goal with |- FOPrH _ (?G0 ++ [?V; ?D]) _ =>
      pose proof (FOPrH_assum n (G0 ++ [V; D]) V
                    ltac:(apply in_or_app; right; cbn [In]; left; reflexivity)) as HV;
      pose proof (FOPrH_disp_tag2 n (G0 ++ [V; D]) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (FOPrH_assum n (G0 ++ [V; D]) D
                       ltac:(apply in_or_app; right; cbn [In]; right; left; reflexivity))) as S2
    end;
    unfold FOSTEP2 in S2.
  - pose proof (FOPrH_or_kr _ _ _ _ S2 ltac:(kill_d)) as D0.
    refine (FOPrH_ST2_var n _ x sc v (FOVar w) _ _ _ _ D0 _);
      [ctx_list | avoid_tms | intros u ? ?; apply FOfree_in_eq_var_num; lia | apply FOPrH_last].
  - pose proof (FOPrH_or_kr _ _ _ _ (FOPrH_or_kl _ _ _ _ S2 ltac:(kill_d)) ltac:(kill_d)) as D1.
    exact (FOPrH_and_r _ _ _ _ D1).
  - pose proof (FOPrH_or_kr _ _ _ _ (FOPrH_or_kl _ _ _ _ (FOPrH_or_kl _ _ _ _ S2 ltac:(kill_d))
                  ltac:(kill_d)) ltac:(kill_d)) as D2.
    refine (FOPrH_ST2_succ n _ x sc (FOcode_tm a) (FOVar w) (S w) _ _ _ _ _ _ _ _ HV D2 _);
      [ctx_list | avoid_tms | intros u ? ?; apply FOfree_in_eq_var_num; lia | lia | free_ctx
      | apply FOfree_in_eq_var_num; lia | avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G1 ++ [?A; ?B]) _ =>
      destruct (FOPrH_app2 n G1 A B) as [T1 P1]
    end.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ (IHa n x sc (S w) ltac:(lia))) T1) as E1.
    exact (FOPrH_cpair_num2 _ _ _ _ (FOVar w) _ _ ltac:(avoid_tms) (FOPrH_refl _ _ _) E1 P1).
  - pose proof (FOPrH_or_kr _ _ _ _ (FOPrH_or_kl _ _ _ _ (FOPrH_or_kl _ _ _ _
                  (FOPrH_or_kl _ _ _ _ S2 ltac:(kill_d)) ltac:(kill_d)) ltac:(kill_d))
                  ltac:(kill_d)) as D3.
    refine (FOPrH_SB_real n _ x sc 3 2 3 (FOcode_tm a) (FOcode_tm b) (FOVar w) (S w) (S (S w))
              (S (S (S w))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HV D3 _);
      [ctx_list | avoid_tms | intros u ? ?; apply FOfree_in_eq_var_num; lia
      | lia | lia | lia | lia | lia | lia | free_ctx | free_ctx | free_ctx
      | apply FOfree_in_eq_var_num; lia | apply FOfree_in_eq_var_num; lia
      | apply FOfree_in_eq_var_num; lia | avoid_tms | avoid_tms | avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G1 ++ [?A; ?B; ?C; ?D]) _ =>
      destruct (FOPrH_app4 n G1 A B C D) as (T1 & T2 & P1 & P2)
    end.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ (IHa n x sc (S w) ltac:(lia))) T1) as E1.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ (IHb n x sc (S (S w)) ltac:(lia))) T2) as E2.
    pose proof (FOPrH_cpair_num2 _ _ _ _ (FOVar (S (S (S w)))) _ _ ltac:(avoid_tms) E1 E2 P1)
      as E3.
    exact (FOPrH_cpair_num2 _ _ _ _ (FOVar w) _ _ ltac:(avoid_tms) (FOPrH_refl _ _ _) E3 P2).
  - pose proof (FOPrH_or_kl _ _ _ _ (FOPrH_or_kl _ _ _ _ (FOPrH_or_kl _ _ _ _
                  (FOPrH_or_kl _ _ _ _ S2 ltac:(kill_d)) ltac:(kill_d)) ltac:(kill_d))
                  ltac:(kill_d)) as D4.
    refine (FOPrH_SB_real n _ x sc 4 2 4 (FOcode_tm a) (FOcode_tm b) (FOVar w) (S w) (S (S w))
              (S (S (S w))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HV D4 _);
      [ctx_list | avoid_tms | intros u ? ?; apply FOfree_in_eq_var_num; lia
      | lia | lia | lia | lia | lia | lia | free_ctx | free_ctx | free_ctx
      | apply FOfree_in_eq_var_num; lia | apply FOfree_in_eq_var_num; lia
      | apply FOfree_in_eq_var_num; lia | avoid_tms | avoid_tms | avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G1 ++ [?A; ?B; ?C; ?D]) _ =>
      destruct (FOPrH_app4 n G1 A B C D) as (T1 & T2 & P1 & P2)
    end.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ (IHa n x sc (S w) ltac:(lia))) T1) as E1.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ (IHb n x sc (S (S w)) ltac:(lia))) T2) as E2.
    pose proof (FOPrH_cpair_num2 _ _ _ _ (FOVar (S (S (S w)))) _ _ ltac:(avoid_tms) E1 E2 P1)
      as E3.
    exact (FOPrH_cpair_num2 _ _ _ _ (FOVar w) _ _ ltac:(avoid_tms) (FOPrH_refl _ _ _) E3 P2).
Qed.

(** ** Formula substitution rows at a closed source are functional. *)

Lemma FOPr_row3_fun : forall A n x sc w, 1000 <= w ->
  FOPrH n [] (FOImplF (FOTBLEX (FOnumeral 3) (FOnumeral x) (FOnumeral sc)
                         (FOnumeral (FOcode_f A)) (FOVar w))
                      (FOEq (FOVar w) (FOnumeral (subc_f x sc A)))).
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros n x sc w Hw;
    apply FOPrH_intro; cbn [app FOcode_f subc_f];
    lazymatch goal with |- FOPrH _ [FOTBLEX ?tg ?a1 ?a2 ?a3 ?r] ?C =>
      refine (FOPrH_tblex_inv n [FOTBLEX tg a1 a2 a3 r] tg a1 a2 a3 r C _ _ _
                (FOPrH_assum n [FOTBLEX tg a1 a2 a3 r] (FOTBLEX tg a1 a2 a3 r)
                   (or_introl eq_refl)) _);
        [ctx_list | avoid_tms | intros u ? ?; apply FOfree_in_eq_var_num; lia |]
    end;
    lazymatch goal with |- FOPrH _ (?G0 ++ [?V; ?D]) _ =>
      pose proof (FOPrH_assum n (G0 ++ [V; D]) V
                    ltac:(apply in_or_app; right; cbn [In]; left; reflexivity)) as HV;
      pose proof (FOPrH_disp_tag3 n (G0 ++ [V; D]) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                    (FOPrH_assum n (G0 ++ [V; D]) D
                       ltac:(apply in_or_app; right; cbn [In]; right; left; reflexivity))) as S3
    end;
    unfold FOSTEP3 in S3.
  - pose proof (FOPrH_or_kr _ _ _ _ S3 ltac:(kill_d)) as D0.
    refine (FOPrH_SB_real n _ x sc 0 2 0 (FOcode_tm a) (FOcode_tm b) (FOVar w) (S w) (S (S w))
              (S (S (S w))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HV D0 _);
      [ctx_list | avoid_tms | intros u ? ?; apply FOfree_in_eq_var_num; lia
      | lia | lia | lia | lia | lia | lia | free_ctx | free_ctx | free_ctx
      | apply FOfree_in_eq_var_num; lia | apply FOfree_in_eq_var_num; lia
      | apply FOfree_in_eq_var_num; lia | avoid_tms | avoid_tms | avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G1 ++ [?A; ?B; ?C; ?D]) _ =>
      destruct (FOPrH_app4 n G1 A B C D) as (T1 & T2 & P1 & P2)
    end.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ (FOPr_row2_fun a n x sc (S w) ltac:(lia)))
                  T1) as E1.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ (FOPr_row2_fun b n x sc (S (S w))
                  ltac:(lia))) T2) as E2.
    pose proof (FOPrH_cpair_num2 _ _ _ _ (FOVar (S (S (S w)))) _ _ ltac:(avoid_tms) E1 E2 P1)
      as E3.
    exact (FOPrH_cpair_num2 _ _ _ _ (FOVar w) _ _ ltac:(avoid_tms) (FOPrH_refl _ _ _) E3 P2).
  - pose proof (FOPrH_or_kr _ _ _ _ (FOPrH_or_kl _ _ _ _ S3 ltac:(kill_d)) ltac:(kill_d)) as D1.
    exact (FOPrH_and_r _ _ _ _ D1).
  - pose proof (FOPrH_or_kr _ _ _ _ (FOPrH_or_kl _ _ _ _ (FOPrH_or_kl _ _ _ _ S3 ltac:(kill_d))
                  ltac:(kill_d)) ltac:(kill_d)) as D2.
    refine (FOPrH_SB_real n _ x sc 2 3 2 (FOcode_f B) (FOcode_f C) (FOVar w) (S w) (S (S w))
              (S (S (S w))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HV D2 _);
      [ctx_list | avoid_tms | intros u ? ?; apply FOfree_in_eq_var_num; lia
      | lia | lia | lia | lia | lia | lia | free_ctx | free_ctx | free_ctx
      | apply FOfree_in_eq_var_num; lia | apply FOfree_in_eq_var_num; lia
      | apply FOfree_in_eq_var_num; lia | avoid_tms | avoid_tms | avoid_tms |].
    lazymatch goal with |- FOPrH _ (?G1 ++ [?A; ?B; ?C; ?D]) _ =>
      destruct (FOPrH_app4 n G1 A B C D) as (T1 & T2 & P1 & P2)
    end.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ (IHB n x sc (S w) ltac:(lia))) T1) as E1.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ (IHC n x sc (S (S w)) ltac:(lia))) T2) as E2.
    pose proof (FOPrH_cpair_num2 _ _ _ _ (FOVar (S (S (S w)))) _ _ ltac:(avoid_tms) E1 E2 P1)
      as E3.
    exact (FOPrH_cpair_num2 _ _ _ _ (FOVar w) _ _ ltac:(avoid_tms) (FOPrH_refl _ _ _) E3 P2).
  - pose proof (FOPrH_or_kr _ _ _ _ (FOPrH_or_kl _ _ _ _ (FOPrH_or_kl _ _ _ _
                  (FOPrH_or_kl _ _ _ _ S3 ltac:(kill_d)) ltac:(kill_d)) ltac:(kill_d))
                  ltac:(kill_d)) as D3.
    destruct (Nat.eqb_spec y x) as [->|Hyx].
    + refine (FOPrH_SQ_same n _ x sc 3 (FOcode_f B) (FOVar w) _ _ _ _ D3 _);
        [ctx_list | avoid_tms | intros u ? ?; apply FOfree_in_eq_var_num; lia | apply FOPrH_last].
    + refine (FOPrH_SQ_real n _ x sc 3 y (FOcode_f B) (FOVar w) (S w) (S (S w)) _ Hyx
                _ _ _ _ _ _ _ _ _ _ _ _ HV D3 _);
        [ctx_list | avoid_tms | intros u ? ?; apply FOfree_in_eq_var_num; lia | lia | lia | lia
        | free_ctx | free_ctx | apply FOfree_in_eq_var_num; lia
        | apply FOfree_in_eq_var_num; lia | avoid_tms | avoid_tms |].
      lazymatch goal with |- FOPrH _ (?G1 ++ [?A; ?B; ?C]) _ =>
        destruct (FOPrH_app3 n G1 A B C) as (T1 & P1 & P2)
      end.
      pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ (IHB n x sc (S w) ltac:(lia))) T1) as E1.
      pose proof (FOPrH_cpair_num2 _ _ _ _ (FOVar (S (S w))) _ _ ltac:(avoid_tms)
                    (FOPrH_refl _ _ _) E1 P1) as E3.
      exact (FOPrH_cpair_num2 _ _ _ _ (FOVar w) _ _ ltac:(avoid_tms) (FOPrH_refl _ _ _) E3 P2).
  - pose proof (FOPrH_or_kl _ _ _ _ (FOPrH_or_kl _ _ _ _ (FOPrH_or_kl _ _ _ _
                  (FOPrH_or_kl _ _ _ _ S3 ltac:(kill_d)) ltac:(kill_d)) ltac:(kill_d))
                  ltac:(kill_d)) as D4.
    destruct (Nat.eqb_spec y x) as [->|Hyx].
    + refine (FOPrH_SQ_same n _ x sc 4 (FOcode_f B) (FOVar w) _ _ _ _ D4 _);
        [ctx_list | avoid_tms | intros u ? ?; apply FOfree_in_eq_var_num; lia | apply FOPrH_last].
    + refine (FOPrH_SQ_real n _ x sc 4 y (FOcode_f B) (FOVar w) (S w) (S (S w)) _ Hyx
                _ _ _ _ _ _ _ _ _ _ _ _ HV D4 _);
        [ctx_list | avoid_tms | intros u ? ?; apply FOfree_in_eq_var_num; lia | lia | lia | lia
        | free_ctx | free_ctx | apply FOfree_in_eq_var_num; lia
        | apply FOfree_in_eq_var_num; lia | avoid_tms | avoid_tms |].
      lazymatch goal with |- FOPrH _ (?G1 ++ [?A; ?B; ?C]) _ =>
        destruct (FOPrH_app3 n G1 A B C) as (T1 & P1 & P2)
      end.
      pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ (IHB n x sc (S w) ltac:(lia))) T1) as E1.
      pose proof (FOPrH_cpair_num2 _ _ _ _ (FOVar (S (S w))) _ _ ltac:(avoid_tms)
                    (FOPrH_refl _ _ _) E1 P1) as E3.
      exact (FOPrH_cpair_num2 _ _ _ _ (FOVar w) _ _ ltac:(avoid_tms) (FOPrH_refl _ _ _) E3 P2).
Qed.

(** ** Closed rows hold in the standard model, hence in T_0. *)

Lemma FOmax_var_tm_numeral : forall k, FOmax_var_tm (FOnumeral k) = 0.
Proof. induction k as [|k IH]; cbn; [reflexivity | exact IH]. Qed.

Lemma TBLsem_sat : forall e tg a1 a2 a3 r, TBLsem tg a1 a2 a3 r ->
  FOsat e (FOTBLEX (FOnumeral tg) (FOnumeral a1) (FOnumeral a2) (FOnumeral a3) (FOnumeral r)).
Proof.
  intros e tg a1 a2 a3 r [vct [vdt [vc1 [vd1 [vc2 [vd2 [vc3 [vd3 [vcr [vdr [vlen [Hv Hr]]]]]]]]]]]].
  unfold FOTBLEX. cbn [FOsat].
  exists vct, vdt, vc1, vd1, vc2, vd2, vc3, vd3, vcr, vdr, vlen.
  apply FOsat_FOAnd. split.
  - apply (proj2 (FOsat_FOTBLVALID _ 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
                    (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
                    ltac:(unfold tbl_below; cbn; lia))).
    cbn [FOeval FOupdate Nat.eqb]. exact Hv.
  - apply (proj2 (FOsat_FOlookup _ 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
                    (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
                    (FOnumeral tg) (FOnumeral a1) (FOnumeral a2) (FOnumeral a3) (FOnumeral r)
                    ltac:(unfold tbl_below; cbn; lia)
                    ltac:(rewrite FOmax_var_tm_numeral; lia)
                    ltac:(rewrite FOmax_var_tm_numeral; lia)
                    ltac:(rewrite FOmax_var_tm_numeral; lia)
                    ltac:(rewrite FOmax_var_tm_numeral; lia)
                    ltac:(rewrite FOmax_var_tm_numeral; lia))).
    cbn [FOeval FOupdate Nat.eqb]. rewrite !FOeval_numeral. exact Hr.
Qed.

Lemma TBLsem_row3 : forall x s A,
  TBLsem 3 x (FOcode_tm s) (FOcode_f A) (FOcode_f (FOsubst_f x s A)).
Proof.
  intros x s A.
  destruct (table_realize (trace3 x s A) (trace3_ok x s A (trace3 x s A) (incl_refl _)))
    as [vct [vdt [vc1 [vd1 [vc2 [vd2 [vc3 [vd3 [vcr [vdr [Hiff Hdisp]]]]]]]]]]].
  exists vct, vdt, vc1, vd1, vc2, vd2, vc3, vd3, vcr, vdr, (length (trace3 x s A)).
  split; [exact Hdisp|].
  apply (proj1 (Hiff _ _ _ _ _)). unfold listL. apply trace3_seed. reflexivity.
Qed.

Lemma TBLsem_row5 : forall k, TBLsem 5 k 0 0 (FOcode_tm (FOnumeral k)).
Proof.
  intros k.
  destruct (table_realize (trace5 k) (trace5_ok k (trace5 k) (incl_refl _)))
    as [vct [vdt [vc1 [vd1 [vc2 [vd2 [vc3 [vd3 [vcr [vdr [Hiff Hdisp]]]]]]]]]]].
  exists vct, vdt, vc1, vd1, vc2, vd2, vc3, vd3, vcr, vdr, (length (trace5 k)).
  split; [exact Hdisp|].
  apply (proj1 (Hiff _ _ _ _ _)). unfold listL. apply trace5_seed. reflexivity.
Qed.

Lemma FOsigma1_TBLEX_num : forall tg a1 a2 a3 r,
  FOsigma1 (FOTBLEX (FOnumeral tg) (FOnumeral a1) (FOnumeral a2) (FOnumeral a3) (FOnumeral r)).
Proof.
  intros tg a1 a2 a3 r. unfold FOTBLEX. repeat apply FOs1_ex. apply FOs1_d0.
  apply FOdelta0_and.
  - apply FOdelta0_FOTBLVALID. unfold tbl_below; cbn; lia.
  - apply FOdelta0_FOlookup; [unfold tbl_below; cbn; lia | ..];
      rewrite FOmax_var_tm_numeral; lia.
Qed.

Lemma FOPrH_tblex_num : forall n G tg a1 a2 a3 r, TBLsem tg a1 a2 a3 r ->
  FOPrH n G (FOTBLEX (FOnumeral tg) (FOnumeral a1) (FOnumeral a2) (FOnumeral a3) (FOnumeral r)).
Proof.
  intros n G tg a1 a2 a3 r H. apply FOPrH_empty. apply FOPrH_true_closed.
  - apply FOsigma1_TBLEX_num.
  - intros v. apply FOfree_in_TBLEX_all; avoid_tms.
  - apply TBLsem_sat. exact H.
Qed.

Lemma FOPrH_row3_num : forall n G x s A,
  FOPrH n G (FOTBLEX (FOnumeral 3) (FOnumeral x) (FOnumeral (FOcode_tm s))
               (FOnumeral (FOcode_f A)) (FOnumeral (FOcode_f (FOsubst_f x s A)))).
Proof. intros n G x s A. apply FOPrH_tblex_num. apply TBLsem_row3. Qed.

Lemma FOPrH_row5_num : forall n G k,
  FOPrH n G (FOTBLEX (FOnumeral 5) (FOnumeral k) FOZero FOZero
               (FOnumeral (FOcode_tm (FOnumeral k)))).
Proof. intros n G k. exact (FOPrH_tblex_num n G 5 k 0 0 _ (TBLsem_row5 k)). Qed.

(** ** The numeral code of a numeral. *)

Lemma FOPrH_numr_num : forall n G k,
  FOPrH n G (FONUMR (FOnumeral k) (FOnumeral (FOcode_tm (FOnumeral k)))).
Proof.
  intros n G k. apply FOPrH_empty.
  refine (FOPrH_numr_exists n [] (FOnumeral k) 1000 _ ltac:(avoid_tms) ltac:(lia)
            (FOfree_ctx_nil 1000) _ ltac:(avoid_tms) _).
  - apply FOfree_in_NUMR_all; avoid_tms.
  - pose proof (FOPrH_last n [] (FONUMR (FOnumeral k) (FOVar 1000))) as Hn.
    pose proof (FOPrH_num5_unique n _ (FOnumeral k) (FOVar 1000) _ (FOPrH_and_l _ _ _ _ Hn)
                  (FOPrH_row5_num n _ k) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as E.
    exact (FOPrH_numr_cong n _ (FOnumeral k) (FOVar 1000) _ Hn E ltac:(avoid_tms)).
Qed.

(** ** Rows rewritten along equations of their third and last fields. *)

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

Lemma FOPrH_tblex_cong_r : forall n G tg a1 a2 a3 r r',
  FOPrH n G (FOTBLEX tg a1 a2 a3 r) -> FOPrH n G (FOEq r r') ->
  FOtms_avoid [tg; a1; a2; a3; r; r'] 2 1000 ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r').
Proof.
  intros n G tg a1 a2 a3 r r' H E Hav.
  assert (K : forall t, FOtm_avoid t 2 1000 ->
             FOsubst_f 999 t (FOTBLEX tg a1 a2 a3 (FOVar 999)) = FOTBLEX tg a1 a2 a3 t).
  { intros t Ht. rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq'.
    rewrite !(FOsubst_t_not_in _ 999 t) by fr_tm. reflexivity. }
  assert (V : FOtm_avoid r 2 1000) by avoid_tm.
  assert (V' : FOtm_avoid r' 2 1000) by avoid_tm.
  pose proof (FOPrH_leibniz n G 999 r r' (FOTBLEX tg a1 a2 a3 (FOVar 999))
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm]) E) as L.
  rewrite (K r V), (K r' V') in L. exact (L H).
Qed.

(** ** Substituting one numeral: the result is determined, and it exists. *)

Lemma FOfree_in_ex_self : forall x A, FOfree_in x (FOExists x A) = false.
Proof. intros x A. cbn [FOfree_in]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma FOfree_in_ex_ex : forall x y A, FOfree_in x (FOExists y (FOExists x A)) = false.
Proof.
  intros x y A. cbn [FOfree_in]. rewrite Nat.eqb_refl. destruct (Nat.eqb y x); reflexivity.
Qed.

Lemma FOPr_sub1_fun : forall n q x A k w,
  1003 <= q -> 1000 <= w -> w <> q -> w <> S q -> w <> S (S q) ->
  FOPrH n [] (FOImplF (FOSUBNUMS q (FOnumeral (FOcode_f A)) [x] [FOnumeral k] (FOVar w))
                      (FOEq (FOVar w) (FOnumeral (FOcode_f (FOsubst_f x (FOnumeral k) A))))).
Proof.
  intros n q x A k w Hq Hw H0 H1 H2.
  assert (HX : forall v, v = q \/ v = S q \/ v = S (S q) ->
            FOfree_in v (FOSUBNUMS q (FOnumeral (FOcode_f A)) [x] [FOnumeral k] (FOVar w))
            = false).
  { intros v Hv. apply FOfree_in_SUBNUMS; [lia | avoid_tms |].
    apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|].
    apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
    apply FOtms_avoid_cons; [apply FOtm_avoid_numeral | apply FOtms_avoid_nil]. }
  apply FOPrH_intro. cbn [app].
  refine (FOPrH_ex_elim n [FOSUBNUMS q (FOnumeral (FOcode_f A)) [x] [FOnumeral k] (FOVar w)]
            q _ _ _ _
            (FOPrH_assum n [FOSUBNUMS q (FOnumeral (FOcode_f A)) [x] [FOnumeral k] (FOVar w)]
               (FOSUBNUMS q (FOnumeral (FOcode_f A)) [x] [FOnumeral k] (FOVar w))
               (or_introl eq_refl)) _).
  { apply FOfree_ctx_cons; [apply HX; lia | apply FOfree_ctx_nil]. }
  { apply FOfree_in_eq_var_num. lia. }
  refine (FOPrH_ex_elim n _ (S q) _ _ _ _ (FOPrH_last _ _ _) _).
  { apply FOfree_ctx_app_inv; [apply FOfree_ctx_cons; [apply HX; lia | apply FOfree_ctx_nil]|].
    apply FOfree_ctx_cons; [apply FOfree_in_ex_self | apply FOfree_ctx_nil]. }
  { apply FOfree_in_eq_var_num. lia. }
  refine (FOPrH_ex_elim n _ (S (S q)) _ _ _ _ (FOPrH_last _ _ _) _).
  { apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv|].
    - apply FOfree_ctx_cons; [apply HX; lia | apply FOfree_ctx_nil].
    - apply FOfree_ctx_cons; [apply FOfree_in_ex_ex | apply FOfree_ctx_nil].
    - apply FOfree_ctx_cons; [apply FOfree_in_ex_self | apply FOfree_ctx_nil]. }
  { apply FOfree_in_eq_var_num. lia. }
  lazymatch goal with |- FOPrH _ (?G1 ++ [?Y]) _ => pose proof (FOPrH_last n G1 Y) as B end.
  pose proof (FOPrH_and_l _ _ _ _ B) as E2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ B)) as N.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ B))) as T.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ B))) as Eqw.
  cbn [FOSUBNUMS] in Eqw.
  pose proof (FOPrH_numr_cong1 _ _ _ _ _ N E2 ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms)) as N'.
  pose proof (FOPrH_numr_unique n _ _ _ _ N' (FOPrH_numr_num n _ k)
                ltac:(avoid_tms) ltac:(avoid_tms)) as E1.
  pose proof (FOPrH_tblex_cong_a2 _ _ _ _ _ _ _ _ T E1 ltac:(avoid_tms)) as T'.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _
                (FOPr_row3_fun A n x (FOcode_tm (FOnumeral k)) q ltac:(lia))) T') as Eq.
  rewrite subc_f_code in Eq.
  exact (FOPrH_eq_trans _ _ _ _ _ (FOPrH_eq_sym _ _ _ _ Eqw) Eq).
Qed.

Lemma FOPr_sub1_ex : forall n q x A k, 1003 <= q ->
  FOPrH n [] (FOSUBNUMS q (FOnumeral (FOcode_f A)) [x] [FOnumeral k]
                (FOnumeral (FOcode_f (FOsubst_f x (FOnumeral k) A)))).
Proof.
  intros n q x A k Hq.
  pose proof (FOPrH_row3_num n [FOEq (FOVar (q + 3))
                                  (FOnumeral (FOcode_f (FOsubst_f x (FOnumeral k) A)))]
                x (FOnumeral k) A) as T.
  remember (FOcode_f (FOsubst_f x (FOnumeral k) A)) as R eqn:HR.
  assert (HE : FOPrH n [] (FOExists (q + 3) (FOEq (FOVar (q + 3)) (FOnumeral R)))).
  { apply (FOPrH_ex_intro _ _ (q + 3) (FOnumeral R)); [apply FOsubst_ok_eq|].
    rewrite FOsubst_f_eq, FOsubst_t_var_eq', FOsubst_t_numeral. apply FOPrH_refl. }
  refine (FOPrH_ex_elim n [] (q + 3) _ _ (FOfree_ctx_nil _) _ HE _).
  { apply FOfree_in_SUBNUMS; [lia | avoid_tms | avoid_tms]. }
  pose proof (FOPrH_last n [] (FOEq (FOVar (q + 3)) (FOnumeral R))) as EN.
  pose proof (FOPrH_tblex_cong_r _ _ _ _ _ _ _ _ T (FOPrH_eq_sym _ _ _ _ EN)
                ltac:(avoid_tms)) as T'.
  refine (FOPrH_subnums_cons n _ q x [] (FOnumeral k) [] (FOnumeral (FOcode_f A)) (FOnumeral R)
            (q + 3) (FOnumeral (FOcode_tm (FOnumeral k))) ltac:(lia) ltac:(cbn [length]; lia)
            ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)
            ltac:(avoid_tms) (FOPrH_numr_num _ _ k) T' _).
  cbn [FOSUBNUMS]. exact EN.
Qed.

(** ** The diagonal lemma.

    [FODIAG v0 w]: [w] codes the result of substituting the numeral of
    the value of [v0] for [v0] in the formula coded by [v0].  With
    [psi := exists w (FODIAG v0 w /\ phi)], the sentence
    [delta := psi[num(code psi)/v0]] satisfies
    [T_n |- delta <-> phi[num(code delta)/w]]. *)

Definition DQ : nat := 5000.

Definition FODIAG (v0 w : nat) : FOFormula :=
  FOSUBNUMS DQ (FOVar v0) [v0] [FOVar v0] (FOVar w).

Definition diag_psi (phi : FOFormula) (v0 w : nat) : FOFormula :=
  FOExists w (FOAnd (FODIAG v0 w) phi).

Definition diag_sent (phi : FOFormula) (v0 w : nat) : FOFormula :=
  FOsubst_f v0 (FOnumeral (FOcode_f (diag_psi phi v0 w))) (diag_psi phi v0 w).

Lemma FOin_tm_subst_self_num : forall t w k, FOin_tm w (FOsubst_t w (FOnumeral k) t) = false.
Proof.
  induction t as [v| |a IHa|a IHa b IHb|a IHa b IHb]; intros w k; cbn [FOsubst_t FOin_tm].
  - destruct (Nat.eqb_spec v w) as [->|Hvw]; [apply FOin_tm_numeral|].
    cbn [FOin_tm]. destruct (Nat.eqb_spec w v); [lia|]. destruct (Nat.eqb_spec v w); [lia|].
    reflexivity.
  - reflexivity.
  - apply IHa.
  - rewrite IHa, IHb. reflexivity.
  - rewrite IHa, IHb. reflexivity.
Qed.

Lemma FOfree_in_subst_self_num : forall A w k, FOfree_in w (FOsubst_f w (FOnumeral k) A) = false.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros w k; cbn [FOsubst_f FOfree_in].
  - rewrite !FOin_tm_subst_self_num. reflexivity.
  - reflexivity.
  - rewrite IHB, IHC. reflexivity.
  - destruct (Nat.eqb y w) eqn:E; cbn [FOfree_in]; rewrite E; [reflexivity | apply IHB].
  - destruct (Nat.eqb y w) eqn:E; cbn [FOfree_in]; rewrite E; [reflexivity | apply IHB].
Qed.

Lemma diag_sent_eq : forall phi v0 w,
  1000 <= v0 -> v0 < DQ -> v0 <> w -> FOfree_in v0 phi = false ->
  diag_sent phi v0 w =
  FOExists w (FOAnd (FOSUBNUMS DQ (FOnumeral (FOcode_f (diag_psi phi v0 w))) [v0]
                        [FOnumeral (FOcode_f (diag_psi phi v0 w))] (FOVar w)) phi).
Proof.
  intros phi v0 w H1 H2 H3 H4.
  unfold diag_sent. unfold diag_psi at 2.
  remember (FOcode_f (diag_psi phi v0 w)) as P eqn:HP. clear HP.
  rewrite FOsubst_f_ex_ne by lia. rewrite FOsubst_f_and.
  unfold FODIAG. rewrite FOsubst_f_SUBNUMS by (unfold DQ in *; cbn [length]; lia).
  rewrite FOsubst_t_var_eq', FOsubst_t_var_ne by lia. cbn [map]. rewrite FOsubst_t_var_eq'.
  rewrite (FOsubst_f_not_free phi v0) by exact H4.
  reflexivity.
Qed.

Lemma diag_core : forall n phi v0 w P Dc D,
  1000 <= w -> w < DQ ->
  D = FOExists w (FOAnd (FOSUBNUMS DQ (FOnumeral P) [v0] [FOnumeral P] (FOVar w)) phi) ->
  FOPrH n [] (FOImplF (FOSUBNUMS DQ (FOnumeral P) [v0] [FOnumeral P] (FOVar w))
                      (FOEq (FOVar w) (FOnumeral Dc))) ->
  FOPrH n [] (FOSUBNUMS DQ (FOnumeral P) [v0] [FOnumeral P] (FOnumeral Dc)) ->
  FOPrH n [] (FOImplF D (FOsubst_f w (FOnumeral Dc) phi)) /\
  FOPrH n [] (FOImplF (FOsubst_f w (FOnumeral Dc) phi) D).
Proof.
  intros n phi v0 w P Dc D Hw HwD HD Fun Ex. subst D. split.
  - apply FOPrH_intro. cbn [app].
    lazymatch goal with |- FOPrH _ [?X] _ =>
      refine (FOPrH_ex_elim n [X] w _ _ _ _ (FOPrH_assum n [X] X (or_introl eq_refl)) _)
    end.
    + apply FOfree_ctx_cons; [apply FOfree_in_ex_self | apply FOfree_ctx_nil].
    + apply FOfree_in_subst_self_num.
    + lazymatch goal with |- FOPrH _ (?G1 ++ [?Y]) _ => pose proof (FOPrH_last n G1 Y) as B end.
      pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty _ _ _ Fun) (FOPrH_and_l _ _ _ _ B)) as E.
      pose proof (FOPrH_and_r _ _ _ _ B) as Ph.
      refine (FOPrH_leibniz n _ w (FOVar w) (FOnumeral Dc) phi (FOsubst_ok_var_self phi w)
                (FOsubst_ok_numeral phi w Dc) E _).
      rewrite FOsubst_f_id. exact Ph.
  - apply FOPrH_intro.
    apply (FOPrH_ex_intro _ _ w (FOnumeral Dc)); [apply FOsubst_ok_numeral|].
    rewrite FOsubst_f_and, FOsubst_f_SUBNUMS by (unfold DQ in *; cbn [length]; lia).
    rewrite FOsubst_t_numeral, FOsubst_t_var_eq'. cbn [map]. rewrite FOsubst_t_numeral.
    apply FOPrH_and_intro; [exact (FOPrH_empty _ _ _ Ex) | apply FOPrH_last].
Qed.

Theorem FOPr_diagonal : forall n phi v0 w,
  1000 <= v0 -> 1000 <= w -> v0 <> w -> v0 < DQ -> w < DQ -> FOfree_in v0 phi = false ->
  FOPrH n [] (FOImplF (diag_sent phi v0 w)
                (FOsubst_f w (FOnumeral (FOcode_f (diag_sent phi v0 w))) phi)) /\
  FOPrH n [] (FOImplF (FOsubst_f w (FOnumeral (FOcode_f (diag_sent phi v0 w))) phi)
                (diag_sent phi v0 w)).
Proof.
  intros n phi v0 w Hv0 Hw Hvw Hv0D HwD Hphi.
  assert (Hsent : diag_sent phi v0 w =
                  FOsubst_f v0 (FOnumeral (FOcode_f (diag_psi phi v0 w))) (diag_psi phi v0 w))
    by reflexivity.
  pose proof (FOPr_sub1_fun n DQ v0 (diag_psi phi v0 w) (FOcode_f (diag_psi phi v0 w)) w
                ltac:(unfold DQ; lia) Hw ltac:(unfold DQ in *; lia) ltac:(unfold DQ in *; lia)
                ltac:(unfold DQ in *; lia)) as Fun.
  pose proof (FOPr_sub1_ex n DQ v0 (diag_psi phi v0 w) (FOcode_f (diag_psi phi v0 w))
                ltac:(unfold DQ; lia)) as Ex.
  rewrite <- Hsent in Fun, Ex.
  exact (diag_core n phi v0 w (FOcode_f (diag_psi phi v0 w)) (FOcode_f (diag_sent phi v0 w))
           (diag_sent phi v0 w) Hw HwD (diag_sent_eq phi v0 w Hv0 Hv0D Hvw Hphi) Fun Ex).
Qed.

(** ** The Loeb sentence.

    [loeb_phi k A] says of [w] that [T_k] proving the sentence coded
    [w] implies [A]; its diagonal sentence [loeb_sent k A] is
    equivalent in [T_0] to [Pr_k(loeb_sent k A) -> A]. *)

Definition loeb_phi (k : nat) (A : FOFormula) : FOFormula :=
  FOImplF (FOPRu (FOPrCores k) (FOu0 k) (FOVar 3001)) A.

Definition loeb_sent (k : nat) (A : FOFormula) : FOFormula :=
  diag_sent (loeb_phi k A) 3000 3001.

Lemma loeb_phi_subst : forall k A m, (forall x, FOfree_in x A = false) ->
  FOsubst_f 3001 (FOnumeral m) (loeb_phi k A) =
  FOImplF (FOPRu (FOPrCores k) (FOu0 k) (FOnumeral m)) A.
Proof.
  intros k A m HA. unfold loeb_phi.
  rewrite FOsubst_f_impl, FOsubst_f_PRu by (lia || avoid_tms).
  rewrite FOsubst_t_var_eq', (FOsubst_f_not_free A) by apply HA. reflexivity.
Qed.

Lemma loeb_fix : forall k A, (forall x, FOfree_in x A = false) ->
  FOProvesTn 0 (FOImplF (loeb_sent k A)
                  (FOImplF (FOProvSentence k (loeb_sent k A)) A)) /\
  FOProvesTn 0 (FOImplF (FOImplF (FOProvSentence k (loeb_sent k A)) A)
                  (loeb_sent k A)).
Proof.
  intros k A HA.
  assert (Hfree : FOfree_in 3000 (loeb_phi k A) = false).
  { unfold loeb_phi. cbn [FOfree_in]. rewrite FOfree_in_PRu by (lia || avoid_tms).
    rewrite HA. reflexivity. }
  destruct (FOPr_diagonal 0 (loeb_phi k A) 3000 3001 ltac:(lia) ltac:(lia) ltac:(lia)
              ltac:(unfold DQ; lia) ltac:(unfold DQ; lia) Hfree) as [H1 H2].
  rewrite loeb_phi_subst, FOPRu_ProvSentence in H1, H2 by exact HA.
  split; [exact H1 | exact H2].
Qed.

(** ** Loeb's theorem inside T_0. *)

Theorem FOLoeb_internal : forall k A, (forall x, FOfree_in x A = false) ->
  FOProvesTn 0 (FOImplF (FOProvSentence k (FOImplF (FOProvSentence k A) A))
                  (FOProvSentence k A)).
Proof.
  intros k A HA.
  set (D := loeb_sent k A).
  set (P := FOProvSentence k).
  destruct (loeb_fix k A HA) as [Hto Hfrom]. fold D P in Hto, Hfrom.
  (* T_0 proves Pr(D) -> Pr(A) *)
  assert (HDA : FOPrH 0 [] (FOImplF (P D) (P A))).
  { pose proof (FOHBL3_provable k 0 _ (FOProvesTn_cumulative 0 k _ ltac:(lia) Hto)) as Hb.
    pose proof (FOHBL2_internal k D (FOImplF (P D) A)) as Hc.
    pose proof (FOHBL2_internal k (P D) A) as Hd.
    pose proof (FOHBL3_internal k D) as He.
    fold P in Hb, Hc, Hd, He.
    apply FOPrH_intro.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ (FOPrH_empty 0 _ _ Hc) (FOPrH_empty 0 _ _ Hb))
                  (FOPrH_last 0 [] (P D))) as X1.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty 0 _ _ He) (FOPrH_last 0 [] (P D))) as X2.
    exact (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ (FOPrH_empty 0 _ _ Hd) X1) X2). }
  (* T_0 proves (Pr(A) -> A) -> D *)
  assert (HAD : FOPrH 0 [] (FOImplF (FOImplF (P A) A) D)).
  { apply FOPrH_intro.
    refine (FOPrH_mp _ _ _ _ (FOPrH_empty 0 _ _ Hfrom) _).
    apply FOPrH_intro.
    lazymatch goal with |- FOPrH _ (?G1 ++ [?Y]) _ =>
      pose proof (FOPrH_mp _ _ _ _ (FOPrH_empty 0 (G1 ++ [Y]) _ HDA) (FOPrH_last 0 G1 Y)) as XA
    end.
    exact (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ (FOPrH_last 0 [] (FOImplF (P A) A))) XA). }
  (* T_0 proves Pr(Pr(A) -> A) -> Pr(D), then Pr(A) *)
  pose proof (FOHBL3_provable k 0 _ (FOProvesTn_cumulative 0 k _ ltac:(lia) HAD)) as Hh.
  pose proof (FOHBL2_internal k (FOImplF (P A) A) D) as H2.
  fold P in Hh, H2.
  change (FOPrH 0 [] (FOImplF (P (FOImplF (P A) A)) (P A))).
  exact (FOPrH_imp_trans _ _ _ _ _ (FOPrH_mp _ _ _ _ (FOPrH_empty 0 _ _ H2) (FOPrH_empty 0 _ _ Hh))
           HDA).
Qed.

(** ** Loeb's rule from the diagonal lemma and the derivability conditions. *)

Theorem FOLoeb_rule_derived : forall k A, (forall x, FOfree_in x A = false) ->
  FOProvesTn k (FOImplF (FOProvSentence k A) A) -> FOProvesTn k A.
Proof.
  intros k A HA H.
  pose proof (FOHBL3_provable k 0 _ H) as H1.
  pose proof (FOProvesTn_MP 0 _ _ (FOLoeb_internal k A HA) H1) as H2.
  exact (FOProvesTn_MP k _ _ H (FOProvesTn_cumulative 0 k _ ltac:(lia) H2)).
Qed.
