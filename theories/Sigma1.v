(******************************************************************************)
(*                                                                            *)
(*                            Provability Verified                            *)
(*                                                                            *)
(*     Part 11 of 12. Provable Sigma_1-completeness and the third condition.  *)
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
  Derivability Rows Patterns Instances.
Open Scope fo_scope.

(** ** The invariant of the main induction.

    [Inv n V G h rho env Sv]: the context lies in [1000 .. V), the slot
    values carry numeral codes, and every variable in [Sv] has a holder
    with its code in the slot [rho] gives it. *)

Definition Inv (n V : nat) (G : list FOFormula) (h : nat -> nat) (rho : nat -> option nat)
    (env : list FOTerm) (Sv : nat -> Prop) : Prop :=
  2000 <= V /\ FOctx_avoid G 0 1000 /\ (forall w, V <= w -> FOfree_ctx w G) /\
  EnvOK n V G env /\ FOtms_avoid env 0 1100 /\ (forall z i, rho z = Some i -> i < length env) /\
  (forall x, Sv x -> HOK n G V h rho env x).

Lemma rho_sub_eq : forall z j rho, rho_sub (Some z) j rho z = Some j.
Proof. intros z j rho. unfold rho_sub. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma rho_sub_ne : forall z j rho x, x <> z -> rho_sub (Some z) j rho x = rho x.
Proof. intros z j rho x H. unfold rho_sub. rewrite (proj2 (Nat.eqb_neq x z) H). reflexivity. Qed.

Lemma Inv_snoc : forall n V G h rho env Sv t w z,
  Inv n V G h rho env Sv -> V <= w ->
  FOtms_avoid [t] 0 1100 -> (forall s, In s [t] -> forall w', V <= w' -> FOin_tm w' s = false) ->
  (forall x, Sv x -> x <> z) ->
  Inv n (S w) (G ++ [FONUMR t (FOVar w)]) h (rho_sub (Some z) (length env) rho)
    (env ++ [FOVar w]) Sv.
Proof.
  intros n V G h rho env Sv t w z [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]] Hw Ht0 Htv Hz.
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (HG1 : FOctx_avoid (G ++ [FONUMR t (FOVar w)]) 0 1000) by (intros w' ? ?; free_ctx).
  assert (Hinc : forall X, In X G -> In X (G ++ [FONUMR t (FOVar w)]))
    by (intros X HX; apply in_or_app; left; exact HX).
  split; [lia|]. split; [exact HG1|]. split; [intros w' Hw'; free_ctx|].
  split.
  { apply (EnvOK_snoc n (S w) _ env (FOVar w) t);
      [ apply (EnvOK_mono n V (S w) G);
        [exact HE | exact Hinc | intros w' ? ?; apply HG1; lia | lia]
      | apply FOPrH_last | avoid_tms | intros w' Hw'; apply FOin_tm_var_ne; lia ]. }
  split; [avoid_tms|]. split.
  - intros z0 i Hz0. rewrite length_app. cbn [length]. unfold rho_sub in Hz0.
    destruct (Nat.eqb z0 z); [injection Hz0 as <-; lia | specialize (Hr z0 i Hz0); lia].
  - intros x Hx.
    refine (HOK_ext n G _ V (S w) h rho _ env _ x (Hh x Hx) Hinc _ _ _ _);
      [ lia | intros i Hi; rewrite (rho_sub_ne z (length env) rho x (Hz x Hx)); exact Hi
      | rewrite length_app; lia | intros i Hi; apply nth_app_lt; exact Hi ].
Qed.

Lemma Inv_weaken : forall n V G h rho env Sv Sv',
  Inv n V G h rho env Sv -> (forall x, Sv' x -> Sv x) -> Inv n V G h rho env Sv'.
Proof.
  intros n V G h rho env Sv Sv' [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]] HS.
  split; [exact HV|]. split; [exact HG0|]. split; [exact HGV|]. split; [exact HE|].
  split; [exact Henv|]. split; [exact Hr|]. intros x Hx. apply Hh. apply HS. exact Hx.
Qed.

Lemma HOK_range : forall n G V h rho env x, HOK n G V h rho env x -> 1100 <= h x < V.
Proof. intros n G V h rho env x [i [_ [_ [_ [H1 H2]]]]]. lia. Qed.

Lemma hsub_facts : forall t n G V h rho env,
  (forall x, FOin_tm x t = true -> HOK n G V h rho env x) ->
  FOtms_avoid [hsub_tm h t] 0 1100 /\
  (forall s, In s [hsub_tm h t] -> forall w, V <= w -> FOin_tm w s = false).
Proof.
  intros t n G V h rho env H. split.
  - intros s [<-|[]]. apply (hsub_tm_avoid t h 1100 1100); [|lia].
    intros x Hx. exact (proj1 (HOK_range n G V h rho env x (H x Hx))).
  - intros s [<-|[]] w Hw. apply (hsub_tm_below t h V); [|exact Hw].
    intros x Hx. exact (proj2 (HOK_range n G V h rho env x (H x Hx))).
Qed.

Ltac fv_cases H ::=
  repeat match type of H with
  | FOfree_in _ (FONeg _) = true => unfold FONeg in H
  | FOfree_in _ (FOAnd _ _) = true => unfold FOAnd, FONeg in H
  | FOfree_in _ (FOImplF _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ (FOEq _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ (FOForall _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ (FOExists _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ FOFalseF = true => discriminate H
  | (if ?c then false else _) = true =>
      let E := fresh "E" in destruct c eqn:E; [discriminate H|]
  | (_ || _)%bool = true => apply Bool.orb_true_iff in H; destruct H as [H|H]
  | FOin_tm _ (FOSucc _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (FOPlus _ _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (FOMult _ _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (opT _ _ _) = true => rewrite FOin_tm_opT_eq in H
  | FOin_tm _ FOZero = true => discriminate H
  | FOin_tm ?x (FOVar _) = true => cbn [FOin_tm] in H; apply Nat.eqb_eq in H; subst x
  | Nat.eqb _ ?x = true => apply Nat.eqb_eq in H; subst x
  | false = true => discriminate H
  end.

(** ** Equations. *)

Lemma FOPr_eq_via : forall a b z,
  FOProvesTn 0 (FOImplF (FOEq a (FOVar z)) (FOImplF (FOEq b (FOVar z)) (FOEq a b))).
Proof.
  intros a b z.
  change (FOPrH 0 [] (FOImplF (FOEq a (FOVar z)) (FOImplF (FOEq b (FOVar z)) (FOEq a b)))).
  apply FOPrH_intro. apply FOPrH_intro. cbn [app].
  apply (FOPrH_eq_trans _ _ _ (FOVar z)); [apply FOPrH_assum; left; reflexivity|].
  apply FOPrH_eq_sym. apply FOPrH_assum. right. left. reflexivity.
Qed.

Lemma FOPr_neq_via : forall a b z1 z2,
  FOProvesTn 0 (FOImplF (FOEq a (FOVar z1)) (FOImplF (FOEq b (FOVar z2))
    (FOImplF (FONeg (FOEq (FOVar z1) (FOVar z2))) (FONeg (FOEq a b))))).
Proof.
  intros a b z1 z2.
  change (FOPrH 0 [] (FOImplF (FOEq a (FOVar z1)) (FOImplF (FOEq b (FOVar z2))
    (FOImplF (FONeg (FOEq (FOVar z1) (FOVar z2))) (FONeg (FOEq a b)))))).
  unfold FONeg. apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_intro.
  cbn [app].
  apply (FOPrH_mp _ _ (FOEq (FOVar z1) (FOVar z2))); [apply FOPrH_assum; right; right; left; reflexivity|].
  apply (FOPrH_eq_trans _ _ _ a); [apply FOPrH_eq_sym; apply FOPrH_assum; left; reflexivity|].
  apply (FOPrH_eq_trans _ _ _ b); [apply FOPrH_assum; right; right; right; left; reflexivity|].
  apply FOPrH_assum. right. left. reflexivity.
Qed.

Lemma PRI_eq_pos : forall n k a b V G h rho env,
  Inv n V G h rho env (fun x => FOfree_in x (FOEq a b) = true) ->
  FOPrH n G (FOEq (hsub_tm h a) (hsub_tm h b)) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho (FOEq a b)) env.
Proof.
  intros n k a b V G h rho env HI Hab.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hha : forall x, FOin_tm x a = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; cbn [FOfree_in]; rewrite Hx; reflexivity).
  assert (Hhb : forall x, FOin_tm x b = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; cbn [FOfree_in]; rewrite Hx; apply Bool.orb_true_r).
  destruct (hsub_facts a n G V h rho env Hha) as [Ha0 Hav].
  destruct (hsub_facts b n G V h rho env Hhb) as [Hb0 Hbv].
  refine (PRI_numr_ex n _ _ V 0 G _ env (hsub_tm h a) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
  intros w Hw _.
  remember (S (FOvars_max (FOEq a b))) as z eqn:Ez.
  cbn [FOvars_max] in Ez.
  assert (Hza : FOin_tm z a = false) by (apply FOin_tm_above; lia).
  assert (Hzb : FOin_tm z b = false) by (apply FOin_tm_above; lia).
  assert (Hxz : forall x, FOfree_in x (FOEq a b) = true -> x <> z).
  { intros x Hx E. subst x. cbn [FOfree_in] in Hx. rewrite Hza, Hzb in Hx. discriminate. }
  pose proof (Inv_snoc n V G h rho env _ (hsub_tm h a) w z HI Hw Ha0 Hav Hxz) as HI2.
  destruct HI2 as [HV2 [HG02 [HGV2 [HE2 [Henv2 [Hr2 Hh2]]]]]].
  assert (Na : FOPrH n (G ++ [FONUMR (hsub_tm h a) (FOVar w)]) (FONUMR (hsub_tm h a) (FOVar w)))
    by apply FOPrH_last.
  pose proof (FOPrH_numr_cong1 n _ (hsub_tm h a) (hsub_tm h b) (FOVar w) Na
                (FOPrH_weak_app _ _ _ _ Hab) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms))
    as Nb.
  pose proof (PRI_teval a n k (S w) _ h _ _ z (length env) HV2 HG02 HGV2 HE2 Henv2 Hr2
                ltac:(intros x Hx; apply Hh2; cbn [FOfree_in]; rewrite Hx; reflexivity)
                Hza (rho_sub_eq z (length env) rho) ltac:(rewrite length_app; cbn [length]; lia)
                ltac:(rewrite nth_snoc_len; exact Na)) as TA.
  pose proof (PRI_teval b n k (S w) _ h _ _ z (length env) HV2 HG02 HGV2 HE2 Henv2 Hr2
                ltac:(intros x Hx; apply Hh2; cbn [FOfree_in]; rewrite Hx; apply Bool.orb_true_r)
                Hzb (rho_sub_eq z (length env) rho) ltac:(rewrite length_app; cbn [length]; lia)
                ltac:(rewrite nth_snoc_len; exact Nb)) as TB.
  pose proof (PRI_thm_open n k (S w) _ _ (rho_sub (Some z) (length env) rho) _
                (FOPr_eq_via a b z) HE2) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ assert (Hx' : FOfree_in x (FOEq a b) = true)
                                by (cbn [FOfree_in]; rewrite Hx; first [reflexivity
                                                                     | apply Bool.orb_true_r]);
                              destruct (Hh2 x Hx') as [i [Hxi [Hi _]]]; exists i;
                              split; assumption
                            | exists (length env); split;
                              [apply rho_sub_eq | rewrite length_app; cbn [length]; lia] ])).
  pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE2 Hr2 T TA) as T1.
  pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE2 Hr2 T1 TB) as T2.
  refine (PRI_reslot n _ _ (S w) _ _ _ rho _ env _ _ _ _ T2); [| above_tac | avoid_tms | lia].
  intros x Hx. unfold SlotAgree. rewrite (rho_sub_ne z (length env) rho x (Hxz x Hx)).
  destruct (Hh x Hx) as [i [Hxi [Hi _]]]. rewrite Hxi, (nth_app_lt env [FOVar w] i Hi).
  apply FOPrH_refl.
Qed.

Lemma PRI_eq_neg : forall n k a b V G h rho env,
  Inv n V G h rho env (fun x => FOfree_in x (FOEq a b) = true) ->
  FOPrH n G (FONeg (FOEq (hsub_tm h a) (hsub_tm h b))) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho (FONeg (FOEq a b))) env.
Proof.
  intros n k a b V G h rho env HI Hab.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hha : forall x, FOin_tm x a = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; cbn [FOfree_in]; rewrite Hx; reflexivity).
  assert (Hhb : forall x, FOin_tm x b = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; cbn [FOfree_in]; rewrite Hx; apply Bool.orb_true_r).
  destruct (hsub_facts a n G V h rho env Hha) as [Ha0 Hav].
  destruct (hsub_facts b n G V h rho env Hhb) as [Hb0 Hbv].
  remember (S (FOvars_max (FOEq a b))) as z1 eqn:Ez1.
  cbn [FOvars_max] in Ez1.
  assert (Hz1a : FOin_tm z1 a = false) by (apply FOin_tm_above; lia).
  assert (Hz1b : FOin_tm z1 b = false) by (apply FOin_tm_above; lia).
  assert (Hz2a : FOin_tm (S z1) a = false) by (apply FOin_tm_above; lia).
  assert (Hz2b : FOin_tm (S z1) b = false) by (apply FOin_tm_above; lia).
  assert (Hxz1 : forall x, FOfree_in x (FOEq a b) = true -> x <> z1).
  { intros x Hx E. subst x. cbn [FOfree_in] in Hx. rewrite Hz1a, Hz1b in Hx. discriminate. }
  assert (Hxz2 : forall x, FOfree_in x (FOEq a b) = true -> x <> S z1).
  { intros x Hx E. subst x. cbn [FOfree_in] in Hx. rewrite Hz2a, Hz2b in Hx. discriminate. }
  refine (PRI_numr_ex n _ _ V 0 G _ env (hsub_tm h a) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
  intros w1 Hw1 _.
  pose proof (Inv_snoc n V G h rho env _ (hsub_tm h a) w1 z1 HI Hw1 Ha0 Hav Hxz1) as HI2.
  pose proof HI2 as [HV2 [HG02 [HGV2 [HE2 [Henv2 [Hr2 Hh2]]]]]].
  pose proof HE2 as [_ [_ [_ Henvv2]]].
  refine (PRI_numr_ex n _ _ (S w1) 0 _ _ _ (hsub_tm h b) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
  intros w2 Hw2 _.
  pose proof (Inv_snoc n (S w1) _ h _ _ _ (hsub_tm h b) w2 (S z1) HI2 Hw2 Hb0
                ltac:(intros s [<-|[]] w' Hw'; apply Hbv; [left; reflexivity | lia]) Hxz2) as HI3.
  pose proof HI3 as [HV3 [HG03 [HGV3 [HE3 [Henv3 [Hr3 Hh3]]]]]].
  pose proof HE3 as [_ [_ [_ Henvv3]]].
  assert (R1 : rho_sub (Some (S z1)) (length (env ++ [FOVar w1]))
                 (rho_sub (Some z1) (length env) rho) z1 = Some (length env)).
  { rewrite rho_sub_ne by lia. apply rho_sub_eq. }
  assert (R2 : rho_sub (Some (S z1)) (length (env ++ [FOVar w1]))
                 (rho_sub (Some z1) (length env) rho) (S z1) = Some (length (env ++ [FOVar w1])))
    by apply rho_sub_eq.
  assert (N1 : nth (length env) ((env ++ [FOVar w1]) ++ [FOVar w2]) FOZero = FOVar w1).
  { rewrite nth_app_lt by (rewrite length_app; cbn [length]; lia). apply nth_snoc_len. }
  assert (N2 : nth (length (env ++ [FOVar w1])) ((env ++ [FOVar w1]) ++ [FOVar w2]) FOZero =
               FOVar w2) by apply nth_snoc_len.
  lazymatch type of HG03 with FOctx_avoid ?G3 _ _ =>
    assert (Na : FOPrH n G3 (FONUMR (hsub_tm h a) (FOVar w1))) by wk_in;
    assert (Nb : FOPrH n G3 (FONUMR (hsub_tm h b) (FOVar w2))) by wk_in;
    assert (Hab3 : FOPrH n G3 (FONeg (FOEq (hsub_tm h a) (hsub_tm h b)))) by wk Hab
  end.
  pose proof (PRI_teval a n k (S w2) _ h _ _ z1 (length env) HV3 HG03 HGV3 HE3 Henv3 Hr3
                ltac:(intros x Hx; apply Hh3; cbn [FOfree_in]; rewrite Hx; reflexivity)
                Hz1a R1 ltac:(rewrite !length_app; cbn [length]; lia)
                ltac:(rewrite N1; exact Na)) as TA.
  pose proof (PRI_teval b n k (S w2) _ h _ _ (S z1) (length (env ++ [FOVar w1])) HV3 HG03
                HGV3 HE3 Henv3 Hr3
                ltac:(intros x Hx; apply Hh3; cbn [FOfree_in]; rewrite Hx; apply Bool.orb_true_r)
                Hz2b R2 ltac:(rewrite !length_app; cbn [length]; lia)
                ltac:(rewrite N2; exact Nb)) as TB.
  pose proof (PRI_neq_gen n k (S w2) _ _ _ z1 (S z1) (length env) (length (env ++ [FOVar w1]))
                (hsub_tm h a) (hsub_tm h b) HV3 HG03 HGV3 HE3 Henv3 ltac:(avoid_tms)
                ltac:(above_tac) R1 R2 Hab3 ltac:(rewrite N1; exact Na)
                ltac:(rewrite N2; exact Nb)) as NE.
  pose proof (PRI_thm_open n k (S w2) _ _ (rho_sub (Some (S z1)) (length (env ++ [FOVar w1]))
                (rho_sub (Some z1) (length env) rho)) _ (FOPr_neq_via a b z1 (S z1)) HE3) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ assert (Hx' : FOfree_in x (FOEq a b) = true)
                                by (cbn [FOfree_in]; rewrite Hx; first [reflexivity
                                                                     | apply Bool.orb_true_r]);
                              destruct (Hh3 x Hx') as [i [Hxi [Hi _]]]; exists i;
                              split; assumption
                            | exists (length env); split;
                              [exact R1 | rewrite !length_app; cbn [length]; lia]
                            | exists (length (env ++ [FOVar w1])); split;
                              [exact R2 | rewrite !length_app; cbn [length]; lia] ])).
  pose proof (PRI_mp n _ _ (S w2) _ _ _ _ _ HE3 Hr3 T TA) as T1.
  pose proof (PRI_mp n _ _ (S w2) _ _ _ _ _ HE3 Hr3 T1 TB) as T2.
  pose proof (PRI_mp n _ _ (S w2) _ _ _ _ _ HE3 Hr3 T2 NE) as T3.
  refine (PRI_reslot n _ _ (S w2) _ _ _ rho _ env _ _ _ _ T3); [| above_tac | avoid_tms | lia].
  intros x Hx. unfold SlotAgree.
  assert (Hx' : FOfree_in x (FOEq a b) = true)
    by (unfold FONeg in Hx; cbn [FOfree_in] in Hx |- *; rewrite Bool.orb_false_r in Hx; exact Hx).
  rewrite (rho_sub_ne (S z1) _ _ x (Hxz2 x Hx')), (rho_sub_ne z1 (length env) rho x (Hxz1 x Hx')).
  destruct (Hh x Hx') as [i [Hxi [Hi _]]]. rewrite Hxi.
  rewrite (nth_app_lt (env ++ [FOVar w1]) [FOVar w2] i) by (rewrite length_app; lia).
  rewrite (nth_app_lt env [FOVar w1] i Hi). apply FOPrH_refl.
Qed.

(** ** The statement of the main induction.

    [D0P n k W A]: for a formula whose variables lie below [W] and
    holders at or above [W], a derivation of the holder instance of [A]
    (of its negation) gives provable instances of the code of [A] (of
    its negation). *)

Definition D0P (n k W : nat) (A : FOFormula) : Prop :=
  FOvars_max A < W ->
  forall V G h rho env,
  Inv n V G h rho env (fun x => FOfree_in x A = true) ->
  (forall x, FOfree_in x A = true -> W <= h x) ->
  (FOPrH n G (hsub_f h A) -> PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho A) env) /\
  (FOPrH n G (FONeg (hsub_f h A)) ->
     PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho (FONeg A)) env).

Lemma hsub_free_range : forall A h lo hi, (forall x, FOfree_in x A = true -> lo <= h x < hi) ->
  forall w, FOfree_in w (hsub_f h A) = true -> lo <= w < hi.
Proof.
  intros A h lo hi H w Hw. destruct (FOfree_in_hsub A h w Hw) as [x [Hx <-]]. exact (H x Hx).
Qed.

Lemma Inv_ext : forall n V G h rho env Sv X,
  Inv n V G h rho env Sv ->
  (forall w, w < 1000 -> FOfree_in w X = false) -> (forall w, V <= w -> FOfree_in w X = false) ->
  Inv n V (G ++ [X]) h rho env Sv.
Proof.
  intros n V G h rho env Sv X [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]] HX0 HXV.
  assert (Hinc : forall Y, In Y G -> In Y (G ++ [X]))
    by (intros Y HY; apply in_or_app; left; exact HY).
  assert (HG1 : FOctx_avoid (G ++ [X]) 0 1000).
  { intros w ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
    apply FOfree_ctx_cons; [apply HX0; lia | apply FOfree_ctx_nil]. }
  split; [exact HV|]. split; [exact HG1|].
  split; [intros w Hw; apply FOfree_ctx_app_inv; [apply HGV; lia|];
          apply FOfree_ctx_cons; [apply HXV; lia | apply FOfree_ctx_nil]|].
  split; [apply (EnvOK_mono n V V G); [exact HE | exact Hinc | intros w ? ?; apply HG1; lia | lia]|].
  split; [exact Henv|]. split; [exact Hr|].
  intros x Hx. refine (HOK_ext n G _ V V h rho rho env env x (Hh x Hx) Hinc _ _ _ _);
    [lia | intros i Hi; exact Hi | lia | intros i Hi; reflexivity].
Qed.

Lemma Inv_hsub_free : forall n V G h rho env A,
  Inv n V G h rho env (fun x => FOfree_in x A = true) ->
  (forall w, w < 1000 -> FOfree_in w (hsub_f h A) = false) /\
  (forall w, V <= w -> FOfree_in w (hsub_f h A) = false).
Proof.
  intros n V G h rho env A [_ [_ [_ [_ [_ [_ Hh]]]]]].
  assert (Hr : forall x, FOfree_in x A = true -> 1100 <= h x < V)
    by (intros x Hx; exact (HOK_range n G V h rho env x (Hh x Hx))).
  split; intros w Hw; destruct (FOfree_in w (hsub_f h A)) eqn:E; try reflexivity;
    pose proof (hsub_free_range A h 1100 V Hr w E); lia.
Qed.

(** ** Propositional facts. *)

Lemma FOPrH_nimp_l : forall n G X Y, FOPrH n G (FONeg (FOImplF X Y)) -> FOPrH n G X.
Proof.
  intros n G X Y H.
  apply (FOPrH_or_elim n G X (FONeg X) X (FOPrH_em n G X)); [apply FOPrH_last|].
  apply FOPrH_efq. unfold FONeg in H |- *.
  apply (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ H)). apply FOPrH_intro.
  apply FOPrH_efq. apply (FOPrH_mp _ _ X); [apply FOPrH_assum; apply in_or_app; left;
    apply in_or_app; right; left; reflexivity | apply FOPrH_last].
Qed.

Lemma FOPrH_nimp_r : forall n G X Y, FOPrH n G (FONeg (FOImplF X Y)) -> FOPrH n G (FONeg Y).
Proof.
  intros n G X Y H. unfold FONeg in H |- *. apply FOPrH_intro.
  apply (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ H)). apply FOPrH_intro.
  apply FOPrH_assum. apply in_or_app. left. apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPr_K : forall B C, FOProvesTn 0 (FOImplF C (FOImplF B C)).
Proof.
  intros B C. change (FOPrH 0 [] (FOImplF C (FOImplF B C))).
  apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_assum. left. reflexivity.
Qed.

Lemma FOPr_neg_imp : forall B C, FOProvesTn 0 (FOImplF (FONeg B) (FOImplF B C)).
Proof.
  intros B C. change (FOPrH 0 [] (FOImplF (FONeg B) (FOImplF B C))).
  apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_efq. cbn [app]. unfold FONeg.
  apply (FOPrH_mp _ _ B); apply FOPrH_assum; [left | right; left]; reflexivity.
Qed.

Lemma FOPr_imp_neg : forall B C,
  FOProvesTn 0 (FOImplF B (FOImplF (FONeg C) (FONeg (FOImplF B C)))).
Proof.
  intros B C. change (FOPrH 0 [] (FOImplF B (FOImplF (FONeg C) (FONeg (FOImplF B C))))).
  unfold FONeg. apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_intro. cbn [app].
  apply (FOPrH_mp _ _ C); [apply FOPrH_assum; right; left; reflexivity|].
  apply (FOPrH_mp _ _ B); apply FOPrH_assum; [right; right; left | left]; reflexivity.
Qed.

Lemma FOPr_neg_false : FOProvesTn 0 (FONeg FOFalseF).
Proof.
  change (FOPrH 0 [] (FONeg FOFalseF)). unfold FONeg. apply FOPrH_intro.
  apply FOPrH_assum. left. reflexivity.
Qed.

(** ** Equations, falsity and implication. *)

Lemma D0P_eq : forall n k W a b, D0P n k W (FOEq a b).
Proof.
  intros n k W a b HW V G h rho env HI Hhw. split.
  - intros H. exact (PRI_eq_pos n k a b V G h rho env HI H).
  - intros H. exact (PRI_eq_neg n k a b V G h rho env HI H).
Qed.

Lemma D0P_false : forall n k W, D0P n k W FOFalseF.
Proof.
  intros n k W HW V G h rho env HI Hhw. split.
  - intros H. apply PRI_efq. exact H.
  - intros _. destruct HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
    exact (PRI_thm_open n k V G _ rho env FOPr_neg_false HE
             ltac:(intros x Hx; unfold FONeg in Hx; cbn in Hx; discriminate)).
Qed.

Lemma D0P_impl : forall n k W B C, D0P n k W B -> D0P n k W C -> D0P n k W (FOImplF B C).
Proof.
  intros n k W B C HB HC HW V G h rho env HI Hhw. cbn [FOvars_max] in HW.
  assert (HWB : FOvars_max B < W) by lia. assert (HWC : FOvars_max C < W) by lia.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  assert (HIB : Inv n V G h rho env (fun x => FOfree_in x B = true))
    by (apply (Inv_weaken n V G h rho env _ _ HI); intros x Hx; cbn [FOfree_in]; rewrite Hx;
        reflexivity).
  assert (HIC : Inv n V G h rho env (fun x => FOfree_in x C = true))
    by (apply (Inv_weaken n V G h rho env _ _ HI); intros x Hx; cbn [FOfree_in]; rewrite Hx;
        apply Bool.orb_true_r).
  assert (HhB : forall x, FOfree_in x B = true -> W <= h x)
    by (intros x Hx; apply Hhw; cbn [FOfree_in]; rewrite Hx; reflexivity).
  assert (HhC : forall x, FOfree_in x C = true -> W <= h x)
    by (intros x Hx; apply Hhw; cbn [FOfree_in]; rewrite Hx; apply Bool.orb_true_r).
  assert (Hfv : forall A', (forall x, FOfree_in x A' = true -> FOfree_in x (FOImplF B C) = true) ->
            forall x, FOfree_in x A' = true -> exists j, rho x = Some j /\ j < length env).
  { intros A' HA' x Hx. destruct (Hh x (HA' x Hx)) as [i [Hxi [Hi _]]]. exists i.
    split; assumption. }
  destruct (Inv_hsub_free n V G h rho env B HIB) as [HB0 HBV].
  split.
  - intros Himp. cbn [hsub_f] in Himp.
    apply (PRI_cases n _ _ V G _ env (hsub_f h B) HB0 HBV).
    + pose proof (Inv_ext n V G h rho env _ _ HIC HB0 HBV) as HIC'.
      pose proof (proj1 (HC HWC V _ h rho env HIC' HhC)
                    (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ Himp) (FOPrH_last _ _ _))) as TC.
      pose proof HIC' as [_ [_ [_ [HE' _]]]].
      pose proof (PRI_thm_open n k V _ _ rho env (FOPr_K B C) HE'
                    (Hfv (FOImplF C (FOImplF B C))
                       ltac:(intros x Hx; fv_cases Hx; cbn [FOfree_in]; rewrite Hx;
                                 first [reflexivity | apply Bool.orb_true_r]))) as T.
      exact (PRI_mp n _ _ V _ rho _ _ env HE' Hr T TC).
    + assert (HNB0 : forall w, w < 1000 -> FOfree_in w (FONeg (hsub_f h B)) = false)
        by (intros w Hw; unfold FONeg; cbn [FOfree_in]; rewrite HB0 by exact Hw; reflexivity).
      assert (HNBV : forall w, V <= w -> FOfree_in w (FONeg (hsub_f h B)) = false)
        by (intros w Hw; unfold FONeg; cbn [FOfree_in]; rewrite HBV by exact Hw; reflexivity).
      pose proof (Inv_ext n V G h rho env _ _ HIB HNB0 HNBV) as HIB'.
      pose proof (proj2 (HB HWB V _ h rho env HIB' HhB) (FOPrH_last _ _ _)) as TB.
      pose proof HIB' as [_ [_ [_ [HE' _]]]].
      pose proof (PRI_thm_open n k V _ _ rho env (FOPr_neg_imp B C) HE'
                    (Hfv (FOImplF (FONeg B) (FOImplF B C))
                       ltac:(intros x Hx; fv_cases Hx; cbn [FOfree_in]; rewrite Hx;
                                 first [reflexivity | apply Bool.orb_true_r]))) as T.
      exact (PRI_mp n _ _ V _ rho _ _ env HE' Hr T TB).
  - intros Hn. cbn [hsub_f] in Hn.
    pose proof (proj1 (HB HWB V G h rho env HIB HhB) (FOPrH_nimp_l _ _ _ _ Hn)) as TB.
    pose proof (proj2 (HC HWC V G h rho env HIC HhC) (FOPrH_nimp_r _ _ _ _ Hn)) as TC.
    pose proof (PRI_thm_open n k V G _ rho env (FOPr_imp_neg B C) HE
                  (Hfv (FOImplF B (FOImplF (FONeg C) (FONeg (FOImplF B C))))
                     ltac:(intros x Hx; fv_cases Hx; cbn [FOfree_in]; rewrite Hx;
                               first [reflexivity | apply Bool.orb_true_r]))) as T.
    exact (PRI_mp n _ _ V G rho _ _ env HE Hr (PRI_mp n _ _ V G rho _ _ env HE Hr T TB) TC).
Qed.

(** ** Patterns of a formula with a variable renamed to a slot name. *)

Lemma cpat_tm_subst_var : forall t v y rho j, FOin_tm y t = false -> rho y = Some j ->
  cpat_tm rho (FOsubst_t v (FOVar y) t) = cpat_tm (rho_sub (Some v) j rho) t.
Proof.
  induction t as [z| |a IH|a IHa b IHb|a IHa b IHb]; intros v y rho j Hy Hj;
    cbn [FOsubst_t cpat_tm].
  - unfold rho_sub. destruct (Nat.eqb_spec z v) as [->|Hzv].
    + cbn [cpat_tm]. rewrite Hj. reflexivity.
    + reflexivity.
  - reflexivity.
  - rewrite (IH v y rho j Hy Hj). reflexivity.
  - cbn [FOin_tm] in Hy. apply Bool.orb_false_iff in Hy as [H1 H2].
    rewrite (IHa v y rho j H1 Hj), (IHb v y rho j H2 Hj). reflexivity.
  - cbn [FOin_tm] in Hy. apply Bool.orb_false_iff in Hy as [H1 H2].
    rewrite (IHa v y rho j H1 Hj), (IHb v y rho j H2 Hj). reflexivity.
Qed.

Lemma cpat_f_subst_var : forall A v y rho j, FOvars_max A < y -> rho y = Some j ->
  cpat_f rho (FOsubst_f v (FOVar y) A) = cpat_f (rho_sub (Some v) j rho) A.
Proof.
  induction A as [a b| |B IHB C IHC|z B IHB|z B IHB]; intros v y rho j Hy Hj;
    cbn [FOvars_max] in Hy.
  - cbn [FOsubst_f cpat_f].
    rewrite (cpat_tm_subst_var a v y rho j), (cpat_tm_subst_var b v y rho j)
      by (first [apply FOin_tm_above; lia | exact Hj]).
    reflexivity.
  - reflexivity.
  - cbn [FOsubst_f cpat_f]. rewrite (IHB v y rho j), (IHC v y rho j) by (lia || exact Hj).
    reflexivity.
  - destruct (Nat.eqb_spec z v) as [->|Hzv].
    + rewrite FOsubst_f_all_self. cbn [cpat_f]. f_equal.
      apply cpat_f_ext. intros z0. symmetry. apply rho_hide_sub_self.
    + rewrite FOsubst_f_all_ne by exact Hzv. cbn [cpat_f]. f_equal.
      rewrite (IHB v y (rho_hide z rho) j) by
        (lia || (unfold rho_hide; rewrite (proj2 (Nat.eqb_neq y z) ltac:(lia)); exact Hj)).
      apply cpat_f_ext. intros z0. apply rho_sub_hide. cbn [ox_eq].
      apply Nat.eqb_neq. exact Hzv.
  - destruct (Nat.eqb_spec z v) as [->|Hzv].
    + rewrite FOsubst_f_ex_self. cbn [cpat_f]. f_equal.
      apply cpat_f_ext. intros z0. symmetry. apply rho_hide_sub_self.
    + rewrite FOsubst_f_ex_ne by exact Hzv. cbn [cpat_f]. f_equal.
      rewrite (IHB v y (rho_hide z rho) j) by
        (lia || (unfold rho_hide; rewrite (proj2 (Nat.eqb_neq y z) ltac:(lia)); exact Hj)).
      apply cpat_f_ext. intros z0. apply rho_sub_hide. cbn [ox_eq].
      apply Nat.eqb_neq. exact Hzv.
Qed.

(** ** Bounded quantifiers: facts of the object theory. *)

Lemma FOfree_in_neg_all_self : forall v X, FOfree_in v (FONeg (FOForall v X)) = false.
Proof. intros v X. unfold FONeg. cbn [FOfree_in]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma FOfree_in_neg_ex_self : forall v X, FOfree_in v (FONeg (FOExists v X)) = false.
Proof. intros v X. unfold FONeg. cbn [FOfree_in]. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma FOPr_ltv_zero : forall n v, FOProvesTn n (FONeg (FOltv v FOZero)).
Proof.
  intros n v. change (FOPrH n [] (FONeg (FOltv v FOZero))). unfold FONeg. apply FOPrH_intro.
  unfold FOltv.
  refine (FOPrH_ex_elim n ([] ++ [FOExists (S v) (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
            FOZero)]) (S v) _ _ _ _ (FOPrH_last _ _ _) _);
    [apply FOfree_ctx_cons; [apply FOfree_in_ex_self | apply FOfree_ctx_nil] | reflexivity |].
  apply (FOPrH_Q_succ_nonzero _ _ (FOPlus (FOVar v) (FOVar (S v)))).
  apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar v) (FOSucc (FOVar (S v)))));
    [apply FOPrH_eq_sym; apply FOPrH_Q_plus_succ | apply FOPrH_last].
Qed.

Lemma FOPr_ltv_succ : forall n v t, FOin_tm (S v) t = false ->
  FOProvesTn n (FOImplF (FOltv v t) (FOltv v (FOSucc t))).
Proof.
  intros n v t Ht. change (FOPrH n [] (FOImplF (FOltv v t) (FOltv v (FOSucc t)))).
  apply FOPrH_intro. unfold FOltv at 1.
  refine (FOPrH_ex_elim n ([] ++ [FOExists (S v) (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v))))
            t)]) (S v) _ _ _ _ (FOPrH_last _ _ _) _);
    [apply FOfree_ctx_cons; [apply FOfree_in_ex_self | apply FOfree_ctx_nil]
    | unfold FOltv; apply FOfree_in_ex_self |].
  unfold FOltv. apply (FOPrH_ex_intro _ _ (S v) (FOSucc (FOVar (S v))));
    [reflexivity|].
  cbn [FOsubst_f FOsubst_t]. rewrite Nat.eqb_refl.
  rewrite (proj2 (Nat.eqb_neq v (S v)) ltac:(lia)).
  rewrite (FOsubst_t_not_in t (S v) _ Ht).
  apply (FOPrH_eq_trans _ _ _ (FOSucc (FOPlus (FOVar v) (FOSucc (FOVar (S v)))))).
  - apply FOPrH_Q_plus_succ.
  - apply FOPrH_congS. apply FOPrH_last.
Qed.

Lemma FOPr_ltv_self : forall n v t, FOin_tm (S v) t = false ->
  FOProvesTn n (FOExists (S v) (FOEq (FOPlus t (FOSucc (FOVar (S v)))) (FOSucc t))).
Proof.
  intros n v t Ht.
  change (FOPrH n [] (FOExists (S v) (FOEq (FOPlus t (FOSucc (FOVar (S v)))) (FOSucc t)))).
  apply (FOPrH_ex_intro _ _ (S v) FOZero); [reflexivity|].
  cbn [FOsubst_f FOsubst_t]. rewrite Nat.eqb_refl. rewrite (FOsubst_t_not_in t (S v) _ Ht).
  apply FOPrH_ring. fo_ring.
Qed.

Lemma FOPr_not_all : forall n v X,
  FOProvesTn n (FOImplF (FONeg (FOForall v X)) (FOExists v (FONeg X))).
Proof.
  intros n v X. change (FOPrH n [] (FOImplF (FONeg (FOForall v X)) (FOExists v (FONeg X)))).
  apply FOPrH_intro. cbn [app].
  apply (FOPrH_or_elim n _ (FOExists v (FONeg X)) (FONeg (FOExists v (FONeg X))) _
           (FOPrH_em _ _ _)); [apply FOPrH_last|].
  apply FOPrH_efq.
  apply (FOPrH_mp _ _ (FOForall v X)); [apply FOPrH_assum; left; reflexivity|].
  apply FOPrH_all_intro.
  { apply FOfree_ctx_cons; [apply FOfree_in_neg_all_self|].
    apply FOfree_ctx_cons; [apply FOfree_in_neg_ex_self | apply FOfree_ctx_nil]. }
  apply (FOPrH_or_elim n _ X (FONeg X) _ (FOPrH_em _ _ _)); [apply FOPrH_last|].
  apply FOPrH_efq.
  apply (FOPrH_mp _ _ (FOExists v (FONeg X)));
    [apply FOPrH_assum; apply in_or_app; left; right; left; reflexivity|].
  apply (FOPrH_ex_intro _ _ v (FOVar v)); [apply FOsubst_ok_var_self|].
  rewrite FOsubst_f_id. apply FOPrH_last.
Qed.

Lemma FOPr_not_ex_and : forall n v L X,
  FOProvesTn n (FOImplF (FONeg (FOExists v (FOAnd L X))) (FOForall v (FOImplF L (FONeg X)))).
Proof.
  intros n v L X.
  change (FOPrH n [] (FOImplF (FONeg (FOExists v (FOAnd L X))) (FOForall v (FOImplF L (FONeg X))))).
  apply FOPrH_intro. cbn [app].
  apply FOPrH_all_intro.
  { apply FOfree_ctx_cons; [apply FOfree_in_neg_ex_self | apply FOfree_ctx_nil]. }
  apply FOPrH_intro. unfold FONeg at 2. apply FOPrH_intro.
  apply (FOPrH_mp _ _ (FOExists v (FOAnd L X))); [apply FOPrH_assum; left; reflexivity|].
  apply (FOPrH_ex_intro _ _ v (FOVar v)); [apply FOsubst_ok_var_self|].
  rewrite FOsubst_f_id. apply FOPrH_and_intro.
  - apply FOPrH_assum. right. left. reflexivity.
  - apply FOPrH_last.
Qed.

(** ** Closed theorems for bounded quantifiers. *)

Lemma FOsubst_f_ltv_var : forall y s v, y <> v -> y <> S v ->
  FOsubst_f y s (FOltv v (FOVar y)) = FOltv v s.
Proof.
  intros y s v H1 H2. unfold FOltv.
  rewrite FOsubst_f_ex_ne by lia. rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_succ.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne by lia. reflexivity.
Qed.

Lemma FOsubst_ok_ltv : forall x s v t, FOin_tm (S v) s = false ->
  FOsubst_ok x s (FOltv v t) = true.
Proof. intros x s v t H. unfold FOltv. apply FOsubst_ok_ex; [exact H | apply FOsubst_ok_eq]. Qed.

Lemma FOPr_ball_base : forall v y D, y <> v -> y <> S v ->
  FOProvesTn 0 (FOImplF (FOEq FOZero (FOVar y)) (FOForall v (FOImplF (FOltv v (FOVar y)) D))).
Proof.
  intros v y D H1 H2.
  change (FOPrH 0 [] (FOImplF (FOEq FOZero (FOVar y)) (FOForall v (FOImplF (FOltv v (FOVar y)) D)))).
  apply FOPrH_intro.
  apply FOPrH_all_intro.
  { apply FOfree_ctx_app_inv; [apply FOfree_ctx_nil|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. cbn [FOfree_in FOin_tm].
    rewrite (proj2 (Nat.eqb_neq y v) H1). reflexivity. }
  apply FOPrH_intro. apply FOPrH_efq.
  assert (E0 : FOPrH 0 (([] ++ [FOEq FOZero (FOVar y)]) ++ [FOltv v (FOVar y)])
                 (FOEq FOZero (FOVar y))) by wk_in.
  pose proof (FOPrH_leibniz 0 (([] ++ [FOEq FOZero (FOVar y)]) ++ [FOltv v (FOVar y)]) y
                (FOVar y) FOZero (FOltv v (FOVar y)) (FOsubst_ok_var_self _ _)
                (FOsubst_ok_ltv y FOZero v (FOVar y) eq_refl)
                (FOPrH_eq_sym _ _ _ _ E0)) as L.
  rewrite FOsubst_f_id, FOsubst_f_ltv_var in L by assumption.
  exact (FOPrH_mp _ _ _ _ (FOPrH_thm _ _ _ (FOPr_ltv_zero 0 v)) (L (FOPrH_last _ _ _))).
Qed.

Lemma FOPr_ball_step : forall v y D, FOvars_max D < y -> S v < y ->
  FOProvesTn 0 (FOImplF (FOsubst_f v (FOVar y) D)
    (FOImplF (FOForall v (FOImplF (FOltv v (FOVar y)) D))
       (FOForall v (FOImplF (FOltv v (FOSucc (FOVar y))) D)))).
Proof.
  intros v y D HD Hv.
  change (FOPrH 0 [] (FOImplF (FOsubst_f v (FOVar y) D)
    (FOImplF (FOForall v (FOImplF (FOltv v (FOVar y)) D))
       (FOForall v (FOImplF (FOltv v (FOSucc (FOVar y))) D))))).
  apply FOPrH_intro. apply FOPrH_intro.
  apply FOPrH_all_intro.
  { apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_nil|]|].
    - apply FOfree_ctx_cons; [apply FOfree_in_subst_away; lia | apply FOfree_ctx_nil].
    - apply FOfree_ctx_cons; [apply FOfree_in_all_self | apply FOfree_ctx_nil]. }
  apply FOPrH_intro.
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (H1 : FOPrH 0 G1 (FOsubst_f v (FOVar y) D)) by wk_in;
    assert (H2 : FOPrH 0 G1 (FOForall v (FOImplF (FOltv v (FOVar y)) D))) by wk_in;
    assert (H3 : FOPrH 0 G1 (FOltv v (FOSucc (FOVar y)))) by wk_in;
    assert (HG1 : forall w, S y <= w -> FOfree_ctx w G1)
  end.
  { intros w Hw.
    apply FOfree_ctx_app_inv;
      [apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_nil|]|]|];
      (apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]).
    - destruct (FOfree_in w (FOsubst_f v (FOVar y) D)) eqn:E; [|reflexivity].
      destruct (FOfree_in_subst_gen D w v (FOVar y) E) as [[_ Hf]|Hf].
      + rewrite FOfree_in_above in Hf by lia. discriminate.
      + cbn [FOin_tm] in Hf. apply Nat.eqb_eq in Hf. lia.
    - apply FOfree_in_above. cbn [FOvars_max FOmax_var_tm]. unfold FOltv.
      cbn [FOvars_max FOmax_var_tm]. lia.
    - apply FOfree_in_above. unfold FOltv. cbn [FOvars_max FOmax_var_tm]. lia. }
  refine (FOPrH_ex_elim_fresh 0 _ (S v) (S y)
            (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) (FOSucc (FOVar y))) D
            (HG1 (S y) (le_n _)) _ _ _ H3 _);
    [apply FOfree_in_above; lia | cbn [FOfree_in FOin_tm]; nat_eqb_simpl; reflexivity
    | reflexivity |].
  cbn [FOsubst_f FOsubst_t]. nat_eqb_simpl.
  lazymatch goal with |- FOPrH _ ?G2 _ =>
    assert (E1 : FOPrH 0 G2 (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S y)))) (FOSucc (FOVar y))))
      by apply FOPrH_last;
    assert (H1' : FOPrH 0 G2 (FOsubst_f v (FOVar y) D)) by wk H1;
    assert (H2' : FOPrH 0 G2 (FOForall v (FOImplF (FOltv v (FOVar y)) D))) by wk H2;
    assert (HG2 : FOfree_ctx (S (S y)) G2)
  end.
  { apply FOfree_ctx_app_inv; [apply HG1; lia|]. apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
    cbn [FOfree_in FOin_tm]. nat_eqb_simpl. reflexivity. }
  lazymatch type of E1 with FOPrH _ ?G2 _ =>
    assert (E2 : FOPrH 0 G2 (FOEq (FOPlus (FOVar v) (FOVar (S y))) (FOVar y)))
  end.
  { apply FOPrH_Q_succ_inj.
    exact (FOPrH_eq_trans _ _ _ _ _ (FOPrH_eq_sym _ _ _ _ (FOPrH_Q_plus_succ _ _ _ _)) E1). }
  apply (FOPrH_cases_zs 0 _ (FOVar (S y)) (S (S y)) D ltac:(lia)
           ltac:(cbn [FOin_tm]; apply Nat.eqb_neq; lia) HG2
           ltac:(apply FOfree_in_above; lia) ltac:(cbn [FOin_tm]; apply Nat.eqb_neq; lia)).
  - lazymatch goal with |- FOPrH _ ?G3 _ =>
      assert (Eu : FOPrH 0 G3 (FOEq (FOVar (S y)) FOZero)) by apply FOPrH_last;
      assert (Evy : FOPrH 0 G3 (FOEq (FOVar y) (FOVar v)))
    end.
    { apply FOPrH_eq_sym.
      apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar v) FOZero));
        [apply FOPrH_eq_sym; apply FOPrH_Q_plus_zero|].
      apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar v) (FOVar (S y)))).
      - apply FOPrH_congPlus; [apply FOPrH_refl | apply FOPrH_eq_sym; exact Eu].
      - apply FOPrH_weak_app. exact E2. }
    pose proof (FOPrH_leibniz 0 _ v (FOVar y) (FOVar v) D
                  (FOsubst_ok_above D v y ltac:(lia)) (FOsubst_ok_var_self D v) Evy) as L.
    rewrite FOsubst_f_id in L. apply L. apply FOPrH_weak_app. exact H1'.
  - lazymatch goal with |- FOPrH _ ?G3 _ =>
      assert (Eu : FOPrH 0 G3 (FOEq (FOVar (S y)) (FOSucc (FOVar (S (S y))))))
        by apply FOPrH_last;
      assert (Lv : FOPrH 0 G3 (FOltv v (FOVar y)))
    end.
    { unfold FOltv. apply (FOPrH_ex_intro _ _ (S v) (FOVar (S (S y)))); [reflexivity|].
      cbn [FOsubst_f FOsubst_t]. nat_eqb_simpl.
      apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar v) (FOVar (S y)))).
      - apply FOPrH_congPlus; [apply FOPrH_refl | apply FOPrH_eq_sym; exact Eu].
      - apply FOPrH_weak_app. exact E2. }
    exact (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _ (FOPrH_weak_app _ _ _ _ H2')) Lv).
Qed.

Lemma FOsubst_f_ball_y : forall v y t A, v <> y -> S v <> y -> FOfree_in y A = false ->
  FOsubst_f y t (FOForall v (FOImplF (FOltv v (FOVar y)) A)) = FOForall v (FOImplF (FOltv v t) A).
Proof.
  intros v y t A H1 H2 HA. rewrite FOsubst_f_all_ne by lia. rewrite FOsubst_f_impl.
  rewrite FOsubst_f_ltv_var by lia. rewrite (FOsubst_f_not_free A y t HA). reflexivity.
Qed.

Lemma FOsubst_ok_ball_y : forall v y t A, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  FOfree_in y A = false ->
  FOsubst_ok y t (FOForall v (FOImplF (FOltv v (FOVar y)) A)) = true.
Proof.
  intros v y t A H1 H2 HA. apply FOsubst_ok_all; [exact H1|]. apply FOsubst_ok_impl;
    [apply FOsubst_ok_ltv; exact H2 | apply FOsubst_ok_not_free; exact HA].
Qed.

Lemma FOPr_ball_final : forall v y t A,
  FOin_tm v t = false -> FOin_tm (S v) t = false -> FOfree_in y A = false ->
  v <> y -> S v <> y ->
  FOProvesTn 0 (FOImplF (FOEq t (FOVar y))
    (FOImplF (FOForall v (FOImplF (FOltv v (FOVar y)) A)) (FOForall v (FOImplF (FOltv v t) A)))).
Proof.
  intros v y t A Hv HSv HA H1 H2.
  change (FOPrH 0 [] (FOImplF (FOEq t (FOVar y))
    (FOImplF (FOForall v (FOImplF (FOltv v (FOVar y)) A)) (FOForall v (FOImplF (FOltv v t) A))))).
  apply FOPrH_intro. apply FOPrH_intro.
  pose proof (FOPrH_leibniz 0 (([] ++ [FOEq t (FOVar y)]) ++
                [FOForall v (FOImplF (FOltv v (FOVar y)) A)]) y (FOVar y) t
                (FOForall v (FOImplF (FOltv v (FOVar y)) A)) (FOsubst_ok_var_self _ _)
                (FOsubst_ok_ball_y v y t A Hv HSv HA)) as L.
  rewrite FOsubst_f_id, FOsubst_f_ball_y in L by assumption.
  apply L; [apply FOPrH_eq_sym; wk_in | apply FOPrH_last].
Qed.

Lemma FOPr_bexneg_final : forall v y t A,
  FOin_tm v t = false -> FOin_tm (S v) t = false -> FOfree_in y A = false ->
  v <> y -> S v <> y -> FOin_tm v (FOVar y) = false ->
  FOProvesTn 0 (FOImplF (FOEq t (FOVar y))
    (FOImplF (FOForall v (FOImplF (FOltv v (FOVar y)) (FONeg A)))
       (FONeg (FOExists v (FOAnd (FOltv v t) A))))).
Proof.
  intros v y t A Hv HSv HA H1 H2 Hvy.
  change (FOPrH 0 [] (FOImplF (FOEq t (FOVar y))
    (FOImplF (FOForall v (FOImplF (FOltv v (FOVar y)) (FONeg A)))
       (FONeg (FOExists v (FOAnd (FOltv v t) A)))))).
  apply FOPrH_intro. apply FOPrH_intro.
  assert (HNA : FOfree_in y (FONeg A) = false)
    by (unfold FONeg; cbn [FOfree_in]; rewrite HA; reflexivity).
  pose proof (FOPrH_leibniz 0 (([] ++ [FOEq t (FOVar y)]) ++
                [FOForall v (FOImplF (FOltv v (FOVar y)) (FONeg A))]) y (FOVar y) t
                (FOForall v (FOImplF (FOltv v (FOVar y)) (FONeg A))) (FOsubst_ok_var_self _ _)
                (FOsubst_ok_ball_y v y t (FONeg A) Hv HSv HNA)) as L.
  rewrite FOsubst_f_id, FOsubst_f_ball_y in L by assumption.
  assert (H3 : FOPrH 0 (([] ++ [FOEq t (FOVar y)]) ++
                 [FOForall v (FOImplF (FOltv v (FOVar y)) (FONeg A))])
                 (FOForall v (FOImplF (FOltv v t) (FONeg A))))
    by (apply L; [apply FOPrH_eq_sym; wk_in | apply FOPrH_last]).
  unfold FONeg at 2. apply FOPrH_intro.
  refine (FOPrH_ex_elim 0 _ v _ FOFalseF _ _ (FOPrH_last _ _ _) _).
  - apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv|]|].
    + apply FOfree_ctx_nil.
    + apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. cbn [FOfree_in].
      rewrite Hv, Hvy. reflexivity.
    + apply FOfree_ctx_cons; [apply FOfree_in_all_self | apply FOfree_ctx_nil].
    + apply FOfree_ctx_cons; [apply FOfree_in_ex_self | apply FOfree_ctx_nil].
  - reflexivity.
  - lazymatch goal with |- FOPrH _ ?G4 _ =>
      assert (H4 : FOPrH 0 G4 (FOForall v (FOImplF (FOltv v t) (FONeg A)))) by wk H3;
      assert (H5 : FOPrH 0 G4 (FOAnd (FOltv v t) A)) by apply FOPrH_last
    end.
    apply FOPrH_all_same in H4. unfold FONeg in H4.
    exact (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ H4 (FOPrH_and_l _ _ _ _ H5)) (FOPrH_and_r _ _ _ _ H5)).
Qed.

Lemma FOPr_ball_neg : forall v u t A, u <> S v -> FOin_tm (S v) t = false ->
  FOProvesTn 0 (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar u))) t)
    (FOImplF (FONeg A) (FONeg (FOForall v (FOImplF (FOltv v t) A))))).
Proof.
  intros v u t A H1 H2.
  change (FOPrH 0 [] (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar u))) t)
    (FOImplF (FONeg A) (FONeg (FOForall v (FOImplF (FOltv v t) A)))))).
  apply FOPrH_intro. apply FOPrH_intro. unfold FONeg at 2. apply FOPrH_intro.
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (E : FOPrH 0 G1 (FOEq (FOPlus (FOVar v) (FOSucc (FOVar u))) t)) by wk_in;
    assert (NA : FOPrH 0 G1 (FONeg A)) by wk_in;
    assert (HA : FOPrH 0 G1 (FOForall v (FOImplF (FOltv v t) A))) by apply FOPrH_last;
    assert (L : FOPrH 0 G1 (FOltv v t))
  end.
  { unfold FOltv. apply (FOPrH_ex_intro _ _ (S v) (FOVar u)); [reflexivity|].
    cbn [FOsubst_f FOsubst_t]. rewrite Nat.eqb_refl.
    rewrite (proj2 (Nat.eqb_neq v (S v)) ltac:(lia)). rewrite (FOsubst_t_not_in t (S v) _ H2).
    exact E. }
  unfold FONeg in NA.
  exact (FOPrH_mp _ _ _ _ NA (FOPrH_mp _ _ _ _ (FOPrH_all_same _ _ _ _ HA) L)).
Qed.

Lemma FOPr_bex_pos : forall v u t A, u <> S v -> FOin_tm (S v) t = false ->
  FOProvesTn 0 (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar u))) t)
    (FOImplF A (FOExists v (FOAnd (FOltv v t) A)))).
Proof.
  intros v u t A H1 H2.
  change (FOPrH 0 [] (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar u))) t)
    (FOImplF A (FOExists v (FOAnd (FOltv v t) A))))).
  apply FOPrH_intro. apply FOPrH_intro.
  apply (FOPrH_ex_intro _ _ v (FOVar v)); [apply FOsubst_ok_var_self|]. rewrite FOsubst_f_id.
  apply FOPrH_and_intro; [|apply FOPrH_last].
  unfold FOltv. apply (FOPrH_ex_intro _ _ (S v) (FOVar u)); [reflexivity|].
  cbn [FOsubst_f FOsubst_t]. rewrite Nat.eqb_refl.
  rewrite (proj2 (Nat.eqb_neq v (S v)) ltac:(lia)). rewrite (FOsubst_t_not_in t (S v) _ H2).
  wk_in.
Qed.

(** ** The bounded universal closure, inside the provability predicate.

    [PhiBall Nt]: every numeral code [m] of [Nt], under the hypothesis
    that the body holds below [Nt], gives a provable instance of [P]
    over [env ++ [m]]. *)

Definition PhiBall (cores : list nat) (u0 B0 m v : nat) (hD : FOFormula) (env : list FOTerm)
    (P : CPat) (Nt : FOTerm) : FOFormula :=
  FOForall m (FOImplF (FONUMR Nt (FOVar m))
    (FOImplF (FOForall v (FOImplF (FOltv v Nt) hD))
       (PRIf cores u0 B0 (env ++ [FOVar m]) P))).

Lemma PhiBall_subst : forall cores u0 B0 m v hD env P N s,
  N <> m -> N <> v -> N <> S v -> 1000 <= N -> N < B0 -> FOtms_avoid [s] 802 805 ->
  FOfree_in N hD = false -> FOtms_avoid env N (S N) ->
  FOsubst_f N s (PhiBall cores u0 B0 m v hD env P (FOVar N)) = PhiBall cores u0 B0 m v hD env P s.
Proof.
  intros cores u0 B0 m v hD env P N s Hm Hv HSv HN HB Hs HhD Henv. unfold PhiBall.
  rewrite (FOsubst_f_all_ne N s m) by lia. rewrite !FOsubst_f_impl, FOsubst_f_NUMR by (lia || avoid_tms).
  rewrite (FOsubst_f_all_ne N s v) by lia. rewrite FOsubst_f_impl, FOsubst_f_ltv_var by lia.
  rewrite (FOsubst_f_not_free hD N s HhD). rewrite FOsubst_f_PRIf by lia.
  rewrite FOsubst_t_var_eq', FOsubst_t_var_ne by lia. rewrite map_app. cbn [map].
  rewrite FOsubst_t_var_ne by lia.
  rewrite (FOsubst_map_avoid N s env) by (intros t Ht; apply (Henv t Ht); lia). reflexivity.
Qed.

Lemma PhiBall_inst : forall n G cores u0 B0 m v hD env P Nt tm,
  FOPrH n G (PhiBall cores u0 B0 m v hD env P Nt) ->
  1000 <= m -> m < B0 -> FOin_tm m Nt = false -> FOfree_in m hD = false ->
  FOtms_avoid env m (S m) -> FOtms_avoid [tm] 0 1000 -> FOtms_avoid [tm] B0 (B0 + cpat_span P) ->
  m <> v -> m <> S v ->
  FOPrH n G (FOImplF (FONUMR Nt tm)
    (FOImplF (FOForall v (FOImplF (FOltv v Nt) hD)) (PRIf cores u0 B0 (env ++ [tm]) P))).
Proof.
  intros n G cores u0 B0 m v hD env P Nt tm H Hm HmB HNt HhD Henv Htm0 HtmB Hmv HmSv.
  unfold PhiBall in H.
  assert (Hfr : FOfree_in m (FOForall v (FOImplF (FOltv v Nt) hD)) = false).
  { cbn [FOfree_in]. destruct (Nat.eqb v m); [reflexivity|].
    apply Bool.orb_false_iff. split; [|exact HhD].
    apply FOfree_in_ltv; [lia | exact HNt]. }
  apply (FOPrH_inst n G m tm) in H;
    [| apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_not_free; exact Hfr|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite !FOsubst_f_impl, FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite (FOsubst_f_not_free _ m tm Hfr) in H.
  rewrite FOsubst_f_PRIf in H by lia. rewrite map_app in H. cbn [map] in H.
  rewrite FOsubst_t_var_eq', (FOsubst_t_not_in Nt m tm HNt) in H.
  rewrite (FOsubst_map_avoid m tm env) in H by (intros t Ht; apply (Henv t Ht); lia).
  exact H.
Qed.

Lemma FOPr_ball_mono : forall n v t X, FOin_tm (S v) t = false ->
  FOProvesTn n (FOImplF (FOForall v (FOImplF (FOltv v (FOSucc t)) X))
                  (FOForall v (FOImplF (FOltv v t) X))).
Proof.
  intros n v t X Ht.
  change (FOPrH n [] (FOImplF (FOForall v (FOImplF (FOltv v (FOSucc t)) X))
                  (FOForall v (FOImplF (FOltv v t) X)))).
  apply FOPrH_intro. apply FOPrH_all_intro.
  { apply FOfree_ctx_app_inv; [apply FOfree_ctx_nil|].
    apply FOfree_ctx_cons; [apply FOfree_in_all_self | apply FOfree_ctx_nil]. }
  apply FOPrH_intro.
  apply (FOPrH_mp _ _ (FOltv v (FOSucc t))).
  - apply FOPrH_all_same with (x := v). apply FOPrH_assum. apply in_or_app. left.
    apply in_or_app. right. left. reflexivity.
  - apply (FOPrH_mp _ _ (FOltv v t)); [apply FOPrH_thm; apply FOPr_ltv_succ; exact Ht|].
    apply FOPrH_last.
Qed.

Lemma CPrel_ball_succ : forall n G v y D rho env a b,
  (forall z, FOfree_in z D = true -> z <> v -> exists i, rho z = Some i /\ i < length env) ->
  y <> v -> y <> S v -> rho y = Some (length env) ->
  FOPrH n G (FOcpairF (FOnumeral 2) a b) ->
  CPrel n G (env ++ [a]) (env ++ [b])
    (cpat_f rho (FOForall v (FOImplF (FOltv v (FOSucc (FOVar y))) D)))
    (cpat_f rho (FOForall v (FOImplF (FOltv v (FOVar y)) D))).
Proof.
  intros n G v y D rho env a b HD Hyv HySv Hy C.
  assert (C' : FOPrH n G (FOcpairF (FOnumeral 2) (nth (length env) (env ++ [a]) FOZero)
                                    (nth (length env) (env ++ [b]) FOZero)))
    by (rewrite !nth_snoc_len; exact C).
  assert (Ry : rho_hide (S v) (rho_hide v rho) y = Some (length env)).
  { unfold rho_hide. rewrite (proj2 (Nat.eqb_neq y (S v)) HySv),
      (proj2 (Nat.eqb_neq y v) Hyv). exact Hy. }
  assert (Rv : rho_hide (S v) (rho_hide v rho) v = None).
  { unfold rho_hide. rewrite (proj2 (Nat.eqb_neq v (S v)) ltac:(lia)), Nat.eqb_refl.
    reflexivity. }
  assert (RSv : rho_hide (S v) (rho_hide v rho) (S v) = None).
  { unfold rho_hide. rewrite Nat.eqb_refl. reflexivity. }
  cbn [cpat_f]. unfold FOltv. cbn [cpat_f cpat_tm]. rewrite Ry, Rv, RSv.
  unfold pAllP, pImpP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair; [apply cpr_lit|].
  apply cpr_pair; [apply cpr_lit|]. apply cpr_pair.
  - cprel_tac.
  - apply CPrel_cpat_f. intros z Hz. unfold SlotAgree, rho_hide.
    destruct (Nat.eqb_spec z v) as [->|Hzv]; [exact I|].
    destruct (HD z Hz Hzv) as [i [Hzi Hi]]. rewrite Hzi.
    rewrite !nth_app_lt by exact Hi. apply FOPrH_refl.
Qed.

(** ** Moving the invariant. *)

Lemma Inv_move : forall n V V' G G' h rho env Sv,
  Inv n V G h rho env Sv -> (forall X, In X G -> In X G') -> V <= V' ->
  FOctx_avoid G' 0 1000 -> (forall w, V' <= w -> FOfree_ctx w G') ->
  Inv n V' G' h rho env Sv.
Proof.
  intros n V V' G G' h rho env Sv [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]] Hinc HVV HG0' HGV'.
  split; [lia|]. split; [exact HG0'|]. split; [exact HGV'|].
  split; [apply (EnvOK_mono n V V' G G' env HE Hinc); [intros w ? ?; apply HG0'; lia | lia]|].
  split; [exact Henv|]. split; [exact Hr|].
  intros x Hx. refine (HOK_ext n G G' V V' h rho rho env env x (Hh x Hx) Hinc HVV _ _ _);
    [intros i Hi; exact Hi | lia | intros i Hi; reflexivity].
Qed.

Lemma Inv_slot : forall n V G h rho env Sv t m z,
  Inv n V G h rho env Sv -> FOPrH n G (FONUMR t m) ->
  FOtms_avoid [m] 0 1100 -> (forall s, In s [m] -> forall w, V <= w -> FOin_tm w s = false) ->
  (forall x, Sv x -> x <> z) ->
  Inv n V G h (rho_sub (Some z) (length env) rho) (env ++ [m]) Sv.
Proof.
  intros n V G h rho env Sv t m z [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]] Hm Hm0 Hmv Hz.
  split; [exact HV|]. split; [exact HG0|]. split; [exact HGV|].
  split; [apply (EnvOK_snoc n V G env m t HE Hm); [avoid_tms | intros w Hw; apply (Hmv m); [left; reflexivity | exact Hw]]|].
  split; [avoid_tms|]. split.
  - intros z0 i Hz0. rewrite length_app. cbn [length]. unfold rho_sub in Hz0.
    destruct (Nat.eqb z0 z); [injection Hz0 as <-; lia | specialize (Hr z0 i Hz0); lia].
  - intros x Hx. refine (HOK_ext n G G V V h rho _ env _ x (Hh x Hx) (fun X HX => HX) _ _ _ _);
      [ lia | intros i Hi; rewrite (rho_sub_ne z (length env) rho x (Hz x Hx)); exact Hi
      | rewrite length_app; lia | intros i Hi; apply nth_app_lt; exact Hi ].
Qed.

Lemma Inv_holder : forall n V G h rho env Sv v N m,
  Inv n V G h rho env (fun x => Sv x /\ x <> v) -> FOPrH n G (FONUMR (FOVar N) m) ->
  1100 <= N -> N < V ->
  FOtms_avoid [m] 0 1100 -> (forall s, In s [m] -> forall w, V <= w -> FOin_tm w s = false) ->
  Inv n V G (h_upd v N h) (rho_sub (Some v) (length env) rho) (env ++ [m]) Sv.
Proof.
  intros n V G h rho env Sv v N m HI Hm HN1 HN2 Hm0 Hmv.
  pose proof (Inv_slot n V G h rho env _ (FOVar N) m v HI Hm Hm0 Hmv
                ltac:(intros x [_ Hx]; exact Hx)) as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  split; [exact HV|]. split; [exact HG0|]. split; [exact HGV|]. split; [exact HE|].
  split; [exact Henv|]. split; [exact Hr|].
  intros x Hx. destruct (Nat.eqb_spec x v) as [->|Hxv].
  - exists (length env). rewrite rho_sub_eq. split; [reflexivity|].
    split; [rewrite length_app; cbn [length]; lia|].
    unfold h_upd. rewrite Nat.eqb_refl, nth_snoc_len. split; [exact Hm | lia].
  - destruct (Hh x (conj Hx Hxv)) as [i [Hxi [Hi [HNx [H1 H2]]]]].
    exists i. unfold h_upd. rewrite (proj2 (Nat.eqb_neq x v) Hxv). split; [exact Hxi|].
    split; [exact Hi|]. split; [exact HNx | lia].
Qed.

Lemma hsub_ltv : forall h v t, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  hsub_f (h_hide v h) (FOltv v t) = FOltv v (hsub_tm h t).
Proof.
  intros h v t H1 H2. unfold FOltv. cbn [hsub_f hsub_tm].
  unfold h_hide at 1 2. rewrite Nat.eqb_refl.
  rewrite (proj2 (Nat.eqb_neq v (S v)) ltac:(lia)). unfold h_hide at 1. rewrite Nat.eqb_refl.
  f_equal. f_equal. apply hsub_tm_ext. intros z Hz. unfold h_hide.
  destruct (Nat.eqb_spec z (S v)) as [->|H3]; [congruence|].
  destruct (Nat.eqb_spec z v) as [->|H4]; [congruence | reflexivity].
Qed.

Ltac fv_cases H ::=
  repeat match type of H with
  | FOfree_in _ (FONeg _) = true => unfold FONeg in H
  | FOfree_in _ (FOAnd _ _) = true => unfold FOAnd, FONeg in H
  | FOfree_in _ (FOltv _ _) = true => unfold FOltv in H
  | FOfree_in _ (FOImplF _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ (FOEq _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ (FOForall _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ (FOExists _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ FOFalseF = true => discriminate H
  | (if ?c then false else _) = true =>
      let E := fresh "E" in destruct c eqn:E; [discriminate H|]
  | (_ || _)%bool = true => apply Bool.orb_true_iff in H; destruct H as [H|H]
  | FOin_tm _ (FOSucc _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (FOPlus _ _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (FOMult _ _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (opT _ _ _) = true => rewrite FOin_tm_opT_eq in H
  | FOin_tm _ FOZero = true => discriminate H
  | FOin_tm ?x (FOVar _) = true => cbn [FOin_tm] in H; apply Nat.eqb_eq in H; subst x
  | Nat.eqb _ ?x = true => apply Nat.eqb_eq in H; subst x
  | false = true => discriminate H
  end;
  try (match goal with E : Nat.eqb ?a ?a = false |- _ =>
         rewrite Nat.eqb_refl in E; discriminate E end).

Definition ballQ (v y : nat) (D : FOFormula) : FOFormula :=
  FOForall v (FOImplF (FOltv v (FOVar y)) D).

Lemma free_ball_hD : forall v Tt h D V w,
  (forall x, FOfree_in x D = true -> x <> v -> 1100 <= h x < V) ->
  (w < 1000 \/ V <= w) -> FOin_tm w Tt = false ->
  FOfree_in w (FOForall v (FOImplF (FOltv v Tt) (hsub_f (h_hide v h) D))) = false.
Proof.
  intros v Tt h D V w Hh Hw HT. cbn [FOfree_in].
  destruct (Nat.eqb_spec v w) as [_|Hvw]; [reflexivity|].
  apply Bool.orb_false_iff. split; [apply FOfree_in_ltv; [lia | exact HT]|].
  destruct (FOfree_in w (hsub_f (h_hide v h) D)) eqn:E; [|reflexivity].
  destruct (FOfree_in_hsub D (h_hide v h) w E) as [x [Hx Ex]]. unfold h_hide in Ex.
  destruct (Nat.eqb_spec x v) as [->|Hxv]; [congruence|].
  specialize (Hh x Hx Hxv). lia.
Qed.

Lemma BALL_base : forall n k W v D V G h rho env y,
  Inv n V G h rho env (fun x => FOfree_in x D = true /\ x <> v) ->
  FOvars_max D < W -> S v < W -> W <= V -> W <= y ->
  PRI n (FOPrCores k) (FOu0 k) (V + 2)
    ((G ++ [FONUMR FOZero (FOVar (V + 1))]) ++
       [FOForall v (FOImplF (FOltv v FOZero) (hsub_f (h_hide v h) D))])
    (cpat_f (rho_sub (Some y) (length env) rho) (ballQ v y D)) (env ++ [FOVar (V + 1)]).
Proof.
  intros n k W v D V G h rho env y HI HWD HWv HWV HWy.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hhr : forall x, FOfree_in x D = true -> x <> v -> 1100 <= h x < V)
    by (intros x Hx Hxv; exact (HOK_range n G V h rho env x (Hh x (conj Hx Hxv)))).
  lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
    assert (HG1 : FOctx_avoid G1 0 1000);
    [| assert (HG1V : forall w, V + 2 <= w -> FOfree_ctx w G1)]
  end.
  { intros w ? ?. apply FOfree_ctx_app_inv; [free_ctx|].
    apply FOfree_ctx_cons; [apply (free_ball_hD v FOZero h D V w Hhr); [lia | reflexivity]|].
    apply FOfree_ctx_nil. }
  { intros w ?. apply FOfree_ctx_app_inv; [free_ctx|].
    apply FOfree_ctx_cons; [apply (free_ball_hD v FOZero h D V w Hhr); [lia | reflexivity]|].
    apply FOfree_ctx_nil. }
  pose proof (Inv_move n V (V + 2) G _ h rho env _ HI
                ltac:(intros X HX; apply in_or_app; left; apply in_or_app; left; exact HX)
                ltac:(lia) HG1 HG1V) as HI1.
  lazymatch type of HG1 with FOctx_avoid ?G1 _ _ =>
    assert (N0 : FOPrH n G1 (FONUMR FOZero (FOVar (V + 1)))) by wk_in
  end.
  assert (Hxy : forall x, FOfree_in x D = true /\ x <> v -> x <> y).
  { intros x [Hx _] E. subst x. pose proof (fv_small D y Hx). lia. }
  pose proof (Inv_slot n (V + 2) _ h rho env _ FOZero (FOVar (V + 1)) y HI1 N0
                ltac:(avoid_tms) ltac:(intros s [<-|[]] w Hw; apply FOin_tm_var_ne; lia) Hxy)
    as HI2.
  destruct HI2 as [HV2 [HG02 [HGV2 [HE2 [Henv2 [Hr2 Hh2]]]]]].
  pose proof (PRI_teval FOZero n k (V + 2) _ h _ _ y (length env) HV2 HG02 HGV2 HE2 Henv2 Hr2
                ltac:(intros x Hx; discriminate Hx) eq_refl (rho_sub_eq y (length env) rho)
                ltac:(rewrite length_app; cbn [length]; lia)
                ltac:(rewrite nth_snoc_len; exact N0)) as T0.
  pose proof (PRI_thm_open n k (V + 2) _ _ (rho_sub (Some y) (length env) rho) _
                (FOPr_ball_base v y D ltac:(lia) ltac:(lia)) HE2) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ exists (length env); split;
                              [apply rho_sub_eq | rewrite length_app; cbn [length]; lia]
                            | assert (Hxv : x <> v)
                                by (intro Exv; subst x; rewrite Nat.eqb_refl in *; discriminate);
                              destruct (Hh2 x (conj Hx Hxv)) as [i [Hxi [Hi _]]];
                              exists i; split; assumption ])).
  exact (PRI_mp n _ _ (V + 2) _ _ _ _ _ HE2 Hr2 T T0).
Qed.

Lemma free_PhiBall : forall cores u0 B0 m v hD env P Nt w,
  FOfree_in w (FOForall v (FOImplF (FOltv v Nt) hD)) = false -> w <> m -> 2 <= B0 ->
  FOtms_avoid [Nt] w (S w) -> FOtms_avoid [Nt] 13 18 -> FOtms_avoid [Nt] 802 805 ->
  18 <= m -> m < 802 \/ 805 <= m -> FOtms_avoid env w (S w) ->
  FOfree_in w (PhiBall cores u0 B0 m v hD env P Nt) = false.
Proof.
  intros cores u0 B0 m v hD env P Nt w HY Hwm HB HNt1 HNt2 HNt3 Hm1 Hm2 Henv.
  unfold PhiBall. cbn [FOfree_in]. rewrite (proj2 (Nat.eqb_neq m w) ltac:(lia)).
  apply Bool.orb_false_iff. split; [apply FOfree_in_NUMR_all; avoid_tms|].
  apply Bool.orb_false_iff. split; [exact HY|].
  apply FOfree_in_PRIf; [exact HB | avoid_tms].
Qed.

Lemma fv_Ds : forall x v y D, FOfree_in x (FOsubst_f v (FOVar y) D) = true ->
  (FOfree_in x D = true /\ x <> v) \/ x = y.
Proof.
  intros x v y D H. destruct (FOfree_in_subst_gen D x v (FOVar y) H) as [[H1 H2]|H1].
  - left. split; assumption.
  - right. cbn [FOin_tm] in H1. apply Nat.eqb_eq in H1. symmetry. exact H1.
Qed.

Lemma BALL_step : forall n k W v D V G h rho env y,
  FOvars_max D < W -> S v < W -> W <= V -> W <= y ->
  (forall V' G' h' rho' env', Inv n V' G' h' rho' env' (fun x => FOfree_in x D = true) ->
     (forall x, FOfree_in x D = true -> W <= h' x) ->
     FOPrH n G' (hsub_f h' D) -> PRI n (FOPrCores k) (FOu0 k) V' G' (cpat_f rho' D) env') ->
  Inv n V G h rho env (fun x => FOfree_in x D = true /\ x <> v) ->
  (forall x, FOfree_in x D = true -> x <> v -> W <= h x) ->
  PRI n (FOPrCores k) (FOu0 k) (V + 2)
    (((G ++ [PhiBall (FOPrCores k) (FOu0 k) (V + 2) (V + 1) v (hsub_f (h_hide v h) D) env
               (cpat_f (rho_sub (Some y) (length env) rho) (ballQ v y D)) (FOVar V)])
       ++ [FONUMR (FOSucc (FOVar V)) (FOVar (V + 1))])
       ++ [FOForall v (FOImplF (FOltv v (FOSucc (FOVar V))) (hsub_f (h_hide v h) D))])
    (cpat_f (rho_sub (Some y) (length env) rho) (ballQ v y D)) (env ++ [FOVar (V + 1)]).
Proof.
  intros n k W v D V G h rho env y HWD HWv HWV HWy IHD HI Hhw.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hhr : forall x, FOfree_in x D = true -> x <> v -> 1100 <= h x < V)
    by (intros x Hx Hxv; exact (HOK_range n G V h rho env x (Hh x (conj Hx Hxv)))).
  assert (HyD : FOvars_max D < y) by lia.
  assert (Hxy : forall x, FOfree_in x D = true -> x <> y).
  { intros x Hx E. subst x. pose proof (fv_small D y Hx). lia. }
  assert (HhD : forall w, (w < 1000 \/ V <= w) -> w <> v ->
            FOfree_in w (hsub_f (h_hide v h) D) = false).
  { intros w Hw Hwv. destruct (FOfree_in w (hsub_f (h_hide v h) D)) eqn:E; [|reflexivity].
    destruct (FOfree_in_hsub D (h_hide v h) w E) as [x [Hx Ex]]. unfold h_hide in Ex.
    destruct (Nat.eqb_spec x v) as [->|Hxv]; [congruence|]. specialize (Hhr x Hx Hxv). lia. }
  set (P := cpat_f (rho_sub (Some y) (length env) rho) (ballQ v y D)).
  set (hD := hsub_f (h_hide v h) D).
  assert (HPsp : forall w, V + 2 + cpat_span P < w -> V + 2 + cpat_span P < w) by (intros; lia).
  lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
    assert (HG1 : FOctx_avoid G1 0 1000);
    [| assert (HG1V : forall w, V + 2 <= w -> FOfree_ctx w G1)]
  end.
  { intros w ? ?. apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv|]|].
    - apply HG0; lia.
    - apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      apply free_PhiBall; try (avoid_tms || lia).
      apply (free_ball_hD v (FOVar V) h D V w Hhr); [lia | apply FOin_tm_var_ne; lia].
    - free_ctx.
    - apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      apply (free_ball_hD v (FOSucc (FOVar V)) h D V w Hhr); [lia | fr_tm]. }
  { intros w ?. apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv|]|].
    - apply HGV; lia.
    - apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      apply free_PhiBall; try (avoid_tms || lia).
      apply (free_ball_hD v (FOVar V) h D V w Hhr); [lia | apply FOin_tm_var_ne; lia].
    - free_ctx.
    - apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      apply (free_ball_hD v (FOSucc (FOVar V)) h D V w Hhr); [lia | fr_tm]. }
  lazymatch type of HG1 with FOctx_avoid ?G1 _ _ =>
    assert (HN1 : FOPrH n G1 (FONUMR (FOSucc (FOVar V)) (FOVar (V + 1)))) by wk_in
  end.
  refine (PRI_numr_invS n _ _ (V + 2) (V + 2 + cpat_span P + 1) _ P _ (FOVar V) (FOVar (V + 1))
            HN1 _ _ _ _ _ _); [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
  intros w Hw HR.
  lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
    assert (HPhi2 : FOPrH n G2 (PhiBall (FOPrCores k) (FOu0 k) (V + 2) (V + 1) v hD env P
                                  (FOVar V))) by wk_in;
    assert (HS2 : FOPrH n G2 (FOForall v (FOImplF (FOltv v (FOSucc (FOVar V))) hD))) by wk_in;
    assert (Cw : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar w) (FOVar (V + 1)))) by wk_in;
    assert (Nw : FOPrH n G2 (FONUMR (FOVar V) (FOVar w))) by wk_in;
    assert (Hinc2 : forall X, In X G -> In X G2)
      by (intros X HX; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left;
          apply in_or_app; left; exact HX);
    assert (HG2 : FOctx_avoid G2 0 1000)
      by (intros w' ? ?; apply FOfree_ctx_app_inv; [apply HG1; lia | free_ctx]);
    assert (HG2V : forall w', S w <= w' -> FOfree_ctx w' G2)
      by (intros w' ?; apply FOfree_ctx_app_inv; [apply HG1V; lia | free_ctx])
  end.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_thm _ _ _ (FOPr_ball_mono n v (FOVar V) hD
                ltac:(apply FOin_tm_var_ne; lia))) HS2) as Hmono.
  pose proof (PhiBall_inst n _ _ _ (V + 2) (V + 1) v hD env P (FOVar V) (FOVar w) HPhi2
                ltac:(lia) ltac:(lia) ltac:(apply FOin_tm_var_ne; lia)
                ltac:(apply HhD; lia) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(lia) ltac:(lia)) as IH.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ IH Nw) Hmono) as IHf.
  pose proof (PRIf_to_PRI n _ _ (S w) _ (env ++ [FOVar w]) P (V + 2) IHf ltac:(lia)
                ltac:(avoid_tms) ltac:(lia) ltac:(avoid_tms) ltac:(above_tac)) as IHP.
  lazymatch type of HG2 with FOctx_avoid ?G2 _ _ =>
    assert (HDN : FOPrH n G2 (hsub_f (h_upd v V h) D))
  end.
  { apply (FOPrH_inst n _ v (FOVar V)) in HS2;
      [| apply FOsubst_ok_impl;
         [apply FOsubst_ok_ltv; apply FOin_tm_var_ne; lia
         | apply (hsub_f_ok D (h_hide v h) v (FOVar V) W HWD);
           intros w' Hw'; cbn [FOin_tm] in Hw'; apply Nat.eqb_eq in Hw'; lia]].
    rewrite FOsubst_f_impl, FOsubst_f_ltv_self in HS2 by fr_tm.
    unfold hD in HS2. rewrite hsub_f_inst in HS2.
    - exact (FOPrH_mp _ _ _ _ HS2 (FOPrH_thm _ _ _ (FOPr_ltv_self n v (FOVar V)
                                                     ltac:(apply FOin_tm_var_ne; lia)))).
    - intros z Hz Hz'. pose proof (Hhw z Hz' Hz). lia. }
  lazymatch type of HG2 with FOctx_avoid ?G2 _ _ =>
    assert (HI4 : Inv n (S w) G2 (h_upd v V h) (rho_sub (Some v) (length env)
                                                  (rho_sub (Some y) (length env) rho))
                    (env ++ [FOVar w]) (fun x => FOfree_in x D = true))
  end.
  { pose proof (Inv_move n V (S w) G _ h rho env _ HI Hinc2 ltac:(lia) HG2 HG2V) as HIm.
    destruct HIm as [HVm [HG0m [HGVm [HEm [Henvm [Hrm Hhm]]]]]].
    split; [exact HVm|]. split; [exact HG0m|]. split; [exact HGVm|].
    split; [apply (EnvOK_snoc n (S w) _ env (FOVar w) (FOVar V) HEm Nw); [avoid_tms
             | intros w' Hw'; apply FOin_tm_var_ne; lia]|].
    split; [avoid_tms|]. split.
    - intros z0 i Hz0. rewrite length_app. cbn [length]. unfold rho_sub in Hz0.
      destruct (Nat.eqb z0 v); [injection Hz0 as <-; lia|].
      destruct (Nat.eqb z0 y); [injection Hz0 as <-; lia | specialize (Hrm z0 i Hz0); lia].
    - intros x Hx. destruct (Nat.eqb_spec x v) as [->|Hxv].
      + exists (length env). rewrite rho_sub_eq. split; [reflexivity|].
        split; [rewrite length_app; cbn [length]; lia|].
        unfold h_upd. rewrite Nat.eqb_refl, nth_snoc_len. split; [exact Nw | lia].
      + destruct (Hhm x (conj Hx Hxv)) as [i [Hxi [Hi [HNx [H1 H2]]]]].
        exists i. rewrite (rho_sub_ne v (length env) _ x Hxv),
          (rho_sub_ne y (length env) rho x (Hxy x Hx)).
        unfold h_upd. rewrite (proj2 (Nat.eqb_neq x v) Hxv).
        split; [exact Hxi|]. split; [rewrite length_app; lia|].
        rewrite nth_app_lt by exact Hi. split; [exact HNx | lia]. }
  pose proof (IHD (S w) _ _ _ _ HI4
                ltac:(intros x Hx; unfold h_upd; destruct (Nat.eqb_spec x v);
                      [lia | exact (Hhw x Hx n0)]) HDN) as TD.
  rewrite <- (cpat_f_subst_var D v y (rho_sub (Some y) (length env) rho) (length env) HyD
                (rho_sub_eq y (length env) rho)) in TD.
  pose proof (Inv_slot n (S w) _ h rho env _ (FOVar V) (FOVar w) y
                (Inv_move n V (S w) G _ h rho env _ HI Hinc2 ltac:(lia) HG2 HG2V) Nw
                ltac:(avoid_tms) ltac:(intros s [<-|[]] w' Hw'; apply FOin_tm_var_ne; lia)
                ltac:(intros x [Hx _]; exact (Hxy x Hx))) as HI5.
  destruct HI5 as [HV5 [HG05 [HGV5 [HE5 [Henv5 [Hr5 Hh5]]]]]].
  pose proof (PRI_thm_open n k (S w) _ _ (rho_sub (Some y) (length env) rho) _
                (FOPr_ball_step v y D HyD ltac:(lia)) HE5) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ exists (length env); split;
                              [apply rho_sub_eq | rewrite length_app; cbn [length]; lia]
                            | destruct (fv_Ds x v y D Hx) as [[Hx1 Hx2]|Hx1];
                              [ destruct (Hh5 x (conj Hx1 Hx2)) as [i [Hxi [Hi _]]];
                                exists i; split; assumption
                              | subst x; exists (length env); split;
                                [apply rho_sub_eq | rewrite length_app; cbn [length]; lia] ]
                            | assert (Hxv : x <> v)
                                by (intro Exv; subst x; rewrite Nat.eqb_refl in *; discriminate);
                              destruct (Hh5 x (conj Hx Hxv)) as [i [Hxi [Hi _]]];
                              exists i; split; assumption ])).
  pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE5 Hr5 T TD) as T1.
  pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE5 Hr5 T1 IHP) as T2.
  refine (PRI_conv n _ _ (S w) _ _ _ _ _ _ _ _ _ T2); [| above_tac | avoid_tms | lia].
  intros G' Hinc. unfold P, ballQ.
  apply (CPrel_ball_succ n G' v y D (rho_sub (Some y) (length env) rho) env (FOVar w)
           (FOVar (V + 1))); [| lia | lia | apply rho_sub_eq | exact (FOPrH_weaken n _ G' _ Hinc Cw)].
  intros z Hz Hzv. destruct (Hh z (conj Hz Hzv)) as [i [Hzi [Hi _]]]. exists i.
  rewrite (rho_sub_ne y (length env) rho z (Hxy z Hz)). split; assumption.
Qed.

(** ** The bounded universal closure. *)

Lemma BALL_GEN : forall n k W v D,
  FOvars_max D < W -> S v < W ->
  (forall V' G' h' rho' env', Inv n V' G' h' rho' env' (fun x => FOfree_in x D = true) ->
     (forall x, FOfree_in x D = true -> W <= h' x) ->
     FOPrH n G' (hsub_f h' D) -> PRI n (FOPrCores k) (FOu0 k) V' G' (cpat_f rho' D) env') ->
  forall V G h rho env T mu y,
  W <= V -> W <= y ->
  Inv n V G h rho env (fun x => FOfree_in x D = true /\ x <> v) ->
  (forall x, FOfree_in x D = true -> x <> v -> W <= h x) ->
  FOtms_avoid [T; mu] 0 1100 ->
  (forall s, In s [T; mu] -> forall w, V <= w -> FOin_tm w s = false) ->
  (forall w, w < W -> FOin_tm w T = false) ->
  FOPrH n G (FONUMR T mu) ->
  FOPrH n G (FOForall v (FOImplF (FOltv v T) (hsub_f (h_hide v h) D))) ->
  PRI n (FOPrCores k) (FOu0 k) V G
    (cpat_f (rho_sub (Some y) (length env) rho) (ballQ v y D)) (env ++ [mu]).
Proof.
  intros n k W v D HWD HWv IHD V G h rho env T mu y HWV HWy HI Hhw HTm0 HTmv HTW HN HB.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hhr : forall x, FOfree_in x D = true -> x <> v -> 1100 <= h x < V)
    by (intros x Hx Hxv; exact (HOK_range n G V h rho env x (Hh x (conj Hx Hxv)))).
  assert (HhD : forall w, (w < 1000 \/ V <= w) -> w <> v ->
            FOfree_in w (hsub_f (h_hide v h) D) = false).
  { intros w Hw Hwv. destruct (FOfree_in w (hsub_f (h_hide v h) D)) eqn:E; [|reflexivity].
    destruct (FOfree_in_hsub D (h_hide v h) w E) as [x [Hx Ex]]. unfold h_hide in Ex.
    destruct (Nat.eqb_spec x v) as [->|Hxv]; [congruence|]. specialize (Hhr x Hx Hxv). lia. }
  set (P := cpat_f (rho_sub (Some y) (length env) rho) (ballQ v y D)).
  set (hD := hsub_f (h_hide v h) D).
  assert (HPhi : FOPrH n G (FOForall V (PhiBall (FOPrCores k) (FOu0 k) (V + 2) (V + 1) v hD env P
                                          (FOVar V)))).
  { apply FOPrH_ind; [apply HGV; lia | |].
    - rewrite PhiBall_subst by first [lia | avoid_tms | apply HhD; lia].
      unfold PhiBall.
      apply FOPrH_all_intro; [apply HGV; lia|]. apply FOPrH_intro. apply FOPrH_intro.
      apply (PRI_to_PRIf n _ _ (V + 2) _ (env ++ [FOVar (V + 1)]) P (V + 2)
               (BALL_base n k W v D V G h rho env y HI HWD HWv HWV HWy)); [lia | lia | | | avoid_tms
                                                                    | above_tac].
      + intros w ? ?. apply FOfree_ctx_app_inv; [free_ctx|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        apply (free_ball_hD v FOZero h D V w Hhr); [lia | reflexivity].
      + intros w ?. apply FOfree_ctx_app_inv; [free_ctx|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        apply (free_ball_hD v FOZero h D V w Hhr); [lia | reflexivity].
    - rewrite PhiBall_subst by first [lia | avoid_tms | apply HhD; lia].
      unfold PhiBall at 2.
      apply FOPrH_all_intro.
      { apply FOfree_ctx_app_inv; [apply HGV; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. unfold PhiBall.
        apply FOfree_in_all_self. }
      apply FOPrH_intro. apply FOPrH_intro.
      apply (PRI_to_PRIf n _ _ (V + 2) _ (env ++ [FOVar (V + 1)]) P (V + 2)
               (BALL_step n k W v D V G h rho env y HWD HWv HWV HWy IHD HI Hhw));
        [lia | lia | | | avoid_tms | above_tac].
      + intros w ? ?.
        apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv|]|].
        * apply HG0; lia.
        * apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
          apply free_PhiBall; try (avoid_tms || lia).
          apply (free_ball_hD v (FOVar V) h D V w Hhr); [lia | apply FOin_tm_var_ne; lia].
        * free_ctx.
        * apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
          apply (free_ball_hD v (FOSucc (FOVar V)) h D V w Hhr); [lia | fr_tm].
      + intros w ?.
        apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv|]|].
        * apply HGV; lia.
        * apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
          apply free_PhiBall; try (avoid_tms || lia).
          apply (free_ball_hD v (FOVar V) h D V w Hhr); [lia | apply FOin_tm_var_ne; lia].
        * free_ctx.
        * apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
          apply (free_ball_hD v (FOSucc (FOVar V)) h D V w Hhr); [lia | fr_tm]. }
  apply (FOPrH_inst n G V T) in HPhi;
    [| unfold PhiBall; apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_impl;
       [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl;
       [ apply FOsubst_ok_all; [apply HTW; lia|]; apply FOsubst_ok_impl;
         [apply FOsubst_ok_ltv; apply HTW; lia
         | apply FOsubst_ok_not_free; apply HhD; lia]
       | apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm] ]].
  rewrite PhiBall_subst in HPhi by first [lia | avoid_tms | apply HhD; lia].
  pose proof (PhiBall_inst n G _ _ (V + 2) (V + 1) v hD env P T mu HPhi ltac:(lia) ltac:(lia)
                ltac:(fr_tm) ltac:(apply HhD; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms) ltac:(lia) ltac:(lia)) as H1.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ H1 HN) HB) as H2.
  exact (PRIf_to_PRI n _ _ V G (env ++ [mu]) P (V + 2) H2 ltac:(lia) ltac:(avoid_tms) ltac:(lia)
           ltac:(avoid_tms) ltac:(above_tac)).
Qed.

(** ** A witness below the bound. *)

Lemma hsub_tm_upd_out : forall t h v N, FOin_tm v t = false ->
  hsub_tm (h_upd v N h) t = hsub_tm h t.
Proof.
  intros t h v N Hv. apply hsub_tm_ext. intros z Hz. unfold h_upd.
  destruct (Nat.eqb_spec z v) as [->|_]; [congruence | reflexivity].
Qed.

Lemma hsub_f_upd_out : forall A h v N, FOfree_in v A = false ->
  hsub_f (h_upd v N h) A = hsub_f h A.
Proof.
  intros A h v N Hv. apply hsub_f_ext. intros z Hz. unfold h_upd.
  destruct (Nat.eqb_spec z v) as [->|_]; [congruence | reflexivity].
Qed.

Lemma WITNESS : forall n k W v t A Ap C,
  FOin_tm (S v) t = false -> FOin_tm v t = false ->
  FOvars_max A < W -> S v < W -> FOmax_var_tm t < W ->
  (forall x, FOfree_in x Ap = true -> FOfree_in x A = true) ->
  (forall V' G' h' rho' env', Inv n V' G' h' rho' env' (fun x => FOfree_in x A = true) ->
     (forall x, FOfree_in x A = true -> W <= h' x) ->
     FOPrH n G' (hsub_f h' Ap) -> PRI n (FOPrCores k) (FOu0 k) V' G' (cpat_f rho' Ap) env') ->
  FOProvesTn 0 (FOImplF (FOEq (FOPlus (FOVar v) (FOSucc (FOVar W))) t) (FOImplF Ap C)) ->
  (forall x, FOfree_in x C = true -> FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) ->
  forall V G h rho env w0,
  Inv n V G h rho env (fun x => FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) ->
  (forall x, FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v) -> W <= h x) ->
  W <= w0 -> 1100 <= w0 -> w0 < V ->
  FOPrH n G (FOExists (S v) (FOEq (FOPlus (FOVar w0) (FOSucc (FOVar (S v)))) (hsub_tm h t))) ->
  FOPrH n G (hsub_f (h_upd v w0 h) Ap) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho C) env.
Proof.
  intros n k W v t A Ap C HSvt Hvt HWA HWv HWt HApA IHAp HTh HC V G h rho env w0 HI Hhw
    HWw0 Hw01 Hw02 HL HAp.
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hht : forall x, FOin_tm x t = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; left; exact Hx).
  destruct (hsub_facts t n G V h rho env Hht) as [Ht0 Htv].
  assert (HtW : forall w, w < W -> FOin_tm w (hsub_tm h t) = false).
  { intros w Hw. destruct (FOin_tm w (hsub_tm h t)) eqn:E; [|reflexivity].
    destruct (FOin_tm_hsub t h w E) as [x [Hx <-]]. specialize (Hhw x (or_introl Hx)). lia. }
  refine (PRI_exe n _ _ V W G _ env (S v)
            (FOEq (FOPlus (FOVar w0) (FOSucc (FOVar (S v)))) (hsub_tm h t)) HL _ _ _ _ _ _ _);
    [lia | avoid_tms | above_tac | | | |].
  { intros w Hw Hwv. cbn [FOfree_in FOin_tm]. apply Bool.orb_false_iff. split.
    - apply Bool.orb_false_iff. split; apply Nat.eqb_neq; lia.
    - fr_tm. }
  { intros w Hw Hwv. cbn [FOfree_in FOin_tm]. apply Bool.orb_false_iff. split.
    - apply Bool.orb_false_iff. split; apply Nat.eqb_neq; lia.
    - apply Htv; [left; reflexivity | lia]. }
  { intros w Hw HWw. reflexivity. }
  intros u0 Hu0 HWu0.
  rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_succ, FOsubst_t_var_eq',
    FOsubst_t_var_ne by lia.
  rewrite (FOsubst_t_not_in (hsub_tm h t) (S v) (FOVar u0)) by (apply HtW; lia).
  refine (PRI_numr_ex n _ _ (S u0) 0 _ _ env (FOVar w0) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; apply FOin_tm_var_ne; lia | avoid_tms | above_tac |].
  intros w1 Hw1 _.
  refine (PRI_numr_ex n _ _ (S w1) 0 _ _ env (FOVar u0) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; apply FOin_tm_var_ne; lia | avoid_tms | above_tac |].
  intros w2 Hw2 _.
  lazymatch goal with |- PRI _ _ _ _ ?G5 _ _ =>
    assert (HG5 : FOctx_avoid G5 0 1000)
      by (intros w' ? ?; apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv;
          [apply FOfree_ctx_app_inv; [apply HG0; lia|]|]|]; free_ctx);
    assert (HG5V : forall w', S w2 <= w' -> FOfree_ctx w' G5)
      by (intros w' ?; apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv;
          [apply FOfree_ctx_app_inv; [apply HGV; lia|]|]|]; free_ctx);
    assert (Hinc5 : forall X, In X G -> In X G5)
      by (intros X HX; apply in_or_app; left; apply in_or_app; left; apply in_or_app; left;
          exact HX);
    assert (E5 : FOPrH n G5 (FOEq (FOPlus (FOVar w0) (FOSucc (FOVar u0))) (hsub_tm h t)))
      by wk_in;
    assert (N1 : FOPrH n G5 (FONUMR (FOVar w0) (FOVar w1))) by wk_in;
    assert (N2 : FOPrH n G5 (FONUMR (FOVar u0) (FOVar w2))) by wk_in;
    assert (HAp5 : FOPrH n G5 (hsub_f (h_upd v w0 h) Ap))
      by exact (FOPrH_weaken n G G5 _ Hinc5 HAp)
  end.
  pose proof (Inv_move n V (S w2) G _ h rho env _ HI Hinc5 ltac:(lia) HG5 HG5V) as HIm.
  pose proof (Inv_weaken n (S w2) _ h rho env _
                (fun x => ((FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) \/ x = v)
                          /\ x <> v) HIm
                ltac:(intros x Hx; cbn beta in Hx; destruct Hx as [[Hx|Hx] Hxv];
                      [exact Hx | exfalso; exact (Hxv Hx)])) as HI0'.
  pose proof (Inv_holder n (S w2) _ h rho env
                (fun x => (FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) \/ x = v)
                v w0 (FOVar w1) HI0' N1 ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(intros s [<-|[]] w Hw; apply FOin_tm_var_ne; lia)) as HI1.
  pose proof (Inv_weaken n (S w2) _ _ _ _ _
                (fun x => (((FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) \/ x = v)
                           \/ x = W) /\ x <> W) HI1
                ltac:(intros x Hx; cbn beta in Hx; destruct Hx as [[Hx|Hx] HxW];
                      [exact Hx | exfalso; exact (HxW Hx)])) as HI1'.
  pose proof (Inv_holder n (S w2) _ (h_upd v w0 h) _ _
                (fun x => ((FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) \/ x = v)
                          \/ x = W)
                W u0 (FOVar w2) HI1' N2 ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(intros s [<-|[]] w Hw; apply FOin_tm_var_ne; lia)) as HI2.
  assert (HWx : forall x, FOfree_in x A = true -> x < W)
    by (intros x Hx; pose proof (fv_small A x Hx); lia).
  assert (Htx : forall x, FOin_tm x t = true -> x < W).
  { intros x Hx. destruct (Nat.le_gt_cases W x) as [Hle|Hlt]; [|exact Hlt].
    rewrite FOin_tm_above in Hx by lia. discriminate. }
  lazymatch type of HG5 with FOctx_avoid ?G5 _ _ =>
    assert (HIE : Inv n (S w2) G5 (h_upd W u0 (h_upd v w0 h))
                    (rho_sub (Some W) (length (env ++ [FOVar w1]))
                       (rho_sub (Some v) (length env) rho))
                    ((env ++ [FOVar w1]) ++ [FOVar w2])
                    (fun x => FOfree_in x (FOEq (FOPlus (FOVar v) (FOSucc (FOVar W))) t) = true))
      by (apply (Inv_weaken n (S w2) _ _ _ _ _ _ HI2); intros x Hx; cbn beta in Hx |- *;
          fv_cases Hx; [left; right; reflexivity | right; reflexivity | left; left; left; exact Hx]);
    assert (HIA : Inv n (S w2) G5 (h_upd W u0 (h_upd v w0 h))
                    (rho_sub (Some W) (length (env ++ [FOVar w1]))
                       (rho_sub (Some v) (length env) rho))
                    ((env ++ [FOVar w1]) ++ [FOVar w2]) (fun x => FOfree_in x A = true))
      by (apply (Inv_weaken n (S w2) _ _ _ _ _ _ HI2); intros x Hx; cbn beta in Hx |- *; left;
          destruct (Nat.eqb_spec x v) as [->|Hxv]; [right; reflexivity|];
          left; right; split; assumption)
  end.
  pose proof (PRI_eq_pos n k (FOPlus (FOVar v) (FOSucc (FOVar W))) t (S w2) _ _ _ _ HIE) as TE.
  assert (Hh5e : hsub_tm (h_upd W u0 (h_upd v w0 h)) (FOPlus (FOVar v) (FOSucc (FOVar W))) =
                 FOPlus (FOVar w0) (FOSucc (FOVar u0))).
  { cbn [hsub_tm]. unfold h_upd. rewrite (proj2 (Nat.eqb_neq v W) ltac:(lia)), !Nat.eqb_refl.
    reflexivity. }
  rewrite Hh5e in TE.
  rewrite (hsub_tm_upd_out t _ W u0) in TE by (apply FOin_tm_above; lia).
  rewrite (hsub_tm_upd_out t h v w0 Hvt) in TE.
  specialize (TE E5).
  assert (HWAp : FOfree_in W Ap = false).
  { destruct (FOfree_in W Ap) eqn:E; [|reflexivity]. specialize (HWx W (HApA W E)). lia. }
  pose proof (IHAp (S w2) _ _ _ _ HIA
                ltac:(intros x Hx; unfold h_upd;
                      destruct (Nat.eqb_spec x W) as [->|_]; [specialize (HWx W Hx); lia|];
                      destruct (Nat.eqb_spec x v) as [->|Hxv]; [exact HWw0|];
                      apply Hhw; right; split; assumption)
                ltac:(rewrite (hsub_f_upd_out Ap _ W u0 HWAp); exact HAp5)) as TA.
  pose proof HIE as [_ [_ [_ [HE5 [_ [Hr5 Hh5]]]]]].
  pose proof HI2 as [_ [_ [_ [_ [_ [_ Hh2]]]]]].
  pose proof (PRI_thm_open n k (S w2) _ _ (rho_sub (Some W) (length (env ++ [FOVar w1]))
                (rho_sub (Some v) (length env) rho)) _ HTh HE5) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ destruct (Hh2 v ltac:(left; right; reflexivity))
                                as [i [Hxi [Hi _]]]; exists i; split; assumption
                            | destruct (Hh2 W ltac:(right; reflexivity))
                                as [i [Hxi [Hi _]]]; exists i; split; assumption
                            | destruct (Hh2 x ltac:(left; left; left; exact Hx))
                                as [i [Hxi [Hi _]]]; exists i; split; assumption
                            | destruct (Nat.eqb_spec x v) as [->|Hxv];
                              [ destruct (Hh2 v ltac:(left; right; reflexivity))
                                  as [i [Hxi [Hi _]]]; exists i; split; assumption
                              | first [ destruct (Hh2 x ltac:(left; left; right; split;
                                          [apply HApA; exact Hx | exact Hxv]))
                                          as [i [Hxi [Hi _]]]; exists i; split; assumption
                                      | destruct (HC x Hx) as [Hc|[Hc Hcv]];
                                        [ destruct (Hh2 x ltac:(left; left; left; exact Hc))
                                            as [i [Hxi [Hi _]]]; exists i; split; assumption
                                        | destruct (Hh2 x ltac:(left; left; right; split;
                                            assumption)) as [i [Hxi [Hi _]]];
                                          exists i; split; assumption ] ] ] ])).
  pose proof (PRI_mp n _ _ (S w2) _ _ _ _ _ HE5 Hr5 T TE) as T1.
  pose proof (PRI_mp n _ _ (S w2) _ _ _ _ _ HE5 Hr5 T1 TA) as T2.
  refine (PRI_reslot n _ _ (S w2) _ _ _ rho _ env _ _ _ _ T2); [| above_tac | avoid_tms | lia].
  intros x Hx. unfold SlotAgree.
  assert (HxS : FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) by exact (HC x Hx).
  assert (Hxv : x <> v) by (destruct HxS as [Hc|[_ Hc]]; [intro; subst x; congruence | exact Hc]).
  assert (HxW : x <> W) by (destruct HxS as [Hc|[Hc _]];
                              [pose proof (Htx x Hc); lia | pose proof (HWx x Hc); lia]).
  rewrite (rho_sub_ne W _ _ x HxW), (rho_sub_ne v _ rho x Hxv).
  destruct (Hh x HxS) as [i [Hxi [Hi _]]]. rewrite Hxi.
  rewrite (nth_app_lt (env ++ [FOVar w1]) [FOVar w2] i) by (rewrite length_app; lia).
  rewrite (nth_app_lt env [FOVar w1] i Hi). apply FOPrH_refl.
Qed.

(** ** Bounded quantifiers in the main induction. *)

Lemma fv_ltv : forall x v t, FOin_tm (S v) t = false ->
  FOfree_in x (FOltv v t) = (Nat.eqb v x || FOin_tm x t)%bool.
Proof.
  intros x v t HSv. unfold FOltv. cbn [FOfree_in FOin_tm].
  destruct (Nat.eqb_spec (S v) x) as [<-|HSvx].
  - rewrite HSv, (proj2 (Nat.eqb_neq v (S v)) ltac:(lia)). reflexivity.
  - rewrite Bool.orb_false_r. reflexivity.
Qed.

Lemma fv_bq : forall v t A x, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  (FOfree_in x (FOForall v (FOImplF (FOltv v t) A)) = true <->
   FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) /\
  (FOfree_in x (FOExists v (FOAnd (FOltv v t) A)) = true <->
   FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)).
Proof.
  intros v t A x Hv HSv.
  assert (K : FOfree_in x (FOImplF (FOltv v t) A) = FOfree_in x (FOAnd (FOltv v t) A)).
  { unfold FOAnd, FONeg. cbn [FOfree_in]. rewrite !Bool.orb_false_r. reflexivity. }
  assert (M : forall X, (FOfree_in x X = FOfree_in x (FOImplF (FOltv v t) A)) ->
            (FOfree_in x (FOForall v X) = true <->
             FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) /\
            (FOfree_in x (FOExists v X) = true <->
             FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v))).
  { intros X HX. cbn [FOfree_in]. rewrite HX. cbn [FOfree_in]. rewrite (fv_ltv x v t HSv).
    destruct (Nat.eqb_spec v x) as [->|Hvx].
    - split; split; intros H; try discriminate;
        destruct H as [H|[_ H]]; try (rewrite Hv in H; discriminate); exfalso; exact (H eq_refl).
    - cbn [orb]. split; split; intros H.
      + apply Bool.orb_true_iff in H. destruct H as [H|H]; [left; exact H | right; split; [exact H | lia]].
      + apply Bool.orb_true_iff. destruct H as [H|[H _]]; [left; exact H | right; exact H].
      + apply Bool.orb_true_iff in H. destruct H as [H|H]; [left; exact H | right; split; [exact H | lia]].
      + apply Bool.orb_true_iff. destruct H as [H|[H _]]; [left; exact H | right; exact H]. }
  split.
  - exact (proj1 (M _ eq_refl)).
  - exact (proj2 (M _ (eq_sym K))).
Qed.

Lemma hsub_ball : forall h v t A, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  hsub_f h (FOForall v (FOImplF (FOltv v t) A)) =
  FOForall v (FOImplF (FOltv v (hsub_tm h t)) (hsub_f (h_hide v h) A)).
Proof. intros h v t A H1 H2. cbn [hsub_f]. rewrite hsub_ltv by assumption. reflexivity. Qed.

Lemma hsub_bex : forall h v t A, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  hsub_f h (FOExists v (FOAnd (FOltv v t) A)) =
  FOExists v (FOAnd (FOltv v (hsub_tm h t)) (hsub_f (h_hide v h) A)).
Proof.
  intros h v t A H1 H2. unfold FOAnd, FONeg. cbn [hsub_f]. rewrite hsub_ltv by assumption.
  reflexivity.
Qed.

Lemma bq_bounds : forall v t A W, FOvars_max (FOForall v (FOImplF (FOltv v t) A)) < W ->
  S v < W /\ FOvars_max A < W /\ FOmax_var_tm t < W.
Proof. intros v t A W H. unfold FOltv in H. cbn [FOvars_max FOmax_var_tm] in H. lia. Qed.

Lemma bq_bounds' : forall v t A W, FOvars_max (FOExists v (FOAnd (FOltv v t) A)) < W ->
  S v < W /\ FOvars_max A < W /\ FOmax_var_tm t < W.
Proof.
  intros v t A W H. unfold FOAnd, FONeg, FOltv in H. cbn [FOvars_max FOmax_var_tm] in H. lia.
Qed.

Lemma fv_neg : forall x A, FOfree_in x (FONeg A) = FOfree_in x A.
Proof. intros x A. unfold FONeg. cbn [FOfree_in]. apply Bool.orb_false_r. Qed.

Lemma hA_free : forall n G V h rho env v A w,
  (forall x, FOfree_in x A = true -> x <> v -> HOK n G V h rho env x) ->
  (w < 1000 \/ V <= w) -> w <> v -> FOfree_in w (hsub_f (h_hide v h) A) = false.
Proof.
  intros n G V h rho env v A w Hh Hw Hwv.
  destruct (FOfree_in w (hsub_f (h_hide v h) A)) eqn:E; [|reflexivity].
  destruct (FOfree_in_hsub A (h_hide v h) w E) as [x [Hx Ex]]. unfold h_hide in Ex.
  destruct (Nat.eqb_spec x v) as [->|Hxv]; [congruence|].
  pose proof (HOK_range n G V h rho env x (Hh x Hx Hxv)). lia.
Qed.

Lemma D0P_ball : forall n k W v t A, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  D0P n k W A -> D0P n k W (FOForall v (FOImplF (FOltv v t) A)).
Proof.
  intros n k W v t A Hvt HSvt IHA HW V G h rho env HI Hhw.
  destruct (bq_bounds v t A W HW) as [HWv [HWA HWt]].
  assert (HS : forall x, FOfree_in x (FOForall v (FOImplF (FOltv v t) A)) = true <->
               FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v))
    by (intros x; exact (proj1 (fv_bq v t A x Hvt HSvt))).
  pose proof (Inv_weaken n V G h rho env _
                (fun x => FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) HI
                ltac:(intros x Hx; apply HS; exact Hx)) as HI'.
  assert (Hhw' : forall x, FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v) -> W <= h x)
    by (intros x Hx; apply Hhw; apply HS; exact Hx).
  pose proof HI' as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hht : forall x, FOin_tm x t = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; left; exact Hx).
  assert (HhA : forall x, FOfree_in x A = true -> x <> v -> HOK n G V h rho env x)
    by (intros x Hx Hxv; apply Hh; right; split; assumption).
  destruct (hsub_facts t n G V h rho env Hht) as [Ht0 Htv].
  assert (HtW : forall w, w < W -> FOin_tm w (hsub_tm h t) = false).
  { intros w Hw. destruct (FOin_tm w (hsub_tm h t)) eqn:E; [|reflexivity].
    destruct (FOin_tm_hsub t h w E) as [x [Hx <-]]. specialize (Hhw' x (or_introl Hx)). lia. }
  assert (HWA' : FOfree_in W A = false) by (apply FOfree_in_above; lia).
  assert (HWt' : FOin_tm W t = false) by (apply FOin_tm_above; lia).
  rewrite !hsub_ball by assumption.
  split.
  - intros HB.
    refine (PRI_numr_ex n _ _ V W G _ env (hsub_tm h t) _ _ _ _ _ _);
      [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
    intros w Hw HWw.
    lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
      assert (HG2 : FOctx_avoid G2 0 1000) by (intros w' ? ?; free_ctx);
      assert (HG2V : forall w', S w <= w' -> FOfree_ctx w' G2) by (intros w' ?; free_ctx);
      assert (Hinc2 : forall X, In X G -> In X G2)
        by (intros X HX; apply in_or_app; left; exact HX);
      assert (N2 : FOPrH n G2 (FONUMR (hsub_tm h t) (FOVar w))) by wk_in;
      assert (HB2 : FOPrH n G2 (FOForall v (FOImplF (FOltv v (hsub_tm h t))
                                              (hsub_f (h_hide v h) A)))) by wk HB
    end.
    pose proof (Inv_move n V (S w) G _ h rho env _ HI' Hinc2 ltac:(lia) HG2 HG2V) as HIm.
    pose proof (BALL_GEN n k W v A HWA HWv
                  (fun V' G' h' rho' env' HI0 Hh0 HD =>
                     proj1 (IHA HWA V' G' h' rho' env' HI0 Hh0) HD)
                  (S w) _ h rho env (hsub_tm h t) (FOVar w) W ltac:(lia) (le_n W)
                  (Inv_weaken n (S w) _ h rho env _ _ HIm ltac:(intros x Hx; right; exact Hx))
                  ltac:(intros x Hx Hxv; apply Hhw'; right; split; assumption)
                  ltac:(avoid_tms) ltac:(above_tac) HtW N2 HB2) as PB.
    unfold ballQ in PB.
    pose proof (Inv_slot n (S w) _ h rho env _ (hsub_tm h t) (FOVar w) W HIm N2 ltac:(avoid_tms)
                  ltac:(intros s [<-|[]] w' Hw'; apply FOin_tm_var_ne; lia)
                  ltac:(intros x [Hx|[Hx _]] E; subst x; congruence)) as HI3.
    destruct HI3 as [HV3 [HG03 [HGV3 [HE3 [Henv3 [Hr3 Hh3]]]]]].
    pose proof (PRI_teval t n k (S w) _ h _ _ W (length env) HV3 HG03 HGV3 HE3 Henv3 Hr3
                  ltac:(intros x Hx; apply Hh3; left; exact Hx) HWt'
                  (rho_sub_eq W (length env) rho) ltac:(rewrite length_app; cbn [length]; lia)
                  ltac:(rewrite nth_snoc_len; exact N2)) as TT.
    pose proof (PRI_thm_open n k (S w) _ _ (rho_sub (Some W) (length env) rho) _
                  (FOPr_ball_final v W t A Hvt HSvt HWA' ltac:(lia) ltac:(lia)) HE3) as T.
    specialize (T ltac:(intros x Hx; fv_cases Hx;
                        first [ exists (length env); split;
                                [apply rho_sub_eq | rewrite length_app; cbn [length]; lia]
                              | destruct (Hh3 x (or_introl Hx)) as [i [Hxi [Hi _]]];
                                exists i; split; assumption
                              | assert (Hxv : x <> v)
                                  by (intro Exv; subst x; rewrite Nat.eqb_refl in *; discriminate);
                                destruct (Hh3 x (or_intror (conj Hx Hxv))) as [i [Hxi [Hi _]]];
                                exists i; split; assumption ])).
    pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE3 Hr3 T TT) as T1.
    pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE3 Hr3 T1 PB) as T2.
    refine (PRI_reslot n _ _ (S w) _ _ _ rho _ env _ _ _ _ T2); [| above_tac | avoid_tms | lia].
    intros x Hx. unfold SlotAgree. apply HS in Hx.
    assert (HxW : x <> W) by (destruct Hx as [Hx|[Hx _]]; intro E; subst x; congruence).
    rewrite (rho_sub_ne W (length env) rho x HxW).
    destruct (Hh x Hx) as [i [Hxi [Hi _]]]. rewrite Hxi, (nth_app_lt env [FOVar w] i Hi).
    apply FOPrH_refl.
  - intros Hn.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_thm _ _ _ (FOPr_not_all n v
                  (FOImplF (FOltv v (hsub_tm h t)) (hsub_f (h_hide v h) A)))) Hn) as HX.
    refine (PRI_exe n _ _ V W G _ env v (FONeg (FOImplF (FOltv v (hsub_tm h t))
              (hsub_f (h_hide v h) A))) HX _ _ _ _ _ _ _); [lia | avoid_tms | above_tac | | | |].
    + intros w Hw Hwv. rewrite fv_neg. cbn [FOfree_in]. rewrite fv_ltv by (apply HtW; lia).
      rewrite (hA_free n G V h rho env v A w HhA ltac:(lia) Hwv).
      rewrite (proj2 (Nat.eqb_neq v w) ltac:(lia)). rewrite Bool.orb_false_r. cbn [orb]. fr_tm.
    + intros w Hw Hwv. rewrite fv_neg. cbn [FOfree_in]. rewrite fv_ltv by (apply HtW; lia).
      rewrite (hA_free n G V h rho env v A w HhA ltac:(lia) Hwv).
      rewrite (proj2 (Nat.eqb_neq v w) ltac:(lia)). rewrite Bool.orb_false_r. cbn [orb].
      apply Htv; [left; reflexivity | exact Hw].
    + intros w Hw HWw. apply FOsubst_ok_neg. apply FOsubst_ok_impl;
        [apply FOsubst_ok_ltv; apply FOin_tm_var_ne; lia
        | apply (hsub_f_ok A (h_hide v h) v (FOVar w) W HWA);
          intros w' Hw'; cbn [FOin_tm] in Hw'; apply Nat.eqb_eq in Hw'; lia].
    + intros w0 Hw0 HWw0.
      rewrite FOsubst_f_neg, FOsubst_f_impl, FOsubst_f_ltv_self by (apply HtW; lia).
      rewrite hsub_f_inst by (intros z Hz Hz'; pose proof (Hhw' z (or_intror (conj Hz' Hz))); lia).
      lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
        assert (HX2 : FOPrH n G2 (FONeg (FOImplF (FOExists (S v) (FOEq (FOPlus (FOVar w0)
                        (FOSucc (FOVar (S v)))) (hsub_tm h t))) (hsub_f (h_upd v w0 h) A))))
          by apply FOPrH_last;
        assert (Hinc2 : forall X, In X G -> In X G2)
          by (intros X HX'; apply in_or_app; left; exact HX');
        assert (HG2 : FOctx_avoid G2 0 1000);
        [| assert (HG2V : forall w', S w0 <= w' -> FOfree_ctx w' G2)]
      end.
      { intros w' ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        rewrite fv_neg. cbn [FOfree_in]. apply Bool.orb_false_iff. split.
        - destruct (Nat.eqb_spec (S v) w') as [_|HSw]; [reflexivity|].
          cbn [FOin_tm]. apply Bool.orb_false_iff.
          split; [apply Bool.orb_false_iff; split; apply Nat.eqb_neq; lia | fr_tm].
        - destruct (FOfree_in w' (hsub_f (h_upd v w0 h) A)) eqn:E; [|reflexivity].
          destruct (FOfree_in_hsub A (h_upd v w0 h) w' E) as [x [Hx Ex]]. unfold h_upd in Ex.
          destruct (Nat.eqb_spec x v) as [->|Hxv]; [lia|].
          pose proof (HOK_range n G V h rho env x (HhA x Hx Hxv)). lia. }
      { intros w' ?. apply FOfree_ctx_app_inv; [apply HGV; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        rewrite fv_neg. cbn [FOfree_in]. apply Bool.orb_false_iff. split.
        - destruct (Nat.eqb_spec (S v) w') as [_|HSw]; [reflexivity|].
          cbn [FOin_tm]. apply Bool.orb_false_iff.
          split; [apply Bool.orb_false_iff; split; apply Nat.eqb_neq; lia
                 | apply Htv; [left; reflexivity | lia]].
        - destruct (FOfree_in w' (hsub_f (h_upd v w0 h) A)) eqn:E; [|reflexivity].
          destruct (FOfree_in_hsub A (h_upd v w0 h) w' E) as [x [Hx Ex]]. unfold h_upd in Ex.
          destruct (Nat.eqb_spec x v) as [->|Hxv]; [lia|].
          pose proof (HOK_range n G V h rho env x (HhA x Hx Hxv)). lia. }
      refine (WITNESS n k W v t A (FONeg A) (FONeg (FOForall v (FOImplF (FOltv v t) A)))
                HSvt Hvt HWA HWv HWt ltac:(intros x Hx; rewrite fv_neg in Hx; exact Hx)
                (fun V' G' h' rho' env' HI0 Hh0 HD => proj2 (IHA HWA V' G' h' rho' env' HI0 Hh0) HD)
                (FOPr_ball_neg v W t A ltac:(lia) HSvt)
                ltac:(intros x Hx; rewrite fv_neg in Hx; apply HS; exact Hx)
                (S w0) _ h rho env w0
                (Inv_move n V (S w0) G _ h rho env _ HI' Hinc2 ltac:(lia) HG2 HG2V)
                Hhw' HWw0 ltac:(lia) ltac:(lia)
                (FOPrH_nimp_l _ _ _ _ HX2) (FOPrH_nimp_r _ _ _ _ HX2)).
Qed.

Lemma fv_and : forall x X Y, FOfree_in x (FOAnd X Y) = (FOfree_in x X || FOfree_in x Y)%bool.
Proof. intros x X Y. unfold FOAnd, FONeg. cbn [FOfree_in]. rewrite !Bool.orb_false_r. reflexivity. Qed.

Lemma D0P_bex : forall n k W v t A, FOin_tm v t = false -> FOin_tm (S v) t = false ->
  D0P n k W A -> D0P n k W (FOExists v (FOAnd (FOltv v t) A)).
Proof.
  intros n k W v t A Hvt HSvt IHA HW V G h rho env HI Hhw.
  destruct (bq_bounds' v t A W HW) as [HWv [HWA HWt]].
  assert (HS : forall x, FOfree_in x (FOExists v (FOAnd (FOltv v t) A)) = true <->
               FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v))
    by (intros x; exact (proj2 (fv_bq v t A x Hvt HSvt))).
  pose proof (Inv_weaken n V G h rho env _
                (fun x => FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v)) HI
                ltac:(intros x Hx; apply HS; exact Hx)) as HI'.
  assert (Hhw' : forall x, FOin_tm x t = true \/ (FOfree_in x A = true /\ x <> v) -> W <= h x)
    by (intros x Hx; apply Hhw; apply HS; exact Hx).
  pose proof HI' as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (Hht : forall x, FOin_tm x t = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; left; exact Hx).
  assert (HhA : forall x, FOfree_in x A = true -> x <> v -> HOK n G V h rho env x)
    by (intros x Hx Hxv; apply Hh; right; split; assumption).
  destruct (hsub_facts t n G V h rho env Hht) as [Ht0 Htv].
  assert (HtW : forall w, w < W -> FOin_tm w (hsub_tm h t) = false).
  { intros w Hw. destruct (FOin_tm w (hsub_tm h t)) eqn:E; [|reflexivity].
    destruct (FOin_tm_hsub t h w E) as [x [Hx <-]]. specialize (Hhw' x (or_introl Hx)). lia. }
  assert (HWA' : FOfree_in W A = false) by (apply FOfree_in_above; lia).
  assert (HWt' : FOin_tm W t = false) by (apply FOin_tm_above; lia).
  rewrite !hsub_bex by assumption.
  split.
  - intros HB.
    refine (PRI_exe n _ _ V W G _ env v (FOAnd (FOltv v (hsub_tm h t)) (hsub_f (h_hide v h) A))
              HB _ _ _ _ _ _ _); [lia | avoid_tms | above_tac | | | |].
    + intros w Hw Hwv. rewrite fv_and, fv_ltv by (apply HtW; lia).
      rewrite (hA_free n G V h rho env v A w HhA ltac:(lia) Hwv).
      rewrite (proj2 (Nat.eqb_neq v w) ltac:(lia)). rewrite Bool.orb_false_r. cbn [orb]. fr_tm.
    + intros w Hw Hwv. rewrite fv_and, fv_ltv by (apply HtW; lia).
      rewrite (hA_free n G V h rho env v A w HhA ltac:(lia) Hwv).
      rewrite (proj2 (Nat.eqb_neq v w) ltac:(lia)). rewrite Bool.orb_false_r. cbn [orb].
      apply Htv; [left; reflexivity | exact Hw].
    + intros w Hw HWw. apply FOsubst_ok_and;
        [apply FOsubst_ok_ltv; apply FOin_tm_var_ne; lia
        | apply (hsub_f_ok A (h_hide v h) v (FOVar w) W HWA);
          intros w' Hw'; cbn [FOin_tm] in Hw'; apply Nat.eqb_eq in Hw'; lia].
    + intros w0 Hw0 HWw0.
      rewrite FOsubst_f_and, FOsubst_f_ltv_self by (apply HtW; lia).
      rewrite hsub_f_inst by (intros z Hz Hz'; pose proof (Hhw' z (or_intror (conj Hz' Hz))); lia).
      lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
        assert (HX2 : FOPrH n G2 (FOAnd (FOExists (S v) (FOEq (FOPlus (FOVar w0)
                        (FOSucc (FOVar (S v)))) (hsub_tm h t))) (hsub_f (h_upd v w0 h) A)))
          by apply FOPrH_last;
        assert (Hinc2 : forall X, In X G -> In X G2)
          by (intros X HX'; apply in_or_app; left; exact HX');
        assert (HG2 : FOctx_avoid G2 0 1000);
        [| assert (HG2V : forall w', S w0 <= w' -> FOfree_ctx w' G2)]
      end.
      { intros w' ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        rewrite fv_and. cbn [FOfree_in]. apply Bool.orb_false_iff. split.
        - destruct (Nat.eqb_spec (S v) w') as [_|HSw]; [reflexivity|].
          cbn [FOin_tm]. apply Bool.orb_false_iff.
          split; [apply Bool.orb_false_iff; split; apply Nat.eqb_neq; lia | fr_tm].
        - destruct (FOfree_in w' (hsub_f (h_upd v w0 h) A)) eqn:E; [|reflexivity].
          destruct (FOfree_in_hsub A (h_upd v w0 h) w' E) as [x [Hx Ex]]. unfold h_upd in Ex.
          destruct (Nat.eqb_spec x v) as [->|Hxv]; [lia|].
          pose proof (HOK_range n G V h rho env x (HhA x Hx Hxv)). lia. }
      { intros w' ?. apply FOfree_ctx_app_inv; [apply HGV; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        rewrite fv_and. cbn [FOfree_in]. apply Bool.orb_false_iff. split.
        - destruct (Nat.eqb_spec (S v) w') as [_|HSw]; [reflexivity|].
          cbn [FOin_tm]. apply Bool.orb_false_iff.
          split; [apply Bool.orb_false_iff; split; apply Nat.eqb_neq; lia
                 | apply Htv; [left; reflexivity | lia]].
        - destruct (FOfree_in w' (hsub_f (h_upd v w0 h) A)) eqn:E; [|reflexivity].
          destruct (FOfree_in_hsub A (h_upd v w0 h) w' E) as [x [Hx Ex]]. unfold h_upd in Ex.
          destruct (Nat.eqb_spec x v) as [->|Hxv]; [lia|].
          pose proof (HOK_range n G V h rho env x (HhA x Hx Hxv)). lia. }
      refine (WITNESS n k W v t A A (FOExists v (FOAnd (FOltv v t) A))
                HSvt Hvt HWA HWv HWt (fun x Hx => Hx)
                (fun V' G' h' rho' env' HI0 Hh0 HD => proj1 (IHA HWA V' G' h' rho' env' HI0 Hh0) HD)
                (FOPr_bex_pos v W t A ltac:(lia) HSvt)
                ltac:(intros x Hx; apply HS; exact Hx)
                (S w0) _ h rho env w0
                (Inv_move n V (S w0) G _ h rho env _ HI' Hinc2 ltac:(lia) HG2 HG2V)
                Hhw' HWw0 ltac:(lia) ltac:(lia)
                (FOPrH_and_l _ _ _ _ HX2) (FOPrH_and_r _ _ _ _ HX2)).
  - intros Hn.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_thm _ _ _ (FOPr_not_ex_and n v
                  (FOltv v (hsub_tm h t)) (hsub_f (h_hide v h) A))) Hn) as HB.
    refine (PRI_numr_ex n _ _ V W G _ env (hsub_tm h t) _ _ _ _ _ _);
      [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
    intros w Hw HWw.
    lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
      assert (HG2 : FOctx_avoid G2 0 1000) by (intros w' ? ?; free_ctx);
      assert (HG2V : forall w', S w <= w' -> FOfree_ctx w' G2) by (intros w' ?; free_ctx);
      assert (Hinc2 : forall X, In X G -> In X G2)
        by (intros X HX; apply in_or_app; left; exact HX);
      assert (N2 : FOPrH n G2 (FONUMR (hsub_tm h t) (FOVar w))) by wk_in;
      assert (HB2 : FOPrH n G2 (FOForall v (FOImplF (FOltv v (hsub_tm h t))
                                              (FONeg (hsub_f (h_hide v h) A))))) by wk HB
    end.
    pose proof (Inv_move n V (S w) G _ h rho env _ HI' Hinc2 ltac:(lia) HG2 HG2V) as HIm.
    assert (HWNA : FOvars_max (FONeg A) < W) by (unfold FONeg; cbn [FOvars_max]; lia).
    assert (IHD : forall V' G' h' rho' env',
              Inv n V' G' h' rho' env' (fun x => FOfree_in x (FONeg A) = true) ->
              (forall x, FOfree_in x (FONeg A) = true -> W <= h' x) ->
              FOPrH n G' (hsub_f h' (FONeg A)) ->
              PRI n (FOPrCores k) (FOu0 k) V' G' (cpat_f rho' (FONeg A)) env').
    { intros V' G' h' rho' env' HI0 Hh0 HD.
      apply (proj2 (IHA HWA V' G' h' rho' env'
                      (Inv_weaken n V' G' h' rho' env' _ (fun x => FOfree_in x A = true) HI0
                         (fun x Hx => eq_trans (fv_neg x A) Hx))
                      (fun x Hx => Hh0 x (eq_trans (fv_neg x A) Hx)))).
      exact HD. }
    lazymatch type of HG2 with FOctx_avoid ?G2 _ _ =>
      assert (HIm' : Inv n (S w) G2 h rho env (fun x => FOfree_in x (FONeg A) = true /\ x <> v))
        by (apply (Inv_weaken n (S w) _ h rho env _ _ HIm); intros x Hx; cbn beta in Hx |- *;
            destruct Hx as [Hx Hxv]; rewrite fv_neg in Hx; right; split; assumption)
    end.
    pose proof (BALL_GEN n k W v (FONeg A) HWNA HWv IHD
                  (S w) _ h rho env (hsub_tm h t) (FOVar w) W ltac:(lia) (le_n W) HIm'
                  ltac:(intros x Hx Hxv; rewrite fv_neg in Hx; apply Hhw'; right; split;
                        assumption)
                  ltac:(avoid_tms) ltac:(above_tac) HtW N2 HB2) as PB.
    unfold ballQ in PB.
    pose proof (Inv_slot n (S w) _ h rho env _ (hsub_tm h t) (FOVar w) W HIm N2 ltac:(avoid_tms)
                  ltac:(intros s [<-|[]] w' Hw'; apply FOin_tm_var_ne; lia)
                  ltac:(intros x [Hx|[Hx _]] E; subst x; congruence)) as HI3.
    destruct HI3 as [HV3 [HG03 [HGV3 [HE3 [Henv3 [Hr3 Hh3]]]]]].
    pose proof (PRI_teval t n k (S w) _ h _ _ W (length env) HV3 HG03 HGV3 HE3 Henv3 Hr3
                  ltac:(intros x Hx; apply Hh3; left; exact Hx) HWt'
                  (rho_sub_eq W (length env) rho) ltac:(rewrite length_app; cbn [length]; lia)
                  ltac:(rewrite nth_snoc_len; exact N2)) as TT.
    pose proof (PRI_thm_open n k (S w) _ _ (rho_sub (Some W) (length env) rho) _
                  (FOPr_bexneg_final v W t A Hvt HSvt HWA' ltac:(lia) ltac:(lia)
                     ltac:(apply FOin_tm_var_ne; lia)) HE3) as T.
    specialize (T ltac:(intros x Hx; fv_cases Hx;
                        first [ exists (length env); split;
                                [apply rho_sub_eq | rewrite length_app; cbn [length]; lia]
                              | destruct (Hh3 x (or_introl Hx)) as [i [Hxi [Hi _]]];
                                exists i; split; assumption
                              | assert (Hxv : x <> v)
                                  by (intro Exv; subst x; rewrite Nat.eqb_refl in *; discriminate);
                                destruct (Hh3 x (or_intror (conj Hx Hxv))) as [i [Hxi [Hi _]]];
                                exists i; split; assumption ])).
    pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE3 Hr3 T TT) as T1.
    pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE3 Hr3 T1 PB) as T2.
    refine (PRI_reslot n _ _ (S w) _ _ _ rho _ env _ _ _ _ T2); [| above_tac | avoid_tms | lia].
    intros x Hx. unfold SlotAgree. rewrite fv_neg in Hx. apply HS in Hx.
    assert (HxW : x <> W) by (destruct Hx as [Hx|[Hx _]]; intro E; subst x; congruence).
    rewrite (rho_sub_ne W (length env) rho x HxW).
    destruct (Hh x Hx) as [i [Hxi [Hi _]]]. rewrite Hxi, (nth_app_lt env [FOVar w] i Hi).
    apply FOPrH_refl.
Qed.

(** ** Bounded formulas. *)

Theorem D0P_all : forall n k W A, FOdelta0 A -> D0P n k W A.
Proof.
  intros n k W A HA.
  induction HA as [a b | | B C HB IHB HC IHC | v t A' Hv HSv HA' IHA' | v t A' Hv HSv HA' IHA'].
  - apply D0P_eq.
  - apply D0P_false.
  - apply D0P_impl; assumption.
  - exact (D0P_ball n k W v t A' Hv HSv IHA').
  - exact (D0P_bex n k W v t A' Hv HSv IHA').
Qed.

(** ** Sigma_1 formulas. *)

Definition S1P (n k W : nat) (A : FOFormula) : Prop :=
  FOvars_max A < W ->
  forall V G h rho env,
  Inv n V G h rho env (fun x => FOfree_in x A = true) ->
  (forall x, FOfree_in x A = true -> W <= h x) ->
  FOPrH n G (hsub_f h A) -> PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho A) env.

Lemma FOPr_ex_self : forall x A, FOProvesTn 0 (FOImplF A (FOExists x A)).
Proof.
  intros x A. change (FOPrH 0 [] (FOImplF A (FOExists x A))). apply FOPrH_intro.
  apply (FOPrH_ex_intro _ _ x (FOVar x)); [apply FOsubst_ok_var_self|].
  rewrite FOsubst_f_id. apply FOPrH_last.
Qed.

Lemma S1P_ex : forall n k W x A, S1P n k W A -> S1P n k W (FOExists x A).
Proof.
  intros n k W x A IHA HW V G h rho env HI Hhw HB. cbn [FOvars_max] in HW.
  assert (HWA : FOvars_max A < W) by lia.
  assert (HS : forall y, FOfree_in y (FOExists x A) = true <-> FOfree_in y A = true /\ y <> x).
  { intros y. cbn [FOfree_in]. destruct (Nat.eqb_spec x y) as [->|Hxy].
    - split; [discriminate | intros [_ H]; exfalso; exact (H eq_refl)].
    - split; [intros H; split; [exact H | lia] | intros [H _]; exact H]. }
  pose proof HI as [HV [HG0 [HGV [HE [Henv [Hr Hh]]]]]].
  pose proof HE as [_ [_ [_ Henvv]]].
  assert (HhA : forall y, FOfree_in y A = true -> y <> x -> HOK n G V h rho env y)
    by (intros y Hy Hyx; apply Hh; apply HS; split; assumption).
  cbn [hsub_f] in HB.
  refine (PRI_exe n _ _ V W G _ env x (hsub_f (h_hide x h) A) HB _ _ _ _ _ _ _);
    [lia | avoid_tms | above_tac | | | |].
  - intros w Hw Hwx. exact (hA_free n G V h rho env x A w HhA ltac:(lia) Hwx).
  - intros w Hw Hwx. exact (hA_free n G V h rho env x A w HhA ltac:(lia) Hwx).
  - intros w Hw HWw. apply (hsub_f_ok A (h_hide x h) x (FOVar w) W HWA).
    intros w' Hw'. cbn [FOin_tm] in Hw'. apply Nat.eqb_eq in Hw'. lia.
  - intros w0 Hw0 HWw0.
    rewrite hsub_f_inst by (intros z Hz Hz'; pose proof (Hhw z ltac:(apply HS; split; assumption));
                           lia).
    refine (PRI_numr_ex n _ _ (S w0) 0 _ _ env (FOVar w0) _ _ _ _ _ _);
      [lia | avoid_tms | intros w' ?; apply FOin_tm_var_ne; lia | avoid_tms | above_tac |].
    intros w1 Hw1 _.
    lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
      assert (HA3 : FOPrH n G3 (hsub_f (h_upd x w0 h) A)) by wk_in;
      assert (N3 : FOPrH n G3 (FONUMR (FOVar w0) (FOVar w1))) by wk_in;
      assert (Hinc3 : forall X, In X G -> In X G3)
        by (intros X HX; apply in_or_app; left; apply in_or_app; left; exact HX);
      assert (HG3 : FOctx_avoid G3 0 1000);
      [| assert (HG3V : forall w', S w1 <= w' -> FOfree_ctx w' G3)]
    end.
    { intros w' ? ?. apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply HG0; lia|]|].
      - apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        destruct (FOfree_in w' (hsub_f (h_upd x w0 h) A)) eqn:E; [|reflexivity].
        destruct (FOfree_in_hsub A (h_upd x w0 h) w' E) as [y [Hy Ey]]. unfold h_upd in Ey.
        destruct (Nat.eqb_spec y x) as [->|Hyx]; [lia|].
        pose proof (HOK_range n G V h rho env y (HhA y Hy Hyx)). lia.
      - free_ctx. }
    { intros w' ?. apply FOfree_ctx_app_inv; [apply FOfree_ctx_app_inv; [apply HGV; lia|]|].
      - apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        destruct (FOfree_in w' (hsub_f (h_upd x w0 h) A)) eqn:E; [|reflexivity].
        destruct (FOfree_in_hsub A (h_upd x w0 h) w' E) as [y [Hy Ey]]. unfold h_upd in Ey.
        destruct (Nat.eqb_spec y x) as [->|Hyx]; [lia|].
        pose proof (HOK_range n G V h rho env y (HhA y Hy Hyx)). lia.
      - free_ctx. }
    pose proof (Inv_move n V (S w1) G _ h rho env _ HI Hinc3 ltac:(lia) HG3 HG3V) as HIm.
    pose proof (Inv_weaken n (S w1) _ h rho env _
                  (fun y => FOfree_in y A = true /\ y <> x) HIm
                  (fun y Hy => proj2 (HS y) Hy)) as HIm'.
    pose proof (Inv_holder n (S w1) _ h rho env (fun y => FOfree_in y A = true) x w0 (FOVar w1)
                  HIm' N3 ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                  ltac:(intros s [<-|[]] w Hw; apply FOin_tm_var_ne; lia)) as HI3.
    pose proof (IHA HWA (S w1) _ _ _ _ HI3
                  ltac:(intros y Hy; unfold h_upd; destruct (Nat.eqb_spec y x) as [->|Hyx];
                        [exact HWw0 | apply Hhw; apply HS; split; assumption]) HA3) as TA.
    pose proof HI3 as [_ [_ [_ [HE3 [_ [Hr3 Hh3]]]]]].
    pose proof (PRI_thm_open n k (S w1) _ _ (rho_sub (Some x) (length env) rho) _
                  (FOPr_ex_self x A) HE3) as T.
    specialize (T ltac:(intros y Hy; cbn [FOfree_in] in Hy;
                        apply Bool.orb_true_iff in Hy; destruct Hy as [Hy|Hy];
                        [ destruct (Hh3 y Hy) as [i [Hyi [Hi _]]]; exists i; split; assumption
                        | destruct (Nat.eqb x y); [discriminate Hy|];
                          destruct (Hh3 y Hy) as [i [Hyi [Hi _]]]; exists i; split; assumption ])).
    pose proof (PRI_mp n _ _ (S w1) _ _ _ _ _ HE3 Hr3 T TA) as T1.
    refine (PRI_reslot n _ _ (S w1) _ _ _ rho _ env _ _ _ _ T1); [| above_tac | avoid_tms | lia].
    intros y Hy. unfold SlotAgree. apply HS in Hy. destruct Hy as [Hy Hyx].
    rewrite (rho_sub_ne x (length env) rho y Hyx).
    destruct (Hh y (proj2 (HS y) (conj Hy Hyx))) as [i [Hyi [Hi _]]].
    rewrite Hyi, (nth_app_lt env [FOVar w1] i Hi). apply FOPrH_refl.
Qed.

Theorem S1P_all : forall n k W A, FOsigma1 A -> S1P n k W A.
Proof.
  intros n k W A HA. induction HA as [A HA | x A HA IH].
  - intros HW V G h rho env HI Hhw HB. exact (proj1 (D0P_all n k W A HA HW V G h rho env HI Hhw) HB).
  - exact (S1P_ex n k W x A IH).
Qed.

(** ** Sigma_1 sentences. *)

Lemma hsub_f_id : forall A h, (forall z, h z = z) -> hsub_f h A = A.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros h H; cbn [hsub_f].
  - assert (K : forall t, hsub_tm h t = t).
    { induction t as [z| |u IH|u IHu w IHw|u IHu w IHw]; cbn [hsub_tm];
        [rewrite H | | rewrite IH | rewrite IHu, IHw | rewrite IHu, IHw]; reflexivity. }
    rewrite !K. reflexivity.
  - reflexivity.
  - rewrite IHB, IHC by exact H. reflexivity.
  - rewrite IHB; [reflexivity|]. intros z. unfold h_hide. destruct (Nat.eqb_spec z y); auto.
  - rewrite IHB; [reflexivity|]. intros z. unfold h_hide. destruct (Nat.eqb_spec z y); auto.
Qed.

Lemma FOPRu_ProvSentence : forall k A,
  FOPRu (FOPrCores k) (FOu0 k) (FOnumeral (FOcode_f A)) = FOProvSentence k A.
Proof.
  intros k A. unfold FOPRu, FOu0. rewrite FOPRMATx_num, FOsubst_f_num.
  rewrite (FOsubst_num_comm (FOPRMAT (FOPrCores k)) 0 1) by lia. reflexivity.
Qed.

Theorem provable_sigma1_sentence : forall k A, FOsigma1 A ->
  (forall x, FOfree_in x A = false) ->
  FOProvesTn 0 (FOImplF A (FOProvSentence k A)).
Proof.
  intros k A HA Hcl.
  set (W := S (FOvars_max A)).
  set (V := 2000 + W).
  assert (HCA : forall w, FOfree_ctx w [A])
    by (intros w; apply FOfree_ctx_cons; [apply Hcl | apply FOfree_ctx_nil]).
  assert (HI : Inv 0 V [A] (fun z => z) (fun _ => None) [] (fun x => FOfree_in x A = true)).
  { split; [unfold V; lia|]. split; [intros w ? ?; apply HCA|]. split; [intros w ?; apply HCA|].
    split; [|split; [apply FOtms_avoid_nil | split; [intros z i Hz; discriminate Hz|]]].
    - split; [split; [intros w ? ?; apply HCA | intros i Hi; cbn in Hi; lia]|].
      split; [apply FOtms_avoid_nil|]. split; [unfold V; lia | intros t []].
    - intros x Hx. rewrite Hcl in Hx. discriminate Hx. }
  pose proof (S1P_all 0 k W A HA ltac:(unfold W; lia) V [A] (fun z => z) (fun _ => None) []
                HI ltac:(intros x Hx; rewrite Hcl in Hx; discriminate Hx)
                ltac:(rewrite (hsub_f_id A (fun z => z) (fun z => eq_refl));
                      apply FOPrH_assum; left; reflexivity)) as HP.
  pose proof (HP [A] V (FOnumeral (FOcode_f A)) (fun X HX => HX) ltac:(intros w ? ?; apply HCA)
                ltac:(avoid_tms) (le_n V)
                ltac:(split; [intros w _; apply HCA | intros t [<-|[]] w _; apply FOin_tm_numeral])
                (FOPrH_patf_closed_code 0 [A] A V ltac:(unfold V; lia))) as H.
  rewrite FOPRu_ProvSentence in H. exact H.
Qed.

(** ** The third derivability condition. *)

Theorem FOHBL3_internal : forall k A,
  FOProvesTn 0 (FOImplF (FOProvSentence k A) (FOProvSentence k (FOProvSentence k A))).
Proof.
  intros k A. apply provable_sigma1_sentence.
  - apply FOsigma1_FOProvSentence.
  - intros x. apply FOProvSentence_closed.
Qed.

(** ** Numerals substituted into a code, one variable after another.

    [FOSUBNUMS q c xs ys r]: substituting, in order, the numeral of the
    value of each [y] for the corresponding variable [x] in the formula
    coded [c] gives the code [r].  Each step names the value [z] (bound
    to [q + 2]), its numeral code [m] ([q + 1]) and the next code [a]
    ([q]): [z = y] carries the value, a tag-[5] row gives [m], and a
    tag-[3] row of the checker's tables gives [a].  The terms [ys] occur
    only in the equations [z = y]. *)

Fixpoint FOSUBNUMS (q : nat) (c : FOTerm) (xs : list nat) (ys : list FOTerm) (r : FOTerm)
    : FOFormula :=
  match xs, ys with
  | x :: xs', y :: ys' =>
      FOExists q (FOExists (S q) (FOExists (S (S q))
        (FOAnd (FOEq (FOVar (S (S q))) y)
          (FOAnd (FONUMR (FOVar (S (S q))) (FOVar (S q)))
            (FOAnd (FOTBLEX (FOnumeral 3) (FOnumeral x) (FOVar (S q)) c (FOVar q))
                   (FOSUBNUMS (S (S (S q))) (FOVar q) xs' ys' r))))))
  | _, _ => FOEq c r
  end.

Lemma FOfree_in_SUBNUMS : forall xs ys q c r w,
  1000 <= q -> FOtms_avoid [c] 13 18 -> FOtms_avoid (c :: r :: ys) w (S w) ->
  FOfree_in w (FOSUBNUMS q c xs ys r) = false.
Proof.
  induction xs as [|x xs IH]; intros ys q c r w Hq Hc Hav.
  - destruct ys; cbn [FOSUBNUMS FOfree_in]; apply Bool.orb_false_iff;
      split; apply Hav; first [left; reflexivity | right; left; reflexivity | lia].
  - destruct ys as [|y ys].
    + cbn [FOSUBNUMS FOfree_in]. apply Bool.orb_false_iff;
        split; apply Hav; first [left; reflexivity | right; left; reflexivity | lia].
    + cbn [FOSUBNUMS]. cbn [FOfree_in].
      destruct (Nat.eqb_spec q w) as [_|Hqw]; [reflexivity|].
      destruct (Nat.eqb_spec (S q) w) as [_|HSqw]; [reflexivity|].
      destruct (Nat.eqb_spec (S (S q)) w) as [_|HSSqw]; [reflexivity|].
      rewrite !fv_and. apply Bool.orb_false_iff. split.
      * cbn [FOfree_in]. apply Bool.orb_false_iff. split; [apply FOin_tm_var_ne; lia|].
        apply Hav; [right; right; left; reflexivity | lia | lia].
      * apply Bool.orb_false_iff. split; [apply FOfree_in_NUMR_all; avoid_tms|].
        apply Bool.orb_false_iff. split; [apply FOfree_in_TBLEX_all; avoid_tms|].
        apply IH; [lia | avoid_tms | avoid_tms].
Qed.

Lemma FOsubst_f_SUBNUMS : forall xs ys q c r z s,
  (z < q \/ q + 3 * length xs <= z) -> 13 <= z -> (z < 28 \/ 50 <= z) -> 1000 <= q ->
  FOsubst_f z s (FOSUBNUMS q c xs ys r) =
  FOSUBNUMS q (FOsubst_t z s c) xs (map (FOsubst_t z s) ys) (FOsubst_t z s r).
Proof.
  induction xs as [|x xs IH]; intros ys q c r z s Hz H13 H28 Hq.
  - destruct ys; reflexivity.
  - destruct ys as [|y ys]; [reflexivity|]. cbn [FOSUBNUMS map length] in *.
    rewrite !FOsubst_f_ex_ne by lia.
    rewrite !FOsubst_f_and, FOsubst_f_eq, FOsubst_f_TBLEX by lia.
    rewrite (FOsubst_f_not_free (FONUMR _ _)) by (apply FOfree_in_NUMR_all; avoid_tms).
    rewrite IH by lia.
    rewrite !FOsubst_t_var_ne by lia. rewrite !FOsubst_t_numeral. reflexivity.
Qed.

Lemma FOsubst_ok_SUBNUMS : forall xs ys q c r z s,
  1000 <= q -> 13 <= z -> (z < q \/ q + 3 * length xs <= z) ->
  FOtms_avoid [c] 13 18 -> FOtms_avoid [s] q (q + 3 * length xs) ->
  (FOtms_avoid [s] 2 50 \/ FOin_tm z c = false) ->
  FOsubst_ok z s (FOSUBNUMS q c xs ys r) = true.
Proof.
  induction xs as [|x xs IH]; intros ys q c r z s Hq H13 Hz Hc Hs Hsc.
  - destruct ys; reflexivity.
  - destruct ys as [|y ys]; [reflexivity|]. cbn [FOSUBNUMS length] in *.
    apply FOsubst_ok_ex; [fr_tm|]. apply FOsubst_ok_ex; [fr_tm|].
    apply FOsubst_ok_ex; [fr_tm|].
    apply FOsubst_ok_and; [apply FOsubst_ok_eq|].
    apply FOsubst_ok_and; [apply FOsubst_ok_not_free, FOfree_in_NUMR_all; avoid_tms|].
    apply FOsubst_ok_and.
    + destruct Hsc as [Hsc|Hsc].
      * apply FOsubst_ok_TBLEX; [exact H13 | avoid_tm].
      * assert (Hcz : FOtms_avoid [c] z (S z))
          by (intros t [<-|[]] v Hv1 Hv2; replace v with z by lia; exact Hsc).
        apply FOsubst_ok_not_free, FOfree_in_TBLEX_all; avoid_tms.
    + apply IH; [lia | exact H13 | lia | avoid_tms | avoid_tms | right; fr_tm].
Qed.

(** ** One step of the substitution chain. *)

Lemma FOPrH_subnums_cons : forall n G q x xs y ys a c N m,
  1000 <= q -> q + 3 + 3 * length xs <= N ->
  FOtms_avoid [a; c; m; y] q (q + 3 + 3 * length xs) ->
  FOtms_avoid ys q (q + 3 + 3 * length xs) ->
  FOtms_avoid [m; y] 2 50 -> FOtms_avoid [m; y] 802 805 ->
  FOtms_avoid [m] 13 18 -> FOtms_avoid [a] 13 18 ->
  FOPrH n G (FONUMR y m) ->
  FOPrH n G (FOTBLEX (FOnumeral 3) (FOnumeral x) m a (FOVar N)) ->
  FOPrH n G (FOSUBNUMS (S (S (S q))) (FOVar N) xs ys c) ->
  FOPrH n G (FOSUBNUMS q a (x :: xs) (y :: ys) c).
Proof.
  intros n G q x xs y ys a c N m Hq HN Hav Hys H2 H802 Hm13 Ha13 Hnum Hrow Hrest.
  assert (Hysq : forall z, q <= z -> z < q + 3 -> forall t, In t ys -> FOin_tm z t = false)
    by (intros z Hz1 Hz2 t Ht; apply (Hys t Ht); lia).
  cbn [FOSUBNUMS].
  (* the code after the step *)
  apply (FOPrH_ex_intro _ _ q (FOVar N)).
  { apply FOsubst_ok_ex; [fr_tm|]. apply FOsubst_ok_ex; [fr_tm|].
    apply FOsubst_ok_and; [apply FOsubst_ok_eq|].
    apply FOsubst_ok_and; [apply FOsubst_ok_not_free, FOfree_in_NUMR_all; avoid_tms|].
    apply FOsubst_ok_and; [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|].
    apply FOsubst_ok_SUBNUMS; [lia | lia | lia | avoid_tms | avoid_tms | left; avoid_tms]. }
  rewrite !FOsubst_f_ex_ne by lia.
  rewrite !FOsubst_f_and, FOsubst_f_eq, FOsubst_f_TBLEX by lia.
  rewrite (FOsubst_f_not_free (FONUMR _ _)) by (apply FOfree_in_NUMR_all; avoid_tms).
  rewrite FOsubst_f_SUBNUMS by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne by lia. rewrite !FOsubst_t_numeral.
  rewrite (FOsubst_t_not_in y q (FOVar N)), (FOsubst_t_not_in a q (FOVar N)),
    (FOsubst_t_not_in c q (FOVar N)) by fr_tm.
  rewrite (FOsubst_map_avoid q (FOVar N) ys) by (intros t Ht; apply (Hysq q); lia || exact Ht).
  (* the numeral code of the value *)
  apply (FOPrH_ex_intro _ _ (S q) m).
  { apply FOsubst_ok_ex; [fr_tm|].
    apply FOsubst_ok_and; [apply FOsubst_ok_eq|].
    apply FOsubst_ok_and; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|].
    apply FOsubst_ok_and; [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|].
    apply FOsubst_ok_SUBNUMS; [lia | lia | lia | avoid_tms | avoid_tms | left; avoid_tms]. }
  rewrite !FOsubst_f_ex_ne by lia.
  rewrite !FOsubst_f_and, FOsubst_f_eq, FOsubst_f_TBLEX, FOsubst_f_NUMR by (lia || avoid_tms).
  rewrite FOsubst_f_SUBNUMS by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne by lia. rewrite !FOsubst_t_numeral.
  rewrite (FOsubst_t_not_in y (S q) m), (FOsubst_t_not_in a (S q) m),
    (FOsubst_t_not_in c (S q) m) by fr_tm.
  rewrite (FOsubst_map_avoid (S q) m ys) by (intros t Ht; apply (Hysq (S q)); lia || exact Ht).
  (* the value *)
  apply (FOPrH_ex_intro _ _ (S (S q)) y).
  { apply FOsubst_ok_and; [apply FOsubst_ok_eq|].
    apply FOsubst_ok_and; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|].
    apply FOsubst_ok_and; [apply FOsubst_ok_not_free, FOfree_in_TBLEX_all; avoid_tms|].
    apply FOsubst_ok_SUBNUMS; [lia | lia | lia | avoid_tms | avoid_tms | left; avoid_tms]. }
  rewrite !FOsubst_f_and, FOsubst_f_eq, FOsubst_f_NUMR by (lia || avoid_tms).
  rewrite (FOsubst_f_not_free (FOTBLEX _ _ _ _ _)) by (apply FOfree_in_TBLEX_all; avoid_tms).
  rewrite FOsubst_f_SUBNUMS by lia.
  rewrite FOsubst_t_var_eq'. rewrite !FOsubst_t_var_ne by lia.
  rewrite (FOsubst_t_not_in y (S (S q)) y), (FOsubst_t_not_in m (S (S q)) y),
    (FOsubst_t_not_in c (S (S q)) y) by fr_tm.
  rewrite (FOsubst_map_avoid (S (S q)) y ys)
    by (intros t Ht; apply (Hysq (S (S q))); lia || exact Ht).
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  apply FOPrH_and_intro; [exact Hnum|].
  apply FOPrH_and_intro; [exact Hrow | exact Hrest].
Qed.

(** ** The chain from one code to another.

    [a] codes [A] with the slots of [rho] filled from [env]; [c] codes
    [A] with, in addition, the variables [xs] filled from [ms], where
    the [i]-th entry of [ms] is the numeral code of the [i]-th entry of
    [ys].  Each step names the next code [F + 3] through the pattern's
    totality and derives its tag-[3] row. *)

Lemma SUBNUMS_chain : forall xs n A G rho env ms ys a c q Ba Bc F,
  NoDup xs -> length ms = length xs -> length ys = length xs ->
  (forall x, In x xs -> rho x = None) ->
  (forall z i, rho z = Some i -> i < length env) ->
  FOctx_avoid G 0 1000 -> (forall w, F <= w -> FOfree_ctx w G) ->
  (forall i, i < length env -> exists w, FOPrH n G (FONUMR w (nth i env FOZero))) ->
  (forall i, i < length xs -> FOPrH n G (FONUMR (nth i ys FOZero) (nth i ms FOZero))) ->
  FOtms_avoid [a; c] 0 (q + 3 * length xs) -> FOtms_avoid ys 0 (q + 3 * length xs) ->
  FOtms_avoid ms 0 (q + 3 * length xs) -> FOtms_avoid env 0 (q + 3 * length xs) ->
  (forall t, In t [a; c] -> forall w, F <= w -> FOin_tm w t = false) ->
  (forall t, In t ys -> forall w, F <= w -> FOin_tm w t = false) ->
  (forall t, In t ms -> forall w, F <= w -> FOin_tm w t = false) ->
  (forall t, In t env -> forall w, F <= w -> FOin_tm w t = false) ->
  1000 <= q -> q + 3 * length xs <= F -> F + 4 * length xs + 4 <= Bc ->
  Bc + cpat_span (cpat_f (rho_seq xs (length env) rho) A) <= Ba ->
  FOPrH n G (FOPATF Ba env (cpat_f rho A) a) ->
  FOPrH n G (FOPATF Bc (env ++ ms) (cpat_f (rho_seq xs (length env) rho) A) c) ->
  FOPrH n G (FOSUBNUMS q a xs ys c).
Proof.
  induction xs as [|x xs IH];
    intros n A G rho env ms ys a c q Ba Bc F Hnd Hlm Hly Hxs Hrho HG0 HGF Henv Hms
      Hac Hys0 Hms0 Henv0 HacF HysF HmsF HenvF Hq HqF HFB HBB Ha Hc.
  - destruct ms; [|discriminate]. destruct ys; [|discriminate].
    cbn [FOSUBNUMS rho_seq length] in *. rewrite app_nil_r in Hc.
    refine (FOPrH_patf_unique (cpat_f rho A) n G Ba Bc env a c Ha Hc _ _ _ _ _ _ _ _);
      try lia.
    + intros w ? ?. apply HGF. lia.
    + intros w ? ?. apply HGF. lia.
    + avoid_tms.
    + avoid_tms.
    + avoid_tms.
  - destruct ms as [|m ms]; [discriminate|]. destruct ys as [|y ys]; [discriminate|].
    cbn [length] in Hlm, Hly, Hac, Hys0, Hms0, Henv0, HqF, HFB.
    injection Hlm as Hlm. injection Hly as Hly.
    inversion Hnd as [|x' xs' Hx Hnd']. subst x' xs'.
    cbn [rho_seq] in HBB, Hc.
    assert (HysF' : forall t, In t ys -> forall w, F <= w -> FOin_tm w t = false)
      by (intros t Ht; apply HysF; right; exact Ht).
    assert (HmsF' : forall t, In t ms -> forall w, F <= w -> FOin_tm w t = false)
      by (intros t Ht; apply HmsF; right; exact Ht).
    assert (HenvmF : forall t, In t (env ++ [m]) -> forall w, F <= w -> FOin_tm w t = false).
    { intros t Ht. apply in_app_or in Ht. destruct Ht as [Ht|[<-|[]]];
        [exact (HenvF t Ht) | exact (HmsF m (or_introl eq_refl))]. }
    remember (Ba + cpat_span (cpat_f rho A)) as Ba' eqn:EBa'.
    pose proof (FOPrH_patf_total (cpat_f (rho_sub (Some x) (length env) rho) A) n G Ba'
                  (env ++ [m]) F ltac:(lia) ltac:(lia)
                  ltac:(intros w ? ?; apply HGF; lia) ltac:(intros w ? ?; apply HG0; lia)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hex.
    refine (FOPrH_exe n G F (F + 3) _ _ Hex _ _ _ _ _).
    { apply HGF. lia. }
    { apply FOfree_in_SUBNUMS; [lia | avoid_tms | avoid_tms]. }
    { apply FOfree_in_PATF_any; [lia | avoid_tms]. }
    { apply FOsubst_ok_PATF. avoid_tm. }
    rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
    rewrite (FOsubst_map_avoid F (FOVar (F + 3)) (env ++ [m]))
      by (intros t Ht; apply (HenvmF t Ht); lia).
    set (G1 := G ++ [FOPATF Ba' (env ++ [m]) (cpat_f (rho_sub (Some x) (length env) rho) A)
                      (FOVar (F + 3))]).
    assert (Hinc : forall X, In X G -> In X G1)
      by (intros X HX; apply in_or_app; left; exact HX).
    assert (HG10 : FOctx_avoid G1 0 1000) by (intros w ? ?; unfold G1; free_ctx).
    assert (HG1F : forall w, F + 4 <= w -> FOfree_ctx w G1) by (intros w ?; unfold G1; free_ctx).
    assert (Hrow : FOPrH n G1 (FOTBLEX (FOnumeral 3) (FOnumeral x) m a (FOVar (F + 3)))).
    { refine (FOPrH_rows_f n (Some x) (FOnumeral x) (FOSucc a) m env (env ++ [m]) (length env)
                A G1 rho Ba Ba' a (FOVar (F + 3)) _ _ Hrho _ _ _ _ _ _ _ _ _ _ _ _).
      - split; [intros i Hi; apply nth_app_lt; exact Hi|].
        split; [apply nth_snoc_len|]. split; [reflexivity|]. avoid_tms.
      - split; [intros w ? ?; apply HG10; lia|]. split.
        + intros i Hi. destruct (Henv i Hi) as [w Hw]. exists w.
          exact (FOPrH_weaken n G G1 _ Hinc Hw).
        + intros G' y' _ _ Hne. apply FOPrH_num_neq. cbn [ox_eq] in Hne.
          apply Nat.eqb_neq. exact Hne.
      - exact (Hxs x (or_introl eq_refl)).
      - exact (FOPrH_weaken n G G1 _ Hinc Ha).
      - unfold G1. apply FOPrH_last.
      - apply FOPrH_le_refl. avoid_tm.
      - lia.
      - lia.
      - left. lia.
      - intros w ? ?. apply HG1F. lia.
      - intros w ? ?. apply HG1F. lia.
      - avoid_tms.
      - avoid_tms.
      - avoid_tms. }
    assert (Hrest : FOPrH n G1 (FOSUBNUMS (S (S (S q))) (FOVar (F + 3)) xs ys c)).
    { refine (IH n A G1 (rho_sub (Some x) (length env) rho) (env ++ [m]) ms ys (FOVar (F + 3))
                c (S (S (S q))) Ba' Bc (F + 4) Hnd' Hlm Hly _ _ HG10 HG1F
                _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); try lia.
      - intros x0 Hx0. rewrite rho_sub_ne by (intro E; subst x0; contradiction).
        apply Hxs. right. exact Hx0.
      - intros z i Hz. rewrite length_app. cbn [length]. unfold rho_sub in Hz.
        destruct (Nat.eqb z x); [injection Hz as <-; lia | specialize (Hrho z i Hz); lia].
      - intros i Hi. rewrite length_app in Hi. cbn [length] in Hi.
        destruct (Nat.lt_ge_cases i (length env)) as [Hi'|Hi'].
        + rewrite nth_app_lt by exact Hi'. destruct (Henv i Hi') as [w Hw]. exists w.
          exact (FOPrH_weaken n G G1 _ Hinc Hw).
        + replace i with (length env) by lia. rewrite nth_snoc_len. exists y.
          exact (FOPrH_weaken n G G1 _ Hinc (Hms 0 ltac:(cbn [length]; lia))).
      - intros i Hi. exact (FOPrH_weaken n G G1 _ Hinc (Hms (S i) ltac:(cbn [length]; lia))).
      - avoid_tms.
      - avoid_tms.
      - avoid_tms.
      - avoid_tms.
      - intros t [<-|[<-|[]]] w Hw; [apply FOin_tm_var_ne; lia|].
        apply (HacF c ltac:(in_list)). lia.
      - intros t Ht w Hw. apply (HysF' t Ht). lia.
      - intros t Ht w Hw. apply (HmsF' t Ht). lia.
      - intros t Ht w Hw. apply (HenvmF t Ht). lia.
      - rewrite length_app. cbn [length].
        replace (length env + 1) with (S (length env)) by lia. lia.
      - unfold G1. apply FOPrH_last.
      - rewrite <- app_assoc. cbn [app]. rewrite length_app. cbn [length].
        replace (length env + 1) with (S (length env)) by lia.
        exact (FOPrH_weaken n G G1 _ Hinc Hc). }
    exact (FOPrH_subnums_cons n G1 q x xs y ys a c (F + 3) m Hq ltac:(lia)
             ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)
             ltac:(avoid_tms) ltac:(avoid_tms)
             (FOPrH_weaken n G G1 _ Hinc (Hms 0 ltac:(cbn [length]; lia))) Hrow Hrest).
Qed.

(** ** Numeral codes for a list of terms, named from [w] upwards. *)

Fixpoint numr_ctx (ts : list FOTerm) (w : nat) : list FOFormula :=
  match ts with
  | [] => []
  | t :: ts' => FONUMR t (FOVar w) :: numr_ctx ts' (S w)
  end.

Lemma numr_ctx_nth : forall ts w i, i < length ts ->
  In (FONUMR (nth i ts FOZero) (nth i (map FOVar (seq w (length ts))) FOZero)) (numr_ctx ts w).
Proof.
  induction ts as [|t ts IH]; intros w i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i]; cbn [numr_ctx nth seq map length].
  - left. reflexivity.
  - right. apply IH. lia.
Qed.

Lemma numr_ctx_free : forall ts w0 w,
  FOtms_avoid ts w (S w) -> FOtms_avoid ts 13 18 -> FOtms_avoid ts 802 805 ->
  1000 <= w0 -> (w < w0 \/ w0 + length ts <= w) -> FOfree_ctx w (numr_ctx ts w0).
Proof.
  induction ts as [|t ts IH]; intros w0 w Hw H13 H802 Hw0 Hr; cbn [numr_ctx length] in *.
  - apply FOfree_ctx_nil.
  - apply FOfree_ctx_cons.
    + apply FOfree_in_NUMR_all; avoid_tms.
    + apply IH; [avoid_tms | avoid_tms | avoid_tms | lia | lia].
Qed.

Lemma numr_exs : forall ts n G w C,
  FOtms_avoid ts 2 1000 -> 1000 <= w ->
  (forall w', w <= w' -> FOfree_ctx w' G) -> (forall w', w <= w' -> FOfree_in w' C = false) ->
  (forall t, In t ts -> forall w', w <= w' -> FOin_tm w' t = false) ->
  FOPrH n (G ++ numr_ctx ts w) C -> FOPrH n G C.
Proof.
  induction ts as [|t ts IH]; intros n G w C Hts Hw HG HC Hab H.
  - rewrite app_nil_r in H. exact H.
  - cbn [numr_ctx] in H.
    assert (Htw : FOtms_avoid [t] w (S w))
      by (intros s [<-|[]] v ? ?; apply (Hab t (or_introl eq_refl)); lia).
    apply (FOPrH_numr_exists n G t w C); [avoid_tms | exact Hw | apply HG; lia | apply HC; lia
                                         | exact Htw |].
    apply (IH n (G ++ [FONUMR t (FOVar w)]) (S w) C); [avoid_tms | lia | | | |].
    + intros w' Hw'. apply FOfree_ctx_app_inv; [apply HG; lia|].
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      apply FOfree_in_NUMR_all; [| avoid_tms | avoid_tms].
      apply FOtms_avoid_cons; [intros v ? ?; apply (Hab t (or_introl eq_refl)); lia|].
      apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia | apply FOtms_avoid_nil].
    + intros w' Hw'. apply HC. lia.
    + intros s Hs w' Hw'. apply (Hab s (or_intror Hs)). lia.
    + rewrite <- app_assoc. exact H.
Qed.

(** ** Holders put back.

    [hR Hb R]: the variables in [R] are themselves, every other
    variable [z] is the holder [Hb + z]. *)

Definition hR (Hb : nat) (R : list nat) : nat -> nat :=
  fun z => if existsb (Nat.eqb z) R then z else Hb + z.

Lemma hR_step : forall Hb R0 x z, z < Hb ->
  (if Nat.eqb (hR Hb R0 z) (Hb + x) then x else hR Hb R0 z) = hR Hb (x :: R0) z.
Proof.
  intros Hb R0 x z Hz. unfold hR. cbn [existsb].
  destruct (existsb (Nat.eqb z) R0) eqn:E; cbn beta iota.
  - rewrite Bool.orb_true_r. destruct (Nat.eqb_spec z (Hb + x)); [lia | reflexivity].
  - rewrite Bool.orb_false_r. destruct (Nat.eqb_spec z x) as [->|Hzx].
    + rewrite Nat.eqb_refl. reflexivity.
    + destruct (Nat.eqb_spec (Hb + z) (Hb + x)); [lia | reflexivity].
Qed.

Lemma hR_all : forall Hb R z, In z R -> hR Hb R z = z.
Proof.
  intros Hb R z Hz. unfold hR.
  replace (existsb (Nat.eqb z) R) with true; [reflexivity|].
  symmetry. apply existsb_exists. exists z. split; [exact Hz | apply Nat.eqb_refl].
Qed.

Lemma hsub_tm_rename : forall t h w u,
  FOsubst_t w (FOVar u) (hsub_tm h t) =
  hsub_tm (fun z => if Nat.eqb (h z) w then u else h z) t.
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros h w u; cbn [hsub_tm].
  - destruct (Nat.eqb_spec (h y) w) as [E|Hne].
    + rewrite E. apply FOsubst_t_var_eq'.
    + apply FOsubst_t_var_ne. exact Hne.
  - reflexivity.
  - rewrite FOsubst_t_succ, IH. reflexivity.
  - rewrite FOsubst_t_plus, IHa, IHb. reflexivity.
  - rewrite FOsubst_t_mult, IHa, IHb. reflexivity.
Qed.

Lemma hsub_f_rename : forall A h w u, FOvars_max A < w ->
  FOsubst_f w (FOVar u) (hsub_f h A) =
  hsub_f (fun z => if Nat.eqb (h z) w then u else h z) A.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros h w u Hw;
    cbn [hsub_f FOvars_max] in *.
  - rewrite FOsubst_f_eq, !hsub_tm_rename. reflexivity.
  - reflexivity.
  - rewrite FOsubst_f_impl, IHB, IHC by lia. reflexivity.
  - rewrite FOsubst_f_all_ne by lia. rewrite IHB by lia. f_equal.
    apply hsub_f_ext. intros z _. unfold h_hide.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [|reflexivity].
    destruct (Nat.eqb_spec y w); [lia | reflexivity].
  - rewrite FOsubst_f_ex_ne by lia. rewrite IHB by lia. f_equal.
    apply hsub_f_ext. intros z _. unfold h_hide.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [|reflexivity].
    destruct (Nat.eqb_spec y w); [lia | reflexivity].
Qed.

Lemma hsub_f_rename_ok : forall A h w u, FOvars_max A < w ->
  (forall z, FOfree_in z A = true -> h z = w -> z = u) ->
  FOsubst_ok w (FOVar u) (hsub_f h A) = true.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros h w u Hw Hu;
    cbn [hsub_f FOvars_max] in *.
  - reflexivity.
  - reflexivity.
  - apply FOsubst_ok_impl.
    + apply IHB; [lia|]. intros z Hz. apply Hu. cbn [FOfree_in]. rewrite Hz. reflexivity.
    + apply IHC; [lia|]. intros z Hz. apply Hu. cbn [FOfree_in]. rewrite Hz.
      apply Bool.orb_true_r.
  - cbn [FOsubst_ok]. destruct (Nat.eqb_spec y w) as [->|Hyw]; [reflexivity|].
    destruct (FOfree_in w (hsub_f (h_hide y h) B)) eqn:E; [|reflexivity].
    apply andb_true_intro. split.
    + destruct (FOfree_in_hsub B (h_hide y h) w E) as [z [Hz Ez]]. revert Ez. unfold h_hide.
      destruct (Nat.eqb_spec z y) as [->|Hzy]; intros Ez; [lia|].
      assert (Hzu : z = u).
      { apply Hu; [|exact Ez]. cbn [FOfree_in].
        rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz. }
      subst z. rewrite (FOin_tm_var_ne y u Hzy). reflexivity.
    + apply IHB; [lia|]. intros z Hz. unfold h_hide.
      destruct (Nat.eqb_spec z y) as [->|Hzy]; intros Ez; [lia|].
      apply Hu; [|exact Ez]. cbn [FOfree_in].
      rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
  - cbn [FOsubst_ok]. destruct (Nat.eqb_spec y w) as [->|Hyw]; [reflexivity|].
    destruct (FOfree_in w (hsub_f (h_hide y h) B)) eqn:E; [|reflexivity].
    apply andb_true_intro. split.
    + destruct (FOfree_in_hsub B (h_hide y h) w E) as [z [Hz Ez]]. revert Ez. unfold h_hide.
      destruct (Nat.eqb_spec z y) as [->|Hzy]; intros Ez; [lia|].
      assert (Hzu : z = u).
      { apply Hu; [|exact Ez]. cbn [FOfree_in].
        rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz. }
      subst z. rewrite (FOin_tm_var_ne y u Hzy). reflexivity.
    + apply IHB; [lia|]. intros z Hz. unfold h_hide.
      destruct (Nat.eqb_spec z y) as [->|Hzy]; intros Ez; [lia|].
      apply Hu; [|exact Ez]. cbn [FOfree_in].
      rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
Qed.

(** ** The substituted provability formula.

    [SPF Q c xs ys R]: some [Q] is the code obtained from [c] by the
    numerals of [ys] at [xs], and [R] holds of it. *)

Definition SPF (Q : nat) (c : FOTerm) (xs : list nat) (ys : list FOTerm) (R : FOFormula)
    : FOFormula :=
  FOExists Q (FOAnd (FOSUBNUMS (S Q) c xs ys (FOVar Q)) R).

Lemma SPF_subst : forall Q c xs ys R w s,
  1000 <= Q -> S Q + 3 * length xs <= w -> FOin_tm w c = false -> FOfree_in w R = false ->
  FOsubst_f w s (SPF Q c xs ys R) = SPF Q c xs (map (FOsubst_t w s) ys) R.
Proof.
  intros Q c xs ys R w s HQ Hw Hc HR. unfold SPF.
  rewrite FOsubst_f_ex_ne by lia. rewrite FOsubst_f_and, FOsubst_f_SUBNUMS by lia.
  rewrite (FOsubst_t_not_in c w s Hc), FOsubst_t_var_ne by lia.
  rewrite (FOsubst_f_not_free R w s HR). reflexivity.
Qed.

Lemma SPF_ok : forall Q c xs ys R w u,
  1000 <= Q -> S Q + 3 * length xs <= w -> u < Q -> FOin_tm w c = false ->
  FOtms_avoid [c] 13 18 -> FOfree_in w R = false ->
  FOsubst_ok w (FOVar u) (SPF Q c xs ys R) = true.
Proof.
  intros Q c xs ys R w u HQ Hw Hu Hc Hc13 HR. unfold SPF.
  apply FOsubst_ok_ex; [apply FOin_tm_var_ne; lia|].
  apply FOsubst_ok_and; [|apply FOsubst_ok_not_free; exact HR].
  apply FOsubst_ok_SUBNUMS; [lia | lia | lia | exact Hc13 | avoid_tms | right; exact Hc].
Qed.

Lemma SPF_free : forall Q c xs ys R w,
  1000 <= Q -> FOtms_avoid [c] 13 18 -> FOtms_avoid (c :: ys) w (S w) ->
  (w = Q \/ FOfree_in w R = false) -> FOfree_in w (SPF Q c xs ys R) = false.
Proof.
  intros Q c xs ys R w HQ Hc Hav HR. unfold SPF. cbn [FOfree_in].
  destruct (Nat.eqb_spec Q w) as [_|HQw]; [reflexivity|].
  rewrite fv_and. apply Bool.orb_false_iff. split.
  - apply FOfree_in_SUBNUMS; [lia | exact Hc|]. avoid_tms.
  - destruct HR as [HR|HR]; [lia | exact HR].
Qed.

(** ** Putting the variables back for the holders, one at a time. *)

Definition HPhi (Hb : nat) (R0 : list nat) (A : FOFormula) (Q : nat) (c : FOTerm)
    (xs : list nat) (R : FOFormula) : FOFormula :=
  FOImplF (hsub_f (hR Hb R0) A) (SPF Q c xs (map (fun z => FOVar (hR Hb R0 z)) xs) R).

Lemma rename_step : forall Hb R0 x A Q c xs R,
  1000 <= Q -> FOvars_max A < Q -> S Q + 3 * length xs <= Hb ->
  (forall z, In z xs -> z <= FOvars_max A) -> In x xs ->
  (forall w, FOin_tm w c = false) -> FOtms_avoid [c] 13 18 ->
  (forall w, w <> Q -> FOfree_in w R = false) ->
  FOProvesTn 0 (HPhi Hb R0 A Q c xs R) -> FOProvesTn 0 (HPhi Hb (x :: R0) A Q c xs R).
Proof.
  intros Hb R0 x A Q c xs R HQ HAQ HHb Hxs Hx Hc Hc13 HR H.
  pose proof (Hxs x Hx) as HxM.
  assert (Hfree : forall z, FOfree_in z A = true -> z <= FOvars_max A).
  { intros z Hz. destruct (Nat.le_gt_cases z (FOvars_max A)) as [Hle|Hgt]; [exact Hle|].
    rewrite (FOfree_in_above A z Hgt) in Hz. discriminate. }
  change (FOPrH 0 [] (HPhi Hb R0 A Q c xs R)) in H.
  apply (FOPrH_all_intro 0 [] (Hb + x)) in H; [|apply FOfree_ctx_nil].
  apply (FOPrH_inst 0 [] (Hb + x) (FOVar x)) in H.
  - unfold HPhi in H. rewrite FOsubst_f_impl in H.
    rewrite hsub_f_rename in H by lia.
    rewrite SPF_subst in H by (lia || apply Hc || apply HR; lia).
    rewrite map_map in H.
    rewrite (hsub_f_ext A _ (hR Hb (x :: R0))) in H
      by (intros z Hz; apply hR_step; pose proof (Hfree z Hz); lia).
    rewrite (map_ext_in _ (fun z => FOVar (hR Hb (x :: R0) z)) xs) in H.
    + exact H.
    + intros z Hz. cbn beta.
      change (FOVar (hR Hb R0 z)) with (hsub_tm (hR Hb R0) (FOVar z)).
      rewrite hsub_tm_rename. cbn [hsub_tm]. rewrite hR_step; [reflexivity|].
      pose proof (Hxs z Hz). lia.
  - unfold HPhi. apply FOsubst_ok_impl.
    + apply hsub_f_rename_ok; [lia|]. intros z Hz Ez. unfold hR in Ez.
      pose proof (Hfree z Hz) as HzM.
      destruct (existsb (Nat.eqb z) R0); lia.
    + apply SPF_ok; [lia | lia | lia | apply Hc | exact Hc13 | apply HR; lia].
Qed.

Lemma rename_all : forall L Hb R0 A Q c xs R,
  1000 <= Q -> FOvars_max A < Q -> S Q + 3 * length xs <= Hb ->
  (forall z, In z xs -> z <= FOvars_max A) -> (forall x, In x L -> In x xs) ->
  (forall w, FOin_tm w c = false) -> FOtms_avoid [c] 13 18 ->
  (forall w, w <> Q -> FOfree_in w R = false) ->
  FOProvesTn 0 (HPhi Hb R0 A Q c xs R) -> FOProvesTn 0 (HPhi Hb (L ++ R0) A Q c xs R).
Proof.
  induction L as [|x L IH]; intros Hb R0 A Q c xs R HQ HAQ HHb Hxs HL Hc Hc13 HR H;
    [exact H|].
  cbn [app]. apply rename_step; try assumption.
  - apply HL. left. reflexivity.
  - apply IH; try assumption. intros x' Hx'. apply HL. right. exact Hx'.
Qed.

(** ** The formula with holders, derived.

    Variable layout: the code variable [subq A], the chain from
    [S (subq A)], the holders from [subHb A], the numeral codes of the
    holders from [Mb], the code of the instance at [V + 3], the fresh
    names of the chain from [V + 4], and the pattern bases above them. *)

Definition subq (A : FOFormula) : nat := 2001 + FOvars_max A.

Definition subHb (A : FOFormula) : nat := S (subq A) + 3 * length (fvs A).

Lemma fvs_le : forall A z, In z (fvs A) -> z <= FOvars_max A.
Proof.
  intros A z Hz. apply fvs_spec in Hz.
  destruct (Nat.le_gt_cases z (FOvars_max A)) as [Hle|Hgt]; [exact Hle|].
  rewrite (FOfree_in_above A z Hgt) in Hz. discriminate.
Qed.

Lemma open_core : forall k A, FOsigma1 A ->
  FOProvesTn 0 (HPhi (subHb A) [] A (subq A) (FOnumeral (FOcode_f A)) (fvs A)
                  (FOPRu (FOPrCores k) (FOu0 k) (FOVar (subq A)))).
Proof.
  intros k A HA. unfold HPhi.
  set (M := FOvars_max A). set (Q := subq A). set (xs := fvs A). set (m := length xs).
  set (Hb := subHb A). set (h := hR Hb []).
  set (Mb := Hb + S M). set (V := Mb + m).
  set (ts := map (fun z => FOVar (h z)) xs).
  set (env := map FOVar (seq Mb m)).
  set (rho := rho_seq xs 0 (fun _ => None)).
  set (R := FOPRu (FOPrCores k) (FOu0 k) (FOVar Q)).
  assert (EM : M = FOvars_max A) by reflexivity.
  assert (EQ : Q = 2001 + M) by reflexivity.
  assert (EHb : Hb = S Q + 3 * m) by reflexivity.
  assert (Eh : forall z, h z = Hb + z) by reflexivity.
  assert (Ets : length ts = m) by (unfold ts; rewrite length_map; reflexivity).
  assert (Eenv : length env = m) by (unfold env; rewrite length_map, length_seq; reflexivity).
  assert (HxM : forall z, In z xs -> z <= M) by (intros z Hz; exact (fvs_le A z Hz)).
  assert (Hxs : forall z, FOfree_in z A = true -> In z xs)
    by (intros z Hz; apply fvs_spec; exact Hz).
  assert (HtsR : forall t, In t ts -> forall w, w < Hb \/ Hb + S M <= w -> FOin_tm w t = false).
  { intros t Ht w Hw. unfold ts in Ht. apply in_map_iff in Ht. destruct Ht as [z [<- Hz]].
    apply FOin_tm_var_ne. rewrite Eh. pose proof (HxM z Hz). lia. }
  assert (HenvR : forall t, In t env -> forall w, w < Mb \/ Mb + m <= w -> FOin_tm w t = false).
  { intros t Ht w Hw. unfold env in Ht. apply in_map_iff in Ht. destruct Ht as [j [<- Hj]].
    apply in_seq in Hj. apply FOin_tm_var_ne. lia. }
  assert (HhA : forall w, w < Hb \/ Hb + S M <= w -> FOfree_in w (hsub_f h A) = false).
  { intros w Hw. destruct (FOfree_in w (hsub_f h A)) eqn:E; [|reflexivity].
    destruct (FOfree_in_hsub A h w E) as [z [Hz Ez]]. rewrite Eh in Ez.
    pose proof (HxM z (Hxs z Hz)). lia. }
  change (FOPrH 0 [] (FOImplF (hsub_f h A) (SPF Q (FOnumeral (FOcode_f A)) xs ts R))).
  apply FOPrH_intro. cbn [app].
  apply (numr_exs ts 0 [hsub_f h A] Mb).
  { intros t Ht w ? ?. apply HtsR; [exact Ht | lia]. }
  { lia. }
  { intros w' Hw'. apply FOfree_ctx_cons; [apply HhA; lia | apply FOfree_ctx_nil]. }
  { intros w' Hw'. apply SPF_free; [lia | avoid_tms | | right].
    - apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|].
      intros t Ht w ? ?. apply HtsR; [exact Ht | lia].
    - unfold R. apply FOfree_in_PRu_all; [avoid_tms | avoid_tm]. }
  { intros t Ht w' Hw'. apply HtsR; [exact Ht | lia]. }
  set (Gm := [hsub_f h A] ++ numr_ctx ts Mb).
  assert (HGmw : forall w, w < Hb \/ V <= w -> FOfree_ctx w Gm).
  { intros w Hw. apply FOfree_ctx_app_inv.
    - apply FOfree_ctx_cons; [apply HhA; lia | apply FOfree_ctx_nil].
    - apply numr_ctx_free; [| | | lia | rewrite Ets; lia];
        intros t Ht w0 ? ?; apply HtsR; [exact Ht | lia | exact Ht | lia | exact Ht | lia]. }
  assert (HGm0 : FOctx_avoid Gm 0 1000) by (intros w ? ?; apply HGmw; lia).
  assert (HGmV : forall w, V <= w -> FOfree_ctx w Gm) by (intros w ?; apply HGmw; lia).
  assert (HGmN : forall i, i < m -> FOPrH 0 Gm (FONUMR (nth i ts FOZero) (nth i env FOZero))).
  { intros i Hi. apply FOPrH_assum. unfold Gm. apply in_or_app. right.
    unfold env. rewrite <- Ets. apply numr_ctx_nth. lia. }
  assert (HI : Inv 0 V Gm h rho env (fun x => FOfree_in x A = true)).
  { split; [lia|]. split; [exact HGm0|]. split; [exact HGmV|].
    split; [|split; [|split]].
    - split; [split|split; [|split]].
      + intros w ? ?. apply HGm0; lia.
      + intros i Hi. exists (nth i ts FOZero). apply HGmN. lia.
      + intros t Ht w ? ?. apply HenvR; [exact Ht | lia].
      + lia.
      + intros t Ht w Hw. apply HenvR; [exact Ht | lia].
    - intros t Ht w ? ?. apply HenvR; [exact Ht | lia].
    - intros z i Hz.
      pose proof (rho_seq_range xs 0 (fun _ => None)
                    ltac:(intros z' i' Hz'; discriminate Hz') z i Hz). lia.
    - intros x Hx. pose proof (Hxs x Hx) as Hx'.
      destruct (In_nth_error xs x Hx') as [i Hi].
      assert (Hil : i < m) by (apply nth_error_Some; rewrite Hi; discriminate).
      exists i. split; [exact (rho_seq_nth xs 0 _ i x (fvs_nodup A) Hi)|].
      split; [lia|]. split.
      + assert (Eti : nth i ts FOZero = FOVar (h x)).
        { apply nth_error_nth. unfold ts. rewrite nth_error_map, Hi. reflexivity. }
        rewrite <- Eti. apply HGmN. exact Hil.
      + rewrite Eh. pose proof (HxM x Hx'). lia. }
  pose proof (S1P_all 0 k (S M) A HA ltac:(lia) V Gm h rho env HI
                ltac:(intros x Hx; rewrite Eh; lia)
                ltac:(apply FOPrH_assum; apply in_or_app; left; left; reflexivity)) as HP.
  set (F := V + 4). set (Bc := F + 4 * m + 4). set (Ba := Bc + cpat_span (cpat_f rho A)).
  assert (EF : F = V + 4) by reflexivity.
  assert (EBc : Bc = F + 4 * m + 4) by reflexivity.
  assert (EBa : Ba = Bc + cpat_span (cpat_f rho A)) by reflexivity.
  pose proof (FOPrH_patf_total (cpat_f rho A) 0 Gm Bc env V ltac:(lia) ltac:(lia)
                ltac:(intros w ? ?; apply HGmV; lia) ltac:(intros w ? ?; apply HGm0; lia)
                ltac:(intros t Ht w ? ?; apply HenvR; [exact Ht | lia])
                ltac:(intros t Ht w ? ?; apply HenvR; [exact Ht | lia])
                ltac:(intros t Ht w ? ?; apply HenvR; [exact Ht | lia])) as Hex.
  refine (FOPrH_exe 0 Gm V (V + 3) _ _ Hex _ _ _ _ _).
  { apply HGmV. lia. }
  { apply SPF_free; [lia | avoid_tms | | right].
    - apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|].
      intros t Ht w ? ?. apply HtsR; [exact Ht | lia].
    - unfold R. apply FOfree_in_PRu_all; [avoid_tms | avoid_tm]. }
  { apply FOfree_in_PATF_any; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
    intros t Ht w ? ?. apply HenvR; [exact Ht | lia]. }
  { apply FOsubst_ok_PATF. apply FOtm_avoid_var. lia. }
  rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
  rewrite (FOsubst_map_avoid V (FOVar (V + 3)) env)
    by (intros t Ht; apply HenvR; [exact Ht | lia]).
  set (Gc := Gm ++ [FOPATF Bc env (cpat_f rho A) (FOVar (V + 3))]).
  assert (Hinc : forall X, In X Gm -> In X Gc)
    by (intros X HX; apply in_or_app; left; exact HX).
  assert (HGcw : forall w, w < Hb \/ Bc <= w -> FOfree_ctx w Gc).
  { intros w Hw. apply FOfree_ctx_app_inv; [apply HGmw; lia|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
    destruct (Nat.lt_ge_cases w 2) as [Hw2|Hw2].
    - apply FOfree_in_PATF_lo; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      intros t Ht w0 ? ?. apply HenvR; [exact Ht | lia].
    - apply FOfree_in_PATF_any; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      intros t Ht w0 ? ?. apply HenvR; [exact Ht | lia]. }
  assert (HGcF : forall w, F <= w -> FOfree_ctx w Gc).
  { intros w Hw. apply FOfree_ctx_app_inv; [apply HGmV; lia|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
    apply FOfree_in_PATF_any; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
    intros t Ht w0 ? ?. apply HenvR; [exact Ht | lia]. }
  assert (HGc0 : FOctx_avoid Gc 0 1000) by (intros w ? ?; apply HGcw; lia).
  pose proof (HP Gc Bc (FOVar (V + 3)) Hinc HGc0 ltac:(avoid_tms) ltac:(lia)
                ltac:(split; [intros w ?; apply HGcF; lia
                             | intros t [<-|[]] w ?; apply FOin_tm_var_ne; lia])
                ltac:(unfold Gc; apply FOPrH_last)) as HPR.
  assert (HCH : FOPrH 0 Gc (FOSUBNUMS (S Q) (FOnumeral (FOcode_f A)) xs ts (FOVar (V + 3)))).
  { refine (SUBNUMS_chain xs 0 A Gc (fun _ => None) [] env ts (FOnumeral (FOcode_f A)) (FOVar (V + 3)) (S Q)
              Ba Bc F (fvs_nodup A) _ _ _ _ HGc0 HGcF _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    - rewrite Eenv. reflexivity.
    - rewrite Ets. reflexivity.
    - intros x _. reflexivity.
    - intros z i Hz. discriminate Hz.
    - intros i Hi. cbn [length] in Hi. lia.
    - intros i Hi. exact (FOPrH_weaken 0 Gm Gc _ Hinc (HGmN i Hi)).
    - apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|]. avoid_tms.
    - intros t Ht w ? ?. apply HtsR; [exact Ht | lia].
    - intros t Ht w ? ?. apply HenvR; [exact Ht | lia].
    - apply FOtms_avoid_nil.
    - intros t [<-|[<-|[]]] w Hw; [apply FOin_tm_numeral | apply FOin_tm_var_ne; lia].
    - intros t Ht w Hw. apply HtsR; [exact Ht | lia].
    - intros t Ht w Hw. apply HenvR; [exact Ht | lia].
    - intros t [].
    - lia.
    - lia.
    - lia.
    - cbn [length]. change (rho_seq xs 0 (fun _ => None)) with rho. lia.
    - exact (FOPrH_patf_closed_code 0 Gc A Ba ltac:(lia)).
    - cbn [length app]. unfold Gc. apply FOPrH_last. }
  unfold SPF.
  apply (FOPrH_ex_intro _ _ Q (FOVar (V + 3))).
  { apply FOsubst_ok_and.
    - apply FOsubst_ok_SUBNUMS; [lia | lia | lia | avoid_tms | avoid_tms | left; avoid_tms].
    - unfold R. apply FOsubst_ok_PRu; [lia | avoid_tm | right; avoid_tm | avoid_tm]. }
  rewrite FOsubst_f_and, FOsubst_f_SUBNUMS by lia.
  rewrite FOsubst_t_numeral, FOsubst_t_var_eq'.
  rewrite (FOsubst_map_avoid Q (FOVar (V + 3)) ts)
    by (intros t Ht; apply HtsR; [exact Ht | lia]).
  unfold R. rewrite FOsubst_f_PRu by (lia || avoid_tms). rewrite FOsubst_t_var_eq'.
  apply FOPrH_and_intro; [exact HCH | exact HPR].
Qed.

(** ** Provable Sigma_1-completeness with free variables. *)

Definition FOSubProv (k : nat) (A : FOFormula) : FOFormula :=
  SPF (subq A) (FOnumeral (FOcode_f A)) (fvs A) (map FOVar (fvs A))
    (FOPRu (FOPrCores k) (FOu0 k) (FOVar (subq A))).

Theorem provable_sigma1_open : forall k A, FOsigma1 A ->
  FOProvesTn 0 (FOImplF A (FOSubProv k A)).
Proof.
  intros k A HA.
  pose proof (rename_all (fvs A) (subHb A) [] A (subq A) (FOnumeral (FOcode_f A)) (fvs A)
                (FOPRu (FOPrCores k) (FOu0 k) (FOVar (subq A)))
                ltac:(unfold subq; lia) ltac:(unfold subq; lia) ltac:(unfold subHb; lia)
                (fvs_le A) (fun x Hx => Hx) ltac:(intros w; apply FOin_tm_numeral)
                ltac:(avoid_tms)
                ltac:(intros w Hw; apply FOfree_in_PRu_all;
                      [intros t [<-|[]] v ? ?; apply FOin_tm_var_ne; lia | avoid_tm])
                (open_core k A HA)) as H1.
  rewrite app_nil_r in H1. unfold HPhi in H1.
  rewrite (hsub_f_ext A (hR (subHb A) (fvs A)) (fun z => z)) in H1
    by (intros z Hz; apply hR_all; apply fvs_spec; exact Hz).
  rewrite hsub_f_id in H1 by reflexivity.
  rewrite (map_ext_in (fun z => FOVar (hR (subHb A) (fvs A) z)) FOVar (fvs A)) in H1
    by (intros z Hz; rewrite hR_all by exact Hz; reflexivity).
  exact H1.
Qed.

(** ** Table rows in the standard model.

    [TBLsem]: some valid table holds the row; [tbl_sound] then gives
    the row's meaning [mspec]. *)

Definition TBLsem (vtg va1 va2 va3 vr : nat) : Prop :=
  exists vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen,
    (forall j, j < vlen ->
       dispatch_sem (tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen)
         vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr j) /\
    tblL vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen vtg va1 va2 va3 vr.

Lemma TBLsem_mspec : forall tg a1 a2 a3 r, TBLsem tg a1 a2 a3 r -> mspec tg a1 a2 a3 r.
Proof.
  intros tg a1 a2 a3 r [vct [vdt [vc1 [vd1 [vc2 [vd2 [vc3 [vd3 [vcr [vdr [vlen [Hv Hr]]]]]]]]]]]].
  exact (tbl_sound vct vdt vc1 vd1 vc2 vd2 vc3 vd3 vcr vdr vlen Hv tg a1 a2 a3 r Hr).
Qed.

Lemma FOsat_TBLEX_ph : forall e,
  FOsat e (FOTBLEX (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16) (FOVar 17)) ->
  TBLsem (e 13) (e 14) (e 15) (e 16) (e 17).
Proof.
  intros e H. unfold FOTBLEX in H. cbn [FOsat] in H.
  destruct H as [v2 [v3 [v4 [v5 [v6 [v7 [v8 [v9 [v10 [v11 [v12 H]]]]]]]]]]].
  apply FOsat_FOAnd in H. destruct H as [Hv Hl].
  pose proof (proj1 (FOsat_FOTBLVALID _ 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
                       (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
                       ltac:(unfold tbl_below; cbn; lia)) Hv) as Hv'.
  clear Hv. rename Hv' into Hv.
  apply (proj1 (FOsat_FOlookup _ 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
                  (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
                  (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16) (FOVar 17)
                  ltac:(unfold tbl_below; cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia)
                  ltac:(cbn; lia) ltac:(cbn; lia) ltac:(cbn; lia))) in Hl.
  cbn [FOeval FOupdate Nat.eqb] in Hv, Hl.
  exists v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12. split; [exact Hv | exact Hl].
Qed.

Lemma FOsat_TBLEX : forall e tg a1 a2 a3 r,
  FOtms_avoid [tg; a1; a2; a3; r] 2 50 -> FOsat e (FOTBLEX tg a1 a2 a3 r) ->
  TBLsem (FOeval e tg) (FOeval e a1) (FOeval e a2) (FOeval e a3) (FOeval e r).
Proof.
  intros e tg a1 a2 a3 r Hav H.
  assert (E1 : FOTBLEX tg a1 a2 a3 r = FOsubst_f 13 tg (FOTBLEX (FOVar 13) a1 a2 a3 r)).
  { rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq'.
    rewrite (FOsubst_t_not_in a1 13 tg), (FOsubst_t_not_in a2 13 tg),
      (FOsubst_t_not_in a3 13 tg), (FOsubst_t_not_in r 13 tg) by fr_tm. reflexivity. }
  rewrite E1 in H.
  pose proof (proj1 (FOsat_subst_f (FOTBLEX (FOVar 13) a1 a2 a3 r) 13 tg e
                       ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])) H) as H1.
  clear H. rename H1 into H.
  set (e1 := FOupdate e 13 (FOeval e tg)) in H.
  assert (E2 : FOTBLEX (FOVar 13) a1 a2 a3 r =
               FOsubst_f 14 a1 (FOTBLEX (FOVar 13) (FOVar 14) a2 a3 r)).
  { rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq', (FOsubst_t_var_ne 14 a1 13) by lia.
    rewrite (FOsubst_t_not_in a2 14 a1), (FOsubst_t_not_in a3 14 a1),
      (FOsubst_t_not_in r 14 a1) by fr_tm. reflexivity. }
  rewrite E2 in H.
  pose proof (proj1 (FOsat_subst_f (FOTBLEX (FOVar 13) (FOVar 14) a2 a3 r) 14 a1 e1
                       ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])) H) as H1.
  clear H. rename H1 into H.
  set (e2 := FOupdate e1 14 (FOeval e1 a1)) in H.
  assert (E3 : FOTBLEX (FOVar 13) (FOVar 14) a2 a3 r =
               FOsubst_f 15 a2 (FOTBLEX (FOVar 13) (FOVar 14) (FOVar 15) a3 r)).
  { rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq', (FOsubst_t_var_ne 15 a2 13),
      (FOsubst_t_var_ne 15 a2 14) by lia.
    rewrite (FOsubst_t_not_in a3 15 a2), (FOsubst_t_not_in r 15 a2) by fr_tm. reflexivity. }
  rewrite E3 in H.
  pose proof (proj1 (FOsat_subst_f (FOTBLEX (FOVar 13) (FOVar 14) (FOVar 15) a3 r) 15 a2 e2
                       ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])) H) as H1.
  clear H. rename H1 into H.
  set (e3 := FOupdate e2 15 (FOeval e2 a2)) in H.
  assert (E4 : FOTBLEX (FOVar 13) (FOVar 14) (FOVar 15) a3 r =
               FOsubst_f 16 a3 (FOTBLEX (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16) r)).
  { rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq', (FOsubst_t_var_ne 16 a3 13),
      (FOsubst_t_var_ne 16 a3 14), (FOsubst_t_var_ne 16 a3 15) by lia.
    rewrite (FOsubst_t_not_in r 16 a3) by fr_tm. reflexivity. }
  rewrite E4 in H.
  pose proof (proj1 (FOsat_subst_f (FOTBLEX (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16) r) 16 a3
                       e3 ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])) H) as H1.
  clear H. rename H1 into H.
  set (e4 := FOupdate e3 16 (FOeval e3 a3)) in H.
  assert (E5 : FOTBLEX (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16) r =
               FOsubst_f 17 r (FOTBLEX (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16) (FOVar 17))).
  { rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq', (FOsubst_t_var_ne 17 r 13),
      (FOsubst_t_var_ne 17 r 14), (FOsubst_t_var_ne 17 r 15), (FOsubst_t_var_ne 17 r 16) by lia.
    reflexivity. }
  rewrite E5 in H.
  pose proof (proj1 (FOsat_subst_f
                       (FOTBLEX (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16) (FOVar 17)) 17 r
                       e4 ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])) H) as H1.
  clear H. rename H1 into H.
  set (e5 := FOupdate e4 17 (FOeval e4 r)) in H.
  apply FOsat_TBLEX_ph in H.
  assert (Q1 : e5 13 = FOeval e tg) by reflexivity.
  assert (Q2 : e5 14 = FOeval e a1).
  { transitivity (FOeval e1 a1); [reflexivity|]. unfold e1.
    apply FOeval_update_not_in. fr_tm. }
  assert (Q3 : e5 15 = FOeval e a2).
  { transitivity (FOeval e2 a2); [reflexivity|]. unfold e2, e1.
    rewrite !FOeval_update_not_in by fr_tm. reflexivity. }
  assert (Q4 : e5 16 = FOeval e a3).
  { transitivity (FOeval e3 a3); [reflexivity|]. unfold e3, e2, e1.
    rewrite !FOeval_update_not_in by fr_tm. reflexivity. }
  assert (Q5 : e5 17 = FOeval e r).
  { transitivity (FOeval e4 r); [reflexivity|]. unfold e4, e3, e2, e1.
    rewrite !FOeval_update_not_in by fr_tm. reflexivity. }
  rewrite Q1, Q2, Q3, Q4, Q5 in H. exact H.
Qed.

(** ** The substitution chain in the standard model. *)

Fixpoint FOsubsts (A : FOFormula) (xs : list nat) (ts : list FOTerm) : FOFormula :=
  match xs, ts with
  | x :: xs', t :: ts' => FOsubsts (FOsubst_f x t A) xs' ts'
  | _, _ => A
  end.

Lemma SUBNUMS_sound : forall xs ys q c r e P,
  1000 <= q -> FOtms_avoid (c :: r :: ys) q (q + 3 * length xs) -> FOtms_avoid [c] 2 50 ->
  FOsat e (FOSUBNUMS q c xs ys r) -> FOeval e c = FOcode_f P ->
  FOeval e r = FOcode_f (FOsubsts P xs (map (fun y => FOnumeral (FOeval e y)) ys)).
Proof.
  induction xs as [|x xs IH]; intros ys q c r e P Hq Hav Hc H HP.
  - destruct ys; cbn [FOSUBNUMS FOsat FOsubsts map] in *; lia.
  - destruct ys as [|y ys].
    + cbn [FOSUBNUMS FOsat FOsubsts map] in *. lia.
    + cbn [FOSUBNUMS length] in H, Hav. cbn [FOsat] in H.
      destruct H as [va [vm [vz H]]].
      set (e3 := FOupdate (FOupdate (FOupdate e q va) (S q) vm) (S (S q)) vz) in H.
      assert (Ee3 : forall t, In t (c :: r :: y :: ys) -> FOeval e3 t = FOeval e t).
      { intros t Ht. unfold e3.
        rewrite (FOeval_update_not_in t _ (S (S q)) vz) by (apply (Hav t Ht); lia).
        rewrite (FOeval_update_not_in t _ (S q) vm) by (apply (Hav t Ht); lia).
        rewrite (FOeval_update_not_in t _ q va) by (apply (Hav t Ht); lia). reflexivity. }
      assert (Ez : e3 (S (S q)) = vz) by (unfold e3; apply FOupdate_eq).
      assert (Em : e3 (S q) = vm).
      { unfold e3. rewrite FOupdate_neq by lia. apply FOupdate_eq. }
      assert (Ea : e3 q = va).
      { unfold e3. rewrite !FOupdate_neq by lia. apply FOupdate_eq. }
      apply FOsat_FOAnd in H. destruct H as [Hz H].
      apply FOsat_FOAnd in H. destruct H as [Hn H].
      apply FOsat_FOAnd in H. destruct H as [Ht Hr].
      cbn [FOsat FOeval] in Hz. rewrite Ez, (Ee3 y ltac:(in_list)) in Hz.
      unfold FONUMR in Hn. apply FOsat_FOAnd in Hn. destruct Hn as [Hn _].
      apply FOsat_TBLEX in Hn; [|avoid_tms]. apply TBLsem_mspec in Hn.
      rewrite FOeval_numeral in Hn. cbn [FOeval] in Hn. rewrite Ez, Em in Hn.
      cbn [mspec] in Hn.
      apply FOsat_TBLEX in Ht; [|avoid_tms]. apply TBLsem_mspec in Ht.
      rewrite !FOeval_numeral in Ht. cbn [FOeval] in Ht. rewrite Em, Ea in Ht.
      cbn [mspec] in Ht.
      specialize (Ht (FOnumeral vz) P Hn ltac:(rewrite (Ee3 c ltac:(in_list)); exact HP)).
      pose proof (IH ys (S (S (S q))) (FOVar q) r e3 (FOsubst_f x (FOnumeral vz) P)
                    ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms) Hr
                    ltac:(cbn [FOeval]; rewrite Ea; exact Ht)) as E.
      rewrite (Ee3 r ltac:(in_list)) in E. rewrite E.
      cbn [map FOsubsts]. rewrite Hz. f_equal. f_equal.
      apply map_ext_in. intros t Htl. rewrite (Ee3 t ltac:(right; right; right; exact Htl)).
      reflexivity.
Qed.

(** ** The provability formula at a variable. *)

Lemma FOsat_PRu_var : forall e cores u0 Q, 252 <= Q ->
  FOsat e (FOPRu cores u0 (FOVar Q)) <-> FOsat e (FOPRu cores u0 (FOnumeral (e Q))).
Proof.
  intros e cores u0 Q HQ.
  rewrite (FOPRu_as_subst cores u0 (FOVar Q)) by (right; avoid_tm).
  rewrite (FOPRu_as_subst cores u0 (FOnumeral (e Q))) by (right; avoid_tm).
  rewrite (FOsat_subst_f (FOsubst_f 1 (FOVar Q) (FOPRMAT cores)) 0 (FOnumeral u0) e
             (FOsubst_ok_numeral _ _ _)).
  rewrite (FOsat_subst_f (FOsubst_f 1 (FOnumeral (e Q)) (FOPRMAT cores)) 0 (FOnumeral u0) e
             (FOsubst_ok_numeral _ _ _)).
  rewrite FOeval_numeral.
  rewrite (FOsat_subst_f (FOPRMAT cores) 1 (FOVar Q) (FOupdate e 0 u0)
             (FOsubst_ok_PRMAT1 cores (FOVar Q) ltac:(avoid_tm))).
  rewrite (FOsat_subst_f (FOPRMAT cores) 1 (FOnumeral (e Q)) (FOupdate e 0 u0)
             (FOsubst_ok_numeral _ _ _)).
  rewrite FOeval_numeral. cbn [FOeval]. rewrite FOupdate_neq by lia. reflexivity.
Qed.

(** ** The substitution chain is total.

    The same derivation as [open_core] with the true hypothesis
    [A -> A] and the code equal to itself in place of provability. *)

Lemma tot_core : forall A,
  FOProvesTn 0 (HPhi (subHb A) [] (FOImplF A A) (subq A) (FOnumeral (FOcode_f A)) (fvs A)
                  (FOEq (FOVar (subq A)) (FOVar (subq A)))).
Proof.
  intros A. unfold HPhi.
  set (M := FOvars_max A). set (Q := subq A). set (xs := fvs A). set (m := length xs).
  set (Hb := subHb A). set (h := hR Hb []).
  set (Mb := Hb + S M). set (V := Mb + m).
  set (ts := map (fun z => FOVar (h z)) xs).
  set (env := map FOVar (seq Mb m)).
  set (rho := rho_seq xs 0 (fun _ => None)).
  set (R := FOEq (FOVar Q) (FOVar Q)).
  assert (EM : M = FOvars_max A) by reflexivity.
  assert (EQ : Q = 2001 + M) by reflexivity.
  assert (EHb : Hb = S Q + 3 * m) by reflexivity.
  assert (Eh : forall z, h z = Hb + z) by reflexivity.
  assert (Ets : length ts = m) by (unfold ts; rewrite length_map; reflexivity).
  assert (Eenv : length env = m) by (unfold env; rewrite length_map, length_seq; reflexivity).
  assert (HxM : forall z, In z xs -> z <= M) by (intros z Hz; exact (fvs_le A z Hz)).
  assert (Hxs : forall z, FOfree_in z A = true -> In z xs)
    by (intros z Hz; apply fvs_spec; exact Hz).
  assert (HtsR : forall t, In t ts -> forall w, w < Hb \/ Hb + S M <= w -> FOin_tm w t = false).
  { intros t Ht w Hw. unfold ts in Ht. apply in_map_iff in Ht. destruct Ht as [z [<- Hz]].
    apply FOin_tm_var_ne. rewrite Eh. pose proof (HxM z Hz). lia. }
  assert (HenvR : forall t, In t env -> forall w, w < Mb \/ Mb + m <= w -> FOin_tm w t = false).
  { intros t Ht w Hw. unfold env in Ht. apply in_map_iff in Ht. destruct Ht as [j [<- Hj]].
    apply in_seq in Hj. apply FOin_tm_var_ne. lia. }
  assert (HhA : forall w, w < Hb \/ Hb + S M <= w ->
                  FOfree_in w (hsub_f h (FOImplF A A)) = false).
  { intros w Hw. cbn [hsub_f FOfree_in].
    destruct (FOfree_in w (hsub_f h A)) eqn:E; [|reflexivity].
    destruct (FOfree_in_hsub A h w E) as [z [Hz Ez]]. rewrite Eh in Ez.
    pose proof (HxM z (Hxs z Hz)). lia. }
  assert (HRw : forall w, w <> Q -> FOfree_in w R = false).
  { intros w Hw. unfold R. cbn [FOfree_in]. rewrite !FOin_tm_var_ne by lia. reflexivity. }
  change (FOPrH 0 [] (FOImplF (hsub_f h (FOImplF A A))
                        (SPF Q (FOnumeral (FOcode_f A)) xs ts R))).
  apply FOPrH_intro. cbn [app].
  apply (numr_exs ts 0 [hsub_f h (FOImplF A A)] Mb).
  { intros t Ht w ? ?. apply HtsR; [exact Ht | lia]. }
  { lia. }
  { intros w' Hw'. apply FOfree_ctx_cons; [apply HhA; lia | apply FOfree_ctx_nil]. }
  { intros w' Hw'. apply SPF_free; [lia | avoid_tms | | right; apply HRw; lia].
    apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|].
    intros t Ht w ? ?. apply HtsR; [exact Ht | lia]. }
  { intros t Ht w' Hw'. apply HtsR; [exact Ht | lia]. }
  set (Gm := [hsub_f h (FOImplF A A)] ++ numr_ctx ts Mb).
  assert (HGmw : forall w, w < Hb \/ V <= w -> FOfree_ctx w Gm).
  { intros w Hw. apply FOfree_ctx_app_inv.
    - apply FOfree_ctx_cons; [apply HhA; lia | apply FOfree_ctx_nil].
    - apply numr_ctx_free; [| | | lia | rewrite Ets; lia];
        intros t Ht w0 ? ?; apply HtsR; [exact Ht | lia | exact Ht | lia | exact Ht | lia]. }
  assert (HGm0 : FOctx_avoid Gm 0 1000) by (intros w ? ?; apply HGmw; lia).
  assert (HGmV : forall w, V <= w -> FOfree_ctx w Gm) by (intros w ?; apply HGmw; lia).
  assert (HGmN : forall i, i < m -> FOPrH 0 Gm (FONUMR (nth i ts FOZero) (nth i env FOZero))).
  { intros i Hi. apply FOPrH_assum. unfold Gm. apply in_or_app. right.
    unfold env. rewrite <- Ets. apply numr_ctx_nth. lia. }
  set (F := V + 4). set (Bc := F + 4 * m + 4). set (Ba := Bc + cpat_span (cpat_f rho A)).
  assert (EF : F = V + 4) by reflexivity.
  assert (EBc : Bc = F + 4 * m + 4) by reflexivity.
  assert (EBa : Ba = Bc + cpat_span (cpat_f rho A)) by reflexivity.
  pose proof (FOPrH_patf_total (cpat_f rho A) 0 Gm Bc env V ltac:(lia) ltac:(lia)
                ltac:(intros w ? ?; apply HGmV; lia) ltac:(intros w ? ?; apply HGm0; lia)
                ltac:(intros t Ht w ? ?; apply HenvR; [exact Ht | lia])
                ltac:(intros t Ht w ? ?; apply HenvR; [exact Ht | lia])
                ltac:(intros t Ht w ? ?; apply HenvR; [exact Ht | lia])) as Hex.
  refine (FOPrH_exe 0 Gm V (V + 3) _ _ Hex _ _ _ _ _).
  { apply HGmV. lia. }
  { apply SPF_free; [lia | avoid_tms | | right; apply HRw; lia].
    apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|].
    intros t Ht w ? ?. apply HtsR; [exact Ht | lia]. }
  { apply FOfree_in_PATF_any; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
    intros t Ht w ? ?. apply HenvR; [exact Ht | lia]. }
  { apply FOsubst_ok_PATF. apply FOtm_avoid_var. lia. }
  rewrite FOsubst_f_PATF by lia. rewrite FOsubst_t_var_eq'.
  rewrite (FOsubst_map_avoid V (FOVar (V + 3)) env)
    by (intros t Ht; apply HenvR; [exact Ht | lia]).
  set (Gc := Gm ++ [FOPATF Bc env (cpat_f rho A) (FOVar (V + 3))]).
  assert (Hinc : forall X, In X Gm -> In X Gc)
    by (intros X HX; apply in_or_app; left; exact HX).
  assert (HGcw : forall w, w < Hb \/ Bc <= w -> FOfree_ctx w Gc).
  { intros w Hw. apply FOfree_ctx_app_inv; [apply HGmw; lia|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
    destruct (Nat.lt_ge_cases w 2) as [Hw2|Hw2].
    - apply FOfree_in_PATF_lo; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      intros t Ht w0 ? ?. apply HenvR; [exact Ht | lia].
    - apply FOfree_in_PATF_any; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      intros t Ht w0 ? ?. apply HenvR; [exact Ht | lia]. }
  assert (HGcF : forall w, F <= w -> FOfree_ctx w Gc).
  { intros w Hw. apply FOfree_ctx_app_inv; [apply HGmV; lia|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
    apply FOfree_in_PATF_any; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
    intros t Ht w0 ? ?. apply HenvR; [exact Ht | lia]. }
  assert (HGc0 : FOctx_avoid Gc 0 1000) by (intros w ? ?; apply HGcw; lia).
  assert (HCH : FOPrH 0 Gc (FOSUBNUMS (S Q) (FOnumeral (FOcode_f A)) xs ts (FOVar (V + 3)))).
  { refine (SUBNUMS_chain xs 0 A Gc (fun _ => None) [] env ts (FOnumeral (FOcode_f A))
              (FOVar (V + 3)) (S Q) Ba Bc F (fvs_nodup A) _ _ _ _ HGc0 HGcF
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    - rewrite Eenv. reflexivity.
    - rewrite Ets. reflexivity.
    - intros x _. reflexivity.
    - intros z i Hz. discriminate Hz.
    - intros i Hi. cbn [length] in Hi. lia.
    - intros i Hi. exact (FOPrH_weaken 0 Gm Gc _ Hinc (HGmN i Hi)).
    - apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|]. avoid_tms.
    - intros t Ht w ? ?. apply HtsR; [exact Ht | lia].
    - intros t Ht w ? ?. apply HenvR; [exact Ht | lia].
    - apply FOtms_avoid_nil.
    - intros t [<-|[<-|[]]] w Hw; [apply FOin_tm_numeral | apply FOin_tm_var_ne; lia].
    - intros t Ht w Hw. apply HtsR; [exact Ht | lia].
    - intros t Ht w Hw. apply HenvR; [exact Ht | lia].
    - intros t [].
    - lia.
    - lia.
    - lia.
    - cbn [length]. change (rho_seq xs 0 (fun _ => None)) with rho. lia.
    - exact (FOPrH_patf_closed_code 0 Gc A Ba ltac:(lia)).
    - cbn [length app]. unfold Gc. apply FOPrH_last. }
  unfold SPF.
  apply (FOPrH_ex_intro _ _ Q (FOVar (V + 3))).
  { apply FOsubst_ok_and.
    - apply FOsubst_ok_SUBNUMS; [lia | lia | lia | avoid_tms | avoid_tms | left; avoid_tms].
    - unfold R. apply FOsubst_ok_eq. }
  rewrite FOsubst_f_and, FOsubst_f_SUBNUMS by lia.
  rewrite FOsubst_t_numeral, FOsubst_t_var_eq'.
  rewrite (FOsubst_map_avoid Q (FOVar (V + 3)) ts)
    by (intros t Ht; apply HtsR; [exact Ht | lia]).
  unfold R. rewrite FOsubst_f_eq, FOsubst_t_var_eq'.
  apply FOPrH_and_intro; [exact HCH | apply FOPrH_refl].
Qed.

Theorem FOSubNums_total : forall A,
  FOProvesTn 0 (SPF (subq A) (FOnumeral (FOcode_f A)) (fvs A) (map FOVar (fvs A))
                  (FOEq (FOVar (subq A)) (FOVar (subq A)))).
Proof.
  intros A.
  assert (HM : FOvars_max (FOImplF A A) = FOvars_max A)
    by (cbn [FOvars_max]; apply Nat.max_id).
  pose proof (rename_all (fvs A) (subHb A) [] (FOImplF A A) (subq A) (FOnumeral (FOcode_f A))
                (fvs A) (FOEq (FOVar (subq A)) (FOVar (subq A)))
                ltac:(unfold subq; lia) ltac:(rewrite HM; unfold subq; lia)
                ltac:(unfold subHb; lia)
                ltac:(intros z Hz; rewrite HM; exact (fvs_le A z Hz)) (fun x Hx => Hx)
                ltac:(intros w; apply FOin_tm_numeral) ltac:(avoid_tms)
                ltac:(intros w Hw; cbn [FOfree_in]; rewrite !FOin_tm_var_ne by lia; reflexivity)
                (tot_core A)) as H1.
  rewrite app_nil_r in H1. unfold HPhi in H1.
  rewrite (hsub_f_ext (FOImplF A A) (hR (subHb A) (fvs A)) (fun z => z)) in H1.
  2: { intros z Hz. apply hR_all. apply fvs_spec. cbn [FOfree_in] in Hz.
       apply Bool.orb_true_iff in Hz. destruct Hz as [Hz|Hz]; exact Hz. }
  rewrite hsub_f_id in H1 by reflexivity.
  rewrite (map_ext_in (fun z => FOVar (hR (subHb A) (fvs A) z)) FOVar (fvs A)) in H1
    by (intros z Hz; rewrite hR_all by exact Hz; reflexivity).
  change (FOPrH 0 [] (SPF (subq A) (FOnumeral (FOcode_f A)) (fvs A) (map FOVar (fvs A))
                        (FOEq (FOVar (subq A)) (FOVar (subq A))))).
  exact (FOPrH_mp 0 [] _ _ H1 (FOPrH_imp_refl 0 [] A)).
Qed.

(** ** What the substituted provability formula says.

    At every valuation [e], [FOSubProv k A] is true exactly when [T_k]
    proves [A] with the numeral of [e x] substituted for each free
    variable [x]. *)

Theorem FOSubProv_sat_iff : forall e k A,
  FOsat e (FOSubProv k A) <->
  FOProvesTn k (FOsubsts A (fvs A) (map (fun x => FOnumeral (e x)) (fvs A))).
Proof.
  intros e k A.
  assert (HxQ : forall x, In x (fvs A) -> x < subq A)
    by (intros x Hx; pose proof (fvs_le A x Hx); unfold subq; lia).
  assert (Hmap : forall v, map (fun y => FOnumeral (FOeval (FOupdate e (subq A) v) y))
                               (map FOVar (fvs A)) = map (fun x => FOnumeral (e x)) (fvs A)).
  { intros v. rewrite map_map. apply map_ext_in. intros x Hx. cbn [FOeval].
    rewrite FOupdate_neq; [reflexivity|]. pose proof (HxQ x Hx). lia. }
  assert (Hsound : forall v,
            FOsat (FOupdate e (subq A) v)
              (FOSUBNUMS (S (subq A)) (FOnumeral (FOcode_f A)) (fvs A) (map FOVar (fvs A))
                 (FOVar (subq A))) ->
            v = FOcode_f (FOsubsts A (fvs A) (map (fun x => FOnumeral (e x)) (fvs A)))).
  { intros v Hs.
    assert (Hav : FOtms_avoid (FOnumeral (FOcode_f A) :: FOVar (subq A) :: map FOVar (fvs A))
                    (S (subq A)) (S (subq A) + 3 * length (fvs A))).
    { apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|].
      apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      intros t Ht. apply in_map_iff in Ht. destruct Ht as [x [<- Hx]].
      apply FOtm_avoid_var. pose proof (HxQ x Hx). lia. }
    pose proof (SUBNUMS_sound (fvs A) (map FOVar (fvs A)) (S (subq A))
                  (FOnumeral (FOcode_f A)) (FOVar (subq A)) (FOupdate e (subq A) v) A
                  ltac:(unfold subq; lia) Hav ltac:(avoid_tms) Hs
                  ltac:(apply FOeval_numeral)) as E.
    cbn [FOeval] in E. rewrite FOupdate_eq, Hmap in E. exact E. }
  split.
  - intros H. unfold FOSubProv, SPF in H. cbn [FOsat] in H. destruct H as [v H].
    apply FOsat_FOAnd in H. destruct H as [Hs Hp].
    pose proof (Hsound v Hs) as Ev.
    pose proof (proj1 (FOsat_PRu_var (FOupdate e (subq A) v) (FOPrCores k) (FOu0 k) (subq A)
                         ltac:(unfold subq; lia)) Hp) as Hp'.
    clear Hp. rename Hp' into Hp.
    rewrite FOupdate_eq, Ev, FOPRu_ProvSentence in Hp.
    exact (proj1 (FOProvSentence_sat_iff _ k _) Hp).
  - intros Hpr.
    pose proof (FOProvesTn_sound 0 _ (FOSubNums_total A) e) as Ht.
    unfold SPF in Ht. cbn [FOsat] in Ht. destruct Ht as [v Ht].
    apply FOsat_FOAnd in Ht. destruct Ht as [Hs _].
    pose proof (Hsound v Hs) as Ev.
    unfold FOSubProv, SPF. cbn [FOsat]. exists v. apply FOsat_FOAnd. split; [exact Hs|].
    apply (proj2 (FOsat_PRu_var (FOupdate e (subq A) v) (FOPrCores k) (FOu0 k) (subq A)
                    ltac:(unfold subq; lia))).
    rewrite FOupdate_eq, Ev, FOPRu_ProvSentence.
    exact (proj2 (FOProvSentence_sat_iff _ k _) Hpr).
Qed.

(** ** Provable Sigma_1-completeness. *)

Theorem provable_sigma1_completeness : forall k,
  (forall A, FOsigma1 A -> FOProvesTn 0 (FOImplF A (FOSubProv k A))) /\
  (forall e A, FOsat e (FOSubProv k A) <->
     FOProvesTn k (FOsubsts A (fvs A) (map (fun x => FOnumeral (e x)) (fvs A)))) /\
  (forall A, FOsigma1 A -> (forall x, FOfree_in x A = false) ->
     FOProvesTn 0 (FOImplF A (FOProvSentence k A))) /\
  (forall A, FOProvesTn 0
     (FOImplF (FOProvSentence k A) (FOProvSentence k (FOProvSentence k A)))).
Proof.
  intros k. split; [|split; [|split]].
  - intros A HA. exact (provable_sigma1_open k A HA).
  - intros e A. exact (FOSubProv_sat_iff e k A).
  - intros A HA Hc. exact (provable_sigma1_sentence k A HA Hc).
  - intros A. exact (FOHBL3_internal k A).
Qed.
