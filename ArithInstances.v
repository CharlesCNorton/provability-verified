(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Loebian Obstacle           *)
(*                                                                            *)
(*     Part 10 of 11. Provable instances, numeral codes, sums and products.   *)
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
  ArithMerge ArithDerivability ArithRows ArithPatterns.
Open Scope fo_scope.

(** ** Codes of closed formulas and provability of theorems. *)

Lemma FOPrH_patf_closed_code : forall n G A B, 2 <= B ->
  FOPrH n G (FOPATF B [] (cpat_f (fun _ => None) A) (FOnumeral (FOcode_f A))).
Proof.
  intros n G A B HB. apply FOPrH_empty. apply FOPrH_true_closed.
  - apply FOs1_d0. apply FOdelta0_FOPATF; [constructor | rewrite FOmax_var_numeral; lia].
  - intros v. destruct (Nat.lt_ge_cases v B) as [Hv|Hv].
    + apply FOfree_in_PATF_lo; [exact Hv|]. apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|].
      apply FOtms_avoid_nil.
    + apply FOfree_in_PATF_any; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_numeral|].
      apply FOtms_avoid_nil.
  - apply (proj2 (FOsat_FOPATF _ _ B [] _ ltac:(constructor)
                    ltac:(rewrite FOmax_var_numeral; lia))).
    rewrite cpat_f_closed_sem by (intros; reflexivity). rewrite FOeval_numeral. reflexivity.
Qed.

Definition FOu0 (k : nat) : nat := FOcode_f (FOPRMAT (FOPrCores k)).

Lemma FOPrH_pru_thm : forall n G k A, FOProvesTn 0 A ->
  FOPrH n G (FOPRu (FOPrCores k) (FOu0 k) (FOnumeral (FOcode_f A))).
Proof.
  intros n G k A H.
  pose proof (FOHBL3_provable k n A (FOProvesTn_cumulative 0 k A (Nat.le_0_l k) H)) as H3.
  apply FOPrH_thm. unfold FOPRu, FOu0. rewrite FOPRMATx_num, FOsubst_f_num.
  rewrite (FOsubst_num_comm (FOPRMAT (FOPrCores k)) 0 1) by lia.
  exact H3.
Qed.

(** ** Provable instances.

    [PRI V G p env]: in every extension of [G] clean above a base
    [B >= V], every code of [p] over [env] is provable.  [EnvOK]: the
    slot codes carry their numeral rows and every variable of [G] and
    [env] lies in [1000 .. V). *)

Definition Clean (G : list FOFormula) (L : list FOTerm) (lo : nat) : Prop :=
  (forall w, lo <= w -> FOfree_ctx w G) /\
  (forall t, In t L -> forall w, lo <= w -> FOin_tm w t = false).

Definition PRI (n : nat) (cores : list nat) (u0 V : nat) (G : list FOFormula) (p : CPat)
    (env : list FOTerm) : Prop :=
  forall G' B c, (forall X, In X G -> In X G') -> FOctx_avoid G' 0 1000 ->
  FOtms_avoid [c] 0 1000 -> V <= B -> Clean G' [c] B ->
  FOPrH n G' (FOPATF B env p c) -> FOPrH n G' (FOPRu cores u0 c).

Definition EnvOK (n V : nat) (G : list FOFormula) (env : list FOTerm) : Prop :=
  SlotCtx n env G /\ FOtms_avoid env 0 1000 /\ 1000 <= V /\
  (forall t, In t env -> forall w, V <= w -> FOin_tm w t = false).

Lemma SlotCtx_mono : forall n env G G',
  (forall X, In X G -> In X G') -> FOctx_avoid G' 2 1000 -> SlotCtx n env G -> SlotCtx n env G'.
Proof.
  intros n env G G' Hinc HG' [_ Hs]. split; [exact HG'|].
  intros i Hi. destruct (Hs i Hi) as [w Hw]. exists w. exact (FOPrH_weaken n G G' _ Hinc Hw).
Qed.

Lemma Clean_tms : forall G L lo a b, Clean G L lo -> lo <= a -> FOtms_avoid L a b.
Proof. intros G L lo a b [_ H] Ha t Ht w Hw1 Hw2. apply (H t Ht). lia. Qed.

Lemma Clean_ctx : forall G L lo a b, Clean G L lo -> lo <= a -> FOctx_avoid G a b.
Proof. intros G L lo a b [H _] Ha w Hw1 Hw2. apply H. lia. Qed.

Lemma env_above : forall env V a b, (forall t, In t env -> forall w, V <= w -> FOin_tm w t = false) ->
  V <= a -> FOtms_avoid env a b.
Proof. intros env V a b H Ha t Ht w Hw1 Hw2. apply (H t Ht). lia. Qed.

(** ** Modus ponens on provable instances. *)

Lemma PRI_mp : forall n cores u0 V G rho A1 A2 env,
  EnvOK n V G env -> (forall z i, rho z = Some i -> i < length env) ->
  PRI n cores u0 V G (cpat_f rho (FOImplF A1 A2)) env ->
  PRI n cores u0 V G (cpat_f rho A1) env ->
  PRI n cores u0 V G (cpat_f rho A2) env.
Proof.
  intros n cores u0 V G rho A1 A2 env [HS [Henv0 [HV Henv]]] Hrho HI H1.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  pose proof (cpat_span_le (cpat_f rho A1)) as Hs1.
  assert (Hs12 : cpat_span (cpat_f rho (FOImplF A1 A2))
                 = 8 + 4 * cpat_pairs (cpat_f rho A1) + cpat_span (cpat_f rho A2))
    by (cbn [cpat_f pImpP cpat_span cpat_pairs]; lia).
  remember (cpat_span (cpat_f rho A2)) as s2 eqn:Es2.
  remember (cpat_pairs (cpat_f rho A1)) as p1 eqn:Ep1.
  assert (HGT : FOctx_avoid G' B (B + 4 * s2 + 4 * p1 + 100))
    by (intros w ? ?; apply HGc; lia).
  assert (HcT : FOtms_avoid (c :: env) B (B + 4 * s2 + 4 * p1 + 100)).
  { intros t Ht w ? ?. destruct Ht as [<-|Ht];
      [apply (Hcc c (or_introl eq_refl)); lia | apply (Henv t Ht); lia]. }
  assert (HS' : SlotCtx n env G')
    by (apply (SlotCtx_mono n env G G' Hinc); [intros w ? ?; apply HG0; lia | exact HS]).
  assert (Hc02 : FOtms_avoid (c :: env) 0 1000) by avoid_tms.
  pose proof (FOPrH_guard_code n G' A2 rho env B c HS' Hrho Hc ltac:(lia)
                ltac:(intros w ? ?; apply HGT; lia) ltac:(avoid_tms) ltac:(avoid_tms)) as Gc.
  (* a code of the implication, named [z] *)
  pose proof (FOPrH_patf_total (cpat_f rho (FOImplF A1 A2)) n G' (B + 2 * s2 + 3) env
                (B + 2 * s2) ltac:(lia) ltac:(lia) ltac:(intros w ? ?; apply HGT; lia)
                ltac:(intros w ? ?; apply HG0; lia) ltac:(rewrite Hs12; avoid_tms)
                ltac:(avoid_tms) ltac:(avoid_tms)) as Ht.
  refine (FOPrH_ex_elim n G' (B + 2 * s2) _ _ _ _ Ht _); [apply HGT; lia | free_fm |].
  lazymatch goal with |- FOPrH _ ?G2 _ =>
    assert (Hpz : FOPrH n G2 (FOPATF (B + 2 * s2 + 3) env (cpat_f rho (FOImplF A1 A2))
                               (FOVar (B + 2 * s2)))) by apply FOPrH_last;
    assert (HG20 : FOctx_avoid G2 0 1000) by ctx_list;
    assert (Hinc2 : forall X, In X G -> In X G2)
      by (intros X HX; apply in_or_app; left; exact (Hinc X HX))
  end.
  assert (Hcl2 : Clean (G' ++ [FOPATF (B + 2 * s2 + 3) env (cpat_f rho (FOImplF A1 A2))
                                  (FOVar (B + 2 * s2))]) [FOVar (B + 2 * s2)] (B + 2 * s2 + 3)).
  { split.
    - intros w Hw.
      assert (Hew : FOtms_avoid env w (S w))
        by (intros t Ht0 w' ? ?; apply (Henv t Ht0); lia).
      apply FOfree_ctx_app_inv; [apply HGc; lia|].
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      apply FOfree_in_PATF_any; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      exact Hew.
    - intros t Ht0 w Hw. destruct Ht0 as [<-|[]]. apply FOin_tm_var_ne. lia. }
  pose proof (HI _ (B + 2 * s2 + 3) (FOVar (B + 2 * s2)) Hinc2 HG20 ltac:(avoid_tms) ltac:(lia)
                Hcl2 Hpz) as Hpr.
  cbn [cpat_f pImpP] in Hpz.
  apply (FOPrH_patf_bin_elim n _ (B + 2 * s2 + 3) env 2 (cpat_f rho A1) (cpat_f rho A2)
           (FOVar (B + 2 * s2)) _ Hpz ltac:(lia));
    [cbn [cpat_span cpat_pairs]; ctx_list | intros w ? ?; cbn [cpat_span cpat_pairs] in *; free_fm
    | cbn [cpat_span cpat_pairs]; avoid_tms |].
  set (B1 := B + 2 * s2 + 3).
  lazymatch goal with |- FOPrH _ ?G3 _ =>
    assert (Hk : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar (B1 + 2)) (FOVar (B + 2 * s2))))
      by wk_in;
    assert (Hp : FOPrH n G3 (FOcpairF (FOVar (B1 + 4)) (FOVar (B1 + 6)) (FOVar (B1 + 2))))
      by wk_in;
    assert (Ha1 : FOPrH n G3 (FOPATF (B1 + 8) env (cpat_f rho A1) (FOVar (B1 + 4)))) by wk_in;
    assert (Ha2 : FOPrH n G3 (FOPATF (B1 + 8 + 4 * cpat_pairs (cpat_f rho A1)) env
                                (cpat_f rho A2) (FOVar (B1 + 6)))) by wk_in;
    assert (HG30 : FOctx_avoid G3 0 1000) by ctx_list;
    assert (Hinc3 : forall X, In X G -> In X G3)
      by (intros X HX; apply in_or_app; left; apply in_or_app; left; exact (Hinc X HX));
    assert (Hc3 : FOPrH n G3 (FOPATF B env (cpat_f rho A2) c)) by wk Hc;
    assert (Gc3 : FOPrH n G3 (FOGUARDB c)) by wk Gc;
    assert (Hpr3 : FOPrH n G3 (FOPRu cores u0 (FOVar (B + 2 * s2)))) by wk Hpr;
    assert (Hcl3 : Clean G3 [FOVar (B1 + 4)] (B1 + 8))
      by (split;
          [ intros w Hw;
            assert (Hew : FOtms_avoid env w (S w))
              by (intros t Ht0 w' ? ?; apply (Henv t Ht0); unfold B1 in *; lia);
            apply FOfree_ctx_app_inv;
            [ apply FOfree_ctx_app_inv; [apply HGc; unfold B1 in *; lia | free_ctx]
            | free_ctx ]
          | intros t Ht0 w Hw; destruct Ht0 as [<-|[]]; apply FOin_tm_var_ne; lia ])
  end.
  pose proof (H1 _ (B1 + 8) (FOVar (B1 + 4)) Hinc3 HG30 ltac:(avoid_tms) ltac:(unfold B1; lia)
                Hcl3 Ha1) as Hpb.
  pose proof (FOPrH_patf_unique (cpat_f rho A2) n _ (B1 + 8 + 4 * cpat_pairs (cpat_f rho A1)) B
                env (FOVar (B1 + 6)) c Ha2 Hc3 ltac:(lia) ltac:(lia) ltac:(unfold B1; lia)
                ltac:(unfold B1 in *; ctx_list) ltac:(unfold B1 in *; ctx_list)
                ltac:(unfold B1 in *; avoid_tms) ltac:(unfold B1 in *; avoid_tms)
                ltac:(avoid_tms)) as Ec.
  pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ (FOPrH_refl _ _ _) Ec (FOPrH_refl _ _ _) Hp)
    as Hp'.
  pose proof (FOPrH_patf_impl01 n _ (FOVar (B + 2 * s2)) (FOVar (B1 + 4)) c (FOVar (B1 + 2))
                Hk Hp' ltac:(avoid_tms) ltac:(avoid_tms)) as HP52.
  exact (FOPrH_mpu n _ cores u0 (FOVar (B + 2 * s2)) (FOVar (B1 + 4)) c
           ltac:(intros w ? ?; apply HG30; lia) HP52 Gc3 ltac:(avoid_tms) Hpr3 Hpb).
Qed.

(** ** Instantiation of provable instances. *)

Lemma PRI_inst : forall n cores u0 V V' G rho x th env m wm,
  EnvOK n V G env -> (forall z i, rho z = Some i -> i < length env) ->
  FOPrH n G (FONUMR wm m) -> FOtms_avoid [m] 0 1000 -> V <= V' ->
  (forall w, V' <= w -> FOin_tm w m = false) ->
  PRI n cores u0 V G (cpat_f rho (FOForall x th)) env ->
  PRI n cores u0 V' G (cpat_f (rho_sub (Some x) (length env) rho) th) (env ++ [m]).
Proof.
  intros n cores u0 V V' G rho x th env m wm [HS [Henv0 [HV Henv]]] Hrho Hm Hm0 HVV' Hmv HI.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  remember (cpat_span (cpat_f (rho_sub (Some x) (length env) rho) th)) as s1 eqn:Es1.
  remember (cpat_span (cpat_f rho (FOForall x th))) as s0 eqn:Es0.
  assert (HGT : FOctx_avoid G' B (B + s1 + 8 + 2 * s0 + 2 * s1 + 10))
    by (intros w ? ?; apply HGc; lia).
  assert (HT : FOtms_avoid (c :: m :: env) B (B + s1 + 8 + 2 * s0 + 2 * s1 + 10)).
  { intros t Ht0 w ? ?. destruct Ht0 as [<-|[<-|Ht0]];
      [apply (Hcc c (or_introl eq_refl)); lia | apply Hmv; lia | apply (Henv t Ht0); lia]. }
  assert (HS' : SlotCtx n env G')
    by (apply (SlotCtx_mono n env G G' Hinc); [intros w ? ?; apply HG0; lia | exact HS]).
  assert (Hm' : FOPrH n G' (FONUMR wm m)) by exact (FOPrH_weaken n G G' _ Hinc Hm).
  assert (Hc02 : FOtms_avoid (c :: m :: env) 0 1000) by avoid_tms.
  pose proof (FOPrH_patf_total (cpat_f rho (FOForall x th)) n G' (B + s1 + 4) env (B + s1)
                ltac:(lia) ltac:(lia) ltac:(intros w ? ?; apply HGT; lia)
                ltac:(intros w ? ?; apply HG0; lia) ltac:(rewrite <- Es0; avoid_tms)
                ltac:(avoid_tms) ltac:(avoid_tms)) as Ht.
  refine (FOPrH_ex_elim n G' (B + s1) _ _ _ _ Ht _); [apply HGT; lia | free_fm |].
  lazymatch goal with |- FOPrH _ ?G2 _ =>
    assert (Hpz : FOPrH n G2 (FOPATF (B + s1 + 4) env (cpat_f rho (FOForall x th))
                               (FOVar (B + s1)))) by apply FOPrH_last;
    assert (HG20 : FOctx_avoid G2 0 1000) by ctx_list;
    assert (Hinc2 : forall X, In X G -> In X G2)
      by (intros X HX; apply in_or_app; left; exact (Hinc X HX));
    assert (Hcl2 : Clean G2 [FOVar (B + s1)] (B + s1 + 4))
      by (split;
          [ intros w Hw;
            assert (Hew : FOtms_avoid env w (S w))
              by (intros t Ht0 w' ? ?; apply (Henv t Ht0); lia);
            apply FOfree_ctx_app_inv; [apply HGc; lia | free_ctx]
          | intros t Ht0 w Hw; destruct Ht0 as [<-|[]]; apply FOin_tm_var_ne; lia ]);
    assert (Hc2 : FOPrH n G2 (FOPATF B (env ++ [m])
                               (cpat_f (rho_sub (Some x) (length env) rho) th) c)) by wk Hc;
    assert (HS2 : SlotCtx n env G2)
      by (apply (SlotCtx_mono n env G' G2); [intros X HX; apply in_or_app; left; exact HX
                                             | intros w ? ?; apply HG20; lia | exact HS']);
    assert (Hm2 : FOPrH n G2 (FONUMR wm m)) by wk Hm'
  end.
  pose proof (HI _ (B + s1 + 4) (FOVar (B + s1)) Hinc2 HG20 ltac:(avoid_tms) ltac:(lia)
                Hcl2 Hpz) as Hpr.
  pose proof (FOPrH_patf_rebase _ n _ B (B + s1 + 4 + 2 * s0) (env ++ [m]) c Hc2 ltac:(lia)
                ltac:(lia) ltac:(rewrite <- Es1; lia) ltac:(rewrite <- Es1; ctx_list)
                ltac:(rewrite <- Es1; avoid_tms) ltac:(rewrite <- Es1; avoid_tms)
                ltac:(avoid_tms)) as Hc1.
  exact (FOPrH_inst_code n _ cores u0 x th rho env m wm (B + s1 + 4) (FOVar (B + s1))
           (B + s1 + 4 + 2 * s0) c (B + s1 + 1) HS2 Hrho Hm2 Hpz Hc1 Hpr HG20 ltac:(lia)
           ltac:(ctx_list) ltac:(lia) ltac:(rewrite <- Es0; lia)
           ltac:(rewrite <- Es0; ctx_list) ltac:(rewrite <- Es1; ctx_list)
           ltac:(avoid_tms) ltac:(avoid_tms) ltac:(rewrite <- Es0; avoid_tms)
           ltac:(rewrite <- Es1; avoid_tms)).
Qed.

(** ** Instantiation of a theorem. *)

Lemma PRI_inst_closed : forall n k V G x th m wm,
  FOProvesTn 0 (FOForall x th) ->
  FOctx_avoid G 0 1000 -> FOPrH n G (FONUMR wm m) -> FOtms_avoid [m] 0 1000 -> 1000 <= V ->
  (forall w, V <= w -> FOin_tm w m = false) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f (rho_sub (Some x) 0 (fun _ => None)) th) [m].
Proof.
  intros n k V G x th m wm Hthm HG Hm Hm0 HV Hmv.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  remember (cpat_span (cpat_f (rho_sub (Some x) 0 (fun _ => None)) th)) as s1 eqn:Es1.
  remember (cpat_span (cpat_f (fun _ => None) (FOForall x th))) as s0 eqn:Es0.
  assert (HGT : FOctx_avoid G' B (B + s1 + 3 + 2 * s0 + 2 * s1 + 10))
    by (intros w ? ?; apply HGc; lia).
  assert (HT : FOtms_avoid [c; m] B (B + s1 + 3 + 2 * s0 + 2 * s1 + 10)).
  { intros t Ht0 w ? ?. destruct Ht0 as [<-|[<-|[]]];
      [apply (Hcc c (or_introl eq_refl)); lia | apply Hmv; lia]. }
  assert (Hm' : FOPrH n G' (FONUMR wm m)) by exact (FOPrH_weaken n G G' _ Hinc Hm).
  assert (HS' : SlotCtx n [] G') by (split; [intros w ? ?; apply HG0; lia | intros i Hi; cbn in Hi; lia]).
  pose proof (FOPrH_patf_closed_code n G' (FOForall x th) (B + s1 + 3) ltac:(lia)) as Hd0.
  pose proof (FOPrH_pru_thm n G' k (FOForall x th) Hthm) as Hpr.
  pose proof (FOPrH_patf_rebase _ n _ B (B + s1 + 3 + 2 * s0) ([] ++ [m]) c Hc ltac:(lia)
                ltac:(lia) ltac:(rewrite <- Es1; lia) ltac:(rewrite <- Es1; ctx_list)
                ltac:(rewrite <- Es1; cbn [app]; avoid_tms)
                ltac:(rewrite <- Es1; cbn [app]; avoid_tms)
                ltac:(cbn [app]; avoid_tms)) as Hc1.
  exact (FOPrH_inst_code n G' (FOPrCores k) (FOu0 k) x th (fun _ => None) [] m wm (B + s1 + 3)
           (FOnumeral (FOcode_f (FOForall x th))) (B + s1 + 3 + 2 * s0) c B HS'
           ltac:(intros z i Hz; discriminate) Hm' Hd0 Hc1 Hpr HG0 ltac:(lia)
           ltac:(intros w ? ?; apply HGT; lia) ltac:(lia) ltac:(rewrite <- Es0; lia)
           ltac:(rewrite <- Es0; intros w ? ?; apply HGT; lia)
           ltac:(cbn [length]; rewrite <- Es1; intros w ? ?; apply HGT; lia)
           ltac:(avoid_tms) ltac:(avoid_tms) ltac:(rewrite <- Es0; avoid_tms)
           ltac:(cbn [length]; rewrite <- Es1; avoid_tms)).
Qed.

(** ** Provable instances converted along [CPrel]. *)

Lemma PRI_conv : forall n cores u0 V G p p' env env',
  (forall G', (forall X, In X G -> In X G') -> CPrel n G' env env' p p') ->
  (forall t, In t (env ++ env') -> forall w, V <= w -> FOin_tm w t = false) ->
  FOtms_avoid (env ++ env') 0 1000 -> 1000 <= V ->
  PRI n cores u0 V G p env -> PRI n cores u0 V G p' env'.
Proof.
  intros n cores u0 V G p p' env env' HR Habove Hlo HV HI.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  assert (HGT : FOctx_avoid G' B (B + cpat_span p' + cpat_span p + 1))
    by (intros w ? ?; apply HGc; lia).
  assert (HT : FOtms_avoid (c :: env ++ env') B (B + cpat_span p' + cpat_span p + 1)).
  { intros t Ht0 w ? ?. destruct Ht0 as [<-|Ht0];
      [apply (Hcc c (or_introl eq_refl)); lia | apply (Habove t Ht0); lia]. }
  pose proof (FOPrH_patf_conv n G' env env' p p' (HR G' Hinc) G' (B + cpat_span p') B c
                (fun X HX => HX) Hc ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros w ? ?; apply HGT; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(apply (FOtms_avoid_sub _ 0 1000); [|lia|lia]; avoid_tms)) as Hc'.
  assert (Hcl : Clean G' [c] (B + cpat_span p')).
  { split; [intros w Hw; apply HGc; lia | intros t Ht0 w Hw; apply (Hcc t Ht0); lia]. }
  exact (HI G' (B + cpat_span p') c Hinc HG0 Hc0 ltac:(lia) Hcl Hc').
Qed.

(** ** The beta function is functional at every base. *)

Ltac ok_leaf :=
  repeat first [ apply FOsubst_ok_all; [fr_tm|]
               | apply FOsubst_ok_impl
               | apply FOsubst_ok_betaF; avoid_tm
               | apply FOsubst_ok_eq ].

Lemma FOPrH_beta_fun_at : forall n G v c d i x y,
  FOPrH n G (FObetaF v c d i x) -> FOPrH n G (FObetaF v c d i y) ->
  2 <= v -> v + 4 <= 420 ->
  FOtms_avoid [c; d; i; x; y] v (v + 4) -> FOtms_avoid [c; d; i; x; y] 420 490 ->
  FOPrH n G (FOEq x y).
Proof.
  intros n G v c d i x y H1 H2 Hv1 Hv2 Hav Hav2.
  pose proof (FOPrH_rebase_cf n G v 480 c d i x ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms) H1)
    as K1.
  pose proof (FOPrH_rebase_cf n G v 480 c d i y ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms) H2)
    as K2.
  pose proof (FOPrH_thm n G _ (FOPr_beta_fun n)) as F.
  apply (FOPrH_inst n G 420 c) in F; [|ok_leaf].
  rewrite !FOsubst_f_all_ne, FOsubst_f_impl, FOsubst_f_impl, !FOsubst_f_betaF, FOsubst_f_eq
    in F by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in F by lia.
  apply (FOPrH_inst n G 421 d) in F; [|ok_leaf].
  rewrite !FOsubst_f_all_ne, FOsubst_f_impl, FOsubst_f_impl, !FOsubst_f_betaF, FOsubst_f_eq
    in F by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in F by lia.
  rewrite (FOsubst_t_not_in c 421 d) in F by fr_tm.
  apply (FOPrH_inst n G 422 i) in F; [|ok_leaf].
  rewrite !FOsubst_f_all_ne, FOsubst_f_impl, FOsubst_f_impl, !FOsubst_f_betaF, FOsubst_f_eq
    in F by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in F by lia.
  rewrite (FOsubst_t_not_in c 422 i), (FOsubst_t_not_in d 422 i) in F by fr_tm.
  apply (FOPrH_inst n G 423 x) in F; [|ok_leaf].
  rewrite !FOsubst_f_all_ne, FOsubst_f_impl, FOsubst_f_impl, !FOsubst_f_betaF, FOsubst_f_eq
    in F by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in F by lia.
  rewrite (FOsubst_t_not_in c 423 x), (FOsubst_t_not_in d 423 x), (FOsubst_t_not_in i 423 x)
    in F by fr_tm.
  apply (FOPrH_inst n G 424 y) in F; [|ok_leaf].
  rewrite FOsubst_f_impl, FOsubst_f_impl, !FOsubst_f_betaF, FOsubst_f_eq in F by lia.
  rewrite FOsubst_t_var_eq' in F.
  rewrite (FOsubst_t_not_in c 424 y), (FOsubst_t_not_in d 424 y), (FOsubst_t_not_in i 424 y),
    (FOsubst_t_not_in x 424 y) in F by fr_tm.
  exact (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ F K1) K2).
Qed.

(** ** Substitution into the dispatch cases. *)

Lemma FOsubst_f_DISPCASES : forall x s ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  x < 50 ->
  FOsubst_f x s (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) =
  FODISPCASES (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s tg) (FOsubst_t x s a1) (FOsubst_t x s a2) (FOsubst_t x s a3)
    (FOsubst_t x s r).
Proof. intros. unfold FODISPCASES. autorewrite with fosubst. reflexivity. Qed.

Lemma FOsubst_ok_DISPCASES : forall x s ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  FOtm_avoid s 50 122 ->
  FOsubst_ok x s (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) = true.
Proof.
  intros x s ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r V.
  assert (V' : FOtm_avoid s 50 (50 + 72)) by exact V.
  unfold FODISPCASES. auto 100 with fook.
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (FOTBLVALID _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOTBLVALID_free
  | |- FOfree_in _ (FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOlookup_free
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

(** ** A row of a valid table satisfies its step clause.

    The table is renamed to [122 .. 132]; the continuation receives
    the validity of the table and the dispatch cases at the row. *)

Lemma FOPrH_tblex_inv : forall n G tg a1 a2 a3 r C,
  FOctx_avoid G 2 1000 -> FOtms_avoid [tg; a1; a2; a3; r] 2 1000 ->
  (forall w, 2 <= w -> w < 1000 -> FOfree_in w C = false) ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r) ->
  FOPrH n (G ++ [FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132);
                 FODISPCASES (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   tg a1 a2 a3 r]) C ->
  FOPrH n G C.
Proof.
  intros n G tg a1 a2 a3 r C HG Hav HC H H0.
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n G tg a1 a2 a3 r 122 C _ _ _ _ _ _ _) H);
    [lia | lia | intros w ? ?; apply HG; lia | intros w ? ?; apply HC; lia | avoid_tms
    | avoid_tms |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (_ ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G X)) as KV;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G X)) as KL
  end.
  unfold FOlookup in KL. rewrite FOBexC_ltv in KL.
  set (T := [FOVar 122; FOVar 123; FOVar 124; FOVar 125; FOVar 126; FOVar 127; FOVar 128;
             FOVar 129; FOVar 130; FOVar 131; FOVar 132]).
  assert (HavT : FOtms_avoid (T ++ [tg; a1; a2; a3; r]) 2 122)
    by (unfold T; avoid_tms).
  assert (HavT2 : FOtms_avoid (T ++ [tg; a1; a2; a3; r]) 133 1000)
    by (unfold T; avoid_tms).
  refine (FOPrH_exe_clean n _ 28 140 _
            (FOAnd (FOExists 29 (FOEq (FOPlus (FOVar 140) (FOSucc (FOVar 29))) (FOVar 132)))
            (FOAnd (FObetaF 30 (FOVar 122) (FOVar 123) (FOVar 140) tg)
            (FOAnd (FObetaF 34 (FOVar 124) (FOVar 125) (FOVar 140) a1)
            (FOAnd (FObetaF 38 (FOVar 126) (FOVar 127) (FOVar 140) a2)
            (FOAnd (FObetaF 42 (FOVar 128) (FOVar 129) (FOVar 140) a3)
                   (FObetaF 46 (FOVar 130) (FOVar 131) (FOVar 140) r))))))
            C KL _ _ _ _ _ _);
    [free_ctx | apply HC; lia | free_fm | solve [auto 100 with fook] | |].
  { unfold FOltv. autorewrite with fosubst. rewrite ?FOsubst_t_var_eq'.
    subst_avoid_h HavT. apply FOPrH_assum; left; reflexivity. }
  lazymatch goal with |- FOPrH _ (?G2 ++ [?Y]) _ =>
    pose proof (FOPrH_last n G2 Y) as KJ;
    pose proof (FOPrH_weak_app _ _ [Y] _ KV) as KV2
  end.
  pose proof (FOPrH_and_l _ _ _ _ KJ) as Lt29.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ KJ)) as B0.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ KJ))) as B1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ KJ)))) as B2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ KJ))))) as B3.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ KJ))))) as B4.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_exeq_rename n _ 29 470 (FOVar 140) (FOVar 132)
                ltac:(lia) ltac:(fr_tm) ltac:(fr_tm) ltac:(fr_tm) ltac:(fr_tm)) Lt29) as Lt470.
  pose proof (FOPrH_ball_inst n _ 18 (FOVar 132) (FOVar 140)
                (FOSTEPDISPATCH 20 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   (FOVar 18)) KV2 Lt470 ltac:(lia)
                ltac:(assert (V : FOtm_avoid (FOVar 140) 20 (20 + 102)) by avoid_tm;
                      auto 100 with fook)
                ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as KD.
  rewrite FOsubst_f_STEPDISPATCH in KD by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in KD by lia.
  refine (FOPrH_ex_elim n _ 20 _ C _ _ KD _); [free_ctx | apply HC; lia |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (?G3 ++ [?Y]) _ =>
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G3 Y)) as KD1 end.
  refine (FOPrH_ex_elim n _ 22 _ C _ _ KD1 _); [free_ctx | apply HC; lia |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (?G3 ++ [?Y]) _ =>
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G3 Y)) as KD2 end.
  refine (FOPrH_ex_elim n _ 24 _ C _ _ KD2 _); [free_ctx | apply HC; lia |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (?G3 ++ [?Y]) _ =>
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G3 Y)) as KD3 end.
  refine (FOPrH_ex_elim n _ 26 _ C _ _ KD3 _); [free_ctx | apply HC; lia |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (?G3 ++ [?Y]) _ =>
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G3 Y)) as KD4 end.
  refine (FOPrH_ex_elim n _ 28 _ C _ _ KD4 _); [free_ctx | apply HC; lia |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (?G3 ++ [?Y]) _ =>
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G3 Y)) as KE end.
  pose proof (FOPrH_and_l _ _ _ _ KE) as D0.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ KE)) as D1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ KE))) as D2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ KE)))) as D3.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ KE))))) as D4.
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ KE))))) as CS.
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (B0' : FOPrH n Gc (FObetaF 30 (FOVar 122) (FOVar 123) (FOVar 140) tg)) by wk B0;
    assert (B1' : FOPrH n Gc (FObetaF 34 (FOVar 124) (FOVar 125) (FOVar 140) a1)) by wk B1;
    assert (B2' : FOPrH n Gc (FObetaF 38 (FOVar 126) (FOVar 127) (FOVar 140) a2)) by wk B2;
    assert (B3' : FOPrH n Gc (FObetaF 42 (FOVar 128) (FOVar 129) (FOVar 140) a3)) by wk B3;
    assert (B4' : FOPrH n Gc (FObetaF 46 (FOVar 130) (FOVar 131) (FOVar 140) r)) by wk B4;
    assert (KV' : FOPrH n Gc (FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125)
                    (FOVar 126) (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131)
                    (FOVar 132))) by wk KV
  end.
  pose proof (FOPrH_beta_fun_at n _ 30 _ _ _ _ _ D0 B0' ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(avoid_tms)) as E0.
  pose proof (FOPrH_beta_fun_at n _ 34 _ _ _ _ _ D1 B1' ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(avoid_tms)) as E1.
  pose proof (FOPrH_beta_fun_at n _ 38 _ _ _ _ _ D2 B2' ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(avoid_tms)) as E2.
  pose proof (FOPrH_beta_fun_at n _ 42 _ _ _ _ _ D3 B3' ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(avoid_tms)) as E3.
  pose proof (FOPrH_beta_fun_at n _ 46 _ _ _ _ _ D4 B4' ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                ltac:(avoid_tms)) as E4.
  assert (Vtg : FOtm_avoid tg 50 122) by avoid_tm.
  assert (Va1 : FOtm_avoid a1 50 122) by avoid_tm.
  assert (Va2 : FOtm_avoid a2 50 122) by avoid_tm.
  assert (Va3 : FOtm_avoid a3 50 122) by avoid_tm.
  assert (Vr : FOtm_avoid r 50 122) by avoid_tm.
  pose proof (FOPrH_leibniz n _ 20 (FOVar 20) tg
                (FODISPCASES (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   (FOVar 20) (FOVar 22) (FOVar 24) (FOVar 26) (FOVar 28))
                ltac:(apply FOsubst_ok_var_self) ltac:(apply FOsubst_ok_DISPCASES; exact Vtg)
                E0) as L0.
  rewrite FOsubst_f_id in L0. specialize (L0 CS).
  rewrite FOsubst_f_DISPCASES in L0 by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in L0 by lia.
  pose proof (FOPrH_leibniz n _ 22 (FOVar 22) a1
                (FODISPCASES (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   tg (FOVar 22) (FOVar 24) (FOVar 26) (FOVar 28))
                ltac:(apply FOsubst_ok_var_self) ltac:(apply FOsubst_ok_DISPCASES; exact Va1)
                E1) as L1.
  rewrite FOsubst_f_id in L1. specialize (L1 L0).
  rewrite FOsubst_f_DISPCASES in L1 by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in L1 by lia.
  rewrite (FOsubst_t_not_in tg 22 a1) in L1 by fr_tm.
  pose proof (FOPrH_leibniz n _ 24 (FOVar 24) a2
                (FODISPCASES (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   tg a1 (FOVar 24) (FOVar 26) (FOVar 28))
                ltac:(apply FOsubst_ok_var_self) ltac:(apply FOsubst_ok_DISPCASES; exact Va2)
                E2) as L2.
  rewrite FOsubst_f_id in L2. specialize (L2 L1).
  rewrite FOsubst_f_DISPCASES in L2 by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in L2 by lia.
  rewrite (FOsubst_t_not_in tg 24 a2), (FOsubst_t_not_in a1 24 a2) in L2 by fr_tm.
  pose proof (FOPrH_leibniz n _ 26 (FOVar 26) a3
                (FODISPCASES (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   tg a1 a2 (FOVar 26) (FOVar 28))
                ltac:(apply FOsubst_ok_var_self) ltac:(apply FOsubst_ok_DISPCASES; exact Va3)
                E3) as L3.
  rewrite FOsubst_f_id in L3. specialize (L3 L2).
  rewrite FOsubst_f_DISPCASES in L3 by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in L3 by lia.
  rewrite (FOsubst_t_not_in tg 26 a3), (FOsubst_t_not_in a1 26 a3), (FOsubst_t_not_in a2 26 a3)
    in L3 by fr_tm.
  pose proof (FOPrH_leibniz n _ 28 (FOVar 28) r
                (FODISPCASES (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                   (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                   tg a1 a2 a3 (FOVar 28))
                ltac:(apply FOsubst_ok_var_self) ltac:(apply FOsubst_ok_DISPCASES; exact Vr)
                E4) as L4.
  rewrite FOsubst_f_id in L4. specialize (L4 L3).
  rewrite FOsubst_f_DISPCASES in L4 by lia.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in L4 by lia.
  rewrite (FOsubst_t_not_in tg 28 r), (FOsubst_t_not_in a1 28 r), (FOsubst_t_not_in a2 28 r),
    (FOsubst_t_not_in a3 28 r) in L4 by fr_tm.
  refine (FOPrH_cut _ _ _ C KV' _).
  refine (FOPrH_cut _ _ _ C (FOPrH_weak_app _ _ _ _ L4) _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros Y HY. apply in_app_or in HY. destruct HY as [HY|[<-|[<-|[]]]].
  - do 2 (apply in_or_app; left). repeat (apply in_or_app; left). exact HY.
  - apply in_or_app. left. apply in_or_app. right. left. reflexivity.
  - apply in_or_app. right. left. reflexivity.
Qed.

(** ** Free variables of the dispatch cases. *)

Lemma FODISPCASES_free : forall w ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  FOfree_in w (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true \/ FOin_tm w tg = true
  \/ FOin_tm w a1 = true \/ FOin_tm w a2 = true \/ FOin_tm w a3 = true
  \/ FOin_tm w r = true \/ w < 2.
Proof.
  intros w ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r H.
  unfold FODISPCASES, FOSTEP0, FOSTEP1, FOSTEP2, FOSTEP3, FOSTEP4, FOSTEP5,
    FOSTEP_bin, FOSTEP_quant0, FOSTEP_substbin, FOSTEP_substquant, FOSTEP_subokbin,
    FOSTEP_subokquant in H.
  ffree_walk; ffin.
Qed.

Lemma FOSTEP5_free : forall w B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r,
  FOfree_in w (FOSTEP5 B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r) = true ->
  FOin_tm w ct = true \/ FOin_tm w dt = true \/ FOin_tm w c1 = true
  \/ FOin_tm w d1 = true \/ FOin_tm w c2 = true \/ FOin_tm w d2 = true
  \/ FOin_tm w c3 = true \/ FOin_tm w d3 = true \/ FOin_tm w cr = true
  \/ FOin_tm w dr = true \/ FOin_tm w len = true \/ FOin_tm w a1 = true
  \/ FOin_tm w r = true \/ w < 2.
Proof.
  intros w B ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r H.
  unfold FOSTEP5 in H. ffree_walk; ffin.
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (FODISPCASES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FODISPCASES_free
  | |- FOfree_in _ (FOSTEP5 _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOSTEP5_free
  | |- FOfree_in _ (FOTBLVALID _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOTBLVALID_free
  | |- FOfree_in _ (FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOlookup_free
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

(** ** The dispatch cases at tag [5]. *)

Ltac disp_kill k :=
  apply FOPrH_efq;
  exact (FOPrH_mp _ _ _ _ (FOPrH_num_neq _ _ 5 k ltac:(lia))
           (FOPrH_and_l _ _ _ _ (FOPrH_last _ _ _))).

Lemma FOPrH_disp_tag5 : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r,
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 5) a1 a2 a3 r) ->
  FOPrH n G (FOSTEP5 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r).
Proof.
  intros n G ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r H. unfold FODISPCASES in H.
  refine (FOPrH_or_elim _ _ _ _ _ H _ _); [disp_kill 0|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill 1|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill 2|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill 3|].
  refine (FOPrH_or_elim _ _ _ _ _ (FOPrH_last _ _ _) _ _); [disp_kill 4|].
  refine (FOPrH_weaken n _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _))).
  intros X HX. exact HX.
Qed.

(** ** A row rewritten along an equation of its second field. *)

Lemma FOPrH_tblex_cong_a1 : forall n G tg a1 a2 a3 r a1',
  FOPrH n G (FOTBLEX tg a1 a2 a3 r) -> FOPrH n G (FOEq a1 a1') ->
  FOtms_avoid [tg; a1; a2; a3; r; a1'] 2 1000 ->
  FOPrH n G (FOTBLEX tg a1' a2 a3 r).
Proof.
  intros n G tg a1 a2 a3 r a1' H E Hav.
  assert (K : forall t, FOtm_avoid t 2 1000 ->
             FOsubst_f 999 t (FOTBLEX tg (FOVar 999) a2 a3 r) = FOTBLEX tg t a2 a3 r).
  { intros t Ht. rewrite FOsubst_f_TBLEX by lia. rewrite FOsubst_t_var_eq'.
    rewrite !(FOsubst_t_not_in _ 999 t) by fr_tm. reflexivity. }
  assert (V1 : FOtm_avoid a1 2 1000) by avoid_tm.
  assert (V1' : FOtm_avoid a1' 2 1000) by avoid_tm.
  pose proof (FOPrH_leibniz n G 999 a1 a1' (FOTBLEX tg (FOVar 999) a2 a3 r)
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm])
                ltac:(apply FOsubst_ok_TBLEX; [lia | avoid_tm]) E) as L.
  rewrite (K a1 V1), (K a1' V1') in L. exact (L H).
Qed.

(** ** Inversion of the numeral rows. *)

Lemma FOPrH_num5_inv0 : forall n G m,
  FOctx_avoid G 2 1000 -> FOtms_avoid [m] 2 1000 ->
  FOPrH n G (FOTBLEX (FOnumeral 5) FOZero FOZero FOZero m) ->
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero m).
Proof.
  intros n G m HG Hm H.
  apply (FOPrH_tblex_inv n G (FOnumeral 5) FOZero FOZero FOZero m
           (FOcpairF (FOnumeral 1) FOZero m) HG ltac:(avoid_tms)
           ltac:(intros w ? ?; free_fm) H).
  lazymatch goal with |- FOPrH _ (?Gx ++ [?V; ?D]) _ =>
    pose proof (FOPrH_disp_tag5 n (Gx ++ [V; D]) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  (FOPrH_assum n (Gx ++ [V; D]) D ltac:(apply in_or_app; right; cbn [In]; right; left; reflexivity)))
      as S5
  end.
  unfold FOSTEP5 in S5.
  refine (FOPrH_or_elim _ _ _ _ _ S5 _ _).
  - exact (FOPrH_and_r _ _ _ _ (FOPrH_last _ _ _)).
  - apply FOPrH_efq.
    lazymatch goal with |- FOPrH _ (?Gx ++ [?Y]) _ => pose proof (FOPrH_last n Gx Y) as K end.
    refine (FOPrH_ex_elim n _ 50 _ FOFalseF _ eq_refl K _); [free_ctx|].
    lazymatch goal with |- FOPrH _ (?Gx ++ [?Y]) _ =>
      pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_last n Gx Y))) as E end.
    exact (FOPrH_Q_succ_nonzero n _ (FOVar 50) (FOPrH_eq_sym _ _ _ _ E)).
Qed.

Lemma FOPrH_num5_invS : forall n G a m w C,
  FOctx_avoid G 2 1000 -> FOtms_avoid [a; m] 2 1000 -> 1000 <= w ->
  FOfree_ctx w G -> FOfree_in w C = false -> FOtms_avoid [a; m] w (S w) ->
  (forall v, 2 <= v -> v < 1000 -> FOfree_in v C = false) ->
  FOPrH n G (FOTBLEX (FOnumeral 5) (FOSucc a) FOZero FOZero m) ->
  FOPrH n (G ++ [FOcpairF (FOnumeral 2) (FOVar w) m;
                 FOTBLEX (FOnumeral 5) a FOZero FOZero (FOVar w)]) C ->
  FOPrH n G C.
Proof.
  intros n G a m w C HG Hav Hw HGw HCw Havw HCv H H0.
  apply (FOPrH_tblex_inv n G (FOnumeral 5) (FOSucc a) FOZero FOZero m C HG ltac:(avoid_tms)
           HCv H).
  lazymatch goal with |- FOPrH _ (?Gx ++ [?V; ?D]) _ =>
    pose proof (FOPrH_disp_tag5 n (Gx ++ [V; D]) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                  (FOPrH_assum n (Gx ++ [V; D]) D ltac:(apply in_or_app; right; cbn [In]; right; left; reflexivity)))
      as S5;
    pose proof (FOPrH_assum n (Gx ++ [V; D]) V ltac:(apply in_or_app; right; cbn [In]; left; reflexivity)) as KV
  end.
  unfold FOSTEP5 in S5.
  refine (FOPrH_or_elim _ _ _ _ _ S5 _ _).
  - apply FOPrH_efq.
    exact (FOPrH_Q_succ_nonzero n _ a (FOPrH_and_l _ _ _ _ (FOPrH_last _ _ _))).
  - lazymatch goal with |- FOPrH _ (?Gx ++ [?Y]) _ => pose proof (FOPrH_last n Gx Y) as K end.
    refine (FOPrH_ex_elim n _ 50 _ C _ _ K _); [free_ctx | apply HCv; lia |].
    lazymatch goal with |- FOPrH _ (?Gx ++ [?Y]) _ =>
      pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_last n Gx Y))) as E;
      pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_last n Gx Y))) as K2
    end.
    pose proof (FOPrH_Q_succ_inj n _ a (FOVar 50) E) as Ea.
    refine (FOPrH_exe_clean n _ 52 w _
              (FOAnd (FOlookup 54 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                        (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                        (FOnumeral 5) (FOVar 50) FOZero FOZero (FOVar w))
                     (FOcpairF (FOnumeral 2) (FOVar w) m))
              C K2 _ _ _ _ _ _);
      [free_ctx | exact HCw | free_fm
      | apply FOsubst_ok_and;
        [ apply FOsubst_ok_ex; [fr_tm | apply FOsubst_ok_eq]
        | apply FOsubst_ok_and; [apply FOsubst_ok_lookup; avoid_tm | apply FOsubst_ok_cpairF] ]
      | |].
    { unfold FOltv. autorewrite with fosubst. rewrite ?FOsubst_t_var_eq'.
      subst_avoid_h Hav.
      refine (FOPrH_and_r _ _ _ _ _). apply FOPrH_assum. left. reflexivity. }
    lazymatch goal with |- FOPrH _ (?Gx ++ [?Y]) _ =>
      pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n Gx Y)) as L54;
      pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n Gx Y)) as Cw;
      assert (KV3 : FOPrH n (Gx ++ [Y]) (FOTBLVALID 18 (FOVar 122) (FOVar 123) (FOVar 124)
                      (FOVar 125) (FOVar 126) (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130)
                      (FOVar 131) (FOVar 132))) by wk KV;
      assert (Ea3 : FOPrH n (Gx ++ [Y]) (FOEq a (FOVar 50))) by wk Ea
    end.
    pose proof (FOPrH_lookup_rebase n _ 54 28 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L54 ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms))
      as L28.
    assert (Va : FOtm_avoid a 28 50) by avoid_tm.
    pose proof (FOPrH_leibniz n _ 27 (FOVar 50) a
                  (FOlookup 28 (FOVar 122) (FOVar 123) (FOVar 124) (FOVar 125) (FOVar 126)
                     (FOVar 127) (FOVar 128) (FOVar 129) (FOVar 130) (FOVar 131) (FOVar 132)
                     (FOnumeral 5) (FOVar 27) FOZero FOZero (FOVar w))
                  ltac:(apply FOsubst_ok_lookup; avoid_tm) ltac:(apply FOsubst_ok_lookup; exact Va)
                  (FOPrH_eq_sym _ _ _ _ Ea3)) as La.
    rewrite !FOsubst_f_lookup in La by lia.
    rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne, !FOsubst_t_numeral, !FOsubst_t_zero in La
      by lia.
    pose proof (FOPrH_tblex_intro n _ (FOtabv 122) (FOnumeral 5) a FOZero FOZero
                  (FOVar w) KV3 (La L28)
                  ltac:(unfold FOtabv, FOtab_terms;
                        cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen Nat.add app];
                        avoid_tms)) as Ta.
    refine (FOPrH_cut _ _ _ C Cw _).
    refine (FOPrH_cut _ _ _ C (FOPrH_weak_app _ _ _ _ Ta) _).
    refine (FOPrH_weaken n _ _ C _ H0).
    intros Y HY. apply in_app_or in HY. destruct HY as [HY|[<-|[<-|[]]]].
    + repeat (apply in_or_app; left). exact HY.
    + apply in_or_app. left. apply in_or_app. right. left. reflexivity.
    + apply in_or_app. right. left. reflexivity.
Qed.

(** ** Numeral codes are unique. *)

Definition FONUMU : FOFormula :=
  FOForall 1001 (FOForall 1002
    (FOTBLEX (FOnumeral 5) (FOVar 1000) FOZero FOZero (FOVar 1001) .->
     FOTBLEX (FOnumeral 5) (FOVar 1000) FOZero FOZero (FOVar 1002) .->
     FOEq (FOVar 1001) (FOVar 1002))).

Lemma FOsubst_f_NUMU : forall t, FOtms_avoid [t] 2 50 -> FOtms_avoid [t] 1001 1003 ->
  FOsubst_f 1000 t FONUMU =
  FOForall 1001 (FOForall 1002
    (FOTBLEX (FOnumeral 5) t FOZero FOZero (FOVar 1001) .->
     FOTBLEX (FOnumeral 5) t FOZero FOZero (FOVar 1002) .->
     FOEq (FOVar 1001) (FOVar 1002))).
Proof.
  intros t H1 H2. unfold FONUMU.
  rewrite !FOsubst_f_all_ne, !FOsubst_f_impl, !FOsubst_f_TBLEX, FOsubst_f_eq by lia.
  rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne, !FOsubst_t_numeral, !FOsubst_t_zero by lia.
  reflexivity.
Qed.

Lemma FOsubst_ok_NUMU : forall t, FOtms_avoid [t] 2 50 -> FOtms_avoid [t] 1001 1003 ->
  FOsubst_ok 1000 t FONUMU = true.
Proof.
  intros t H1 H2. unfold FONUMU.
  apply FOsubst_ok_all; [fr_tm|]. apply FOsubst_ok_all; [fr_tm|].
  apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|].
  apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm] | apply FOsubst_ok_eq].
Qed.

Theorem FOPr_num5_unique : forall n, FOProvesTn n (FOForall 1000 FONUMU).
Proof.
  intro n. change (FOPrH n [] (FOForall 1000 FONUMU)).
  apply FOPrH_ind; [apply FOfree_ctx_nil| |].
  - rewrite FOsubst_f_NUMU by avoid_tms.
    apply FOPrH_all_intro; [apply FOfree_ctx_nil|]. apply FOPrH_all_intro; [apply FOfree_ctx_nil|].
    apply FOPrH_intro. apply FOPrH_intro.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (HGc : FOctx_avoid Gc 2 1000) by ctx_list end.
    pose proof (FOPrH_num5_inv0 n _ (FOVar 1001) HGc ltac:(avoid_tms) ltac:(wk_in)) as C1.
    pose proof (FOPrH_num5_inv0 n _ (FOVar 1002) HGc ltac:(avoid_tms) ltac:(wk_in)) as C2.
    exact (FOPrH_cpair_fun n _ _ _ (FOVar 1001) (FOVar 1002) ltac:(avoid_tms) C1 C2).
  - rewrite FOsubst_f_NUMU by avoid_tms.
    apply FOPrH_all_intro; [apply FOfree_ctx_b; vm_compute; reflexivity|].
    apply FOPrH_all_intro; [apply FOfree_ctx_b; vm_compute; reflexivity|].
    apply FOPrH_intro. apply FOPrH_intro.
    unfold FONUMU at 1.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (HGc : FOctx_avoid Gc 2 1000) by ctx_list;
      assert (T1 : FOPrH n Gc (FOTBLEX (FOnumeral 5) (FOSucc (FOVar 1000)) FOZero FOZero
                                 (FOVar 1001))) by wk_in;
      assert (T2 : FOPrH n Gc (FOTBLEX (FOnumeral 5) (FOSucc (FOVar 1000)) FOZero FOZero
                                 (FOVar 1002))) by wk_in
    end.
    apply (FOPrH_num5_invS n _ (FOVar 1000) (FOVar 1001) 1003 (FOEq (FOVar 1001) (FOVar 1002))
             HGc ltac:(avoid_tms) ltac:(lia)
             ltac:(free_ctx) ltac:(reflexivity) ltac:(avoid_tms)
             ltac:(intros v ? ?; cbn [FOfree_in FOin_tm]; apply Bool.orb_false_iff; split;
                   apply Nat.eqb_neq; lia) T1).
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (HGc2 : FOctx_avoid Gc 2 1000) by ctx_list;
      assert (T2' : FOPrH n Gc (FOTBLEX (FOnumeral 5) (FOSucc (FOVar 1000)) FOZero FOZero
                                  (FOVar 1002))) by wk T2
    end.
    apply (FOPrH_num5_invS n _ (FOVar 1000) (FOVar 1002) 1004 (FOEq (FOVar 1001) (FOVar 1002))
             HGc2 ltac:(avoid_tms) ltac:(lia)
             ltac:(free_ctx) ltac:(reflexivity) ltac:(avoid_tms)
             ltac:(intros v ? ?; cbn [FOfree_in FOin_tm]; apply Bool.orb_false_iff; split;
                   apply Nat.eqb_neq; lia) T2').
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (C1 : FOPrH n Gc (FOcpairF (FOnumeral 2) (FOVar 1003) (FOVar 1001))) by wk_in;
      assert (U1 : FOPrH n Gc (FOTBLEX (FOnumeral 5) (FOVar 1000) FOZero FOZero (FOVar 1003)))
        by wk_in;
      assert (C2 : FOPrH n Gc (FOcpairF (FOnumeral 2) (FOVar 1004) (FOVar 1002))) by wk_in;
      assert (U2 : FOPrH n Gc (FOTBLEX (FOnumeral 5) (FOVar 1000) FOZero FOZero (FOVar 1004)))
        by wk_in;
      assert (IH : FOPrH n Gc FONUMU) by wk_in
    end.
    unfold FONUMU in IH.
    apply (FOPrH_inst _ _ 1001 (FOVar 1003)) in IH;
      [| apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_impl;
         [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|];
         apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm] | apply FOsubst_ok_eq]].
    rewrite FOsubst_f_all_ne, !FOsubst_f_impl, !FOsubst_f_TBLEX, FOsubst_f_eq in IH by lia.
    rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne, !FOsubst_t_numeral, !FOsubst_t_zero in IH
      by lia.
    apply (FOPrH_inst _ _ 1002 (FOVar 1004)) in IH;
      [| apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|];
         apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm] | apply FOsubst_ok_eq]].
    rewrite !FOsubst_f_impl, !FOsubst_f_TBLEX, FOsubst_f_eq in IH by lia.
    rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne, !FOsubst_t_numeral, !FOsubst_t_zero in IH
      by lia.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ IH U1) U2) as E34.
    pose proof (FOPrH_cpairF_cong _ _ _ _ _ _ _ _ (FOPrH_refl _ _ _) E34 (FOPrH_refl _ _ _) C1)
      as C1'.
    exact (FOPrH_cpair_fun n _ _ _ (FOVar 1001) (FOVar 1002) ltac:(avoid_tms) C1' C2).
Qed.

Lemma FOPrH_num5_unique : forall n G a m m',
  FOPrH n G (FOTBLEX (FOnumeral 5) a FOZero FOZero m) ->
  FOPrH n G (FOTBLEX (FOnumeral 5) a FOZero FOZero m') ->
  FOtms_avoid [a; m; m'] 2 50 -> FOtms_avoid [a; m; m'] 440 442 ->
  FOtms_avoid [a; m; m'] 1001 1003 ->
  FOPrH n G (FOEq m m').
Proof.
  intros n G a m m' H1 H2 Hav1 Hav2 Hav3.
  pose proof (FOPrH_thm n G _ (FOPr_num5_unique n)) as U.
  apply (FOPrH_inst n G 1000 a) in U; [|apply FOsubst_ok_NUMU; avoid_tms].
  rewrite FOsubst_f_NUMU in U by avoid_tms.
  apply (FOPrH_inst _ _ 1001 m) in U;
    [| apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_impl;
       [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm] | apply FOsubst_ok_eq]].
  rewrite FOsubst_f_all_ne, !FOsubst_f_impl, !FOsubst_f_TBLEX, FOsubst_f_eq in U by lia.
  rewrite !FOsubst_t_var_eq', !FOsubst_t_var_ne, !FOsubst_t_numeral, !FOsubst_t_zero in U
    by lia.
  rewrite (FOsubst_t_not_in a 1001 m) in U by fr_tm.
  apply (FOPrH_inst _ _ 1002 m') in U;
    [| apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_TBLEX; [lia | avoid_tm] | apply FOsubst_ok_eq]].
  rewrite !FOsubst_f_impl, !FOsubst_f_TBLEX, FOsubst_f_eq in U by lia.
  rewrite !FOsubst_t_var_eq', !FOsubst_t_numeral, !FOsubst_t_zero in U.
  rewrite (FOsubst_t_not_in a 1002 m'), (FOsubst_t_not_in m 1002 m') in U by fr_tm.
  exact (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ U H1) H2).
Qed.

(** ** Numeral codes: existence, uniqueness, inversion, successor. *)

Lemma FOsubst_ok_NUMR : forall x s a m, 13 <= x ->
  FOtms_avoid [s] 2 50 -> FOtms_avoid [s] 802 805 ->
  FOsubst_ok x s (FONUMR a m) = true.
Proof.
  intros x s a m Hx H1 H2. unfold FONUMR.
  apply FOsubst_ok_and; [apply FOsubst_ok_TBLEX; [lia | avoid_tm]|].
  apply FOsubst_ok_and.
  - apply FOsubst_ok_all; [fr_tm|]. apply FOsubst_ok_all; [fr_tm|].
    apply FOsubst_ok_TBLEX; [lia | avoid_tm].
  - apply FOsubst_ok_all; [fr_tm|]. apply FOsubst_ok_TBLEX; [lia | avoid_tm].
Qed.

Lemma FOPrH_numr_exists : forall n G t w C,
  FOtms_avoid [t] 2 1000 -> 1000 <= w -> FOfree_ctx w G -> FOfree_in w C = false ->
  FOtms_avoid [t] w (S w) ->
  FOPrH n (G ++ [FONUMR t (FOVar w)]) C -> FOPrH n G C.
Proof.
  intros n G t w C Ht Hw HGw HCw Htw H0.
  pose proof (FOPrH_thm n G _ (FOPr_numr n)) as H.
  apply (FOPrH_inst n G 800 t) in H;
    [| apply FOsubst_ok_ex; [fr_tm | apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]]].
  rewrite FOsubst_f_ex_ne, FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_t_var_eq', FOsubst_t_var_ne in H by lia.
  refine (FOPrH_exe_clean n G 801 w _ (FONUMR t (FOVar w)) C H HGw HCw _ _ _ H0).
  - free_fm.
  - apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms].
  - rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_var_eq', (FOsubst_t_not_in t 801 (FOVar w)) by fr_tm.
    apply FOPrH_assum. left. reflexivity.
Qed.

Lemma FOPrH_numr_unique : forall n G a m m',
  FOPrH n G (FONUMR a m) -> FOPrH n G (FONUMR a m') ->
  FOtms_avoid [a; m; m'] 2 1000 -> FOtms_avoid [a; m; m'] 1001 1003 ->
  FOPrH n G (FOEq m m').
Proof.
  intros n G a m m' H1 H2 Hav Hav2.
  exact (FOPrH_num5_unique n G a m m' (FOPrH_and_l _ _ _ _ H1) (FOPrH_and_l _ _ _ _ H2)
           ltac:(avoid_tms) ltac:(avoid_tms) Hav2).
Qed.

Lemma FOPrH_numr_cong : forall n G a m m',
  FOPrH n G (FONUMR a m) -> FOPrH n G (FOEq m m') -> FOtms_avoid [a; m; m'] 2 1000 ->
  FOPrH n G (FONUMR a m').
Proof.
  intros n G a m m' H E Hav.
  assert (K : forall t, FOtm_avoid t 2 1000 ->
             FOsubst_f 999 t (FONUMR a (FOVar 999)) = FONUMR a t).
  { intros t Ht.
    assert (Ht' : FOtms_avoid [t] 2 1000)
      by (apply FOtms_avoid_cons; [exact Ht | apply FOtms_avoid_nil]).
    rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_var_eq', (FOsubst_t_not_in a 999 t) by fr_tm. reflexivity. }
  assert (V : FOtm_avoid m 2 1000) by avoid_tm.
  assert (V' : FOtm_avoid m' 2 1000) by avoid_tm.
  pose proof (FOPrH_leibniz n G 999 m m' (FONUMR a (FOVar 999))
                ltac:(apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]) ltac:(apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms])
                E) as L.
  rewrite (K m V), (K m' V') in L. exact (L H).
Qed.

Lemma FOPrH_numr_of5 : forall n G a m w,
  FOPrH n G (FOTBLEX (FOnumeral 5) a FOZero FOZero m) ->
  FOtms_avoid [a; m] 2 1000 -> FOtms_avoid [a; m] 1001 1003 -> 1003 <= w ->
  FOfree_ctx w G -> FOtms_avoid [a; m] w (S w) ->
  FOPrH n G (FONUMR a m).
Proof.
  intros n G a m w H Hav Hav2 Hw HGw Havw.
  apply (FOPrH_numr_exists n G a w (FONUMR a m) ltac:(avoid_tms) ltac:(lia) HGw ltac:(free_fm)
           ltac:(avoid_tms)).
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (Hw' : FOPrH n Gc (FONUMR a (FOVar w))) by apply FOPrH_last end.
  pose proof (FOPrH_num5_unique n _ a (FOVar w) m (FOPrH_and_l _ _ _ _ Hw')
                (FOPrH_weak_app _ _ _ _ H) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms))
    as E.
  exact (FOPrH_numr_cong n _ a (FOVar w) m Hw' E ltac:(avoid_tms)).
Qed.

Lemma FOPrH_numr_inv0 : forall n G m,
  FOctx_avoid G 2 1000 -> FOtms_avoid [m] 2 1000 ->
  FOPrH n G (FONUMR FOZero m) -> FOPrH n G (FOcpairF (FOnumeral 1) FOZero m).
Proof.
  intros n G m HG Hm H. exact (FOPrH_num5_inv0 n G m HG Hm (FOPrH_and_l _ _ _ _ H)).
Qed.

Lemma FOPrH_numr_invS : forall n G a m w C,
  FOctx_avoid G 2 1000 -> FOtms_avoid [a; m] 2 1000 -> FOtms_avoid [a; m] 1001 1003 ->
  1003 <= w -> FOfree_ctx w G -> FOfree_ctx (S w) G -> FOfree_in w C = false ->
  FOtms_avoid [a; m] w (S (S w)) ->
  (forall v, 2 <= v -> v < 1000 -> FOfree_in v C = false) ->
  FOPrH n G (FONUMR (FOSucc a) m) ->
  FOPrH n (G ++ [FOcpairF (FOnumeral 2) (FOVar w) m; FONUMR a (FOVar w)]) C ->
  FOPrH n G C.
Proof.
  intros n G a m w C HG Hav Hav2 Hw HGw HGw' HCw Havw HCv H H0.
  apply (FOPrH_num5_invS n G a m w C HG Hav ltac:(lia) HGw HCw ltac:(avoid_tms) HCv
           (FOPrH_and_l _ _ _ _ H)).
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (T : FOPrH n Gc (FOTBLEX (FOnumeral 5) a FOZero FOZero (FOVar w))) by wk_in;
    assert (Cw : FOPrH n Gc (FOcpairF (FOnumeral 2) (FOVar w) m)) by wk_in;
    assert (HGw2 : FOfree_ctx (S w) Gc) by free_ctx
  end.
  pose proof (FOPrH_numr_of5 n _ a (FOVar w) (S w) T ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(lia) HGw2 ltac:(avoid_tms)) as Na.
  refine (FOPrH_cut _ _ _ C Na _).
  refine (FOPrH_weaken n _ _ C _ H0).
  intros Y HY. apply in_app_or in HY. destruct HY as [HY|[<-|[<-|[]]]].
  - repeat (apply in_or_app; left). exact HY.
  - apply in_or_app. left. apply in_or_app. right. left. reflexivity.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_numr_succ : forall n G a m m',
  FOctx_avoid G 2 1000 -> FOtms_avoid [a; m; m'] 2 1000 ->
  FOPrH n G (FONUMR a m) -> FOPrH n G (FOcpairF (FOnumeral 2) m m') ->
  FOPrH n G (FONUMR (FOSucc a) m').
Proof.
  intros n G a m m' HG Hav H HC.
  assert (HG5 : FOctx_avoid G 2 500) by (intros w ? ?; apply HG; lia).
  unfold FONUMR in H |- *.
  apply FOPrH_and_intro;
    [exact (FOPrH_num5_succ n G a m m' HG5 ltac:(avoid_tms) (FOPrH_and_l _ _ _ _ H) HC)|].
  apply FOPrH_and_intro.
  - apply FOPrH_all_intro; [apply HG; lia|]. apply FOPrH_all_intro; [apply HG; lia|].
    pose proof (FOPrH_all_same _ _ _ _ (FOPrH_all_same _ _ _ _
                  (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ H)))) as I2.
    exact (FOPrH_num2_succ n G (FOVar 802) (FOVar 803) m m' HG5 ltac:(avoid_tms) I2 HC).
  - apply FOPrH_all_intro; [apply HG; lia|].
    pose proof (FOPrH_all_same _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ H))) as I0.
    exact (FOPrH_num0_succ n G (FOVar 804) m m' HG5 ltac:(avoid_tms) I0 HC).
Qed.

(** ** Substitution of a term that does not mention the variable. *)

Lemma FOin_tm_subst_closed : forall u x y t, FOin_tm x t = false ->
  FOin_tm x (FOsubst_t y t u) = true -> FOin_tm x u = true.
Proof.
  induction u as [z| |a IH|a IHa b IHb|a IHa b IHb]; intros x y t Ht H; cbn in H |- *.
  - destruct (Nat.eqb z y); [rewrite Ht in H; discriminate | exact H].
  - exact H.
  - exact (IH x y t Ht H).
  - apply Bool.orb_true_iff in H. apply Bool.orb_true_iff.
    destruct H as [H|H]; [left; exact (IHa x y t Ht H) | right; exact (IHb x y t Ht H)].
  - apply Bool.orb_true_iff in H. apply Bool.orb_true_iff.
    destruct H as [H|H]; [left; exact (IHa x y t Ht H) | right; exact (IHb x y t Ht H)].
Qed.

Lemma FOfree_in_subst_closed : forall A x y t, FOin_tm x t = false ->
  FOfree_in x (FOsubst_f y t A) = true -> FOfree_in x A = true.
Proof.
  induction A as [a b| |B IHB C IHC|z B IHB|z B IHB]; intros x y t Ht H; cbn in H |- *.
  - apply Bool.orb_true_iff in H. apply Bool.orb_true_iff.
    destruct H as [H|H];
      [left; exact (FOin_tm_subst_closed a x y t Ht H)
      | right; exact (FOin_tm_subst_closed b x y t Ht H)].
  - exact H.
  - apply Bool.orb_true_iff in H. apply Bool.orb_true_iff.
    destruct H as [H|H]; [left; exact (IHB x y t Ht H) | right; exact (IHC x y t Ht H)].
  - destruct (Nat.eqb z y); [exact H|]. cbn in H.
    destruct (Nat.eqb z x); [exact H | exact (IHB x y t Ht H)].
  - destruct (Nat.eqb z y); [exact H|]. cbn in H.
    destruct (Nat.eqb z x); [exact H | exact (IHB x y t Ht H)].
Qed.

Lemma FOsubst_ok_subst_closed : forall A x s y t, FOin_tm x t = false ->
  FOsubst_ok x s A = true -> FOsubst_ok x s (FOsubst_f y t A) = true.
Proof.
  induction A as [a b| |B IHB C IHC|z B IHB|z B IHB]; intros x s y t Ht H; cbn in H |- *.
  - reflexivity.
  - reflexivity.
  - apply Bool.andb_true_iff in H as [H1 H2].
    rewrite (IHB x s y t Ht H1), (IHC x s y t Ht H2). reflexivity.
  - destruct (Nat.eqb z y); [exact H|]. cbn.
    destruct (Nat.eqb z x); [reflexivity|].
    destruct (FOfree_in x (FOsubst_f y t B)) eqn:E; [|reflexivity].
    rewrite (FOfree_in_subst_closed B x y t Ht E) in H.
    apply Bool.andb_true_iff in H as [H1 H2]. rewrite H1, (IHB x s y t Ht H2). reflexivity.
  - destruct (Nat.eqb z y); [exact H|]. cbn.
    destruct (Nat.eqb z x); [reflexivity|].
    destruct (FOfree_in x (FOsubst_f y t B)) eqn:E; [|reflexivity].
    rewrite (FOfree_in_subst_closed B x y t Ht E) in H.
    apply Bool.andb_true_iff in H as [H1 H2]. rewrite H1, (IHB x s y t Ht H2). reflexivity.
Qed.

(** ** Substitution into a substituted term. *)

Lemma FOsubst_t_subst_into : forall u x y s t, FOin_tm x u = false ->
  FOsubst_t x s (FOsubst_t y t u) = FOsubst_t y (FOsubst_t x s t) u.
Proof.
  induction u as [z| |a IH|a IHa b IHb|a IHa b IHb]; intros x y s t Hu; cbn in Hu |- *.
  - destruct (Nat.eqb z y); [reflexivity|]. cbn. rewrite Hu. reflexivity.
  - reflexivity.
  - rewrite (IH x y s t Hu). reflexivity.
  - apply Bool.orb_false_iff in Hu as [H1 H2].
    rewrite (IHa x y s t H1), (IHb x y s t H2). reflexivity.
  - apply Bool.orb_false_iff in Hu as [H1 H2].
    rewrite (IHa x y s t H1), (IHb x y s t H2). reflexivity.
Qed.

Lemma FOsubst_f_all_self : forall x s A, FOsubst_f x s (FOForall x A) = FOForall x A.
Proof. intros x s A. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma FOsubst_f_ex_self : forall x s A, FOsubst_f x s (FOExists x A) = FOExists x A.
Proof. intros x s A. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma FOsubst_f_subst_into : forall A x y s t, FOfree_in x A = false ->
  FOsubst_ok y t A = true ->
  FOsubst_f x s (FOsubst_f y t A) = FOsubst_f y (FOsubst_t x s t) A.
Proof.
  induction A as [a b| |B IHB C IHC|z B IHB|z B IHB]; intros x y s t Hx Hok.
  - cbn in Hx. apply Bool.orb_false_iff in Hx as [H1 H2]. cbn.
    rewrite (FOsubst_t_subst_into a x y s t H1), (FOsubst_t_subst_into b x y s t H2).
    reflexivity.
  - reflexivity.
  - cbn in Hx, Hok. apply Bool.orb_false_iff in Hx as [H1 H2].
    apply Bool.andb_true_iff in Hok as [K1 K2].
    cbn [FOsubst_f]. rewrite (IHB x y s t H1 K1), (IHC x y s t H2 K2). reflexivity.
  - destruct (Nat.eqb_spec z y) as [Ezy|Ezy].
    + subst z. rewrite !FOsubst_f_all_self. exact (FOsubst_f_not_free _ x s Hx).
    + rewrite (FOsubst_f_all_ne y t z B Ezy), (FOsubst_f_all_ne y (FOsubst_t x s t) z B Ezy).
      cbn [FOsubst_ok] in Hok. rewrite (proj2 (Nat.eqb_neq z y) Ezy) in Hok.
      destruct (Nat.eqb_spec z x) as [Ezx|Ezx].
      * subst z. rewrite FOsubst_f_all_self. f_equal.
        destruct (FOfree_in y B) eqn:Ey.
        -- apply Bool.andb_true_iff in Hok as [K1 _]. apply Bool.negb_true_iff in K1.
           rewrite (FOsubst_t_not_in t x s K1). reflexivity.
        -- rewrite !(FOsubst_f_not_free B y) by exact Ey. reflexivity.
      * rewrite FOsubst_f_all_ne by exact Ezx. f_equal.
        cbn [FOfree_in] in Hx. rewrite (proj2 (Nat.eqb_neq z x) Ezx) in Hx.
        destruct (FOfree_in y B) eqn:Ey.
        -- apply Bool.andb_true_iff in Hok as [_ K2]. exact (IHB x y s t Hx K2).
        -- rewrite !(FOsubst_f_not_free B y) by exact Ey.
           exact (FOsubst_f_not_free B x s Hx).
  - destruct (Nat.eqb_spec z y) as [Ezy|Ezy].
    + subst z. rewrite !FOsubst_f_ex_self. exact (FOsubst_f_not_free _ x s Hx).
    + rewrite (FOsubst_f_ex_ne y t z B Ezy), (FOsubst_f_ex_ne y (FOsubst_t x s t) z B Ezy).
      cbn [FOsubst_ok] in Hok. rewrite (proj2 (Nat.eqb_neq z y) Ezy) in Hok.
      destruct (Nat.eqb_spec z x) as [Ezx|Ezx].
      * subst z. rewrite FOsubst_f_ex_self. f_equal.
        destruct (FOfree_in y B) eqn:Ey.
        -- apply Bool.andb_true_iff in Hok as [K1 _]. apply Bool.negb_true_iff in K1.
           rewrite (FOsubst_t_not_in t x s K1). reflexivity.
        -- rewrite !(FOsubst_f_not_free B y) by exact Ey. reflexivity.
      * rewrite FOsubst_f_ex_ne by exact Ezx. f_equal.
        cbn [FOfree_in] in Hx. rewrite (proj2 (Nat.eqb_neq z x) Ezx) in Hx.
        destruct (FOfree_in y B) eqn:Ey.
        -- apply Bool.andb_true_iff in Hok as [_ K2]. exact (IHB x y s t Hx K2).
        -- rewrite !(FOsubst_f_not_free B y) by exact Ey.
           exact (FOsubst_f_not_free B x s Hx).
Qed.

Lemma FOsubst_ok_subst_into : forall A x y s t, FOfree_in x A = false ->
  FOsubst_ok y t A = true -> FOsubst_ok y s A = true ->
  FOsubst_ok x s (FOsubst_f y t A) = true.
Proof.
  induction A as [a b| |B IHB C IHC|z B IHB|z B IHB]; intros x y s t Hx Hok Hoks.
  - reflexivity.
  - reflexivity.
  - cbn in Hx, Hok, Hoks. apply Bool.orb_false_iff in Hx as [H1 H2].
    apply Bool.andb_true_iff in Hok as [K1 K2]. apply Bool.andb_true_iff in Hoks as [L1 L2].
    cbn [FOsubst_f FOsubst_ok]. rewrite (IHB x y s t H1 K1 L1), (IHC x y s t H2 K2 L2).
    reflexivity.
  - destruct (Nat.eqb_spec z y) as [Ezy|Ezy].
    + subst z. rewrite FOsubst_f_all_self. exact (FOsubst_ok_not_free _ x s Hx).
    + rewrite (FOsubst_f_all_ne y t z B Ezy).
      cbn [FOsubst_ok] in Hok, Hoks |- *.
      rewrite (proj2 (Nat.eqb_neq z y) Ezy) in Hok, Hoks.
      destruct (Nat.eqb_spec z x) as [Ezx|Ezx]; [reflexivity|].
      cbn [FOfree_in] in Hx. rewrite (proj2 (Nat.eqb_neq z x) Ezx) in Hx.
      destruct (FOfree_in x (FOsubst_f y t B)) eqn:E; [|reflexivity].
      destruct (FOfree_in y B) eqn:Ey.
      * apply Bool.andb_true_iff in Hok as [_ K2]. apply Bool.andb_true_iff in Hoks as [L1 L2].
        rewrite L1. exact (IHB x y s t Hx K2 L2).
      * rewrite (FOsubst_f_not_free B y t Ey), Hx in E. discriminate E.
  - destruct (Nat.eqb_spec z y) as [Ezy|Ezy].
    + subst z. rewrite FOsubst_f_ex_self. exact (FOsubst_ok_not_free _ x s Hx).
    + rewrite (FOsubst_f_ex_ne y t z B Ezy).
      cbn [FOsubst_ok] in Hok, Hoks |- *.
      rewrite (proj2 (Nat.eqb_neq z y) Ezy) in Hok, Hoks.
      destruct (Nat.eqb_spec z x) as [Ezx|Ezx]; [reflexivity|].
      cbn [FOfree_in] in Hx. rewrite (proj2 (Nat.eqb_neq z x) Ezx) in Hx.
      destruct (FOfree_in x (FOsubst_f y t B)) eqn:E; [|reflexivity].
      destruct (FOfree_in y B) eqn:Ey.
      * apply Bool.andb_true_iff in Hok as [_ K2]. apply Bool.andb_true_iff in Hoks as [L1 L2].
        rewrite L1. exact (IHB x y s t Hx K2 L2).
      * rewrite (FOsubst_f_not_free B y t Ey), Hx in E. discriminate E.
Qed.

(** ** Substitutions at distinct variables commute. *)

Lemma FOsubst_t_comm_gen : forall u x y s t, x <> y -> FOin_tm x t = false ->
  FOin_tm y s = false ->
  FOsubst_t x s (FOsubst_t y t u) = FOsubst_t y t (FOsubst_t x s u).
Proof.
  induction u as [z| |a IH|a IHa b IHb|a IHa b IHb]; intros x y s t Hxy Ht Hs.
  - cbn [FOsubst_t].
    destruct (Nat.eqb_spec z y) as [Ezy|Ezy]; destruct (Nat.eqb_spec z x) as [Ezx|Ezx].
    + lia.
    + subst z. rewrite (FOsubst_t_not_in t x s Ht), FOsubst_t_var_eq'. reflexivity.
    + subst z. rewrite (FOsubst_t_not_in s y t Hs), FOsubst_t_var_eq'. reflexivity.
    + rewrite !FOsubst_t_var_ne by assumption. reflexivity.
  - reflexivity.
  - cbn. rewrite (IH x y s t Hxy Ht Hs). reflexivity.
  - cbn. rewrite (IHa x y s t Hxy Ht Hs), (IHb x y s t Hxy Ht Hs). reflexivity.
  - cbn. rewrite (IHa x y s t Hxy Ht Hs), (IHb x y s t Hxy Ht Hs). reflexivity.
Qed.

Lemma FOsubst_f_comm_gen : forall A x y s t, x <> y -> FOin_tm x t = false ->
  FOin_tm y s = false ->
  FOsubst_f x s (FOsubst_f y t A) = FOsubst_f y t (FOsubst_f x s A).
Proof.
  induction A as [a b| |B IHB C IHC|z B IHB|z B IHB]; intros x y s t Hxy Ht Hs.
  - cbn. rewrite !(FOsubst_t_comm_gen _ x y s t Hxy Ht Hs). reflexivity.
  - reflexivity.
  - cbn [FOsubst_f]. rewrite (IHB x y s t Hxy Ht Hs), (IHC x y s t Hxy Ht Hs). reflexivity.
  - destruct (Nat.eqb_spec z y) as [Ezy|Ezy]; destruct (Nat.eqb_spec z x) as [Ezx|Ezx].
    + lia.
    + subst z. rewrite FOsubst_f_all_self, (FOsubst_f_all_ne x s y) by exact Ezx.
      rewrite FOsubst_f_all_self. reflexivity.
    + subst z. rewrite FOsubst_f_all_self, (FOsubst_f_all_ne y t x) by exact Ezy.
      rewrite FOsubst_f_all_self. reflexivity.
    + rewrite !FOsubst_f_all_ne by assumption. rewrite (IHB x y s t Hxy Ht Hs). reflexivity.
  - destruct (Nat.eqb_spec z y) as [Ezy|Ezy]; destruct (Nat.eqb_spec z x) as [Ezx|Ezx].
    + lia.
    + subst z. rewrite FOsubst_f_ex_self, (FOsubst_f_ex_ne x s y) by exact Ezx.
      rewrite FOsubst_f_ex_self. reflexivity.
    + subst z. rewrite FOsubst_f_ex_self, (FOsubst_f_ex_ne y t x) by exact Ezy.
      rewrite FOsubst_f_ex_self. reflexivity.
    + rewrite !FOsubst_f_ex_ne by assumption. rewrite (IHB x y s t Hxy Ht Hs). reflexivity.
Qed.

(** ** The provability matrix under substitution. *)

Lemma FOsubst_ok_PRMAT1 : forall cores s, FOtm_avoid s 2 252 ->
  FOsubst_ok 1 s (FOPRMAT cores) = true.
Proof.
  intros cores s Hs. unfold FOPRMAT. rewrite FOPRDER_p.
  do 16 (apply FOsubst_ok_ex; [apply Hs; lia|]).
  apply FOsubst_ok_PRDERp. apply (FOtm_avoid_sub s 2 252); [exact Hs | lia | lia].
Qed.

Lemma FOPRu_var1 : forall cores u0,
  FOPRu cores u0 (FOVar 1) = FOsubst_f 0 (FOnumeral u0) (FOPRMAT cores).
Proof. intros cores u0. unfold FOPRu, FOPRMATx, FOPRMAT. rewrite FOPRDER_p. reflexivity. Qed.

Definition PRuOK (c : FOTerm) : Prop := c = FOVar 1 \/ FOtm_avoid c 1 18.

Lemma FOPRu_as_subst : forall cores u0 c, PRuOK c ->
  FOPRu cores u0 c = FOsubst_f 0 (FOnumeral u0) (FOsubst_f 1 c (FOPRMAT cores)).
Proof.
  intros cores u0 c [->|Hc].
  - rewrite FOsubst_f_id. apply FOPRu_var1.
  - unfold FOPRu. rewrite FOsubst_f_PRMAT1 by exact Hc. reflexivity.
Qed.

Lemma FOsubst_f_PRu_gen : forall cores u0 x s c, 2 <= x -> FOin_tm 0 s = false ->
  FOtm_avoid c 2 252 -> PRuOK c -> PRuOK (FOsubst_t x s c) ->
  FOsubst_f x s (FOPRu cores u0 c) = FOPRu cores u0 (FOsubst_t x s c).
Proof.
  intros cores u0 x s c Hx Hs Hc Hc1 Hc2.
  rewrite (FOPRu_as_subst cores u0 c Hc1), (FOPRu_as_subst cores u0 _ Hc2).
  rewrite (FOsubst_f_comm_gen _ x 0 s (FOnumeral u0)) by (lia || apply FOin_tm_numeral || exact Hs).
  rewrite (FOsubst_f_subst_into (FOPRMAT cores) x 1 s c);
    [reflexivity | apply FOPRMAT_free; lia | apply FOsubst_ok_PRMAT1; exact Hc].
Qed.

Lemma FOsubst_f_PRu : forall cores u0 x s c, 2 <= x ->
  FOtms_avoid [s; c] 0 252 ->
  FOsubst_f x s (FOPRu cores u0 c) = FOPRu cores u0 (FOsubst_t x s c).
Proof.
  intros cores u0 x s c Hx Hav.
  apply FOsubst_f_PRu_gen; [exact Hx | fr_tm | avoid_tm | right; avoid_tm |].
  right. intros w Hw1 Hw2. destruct (FOin_tm w (FOsubst_t x s c)) eqn:E; [|reflexivity].
  destruct (FOin_tm x c) eqn:Ex.
  - exfalso. assert (Hs : FOin_tm w s = false) by fr_tm.
    assert (Hc : FOin_tm w c = false) by fr_tm.
    rewrite (FOin_tm_subst_closed c w x s Hs E) in Hc. discriminate.
  - rewrite (FOsubst_t_not_in c x s Ex) in E. assert (Hc : FOin_tm w c = false) by fr_tm.
    rewrite Hc in E. discriminate.
Qed.

Lemma FOsubst_f_PRu_var1 : forall cores u0 s, FOtm_avoid s 0 18 ->
  FOsubst_f 1 s (FOPRu cores u0 (FOVar 1)) = FOPRu cores u0 s.
Proof.
  intros cores u0 s Hs. rewrite FOPRu_var1.
  rewrite (FOsubst_f_comm_gen _ 1 0 s (FOnumeral u0))
    by first [lia | apply FOin_tm_numeral | apply Hs; lia].
  rewrite FOsubst_f_PRMAT1 by (apply (FOtm_avoid_sub s 0 18); [exact Hs | lia | lia]).
  reflexivity.
Qed.

Lemma FOsubst_ok_PRu : forall cores u0 x s c, 2 <= x ->
  FOtm_avoid c 2 252 -> PRuOK c -> FOtm_avoid s 2 252 ->
  FOsubst_ok x s (FOPRu cores u0 c) = true.
Proof.
  intros cores u0 x s c Hx Hc Hc1 Hs.
  rewrite (FOPRu_as_subst cores u0 c Hc1).
  apply FOsubst_ok_subst_closed; [apply FOin_tm_numeral|].
  apply FOsubst_ok_subst_into;
    [apply FOPRMAT_free; lia | apply FOsubst_ok_PRMAT1; exact Hc
    | apply FOsubst_ok_PRMAT1; exact Hs].
Qed.

Lemma FOsubst_ok_PRu_var1 : forall cores u0 s, FOtm_avoid s 2 252 ->
  FOsubst_ok 1 s (FOPRu cores u0 (FOVar 1)) = true.
Proof.
  intros cores u0 s Hs. rewrite FOPRu_var1.
  apply FOsubst_ok_subst_closed; [apply FOin_tm_numeral | apply FOsubst_ok_PRMAT1; exact Hs].
Qed.

Lemma FOfree_in_PRu_var1 : forall cores u0 w, w <> 1 ->
  FOfree_in w (FOPRu cores u0 (FOVar 1)) = false.
Proof.
  intros cores u0 w Hw. rewrite FOPRu_var1, FOsubst_f_num, FOfree_in_subst_num.
  destruct (Nat.eqb_spec w 0) as [->|Hw0]; [reflexivity|].
  apply FOPRMAT_free. lia.
Qed.

(** ** Provable instances as a formula.

    [PRIf cores u0 B0 env p]: every code of [p] over [env], described
    at base [B0], is provable. *)

Definition PRIf (cores : list nat) (u0 B0 : nat) (env : list FOTerm) (p : CPat) : FOFormula :=
  FOForall 1 (FOImplF (FOPATF B0 env p (FOVar 1)) (FOPRu cores u0 (FOVar 1))).

Lemma FOfree_in_PRIf : forall cores u0 B0 env p w, 2 <= B0 ->
  FOtms_avoid env w (S w) -> FOfree_in w (PRIf cores u0 B0 env p) = false.
Proof.
  intros cores u0 B0 env p w HB Hav. unfold PRIf. cbn [FOfree_in].
  destruct (Nat.eqb_spec 1 w) as [E|E]; [reflexivity|].
  apply Bool.orb_false_iff. split.
  - destruct (Nat.lt_ge_cases w 2) as [Hw|Hw].
    + apply FOfree_in_PATF_lo; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      exact Hav.
    + apply FOfree_in_PATF_any; [lia|]. apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      exact Hav.
  - apply FOfree_in_PRu_var1. lia.
Qed.

Lemma FOsubst_f_PRIf : forall cores u0 B0 env p x s, 2 <= x -> x < B0 ->
  FOsubst_f x s (PRIf cores u0 B0 env p) = PRIf cores u0 B0 (map (FOsubst_t x s) env) p.
Proof.
  intros cores u0 B0 env p x s Hx HB. unfold PRIf.
  rewrite FOsubst_f_all_ne by lia. rewrite FOsubst_f_impl, FOsubst_f_PATF by lia.
  rewrite FOsubst_t_var_ne by lia.
  rewrite (FOsubst_f_not_free (FOPRu cores u0 (FOVar 1))) by (apply FOfree_in_PRu_var1; lia).
  reflexivity.
Qed.

Lemma FOsubst_ok_PRIf : forall cores u0 B0 env p x s, 2 <= x ->
  FOin_tm 1 s = false -> FOtm_avoid s B0 (B0 + cpat_span p) ->
  FOsubst_ok x s (PRIf cores u0 B0 env p) = true.
Proof.
  intros cores u0 B0 env p x s Hx H1 Hs. unfold PRIf.
  apply FOsubst_ok_all; [exact H1|]. apply FOsubst_ok_impl; [apply FOsubst_ok_PATF; exact Hs|].
  apply FOsubst_ok_not_free. apply FOfree_in_PRu_var1. lia.
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (PRIf _ _ _ _ _) = false => apply FOfree_in_PRIf; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FODISPCASES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FODISPCASES_free
  | |- FOfree_in _ (FOSTEP5 _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOSTEP5_free
  | |- FOfree_in _ (FOTBLVALID _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOTBLVALID_free
  | |- FOfree_in _ (FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOlookup_free
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

(** ** Using an internal provable-instance fact. *)

Lemma FOPrH_prif_elim : forall n G cores u0 B0 env p c,
  FOPrH n G (PRIf cores u0 B0 env p) -> FOPrH n G (FOPATF B0 env p c) ->
  2 <= B0 -> FOtms_avoid env 1 2 -> FOtm_avoid c B0 (B0 + cpat_span p) ->
  FOtm_avoid c 0 252 ->
  FOPrH n G (FOPRu cores u0 c).
Proof.
  intros n G cores u0 B0 env p c H Hp HB Henv Hc Hc0.
  assert (Hc18 : FOtm_avoid c 0 18) by (apply (FOtm_avoid_sub c 0 252); [exact Hc0 | lia | lia]).
  assert (Hc2 : FOtm_avoid c 2 252) by (apply (FOtm_avoid_sub c 0 252); [exact Hc0 | lia | lia]).
  unfold PRIf in H.
  apply (FOPrH_inst n G 1 c) in H;
    [| apply FOsubst_ok_impl; [apply FOsubst_ok_PATF; exact Hc |
                               apply FOsubst_ok_PRu_var1; exact Hc2]].
  rewrite FOsubst_f_impl, FOsubst_f_PATF, FOsubst_t_var_eq', FOsubst_f_PRu_var1 in H
    by first [lia | exact Hc18].
  rewrite (FOsubst_map_avoid 1 c env) in H by (intros t Ht; apply (Henv t Ht); lia).
  exact (FOPrH_mp _ _ _ _ H Hp).
Qed.

(** ** Provable instances: monotonicity. *)

Lemma PRI_mono : forall n cores u0 V V' G G' p env, V <= V' ->
  (forall X, In X G -> In X G') ->
  PRI n cores u0 V G p env -> PRI n cores u0 V' G' p env.
Proof.
  intros n cores u0 V V' G G' p env HV Hinc HI G'' B c Hinc' HG0 Hc0 HBV Hcl Hc.
  exact (HI G'' B c (fun X HX => Hinc' X (Hinc X HX)) HG0 Hc0 ltac:(lia) Hcl Hc).
Qed.

Lemma PRI_efq : forall n cores u0 V G p env,
  FOPrH n G FOFalseF -> PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V G p env HF G' B c Hinc _ _ _ _ _.
  apply FOPrH_efq. exact (FOPrH_weaken n G G' _ Hinc HF).
Qed.

(** ** Pattern facts under substitution above their region. *)

Lemma FOsubst_f_PATF_hi : forall p x s B env d, B + cpat_span p <= x ->
  FOsubst_f x s (FOPATF B env p d) =
  FOPATF B (map (FOsubst_t x s) env) p (FOsubst_t x s d).
Proof.
  induction p as [k|j|q IH|a IHa b IHb]; intros x s B env d H;
    cbn [FOPATF cpat_span] in *.
  - rewrite FOsubst_f_eq, FOsubst_t_numeral. reflexivity.
  - rewrite FOsubst_f_eq, FOsubst_t_nth. reflexivity.
  - rewrite FOsubst_f_bex_ne by lia. rewrite FOsubst_f_and, FOsubst_f_eq, FOsubst_t_succ.
    rewrite IH by lia. rewrite !FOsubst_t_var_ne by lia. reflexivity.
  - pose proof (cpat_span_le a) as Ha.
    rewrite FOsubst_f_bex_ne by lia. rewrite FOsubst_f_bex_ne by lia.
    rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_and, !FOsubst_t_succ.
    rewrite IHa, IHb by lia. rewrite !FOsubst_t_var_ne by lia. reflexivity.
Qed.

(** ** Provable instances and their internal form. *)

Lemma PRIf_to_PRI : forall n cores u0 V G env p B0,
  FOPrH n G (PRIf cores u0 B0 env p) -> 500 <= B0 -> FOtms_avoid env B0 (B0 + cpat_span p) ->
  1000 <= V ->
  FOtms_avoid env 0 1000 -> (forall t, In t env -> forall w, V <= w -> FOin_tm w t = false) ->
  PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V G env p B0 HI HB0 HenvB HV Henv0 Henv.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  remember (B + B0 + cpat_span p + 1) as z eqn:Ez.
  assert (Hcz : FOtms_avoid [c] B (S (S z + cpat_span p))).
  { intros t [<-|[]] w ? ?. apply (Hcc c (or_introl eq_refl)). lia. }
  assert (Henvz : FOtms_avoid env V (S (S z + cpat_span p))).
  { intros t Ht w ? ?. apply (Henv t Ht). lia. }
  pose proof (FOPrH_patf_rebase p n G' B (S z) env c Hc ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros w ? ?; apply HGc; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms)) as Hc1.
  assert (Hex : FOPrH n G' (FOExists z (FOEq (FOVar z) c))).
  { apply (FOPrH_ex_intro n G' z c); [apply FOsubst_ok_eq|].
    rewrite FOsubst_f_eq, FOsubst_t_var_eq', (FOsubst_t_not_in c z c) by fr_tm.
    apply FOPrH_refl. }
  refine (FOPrH_ex_elim n G' z _ _ _ _ Hex _); [apply HGc; lia | free_fm |].
  lazymatch goal with |- FOPrH _ ?G2 _ =>
    assert (E : FOPrH n G2 (FOEq (FOVar z) c)) by apply FOPrH_last;
    assert (Hc2 : FOPrH n G2 (FOPATF (S z) env p c)) by wk Hc1;
    assert (HI2 : FOPrH n G2 (PRIf cores u0 B0 env p))
      by exact (FOPrH_weaken n G G2 _
                  (fun X HX => in_or_app _ _ _ (or_introl (Hinc X HX))) HI);
    assert (HG2 : FOctx_avoid G2 (S z) (S z + cpat_span p))
      by (intros w ? ?; apply FOfree_ctx_app_inv; [apply HGc; lia | free_ctx])
  end.
  assert (Hpz : FOPrH n (G' ++ [FOEq (FOVar z) c]) (FOPATF (S z) env p (FOVar z))).
  { pose proof (FOPrH_leibniz n _ z c (FOVar z) (FOPATF (S z) env p (FOVar z))
                  ltac:(apply FOsubst_ok_PATF; avoid_tm) ltac:(apply FOsubst_ok_PATF; avoid_tm)
                  (FOPrH_eq_sym _ _ _ _ E)) as L.
    rewrite !FOsubst_f_PATF in L by lia.
    rewrite !FOsubst_t_var_eq', (FOsubst_map_avoid z c env), (FOsubst_map_avoid z (FOVar z) env)
      in L by (intros t Ht; apply (Henv t Ht); lia).
    exact (L Hc2). }
  pose proof (FOPrH_patf_rebase p n _ (S z) B0 env (FOVar z) Hpz ltac:(lia) ltac:(lia)
                ltac:(lia) HG2 ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hp0.
  pose proof (FOPrH_prif_elim n _ cores u0 B0 env p (FOVar z) HI2 Hp0 ltac:(lia)
                ltac:(avoid_tms) ltac:(avoid_tm) ltac:(avoid_tm)) as Hpr.
  pose proof (FOPrH_leibniz n _ z (FOVar z) c (FOPRu cores u0 (FOVar z))
                ltac:(apply FOsubst_ok_PRu; [lia | avoid_tm | right; avoid_tm | avoid_tm])
                ltac:(apply FOsubst_ok_PRu; [lia | avoid_tm | right; avoid_tm | avoid_tm]) E)
    as L.
  rewrite FOsubst_f_id, FOsubst_f_PRu, FOsubst_t_var_eq' in L by first [lia | avoid_tms].
  exact (L Hpr).
Qed.

Lemma PRI_to_PRIf : forall n cores u0 V G env p B0,
  PRI n cores u0 V G p env -> V <= B0 -> 1000 <= V ->
  FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  FOtms_avoid env 0 1000 -> (forall t, In t env -> forall w, V <= w -> FOin_tm w t = false) ->
  FOPrH n G (PRIf cores u0 B0 env p).
Proof.
  intros n cores u0 V G env p B0 HI HVB HV HG0 HGV Henv0 Henv.
  remember (B0 + cpat_span p + 1) as z eqn:Ez.
  assert (Henvz : FOtms_avoid env V (S (S z + cpat_span p))).
  { intros t Ht w ? ?. apply (Henv t Ht). lia. }
  assert (Hz : FOPrH n G (FOForall z (FOImplF (FOPATF B0 env p (FOVar z))
                                        (FOPRu cores u0 (FOVar z))))).
  { apply FOPrH_all_intro; [apply HGV; lia|]. apply FOPrH_intro.
    assert (HP : forall w, 2 <= w -> w <> z -> (w < 1000 \/ V <= w) ->
               FOfree_in w (FOPATF B0 env p (FOVar z)) = false).
    { intros w Hw Hwz Hw'. apply FOfree_in_PATF_any; [lia|].
      apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      intros t Ht w' ? ?. destruct Hw' as [Hw'|Hw'];
        [apply (Henv0 t Ht); lia | apply (Henv t Ht); lia]. }
    assert (HP0 : forall w, w < 2 -> FOfree_in w (FOPATF B0 env p (FOVar z)) = false).
    { intros w Hw. apply FOfree_in_PATF_lo; [lia|].
      apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia|].
      intros t Ht w' ? ?. apply (Henv0 t Ht); lia. }
    assert (Hp : FOPrH n (G ++ [FOPATF B0 env p (FOVar z)]) (FOPATF B0 env p (FOVar z)))
      by apply FOPrH_last.
    pose proof (FOPrH_patf_rebase p n _ B0 (S z) env (FOVar z) Hp ltac:(lia) ltac:(lia)
                  ltac:(lia)
                  ltac:(intros w ? ?; apply FOfree_ctx_app_inv;
                        [apply HGV; lia | apply FOfree_ctx_cons;
                                          [apply HP; lia | apply FOfree_ctx_nil]])
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hp1.
    refine (HI _ (S z) (FOVar z) (fun X HX => in_or_app _ _ _ (or_introl HX)) _
              ltac:(avoid_tms) ltac:(lia) _ Hp1).
    - intros w ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      destruct (Nat.lt_ge_cases w 2) as [Hw2|Hw2]; [apply HP0; lia | apply HP; lia].
    - split.
      + intros w Hw. apply FOfree_ctx_app_inv; [apply HGV; lia|].
        apply FOfree_ctx_cons; [apply HP; lia | apply FOfree_ctx_nil].
      + intros t [<-|[]] w Hw. apply FOin_tm_var_ne. lia. }
  unfold PRIf. apply FOPrH_all_intro; [apply HG0; lia|].
  apply (FOPrH_inst n G z (FOVar 1)) in Hz;
    [| apply FOsubst_ok_impl;
       [apply FOsubst_ok_PATF; apply FOtm_avoid_var; lia
       | apply FOsubst_ok_PRu; [lia | avoid_tm | right; avoid_tm | avoid_tm]]].
  rewrite FOsubst_f_impl, FOsubst_f_PATF_hi in Hz by lia.
  rewrite (FOsubst_map_avoid z (FOVar 1) env) in Hz by (intros t Ht; apply (Henv t Ht); lia).
  rewrite (FOsubst_f_PRu_gen cores u0 z (FOVar 1) (FOVar z)) in Hz;
    [| lia | reflexivity | avoid_tm | right; avoid_tm | left; apply FOsubst_t_var_eq'].
  rewrite !FOsubst_t_var_eq' in Hz. exact Hz.
Qed.

(** ** Existential elimination for provable instances. *)

Lemma PRI_exe : forall n cores u0 V R G p env x X,
  FOPrH n G (FOExists x X) -> 1000 <= V ->
  FOtms_avoid env 0 1000 -> (forall t, In t env -> forall w, V <= w -> FOin_tm w t = false) ->
  (forall w, w < 1000 -> w <> x -> FOfree_in w X = false) ->
  (forall w, V <= w -> w <> x -> FOfree_in w X = false) ->
  (forall w, V <= w -> R <= w -> FOsubst_ok x (FOVar w) X = true) ->
  (forall w, V <= w -> R <= w -> PRI n cores u0 (S w) (G ++ [FOsubst_f x (FOVar w) X]) p env) ->
  PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V R G p env x X HE HV Henv0 Henv HXlo HXhi HXok HK.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  remember (B + x + cpat_span p + R + 1) as w eqn:Ew.
  assert (Hcz : FOtms_avoid [c] B (S (S w + cpat_span p))).
  { intros t [<-|[]] w' ? ?. apply (Hcc c (or_introl eq_refl)). lia. }
  assert (Henvz : FOtms_avoid env V (S (S w + cpat_span p))).
  { intros t Ht w' ? ?. apply (Henv t Ht). lia. }
  assert (HXw : forall w', FOfree_in w' (FOsubst_f x (FOVar w) X) = true ->
            w' = w \/ (w' <> x /\ FOfree_in w' X = true)).
  { intros w' H. destruct (Nat.eqb_spec w' w) as [->|Hne]; [left; reflexivity|right].
    split.
    - intro E. subst w'. rewrite FOfree_in_subst_away in H by lia. discriminate.
    - exact (FOfree_in_subst_closed X w' x (FOVar w) ltac:(apply FOin_tm_var_ne; lia) H). }
  pose proof (FOPrH_patf_rebase p n G' B (S w) env c Hc ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros w' ? ?; apply HGc; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms)) as Hc1.
  refine (FOPrH_ex_elim_fresh n G' x w X _ _ _ _ _ (FOPrH_weaken n G G' _ Hinc HE) _).
  - apply HGc. lia.
  - free_fm.
  - apply HXhi; lia.
  - apply HXok; lia.
  - refine (HK w ltac:(lia) ltac:(lia) _ (S w) c _ _ Hc0 (le_n _) _
              (FOPrH_weak_app _ _ _ _ Hc1)).
    + intros Y HY. apply in_app_or in HY. destruct HY as [HY|HY]; apply in_or_app;
        [left; exact (Hinc Y HY) | right; exact HY].
    + intros w' ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
      destruct (FOfree_in w' (FOsubst_f x (FOVar w) X)) eqn:E; [exfalso|reflexivity].
      destruct (HXw w' E) as [->|[Hne Hf]]; [lia|]. rewrite HXlo in Hf by lia. discriminate.
    + split.
      * intros w' Hw'. apply FOfree_ctx_app_inv; [apply HGc; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
        destruct (FOfree_in w' (FOsubst_f x (FOVar w) X)) eqn:E; [exfalso|reflexivity].
        destruct (HXw w' E) as [->|[Hne Hf]]; [lia|]. rewrite HXhi in Hf by lia. discriminate.
      * intros t [<-|[]] w' Hw'. apply (Hcc c (or_introl eq_refl)). lia.
Qed.

(** ** Case analysis on a formula. *)

Lemma PRI_cases : forall n cores u0 V G p env X,
  (forall w, w < 1000 -> FOfree_in w X = false) -> (forall w, V <= w -> FOfree_in w X = false) ->
  PRI n cores u0 V (G ++ [X]) p env -> PRI n cores u0 V (G ++ [FONeg X]) p env ->
  PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V G p env X HX0 HXV H1 H2 G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  assert (HN0 : forall w, w < 1000 -> FOfree_in w (FONeg X) = false).
  { intros w Hw. unfold FONeg. cbn [FOfree_in]. rewrite HX0 by exact Hw. reflexivity. }
  assert (HNV : forall w, V <= w -> FOfree_in w (FONeg X) = false).
  { intros w Hw. unfold FONeg. cbn [FOfree_in]. rewrite HXV by exact Hw. reflexivity. }
  apply (FOPrH_or_elim n G' X (FONeg X) _ (FOPrH_em n G' X)).
  - apply (H1 (G' ++ [X]) B c).
    + intros Y HY. apply in_app_or in HY. destruct HY as [HY|HY]; apply in_or_app;
        [left; exact (Hinc Y HY) | right; exact HY].
    + intros w ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
      apply FOfree_ctx_cons; [apply HX0; lia | apply FOfree_ctx_nil].
    + exact Hc0.
    + exact HBV.
    + split; [|exact Hcc]. intros w Hw. apply FOfree_ctx_app_inv; [apply HGc; lia|].
      apply FOfree_ctx_cons; [apply HXV; lia | apply FOfree_ctx_nil].
    + apply FOPrH_weak_app. exact Hc.
  - apply (H2 (G' ++ [FONeg X]) B c).
    + intros Y HY. apply in_app_or in HY. destruct HY as [HY|HY]; apply in_or_app;
        [left; exact (Hinc Y HY) | right; exact HY].
    + intros w ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
      apply FOfree_ctx_cons; [apply HN0; lia | apply FOfree_ctx_nil].
    + exact Hc0.
    + exact HBV.
    + split; [|exact Hcc]. intros w Hw. apply FOfree_ctx_app_inv; [apply HGc; lia|].
      apply FOfree_ctx_cons; [apply HNV; lia | apply FOfree_ctx_nil].
    + apply FOPrH_weak_app. exact Hc.
Qed.

(** ** Theorems. *)

Lemma FOPrH_pru_eq : forall n G cores u0 a b, FOPrH n G (FOEq a b) ->
  FOtms_avoid [a; b] 0 252 ->
  FOPrH n G (FOPRu cores u0 a) -> FOPrH n G (FOPRu cores u0 b).
Proof.
  intros n G cores u0 a b E Hav Ha.
  pose proof (FOPrH_leibniz n G 300 a b (FOPRu cores u0 (FOVar 300))
                ltac:(apply FOsubst_ok_PRu; [lia | avoid_tm | right; avoid_tm | avoid_tm])
                ltac:(apply FOsubst_ok_PRu; [lia | avoid_tm | right; avoid_tm | avoid_tm]) E) as L.
  rewrite !FOsubst_f_PRu, !FOsubst_t_var_eq' in L by first [lia | avoid_tms].
  exact (L Ha).
Qed.

Lemma PRI_closed : forall n k V G A, FOProvesTn 0 A -> 1000 <= V ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f (fun _ => None) A) [].
Proof.
  intros n k V G A HA HV G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  assert (Hcz : FOtms_avoid [c] B (B + 2 * cpat_span (cpat_f (fun _ => None) A) + 1)).
  { intros t [<-|[]] w ? ?. apply (Hcc c (or_introl eq_refl)). lia. }
  pose proof (FOPrH_patf_closed_code n G' A (B + cpat_span (cpat_f (fun _ => None) A))
                ltac:(lia)) as Hd.
  pose proof (FOPrH_patf_unique (cpat_f (fun _ => None) A) n G' B
                (B + cpat_span (cpat_f (fun _ => None) A)) [] c (FOnumeral (FOcode_f A)) Hc Hd
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros w ? ?; apply HGc; lia)
                ltac:(intros w ? ?; apply HGc; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms)) as E.
  exact (FOPrH_pru_eq n G' _ _ _ _ (FOPrH_eq_sym _ _ _ _ E) ltac:(avoid_tms)
           (FOPrH_pru_thm n G' k A HA)).
Qed.

Lemma EnvOK_snoc : forall n V G env m w, EnvOK n V G env -> FOPrH n G (FONUMR w m) ->
  FOtms_avoid [m] 0 1000 -> (forall w', V <= w' -> FOin_tm w' m = false) ->
  EnvOK n V G (env ++ [m]).
Proof.
  intros n V G env m w [HS [H0 [HV Hab]]] Hm Hm0 Hmv.
  split; [exact (SlotCtx_snoc n env G m w HS Hm)|]. split; [avoid_tms|]. split; [exact HV|].
  intros t Ht w' Hw'. apply in_app_or in Ht.
  destruct Ht as [Ht|[<-|[]]]; [exact (Hab t Ht w' Hw') | exact (Hmv w' Hw')].
Qed.

Lemma EnvOK_nil : forall n V G env, EnvOK n V G env -> EnvOK n V G [].
Proof.
  intros n V G env [[HG _] [_ [HV _]]]. split; [split; [exact HG | intros i Hi; cbn in Hi; lia]|].
  split; [apply FOtms_avoid_nil|]. split; [exact HV | intros t []].
Qed.

Fixpoint FOForalls (xs : list nat) (A : FOFormula) : FOFormula :=
  match xs with [] => A | x :: xs' => FOForall x (FOForalls xs' A) end.

Fixpoint rho_seq (xs : list nat) (k : nat) (rho : nat -> option nat) : nat -> option nat :=
  match xs with [] => rho | x :: xs' => rho_seq xs' (S k) (rho_sub (Some x) k rho) end.

Lemma rho_seq_out : forall xs k rho x, ~ In x xs -> rho_seq xs k rho x = rho x.
Proof.
  induction xs as [|y xs IH]; intros k rho x Hx; [reflexivity|].
  cbn [rho_seq]. rewrite IH by (intro H; apply Hx; right; exact H).
  unfold rho_sub. destruct (Nat.eqb_spec x y) as [->|Hne]; [|reflexivity].
  exfalso. apply Hx. left. reflexivity.
Qed.

Lemma rho_seq_nth : forall xs k rho i x, NoDup xs -> nth_error xs i = Some x ->
  rho_seq xs k rho x = Some (k + i).
Proof.
  induction xs as [|y xs IH]; intros k rho i x Hnd Hi; [destruct i; discriminate|].
  inversion Hnd as [|y' xs' Hy Hnd']. subst y' xs'.
  cbn [rho_seq]. destruct i as [|i]; cbn [nth_error] in Hi.
  - injection Hi as <-. rewrite rho_seq_out by exact Hy. unfold rho_sub.
    rewrite Nat.eqb_refl. f_equal. lia.
  - rewrite (IH (S k) _ i x Hnd' Hi). f_equal. lia.
Qed.

Lemma rho_seq_range : forall xs k rho, (forall z i, rho z = Some i -> i < k) ->
  forall z i, rho_seq xs k rho z = Some i -> i < k + length xs.
Proof.
  induction xs as [|y xs IH]; intros k rho Hr z i Hz; cbn [rho_seq length] in *.
  - specialize (Hr z i Hz). lia.
  - specialize (IH (S k) (rho_sub (Some y) k rho)).
    assert (Hr' : forall z i, rho_sub (Some y) k rho z = Some i -> i < S k).
    { intros z' i' Hz'. unfold rho_sub in Hz'. destruct (Nat.eqb z' y);
        [injection Hz' as <-; lia | specialize (Hr z' i' Hz'); lia]. }
    specialize (IH Hr' z i Hz). lia.
Qed.

Lemma PRI_insts : forall xs ms n cores u0 V G rho env A,
  length ms = length xs ->
  EnvOK n V G env -> (forall z i, rho z = Some i -> i < length env) ->
  (forall m, In m ms -> exists w, FOPrH n G (FONUMR w m)) ->
  FOtms_avoid ms 0 1000 -> (forall m, In m ms -> forall w, V <= w -> FOin_tm w m = false) ->
  PRI n cores u0 V G (cpat_f rho (FOForalls xs A)) env ->
  PRI n cores u0 V G (cpat_f (rho_seq xs (length env) rho) A) (env ++ ms).
Proof.
  induction xs as [|x xs IH]; intros ms n cores u0 V G rho env A Hlen HE Hrho Hnum Hm0 Hmv HI.
  - destruct ms; [|discriminate]. rewrite app_nil_r. exact HI.
  - destruct ms as [|m ms]; [discriminate|]. cbn [length] in Hlen. injection Hlen as Hlen.
    destruct (Hnum m (or_introl eq_refl)) as [w Hw].
    cbn [FOForalls] in HI.
    assert (Hm1 : FOtms_avoid [m] 0 1000) by avoid_tms.
    pose proof (PRI_inst n cores u0 V V G rho x (FOForalls xs A) env m w HE Hrho Hw Hm1
                  (le_n V) (Hmv m (or_introl eq_refl)) HI) as H1.
    replace (env ++ m :: ms) with ((env ++ [m]) ++ ms) by (rewrite <- app_assoc; reflexivity).
    cbn [rho_seq].
    replace (S (length env)) with (length (env ++ [m])) by (rewrite length_app; cbn; lia).
    apply IH; try assumption.
    + exact (EnvOK_snoc n V G env m w HE Hw Hm1 (Hmv m (or_introl eq_refl))).
    + intros z i Hz. rewrite length_app. cbn [length]. unfold rho_sub in Hz.
      destruct (Nat.eqb z x); [injection Hz as <-; lia | specialize (Hrho z i Hz); lia].
    + intros m' Hm'. apply Hnum. right. exact Hm'.
    + avoid_tms.
    + intros m' Hm'. apply Hmv. right. exact Hm'.
Qed.

(** ** Same formula, agreeing slots. *)

Definition SlotAgree (n : nat) (G : list FOFormula) (rho rho' : nat -> option nat)
    (env env' : list FOTerm) (z : nat) : Prop :=
  match rho z, rho' z with
  | Some i, Some j => FOPrH n G (FOEq (nth i env FOZero) (nth j env' FOZero))
  | None, None => True
  | _, _ => False
  end.

Lemma SlotAgree_weaken : forall n G G' rho rho' env env' z,
  (forall X, In X G -> In X G') ->
  SlotAgree n G rho rho' env env' z -> SlotAgree n G' rho rho' env env' z.
Proof.
  intros n G G' rho rho' env env' z Hinc H. unfold SlotAgree in *.
  destruct (rho z); destruct (rho' z); try exact H.
  exact (FOPrH_weaken n G G' _ Hinc H).
Qed.

Lemma CPrel_cpat_tm : forall t n G rho rho' env env',
  (forall z, FOin_tm z t = true -> SlotAgree n G rho rho' env env' z) ->
  CPrel n G env env' (cpat_tm rho t) (cpat_tm rho' t).
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros n G rho rho' env env' H;
    cbn [cpat_tm].
  - specialize (H y ltac:(cbn [FOin_tm]; apply Nat.eqb_refl)). unfold SlotAgree in H.
    destruct (rho y) as [i|]; destruct (rho' y) as [j|]; try contradiction.
    + apply cpr_slot. exact H.
    + repeat (first [apply cpr_pair | apply cpr_lit]).
  - repeat (first [apply cpr_pair | apply cpr_lit]).
  - unfold tSuccP. apply cpr_pair; [apply cpr_lit|]. apply IH. intros z Hz. apply H. exact Hz.
  - unfold tPlusP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair.
    + apply IHa. intros z Hz. apply H. cbn [FOin_tm]. rewrite Hz. reflexivity.
    + apply IHb. intros z Hz. apply H. cbn [FOin_tm]. rewrite Hz. apply Bool.orb_true_r.
  - unfold tMultP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair.
    + apply IHa. intros z Hz. apply H. cbn [FOin_tm]. rewrite Hz. reflexivity.
    + apply IHb. intros z Hz. apply H. cbn [FOin_tm]. rewrite Hz. apply Bool.orb_true_r.
Qed.

Lemma CPrel_cpat_f : forall A n G rho rho' env env',
  (forall z, FOfree_in z A = true -> SlotAgree n G rho rho' env env' z) ->
  CPrel n G env env' (cpat_f rho A) (cpat_f rho' A).
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros n G rho rho' env env' H;
    cbn [cpat_f].
  - unfold pEqP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair.
    + apply CPrel_cpat_tm. intros z Hz. apply H. cbn [FOfree_in]. rewrite Hz. reflexivity.
    + apply CPrel_cpat_tm. intros z Hz. apply H. cbn [FOfree_in]. rewrite Hz.
      apply Bool.orb_true_r.
  - repeat (first [apply cpr_pair | apply cpr_lit]).
  - unfold pImpP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair.
    + apply IHB. intros z Hz. apply H. cbn [FOfree_in]. rewrite Hz. reflexivity.
    + apply IHC. intros z Hz. apply H. cbn [FOfree_in]. rewrite Hz. apply Bool.orb_true_r.
  - unfold pAllP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair; [apply cpr_lit|].
    apply IHB. intros z Hz. unfold SlotAgree, rho_hide.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [exact I|].
    apply H. cbn [FOfree_in]. rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
  - unfold pExP. apply cpr_pair; [apply cpr_lit|]. apply cpr_pair; [apply cpr_lit|].
    apply IHB. intros z Hz. unfold SlotAgree, rho_hide.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [exact I|].
    apply H. cbn [FOfree_in]. rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
Qed.

Lemma PRI_reslot : forall n cores u0 V G A rho rho' env env',
  (forall z, FOfree_in z A = true -> SlotAgree n G rho rho' env env' z) ->
  (forall t, In t (env ++ env') -> forall w, V <= w -> FOin_tm w t = false) ->
  FOtms_avoid (env ++ env') 0 1000 -> 1000 <= V ->
  PRI n cores u0 V G (cpat_f rho A) env -> PRI n cores u0 V G (cpat_f rho' A) env'.
Proof.
  intros n cores u0 V G A rho rho' env env' H Hab H0 HV HI.
  apply (PRI_conv n cores u0 V G (cpat_f rho A) (cpat_f rho' A) env env'); try assumption.
  intros G' Hinc. apply CPrel_cpat_f. intros z Hz. exact (SlotAgree_weaken n G G' _ _ _ _ z Hinc (H z Hz)).
Qed.

(** ** Instances of theorems. *)

Definition fvs (A : FOFormula) : list nat :=
  filter (fun x => FOfree_in x A) (seq 0 (S (FOvars_max A))).

Lemma fvs_spec : forall A x, In x (fvs A) <-> FOfree_in x A = true.
Proof.
  intros A x. unfold fvs. rewrite filter_In, in_seq. split; [intros [_ H]; exact H|].
  intros H. split; [|exact H]. split; [lia|].
  destruct (Nat.le_gt_cases x (FOvars_max A)) as [Hle|Hgt]; [lia|].
  rewrite (FOfree_in_above A x Hgt) in H. discriminate.
Qed.

Lemma fvs_nodup : forall A, NoDup (fvs A).
Proof. intros A. apply NoDup_filter, seq_NoDup. Qed.

Definition slotval (rho : nat -> option nat) (env : list FOTerm) (x : nat) : FOTerm :=
  match rho x with Some j => nth j env FOZero | None => FOZero end.

Lemma PRI_thm : forall n k V G xs A rho env,
  FOProvesTn 0 (FOForalls xs A) -> NoDup xs ->
  (forall x, FOfree_in x A = true -> In x xs) ->
  EnvOK n V G env ->
  (forall x, In x xs -> exists j, rho x = Some j /\ j < length env) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho A) env.
Proof.
  intros n k V G xs A rho env Hthm Hnd Hfv HE Hxs.
  pose proof HE as [[HG2 HS] [Henv0 [HV Henv]]].
  assert (Hms : forall m, In m (map (slotval rho env) xs) -> In m env).
  { intros m Hm. apply in_map_iff in Hm. destruct Hm as [x [<- Hx]].
    destruct (Hxs x Hx) as [j [Hj Hjl]]. unfold slotval. rewrite Hj. apply nth_In. exact Hjl. }
  pose proof (PRI_closed n k V G (FOForalls xs A) Hthm HV) as H0.
  pose proof (PRI_insts xs (map (slotval rho env) xs) n (FOPrCores k) (FOu0 k) V G
                (fun _ => None) [] A ltac:(apply length_map) (EnvOK_nil n V G env HE)
                ltac:(intros z i Hz; discriminate)
                ltac:(intros m Hm; apply in_map_iff in Hm; destruct Hm as [x [<- Hx]];
                      destruct (Hxs x Hx) as [j [Hj Hjl]]; unfold slotval; rewrite Hj;
                      exact (HS j Hjl))
                ltac:(intros t Ht; apply Henv0; exact (Hms t Ht))
                ltac:(intros m Hm; exact (Henv m (Hms m Hm))) H0) as H1.
  cbn [length app] in H1.
  refine (PRI_reslot n _ _ V G A _ rho _ env _ _ _ HV H1).
  - intros z Hz. unfold SlotAgree.
    destruct (In_nth_error xs z (Hfv z Hz)) as [i Hi].
    rewrite (rho_seq_nth xs 0 _ i z Hnd Hi). cbn [Nat.add].
    destruct (Hxs z (Hfv z Hz)) as [j [Hj _]]. rewrite Hj.
    rewrite (nth_error_nth (map (slotval rho env) xs) i FOZero (x := slotval rho env z))
      by (rewrite nth_error_map, Hi; reflexivity).
    unfold slotval. rewrite Hj. apply FOPrH_refl.
  - intros t Ht. apply in_app_or in Ht. destruct Ht as [Ht|Ht]; [exact (Henv t (Hms t Ht)) | exact (Henv t Ht)].
  - intros t Ht. apply in_app_or in Ht. destruct Ht as [Ht|Ht]; [exact (Henv0 t (Hms t Ht)) | exact (Henv0 t Ht)].
Qed.

(** ** Free variables of a substitution instance. *)

Lemma FOin_tm_subst_gen : forall u w p s, FOin_tm w (FOsubst_t p s u) = true ->
  (w <> p /\ FOin_tm w u = true) \/ FOin_tm w s = true.
Proof.
  induction u as [z| |a IH|a IHa b IHb|a IHa b IHb]; intros w p s H; cbn [FOsubst_t] in H.
  - destruct (Nat.eqb_spec z p) as [->|Hzp]; [right; exact H|].
    left. cbn [FOin_tm] in H |- *. apply Nat.eqb_eq in H. subst z. split; [exact Hzp|].
    apply Nat.eqb_refl.
  - discriminate H.
  - cbn [FOin_tm] in H |- *. exact (IH w p s H).
  - cbn [FOin_tm] in H |- *. apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (IHa w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|] | right; exact H2].
      rewrite H2. reflexivity.
    + destruct (IHb w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|] | right; exact H2].
      rewrite H2. apply Bool.orb_true_r.
  - cbn [FOin_tm] in H |- *. apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (IHa w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|] | right; exact H2].
      rewrite H2. reflexivity.
    + destruct (IHb w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|] | right; exact H2].
      rewrite H2. apply Bool.orb_true_r.
Qed.

Lemma FOfree_in_subst_gen : forall A w p s, FOfree_in w (FOsubst_f p s A) = true ->
  (w <> p /\ FOfree_in w A = true) \/ FOin_tm w s = true.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros w p s H.
  - cbn [FOsubst_f FOfree_in] in H |- *. apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (FOin_tm_subst_gen a w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|]
        | right; exact H2]. rewrite H2. reflexivity.
    + destruct (FOin_tm_subst_gen b w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|]
        | right; exact H2]. rewrite H2. apply Bool.orb_true_r.
  - discriminate H.
  - cbn [FOsubst_f FOfree_in] in H |- *. apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (IHB w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|] | right; exact H2].
      rewrite H2. reflexivity.
    + destruct (IHC w p s H) as [[H1 H2]|H2]; [left; split; [exact H1|] | right; exact H2].
      rewrite H2. apply Bool.orb_true_r.
  - destruct (Nat.eqb_spec y p) as [->|Hyp].
    + rewrite FOsubst_f_all_self in H. left. split; [|exact H].
      intro E. subst w. cbn [FOfree_in] in H. rewrite Nat.eqb_refl in H. discriminate.
    + rewrite FOsubst_f_all_ne in H by exact Hyp. cbn [FOfree_in] in H |- *.
      destruct (Nat.eqb y w); [discriminate H|]. exact (IHB w p s H).
  - destruct (Nat.eqb_spec y p) as [->|Hyp].
    + rewrite FOsubst_f_ex_self in H. left. split; [|exact H].
      intro E. subst w. cbn [FOfree_in] in H. rewrite Nat.eqb_refl in H. discriminate.
    + rewrite FOsubst_f_ex_ne in H by exact Hyp. cbn [FOfree_in] in H |- *.
      destruct (Nat.eqb y w); [discriminate H|]. exact (IHB w p s H).
Qed.

Lemma FOfree_in_subst_false : forall A w p s, FOfree_in w A = false -> FOin_tm w s = false ->
  FOfree_in w (FOsubst_f p s A) = false.
Proof.
  intros A w p s H1 H2. destruct (FOfree_in w (FOsubst_f p s A)) eqn:E; [|reflexivity].
  destruct (FOfree_in_subst_gen A w p s E) as [[_ H]|H]; congruence.
Qed.

Lemma FOfree_in_TBLEX_lo : forall w tg a1 a2 a3 r, w < 2 ->
  FOtms_avoid [tg; a1; a2; a3; r] w (S w) -> FOtms_avoid [tg; a1; a2; a3; r] 13 18 ->
  FOfree_in w (FOTBLEX tg a1 a2 a3 r) = false.
Proof.
  intros w tg a1 a2 a3 r Hw Hav Hav2.
  assert (E : FOTBLEX tg a1 a2 a3 r =
              FOsubst_f 13 tg (FOsubst_f 14 a1 (FOsubst_f 15 a2 (FOsubst_f 16 a3 (FOsubst_f 17 r
                (FOTBLEX (FOVar 13) (FOVar 14) (FOVar 15) (FOVar 16) (FOVar 17))))))).
  { rewrite !FOsubst_f_TBLEX by lia.
    rewrite ?FOsubst_t_var_eq', ?FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in r 16 a3), (FOsubst_t_not_in r 15 a2), (FOsubst_t_not_in r 14 a1),
      (FOsubst_t_not_in r 13 tg), (FOsubst_t_not_in a3 15 a2), (FOsubst_t_not_in a3 14 a1),
      (FOsubst_t_not_in a3 13 tg), (FOsubst_t_not_in a2 14 a1), (FOsubst_t_not_in a2 13 tg),
      (FOsubst_t_not_in a1 13 tg) by fr_tm.
    reflexivity. }
  rewrite E.
  repeat (apply FOfree_in_subst_false; [|fr_tm]).
  destruct w as [|[|w]]; [vm_compute; reflexivity | vm_compute; reflexivity | lia].
Qed.

Lemma FOfree_in_TBLEX_all : forall w tg a1 a2 a3 r,
  FOtms_avoid [tg; a1; a2; a3; r] w (S w) -> FOtms_avoid [tg; a1; a2; a3; r] 13 18 ->
  FOfree_in w (FOTBLEX tg a1 a2 a3 r) = false.
Proof.
  intros w tg a1 a2 a3 r Hav Hav2. destruct (Nat.lt_ge_cases w 2) as [Hw|Hw].
  - exact (FOfree_in_TBLEX_lo w tg a1 a2 a3 r Hw Hav Hav2).
  - exact (FOfree_in_TBLEX_any w tg a1 a2 a3 r Hw Hav).
Qed.

Lemma FOfree_in_NUMR_all : forall w a m, FOtms_avoid [a; m] w (S w) ->
  FOtms_avoid [a; m] 13 18 -> FOtms_avoid [a; m] 802 805 ->
  FOfree_in w (FONUMR a m) = false.
Proof.
  intros w a m Hav H13 H802. unfold FONUMR. rewrite !FOfree_in_FOAnd.
  apply Bool.orb_false_iff. split; [apply FOfree_in_TBLEX_all; avoid_tms|].
  apply Bool.orb_false_iff. split.
  - cbn [FOfree_in]. destruct (Nat.eqb_spec 802 w) as [_|E1]; [reflexivity|].
    destruct (Nat.eqb_spec 803 w) as [_|E2]; [reflexivity|].
    apply FOfree_in_TBLEX_all; avoid_tms.
  - cbn [FOfree_in]. destruct (Nat.eqb_spec 804 w) as [_|E3]; [reflexivity|].
    apply FOfree_in_TBLEX_all; avoid_tms.
Qed.

Lemma FOfree_in_PRu_all : forall cores u0 w c, FOtms_avoid [c] w (S w) -> FOtm_avoid c 1 18 ->
  FOfree_in w (FOPRu cores u0 c) = false.
Proof.
  intros cores u0 w c Hav H1.
  rewrite (FOPRu_as_subst cores u0 c (or_intror H1)).
  destruct (FOfree_in w (FOsubst_f 0 (FOnumeral u0) (FOsubst_f 1 c (FOPRMAT cores)))) eqn:E;
    [|reflexivity].
  destruct (FOfree_in_subst_gen _ w 0 (FOnumeral u0) E) as [[Hw0 Hf]|Hn];
    [| rewrite FOin_tm_numeral in Hn; discriminate].
  destruct (FOfree_in_subst_gen _ w 1 c Hf) as [[Hw1 Hf']|Hc].
  - rewrite FOPRMAT_free in Hf' by lia. discriminate.
  - assert (Hc' : FOin_tm w c = false) by fr_tm. congruence.
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (PRIf _ _ _ _ _) = false => apply FOfree_in_PRIf; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FODISPCASES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FODISPCASES_free
  | |- FOfree_in _ (FOSTEP5 _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOSTEP5_free
  | |- FOfree_in _ (FOTBLVALID _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOTBLVALID_free
  | |- FOfree_in _ (FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOlookup_free
  | |- FOfree_in _ (FOPRu _ _ _) = false =>
      first [ apply FOfree_in_PRu; [nat_fast | avoid_tms]
            | apply FOfree_in_PRu_all; [avoid_tms | avoid_tm] ]
  | |- FOfree_in _ (FOTBLEX3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_TBLEX3_any; [nat_fast | avoid_tms]
  | |- FOfree_in ?w (FOBexC ?v _ _) = false =>
      first [ constr_eq w v; apply FOfree_in_FOBexC_self
            | rewrite FOBexC_ltv; free_fm ]
  | |- FOfree_in _ (FOJUSTCK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOJUSTCK_free
  | |- FOfree_in _ (FOGUARDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOGUARDC_free
  | |- FOfree_in _ (FONUMR _ _) = false =>
      first [ apply FOfree_in_NUMR_all; avoid_tms | unfold FONUMR; free_fm ]
  | |- FOfree_in _ (FOTBLEX _ _ _ _ _) = false =>
      first [ apply FOfree_in_TBLEX_any; [nat_fast | avoid_tms]
            | apply FOfree_in_TBLEX_all; [avoid_tms | avoid_tms] ]
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

(** ** Fresh numeral codes for provable instances. *)

Lemma PRI_numr_ex : forall n cores u0 V R G p env t,
  1000 <= V -> FOtms_avoid [t] 0 1000 -> (forall w, V <= w -> FOin_tm w t = false) ->
  FOtms_avoid env 0 1000 -> (forall s, In s env -> forall w, V <= w -> FOin_tm w s = false) ->
  (forall w, V <= w -> R <= w -> PRI n cores u0 (S w) (G ++ [FONUMR t (FOVar w)]) p env) ->
  PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V R G p env t HV Ht0 Htv Henv0 Henv HK.
  pose proof (FOPrH_thm n G _ (FOPr_numr n)) as H.
  apply (FOPrH_inst n G 800 t) in H;
    [| apply FOsubst_ok_ex; [fr_tm | apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]]].
  rewrite FOsubst_f_ex_ne, FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_t_var_eq', FOsubst_t_var_ne in H by lia.
  apply (PRI_exe n cores u0 V R G p env 801 (FONUMR t (FOVar 801)) H HV Henv0 Henv).
  - intros w Hw Hw'. free_fm.
  - intros w Hw Hw'. assert (Htw : FOtms_avoid [t] w (S w))
      by (intros s [<-|[]] w' ? ?; apply Htv; lia).
    free_fm.
  - intros w Hw _. apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms].
  - intros w Hw HR. assert (Htw : FOtms_avoid [t] w (S w))
      by (intros s [<-|[]] w' ? ?; apply Htv; lia).
    rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_var_eq', (FOsubst_t_not_in t 801 (FOVar w)) by fr_tm.
    exact (HK w Hw HR).
Qed.

Lemma PRI_numr_invS : forall n cores u0 V R G p env a m,
  FOPrH n G (FONUMR (FOSucc a) m) -> 1100 <= V ->
  FOtms_avoid [a; m] 0 1100 -> (forall t, In t [a; m] -> forall w, V <= w -> FOin_tm w t = false) ->
  FOtms_avoid env 0 1000 -> (forall s, In s env -> forall w, V <= w -> FOin_tm w s = false) ->
  (forall w, V <= w -> R <= w ->
     PRI n cores u0 (S w) (G ++ [FOcpairF (FOnumeral 2) (FOVar w) m; FONUMR a (FOVar w)]) p env) ->
  PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V R G p env a m H HV Ham0 Hamv Henv0 Henv HK.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  remember (B + cpat_span p + R + 1) as w eqn:Ew.
  assert (Hcz : FOtms_avoid [c] B (S (S (S w) + cpat_span p))).
  { intros t [<-|[]] w' ? ?. apply (Hcc c (or_introl eq_refl)). lia. }
  assert (Henvz : FOtms_avoid env V (S (S (S w) + cpat_span p))).
  { intros t Ht w' ? ?. apply (Henv t Ht). lia. }
  assert (Hamz : FOtms_avoid [a; m] V (S (S (S w) + cpat_span p))).
  { intros t Ht w' ? ?. apply (Hamv t Ht). lia. }
  pose proof (FOPrH_patf_rebase p n G' B (S w) env c Hc ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(intros w' ? ?; apply HGc; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms)) as Hc1.
  refine (FOPrH_numr_invS n G' a m w (FOPRu cores u0 c)
            ltac:(intros w' ? ?; apply HG0; lia) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(lia)
            ltac:(apply HGc; lia) ltac:(apply HGc; lia) ltac:(free_fm) ltac:(avoid_tms)
            ltac:(intros v ? ?; free_fm) (FOPrH_weaken n G G' _ Hinc H) _).
  refine (HK w ltac:(lia) ltac:(lia) _ (S w) c _ _ Hc0 (le_n _) _ (FOPrH_weak_app _ _ _ _ Hc1)).
  - intros Y HY. apply in_app_or in HY. destruct HY as [HY|HY]; apply in_or_app;
      [left; exact (Hinc Y HY) | right; exact HY].
  - intros w' ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|].
    apply FOfree_ctx_cons; [free_fm|]. apply FOfree_ctx_cons; [free_fm | apply FOfree_ctx_nil].
  - split.
    + intros w' Hw'. assert (Haw : FOtms_avoid [a; m] w' (S w'))
        by (intros t Ht w'' ? ?; apply (Hamv t Ht); lia).
      apply FOfree_ctx_app_inv; [apply HGc; lia|].
      apply FOfree_ctx_cons; [free_fm|]. apply FOfree_ctx_cons; [free_fm | apply FOfree_ctx_nil].
    + intros t [<-|[]] w' Hw'. apply (Hcc c (or_introl eq_refl)). lia.
Qed.

(** ** Instances of theorems with free variables. *)

Lemma FOForalls_gen : forall xs A, FOProvesTn 0 A -> FOProvesTn 0 (FOForalls xs A).
Proof.
  induction xs as [|x xs IH]; intros A H; [exact H|].
  cbn [FOForalls]. apply FOProvesTn_Gen. exact (IH A H).
Qed.

Lemma PRI_thm_open : forall n k V G A rho env,
  FOProvesTn 0 A -> EnvOK n V G env ->
  (forall x, FOfree_in x A = true -> exists j, rho x = Some j /\ j < length env) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho A) env.
Proof.
  intros n k V G A rho env HA HE Hx.
  apply (PRI_thm n k V G (fvs A) A rho env (FOForalls_gen (fvs A) A HA) (fvs_nodup A)).
  - intros x Hx'. apply fvs_spec. exact Hx'.
  - exact HE.
  - intros x Hx'. apply Hx. apply fvs_spec. exact Hx'.
Qed.

(** ** Holders: free variables renamed to holder variables. *)

Fixpoint hsub_tm (h : nat -> nat) (t : FOTerm) : FOTerm :=
  match t with
  | FOVar y => FOVar (h y)
  | FOZero => FOZero
  | FOSucc a => FOSucc (hsub_tm h a)
  | FOPlus a b => FOPlus (hsub_tm h a) (hsub_tm h b)
  | FOMult a b => FOMult (hsub_tm h a) (hsub_tm h b)
  end.

Definition h_hide (y : nat) (h : nat -> nat) : nat -> nat :=
  fun z => if Nat.eqb z y then y else h z.

Definition h_upd (y N : nat) (h : nat -> nat) : nat -> nat :=
  fun z => if Nat.eqb z y then N else h z.

Fixpoint hsub_f (h : nat -> nat) (A : FOFormula) : FOFormula :=
  match A with
  | FOEq a b => FOEq (hsub_tm h a) (hsub_tm h b)
  | FOFalseF => FOFalseF
  | FOImplF B C => FOImplF (hsub_f h B) (hsub_f h C)
  | FOForall y B => FOForall y (hsub_f (h_hide y h) B)
  | FOExists y B => FOExists y (hsub_f (h_hide y h) B)
  end.

Lemma hsub_tm_ext : forall t h h', (forall z, FOin_tm z t = true -> h z = h' z) ->
  hsub_tm h t = hsub_tm h' t.
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros h h' H; cbn [hsub_tm].
  - rewrite (H y ltac:(cbn [FOin_tm]; apply Nat.eqb_refl)). reflexivity.
  - reflexivity.
  - rewrite (IH h h' H). reflexivity.
  - rewrite (IHa h h'), (IHb h h'); [reflexivity| |];
      intros z Hz; apply H; cbn [FOin_tm]; rewrite Hz; [apply Bool.orb_true_r | reflexivity].
  - rewrite (IHa h h'), (IHb h h'); [reflexivity| |];
      intros z Hz; apply H; cbn [FOin_tm]; rewrite Hz; [apply Bool.orb_true_r | reflexivity].
Qed.

Lemma hsub_f_ext : forall A h h', (forall z, FOfree_in z A = true -> h z = h' z) ->
  hsub_f h A = hsub_f h' A.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros h h' H; cbn [hsub_f].
  - rewrite (hsub_tm_ext a h h'), (hsub_tm_ext b h h'); [reflexivity| |];
      intros z Hz; apply H; cbn [FOfree_in]; rewrite Hz; [apply Bool.orb_true_r | reflexivity].
  - reflexivity.
  - rewrite (IHB h h'), (IHC h h'); [reflexivity| |];
      intros z Hz; apply H; cbn [FOfree_in]; rewrite Hz; [apply Bool.orb_true_r | reflexivity].
  - f_equal. apply IHB. intros z Hz. unfold h_hide.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [reflexivity|].
    apply H. cbn [FOfree_in]. rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
  - f_equal. apply IHB. intros z Hz. unfold h_hide.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [reflexivity|].
    apply H. cbn [FOfree_in]. rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
Qed.

Lemma FOin_tm_hsub : forall t h w, FOin_tm w (hsub_tm h t) = true ->
  exists z, FOin_tm z t = true /\ h z = w.
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros h w H; cbn [hsub_tm FOin_tm] in H.
  - exists y. split; [cbn [FOin_tm]; apply Nat.eqb_refl | apply Nat.eqb_eq; exact H].
  - discriminate H.
  - exact (IH h w H).
  - apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (IHa h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOin_tm]. rewrite Hz. reflexivity.
    + destruct (IHb h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOin_tm]. rewrite Hz. apply Bool.orb_true_r.
  - apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (IHa h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOin_tm]. rewrite Hz. reflexivity.
    + destruct (IHb h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOin_tm]. rewrite Hz. apply Bool.orb_true_r.
Qed.

Lemma FOfree_in_hsub : forall A h w, FOfree_in w (hsub_f h A) = true ->
  exists z, FOfree_in z A = true /\ h z = w.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros h w H; cbn [hsub_f FOfree_in] in H.
  - apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (FOin_tm_hsub a h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOfree_in]. rewrite Hz. reflexivity.
    + destruct (FOin_tm_hsub b h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOfree_in]. rewrite Hz. apply Bool.orb_true_r.
  - discriminate H.
  - apply Bool.orb_true_iff in H. destruct H as [H|H].
    + destruct (IHB h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOfree_in]. rewrite Hz. reflexivity.
    + destruct (IHC h w H) as [z [Hz Ez]]. exists z. split; [|exact Ez].
      cbn [FOfree_in]. rewrite Hz. apply Bool.orb_true_r.
  - destruct (Nat.eqb_spec y w) as [->|Hyw]; [discriminate H|].
    destruct (IHB (h_hide y h) w H) as [z [Hz Ez]]. unfold h_hide in Ez.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [congruence|].
    exists z. split; [|exact Ez]. cbn [FOfree_in].
    rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
  - destruct (Nat.eqb_spec y w) as [->|Hyw]; [discriminate H|].
    destruct (IHB (h_hide y h) w H) as [z [Hz Ez]]. unfold h_hide in Ez.
    destruct (Nat.eqb_spec z y) as [->|Hzy]; [congruence|].
    exists z. split; [|exact Ez]. cbn [FOfree_in].
    rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz.
Qed.

Lemma h_hide_comm : forall y v h z, y <> v ->
  h_hide y (h_hide v h) z = h_hide v (h_hide y h) z.
Proof.
  intros y v h z Hyv. unfold h_hide.
  destruct (Nat.eqb_spec z y) as [Ezy|Ezy]; destruct (Nat.eqb_spec z v) as [Ezv|Ezv];
    subst; [lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma h_upd_hide_comm : forall y v N h z, y <> v ->
  h_upd v N (h_hide y h) z = h_hide y (h_upd v N h) z.
Proof.
  intros y v N h z Hyv. unfold h_hide, h_upd.
  destruct (Nat.eqb_spec z y) as [Ezy|Ezy]; destruct (Nat.eqb_spec z v) as [Ezv|Ezv];
    subst; [lia | reflexivity | reflexivity | reflexivity].
Qed.

Lemma hsub_tm_inst : forall t v N h, (forall z, z <> v -> FOin_tm z t = true -> h z <> v) ->
  FOsubst_t v (FOVar N) (hsub_tm (h_hide v h) t) = hsub_tm (h_upd v N h) t.
Proof.
  induction t as [y| |a IH|a IHa b IHb|a IHa b IHb]; intros v N h H; cbn [hsub_tm].
  - unfold h_hide, h_upd. destruct (Nat.eqb_spec y v) as [->|Hyv].
    + apply FOsubst_t_var_eq'.
    + apply FOsubst_t_var_ne. apply H; [exact Hyv | cbn [FOin_tm]; apply Nat.eqb_refl].
  - reflexivity.
  - rewrite FOsubst_t_succ, IH by exact H. reflexivity.
  - rewrite FOsubst_t_plus, IHa, IHb; [reflexivity| |];
      intros z Hz Hz'; apply H; try exact Hz; cbn [FOin_tm]; rewrite Hz';
      [apply Bool.orb_true_r | reflexivity].
  - rewrite FOsubst_t_mult, IHa, IHb; [reflexivity| |];
      intros z Hz Hz'; apply H; try exact Hz; cbn [FOin_tm]; rewrite Hz';
      [apply Bool.orb_true_r | reflexivity].
Qed.

Lemma hsub_f_inst : forall A v N h, (forall z, z <> v -> FOfree_in z A = true -> h z <> v) ->
  FOsubst_f v (FOVar N) (hsub_f (h_hide v h) A) = hsub_f (h_upd v N h) A.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros v N h H; cbn [hsub_f].
  - rewrite FOsubst_f_eq, !hsub_tm_inst; [reflexivity| |];
      intros z Hz Hz'; apply H; try exact Hz; cbn [FOfree_in]; rewrite Hz';
      [apply Bool.orb_true_r | reflexivity].
  - reflexivity.
  - rewrite FOsubst_f_impl, IHB, IHC; [reflexivity| |];
      intros z Hz Hz'; apply H; try exact Hz; cbn [FOfree_in]; rewrite Hz';
      [apply Bool.orb_true_r | reflexivity].
  - destruct (Nat.eqb_spec y v) as [->|Hyv].
    + rewrite FOsubst_f_all_self. f_equal. apply hsub_f_ext. intros z _.
      unfold h_hide, h_upd. destruct (Nat.eqb z v); reflexivity.
    + rewrite FOsubst_f_all_ne by exact Hyv. f_equal.
      rewrite (hsub_f_ext B (h_hide y (h_hide v h)) (h_hide v (h_hide y h)))
        by (intros z _; apply h_hide_comm; exact Hyv).
      rewrite IHB.
      * apply hsub_f_ext. intros z _. apply h_upd_hide_comm. exact Hyv.
      * intros z Hz Hz'. unfold h_hide. destruct (Nat.eqb_spec z y) as [->|Hzy]; [exact Hyv|].
        apply H; [exact Hz|]. cbn [FOfree_in].
        rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz'.
  - destruct (Nat.eqb_spec y v) as [->|Hyv].
    + rewrite FOsubst_f_ex_self. f_equal. apply hsub_f_ext. intros z _.
      unfold h_hide, h_upd. destruct (Nat.eqb z v); reflexivity.
    + rewrite FOsubst_f_ex_ne by exact Hyv. f_equal.
      rewrite (hsub_f_ext B (h_hide y (h_hide v h)) (h_hide v (h_hide y h)))
        by (intros z _; apply h_hide_comm; exact Hyv).
      rewrite IHB.
      * apply hsub_f_ext. intros z _. apply h_upd_hide_comm. exact Hyv.
      * intros z Hz Hz'. unfold h_hide. destruct (Nat.eqb_spec z y) as [->|Hzy]; [exact Hyv|].
        apply H; [exact Hz|]. cbn [FOfree_in].
        rewrite (proj2 (Nat.eqb_neq y z) (not_eq_sym Hzy)). exact Hz'.
Qed.

Lemma hsub_f_ok : forall A h x s W, FOvars_max A < W ->
  (forall w, FOin_tm w s = true -> W <= w) -> FOsubst_ok x s (hsub_f h A) = true.
Proof.
  induction A as [a b| |B IHB C IHC|y B IHB|y B IHB]; intros h x s W HA Hs;
    cbn [hsub_f FOvars_max] in *.
  - reflexivity.
  - reflexivity.
  - apply FOsubst_ok_impl; [apply (IHB h x s W) | apply (IHC h x s W)]; try exact Hs; lia.
  - apply FOsubst_ok_all; [|apply (IHB (h_hide y h) x s W); [lia | exact Hs]].
    destruct (FOin_tm y s) eqn:E; [|reflexivity]. specialize (Hs y E). lia.
  - apply FOsubst_ok_ex; [|apply (IHB (h_hide y h) x s W); [lia | exact Hs]].
    destruct (FOin_tm y s) eqn:E; [|reflexivity]. specialize (Hs y E). lia.
Qed.

(** ** Side conditions from bounds above a level. *)

Definition opT (f : bool) (a b : FOTerm) : FOTerm := if f then FOPlus a b else FOMult a b.

Lemma FOsubst_t_opT : forall f x s a b,
  FOsubst_t x s (opT f a b) = opT f (FOsubst_t x s a) (FOsubst_t x s b).
Proof. intros [|]; reflexivity. Qed.

Lemma FOtm_avoid_opT : forall f a b lo hi, FOtm_avoid a lo hi -> FOtm_avoid b lo hi ->
  FOtm_avoid (opT f a b) lo hi.
Proof. intros [|] a b lo hi Ha Hb; [apply FOtm_avoid_plus | apply FOtm_avoid_mult]; assumption. Qed.

Lemma FOin_tm_opT : forall f w a b, FOin_tm w a = false -> FOin_tm w b = false ->
  FOin_tm w (opT f a b) = false.
Proof. intros [|] w a b Ha Hb; cbn [opT FOin_tm]; rewrite Ha, Hb; reflexivity. Qed.

Ltac avoid_tm ::=
  lazymatch goal with
  | |- FOtm_avoid (opT _ _ _) _ _ => apply FOtm_avoid_opT; avoid_tm
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
      first
        [ match goal with
          | H : FOtms_avoid ?L ?lo' ?hi' |- _ =>
              apply (FOtm_avoid_sub t lo' hi' lo hi); [apply H; in_list | nat_fast | nat_fast]
          end
        | match goal with
          | H : forall s, In s ?L -> forall w, ?V <= w -> FOin_tm w s = false |- _ =>
              let w := fresh "w" in let H1 := fresh "Hw" in let H2 := fresh "Hw" in
              intros w H1 H2; apply (H t ltac:(in_list) w); nat_fast
          end ]
  end.

Ltac fr_tm ::=
  lazymatch goal with
  | |- FOin_tm _ (opT _ _ _) = false => apply FOin_tm_opT; fr_tm
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
      first
        [ match goal with H : FOtms_avoid ?L ?lo ?hi |- _ =>
            apply (H t ltac:(in_list) w); nat_fast end
        | match goal with
          | H : forall s, In s ?L -> forall w, ?V <= w -> FOin_tm w s = false |- _ =>
              apply (H t ltac:(in_list) w); nat_fast
          end ]
  end.

Ltac free_ctx ::=
  lazymatch goal with
  | |- FOfree_ctx _ (_ ++ _) => apply FOfree_ctx_app_inv; free_ctx
  | |- FOfree_ctx _ (_ :: _) => apply FOfree_ctx_cons; [free_fm | free_ctx]
  | |- FOfree_ctx _ [] => apply FOfree_ctx_nil
  | |- FOfree_ctx ?w ?G =>
      first [ assumption
            | match goal with HG : FOctx_avoid G ?lo ?hi |- _ => apply HG; nat_fast end
            | match goal with HG : forall w, ?V <= w -> FOfree_ctx w G |- _ =>
                apply HG; nat_fast end ]
  end.

(** ** Numeral codes along an equation of their numbers. *)

Lemma FOPrH_numr_cong1 : forall n G a b m,
  FOPrH n G (FONUMR a m) -> FOPrH n G (FOEq a b) ->
  FOtms_avoid [a; b; m] 2 50 -> FOtms_avoid [a; b; m] 802 805 -> FOtms_avoid [m] 999 1000 ->
  FOPrH n G (FONUMR b m).
Proof.
  intros n G a b m H E Hav Hav2 Hm.
  assert (K : forall t, FOtms_avoid [t] 2 50 -> FOtms_avoid [t] 802 805 ->
             FOsubst_f 999 t (FONUMR (FOVar 999) m) = FONUMR t m).
  { intros t Ht1 Ht2. rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_var_eq', (FOsubst_t_not_in m 999 t) by fr_tm. reflexivity. }
  pose proof (FOPrH_leibniz n G 999 a b (FONUMR (FOVar 999) m)
                ltac:(apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms])
                ltac:(apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]) E) as L.
  rewrite (K a), (K b) in L by avoid_tms. exact (L H).
Qed.

(** ** Sums and products of numerals, inside the provability predicate.

    [PhiOp]: every numeral code [a] of [Nt] and code [b] of [x op Nt]
    give a provable instance of the pattern [P] over [m1; a; b]. *)

Definition PhiOp (cores : list nat) (u0 B0 a b : nat) (f : bool) (x m1 : FOTerm) (P : CPat)
    (Nt : FOTerm) : FOFormula :=
  FOForall a (FOForall b (FOImplF (FONUMR Nt (FOVar a))
    (FOImplF (FONUMR (opT f x Nt) (FOVar b)) (PRIf cores u0 B0 [m1; FOVar a; FOVar b] P)))).

Lemma PhiOp_subst : forall cores u0 B0 a b f x m1 P N s,
  N <> a -> N <> b -> 1000 <= N -> N < B0 -> FOtms_avoid [s] 802 805 ->
  FOin_tm N x = false -> FOin_tm N m1 = false ->
  FOsubst_f N s (PhiOp cores u0 B0 a b f x m1 P (FOVar N)) = PhiOp cores u0 B0 a b f x m1 P s.
Proof.
  intros cores u0 B0 a b f x m1 P N s Ha Hb HN HB Hs Hx Hm1. unfold PhiOp.
  rewrite (FOsubst_f_all_ne N s a) by lia. rewrite (FOsubst_f_all_ne N s b) by lia.
  rewrite !FOsubst_f_impl, !FOsubst_f_NUMR by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf by lia. cbn [map].
  rewrite FOsubst_t_opT, FOsubst_t_var_eq', !FOsubst_t_var_ne by lia.
  rewrite (FOsubst_t_not_in x N s Hx), (FOsubst_t_not_in m1 N s Hm1). reflexivity.
Qed.

Lemma PhiOp_inst : forall n G cores u0 B0 a b f x m1 P Nt ta tb,
  FOPrH n G (PhiOp cores u0 B0 a b f x m1 P Nt) ->
  a <> b -> 1000 <= a -> 1000 <= b -> a < B0 -> b < B0 ->
  FOtms_avoid [Nt; x; m1] a (S a) -> FOtms_avoid [Nt; x; m1; ta] b (S b) ->
  FOtms_avoid [ta; tb] 0 1000 -> FOtms_avoid [ta; tb] B0 (B0 + cpat_span P) ->
  FOPrH n G (FOImplF (FONUMR Nt ta)
    (FOImplF (FONUMR (opT f x Nt) tb) (PRIf cores u0 B0 [m1; ta; tb] P))).
Proof.
  intros n G cores u0 B0 a b f x m1 P Nt ta tb H Hab Ha Hb HaB HbB Hava Havb Hav0 HavB.
  unfold PhiOp in H.
  apply (FOPrH_inst n G a ta) in H;
    [| apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_impl;
       [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite (FOsubst_f_all_ne a ta b) in H by lia.
  rewrite !FOsubst_f_impl, !FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf in H by lia. cbn [map] in H.
  rewrite FOsubst_t_opT, FOsubst_t_var_eq', FOsubst_t_var_ne in H by lia.
  rewrite (FOsubst_t_not_in Nt a ta), (FOsubst_t_not_in x a ta), (FOsubst_t_not_in m1 a ta)
    in H by fr_tm.
  apply (FOPrH_inst n G b tb) in H;
    [| apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite !FOsubst_f_impl, !FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf in H by lia. cbn [map] in H.
  rewrite FOsubst_t_opT, FOsubst_t_var_eq' in H.
  rewrite (FOsubst_t_not_in Nt b tb), (FOsubst_t_not_in x b tb), (FOsubst_t_not_in m1 b tb),
    (FOsubst_t_not_in ta b tb) in H by fr_tm.
  exact H.
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (PhiOp _ _ _ _ _ _ _ _ _ _) = false => unfold PhiOp; free_fm
  | |- FOfree_in _ (PRIf _ _ _ _ _) = false => apply FOfree_in_PRIf; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FODISPCASES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FODISPCASES_free
  | |- FOfree_in _ (FOSTEP5 _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOSTEP5_free
  | |- FOfree_in _ (FOTBLVALID _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOTBLVALID_free
  | |- FOfree_in _ (FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOlookup_free
  | |- FOfree_in _ (FOPRu _ _ _) = false =>
      first [ apply FOfree_in_PRu; [nat_fast | avoid_tms]
            | apply FOfree_in_PRu_all; [avoid_tms | avoid_tm] ]
  | |- FOfree_in _ (FOTBLEX3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_TBLEX3_any; [nat_fast | avoid_tms]
  | |- FOfree_in ?w (FOBexC ?v _ _) = false =>
      first [ constr_eq w v; apply FOfree_in_FOBexC_self
            | rewrite FOBexC_ltv; free_fm ]
  | |- FOfree_in _ (FOJUSTCK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOJUSTCK_free
  | |- FOfree_in _ (FOGUARDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOGUARDC_free
  | |- FOfree_in _ (FONUMR _ _) = false =>
      first [ apply FOfree_in_NUMR_all; avoid_tms | unfold FONUMR; free_fm ]
  | |- FOfree_in _ (FOTBLEX _ _ _ _ _) = false =>
      first [ apply FOfree_in_TBLEX_any; [nat_fast | avoid_tms]
            | apply FOfree_in_TBLEX_all; [avoid_tms | avoid_tms] ]
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

(** ** Slot maps and small environments. *)

Definition rhoN (k : nat) : nat -> option nat := fun z => if Nat.ltb z k then Some z else None.

Lemma rhoN_range : forall k z i, rhoN k z = Some i -> i < k.
Proof.
  intros k z i H. unfold rhoN in H.
  destruct (Nat.ltb_spec z k); [injection H as <-; lia | discriminate].
Qed.

Lemma fv_small : forall A z, FOfree_in z A = true -> z <= FOvars_max A.
Proof.
  intros A z H. destruct (Nat.le_gt_cases z (FOvars_max A)) as [Hle|Hgt]; [exact Hle|].
  rewrite (FOfree_in_above A z Hgt) in H. discriminate.
Qed.

Lemma rhoN_fv : forall k A, FOvars_max A < k ->
  forall z, FOfree_in z A = true -> exists j, rhoN k z = Some j /\ j < k.
Proof.
  intros k A HA z Hz. pose proof (fv_small A z Hz). exists z. unfold rhoN.
  destruct (Nat.ltb_spec z k); [split; [reflexivity | lia] | lia].
Qed.

Lemma EnvOK3 : forall n V G a b c wa wb wc, FOctx_avoid G 2 1000 ->
  FOPrH n G (FONUMR wa a) -> FOPrH n G (FONUMR wb b) -> FOPrH n G (FONUMR wc c) ->
  FOtms_avoid [a; b; c] 0 1000 -> 1000 <= V ->
  (forall t, In t [a; b; c] -> forall w, V <= w -> FOin_tm w t = false) ->
  EnvOK n V G [a; b; c].
Proof.
  intros n V G a b c wa wb wc HG Ha Hb Hc H0 HV Hab.
  split; [split; [exact HG|] | split; [exact H0 | split; [exact HV | exact Hab]]].
  intros [|[|[|i]]] Hi; cbn [nth];
    [exists wa; exact Ha | exists wb; exact Hb | exists wc; exact Hc | cbn in Hi; lia].
Qed.

Lemma EnvOK4 : forall n V G a b c d wa wb wc wd, FOctx_avoid G 2 1000 ->
  FOPrH n G (FONUMR wa a) -> FOPrH n G (FONUMR wb b) -> FOPrH n G (FONUMR wc c) ->
  FOPrH n G (FONUMR wd d) ->
  FOtms_avoid [a; b; c; d] 0 1000 -> 1000 <= V ->
  (forall t, In t [a; b; c; d] -> forall w, V <= w -> FOin_tm w t = false) ->
  EnvOK n V G [a; b; c; d].
Proof.
  intros n V G a b c d wa wb wc wd HG Ha Hb Hc Hd H0 HV Hab.
  split; [split; [exact HG|] | split; [exact H0 | split; [exact HV | exact Hab]]].
  intros [|[|[|[|i]]]] Hi; cbn [nth];
    [exists wa; exact Ha | exists wb; exact Hb | exists wc; exact Hc | exists wd; exact Hd
    | cbn in Hi; lia].
Qed.

Ltac cprel_tac :=
  repeat first
    [ apply cpr_lit
    | apply cpr_slot; cbn [nth]; first [apply FOPrH_refl | eassumption]
    | apply cpr_zero_r; cbn [nth]; eassumption
    | apply cpr_zero_l; cbn [nth]; eassumption
    | apply cpr_succ_r; cbn [nth]; eassumption
    | apply cpr_succ_l; cbn [nth]; eassumption
    | apply cpr_pair ].

Ltac above_tac :=
  let t := fresh "t" in let Ht := fresh "Ht" in let w0 := fresh "w0" in
  let Hw0 := fresh "Hw0" in
  intros t Ht w0 Hw0; cbn [In app] in Ht;
  repeat match type of Ht with
         | _ \/ _ => destruct Ht as [<-|Ht]; [fr_tm|]
         | False => destruct Ht
         end.

(** ** The induction on the second summand or factor. *)

Lemma PRI_opind : forall n k V G f x m1 y m2 m3 P,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  FOtms_avoid [x; m1; y; m2; m3] 0 1100 ->
  (forall t, In t [x; m1; y; m2; m3] -> forall w, V <= w -> FOin_tm w t = false) ->
  FOPrH n G (FONUMR y m2) -> FOPrH n G (FONUMR (opT f x y) m3) ->
  PRI n (FOPrCores k) (FOu0 k) (V + 3)
    ((G ++ [FONUMR FOZero (FOVar (V + 1))]) ++ [FONUMR (opT f x FOZero) (FOVar (V + 2))])
    P [m1; FOVar (V + 1); FOVar (V + 2)] ->
  PRI n (FOPrCores k) (FOu0 k) (V + 3)
    (((G ++ [PhiOp (FOPrCores k) (FOu0 k) (V + 3) (V + 1) (V + 2) f x m1 P (FOVar V)])
       ++ [FONUMR (FOSucc (FOVar V)) (FOVar (V + 1))])
       ++ [FONUMR (opT f x (FOSucc (FOVar V))) (FOVar (V + 2))])
    P [m1; FOVar (V + 1); FOVar (V + 2)] ->
  PRI n (FOPrCores k) (FOu0 k) V G P [m1; m2; m3].
Proof.
  intros n k V G f x m1 y m2 m3 P HV HG0 HGV Hav0 Havv Hy Hxy Hbase Hstep.
  assert (HI : FOPrH n G (FOForall V
            (PhiOp (FOPrCores k) (FOu0 k) (V + 3) (V + 1) (V + 2) f x m1 P (FOVar V)))).
  { apply FOPrH_ind; [apply HGV; lia | |].
    - rewrite PhiOp_subst by first [lia | avoid_tms | fr_tm].
      unfold PhiOp.
      apply FOPrH_all_intro; [apply HGV; lia|]. apply FOPrH_all_intro; [apply HGV; lia|].
      apply FOPrH_intro. apply FOPrH_intro.
      apply (PRI_to_PRIf n _ _ (V + 3) _ [m1; FOVar (V + 1); FOVar (V + 2)] P (V + 3) Hbase);
        [lia | lia | intros w ? ?; free_ctx | intros w ?; free_ctx | avoid_tms | above_tac].
    - rewrite PhiOp_subst by first [lia | avoid_tms | fr_tm].
      unfold PhiOp at 2.
      apply FOPrH_all_intro; [free_ctx|].
      apply FOPrH_all_intro; [free_ctx|].
      apply FOPrH_intro. apply FOPrH_intro.
      apply (PRI_to_PRIf n _ _ (V + 3) _ [m1; FOVar (V + 1); FOVar (V + 2)] P (V + 3) Hstep);
        [lia | lia | intros w ? ?; free_ctx | intros w ?; free_ctx | avoid_tms | above_tac]. }
  apply (FOPrH_inst n G V y) in HI;
    [| unfold PhiOp; apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_all; [fr_tm|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite PhiOp_subst in HI by first [lia | avoid_tms | fr_tm].
  pose proof (PhiOp_inst n G _ _ (V + 3) (V + 1) (V + 2) f x m1 P y m2 m3 HI ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms) ltac:(avoid_tms)) as HI2.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ HI2 Hy) Hxy) as HP.
  exact (PRIf_to_PRI n _ _ V G [m1; m2; m3] P (V + 3) HP ltac:(lia) ltac:(avoid_tms)
           ltac:(lia) ltac:(avoid_tms) ltac:(above_tac)).
Qed.

(** ** Sums. *)

Definition fPlus3 : FOFormula := FOEq (FOPlus (FOVar 0) (FOVar 1)) (FOVar 2).

Lemma FOPr_plus_step :
  FOProvesTn 0 (FOImplF fPlus3 (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1))) (FOSucc (FOVar 2)))).
Proof.
  change (FOPrH 0 [] (FOImplF fPlus3
            (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1))) (FOSucc (FOVar 2))))).
  apply FOPrH_intro. cbn [app]. unfold fPlus3.
  eapply FOPrH_eq_trans; [apply FOPrH_Q_plus_succ|]. apply FOPrH_congS.
  apply FOPrH_assum. left. reflexivity.
Qed.

Lemma PRI_plus : forall n k V G x y m1 m2 m3,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  FOtms_avoid [x; m1; y; m2; m3] 0 1100 ->
  (forall t, In t [x; m1; y; m2; m3] -> forall w, V <= w -> FOin_tm w t = false) ->
  FOPrH n G (FONUMR x m1) -> FOPrH n G (FONUMR y m2) -> FOPrH n G (FONUMR (FOPlus x y) m3) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f (rhoN 3) fPlus3) [m1; m2; m3].
Proof.
  intros n k V G x y m1 m2 m3 HV HG0 HGV Hav0 Havv Hx Hy Hxy.
  apply (PRI_opind n k V G true x m1 y m2 m3 _ HV HG0 HGV Hav0 Havv Hy Hxy).
  - lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
      assert (HG1 : FOctx_avoid G1 0 1000) by (intros w ? ?; free_ctx);
      assert (Ha : FOPrH n G1 (FONUMR FOZero (FOVar (V + 1)))) by wk_in;
      assert (Hb : FOPrH n G1 (FONUMR (FOPlus x FOZero) (FOVar (V + 2)))) by wk_in;
      assert (Hx1 : FOPrH n G1 (FONUMR x m1)) by wk Hx
    end.
    pose proof (FOPrH_numr_cong1 n _ (FOPlus x FOZero) x (FOVar (V + 2)) Hb
                  (FOPrH_Q_plus_zero n _ x) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms))
      as E1.
    pose proof (FOPrH_numr_unique n _ x m1 (FOVar (V + 2)) Hx1 E1 ltac:(avoid_tms)
                  ltac:(avoid_tms)) as E2.
    pose proof (FOPrH_numr_inv0 n _ (FOVar (V + 1)) ltac:(intros w ? ?; apply HG1; lia)
                  ltac:(avoid_tms) Ha) as C0.
    assert (HE : EnvOK n (V + 3) ((G ++ [FONUMR FOZero (FOVar (V + 1))]) ++
                   [FONUMR (opT true x FOZero) (FOVar (V + 2))])
                   [m1; FOVar (V + 1); FOVar (V + 2)])
      by (apply (EnvOK3 n _ _ _ _ _ x FOZero (FOPlus x FOZero));
          [intros w ? ?; apply HG1; lia | exact Hx1 | exact Ha | exact Hb | avoid_tms | lia
          | above_tac]).
    pose proof (PRI_thm_open n k (V + 3) _ (FOEq (FOPlus (FOVar 0) FOZero) (FOVar 0)) (rhoN 3)
                  _ ltac:(change (FOPrH 0 [] (FOEq (FOPlus (FOVar 0) FOZero) (FOVar 0)));
                          apply FOPrH_Q_plus_zero)
                  HE (rhoN_fv 3 (FOEq (FOPlus (FOVar 0) FOZero) (FOVar 0))
                        ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T0.
    refine (PRI_conv n _ _ (V + 3) _ _ _ _ _ _ _ _ _ T0); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc C0) as C0'.
    pose proof (FOPrH_weaken n _ G' _ Hinc E2) as E2'.
    unfold fPlus3, rhoN. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
  - lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
      assert (HG1 : FOctx_avoid G1 0 1000) by (intros w ? ?; free_ctx);
      assert (HG1V : forall w, V + 3 <= w -> FOfree_ctx w G1) by (intros w ?; free_ctx);
      assert (HPhi : FOPrH n G1 (PhiOp (FOPrCores k) (FOu0 k) (V + 3) (V + 1) (V + 2) true x m1
                                  (cpat_f (rhoN 3) fPlus3) (FOVar V))) by wk_in;
      assert (Ha : FOPrH n G1 (FONUMR (FOSucc (FOVar V)) (FOVar (V + 1)))) by wk_in;
      assert (Hb : FOPrH n G1 (FONUMR (FOPlus x (FOSucc (FOVar V))) (FOVar (V + 2)))) by wk_in;
      assert (Hx1 : FOPrH n G1 (FONUMR x m1)) by wk Hx
    end.
    refine (PRI_numr_invS n _ _ (V + 3) (V + 3 + cpat_span (cpat_f (rhoN 3) fPlus3) + 1) _ _ _
              (FOVar V) (FOVar (V + 1)) Ha _ _ _ _ _ _);
      [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
    intros w Hw HR.
    lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
      assert (HG2 : FOctx_avoid G2 0 1000) by (intros w' ? ?; free_ctx);
      assert (Cw : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar w) (FOVar (V + 1)))) by wk_in;
      assert (Nw : FOPrH n G2 (FONUMR (FOVar V) (FOVar w))) by wk_in;
      assert (Hb2 : FOPrH n G2 (FONUMR (FOPlus x (FOSucc (FOVar V))) (FOVar (V + 2)))) by wk Hb
    end.
    pose proof (FOPrH_numr_cong1 n _ (FOPlus x (FOSucc (FOVar V))) (FOSucc (FOPlus x (FOVar V)))
                  (FOVar (V + 2)) Hb2 (FOPrH_Q_plus_succ n _ x (FOVar V)) ltac:(avoid_tms)
                  ltac:(avoid_tms) ltac:(avoid_tms)) as Hb3.
    refine (PRI_numr_invS n _ _ (S w) (V + 3 + cpat_span (cpat_f (rhoN 3) fPlus3) + 1) _ _ _
              (FOPlus x (FOVar V)) (FOVar (V + 2)) Hb3 _ _ _ _ _ _);
      [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
    intros w' Hw' HR'.
    lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
      assert (HG3 : FOctx_avoid G3 0 1000) by (intros w'' ? ?; free_ctx);
      assert (Cw' : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar w') (FOVar (V + 2)))) by wk_in;
      assert (Nw' : FOPrH n G3 (FONUMR (FOPlus x (FOVar V)) (FOVar w'))) by wk_in;
      assert (Cw3 : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar w) (FOVar (V + 1)))) by wk Cw;
      assert (Nw3 : FOPrH n G3 (FONUMR (FOVar V) (FOVar w))) by wk Nw;
      assert (HPhi3 : FOPrH n G3 (PhiOp (FOPrCores k) (FOu0 k) (V + 3) (V + 1) (V + 2) true x m1
                                   (cpat_f (rhoN 3) fPlus3) (FOVar V))) by wk HPhi;
      assert (Hx3 : FOPrH n G3 (FONUMR x m1)) by wk Hx1
    end.
    pose proof (PhiOp_inst n _ _ _ (V + 3) (V + 1) (V + 2) true x m1 _ (FOVar V) (FOVar w)
                  (FOVar w') HPhi3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as IH.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ IH Nw3) Nw') as IHf.
    pose proof (PRIf_to_PRI n _ _ (S w') _ _ _ (V + 3) IHf ltac:(lia) ltac:(avoid_tms) ltac:(lia)
                  ltac:(avoid_tms) ltac:(above_tac)) as IHP.
    assert (HE : EnvOK n (S w') _ [m1; FOVar w; FOVar w'])
      by (apply (EnvOK3 n _ _ _ _ _ x (FOVar V) (FOPlus x (FOVar V)));
          [intros w'' ? ?; apply HG3; lia | exact Hx3 | exact Nw3 | exact Nw' | avoid_tms | lia
          | above_tac]).
    pose proof (PRI_thm_open n k (S w') _ _ (rhoN 3) _ FOPr_plus_step HE
                  (rhoN_fv 3 (FOImplF fPlus3 (FOEq (FOPlus (FOVar 0) (FOSucc (FOVar 1)))
                                                 (FOSucc (FOVar 2))))
                     ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T1.
    pose proof (PRI_mp n _ _ (S w') _ (rhoN 3) _ _ _ HE (rhoN_range 3) T1 IHP) as T2.
    refine (PRI_conv n _ _ (S w') _ _ _ _ _ _ _ _ _ T2); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cw3) as C1.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cw') as C2.
    unfold fPlus3, rhoN. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
Qed.

(** ** Products. *)

Definition fTimes3 : FOFormula := FOEq (FOMult (FOVar 0) (FOVar 1)) (FOVar 2).

Lemma FOPr_times_zero : FOProvesTn 0 (FOEq (FOMult (FOVar 0) FOZero) FOZero).
Proof.
  change (FOPrH 0 [] (FOEq (FOMult (FOVar 0) FOZero) FOZero)). apply FOPrH_ring. fo_ring.
Qed.

Lemma FOPr_times_step :
  FOProvesTn 0 (FOImplF (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOVar 3))
                  (FOImplF (FOEq (FOPlus (FOVar 3) (FOVar 0)) (FOVar 2))
                     (FOEq (FOMult (FOVar 0) (FOSucc (FOVar 1))) (FOVar 2)))).
Proof.
  change (FOPrH 0 [] (FOImplF (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOVar 3))
                  (FOImplF (FOEq (FOPlus (FOVar 3) (FOVar 0)) (FOVar 2))
                     (FOEq (FOMult (FOVar 0) (FOSucc (FOVar 1))) (FOVar 2))))).
  apply FOPrH_intro. apply FOPrH_intro. cbn [app].
  apply (FOPrH_eq_trans _ _ _ (FOPlus (FOMult (FOVar 0) (FOVar 1)) (FOVar 0)));
    [apply FOPrH_ring; fo_ring|].
  apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar 3) (FOVar 0))).
  - apply FOPrH_congPlus; [apply FOPrH_assum; left; reflexivity | apply FOPrH_refl].
  - apply FOPrH_assum. right. left. reflexivity.
Qed.

Lemma PRI_times : forall n k V G x y m1 m2 m3,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  FOtms_avoid [x; m1; y; m2; m3] 0 1100 ->
  (forall t, In t [x; m1; y; m2; m3] -> forall w, V <= w -> FOin_tm w t = false) ->
  FOPrH n G (FONUMR x m1) -> FOPrH n G (FONUMR y m2) -> FOPrH n G (FONUMR (FOMult x y) m3) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f (rhoN 3) fTimes3) [m1; m2; m3].
Proof.
  intros n k V G x y m1 m2 m3 HV HG0 HGV Hav0 Havv Hx Hy Hxy.
  apply (PRI_opind n k V G false x m1 y m2 m3 _ HV HG0 HGV Hav0 Havv Hy Hxy).
  - lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
      assert (HG1 : FOctx_avoid G1 0 1000) by (intros w ? ?; free_ctx);
      assert (Ha : FOPrH n G1 (FONUMR FOZero (FOVar (V + 1)))) by wk_in;
      assert (Hb : FOPrH n G1 (FONUMR (FOMult x FOZero) (FOVar (V + 2)))) by wk_in;
      assert (Hx1 : FOPrH n G1 (FONUMR x m1)) by wk Hx
    end.
    pose proof (FOPrH_numr_cong1 n _ (FOMult x FOZero) FOZero (FOVar (V + 2)) Hb
                  ltac:(apply FOPrH_ring; fo_ring) ltac:(avoid_tms) ltac:(avoid_tms)
                  ltac:(avoid_tms)) as Hb0.
    pose proof (FOPrH_numr_inv0 n _ (FOVar (V + 1)) ltac:(intros w ? ?; apply HG1; lia)
                  ltac:(avoid_tms) Ha) as Ca.
    pose proof (FOPrH_numr_inv0 n _ (FOVar (V + 2)) ltac:(intros w ? ?; apply HG1; lia)
                  ltac:(avoid_tms) Hb0) as Cb.
    assert (HE : EnvOK n (V + 3) ((G ++ [FONUMR FOZero (FOVar (V + 1))]) ++
                   [FONUMR (opT false x FOZero) (FOVar (V + 2))])
                   [m1; FOVar (V + 1); FOVar (V + 2)])
      by (apply (EnvOK3 n _ _ _ _ _ x FOZero (FOMult x FOZero));
          [intros w ? ?; apply HG1; lia | exact Hx1 | exact Ha | exact Hb | avoid_tms | lia
          | above_tac]).
    pose proof (PRI_thm_open n k (V + 3) _ (FOEq (FOMult (FOVar 0) FOZero) FOZero) (rhoN 3)
                  _ FOPr_times_zero HE
                  (rhoN_fv 3 (FOEq (FOMult (FOVar 0) FOZero) FOZero)
                     ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T0.
    refine (PRI_conv n _ _ (V + 3) _ _ _ _ _ _ _ _ _ T0); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc Ca) as Ca'.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cb) as Cb'.
    unfold fTimes3, rhoN. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
  - lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
      assert (HG1 : FOctx_avoid G1 0 1000) by (intros w ? ?; free_ctx);
      assert (HPhi : FOPrH n G1 (PhiOp (FOPrCores k) (FOu0 k) (V + 3) (V + 1) (V + 2) false x m1
                                  (cpat_f (rhoN 3) fTimes3) (FOVar V))) by wk_in;
      assert (Ha : FOPrH n G1 (FONUMR (FOSucc (FOVar V)) (FOVar (V + 1)))) by wk_in;
      assert (Hb : FOPrH n G1 (FONUMR (FOMult x (FOSucc (FOVar V))) (FOVar (V + 2)))) by wk_in;
      assert (Hx1 : FOPrH n G1 (FONUMR x m1)) by wk Hx
    end.
    refine (PRI_numr_invS n _ _ (V + 3) (V + 3 + cpat_span (cpat_f (rhoN 3) fTimes3) + 1) _ _ _
              (FOVar V) (FOVar (V + 1)) Ha _ _ _ _ _ _);
      [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
    intros w Hw HR.
    refine (PRI_numr_ex n _ _ (S w) (V + 3 + cpat_span (cpat_f (rhoN 3) fTimes3) + 1) _ _ _
              (FOMult x (FOVar V)) _ _ _ _ _ _);
      [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
    intros w2 Hw2 HR2.
    lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
      assert (HG3 : FOctx_avoid G3 0 1000) by (intros w'' ? ?; free_ctx);
      assert (Cw : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar w) (FOVar (V + 1)))) by wk_in;
      assert (Nw : FOPrH n G3 (FONUMR (FOVar V) (FOVar w))) by wk_in;
      assert (N2 : FOPrH n G3 (FONUMR (FOMult x (FOVar V)) (FOVar w2))) by wk_in;
      assert (HPhi3 : FOPrH n G3 (PhiOp (FOPrCores k) (FOu0 k) (V + 3) (V + 1) (V + 2) false x m1
                                   (cpat_f (rhoN 3) fTimes3) (FOVar V))) by wk HPhi;
      assert (Hb3 : FOPrH n G3 (FONUMR (FOMult x (FOSucc (FOVar V))) (FOVar (V + 2)))) by wk Hb;
      assert (Hx3 : FOPrH n G3 (FONUMR x m1)) by wk Hx1
    end.
    pose proof (PhiOp_inst n _ _ _ (V + 3) (V + 1) (V + 2) false x m1 _ (FOVar V) (FOVar w)
                  (FOVar w2) HPhi3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as IH.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ IH Nw) N2) as IHf.
    pose proof (PRIf_to_PRI n _ _ (S w2) _ _ _ (V + 3) IHf ltac:(lia) ltac:(avoid_tms) ltac:(lia)
                  ltac:(avoid_tms) ltac:(above_tac)) as IHP.
    pose proof (FOPrH_numr_cong1 n _ (FOMult x (FOSucc (FOVar V)))
                  (FOPlus (FOMult x (FOVar V)) x) (FOVar (V + 2)) Hb3
                  ltac:(apply FOPrH_ring; fo_ring) ltac:(avoid_tms) ltac:(avoid_tms)
                  ltac:(avoid_tms)) as Hb4.
    pose proof (PRI_plus n k (S w2) _ (FOMult x (FOVar V)) x (FOVar w2) m1 (FOVar (V + 2))
                  ltac:(lia) HG3 ltac:(intros w'' ?; free_ctx) ltac:(avoid_tms) ltac:(above_tac)
                  N2 Hx3 Hb4) as PL.
    lazymatch type of HG3 with FOctx_avoid ?G3 _ _ =>
      assert (HE4 : EnvOK n (S w2) G3 [m1; FOVar w; FOVar (V + 2); FOVar w2])
        by (apply (EnvOK4 n _ _ _ _ _ _ x (FOVar V) (FOMult x (FOSucc (FOVar V)))
                     (FOMult x (FOVar V)));
            [intros w'' ? ?; apply HG3; lia | exact Hx3 | exact Nw | exact Hb3 | exact N2
            | avoid_tms | lia | above_tac]);
      assert (IH4 : PRI n (FOPrCores k) (FOu0 k) (S w2) G3
                      (cpat_f (rhoN 4) (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOVar 3)))
                      [m1; FOVar w; FOVar (V + 2); FOVar w2])
    end.
    { refine (PRI_conv n _ _ (S w2) _ _ _ _ _ _ _ _ _ IHP); [| above_tac | avoid_tms | lia].
      intros G' Hinc. unfold fTimes3, rhoN. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac. }
    lazymatch type of HG3 with FOctx_avoid ?G3 _ _ =>
      assert (PL4 : PRI n (FOPrCores k) (FOu0 k) (S w2) G3
                      (cpat_f (rhoN 4) (FOEq (FOPlus (FOVar 3) (FOVar 0)) (FOVar 2)))
                      [m1; FOVar w; FOVar (V + 2); FOVar w2])
    end.
    { refine (PRI_conv n _ _ (S w2) _ _ _ _ _ _ _ _ _ PL); [| above_tac | avoid_tms | lia].
      intros G' Hinc. unfold fPlus3, rhoN. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac. }
    pose proof (PRI_thm_open n k (S w2) _ _ (rhoN 4) _ FOPr_times_step HE4
                  (rhoN_fv 4 (FOImplF (FOEq (FOMult (FOVar 0) (FOVar 1)) (FOVar 3))
                               (FOImplF (FOEq (FOPlus (FOVar 3) (FOVar 0)) (FOVar 2))
                                  (FOEq (FOMult (FOVar 0) (FOSucc (FOVar 1))) (FOVar 2))))
                     ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T1.
    pose proof (PRI_mp n _ _ (S w2) _ (rhoN 4) _ _ _ HE4 (rhoN_range 4) T1 IH4) as T2.
    pose proof (PRI_mp n _ _ (S w2) _ (rhoN 4) _ _ _ HE4 (rhoN_range 4) T2 PL4) as T3.
    refine (PRI_conv n _ _ (S w2) _ _ _ _ _ _ _ _ _ T3); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cw) as C1.
    unfold fTimes3, rhoN. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
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
      first
        [ match goal with
          | H : FOtms_avoid ?L' ?lo' ?hi' |- _ =>
              apply (FOtms_avoid_incl L L' lo' hi' lo hi H);
              [ let t := fresh "t" in let Ht := fresh "Ht" in
                intros t Ht; clear -Ht; cbn [In] in *; repeat rewrite in_app_iff in *;
                cbn [In] in *; tauto
              | nat_fast | nat_fast]
          end
        | match goal with
          | H : forall s, In s L -> forall w, ?V <= w -> FOin_tm w s = false |- _ =>
              let t := fresh "t" in let Ht := fresh "Ht" in let w := fresh "w" in
              let H1 := fresh "Hw" in let H2 := fresh "Hw" in
              intros t Ht w H1 H2; apply (H t Ht w); nat_fast
          end ]
  end.

Ltac above_tac ::=
  let t := fresh "t" in let Ht := fresh "Ht" in let w0 := fresh "w0" in
  let Hw0 := fresh "Hw0" in
  intros t Ht w0 Hw0;
  repeat match goal with
    | H : In t (_ ++ _) |- _ => apply in_app_or in H
    | H : In t (_ :: _) |- _ => cbn [In] in H
    | H : In t [] |- _ => destruct H
    | H : In t _ \/ _ |- _ => destruct H as [H|H]
    | H : _ = t \/ _ |- _ => destruct H as [H|H]
    | H : False |- _ => destruct H
    | H : _ = t |- _ => subst t
    end;
  first [ fr_tm
        | match goal with
          | H : forall s, In s ?L -> forall w, ?V <= w -> FOin_tm w s = false,
            H' : In t ?L |- _ => apply (H t H' w0); nat_fast
          end ].

(** ** Sums and products at arbitrary slots. *)

Lemma PRI_op_gen : forall n k V G f rho env z1 z2 z3 j1 j2 j3 x y,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  EnvOK n V G env -> FOtms_avoid env 0 1100 -> FOtms_avoid [x; y] 0 1100 ->
  (forall t, In t [x; y] -> forall w, V <= w -> FOin_tm w t = false) ->
  rho z1 = Some j1 -> rho z2 = Some j2 -> rho z3 = Some j3 ->
  FOPrH n G (FONUMR x (nth j1 env FOZero)) -> FOPrH n G (FONUMR y (nth j2 env FOZero)) ->
  FOPrH n G (FONUMR (opT f x y) (nth j3 env FOZero)) ->
  PRI n (FOPrCores k) (FOu0 k) V G
    (cpat_f rho (FOEq (opT f (FOVar z1) (FOVar z2)) (FOVar z3))) env.
Proof.
  intros n k V G f rho env z1 z2 z3 j1 j2 j3 x y HV HG0 HGV HE Henv Hxy Hxyv Hz1 Hz2 Hz3
    H1 H2 H3.
  pose proof HE as [_ [_ [_ Henvv]]].
  destruct f.
  - pose proof (PRI_plus n k V G x y (nth j1 env FOZero) (nth j2 env FOZero)
                  (nth j3 env FOZero) HV HG0 HGV ltac:(avoid_tms) ltac:(above_tac) H1 H2 H3) as T.
    refine (PRI_conv n _ _ V G _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
    intros G' Hinc. unfold fPlus3, rhoN. cbn [cpat_f cpat_tm opT Nat.ltb Nat.leb].
    rewrite Hz1, Hz2, Hz3. cprel_tac.
  - pose proof (PRI_times n k V G x y (nth j1 env FOZero) (nth j2 env FOZero)
                  (nth j3 env FOZero) HV HG0 HGV ltac:(avoid_tms) ltac:(above_tac) H1 H2 H3) as T.
    refine (PRI_conv n _ _ V G _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
    intros G' Hinc. unfold fTimes3, rhoN. cbn [cpat_f cpat_tm opT Nat.ltb Nat.leb].
    rewrite Hz1, Hz2, Hz3. cprel_tac.
Qed.

Lemma FOin_tm_opT_eq : forall f w a b, FOin_tm w (opT f a b) = (FOin_tm w a || FOin_tm w b)%bool.
Proof. intros [|] w a b; reflexivity. Qed.

(** ** Holder facts. *)

Definition HOK (n : nat) (G : list FOFormula) (V : nat) (h : nat -> nat)
    (rho : nat -> option nat) (env : list FOTerm) (x : nat) : Prop :=
  exists i, rho x = Some i /\ i < length env /\
    FOPrH n G (FONUMR (FOVar (h x)) (nth i env FOZero)) /\ 1100 <= h x /\ h x < V.

Lemma HOK_ext : forall n G G' V V' h rho rho' env env' x,
  HOK n G V h rho env x -> (forall X, In X G -> In X G') -> V <= V' ->
  (forall i, rho x = Some i -> rho' x = Some i) -> length env <= length env' ->
  (forall i, i < length env -> nth i env' FOZero = nth i env FOZero) ->
  HOK n G' V' h rho' env' x.
Proof.
  intros n G G' V V' h rho rho' env env' x [i [Hr [Hi [HN [H1 H2]]]]] Hinc HV Hrr Hl Hn.
  exists i. split; [exact (Hrr i Hr)|]. split; [lia|]. split; [|lia].
  rewrite (Hn i Hi). exact (FOPrH_weaken n G G' _ Hinc HN).
Qed.

Lemma hsub_tm_range : forall t h lo hi, (forall x, FOin_tm x t = true -> lo <= h x < hi) ->
  forall w, FOin_tm w (hsub_tm h t) = true -> lo <= w < hi.
Proof.
  intros t h lo hi H w Hw. destruct (FOin_tm_hsub t h w Hw) as [x [Hx <-]]. exact (H x Hx).
Qed.

Lemma hsub_tm_avoid : forall t h lo hi, (forall x, FOin_tm x t = true -> lo <= h x) ->
  hi <= lo -> FOtm_avoid (hsub_tm h t) 0 hi.
Proof.
  intros t h lo hi H Hhi w Hw1 Hw2. destruct (FOin_tm w (hsub_tm h t)) eqn:E.
  - destruct (FOin_tm_hsub t h w E) as [x [Hx <-]]. specialize (H x Hx). lia.
  - reflexivity.
Qed.

Lemma hsub_tm_below : forall t h V, (forall x, FOin_tm x t = true -> h x < V) ->
  forall w, V <= w -> FOin_tm w (hsub_tm h t) = false.
Proof.
  intros t h V H w Hw. destruct (FOin_tm w (hsub_tm h t)) eqn:E; [|reflexivity].
  destruct (FOin_tm_hsub t h w E) as [x [Hx <-]]. specialize (H x Hx). lia.
Qed.

Lemma EnvOK_mono : forall n V V' G G' env, EnvOK n V G env ->
  (forall X, In X G -> In X G') -> FOctx_avoid G' 2 1000 -> V <= V' -> EnvOK n V' G' env.
Proof.
  intros n V V' G G' env [HS [H0 [HV Hab]]] Hinc HG' HVV.
  split; [exact (SlotCtx_mono n env G G' Hinc HG' HS)|]. split; [exact H0|]. split; [lia|].
  intros t Ht w Hw. apply (Hab t Ht). lia.
Qed.

Lemma nth_app_lt : forall (env l : list FOTerm) i, i < length env ->
  nth i (env ++ l) FOZero = nth i env FOZero.
Proof. intros env l i Hi. apply app_nth1. exact Hi. Qed.

Lemma nth_app_len : forall (env l : list FOTerm) i,
  nth (length env + i) (env ++ l) FOZero = nth i l FOZero.
Proof.
  intros env l i. rewrite app_nth2 by lia. f_equal. lia.
Qed.

(** ** Values of terms. *)

Lemma FOPr_succ_cong :  forall a z,
  FOProvesTn 0 (FOImplF (FOEq a (FOVar z)) (FOEq (FOSucc a) (FOSucc (FOVar z)))).
Proof.
  intros a z. change (FOPrH 0 [] (FOImplF (FOEq a (FOVar z)) (FOEq (FOSucc a) (FOSucc (FOVar z))))).
  apply FOPrH_intro. apply FOPrH_congS. apply FOPrH_assum. left. reflexivity.
Qed.

Lemma FOPr_op_cong : forall f a b z1 z2 z,
  FOProvesTn 0 (FOImplF (FOEq a (FOVar z1)) (FOImplF (FOEq b (FOVar z2))
    (FOImplF (FOEq (opT f (FOVar z1) (FOVar z2)) (FOVar z)) (FOEq (opT f a b) (FOVar z))))).
Proof.
  intros f a b z1 z2 z.
  change (FOPrH 0 [] (FOImplF (FOEq a (FOVar z1)) (FOImplF (FOEq b (FOVar z2))
    (FOImplF (FOEq (opT f (FOVar z1) (FOVar z2)) (FOVar z)) (FOEq (opT f a b) (FOVar z)))))).
  apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_intro. cbn [app].
  apply (FOPrH_eq_trans _ _ _ (opT f (FOVar z1) (FOVar z2))).
  - destruct f; cbn [opT].
    + apply FOPrH_congPlus; apply FOPrH_assum; [left | right; left]; reflexivity.
    + apply FOPrH_congMult; apply FOPrH_assum; [left | right; left]; reflexivity.
  - apply FOPrH_assum. right. right. left. reflexivity.
Qed.

Lemma FOPr_var_refl : forall x, FOProvesTn 0 (FOEq (FOVar x) (FOVar x)).
Proof. intros x. change (FOPrH 0 [] (FOEq (FOVar x) (FOVar x))). apply FOPrH_refl. Qed.

Lemma FOPr_zero_refl : FOProvesTn 0 (FOEq FOZero FOZero).
Proof. change (FOPrH 0 [] (FOEq FOZero FOZero)). apply FOPrH_refl. Qed.

Ltac fv_cases H :=
  repeat match type of H with
  | FOfree_in _ (FOImplF _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ (FOEq _ _) = true => cbn [FOfree_in] in H
  | FOfree_in _ FOFalseF = true => discriminate H
  | (_ || _)%bool = true => apply Bool.orb_true_iff in H; destruct H as [H|H]
  | FOin_tm _ (FOSucc _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (FOPlus _ _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (FOMult _ _) = true => cbn [FOin_tm] in H
  | FOin_tm _ (opT _ _ _) = true => rewrite FOin_tm_opT_eq in H
  | FOin_tm _ FOZero = true => discriminate H
  | FOin_tm ?x (FOVar _) = true => cbn [FOin_tm] in H; apply Nat.eqb_eq in H; subst x
  | Nat.eqb _ ?x = true => apply Nat.eqb_eq in H; subst x
  end.

(** [TEV n k t]: a numeral code of the value of [t], at the holders,
    makes the equation of [t] with that code provable. *)

Definition TEV (n k : nat) (t : FOTerm) : Prop :=
  forall V G h rho env z j,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  EnvOK n V G env -> FOtms_avoid env 0 1100 ->
  (forall z' i, rho z' = Some i -> i < length env) ->
  (forall x, FOin_tm x t = true -> HOK n G V h rho env x) ->
  FOin_tm z t = false -> rho z = Some j -> j < length env ->
  FOPrH n G (FONUMR (hsub_tm h t) (nth j env FOZero)) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho (FOEq t (FOVar z))) env.

Lemma TEV_var : forall n k x, TEV n k (FOVar x).
Proof.
  intros n k x V G h rho env z j HV HG0 HGV HE Henv Hr Hh Hz Hzj Hj HN.
  pose proof HE as [_ [_ [_ Henvv]]].
  destruct (Hh x ltac:(cbn [FOin_tm]; apply Nat.eqb_refl)) as [i [Hxi [Hi [HNx [H1 H2]]]]].
  cbn [hsub_tm] in HN.
  pose proof (FOPrH_numr_unique n G (FOVar (h x)) (nth i env FOZero) (nth j env FOZero) HNx HN
                ltac:(avoid_tms) ltac:(avoid_tms)) as E.
  assert (Hfv : forall x', FOfree_in x' (FOEq (FOVar x) (FOVar x)) = true ->
            exists j', rho x' = Some j' /\ j' < length env).
  { intros x' Hx'. cbn [FOfree_in FOin_tm] in Hx'. rewrite Bool.orb_diag in Hx'.
    apply Nat.eqb_eq in Hx'. subst x'. exists i. split; assumption. }
  pose proof (PRI_thm_open n k V G _ rho env (FOPr_var_refl x) HE Hfv) as T.
  refine (PRI_conv n _ _ V G _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
  intros G' Hinc. pose proof (FOPrH_weaken n G G' _ Hinc E) as E'.
  cbn [cpat_f cpat_tm]. rewrite Hxi, Hzj. cprel_tac.
Qed.

Lemma TEV_zero : forall n k, TEV n k FOZero.
Proof.
  intros n k V G h rho env z j HV HG0 HGV HE Henv Hr Hh Hz Hzj Hj HN.
  pose proof HE as [_ [_ [_ Henvv]]].
  cbn [hsub_tm] in HN.
  pose proof (FOPrH_numr_inv0 n G (nth j env FOZero) ltac:(intros w ? ?; apply HG0; lia)
                ltac:(avoid_tms) HN) as C.
  pose proof (PRI_thm_open n k V G _ rho env FOPr_zero_refl HE
                ltac:(intros x' Hx'; discriminate Hx')) as T.
  refine (PRI_conv n _ _ V G _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
  intros G' Hinc. pose proof (FOPrH_weaken n G G' _ Hinc C) as C'.
  cbn [cpat_f cpat_tm]. rewrite Hzj. cprel_tac.
Qed.

Lemma nth_snoc_len : forall (env : list FOTerm) x, nth (length env) (env ++ [x]) FOZero = x.
Proof. intros env x. rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma TEV_succ : forall n k a, TEV n k a -> TEV n k (FOSucc a).
Proof.
  intros n k a IH V G h rho env z j HV HG0 HGV HE Henv Hr Hh Hz Hzj Hj HN.
  pose proof HE as [_ [_ [_ Henvv]]].
  cbn [hsub_tm] in HN. cbn [FOin_tm] in Hz.
  assert (Hha : forall x, FOin_tm x a = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; cbn [FOin_tm]; exact Hx).
  assert (Hhr : forall x, FOin_tm x a = true -> 1100 <= h x < V)
    by (intros x Hx; destruct (Hha x Hx) as [i [_ [_ [_ [H1 H2]]]]]; lia).
  assert (Hav_a : FOtms_avoid [hsub_tm h a] 0 1100).
  { intros s [<-|[]]. apply (hsub_tm_avoid a h 1100 1100); [|lia].
    intros x Hx. apply Hhr. exact Hx. }
  assert (Hab_a : forall s, In s [hsub_tm h a] -> forall w, V <= w -> FOin_tm w s = false).
  { intros s [<-|[]] w Hw. apply (hsub_tm_below a h V); [|exact Hw].
    intros x Hx. apply Hhr. exact Hx. }
  refine (PRI_numr_invS n _ _ V 0 G _ env (hsub_tm h a) (nth j env FOZero) HN _ _ _ _ _ _);
    [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
  intros w Hw _.
  remember (S (Nat.max (FOmax_var_tm a) z)) as z' eqn:Ez'.
  assert (Hz'a : FOin_tm z' a = false) by (apply FOin_tm_above; lia).
  assert (Hr2 : rho_sub (Some z') (length env) rho z' = Some (length env))
    by (unfold rho_sub; rewrite Nat.eqb_refl; reflexivity).
  assert (Hrho2 : forall x, x <> z' -> rho_sub (Some z') (length env) rho x = rho x)
    by (intros x Hx; unfold rho_sub; rewrite (proj2 (Nat.eqb_neq x z') Hx); reflexivity).
  assert (Hxz' : forall x, FOin_tm x a = true -> x <> z').
  { intros x Hx E. subst x. congruence. }
  lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
    assert (HG2 : FOctx_avoid G2 0 1000) by (intros w' ? ?; free_ctx);
    assert (HG2V : forall w', S w <= w' -> FOfree_ctx w' G2) by (intros w' ?; free_ctx);
    assert (Hinc2 : forall X, In X G -> In X G2) by (intros X HX; apply in_or_app; left; exact HX);
    assert (Cw : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar w) (nth j env FOZero))) by wk_in;
    assert (Nw : FOPrH n G2 (FONUMR (hsub_tm h a) (FOVar w))) by wk_in;
    assert (HE2 : EnvOK n (S w) G2 (env ++ [FOVar w]))
      by (apply (EnvOK_snoc n (S w) G2 env (FOVar w) (hsub_tm h a));
          [ apply (EnvOK_mono n V (S w) G);
            [exact HE | exact Hinc2 | intros w' ? ?; apply HG2; lia | lia]
          | exact Nw | avoid_tms | intros w' Hw'; apply FOin_tm_var_ne; lia ])
  end.
  assert (Hr2' : forall z0 i, rho_sub (Some z') (length env) rho z0 = Some i ->
            i < length (env ++ [FOVar w])).
  { intros z0 i Hz0. rewrite length_app. cbn [length]. unfold rho_sub in Hz0.
    destruct (Nat.eqb z0 z'); [injection Hz0 as <-; lia | specialize (Hr z0 i Hz0); lia]. }
  pose proof (IH (S w) _ h (rho_sub (Some z') (length env) rho) (env ++ [FOVar w]) z'
                (length env) ltac:(lia) HG2 HG2V HE2 ltac:(avoid_tms) Hr2'
                ltac:(intros x Hx;
                      refine (HOK_ext n G _ V (S w) h rho _ env (env ++ [FOVar w]) x (Hha x Hx)
                                Hinc2 _ _ _ _);
                      [ lia | intros i Hi; rewrite (Hrho2 x (Hxz' x Hx)); exact Hi
                      | rewrite length_app; lia | intros i Hi; apply nth_app_lt; exact Hi ])
                Hz'a Hr2 ltac:(rewrite length_app; cbn [length]; lia)
                ltac:(rewrite nth_snoc_len; exact Nw)) as IHa.
  pose proof (PRI_thm_open n k (S w) _ _ (rho_sub (Some z') (length env) rho) _
                (FOPr_succ_cong a z') HE2) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ destruct (Hha x Hx) as [i [Hxi [Hi _]]]; exists i;
                              rewrite (Hrho2 x (Hxz' x Hx));
                              split; [exact Hxi | rewrite length_app; lia]
                            | exists (length env);
                              split; [exact Hr2 | rewrite length_app; cbn [length]; lia] ])).
  pose proof (PRI_mp n _ _ (S w) _ _ _ _ _ HE2 Hr2' T IHa) as T2.
  refine (PRI_conv n _ _ (S w) _ _ _ _ _ _ _ _ _ T2); [| above_tac | avoid_tms | lia].
  intros G' Hinc. pose proof (FOPrH_weaken n _ G' _ Hinc Cw) as Cw'.
  cbn [cpat_f cpat_tm]. rewrite Hr2, Hzj.
  apply cpr_pair; [apply cpr_lit|]. apply cpr_pair.
  - apply cpr_pair; [apply cpr_lit|]. apply CPrel_cpat_tm. intros x Hx. unfold SlotAgree.
    rewrite (Hrho2 x (Hxz' x Hx)). destruct (Hha x Hx) as [i [Hxi [Hi _]]]. rewrite Hxi.
    rewrite nth_app_lt by exact Hi. apply FOPrH_refl.
  - apply cpr_succ_r. rewrite nth_snoc_len. exact Cw'.
Qed.

Lemma hsub_tm_opT : forall f h a b, hsub_tm h (opT f a b) = opT f (hsub_tm h a) (hsub_tm h b).
Proof. intros [|] h a b; reflexivity. Qed.

Lemma TEV_op : forall n k f a b, TEV n k a -> TEV n k b -> TEV n k (opT f a b).
Proof.
  intros n k f a b IHa IHb V G h rho env z j HV HG0 HGV HE Henv Hr Hh Hz Hzj Hj HN.
  pose proof HE as [_ [_ [_ Henvv]]].
  rewrite hsub_tm_opT in HN. rewrite FOin_tm_opT_eq in Hz.
  apply Bool.orb_false_iff in Hz as [Hza Hzb].
  assert (Hha : forall x, FOin_tm x a = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; rewrite FOin_tm_opT_eq, Hx; reflexivity).
  assert (Hhb : forall x, FOin_tm x b = true -> HOK n G V h rho env x)
    by (intros x Hx; apply Hh; rewrite FOin_tm_opT_eq, Hx; apply Bool.orb_true_r).
  assert (Hhra : forall x, FOin_tm x a = true -> 1100 <= h x < V)
    by (intros x Hx; destruct (Hha x Hx) as [i [_ [_ [_ [H1 H2]]]]]; lia).
  assert (Hhrb : forall x, FOin_tm x b = true -> 1100 <= h x < V)
    by (intros x Hx; destruct (Hhb x Hx) as [i [_ [_ [_ [H1 H2]]]]]; lia).
  assert (Hav_ab : FOtms_avoid [hsub_tm h a; hsub_tm h b] 0 1100).
  { intros s [<-|[<-|[]]];
      [apply (hsub_tm_avoid a h 1100 1100) | apply (hsub_tm_avoid b h 1100 1100)];
      try lia; intros x Hx; [apply Hhra | apply Hhrb]; exact Hx. }
  assert (Hab_ab : forall s, In s [hsub_tm h a; hsub_tm h b] ->
            forall w, V <= w -> FOin_tm w s = false).
  { intros s [<-|[<-|[]]] w Hw; [apply (hsub_tm_below a h V) | apply (hsub_tm_below b h V)];
      try exact Hw; intros x Hx; [apply Hhra | apply Hhrb]; exact Hx. }
  refine (PRI_numr_ex n _ _ V 0 G _ env (hsub_tm h a) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
  intros w1 Hw1 _.
  refine (PRI_numr_ex n _ _ (S w1) 0 _ _ env (hsub_tm h b) _ _ _ _ _ _);
    [lia | avoid_tms | intros w' ?; fr_tm | avoid_tms | above_tac |].
  intros w2 Hw2 _.
  remember (S (Nat.max (Nat.max (FOmax_var_tm a) (FOmax_var_tm b)) z)) as z1 eqn:Ez1.
  assert (Hz1a : FOin_tm z1 a = false) by (apply FOin_tm_above; lia).
  assert (Hz1b : FOin_tm z1 b = false) by (apply FOin_tm_above; lia).
  assert (Hz2a : FOin_tm (S z1) a = false) by (apply FOin_tm_above; lia).
  assert (Hz2b : FOin_tm (S z1) b = false) by (apply FOin_tm_above; lia).
  remember (rho_sub (Some (S z1)) (S (length env)) (rho_sub (Some z1) (length env) rho))
    as rho3 eqn:Erho3.
  assert (H31 : rho3 z1 = Some (length env)).
  { subst rho3. unfold rho_sub. rewrite (proj2 (Nat.eqb_neq z1 (S z1)) ltac:(lia)).
    rewrite Nat.eqb_refl. reflexivity. }
  assert (H32 : rho3 (S z1) = Some (S (length env))).
  { subst rho3. unfold rho_sub. rewrite Nat.eqb_refl. reflexivity. }
  assert (H3x : forall x, x <> z1 -> x <> S z1 -> rho3 x = rho x).
  { intros x Hx1 Hx2. subst rho3. unfold rho_sub.
    rewrite (proj2 (Nat.eqb_neq x (S z1)) Hx2), (proj2 (Nat.eqb_neq x z1) Hx1). reflexivity. }
  assert (Hxa : forall x, FOin_tm x a = true -> x <> z1 /\ x <> S z1).
  { intros x Hx. split; intro E; subst x; congruence. }
  assert (Hxb : forall x, FOin_tm x b = true -> x <> z1 /\ x <> S z1).
  { intros x Hx. split; intro E; subst x; congruence. }
  assert (Hzz : z <> z1 /\ z <> S z1) by lia.
  assert (Hn1 : nth (length env) ((env ++ [FOVar w1]) ++ [FOVar w2]) FOZero = FOVar w1).
  { rewrite nth_app_lt by (rewrite length_app; cbn [length]; lia). apply nth_snoc_len. }
  assert (Hn2 : nth (S (length env)) ((env ++ [FOVar w1]) ++ [FOVar w2]) FOZero = FOVar w2).
  { replace (S (length env)) with (length (env ++ [FOVar w1]))
      by (rewrite length_app; cbn [length]; lia). apply nth_snoc_len. }
  assert (Hn0 : forall i, i < length env ->
            nth i ((env ++ [FOVar w1]) ++ [FOVar w2]) FOZero = nth i env FOZero).
  { intros i Hi. rewrite nth_app_lt by (rewrite length_app; cbn [length]; lia).
    apply nth_app_lt. exact Hi. }
  assert (Hl3 : length ((env ++ [FOVar w1]) ++ [FOVar w2]) = S (S (length env)))
    by (rewrite !length_app; cbn [length]; lia).
  assert (Hr3 : forall z0 i, rho3 z0 = Some i -> i < length ((env ++ [FOVar w1]) ++ [FOVar w2])).
  { intros z0 i Hz0. rewrite Hl3. subst rho3. unfold rho_sub in Hz0.
    destruct (Nat.eqb z0 (S z1)); [injection Hz0 as <-; lia|].
    destruct (Nat.eqb z0 z1); [injection Hz0 as <-; lia|]. specialize (Hr z0 i Hz0). lia. }
  lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
    assert (HG3 : FOctx_avoid G3 0 1000) by (intros w' ? ?; free_ctx);
    assert (HG3V : forall w', S w2 <= w' -> FOfree_ctx w' G3) by (intros w' ?; free_ctx);
    assert (Hinc3 : forall X, In X G -> In X G3)
      by (intros X HX; apply in_or_app; left; apply in_or_app; left; exact HX);
    assert (Na : FOPrH n G3 (FONUMR (hsub_tm h a) (FOVar w1))) by wk_in;
    assert (Nb : FOPrH n G3 (FONUMR (hsub_tm h b) (FOVar w2))) by wk_in;
    assert (HN3 : FOPrH n G3 (FONUMR (opT f (hsub_tm h a) (hsub_tm h b)) (nth j env FOZero)))
      by exact (FOPrH_weaken n G G3 _ Hinc3 HN);
    assert (HE3 : EnvOK n (S w2) G3 ((env ++ [FOVar w1]) ++ [FOVar w2]))
      by (apply (EnvOK_snoc n (S w2) G3 _ (FOVar w2) (hsub_tm h b));
          [ apply (EnvOK_snoc n (S w2) G3 env (FOVar w1) (hsub_tm h a));
            [ apply (EnvOK_mono n V (S w2) G);
              [exact HE | exact Hinc3 | intros w' ? ?; apply HG3; lia | lia]
            | exact Na | avoid_tms | intros w' Hw'; apply FOin_tm_var_ne; lia ]
          | exact Nb | avoid_tms | intros w' Hw'; apply FOin_tm_var_ne; lia ])
  end.
  lazymatch type of HG3 with FOctx_avoid ?G3 _ _ =>
    assert (HOKa : forall x, FOin_tm x a = true ->
              HOK n G3 (S w2) h rho3 ((env ++ [FOVar w1]) ++ [FOVar w2]) x)
      by (intros x Hx; destruct (Hxa x Hx) as [Hx1 Hx2];
          refine (HOK_ext n G _ V (S w2) h rho _ env _ x (Hha x Hx) Hinc3 _ _ _ _);
          [lia | intros i Hi; rewrite (H3x x Hx1 Hx2); exact Hi | rewrite Hl3; lia
          | exact Hn0]);
    assert (HOKb : forall x, FOin_tm x b = true ->
              HOK n G3 (S w2) h rho3 ((env ++ [FOVar w1]) ++ [FOVar w2]) x)
      by (intros x Hx; destruct (Hxb x Hx) as [Hx1 Hx2];
          refine (HOK_ext n G _ V (S w2) h rho _ env _ x (Hhb x Hx) Hinc3 _ _ _ _);
          [lia | intros i Hi; rewrite (H3x x Hx1 Hx2); exact Hi | rewrite Hl3; lia
          | exact Hn0])
  end.
  pose proof (IHa (S w2) _ h rho3 _ z1 (length env) ltac:(lia) HG3 HG3V HE3 ltac:(avoid_tms) Hr3
                HOKa Hz1a H31 ltac:(rewrite Hl3; lia) ltac:(rewrite Hn1; exact Na)) as Ta.
  pose proof (IHb (S w2) _ h rho3 _ (S z1) (S (length env)) ltac:(lia) HG3 HG3V HE3
                ltac:(avoid_tms) Hr3 HOKb Hz2b H32 ltac:(rewrite Hl3; lia)
                ltac:(rewrite Hn2; exact Nb)) as Tb.
  pose proof (PRI_op_gen n k (S w2) _ f rho3 _ z1 (S z1) z (length env) (S (length env)) j
                (hsub_tm h a) (hsub_tm h b) ltac:(lia) HG3 HG3V HE3 ltac:(avoid_tms)
                ltac:(avoid_tms) ltac:(above_tac) H31 H32
                ltac:(rewrite (H3x z (proj1 Hzz) (proj2 Hzz)); exact Hzj)
                ltac:(rewrite Hn1; exact Na) ltac:(rewrite Hn2; exact Nb)
                ltac:(rewrite (Hn0 j Hj); exact HN3)) as Top.
  pose proof (PRI_thm_open n k (S w2) _ _ rho3 _ (FOPr_op_cong f a b z1 (S z1) z) HE3) as T.
  specialize (T ltac:(intros x Hx; fv_cases Hx;
                      first [ destruct (HOKa x Hx) as [i [Hxi [Hi _]]]; exists i; split; assumption
                            | destruct (HOKb x Hx) as [i [Hxi [Hi _]]]; exists i; split; assumption
                            | exists (length env); split; [exact H31 | rewrite Hl3; lia]
                            | exists (S (length env)); split; [exact H32 | rewrite Hl3; lia]
                            | exists j; split;
                              [rewrite (H3x z (proj1 Hzz) (proj2 Hzz)); exact Hzj
                              | rewrite Hl3; lia] ])).
  pose proof (PRI_mp n _ _ (S w2) _ rho3 _ _ _ HE3 Hr3 T Ta) as T1.
  pose proof (PRI_mp n _ _ (S w2) _ rho3 _ _ _ HE3 Hr3 T1 Tb) as T2.
  pose proof (PRI_mp n _ _ (S w2) _ rho3 _ _ _ HE3 Hr3 T2 Top) as T3.
  refine (PRI_reslot n _ _ (S w2) _ _ rho3 rho _ env _ _ _ _ T3); [| above_tac | avoid_tms | lia].
  intros x Hx. unfold SlotAgree. fv_cases Hx.
  - destruct (Hxa x Hx) as [Hx1 Hx2]. rewrite (H3x x Hx1 Hx2).
    destruct (Hha x Hx) as [i [Hxi [Hi _]]]. rewrite Hxi, (Hn0 i Hi). apply FOPrH_refl.
  - destruct (Hxb x Hx) as [Hx1 Hx2]. rewrite (H3x x Hx1 Hx2).
    destruct (Hhb x Hx) as [i [Hxi [Hi _]]]. rewrite Hxi, (Hn0 i Hi). apply FOPrH_refl.
  - rewrite (H3x z (proj1 Hzz) (proj2 Hzz)), Hzj, (Hn0 j Hj). apply FOPrH_refl.
Qed.

Theorem PRI_teval : forall t n k, TEV n k t.
Proof.
  induction t as [x| |a IH|a IHa b IHb|a IHa b IHb]; intros n k.
  - apply TEV_var.
  - apply TEV_zero.
  - apply TEV_succ. apply IH.
  - exact (TEV_op n k true a b (IHa n k) (IHb n k)).
  - exact (TEV_op n k false a b (IHa n k) (IHb n k)).
Qed.

(** ** Zero or successor, for provable instances. *)

Lemma PRI_zs : forall n cores u0 V R G p env t,
  1000 <= V -> FOtms_avoid [t] 0 1000 -> (forall w, V <= w -> FOin_tm w t = false) ->
  FOtms_avoid env 0 1000 -> (forall s, In s env -> forall w, V <= w -> FOin_tm w s = false) ->
  PRI n cores u0 V (G ++ [FOEq t FOZero]) p env ->
  (forall w, V <= w -> R <= w ->
     PRI n cores u0 (S w) (G ++ [FOEq t (FOSucc (FOVar w))]) p env) ->
  PRI n cores u0 V G p env.
Proof.
  intros n cores u0 V R G p env t HV Ht0 Htv Henv0 Henv H0 HS.
  intros G' B c Hinc HG0 Hc0 HBV [HGc Hcc] Hc.
  remember (B + cpat_span p + R + 1) as w eqn:Ew.
  assert (Hcz : FOtms_avoid [c] B (S (S w + cpat_span p))).
  { intros s [<-|[]] w' ? ?. apply (Hcc c (or_introl eq_refl)). lia. }
  assert (Henvz : FOtms_avoid env V (S (S w + cpat_span p))).
  { intros s Hs w' ? ?. apply (Henv s Hs). lia. }
  assert (Htz : FOtms_avoid [t] V (S (S w + cpat_span p))).
  { intros s [<-|[]] w' ? ?. apply Htv. lia. }
  apply (FOPrH_cases_zs n G' t w (FOPRu cores u0 c) ltac:(lia) ltac:(fr_tm)
           ltac:(apply HGc; lia) ltac:(free_fm) ltac:(fr_tm)).
  - apply (H0 (G' ++ [FOEq t FOZero]) B c).
    + intros Y HY. apply in_app_or in HY. destruct HY as [HY|HY]; apply in_or_app;
        [left; exact (Hinc Y HY) | right; exact HY].
    + intros w' ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|]. free_ctx.
    + exact Hc0.
    + exact HBV.
    + split; [|exact Hcc]. intros w' Hw'. apply FOfree_ctx_app_inv; [apply HGc; lia|].
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. cbn [FOfree_in].
      rewrite (Htv w' ltac:(lia)). reflexivity.
    + apply FOPrH_weak_app. exact Hc.
  - pose proof (FOPrH_patf_rebase p n G' B (S w) env c Hc ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(intros w' ? ?; apply HGc; lia) ltac:(avoid_tms) ltac:(avoid_tms)
                  ltac:(avoid_tms)) as Hc1.
    apply (HS w ltac:(lia) ltac:(lia) (G' ++ [FOEq t (FOSucc (FOVar w))]) (S w) c).
    + intros Y HY. apply in_app_or in HY. destruct HY as [HY|HY]; apply in_or_app;
        [left; exact (Hinc Y HY) | right; exact HY].
    + intros w' ? ?. apply FOfree_ctx_app_inv; [apply HG0; lia|]. free_ctx.
    + exact Hc0.
    + lia.
    + split.
      * intros w' Hw'. apply FOfree_ctx_app_inv; [apply HGc; lia|].
        apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. cbn [FOfree_in FOin_tm].
        rewrite (Htv w' ltac:(lia)). cbn. apply Nat.eqb_neq. lia.
      * intros s [<-|[]] w' Hw'. apply (Hcc c (or_introl eq_refl)). lia.
    + apply FOPrH_weak_app. exact Hc1.
Qed.

(** ** Distinct numbers, inside the provability predicate.

    [PhiNeq Xt]: for every [Y] other than [Xt] and all numeral codes
    [a] of [Xt] and [b] of [Y], the disequation of the codes is provable. *)

Definition fNeq2 : FOFormula := FONeg (FOEq (FOVar 0) (FOVar 1)).

Definition PhiNeq (cores : list nat) (u0 B0 Y a b : nat) (P : CPat) (Xt : FOTerm) : FOFormula :=
  FOForall Y (FOForall a (FOForall b
    (FOImplF (FONeg (FOEq Xt (FOVar Y)))
      (FOImplF (FONUMR Xt (FOVar a))
        (FOImplF (FONUMR (FOVar Y) (FOVar b)) (PRIf cores u0 B0 [FOVar a; FOVar b] P)))))).

Lemma PhiNeq_subst : forall cores u0 B0 Y a b P N s,
  N <> Y -> N <> a -> N <> b -> 1000 <= N -> N < B0 -> FOtms_avoid [s] 802 805 ->
  FOsubst_f N s (PhiNeq cores u0 B0 Y a b P (FOVar N)) = PhiNeq cores u0 B0 Y a b P s.
Proof.
  intros cores u0 B0 Y a b P N s HY Ha Hb HN HB Hs. unfold PhiNeq.
  rewrite (FOsubst_f_all_ne N s Y) by lia. rewrite (FOsubst_f_all_ne N s a) by lia.
  rewrite (FOsubst_f_all_ne N s b) by lia.
  rewrite !FOsubst_f_impl, FOsubst_f_neg, FOsubst_f_eq, !FOsubst_f_NUMR by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf by lia. cbn [map].
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne by lia. reflexivity.
Qed.

Lemma PhiNeq_inst : forall n G cores u0 B0 Y a b P Xt ty ta tb,
  FOPrH n G (PhiNeq cores u0 B0 Y a b P Xt) ->
  Y <> a -> Y <> b -> a <> b -> 1000 <= Y -> 1000 <= a -> 1000 <= b ->
  Y < B0 -> a < B0 -> b < B0 ->
  FOtms_avoid [Xt] Y (S Y) -> FOtms_avoid [Xt; ty] a (S a) -> FOtms_avoid [Xt; ty; ta] b (S b) ->
  FOtms_avoid [ty; ta; tb] 0 1000 -> FOtms_avoid [ty; ta; tb] B0 (B0 + cpat_span P) ->
  FOPrH n G (FOImplF (FONeg (FOEq Xt ty)) (FOImplF (FONUMR Xt ta)
    (FOImplF (FONUMR ty tb) (PRIf cores u0 B0 [ta; tb] P)))).
Proof.
  intros n G cores u0 B0 Y a b P Xt ty ta tb H HYa HYb Hab HY Ha Hb HYB HaB HbB
    HavY Hava Havb Hav0 HavB.
  unfold PhiNeq in H.
  apply (FOPrH_inst n G Y ty) in H;
    [| apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_all; [fr_tm|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_neg; apply FOsubst_ok_eq|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite (FOsubst_f_all_ne Y ty a) in H by lia. rewrite (FOsubst_f_all_ne Y ty b) in H by lia.
  rewrite !FOsubst_f_impl, FOsubst_f_neg, FOsubst_f_eq, !FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf in H by lia. cbn [map] in H.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in H by lia.
  rewrite (FOsubst_t_not_in Xt Y ty) in H by fr_tm.
  apply (FOPrH_inst n G a ta) in H;
    [| apply FOsubst_ok_all; [fr_tm|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_neg; apply FOsubst_ok_eq|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite (FOsubst_f_all_ne a ta b) in H by lia.
  rewrite !FOsubst_f_impl, FOsubst_f_neg, FOsubst_f_eq, !FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf in H by lia. cbn [map] in H.
  rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne in H by lia.
  rewrite (FOsubst_t_not_in Xt a ta), (FOsubst_t_not_in ty a ta) in H by fr_tm.
  apply (FOPrH_inst n G b tb) in H;
    [| apply FOsubst_ok_impl; [apply FOsubst_ok_neg; apply FOsubst_ok_eq|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite !FOsubst_f_impl, FOsubst_f_neg, FOsubst_f_eq, !FOsubst_f_NUMR in H by (lia || avoid_tms).
  rewrite FOsubst_f_PRIf in H by lia. cbn [map] in H.
  rewrite FOsubst_t_var_eq' in H.
  rewrite (FOsubst_t_not_in Xt b tb), (FOsubst_t_not_in ty b tb), (FOsubst_t_not_in ta b tb)
    in H by fr_tm.
  exact H.
Qed.

Ltac free_fm ::=
  lazymatch goal with
  | |- FOfree_in _ (PhiNeq _ _ _ _ _ _ _ _) = false => unfold PhiNeq; free_fm
  | |- FOfree_in _ (PhiOp _ _ _ _ _ _ _ _ _ _) = false => unfold PhiOp; free_fm
  | |- FOfree_in _ (PRIf _ _ _ _ _) = false => apply FOfree_in_PRIf; [nat_fast | avoid_tms]
  | |- FOfree_in _ (FODISPCASES _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FODISPCASES_free
  | |- FOfree_in _ (FOSTEP5 _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOSTEP5_free
  | |- FOfree_in _ (FOTBLVALID _ _ _ _ _ _ _ _ _ _ _ _) = false => free_by FOTBLVALID_free
  | |- FOfree_in _ (FOlookup _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOlookup_free
  | |- FOfree_in _ (FOPRu _ _ _) = false =>
      first [ apply FOfree_in_PRu; [nat_fast | avoid_tms]
            | apply FOfree_in_PRu_all; [avoid_tms | avoid_tm] ]
  | |- FOfree_in _ (FOTBLEX3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      apply FOfree_in_TBLEX3_any; [nat_fast | avoid_tms]
  | |- FOfree_in ?w (FOBexC ?v _ _) = false =>
      first [ constr_eq w v; apply FOfree_in_FOBexC_self
            | rewrite FOBexC_ltv; free_fm ]
  | |- FOfree_in _ (FOJUSTCK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOJUSTCK_free
  | |- FOfree_in _ (FOGUARDC _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) = false =>
      free_by FOGUARDC_free
  | |- FOfree_in _ (FONUMR _ _) = false =>
      first [ apply FOfree_in_NUMR_all; avoid_tms | unfold FONUMR; free_fm ]
  | |- FOfree_in _ (FOTBLEX _ _ _ _ _) = false =>
      first [ apply FOfree_in_TBLEX_any; [nat_fast | avoid_tms]
            | apply FOfree_in_TBLEX_all; [avoid_tms | avoid_tms] ]
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

Lemma FOPr_zero_ne_succ : FOProvesTn 0 (FONeg (FOEq FOZero (FOSucc (FOVar 0)))).
Proof.
  change (FOPrH 0 [] (FONeg (FOEq FOZero (FOSucc (FOVar 0))))). unfold FONeg.
  apply FOPrH_intro. apply (FOPrH_Q_succ_nonzero _ _ (FOVar 0)). apply FOPrH_eq_sym.
  apply FOPrH_assum. left. reflexivity.
Qed.

Lemma FOPr_succ_ne_zero : FOProvesTn 0 (FONeg (FOEq (FOSucc (FOVar 0)) FOZero)).
Proof.
  change (FOPrH 0 [] (FONeg (FOEq (FOSucc (FOVar 0)) FOZero))). unfold FONeg.
  apply FOPrH_intro. apply (FOPrH_Q_succ_nonzero _ _ (FOVar 0)).
  apply FOPrH_assum. left. reflexivity.
Qed.

Lemma FOPr_succ_ne : FOProvesTn 0 (FOImplF (FONeg (FOEq (FOVar 0) (FOVar 1)))
                                   (FONeg (FOEq (FOSucc (FOVar 0)) (FOSucc (FOVar 1))))).
Proof.
  change (FOPrH 0 [] (FOImplF (FONeg (FOEq (FOVar 0) (FOVar 1)))
                                   (FONeg (FOEq (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))))).
  unfold FONeg. apply FOPrH_intro. apply FOPrH_intro. cbn [app].
  apply (FOPrH_mp _ _ (FOEq (FOVar 0) (FOVar 1))); [apply FOPrH_assum; left; reflexivity|].
  apply FOPrH_Q_succ_inj. apply FOPrH_assum. right. left. reflexivity.
Qed.

Lemma EnvOK1 : forall n V G a wa, FOctx_avoid G 2 1000 -> FOPrH n G (FONUMR wa a) ->
  FOtms_avoid [a] 0 1000 -> 1000 <= V ->
  (forall t, In t [a] -> forall w, V <= w -> FOin_tm w t = false) -> EnvOK n V G [a].
Proof.
  intros n V G a wa HG Ha H0 HV Hab.
  split; [split; [exact HG|] | split; [exact H0 | split; [exact HV | exact Hab]]].
  intros [|i] Hi; cbn [nth]; [exists wa; exact Ha | cbn in Hi; lia].
Qed.

Lemma EnvOK2 : forall n V G a b wa wb, FOctx_avoid G 2 1000 ->
  FOPrH n G (FONUMR wa a) -> FOPrH n G (FONUMR wb b) ->
  FOtms_avoid [a; b] 0 1000 -> 1000 <= V ->
  (forall t, In t [a; b] -> forall w, V <= w -> FOin_tm w t = false) -> EnvOK n V G [a; b].
Proof.
  intros n V G a b wa wb HG Ha Hb H0 HV Hab.
  split; [split; [exact HG|] | split; [exact H0 | split; [exact HV | exact Hab]]].
  intros [|[|i]] Hi; cbn [nth]; [exists wa; exact Ha | exists wb; exact Hb | cbn in Hi; lia].
Qed.

Lemma NEQ_base : forall n k V G,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  PRI n (FOPrCores k) (FOu0 k) (V + 4)
    (((G ++ [FONeg (FOEq FOZero (FOVar (V + 1)))]) ++ [FONUMR FOZero (FOVar (V + 2))])
       ++ [FONUMR (FOVar (V + 1)) (FOVar (V + 3))])
    (cpat_f (rhoN 2) fNeq2) [FOVar (V + 2); FOVar (V + 3)].
Proof.
  intros n k V G HV HG0 HGV.
  lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
    assert (HG1 : FOctx_avoid G1 0 1000) by (intros w ? ?; free_ctx);
    assert (Hne : FOPrH n G1 (FONeg (FOEq FOZero (FOVar (V + 1))))) by wk_in;
    assert (Ha : FOPrH n G1 (FONUMR FOZero (FOVar (V + 2)))) by wk_in;
    assert (Hb : FOPrH n G1 (FONUMR (FOVar (V + 1)) (FOVar (V + 3)))) by wk_in
  end.
  pose proof (FOPrH_numr_inv0 n _ (FOVar (V + 2)) ltac:(intros w ? ?; apply HG1; lia)
                ltac:(avoid_tms) Ha) as Ca.
  refine (PRI_zs n _ _ (V + 4) (V + 4 + cpat_span (cpat_f (rhoN 2) fNeq2) + 1) _ _ _
            (FOVar (V + 1)) _ _ _ _ _ _ _);
    [lia | avoid_tms | intros w ?; fr_tm | avoid_tms | above_tac | |].
  - apply PRI_efq. unfold FONeg in Hne.
    apply (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ Hne)). apply FOPrH_eq_sym. apply FOPrH_last.
  - intros w Hw HR.
    lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
      assert (HG2 : FOctx_avoid G2 0 1000) by (intros w' ? ?; free_ctx);
      assert (HY : FOPrH n G2 (FOEq (FOVar (V + 1)) (FOSucc (FOVar w)))) by wk_in;
      assert (Hb2 : FOPrH n G2 (FONUMR (FOVar (V + 1)) (FOVar (V + 3)))) by wk Hb;
      assert (Ca2 : FOPrH n G2 (FOcpairF (FOnumeral 1) FOZero (FOVar (V + 2)))) by wk Ca
    end.
    pose proof (FOPrH_numr_cong1 n _ (FOVar (V + 1)) (FOSucc (FOVar w)) (FOVar (V + 3)) Hb2 HY
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hb3.
    refine (PRI_numr_invS n _ _ (S w) 0 _ _ _ (FOVar w) (FOVar (V + 3)) Hb3 _ _ _ _ _ _);
      [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
    intros w' Hw' _.
    lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
      assert (HG3 : FOctx_avoid G3 0 1000) by (intros w'' ? ?; free_ctx);
      assert (Cb : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar w') (FOVar (V + 3)))) by wk_in;
      assert (Nw : FOPrH n G3 (FONUMR (FOVar w) (FOVar w'))) by wk_in;
      assert (Ca3 : FOPrH n G3 (FOcpairF (FOnumeral 1) FOZero (FOVar (V + 2)))) by wk Ca2;
      assert (HE : EnvOK n (S w') G3 [FOVar w'])
        by (apply (EnvOK1 n _ _ _ (FOVar w)); [intros w'' ? ?; apply HG3; lia | exact Nw
                                              | avoid_tms | lia | above_tac])
    end.
    pose proof (PRI_thm_open n k (S w') _ _ (rhoN 1) _ FOPr_zero_ne_succ HE
                  (rhoN_fv 1 (FONeg (FOEq FOZero (FOSucc (FOVar 0))))
                     ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T.
    refine (PRI_conv n _ _ (S w') _ _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc Ca3) as C1.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cb) as C2.
    unfold fNeq2, rhoN, FONeg. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
Qed.

Lemma NEQ_step : forall n k V G,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  PRI n (FOPrCores k) (FOu0 k) (V + 4)
    ((((G ++ [PhiNeq (FOPrCores k) (FOu0 k) (V + 4) (V + 1) (V + 2) (V + 3)
                (cpat_f (rhoN 2) fNeq2) (FOVar V)])
        ++ [FONeg (FOEq (FOSucc (FOVar V)) (FOVar (V + 1)))])
        ++ [FONUMR (FOSucc (FOVar V)) (FOVar (V + 2))])
        ++ [FONUMR (FOVar (V + 1)) (FOVar (V + 3))])
    (cpat_f (rhoN 2) fNeq2) [FOVar (V + 2); FOVar (V + 3)].
Proof.
  intros n k V G HV HG0 HGV.
  set (R := V + 4 + cpat_span (cpat_f (rhoN 2) fNeq2) + 1).
  lazymatch goal with |- PRI _ _ _ _ ?G1 _ _ =>
    assert (HG1 : FOctx_avoid G1 0 1000) by (intros w ? ?; free_ctx);
    assert (HPhi : FOPrH n G1 (PhiNeq (FOPrCores k) (FOu0 k) (V + 4) (V + 1) (V + 2) (V + 3)
                                (cpat_f (rhoN 2) fNeq2) (FOVar V))) by wk_in;
    assert (Hne : FOPrH n G1 (FONeg (FOEq (FOSucc (FOVar V)) (FOVar (V + 1))))) by wk_in;
    assert (Ha : FOPrH n G1 (FONUMR (FOSucc (FOVar V)) (FOVar (V + 2)))) by wk_in;
    assert (Hb : FOPrH n G1 (FONUMR (FOVar (V + 1)) (FOVar (V + 3)))) by wk_in
  end.
  refine (PRI_numr_invS n _ _ (V + 4) R _ _ _ (FOVar V) (FOVar (V + 2)) Ha _ _ _ _ _ _);
    [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
  intros w1 Hw1 HR1.
  lazymatch goal with |- PRI _ _ _ _ ?G2 _ _ =>
    assert (HG2 : FOctx_avoid G2 0 1000) by (intros w ? ?; free_ctx);
    assert (Ca : FOPrH n G2 (FOcpairF (FOnumeral 2) (FOVar w1) (FOVar (V + 2)))) by wk_in;
    assert (N1 : FOPrH n G2 (FONUMR (FOVar V) (FOVar w1))) by wk_in;
    assert (HPhi2 : FOPrH n G2 (PhiNeq (FOPrCores k) (FOu0 k) (V + 4) (V + 1) (V + 2) (V + 3)
                                  (cpat_f (rhoN 2) fNeq2) (FOVar V))) by wk HPhi;
    assert (Hne2 : FOPrH n G2 (FONeg (FOEq (FOSucc (FOVar V)) (FOVar (V + 1))))) by wk Hne;
    assert (Hb2 : FOPrH n G2 (FONUMR (FOVar (V + 1)) (FOVar (V + 3)))) by wk Hb
  end.
  refine (PRI_zs n _ _ (S w1) R _ _ _ (FOVar (V + 1)) _ _ _ _ _ _ _);
    [lia | avoid_tms | intros w ?; fr_tm | avoid_tms | above_tac | |].
  - lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
      assert (HG3 : FOctx_avoid G3 0 1000) by (intros w ? ?; free_ctx);
      assert (HY : FOPrH n G3 (FOEq (FOVar (V + 1)) FOZero)) by wk_in;
      assert (Hb3 : FOPrH n G3 (FONUMR (FOVar (V + 1)) (FOVar (V + 3)))) by wk Hb2;
      assert (Ca3 : FOPrH n G3 (FOcpairF (FOnumeral 2) (FOVar w1) (FOVar (V + 2)))) by wk Ca;
      assert (N13 : FOPrH n G3 (FONUMR (FOVar V) (FOVar w1))) by wk N1
    end.
    pose proof (FOPrH_numr_cong1 n _ (FOVar (V + 1)) FOZero (FOVar (V + 3)) Hb3 HY
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hb0.
    pose proof (FOPrH_numr_inv0 n _ (FOVar (V + 3)) ltac:(intros w ? ?; apply HG3; lia)
                  ltac:(avoid_tms) Hb0) as Cb.
    lazymatch type of HG3 with FOctx_avoid ?G3 _ _ =>
      assert (HE : EnvOK n (S w1) G3 [FOVar w1])
        by (apply (EnvOK1 n _ _ _ (FOVar V)); [intros w ? ?; apply HG3; lia | exact N13
                                             | avoid_tms | lia | above_tac])
    end.
    pose proof (PRI_thm_open n k (S w1) _ _ (rhoN 1) _ FOPr_succ_ne_zero HE
                  (rhoN_fv 1 (FONeg (FOEq (FOSucc (FOVar 0)) FOZero))
                     ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T.
    refine (PRI_conv n _ _ (S w1) _ _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc Ca3) as C1.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cb) as C2.
    unfold fNeq2, rhoN, FONeg. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
  - intros w2 Hw2 HR2.
    lazymatch goal with |- PRI _ _ _ _ ?G3 _ _ =>
      assert (HG3 : FOctx_avoid G3 0 1000) by (intros w ? ?; free_ctx);
      assert (HY : FOPrH n G3 (FOEq (FOVar (V + 1)) (FOSucc (FOVar w2)))) by wk_in;
      assert (Hb3 : FOPrH n G3 (FONUMR (FOVar (V + 1)) (FOVar (V + 3)))) by wk Hb2
    end.
    pose proof (FOPrH_numr_cong1 n _ (FOVar (V + 1)) (FOSucc (FOVar w2)) (FOVar (V + 3)) Hb3 HY
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as Hb4.
    refine (PRI_numr_invS n _ _ (S w2) R _ _ _ (FOVar w2) (FOVar (V + 3)) Hb4 _ _ _ _ _ _);
      [lia | avoid_tms | above_tac | avoid_tms | above_tac |].
    intros w3 Hw3 HR3.
    lazymatch goal with |- PRI _ _ _ _ ?G4 _ _ =>
      assert (HG4 : FOctx_avoid G4 0 1000) by (intros w ? ?; free_ctx);
      assert (Cb : FOPrH n G4 (FOcpairF (FOnumeral 2) (FOVar w3) (FOVar (V + 3)))) by wk_in;
      assert (N3 : FOPrH n G4 (FONUMR (FOVar w2) (FOVar w3))) by wk_in;
      assert (HY4 : FOPrH n G4 (FOEq (FOVar (V + 1)) (FOSucc (FOVar w2)))) by wk HY;
      assert (Ca4 : FOPrH n G4 (FOcpairF (FOnumeral 2) (FOVar w1) (FOVar (V + 2)))) by wk Ca;
      assert (N14 : FOPrH n G4 (FONUMR (FOVar V) (FOVar w1))) by wk N1;
      assert (HPhi4 : FOPrH n G4 (PhiNeq (FOPrCores k) (FOu0 k) (V + 4) (V + 1) (V + 2)
                                    (V + 3) (cpat_f (rhoN 2) fNeq2) (FOVar V))) by wk HPhi2;
      assert (Hne4 : FOPrH n G4 (FONeg (FOEq (FOSucc (FOVar V)) (FOVar (V + 1))))) by wk Hne2
    end.
    lazymatch type of HG4 with FOctx_avoid ?G4 _ _ =>
      assert (Hvw : FOPrH n G4 (FONeg (FOEq (FOVar V) (FOVar w2))))
    end.
    { unfold FONeg. apply FOPrH_intro.
      apply (FOPrH_mp _ _ _ _ (FOPrH_weak_app _ _ _ _ Hne4)).
      apply (FOPrH_eq_trans _ _ _ (FOSucc (FOVar w2))).
      - apply FOPrH_congS. apply FOPrH_last.
      - apply FOPrH_eq_sym. apply FOPrH_weak_app. exact HY4. }
    pose proof (PhiNeq_inst n _ _ _ (V + 4) (V + 1) (V + 2) (V + 3) _ (FOVar V) (FOVar w2)
                  (FOVar w1) (FOVar w3) HPhi4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(avoid_tms)
                  ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)) as IH.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ IH Hvw) N14) N3) as IHf.
    pose proof (PRIf_to_PRI n _ _ (S w3) _ _ _ (V + 4) IHf ltac:(lia) ltac:(avoid_tms) ltac:(lia)
                  ltac:(avoid_tms) ltac:(above_tac)) as IHP.
    lazymatch type of HG4 with FOctx_avoid ?G4 _ _ =>
      assert (HE : EnvOK n (S w3) G4 [FOVar w1; FOVar w3])
        by (apply (EnvOK2 n _ _ _ _ (FOVar V) (FOVar w2));
            [intros w ? ?; apply HG4; lia | exact N14 | exact N3 | avoid_tms | lia
            | above_tac])
    end.
    pose proof (PRI_thm_open n k (S w3) _ _ (rhoN 2) _ FOPr_succ_ne HE
                  (rhoN_fv 2 (FOImplF (FONeg (FOEq (FOVar 0) (FOVar 1)))
                                (FONeg (FOEq (FOSucc (FOVar 0)) (FOSucc (FOVar 1)))))
                     ltac:(apply Nat.ltb_lt; vm_compute; reflexivity))) as T.
    pose proof (PRI_mp n _ _ (S w3) _ (rhoN 2) _ _ _ HE (rhoN_range 2) T IHP) as T2.
    refine (PRI_conv n _ _ (S w3) _ _ _ _ _ _ _ _ _ T2); [| above_tac | avoid_tms | lia].
    intros G' Hinc.
    pose proof (FOPrH_weaken n _ G' _ Hinc Ca4) as C1.
    pose proof (FOPrH_weaken n _ G' _ Hinc Cb) as C2.
    unfold fNeq2, rhoN, FONeg. cbn [cpat_f cpat_tm Nat.ltb Nat.leb]. cprel_tac.
Qed.

Lemma PRI_neq : forall n k V G x y m1 m2,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  FOtms_avoid [x; y; m1; m2] 0 1100 ->
  (forall t, In t [x; y; m1; m2] -> forall w, V <= w -> FOin_tm w t = false) ->
  FOPrH n G (FONeg (FOEq x y)) -> FOPrH n G (FONUMR x m1) -> FOPrH n G (FONUMR y m2) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f (rhoN 2) fNeq2) [m1; m2].
Proof.
  intros n k V G x y m1 m2 HV HG0 HGV Hav0 Havv Hne Hx Hy.
  assert (HI : FOPrH n G (FOForall V (PhiNeq (FOPrCores k) (FOu0 k) (V + 4) (V + 1) (V + 2)
                                        (V + 3) (cpat_f (rhoN 2) fNeq2) (FOVar V)))).
  { apply FOPrH_ind; [apply HGV; lia | |].
    - rewrite PhiNeq_subst by first [lia | avoid_tms].
      unfold PhiNeq.
      apply FOPrH_all_intro; [apply HGV; lia|]. apply FOPrH_all_intro; [apply HGV; lia|].
      apply FOPrH_all_intro; [apply HGV; lia|].
      apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_intro.
      apply (PRI_to_PRIf n _ _ (V + 4) _ [FOVar (V + 2); FOVar (V + 3)] _ (V + 4)
               (NEQ_base n k V G HV HG0 HGV));
        [lia | lia | intros w ? ?; free_ctx | intros w ?; free_ctx | avoid_tms | above_tac].
    - rewrite PhiNeq_subst by first [lia | avoid_tms].
      unfold PhiNeq at 2.
      apply FOPrH_all_intro; [free_ctx|]. apply FOPrH_all_intro; [free_ctx|].
      apply FOPrH_all_intro; [free_ctx|].
      apply FOPrH_intro. apply FOPrH_intro. apply FOPrH_intro.
      apply (PRI_to_PRIf n _ _ (V + 4) _ [FOVar (V + 2); FOVar (V + 3)] _ (V + 4)
               (NEQ_step n k V G HV HG0 HGV));
        [lia | lia | intros w ? ?; free_ctx | intros w ?; free_ctx | avoid_tms | above_tac]. }
  apply (FOPrH_inst n G V x) in HI;
    [| unfold PhiNeq; apply FOsubst_ok_all; [fr_tm|]; apply FOsubst_ok_all; [fr_tm|];
       apply FOsubst_ok_all; [fr_tm|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_neg; apply FOsubst_ok_eq|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_impl; [apply FOsubst_ok_NUMR; [lia | avoid_tms | avoid_tms]|];
       apply FOsubst_ok_PRIf; [lia | fr_tm | avoid_tm]].
  rewrite PhiNeq_subst in HI by first [lia | avoid_tms].
  pose proof (PhiNeq_inst n G _ _ (V + 4) (V + 1) (V + 2) (V + 3) _ x y m1 m2 HI ltac:(lia)
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(lia) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms) ltac:(avoid_tms)
                ltac:(avoid_tms)) as HI2.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ (FOPrH_mp _ _ _ _ HI2 Hne) Hx) Hy) as HP.
  exact (PRIf_to_PRI n _ _ V G [m1; m2] _ (V + 4) HP ltac:(lia) ltac:(avoid_tms) ltac:(lia)
           ltac:(avoid_tms) ltac:(above_tac)).
Qed.

Lemma PRI_neq_gen : forall n k V G rho env z1 z2 j1 j2 x y,
  2000 <= V -> FOctx_avoid G 0 1000 -> (forall w, V <= w -> FOfree_ctx w G) ->
  EnvOK n V G env -> FOtms_avoid env 0 1100 -> FOtms_avoid [x; y] 0 1100 ->
  (forall t, In t [x; y] -> forall w, V <= w -> FOin_tm w t = false) ->
  rho z1 = Some j1 -> rho z2 = Some j2 ->
  FOPrH n G (FONeg (FOEq x y)) -> FOPrH n G (FONUMR x (nth j1 env FOZero)) ->
  FOPrH n G (FONUMR y (nth j2 env FOZero)) ->
  PRI n (FOPrCores k) (FOu0 k) V G (cpat_f rho (FONeg (FOEq (FOVar z1) (FOVar z2)))) env.
Proof.
  intros n k V G rho env z1 z2 j1 j2 x y HV HG0 HGV HE Henv Hxy Hxyv Hz1 Hz2 Hne H1 H2.
  pose proof HE as [_ [_ [_ Henvv]]].
  pose proof (PRI_neq n k V G x y (nth j1 env FOZero) (nth j2 env FOZero) HV HG0 HGV
                ltac:(avoid_tms) ltac:(above_tac) Hne H1 H2) as T.
  refine (PRI_conv n _ _ V G _ _ _ _ _ _ _ _ T); [| above_tac | avoid_tms | lia].
  intros G' Hinc. unfold fNeq2, rhoN, FONeg. cbn [cpat_f cpat_tm Nat.ltb Nat.leb].
  rewrite Hz1, Hz2. cprel_tac.
Qed.
