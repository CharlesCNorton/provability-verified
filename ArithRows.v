(******************************************************************************)
(*                                                                            *)
(*           Parametric Provability: Bypassing the Loebian Obstacle           *)
(*                                                                            *)
(*     Part 8 of 11. Table rows and one-line derivations inside T_0.          *)
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
  ArithMerge ArithDerivability.
Open Scope fo_scope.

(** ** Freshness of the pattern and guard facts. *)

Lemma FOfree_in_PATF_any : forall w B env p d,
  2 <= w -> FOtms_avoid (d :: env) w (S w) -> FOfree_in w (FOPATF B env p d) = false.
Proof.
  intros w B env p d Hw Hav.
  destruct (FOfree_in w (FOPATF B env p d)) eqn:E; [exfalso | reflexivity].
  apply FOPATF_free in E. destruct E as [E|[E|E]].
  - apply existsb_exists in E. destruct E as [t [Ht E]].
    rewrite (Hav t (or_intror Ht) w ltac:(lia) ltac:(lia)) in E. discriminate E.
  - rewrite (Hav d (or_introl eq_refl) w ltac:(lia) ltac:(lia)) in E. discriminate E.
  - lia.
Qed.

Lemma FOfree_in_GUARDB_any : forall w c,
  2 <= w -> FOtms_avoid [c] w (S w) -> FOfree_in w (FOGUARDB c) = false.
Proof.
  intros w c Hw Hav. unfold FOGUARDB.
  repeat match goal with
         | |- FOfree_in _ (FOExists ?y _) = false =>
             destruct (Nat.eq_dec y w) as [<-|?];
             [apply FOfree_in_ex_self | rewrite FOfree_in_FOExists_neq by assumption]
         end.
  rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
  - free_by FOTBLVALID_free.
  - rewrite FOBexC_ltv.
    destruct (Nat.eq_dec 13 w) as [<-|?]; [apply FOfree_in_ex_self|].
    rewrite FOfree_in_FOExists_neq by assumption.
    rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    + apply FOfree_in_ltv; [lia | fr_tm].
    + free_by FOlookup_free.
Qed.

Ltac free_fm ::=
  lazymatch goal with
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
  | |- _ => free_fm_core
  end.

(** ** Modus ponens under the matrix in a context whose free variables
    lie outside the eigenvariable ranges. *)

Lemma FOPrH_D2_gen : forall n G cores a b c,
  FOctx_avoid G 2 500 ->
  FOPrH n G (FOPATF 52 [b; c] cpatImpl01 a) ->
  FOPrH n G (FOGUARDB c) ->
  FOtms_avoid [a; b; c] 1 500 ->
  FOPrH n G (FOPRMATx cores a .-> FOPRMATx cores b .-> FOPRMATx cores c).
Proof.
  intros n G cores a b c HG HP HB Hav.
  apply (FOPrH_PRMAT_elim_rename n G cores a 330);
    [lia | lia | intros w H1 H2; apply HG; lia | side | avoid_tms |].
  cbn [Nat.add].
  apply (FOPrH_PRMAT_elim_rename n _ cores b 260); [lia | lia | side | side | avoid_tms |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (D1 : FOPrH n Gc (FOPRDERp cores a (FOtabv 330) (FOVar 341) (FOVar 342)
                               (FOVar 343) (FOVar 344) (FOVar 345))) by wk_in;
    assert (D2 : FOPrH n Gc (FOPRDERp cores b (FOtabv 260) (FOVar 271) (FOVar 272)
                               (FOVar 273) (FOVar 274) (FOVar 275))) by wk_in;
    assert (HP0 : FOPrH n Gc (FOPATF 52 [b; c] cpatImpl01 a)) by wk HP;
    assert (HB0 : FOPrH n Gc (FOGUARDB c)) by wk HB;
    assert (A0 : FOctx_avoid Gc 2 18) by ctx_list;
    assert (A1 : FOctx_avoid Gc 18 260) by ctx_list;
    assert (A2 : FOctx_avoid Gc 276 330) by ctx_list;
    assert (A3 : FOctx_avoid Gc 346 500) by ctx_list;
    set (G0 := Gc) in *
  end.
  clearbody G0. clear HP HB HG.
  refine (FOPrH_mp _ _ (FOGUARDB c) _ _ HB0).
  unfold FOGUARDB.
  do 11 (apply FOPrH_imp_exl; [free_ctx | free_fm |]).
  apply FOPrH_imp_andl. apply FOPrH_intro.
  apply FOPrH_imp_bexl; [free_ctx | free_fm |]. apply FOPrH_intro.
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (D1' : FOPrH n Gc (FOPRDERp cores a (FOtabv 330) (FOVar 341) (FOVar 342)
                                (FOVar 343) (FOVar 344) (FOVar 345))) by wk D1;
    assert (D2' : FOPrH n Gc (FOPRDERp cores b (FOtabv 260) (FOVar 271) (FOVar 272)
                                (FOVar 273) (FOVar 274) (FOVar 275))) by wk D2;
    assert (HP1 : FOPrH n Gc (FOPATF 52 [b; c] cpatImpl01 a)) by wk HP0;
    assert (VB : FOPrH n Gc (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5)
                               (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10)
                               (FOVar 11) (FOVar 12))) by wk_in;
    assert (LK : FOPrH n Gc (FOlookup 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5)
                               (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10)
                               (FOVar 11) (FOVar 12) (FOnumeral 3) (FOSucc c) FOZero c
                               (FOVar 13))) by wk_in;
    assert (Le : FOPrH n Gc (FOle (FOSucc (FOVar 13)) (FOSucc (FOVar 10))))
      by (apply FOPrH_le_of_ltv; [free_ctx | lia | lia | avoid_tm | avoid_tm | wk_in]);
    assert (B1 : FOctx_avoid Gc 18 260) by ctx_list;
    assert (B2 : FOctx_avoid Gc 276 330) by ctx_list;
    assert (B3 : FOctx_avoid Gc 346 500) by ctx_list;
    set (G1 := Gc) in *
  end.
  clearbody G1. clear D1 D2 HP0 HB0 A0 A1 A2 A3.
  pose proof D1' as E1. unfold FOPRDERp in E1.
  apply FOPrH_and_r, FOPrH_and_l in E1.
  pose proof D2' as E2. unfold FOPRDERp in E2.
  apply FOPrH_and_r, FOPrH_and_l in E2.
  apply (FOPrH_final_elim n _ (FOVar 345) (FOVar 341) (FOVar 342) a 290 _ E1);
    [side | side | lia | side | side |].
  apply (FOPrH_final_elim n _ (FOVar 275) (FOVar 271) (FOVar 272) b 291);
    [wk E2 | side | side | lia | side | side |].
  apply (FOPrH_merge3_elim n _ (FOVar 330) (FOVar 331) (FOVar 340) (FOVar 260) (FOVar 261)
           (FOVar 270) (FOVar 2) (FOVar 3) (FOVar 12) 292 293 294 295); [side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 332) (FOVar 333) (FOVar 340) (FOVar 262) (FOVar 263)
           (FOVar 270) (FOVar 4) (FOVar 5) (FOVar 12) 296 297 298 299); [side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 334) (FOVar 335) (FOVar 340) (FOVar 264) (FOVar 265)
           (FOVar 270) (FOVar 6) (FOVar 7) (FOVar 12) 300 301 302 303); [side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 336) (FOVar 337) (FOVar 340) (FOVar 266) (FOVar 267)
           (FOVar 270) (FOVar 8) (FOVar 9) (FOVar 12) 304 305 306 307); [side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 338) (FOVar 339) (FOVar 340) (FOVar 268) (FOVar 269)
           (FOVar 270) (FOVar 10) (FOVar 11) (FOVar 12) 308 309 310 311); [side.. |].
  apply (FOPrH_ftrack_elim n _ (FOVar 341) (FOVar 342) (FOVar 345) (FOVar 271) (FOVar 272)
           (FOVar 275) c 312 313 314 315); [side.. |].
  apply (FOPrH_jtrack_elim n _ (FOVar 343) (FOVar 344) (FOVar 345) (FOVar 273) (FOVar 274)
           (FOVar 275) (FOVar 290) (FOVar 291) 316); [side.. |].
  cbn [Nat.add].
  apply (FOPrH_PRMAT_intro n _ cores c (FOVar 294) (FOVar 295) (FOVar 298) (FOVar 299)
           (FOVar 302) (FOVar 303) (FOVar 306) (FOVar 307) (FOVar 310) (FOVar 311)
           (FOPlus (FOPlus (FOVar 340) (FOVar 270)) (FOVar 12)) (FOVar 314) (FOVar 315)
           (FOVar 323) (FOVar 324) (FOPlus (FOPlus (FOVar 345) (FOVar 275)) (FOSucc FOZero)));
    [avoid_tms | avoid_tms |].
  apply (FOPrH_D2_body n _ cores (FOtabv 330) (FOtabv 260) (FOtabv 2)
           (mkTab (FOVar 294) (FOVar 295) (FOVar 298) (FOVar 299) (FOVar 302) (FOVar 303)
              (FOVar 306) (FOVar 307) (FOVar 310) (FOVar 311)
              (FOPlus (FOPlus (FOVar 340) (FOVar 270)) (FOVar 12)))
           (FOVar 341) (FOVar 342) (FOVar 343) (FOVar 344) (FOVar 345)
           (FOVar 271) (FOVar 272) (FOVar 273) (FOVar 274) (FOVar 275)
           (FOVar 314) (FOVar 315) (FOVar 323) (FOVar 324) (FOVar 290) (FOVar 291)
           a b c (FOVar 321) (FOVar 322) (FOVar 13) 316 325 326 327 328 329).
  all: lazymatch goal with
       | |- FOPrH _ _ _ => idtac
       | |- FOtms_avoid _ _ _ => tab_avoid
       | |- forall v, In v _ -> _ =>
           let v := fresh "v" in let Hv := fresh "Hv" in
           intros v Hv; simpl in Hv;
           destruct Hv as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; tab_avoid
       | |- _ = _ => reflexivity
       | |- _ => side
       end.
  - wk D1'.
  - wk D2'.
  - wk VB.
  - wk Le.
  - wk LK.
  - apply (FOPrH_and_l _ _ _ (FObetaF 20 (FOVar 341) (FOVar 342) (FOVar 290) a)). wk_in.
  - apply (FOPrH_and_r _ _ (FOEq (FOVar 345) (FOSucc (FOVar 290)))). wk_in.
  - apply (FOPrH_and_l _ _ _ (FObetaF 20 (FOVar 271) (FOVar 272) (FOVar 291) b)). wk_in.
  - apply (FOPrH_and_r _ _ (FOEq (FOVar 275) (FOSucc (FOVar 291)))). wk_in.
  - wk HP1.
  - unfold FOTABM3.
    apply FOPrH_and_intro; [wk_in|].
    apply FOPrH_and_intro; [wk_in|].
    apply FOPrH_and_intro; [wk_in|].
    apply FOPrH_and_intro; wk_in.
  - wk_in.
  - wk_in.
Qed.

(** ** Internal modus ponens as one theorem of the tower.

    For all codes [a], [b], [c]: when [a] codes the implication from
    [b] to [c] and the guard rows of [c] exist, the matrix at [a] and at
    [b] gives the matrix at [c].  The variable [0] stays free. *)

Definition FOD2F (cores : list nat) : FOFormula :=
  FOForall 600 (FOForall 601 (FOForall 602
    (FOPATF 52 [FOVar 601; FOVar 602] cpatImpl01 (FOVar 600) .->
     FOGUARDB (FOVar 602) .->
     FOPRMATx cores (FOVar 600) .-> FOPRMATx cores (FOVar 601) .->
     FOPRMATx cores (FOVar 602)))).

Theorem FOPr_D2F : forall n cores, FOProvesTn n (FOD2F cores).
Proof.
  intros n cores.
  assert (H : FOPrH n [FOPATF 52 [FOVar 601; FOVar 602] cpatImpl01 (FOVar 600);
                       FOGUARDB (FOVar 602)]
                (FOPRMATx cores (FOVar 600) .-> FOPRMATx cores (FOVar 601) .->
                 FOPRMATx cores (FOVar 602))).
  { apply FOPrH_D2_gen.
    - intros w H1 H2. free_ctx.
    - apply FOPrH_assum. left. reflexivity.
    - apply FOPrH_assum. right. left. reflexivity.
    - avoid_tms. }
  change [FOPATF 52 [FOVar 601; FOVar 602] cpatImpl01 (FOVar 600); FOGUARDB (FOVar 602)]
    with ([] ++ [FOPATF 52 [FOVar 601; FOVar 602] cpatImpl01 (FOVar 600)] ++
          [FOGUARDB (FOVar 602)]) in H.
  rewrite app_assoc in H.
  apply FOPrH_intro, FOPrH_intro in H.
  unfold FOD2F.
  apply (FOPrH_all_intro n [] 602 _ (FOfree_ctx_nil 602)) in H.
  apply (FOPrH_all_intro n [] 601 _ (FOfree_ctx_nil 601)) in H.
  apply (FOPrH_all_intro n [] 600 _ (FOfree_ctx_nil 600)) in H.
  unfold FOPrH in H. cbn [FOimps] in H.
  exact H.
Qed.

(** ** A bounded universal extended by its last position. *)

Lemma FOPrH_ball_snoc : forall n G v L P w,
  FOPrH n G (FOBallC v L P) -> FOPrH n G (FOsubst_f v L P) ->
  FOsubst_ok v L P = true ->
  2 <= v -> v < 399 -> 1 < w -> w <> v -> w <> S v ->
  FOfree_ctx v G -> FOfree_ctx (S v) G -> FOfree_ctx w G ->
  FOfree_in (S v) P = false -> FOfree_in w P = false ->
  FOtms_avoid [L] v (S (S v)) -> FOtms_avoid [L] w (S w) -> FOtms_avoid [L] 400 500 ->
  FOPrH n G (FOBallC v (FOSucc L) P).
Proof.
  intros n G v L P w H1 H2 Hok Hv1 Hv2 Hw1 Hwv HwSv HGv HGSv HGw FSP FwP Hav1 Hav2 Hav3.
  rewrite FOBallC_ltv. apply FOPrH_all_intro; [exact HGv|]. apply FOPrH_intro.
  refine (FOPrH_ex_elim _ _ (S v) (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) (FOSucc L))
            _ _ FSP _ _); [free_ctx | unfold FOltv; apply FOPrH_last |].
  apply (FOPrH_cases_zs _ _ (FOVar (S v)) w P); [lia | fr_tm | free_ctx | exact FwP | fr_tm | |].
  - lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (Z : FOPrH n Gc (FOEq (FOVar (S v)) FOZero)) by wk_in;
      assert (H2w : FOPrH n Gc (FOsubst_f v L P)) by wk H2;
      assert (E2 : FOPrH n Gc (FOEq L (FOVar v)))
    end.
    { pose proof (FOPrH_eq_sym _ _ _ _ Z) as Z'.
      fo_lin [(.S .0, #v .+ .S (FOVar (S v)), .S L); (.S .0, .0, FOVar (S v))]; exact Z'. }
    pose proof (FOPrH_leibniz _ _ v L (FOVar v) P Hok (FOsubst_ok_var_self P v) E2 H2w) as E3.
    rewrite FOsubst_f_id in E3. exact E3.
  - lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (E1 : FOPrH n Gc (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) (FOSucc L)))
        by wk_in;
      assert (H1w : FOPrH n Gc (FOBallC v L P)) by wk H1
    end.
    pose proof (FOPrH_eq_sym _ _ _ _ E1) as E1'.
    rewrite FOBallC_ltv in H1w. apply FOPrH_all_same in H1w.
    refine (FOPrH_mp _ _ _ _ H1w _).
    unfold FOltv. apply (FOPrH_ex_intro _ _ (S v) (FOVar w)); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_succ, FOsubst_t_var_eq',
      FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in L (S v) _ (Hav1 L ltac:(in_list) (S v) ltac:(lia) ltac:(lia))).
    fo_lin [(.S .0, .S L, #v .+ .S (FOVar (S v))); (.S .0, FOVar (S v), .S (FOVar w))];
      exact E1'.
Qed.

(** ** A table extended by one row.

    [FOTEXT T T' tg a1 a2 a3 r]: every column of [T'] extends the
    column of [T] by one entry, the entries forming the row
    [(tg, a1, a2, a3, r)]; the length of [T'] is one more. *)

Definition FOTEXT (T T' : FOtab) (tg a1 a2 a3 r : FOTerm) : FOFormula :=
  FOAnd (FOEXTF (tct T) (tlen T) (tct T) (tdt T) tg (tct T') (tdt T'))
  (FOAnd (FOEXTF (tc1 T) (tlen T) (tc1 T) (td1 T) a1 (tc1 T') (td1 T'))
  (FOAnd (FOEXTF (tc2 T) (tlen T) (tc2 T) (td2 T) a2 (tc2 T') (td2 T'))
  (FOAnd (FOEXTF (tc3 T) (tlen T) (tc3 T) (td3 T) a3 (tc3 T') (td3 T'))
         (FOEXTF (tcr T) (tlen T) (tcr T) (tdr T) r (tcr T') (tdr T'))))).

Lemma FOPrH_ex468_le : forall n G b c,
  FOPrH n G (FOExists 468 (FOEq (FOPlus b (FOVar 468)) c)) ->
  FOtms_avoid [b; c] 420 500 ->
  FOPrH n G (FOle (FOSucc b) (FOSucc c)).
Proof.
  intros n G b c H Hav.
  refine (FOPrH_ctxfree n G _ _ _ H).
  refine (FOPrH_ex_elim n [FOExists 468 (FOEq (FOPlus b (FOVar 468)) c)] 468
            (FOEq (FOPlus b (FOVar 468)) c) _ _ _ _ _);
    [free_ctx | free_fm | apply FOPrH_assum; left; reflexivity |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (E : FOPrH n Gc (FOEq c (FOPlus b (FOVar 468)))) by (apply FOPrH_eq_sym; wk_in)
  end.
  unfold FOle. apply (FOPrH_ex_intro _ _ 498 (FOVar 468)); [cbn [FOsubst_ok]; reflexivity|].
  rewrite FOsubst_f_eq, FOsubst_t_plus, !FOsubst_t_succ, FOsubst_t_var_eq'. subst_avoid_h Hav.
  fo_lin [(.S .0, c, b .+ #468)]; exact E.
Qed.

Ltac text_split H :=
  unfold FOTEXT, FOEXTF in H;
  let Xt := fresh "Xt" in let X1 := fresh "X1" in let X2 := fresh "X2" in
  let X3 := fresh "X3" in let Xr := fresh "Xr" in
  pose proof (FOPrH_and_l _ _ _ _ H) as Xt;
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ H)) as X1;
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ H))) as X2;
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ H)))) as X3;
  pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                (FOPrH_and_r _ _ _ _ H)))) as Xr.

Lemma FOPrH_text_mono : forall n G T T' tg a1 a2 a3 r,
  FOPrH n G (FOTEXT T T' tg a1 a2 a3 r) -> tlen T' = FOSucc (tlen T) ->
  FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 420 500 ->
  FOTabMono n G T T'.
Proof.
  intros n G T T' tg a1 a2 a3 r H Hlen HG Hav.
  text_split H.
  split.
  - unfold FOTabAgree. apply FOPrH_incl_agr;
      [ exact (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ Xt))
      | exact (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ X1))
      | exact (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ X2))
      | exact (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ X3))
      | exact (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ Xr))
      | | exact HG | avoid_tms ].
    rewrite Hlen. unfold FOle.
    apply (FOPrH_ex_intro _ _ 498 (FOSucc FOZero)); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, FOsubst_t_plus, ?FOsubst_t_succ, FOsubst_t_var_eq'.
    subst_avoid_h Hav. apply FOPrH_ring. fo_ring.
  - repeat split; apply FOPrH_ex468_le;
      first [ exact (FOPrH_and_l _ _ _ _ Xt) | exact (FOPrH_and_l _ _ _ _ X1)
            | exact (FOPrH_and_l _ _ _ _ X2) | exact (FOPrH_and_l _ _ _ _ X3)
            | exact (FOPrH_and_l _ _ _ _ Xr) | avoid_tms ].
Qed.

Lemma FOPrH_text_lookup : forall n G B T T' tg a1 a2 a3 r,
  FOPrH n G (FOTEXT T T' tg a1 a2 a3 r) -> tlen T' = FOSucc (tlen T) ->
  2 <= B -> B + 22 <= 420 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) B (B + 22) ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 420 500 ->
  FOPrH n G (FOlookup B (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') tg a1 a2 a3 r).
Proof.
  intros n G B T T' tg a1 a2 a3 r H Hlen HB1 HB2 Hav1 Hav2.
  text_split H.
  unfold FOlookup. rewrite Hlen.
  apply (FOPrH_bex_intro_t _ _ B (FOSucc (tlen T)) (tlen T)); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | | | ].
  - unfold FOle. apply (FOPrH_ex_intro _ _ 498 FOZero); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, FOsubst_t_plus, !FOsubst_t_succ, FOsubst_t_var_eq'.
    subst_avoid_h Hav2. apply FOPrH_Q_plus_zero.
  - repeat (apply FOsubst_ok_and; [apply FOsubst_ok_betaF; avoid_tm|]);
      apply FOsubst_ok_betaF; avoid_tm.
  - rewrite !FOsubst_f_and, !FOsubst_f_betaF by lia. rewrite !FOsubst_t_var_eq'.
    subst_avoid_h Hav1.
    repeat (apply FOPrH_and_intro;
            [ first [ refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                               (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ Xt)));
                      [lia | avoid_tms | avoid_tms]
                    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                               (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ X1)));
                      [lia | avoid_tms | avoid_tms]
                    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                               (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ X2)));
                      [lia | avoid_tms | avoid_tms]
                    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                               (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ X3)));
                      [lia | avoid_tms | avoid_tms] ] |]).
    refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
              (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ Xr)));
      [lia | avoid_tms | avoid_tms].
Qed.

(** A valid table extended by a row whose dispatch clause holds at the
    new position is valid. *)

Lemma FOPrH_tbl_extend : forall n G T T' tg a1 a2 a3 r,
  FOPrH n G (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T)) ->
  FOPrH n G (FOTEXT T T' tg a1 a2 a3 r) -> tlen T' = FOSucc (tlen T) ->
  FOPrH n G (FOSTEPDISPATCH 20 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T')
               (tc3 T') (td3 T') (tcr T') (tdr T') (tlen T') (tlen T)) ->
  FOctx_avoid G 18 122 -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 18 122 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 400 500 ->
  FOPrH n G (FOTBLVALID 18 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T')).
Proof.
  intros n G T T' tg a1 a2 a3 r HV HX Hlen HD HG HG2 Hav1 Hav2.
  assert (Hav : FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r])
                  420 500) by avoid_tms.
  pose proof (FOPrH_text_mono n G T T' tg a1 a2 a3 r HX Hlen HG2 Hav) as Hm.
  text_split HX.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ Xt)) as At.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ X1)) as A1.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ X2)) as A2.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ X3)) as A3.
  pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ Xr)) as Ar.
  clear Xt X1 X2 X3 Xr.
  unfold FOTBLVALID in *. rewrite Hlen at 1.
  apply (FOPrH_ball_snoc n G 18 (tlen T) _ 21);
    [ | | apply FOsubst_ok_STEPDISPATCH; avoid_tm | lia | lia | lia | lia | lia
      | apply HG; lia | apply HG; lia | apply HG; lia
      | free_by FOSTEPDISPATCH_free | free_by FOSTEPDISPATCH_free
      | avoid_tms | avoid_tms | avoid_tms ].
  - refine (FOPrH_mp _ _ _ _ _ HV).
    apply FOPrH_ball_mono; [apply HG; lia | apply FOPrH_imp_refl|].
    apply FOPrH_intro.
    assert (Lt : FOPrH n (G ++ [FOltv 18 (tlen T)]) (FOlt470 (FOVar 18) (tlen T))).
    { refine (FOPrH_mp _ _ _ _ (FOPrH_ltv_470 _ _ 18 (tlen T) _ _ _ _) (FOPrH_last _ _ _));
        [lia | lia | avoid_tm | avoid_tm]. }
    apply (FOtr_DISPATCH n _ 20 T T' (FOVar 18) (FOVar 18));
      [ apply FOTabMono_weak; exact Hm
      | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ At) Lt _ _);
          [avoid_tms | avoid_tms]
      | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ A1) Lt _ _);
          [avoid_tms | avoid_tms]
      | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ A2) Lt _ _);
          [avoid_tms | avoid_tms]
      | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ A3) Lt _ _);
          [avoid_tms | avoid_tms]
      | refine (FOPrH_agr_row _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ Ar) Lt _ _);
          [avoid_tms | avoid_tms]
      | lia | ctx_list | ctx_list | avoid_tms | avoid_tms ].
  - rewrite FOsubst_f_STEPDISPATCH by lia. rewrite FOsubst_t_var_eq'. subst_avoid_h Hav1.
    exact HD.
Qed.

(** ** The dispatch clause at one row.

    [FODISPCASES]: the case split of the dispatch at base [20] with the
    row's fields [(tg, a1, a2, a3, r)] in place of its witnesses. *)

Definition FODISPCASES (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm)
    (tg a1 a2 a3 r : FOTerm) : FOFormula :=
  FOOr (FOAnd (FOEq tg FOZero)
          (FOSTEP0 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 r))
  (FOOr (FOAnd (FOEq tg (FOnumeral 1))
          (FOSTEP1 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 r))
  (FOOr (FOAnd (FOEq tg (FOnumeral 2))
          (FOSTEP2 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r))
  (FOOr (FOAnd (FOEq tg (FOnumeral 3))
          (FOSTEP3 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r))
  (FOOr (FOAnd (FOEq tg (FOnumeral 4))
          (FOSTEP4 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 a2 a3 r))
        (FOAnd (FOEq tg (FOnumeral 5))
          (FOSTEP5 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len a1 r)))))).

Ltac ok_step :=
  lazymatch goal with
  | |- FOsubst_ok _ ?s _ = true =>
      let V := fresh "V" in assert (V : FOtm_avoid s 20 122) by avoid_tm;
      solve [auto 100 with fook]
  end.

Lemma FOPrH_dispatch_intro : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len j tg a1 a2 a3 r,
  FOPrH n G (FObetaF 30 ct dt j tg) -> FOPrH n G (FObetaF 34 c1 d1 j a1) ->
  FOPrH n G (FObetaF 38 c2 d2 j a2) -> FOPrH n G (FObetaF 42 c3 d3 j a3) ->
  FOPrH n G (FObetaF 46 cr dr j r) ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) ->
  FOctx_avoid G 20 122 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; j; tg; a1; a2; a3; r] 20 122 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; j; tg; a1; a2; a3; r] 498 499 ->
  FOPrH n G (FOSTEPDISPATCH 20 ct dt c1 d1 c2 d2 c3 d3 cr dr len j).
Proof.
  intros n G ct dt c1 d1 c2 d2 c3 d3 cr dr len j tg a1 a2 a3 r Bt B1 B2 B3 Br HC HG Hav Hav2.
  assert (Le : forall v c d x, FOPrH n G (FObetaF v c d j x) -> v + 4 <= 122 -> 20 <= v ->
            FOtms_avoid [c; d; x] 20 122 -> FOtms_avoid [c; d; x] 498 499 ->
            FOPrH n G (FOle (FOSucc x) (FOSucc c))).
  { intros v c d x Hb Hv1 Hv2 Hc1 Hc2.
    pose proof (FOPrH_mp _ _ _ _ (FOPrH_beta_le n G v c d j x
                  ltac:(intros w ? ?; apply HG; lia) ltac:(lia) ltac:(avoid_tms)
                  ltac:(avoid_tms)) Hb) as H.
    unfold FOle in H |- *.
    refine (FOPrH_mp _ _ _ _ _ H). apply FOPrH_empty.
    apply FOPrH_intro.
    refine (FOPrH_ex_elim _ _ 498 (FOEq (FOPlus x (FOVar 498)) c) _ _ _ _ _);
      [free_ctx | free_fm | apply FOPrH_last |].
    apply (FOPrH_ex_intro _ _ 498 (FOVar 498)); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_id.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (E : FOPrH n Gc (FOEq c (FOPlus x (FOVar 498)))) by (apply FOPrH_eq_sym; wk_in)
    end.
    fo_lin [(.S .0, c, x .+ #498)]; exact E. }
  unfold FOSTEPDISPATCH.
  apply (FOPrH_bex_intro_t _ _ 20 (FOSucc ct) tg); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | apply (Le 30 ct dt tg Bt); [lia | lia | avoid_tms | avoid_tms]
    | ok_step | ].
  autorewrite with fosubst. subst_avoid_h Hav.
  apply (FOPrH_bex_intro_t _ _ 22 (FOSucc c1) a1); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | apply (Le 34 c1 d1 a1 B1); [lia | lia | avoid_tms | avoid_tms]
    | ok_step | ].
  autorewrite with fosubst. subst_avoid_h Hav.
  apply (FOPrH_bex_intro_t _ _ 24 (FOSucc c2) a2); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | apply (Le 38 c2 d2 a2 B2); [lia | lia | avoid_tms | avoid_tms]
    | ok_step | ].
  autorewrite with fosubst. subst_avoid_h Hav.
  apply (FOPrH_bex_intro_t _ _ 26 (FOSucc c3) a3); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | apply (Le 42 c3 d3 a3 B3); [lia | lia | avoid_tms | avoid_tms]
    | ok_step | ].
  autorewrite with fosubst. subst_avoid_h Hav.
  apply (FOPrH_bex_intro_t _ _ 28 (FOSucc cr) r); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | apply (Le 46 cr dr r Br); [lia | lia | avoid_tms | avoid_tms]
    | ok_step | ].
  autorewrite with fosubst. subst_avoid_h Hav.
  repeat (apply FOPrH_and_intro; [assumption|]).
  exact HC.
Qed.

(** ** Adding a row to a table.

    [FOPrH_text_elim] names the columns of an extension of [T] by fresh
    variables [k] .. [k+9]; [FOPrH_row_add] turns the dispatch clause of
    the new row into validity of the extension, its inclusion of [T],
    and the lookup of the new row. *)

Definition FOtabx (k : nat) (len : FOTerm) : FOtab :=
  mkTab (FOVar k) (FOVar (k + 1)) (FOVar (k + 2)) (FOVar (k + 3)) (FOVar (k + 4))
    (FOVar (k + 5)) (FOVar (k + 6)) (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) len.

Lemma FOPrH_text_elim : forall n G T tg a1 a2 a3 r k C,
  FOctx_avoid G 420 500 -> FOctx_avoid G k (k + 10) ->
  2 <= k -> k + 10 <= 420 ->
  (forall w, k <= w -> w < k + 10 -> FOfree_in w C = false) ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r]) 420 500 ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r]) k (k + 10) ->
  FOPrH n (G ++ [FOTEXT T (FOtabx k (FOSucc (tlen T))) tg a1 a2 a3 r]) C ->
  FOPrH n G C.
Proof.
  intros n G T tg a1 a2 a3 r k C HG HGk Hk Hk' HC Hav Havk H0.
  apply (FOPrH_extend_elim n G (tct T) (tdt T) (tlen T) tg (tct T) k (k + 1) C);
    try (apply HGk; lia); try (apply HC; lia); try lia; try avoid_tms; try assumption.
  apply (FOPrH_extend_elim n _ (tc1 T) (td1 T) (tlen T) a1 (tc1 T) (k + 2) (k + 3) C);
    try (apply HC; lia); try lia; try avoid_tms; try ctx_list; try free_ctx.
  apply (FOPrH_extend_elim n _ (tc2 T) (td2 T) (tlen T) a2 (tc2 T) (k + 4) (k + 5) C);
    try (apply HC; lia); try lia; try avoid_tms; try ctx_list; try free_ctx.
  apply (FOPrH_extend_elim n _ (tc3 T) (td3 T) (tlen T) a3 (tc3 T) (k + 6) (k + 7) C);
    try (apply HC; lia); try lia; try avoid_tms; try ctx_list; try free_ctx.
  apply (FOPrH_extend_elim n _ (tcr T) (tdr T) (tlen T) r (tcr T) (k + 8) (k + 9) C);
    try (apply HC; lia); try lia; try avoid_tms; try ctx_list; try free_ctx.
  refine (FOPrH_cut _ _ (FOTEXT T (FOtabx k (FOSucc (tlen T))) tg a1 a2 a3 r) _ _ _).
  - unfold FOTEXT, FOtabx. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen].
    do 4 (apply FOPrH_and_intro; [wk_in|]). wk_in.
  - refine (FOPrH_weaken n _ _ _ _ H0).
    intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
    + do 6 (apply in_or_app; left). exact HX.
    + apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_row_add : forall n G T T' tg a1 a2 a3 r,
  FOPrH n G (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T)) ->
  FOPrH n G (FOTEXT T T' tg a1 a2 a3 r) -> tlen T' = FOSucc (tlen T) ->
  FOPrH n G (FODISPCASES (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T') tg a1 a2 a3 r) ->
  FOctx_avoid G 18 122 -> FOctx_avoid G 420 500 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 18 122 ->
  FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r]) 400 500 ->
  FOPrH n G (FOTBLVALID 18 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
               (td3 T') (tcr T') (tdr T') (tlen T')) /\
  FOTabMono n G T T'.
Proof.
  intros n G T T' tg a1 a2 a3 r HV HX Hlen HC HG HG2 Hav1 Hav2.
  assert (Hav : FOtms_avoid (FOtab_terms T ++ FOtab_terms T' ++ [tg; a1; a2; a3; r])
                  420 500) by avoid_tms.
  split; [|exact (FOPrH_text_mono n G T T' tg a1 a2 a3 r HX Hlen HG2 Hav)].
  apply (FOPrH_tbl_extend n G T T' tg a1 a2 a3 r HV HX Hlen); try assumption.
  pose proof HX as HX'. text_split HX'.
  apply (FOPrH_dispatch_intro n G _ _ _ _ _ _ _ _ _ _ _ _ tg a1 a2 a3 r);
    [ refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ Xt))); [lia | avoid_tms | avoid_tms]
    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ X1))); [lia | avoid_tms | avoid_tms]
    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ X2))); [lia | avoid_tms | avoid_tms]
    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ X3))); [lia | avoid_tms | avoid_tms]
    | refine (FOPrH_rebase_cf _ _ 488 _ _ _ _ _ _ _ _
                (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ Xr))); [lia | avoid_tms | avoid_tms]
    | exact HC | intros w ? ?; apply HG; lia | avoid_tms | avoid_tms ].
Qed.

(** ** A lookup at another base. *)

Lemma FOPrH_lookup_rebase : forall n G B B' ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  FOPrH n G (FOlookup B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) ->
  2 <= B -> 2 <= B' -> B + 22 <= 420 -> B' + 22 <= 420 ->
  B + 22 <= B' \/ B' + 22 <= B ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; tg; a1; a2; a3; r] B (B + 22) ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; tg; a1; a2; a3; r] B' (B' + 22) ->
  FOPrH n G (FOlookup B' ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r).
Proof.
  intros n G B B' ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r H HB1 HB2 HB3 HB4 HBB
    Hav Hav'.
  refine (FOPrH_mp _ _ _ _ _ H). apply FOPrH_empty.
  unfold FOlookup. rewrite !FOBexC_ltv.
  assert (V : FOtm_avoid (FOVar B') B (B + 22)) by (apply FOtm_avoid_var; lia).
  refine (FOPrH_imp_trans _ _ _ _ _ (FOPrH_thm _ _ _ (FOPr_ex_rename n B B' _ _ _)) _).
  - unfold FOltv. rewrite !FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    + rewrite FOfree_in_FOExists_neq by lia. cbn [FOfree_in]. apply Bool.orb_false_iff.
      split; fr_tm.
    + repeat (apply Bool.orb_false_iff; split; [apply FOfree_in_betaF_not; [lia | fr_tm..]|]).
      apply FOfree_in_betaF_not; [lia | fr_tm..].
  - unfold FOltv.
    repeat (apply FOsubst_ok_and; [first [apply FOsubst_ok_betaF; avoid_tm
                                         | apply FOsubst_ok_ex; [fr_tm | apply FOsubst_ok_eq]]
                                  |]).
    apply FOsubst_ok_betaF; avoid_tm.
  - apply FOPrH_ex_imp; [apply FOfree_ctx_nil|].
    apply (FOPrH_ex_intro _ _ B' (FOVar B')); [apply FOsubst_ok_var_self|].
    rewrite FOsubst_f_id.
    unfold FOltv.
    rewrite !FOsubst_f_and, FOsubst_f_ex_ne by lia.
    rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_succ, FOsubst_t_var_eq',
      FOsubst_t_var_ne by lia.
    rewrite !FOsubst_f_betaF by lia. rewrite !FOsubst_t_var_eq'. subst_avoid_h Hav.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      pose proof (FOPrH_last n [] (FOAnd (FOExists (S B) (FOEq (FOPlus (FOVar B')
                    (FOSucc (FOVar (S B)))) len)) (FOAnd (FObetaF (B + 2) ct dt (FOVar B') tg)
                    (FOAnd (FObetaF (B + 6) c1 d1 (FOVar B') a1)
                    (FOAnd (FObetaF (B + 10) c2 d2 (FOVar B') a2)
                    (FOAnd (FObetaF (B + 14) c3 d3 (FOVar B') a3)
                           (FObetaF (B + 18) cr dr (FOVar B') r))))))) as K
    end.
    cbn [app] in K.
    apply FOPrH_and_intro.
    { refine (FOPrH_mp _ _ _ _ (FOPrH_exeq_rename _ _ (S B) (S B') (FOVar B') len _ _ _ _ _)
                (FOPrH_and_l _ _ _ _ K)); [lia | fr_tm | fr_tm | fr_tm | fr_tm]. }
    apply FOPrH_and_r in K.
    do 4 (apply FOPrH_and_intro;
          [ refine (FOPrH_rebase_cf _ _ _ _ _ _ _ _ _ _ _ (FOPrH_and_l _ _ _ _ K));
            [lia | avoid_tms | avoid_tms] | apply FOPrH_and_r in K ]).
    refine (FOPrH_rebase_cf _ _ _ _ _ _ _ _ _ _ _ K); [lia | avoid_tms | avoid_tms].
Qed.

(** ** Order facts for the step witnesses. *)

Lemma FOPrH_le_refl : forall n G a, FOtm_avoid a 498 499 -> FOPrH n G (FOle a a).
Proof.
  intros n G a Ha. unfold FOle.
  apply (FOPrH_ex_intro _ _ 498 FOZero); [cbn [FOsubst_ok]; reflexivity|].
  rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_var_eq'.
  rewrite (FOsubst_t_not_in a 498 _ (Ha 498 ltac:(lia) ltac:(lia))).
  apply FOPrH_Q_plus_zero.
Qed.

Lemma FOPrH_cpair_lt : forall n G a b c,
  FOPrH n G (FOcpairF (FOSucc a) b c) ->
  FOtms_avoid [a; b; c] 420 500 ->
  FOPrH n G (FOle (FOSucc b) c).
Proof.
  intros n G a b c H Hav.
  refine (FOPrH_ctxfree n G _ _ _ H).
  destruct (FOPrH_cpair_le_cf n [FOcpairF (FOSucc a) b c] (FOSucc a) b c ltac:(avoid_tms)
              (FOPrH_assum n [FOcpairF (FOSucc a) b c] (FOcpairF (FOSucc a) b c)
                 (or_introl eq_refl))) as [_ Hb].
  unfold FOle in Hb.
  refine (FOPrH_ex_elim n _ 498 (FOEq (FOPlus b (FOVar 498)) c) _ _ _ Hb _);
    [free_ctx | free_fm |].
  apply (FOPrH_cases_zs _ _ (FOVar 498) 499 _); [lia | fr_tm | free_ctx | free_fm | fr_tm | |].
  - apply FOPrH_efq.
    apply (FOPrH_Q_succ_nonzero _ _ (FOPlus (FOMult (FOPlus (FOSucc a) b) (FOPlus (FOSucc a) b))
                                         (FOPlus a b))).
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (Z : FOPrH n Gc (FOEq FOZero (FOVar 498))) by (apply FOPrH_eq_sym; wk_in)
    end.
    unfold FOcpairF in *.
    fo_lin [(.S .0, c .+ c,
             FOPlus (FOMult (FOPlus (FOSucc a) b) (FOSucc (FOPlus (FOSucc a) b))) (b .+ b));
            (.S (.S .0), b .+ #498, c); (.S (.S .0), .0, #498)]; exact Z.
  - lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (E : FOPrH n Gc (FOEq c (FOPlus b (FOVar 498)))) by (apply FOPrH_eq_sym; wk_in)
    end.
    unfold FOle. apply (FOPrH_ex_intro _ _ 498 (FOVar 499)); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_eq, FOsubst_t_plus, !FOsubst_t_succ, FOsubst_t_var_eq'.
    subst_avoid_h Hav.
    fo_lin [(.S .0, c, b .+ #498); (.S .0, #498, .S #499)]; exact E.
Qed.

(** ** The step clauses of the numeral rows.

    Tag [5] computes the code of a numeral, tag [0] the occurrence of a
    variable in a term and tag [2] the substitution into a term; on the
    code [1] of [0] and the code [cpair 2 t] of a successor each clause
    holds from the row of [t]. *)

Ltac ok_row :=
  lazymatch goal with
  | |- FOsubst_ok _ ?s _ = true =>
      let V := fresh "V" in assert (V : FOtm_avoid s 20 122) by avoid_tm;
      solve [auto 100 with fook]
  end.

Ltac row_bex s :=
  lazymatch goal with
  | |- FOPrH _ _ (FOBexC ?x ?t _) =>
      apply (FOPrH_bex_intro_t _ _ x t s);
      [lia | lia | avoid_tm | avoid_tm | avoid_tm | avoid_tm | | ok_row |
       autorewrite with fosubst; subst_avoid_h_all ]
  end
with subst_avoid_h_all :=
  repeat match goal with
         | H : FOtms_avoid _ _ _ |- _ => progress subst_avoid_h H
         end.

Section NumRows.
Variables (n : nat) (G : list FOFormula) (ct dt c1 d1 c2 d2 c3 d3 cr dr len : FOTerm).

Lemma FOPrH_case5_zero : forall r,
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero r) ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 5) FOZero FOZero
               FOZero r).
Proof.
  intros r H. unfold FODISPCASES. do 5 apply FOPrH_or_intro_r.
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  unfold FOSTEP5. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_refl | exact H].
Qed.

Lemma FOPrH_case5_succ : forall x r r',
  FOPrH n G (FOlookup 54 ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 5) x FOZero FOZero r) ->
  FOPrH n G (FOcpairF (FOnumeral 2) r r') ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; x; r; r'] 20 122 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; x; r; r'] 420 500 ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 5) (FOSucc x) FOZero
               FOZero r').
Proof.
  intros x r r' HL HC Hav Hav2. unfold FODISPCASES. do 5 apply FOPrH_or_intro_r.
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  unfold FOSTEP5. apply FOPrH_or_intro_r.
  row_bex x; [apply FOPrH_le_refl; avoid_tm|].
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  row_bex r; [exact (FOPrH_cpair_lt _ _ _ _ _ HC ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact HL | exact HC].
Qed.

Lemma FOPrH_case0_zero : forall w tc,
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero tc) ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len FOZero w tc FOZero FOZero).
Proof.
  intros w tc H. unfold FODISPCASES. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  unfold FOSTEP0. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [exact H | apply FOPrH_refl].
Qed.

Lemma FOPrH_case0_succ : forall w t tc r,
  FOPrH n G (FOlookup 52 ct dt c1 d1 c2 d2 c3 d3 cr dr len FOZero w t FOZero r) ->
  FOPrH n G (FOcpairF (FOnumeral 2) t tc) ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; w; t; tc; r] 20 122 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; w; t; tc; r] 420 500 ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len FOZero w tc FOZero r).
Proof.
  intros w t tc r HL HC Hav Hav2. unfold FODISPCASES. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  unfold FOSTEP0. do 2 apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  row_bex t.
  { destruct (FOPrH_cpair_le_cf n G (FOnumeral 2) t tc ltac:(avoid_tms) HC) as [_ Hle].
    unfold FOle in Hle |- *.
    refine (FOPrH_mp _ _ _ _ _ Hle). apply FOPrH_empty. apply FOPrH_intro.
    refine (FOPrH_ex_elim _ _ 498 (FOEq (FOPlus t (FOVar 498)) tc) _ _ _ _ _);
      [free_ctx | free_fm | apply FOPrH_last |].
    apply (FOPrH_ex_intro _ _ 498 (FOVar 498)); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_id.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (E : FOPrH n Gc (FOEq tc (FOPlus t (FOVar 498)))) by (apply FOPrH_eq_sym; wk_in)
    end.
    fo_lin [(.S .0, tc, t .+ #498)]; exact E. }
  apply FOPrH_and_intro; [exact HC | exact HL].
Qed.

Lemma FOPrH_case2_zero : forall x sc tc,
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero tc) ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 2) x sc tc tc).
Proof.
  intros x sc tc H. unfold FODISPCASES. do 2 apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  unfold FOSTEP2. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [exact H | apply FOPrH_refl].
Qed.

Lemma FOPrH_case2_succ : forall x sc t t' tc r,
  FOPrH n G (FOlookup 54 ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 2) x sc t t') ->
  FOPrH n G (FOcpairF (FOnumeral 2) t tc) -> FOPrH n G (FOcpairF (FOnumeral 2) t' r) ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; x; sc; t; t'; tc; r] 20 122 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; x; sc; t; t'; tc; r] 420 500 ->
  FOPrH n G (FODISPCASES ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 2) x sc tc r).
Proof.
  intros x sc t t' tc r HL HC HC' Hav Hav2. unfold FODISPCASES.
  do 2 apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_refl|].
  unfold FOSTEP2. do 2 apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  row_bex t.
  { destruct (FOPrH_cpair_le_cf n G (FOnumeral 2) t tc ltac:(avoid_tms) HC) as [_ Hle].
    unfold FOle in Hle |- *.
    refine (FOPrH_mp _ _ _ _ _ Hle). apply FOPrH_empty. apply FOPrH_intro.
    refine (FOPrH_ex_elim _ _ 498 (FOEq (FOPlus t (FOVar 498)) tc) _ _ _ _ _);
      [free_ctx | free_fm | apply FOPrH_last |].
    apply (FOPrH_ex_intro _ _ 498 (FOVar 498)); [cbn [FOsubst_ok]; reflexivity|].
    rewrite FOsubst_f_id.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (E : FOPrH n Gc (FOEq tc (FOPlus t (FOVar 498)))) by (apply FOPrH_eq_sym; wk_in)
    end.
    fo_lin [(.S .0, tc, t .+ #498)]; exact E. }
  apply FOPrH_and_intro; [exact HC|].
  row_bex t'; [exact (FOPrH_cpair_lt _ _ _ _ _ HC' ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact HL | exact HC'].
Qed.

End NumRows.

(** ** A new row added to a valid table.

    The dispatch clause of the new row is supplied for every extension
    of [T]; the continuation receives the extension [T'] at the
    variables [k] .. [k+9], its validity, its inclusion of [T], and the
    lookup of the new row at base [28]. *)

Definition FOTBLNEW (T T' : FOtab) (tg a1 a2 a3 r : FOTerm) : FOFormula :=
  FOAnd (FOTBLVALID 18 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
           (td3 T') (tcr T') (tdr T') (tlen T'))
  (FOAnd (FOINCL T T')
         (FOlookup 28 (tct T') (tdt T') (tc1 T') (td1 T') (tc2 T') (td2 T') (tc3 T')
            (td3 T') (tcr T') (tdr T') (tlen T') tg a1 a2 a3 r)).

Lemma FOfree_in_INCL_any : forall w T T',
  2 <= w -> FOtms_avoid (FOtab_terms T ++ FOtab_terms T') w (S w) ->
  FOfree_in w (FOINCL T T') = false.
Proof.
  intros w T T' Hw Hav. unfold FOINCL, FOROWMAP.
  destruct (Nat.eq_dec 460 w) as [<-|H0]; [apply FOfree_in_all_self|].
  rewrite FOfree_in_all_ne by exact H0. rewrite FOfree_in_impl.
  apply Bool.orb_false_iff. split.
  - destruct (Nat.eq_dec 461 w) as [<-|H1]; [apply FOfree_in_ex_self|].
    rewrite FOfree_in_FOExists_neq by exact H1. free_fm.
  - destruct (Nat.eq_dec 462 w) as [<-|H2]; [apply FOfree_in_ex_self|].
    rewrite FOfree_in_FOExists_neq by exact H2.
    rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    + destruct (Nat.eq_dec 463 w) as [<-|H3]; [apply FOfree_in_ex_self|].
      rewrite FOfree_in_FOExists_neq by exact H3. free_fm.
    + free_fm.
Qed.

Ltac free_fm ::=
  lazymatch goal with
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

Lemma FOPrH_row_new : forall n G T tg a1 a2 a3 r k C,
  FOPrH n G (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T)) ->
  (forall G', (forall X, In X G -> In X G') ->
     FOctx_avoid G' 18 122 -> FOctx_avoid G' 420 500 ->
     FOTabMono n G' T (FOtabx k (FOSucc (tlen T))) ->
     FOPrH n G' (FODISPCASES (FOVar k) (FOVar (k + 1)) (FOVar (k + 2)) (FOVar (k + 3))
                   (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6)) (FOVar (k + 7))
                   (FOVar (k + 8)) (FOVar (k + 9)) (FOSucc (tlen T)) tg a1 a2 a3 r)) ->
  FOctx_avoid G 18 122 -> FOctx_avoid G 420 500 -> FOctx_avoid G k (k + 10) ->
  122 <= k -> k + 10 <= 400 ->
  (forall w, k <= w -> w < k + 10 -> FOfree_in w C = false) ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r]) 18 122 ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r]) 400 500 ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r]) k (k + 10) ->
  FOPrH n (G ++ [FOTBLNEW T (FOtabx k (FOSucc (tlen T))) tg a1 a2 a3 r]) C ->
  FOPrH n G C.
Proof.
  intros n G T tg a1 a2 a3 r k C HV HD HG1 HG2 HGk Hk1 Hk2 HC Hav1 Hav2 Hav3 H0.
  apply (FOPrH_text_elim n G T tg a1 a2 a3 r k C);
    [exact HG2 | exact HGk | lia | lia | exact HC | avoid_tms | avoid_tms |].
  assert (HavA : FOtms_avoid (FOtab_terms T ++ FOtab_terms (FOtabx k (FOSucc (tlen T))) ++
                              [tg; a1; a2; a3; r]) 18 122).
  { unfold FOtabx, FOtab_terms at 2. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen].
    avoid_tms. }
  assert (HavB : FOtms_avoid (FOtab_terms T ++ FOtab_terms (FOtabx k (FOSucc (tlen T))) ++
                              [tg; a1; a2; a3; r]) 400 500).
  { unfold FOtabx, FOtab_terms at 2. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen].
    avoid_tms. }
  assert (HavC : FOtms_avoid (FOtab_terms T ++ FOtab_terms (FOtabx k (FOSucc (tlen T))) ++
                              [tg; a1; a2; a3; r]) 420 500) by avoid_tms.
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (HX : FOPrH n G1 (FOTEXT T (FOtabx k (FOSucc (tlen T))) tg a1 a2 a3 r))
      by apply FOPrH_last;
    assert (HV1 : FOPrH n G1 (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T)
                               (tc3 T) (td3 T) (tcr T) (tdr T) (tlen T))) by wk HV;
    assert (C1 : FOctx_avoid G1 18 122);
    [ intros w ? ?; apply FOfree_ctx_app_inv; [apply HG1; lia|];
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil];
      unfold FOTEXT, FOtabx; cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen]; free_fm |];
    assert (C2 : FOctx_avoid G1 420 500);
    [ intros w ? ?; apply FOfree_ctx_app_inv; [apply HG2; lia|];
      apply FOfree_ctx_cons; [|apply FOfree_ctx_nil];
      unfold FOTEXT, FOtabx; cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen]; free_fm |]
  end.
  pose proof (FOPrH_text_mono n _ T _ tg a1 a2 a3 r HX eq_refl C2 HavC) as Hm.
  pose proof (HD _ (fun X HX => in_or_app _ _ _ (or_introl HX)) C1 C2 Hm) as HDC.
  destruct (FOPrH_row_add n _ T _ tg a1 a2 a3 r HV1 HX eq_refl HDC C1 C2 HavA HavB)
    as [HV' _].
  pose proof (FOPrH_text_lookup n _ 28 T _ tg a1 a2 a3 r HX eq_refl ltac:(lia) ltac:(lia)
                ltac:(avoid_tms) HavC) as HL.
  destruct Hm as [HI _].
  refine (FOPrH_cut _ _ (FOTBLNEW T (FOtabx k (FOSucc (tlen T))) tg a1 a2 a3 r) _ _ _).
  - unfold FOTBLNEW. apply FOPrH_and_intro; [exact HV'|].
    apply FOPrH_and_intro; [exact HI | exact HL].
  - refine (FOPrH_weaken n _ _ _ _ H0).
    intros X HX'. apply in_app_or in HX'. destruct HX' as [HX'|[<-|[]]].
    + do 2 (apply in_or_app; left). exact HX'.
    + apply in_or_app. right. left. reflexivity.
Qed.

(** ** Some valid table has a given row.

    [FOTBLEX tg a1 a2 a3 r]: the table sits at the variables [2]
    through [12], the row is looked up at base [28]. *)

Definition FOTBLEX (tg a1 a2 a3 r : FOTerm) : FOFormula :=
  FOExists 2 (FOExists 3 (FOExists 4 (FOExists 5 (FOExists 6 (FOExists 7
  (FOExists 8 (FOExists 9 (FOExists 10 (FOExists 11 (FOExists 12
    (FOAnd (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12))
       (FOlookup 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
          (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
          tg a1 a2 a3 r)))))))))))).

Ltac tblex_intro_step t Hav :=
  lazymatch goal with
  | |- FOPrH _ _ (FOExists ?z ?A) =>
      apply (FOPrH_ex_intro _ _ z t);
      [ let V := fresh "V" in assert (V : FOtm_avoid t 2 122) by avoid_tm;
        solve [auto 100 with fook]
      | autorewrite with fosubst; rewrite ?FOsubst_t_var_eq'; subst_avoid_h Hav ]
  end.

Lemma FOPrH_tblex_intro : forall n G T tg a1 a2 a3 r,
  FOPrH n G (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T)) ->
  FOPrH n G (FOlookup 28 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) tg a1 a2 a3 r) ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r]) 2 122 ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r).
Proof.
  intros n G T tg a1 a2 a3 r HV HL Hav.
  destruct T as [ct dt c1 d1 c2 d2 c3 d3 cr dr len].
  unfold FOtab_terms in Hav. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app] in *.
  unfold FOTBLEX.
  tblex_intro_step ct Hav. tblex_intro_step dt Hav. tblex_intro_step c1 Hav.
  tblex_intro_step d1 Hav. tblex_intro_step c2 Hav. tblex_intro_step d2 Hav.
  tblex_intro_step c3 Hav. tblex_intro_step d3 Hav. tblex_intro_step cr Hav.
  tblex_intro_step dr Hav. tblex_intro_step len Hav.
  apply FOPrH_and_intro; assumption.
Qed.

Ltac tblex_rename_step Hr w :=
  lazymatch goal with
  | |- FOPrH _ _ (FOImplF (FOExists ?z ?A) _) =>
      apply (FOPrH_imp_exl_rename _ _ z w A);
      [ solve [match goal with HG : FOctx_avoid _ _ _ |- _ => apply HG; lia end]
      | solve [match goal with HC : forall w, _ -> _ -> FOfree_in w _ = false |- _ =>
                                     apply HC; lia end]
      | repeat rewrite FOfree_in_FOExists_neq by lia; free_fm
      | let V := fresh "V" in assert (V : FOtm_avoid (FOVar w) 2 122) by avoid_tm;
        solve [auto 100 with fook]
      | autorewrite with fosubst; rewrite ?FOsubst_t_var_eq'; subst_avoid_h Hr ]
  end.

Lemma FOPrH_tblex_elim : forall n G tg a1 a2 a3 r k C,
  122 <= k -> k + 11 <= 420 ->
  FOctx_avoid G k (k + 11) ->
  (forall w, k <= w -> w < k + 11 -> FOfree_in w C = false) ->
  FOtms_avoid [tg; a1; a2; a3; r] 2 122 -> FOtms_avoid [tg; a1; a2; a3; r] k (k + 11) ->
  FOPrH n (G ++ [FOAnd (FOTBLVALID 18 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10)))
                       (FOlookup 28 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10))
                          tg a1 a2 a3 r)]) C ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r .-> C).
Proof.
  intros n G tg a1 a2 a3 r k C Hk Hk' HG HC Hr Hrk H.
  unfold FOTBLEX.
  tblex_rename_step Hr k. tblex_rename_step Hr (k + 1). tblex_rename_step Hr (k + 2).
  tblex_rename_step Hr (k + 3). tblex_rename_step Hr (k + 4). tblex_rename_step Hr (k + 5).
  tblex_rename_step Hr (k + 6). tblex_rename_step Hr (k + 7). tblex_rename_step Hr (k + 8).
  tblex_rename_step Hr (k + 9). tblex_rename_step Hr (k + 10).
  apply FOPrH_intro. exact H.
Qed.

(** ** The empty table. *)

Definition FOtab0 : FOtab :=
  mkTab FOZero FOZero FOZero FOZero FOZero FOZero FOZero FOZero FOZero FOZero FOZero.

Lemma FOPrH_tbl_empty : forall n G,
  FOfree_ctx 18 G -> FOfree_ctx 19 G ->
  FOPrH n G (FOTBLVALID 18 (tct FOtab0) (tdt FOtab0) (tc1 FOtab0) (td1 FOtab0) (tc2 FOtab0)
               (td2 FOtab0) (tc3 FOtab0) (td3 FOtab0) (tcr FOtab0) (tdr FOtab0)
               (tlen FOtab0)).
Proof.
  intros n G HG HG'. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen FOtab0].
  unfold FOTBLVALID. rewrite FOBallC_ltv. apply FOPrH_all_intro; [exact HG|].
  apply FOPrH_intro. apply FOPrH_efq. unfold FOltv.
  refine (FOPrH_ex_elim _ _ 19 (FOEq (FOPlus (FOVar 18) (FOSucc (FOVar 19))) FOZero)
            _ _ _ _ _); [| reflexivity | apply FOPrH_last |].
  { apply FOfree_ctx_app_inv; [exact HG'|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. apply FOfree_in_ex_self. }
  apply (FOPrH_Q_succ_nonzero _ _ (FOPlus (FOVar 18) (FOVar 19))).
  apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar 18) (FOSucc (FOVar 19))));
    [apply FOPrH_eq_sym; apply FOPrH_Q_plus_succ | apply FOPrH_last].
Qed.

Lemma FOPrH_cpair_one : forall n G, FOPrH n G (FOcpairF (FOnumeral 1) FOZero (FOnumeral 1)).
Proof. intros n G. unfold FOcpairF. cbn [FOnumeral]. apply FOPrH_ring. fo_ring. Qed.

(** ** Rows of the numerals.

    For each numeral code, some valid table has its tag-[5] row, its
    tag-[2] row for every substitution, and its tag-[0] row for every
    variable; the successor rows extend a table holding the row of the
    predecessor. *)

Lemma FOfree_in_TBLEX_any : forall w tg a1 a2 a3 r,
  2 <= w -> FOtms_avoid [tg; a1; a2; a3; r] w (S w) ->
  FOfree_in w (FOTBLEX tg a1 a2 a3 r) = false.
Proof.
  intros w tg a1 a2 a3 r Hw Hav. unfold FOTBLEX.
  repeat match goal with
         | |- FOfree_in _ (FOExists ?y _) = false =>
             destruct (Nat.eq_dec y w) as [<-|?];
             [apply FOfree_in_ex_self | rewrite FOfree_in_FOExists_neq by assumption]
         end.
  rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
  - free_by FOTBLVALID_free.
  - free_by FOlookup_free.
Qed.

Ltac free_fm ::=
  lazymatch goal with
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

Ltac tab_avoid ::=
  try unfold FOtab_terms; try unfold FOtabv; try unfold FOtabx; try unfold FOtab0;
  cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app]; avoid_tms.

Ltac tab_side :=
  lazymatch goal with
  | |- FOctx_avoid _ _ _ => ctx_list
  | |- FOtms_avoid _ _ _ => tab_avoid
  | |- FOfree_ctx _ _ => free_ctx
  | |- FOfree_in _ _ = false => free_fm
  | |- forall w, _ -> _ -> FOfree_in w _ = false =>
      let w := fresh "w" in intros w ? ?; free_fm
  | |- _ => nat_fast
  end.

Lemma FOPrH_tab_base : forall n G tg a1 a2 a3 r,
  FOctx_avoid G 2 500 -> FOtms_avoid [tg; a1; a2; a3; r] 2 500 ->
  FOPrH n G (FODISPCASES (FOVar 141) (FOVar 142) (FOVar 143) (FOVar 144) (FOVar 145)
               (FOVar 146) (FOVar 147) (FOVar 148) (FOVar 149) (FOVar 150)
               (FOSucc FOZero) tg a1 a2 a3 r) ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r).
Proof.
  intros n G tg a1 a2 a3 r HG Hav HD.
  apply (FOPrH_row_new n G FOtab0 tg a1 a2 a3 r 141 _);
    [ apply FOPrH_tbl_empty; apply HG; lia
    | intros G' Hinc _ _ _; exact (FOPrH_weaken n G G' _ Hinc HD)
    | tab_side .. |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (N : FOPrH n Gc (FOTBLNEW FOtab0 (FOtabx 141 (FOSucc (tlen FOtab0)))
                              tg a1 a2 a3 r)) by apply FOPrH_last
  end.
  unfold FOTBLNEW in N.
  apply (FOPrH_tblex_intro n _ (FOtabx 141 (FOSucc (tlen FOtab0))) tg a1 a2 a3 r
           (FOPrH_and_l _ _ _ _ N) (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ N))).
  tab_side.
Qed.

Lemma FOPrH_tab_step : forall n G tg a1 a2 a3 r tg' a1' a2' a3' r',
  FOctx_avoid G 2 500 ->
  FOtms_avoid [tg; a1; a2; a3; r; tg'; a1'; a2'; a3'; r'] 2 500 ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r) ->
  (forall G', (forall X, In X G -> In X G') ->
     FOPrH n G' (FOlookup 28 (FOVar 141) (FOVar 142) (FOVar 143) (FOVar 144) (FOVar 145)
                   (FOVar 146) (FOVar 147) (FOVar 148) (FOVar 149) (FOVar 150)
                   (FOSucc (FOVar 140)) tg a1 a2 a3 r) ->
     FOPrH n G' (FODISPCASES (FOVar 141) (FOVar 142) (FOVar 143) (FOVar 144) (FOVar 145)
                   (FOVar 146) (FOVar 147) (FOVar 148) (FOVar 149) (FOVar 150)
                   (FOSucc (FOVar 140)) tg' a1' a2' a3' r')) ->
  FOPrH n G (FOTBLEX tg' a1' a2' a3' r').
Proof.
  intros n G tg a1 a2 a3 r tg' a1' a2' a3' r' HG Hav HE HP.
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n G tg a1 a2 a3 r 130 _ _ _ _ _ _ _ _) HE);
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  lazymatch goal with |- FOPrH _ ?G1 _ =>
    assert (K : FOPrH n G1 (FOAnd (FOTBLVALID 18 (tct (FOtabv 130)) (tdt (FOtabv 130))
                   (tc1 (FOtabv 130)) (td1 (FOtabv 130)) (tc2 (FOtabv 130)) (td2 (FOtabv 130))
                   (tc3 (FOtabv 130)) (td3 (FOtabv 130)) (tcr (FOtabv 130)) (tdr (FOtabv 130))
                   (tlen (FOtabv 130)))
                 (FOlookup 28 (tct (FOtabv 130)) (tdt (FOtabv 130))
                   (tc1 (FOtabv 130)) (td1 (FOtabv 130)) (tc2 (FOtabv 130)) (td2 (FOtabv 130))
                   (tc3 (FOtabv 130)) (td3 (FOtabv 130)) (tcr (FOtabv 130)) (tdr (FOtabv 130))
                   (tlen (FOtabv 130)) tg a1 a2 a3 r))) by apply FOPrH_last;
    assert (HGinc : forall X, In X G -> In X G1)
      by (intros X HX; apply in_or_app; left; exact HX)
  end.
  apply (FOPrH_row_new n _ (FOtabv 130) tg' a1' a2' a3' r' 141 _);
    [ exact (FOPrH_and_l _ _ _ _ K)
    | intros G' Hinc HA1 HA2 Hm;
      refine (HP G' (fun X HX => Hinc X (HGinc X HX)) _);
      refine (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n G' 28 (FOtabv 130) _ tg a1 a2 a3 r Hm
                                  ltac:(lia) _ _ _ _)
                (FOPrH_weaken n _ G' _ Hinc (FOPrH_and_r _ _ _ _ K)));
      [ intros w ? ?; apply HA1; lia
      | exact HA2
      | tab_side | tab_side ]
    | tab_side .. |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (N : FOPrH n Gc (FOTBLNEW (FOtabv 130) (FOtabx 141 (FOSucc (tlen (FOtabv 130))))
                              tg' a1' a2' a3' r')) by apply FOPrH_last
  end.
  unfold FOTBLNEW in N.
  apply (FOPrH_tblex_intro n _ (FOtabx 141 (FOSucc (tlen (FOtabv 130)))) tg' a1' a2' a3' r'
           (FOPrH_and_l _ _ _ _ N) (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ N))).
  tab_side.
Qed.

(** ** Substitution at a variable outside a builder's binders. *)

Lemma FOsubst_ok_not_free : forall A x s, FOfree_in x A = false -> FOsubst_ok x s A = true.
Proof.
  induction A as [a b | | B IHB C IHC | y B IHB | y B IHB]; intros x s H; cbn in *.
  - reflexivity.
  - reflexivity.
  - apply Bool.orb_false_iff in H. destruct H as [H1 H2].
    rewrite (IHB x s H1), (IHC x s H2). reflexivity.
  - destruct (Nat.eqb y x); [reflexivity|]. rewrite H. reflexivity.
  - destruct (Nat.eqb y x); [reflexivity|]. rewrite H. reflexivity.
Qed.

Lemma FOsubst_f_bex_ne : forall x s v t A, x <> v -> x <> S v ->
  FOsubst_f x s (FOBexC v t A) = FOBexC v (FOsubst_t x s t) (FOsubst_f x s A).
Proof.
  intros x s v t A H1 H2. unfold FOBexC, FOAnd, FONeg. cbn [FOsubst_f FOsubst_t].
  nat_eqb_simpl. reflexivity.
Qed.

Lemma FOsubst_f_betaF_ne : forall x s v c d i y, x < v \/ v + 4 <= x ->
  FOsubst_f x s (FObetaF v c d i y) =
  FObetaF v (FOsubst_t x s c) (FOsubst_t x s d) (FOsubst_t x s i) (FOsubst_t x s y).
Proof.
  intros x s v c d i y H. unfold FObetaF.
  rewrite FOsubst_f_bex_ne by lia. rewrite FOsubst_f_and, FOsubst_f_eq.
  rewrite FOsubst_f_bex_ne by lia. rewrite FOsubst_f_eq.
  rewrite !FOsubst_t_plus, !FOsubst_t_mult, !FOsubst_t_succ, !FOsubst_t_var_ne by lia.
  reflexivity.
Qed.

Lemma FOsubst_f_lookup_ne : forall x s B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  x < B \/ B + 22 <= x ->
  FOsubst_f x s (FOlookup B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) =
  FOlookup B (FOsubst_t x s ct) (FOsubst_t x s dt) (FOsubst_t x s c1) (FOsubst_t x s d1)
    (FOsubst_t x s c2) (FOsubst_t x s d2) (FOsubst_t x s c3) (FOsubst_t x s d3)
    (FOsubst_t x s cr) (FOsubst_t x s dr) (FOsubst_t x s len)
    (FOsubst_t x s tg) (FOsubst_t x s a1) (FOsubst_t x s a2) (FOsubst_t x s a3)
    (FOsubst_t x s r).
Proof.
  intros. unfold FOlookup.
  rewrite FOsubst_f_bex_ne by lia. rewrite !FOsubst_f_and.
  rewrite !FOsubst_f_betaF_ne by lia. rewrite FOsubst_t_var_ne by lia. reflexivity.
Qed.

Lemma FOsubst_f_TBLEX : forall x s tg a1 a2 a3 r, 13 <= x -> x < 28 \/ 50 <= x ->
  FOsubst_f x s (FOTBLEX tg a1 a2 a3 r) =
  FOTBLEX (FOsubst_t x s tg) (FOsubst_t x s a1) (FOsubst_t x s a2) (FOsubst_t x s a3)
    (FOsubst_t x s r).
Proof.
  intros x s tg a1 a2 a3 r H1 H2. unfold FOTBLEX.
  rewrite !FOsubst_f_ex_ne by lia. rewrite FOsubst_f_and.
  rewrite (FOsubst_f_not_free (FOTBLVALID 18 _ _ _ _ _ _ _ _ _ _ _) x s).
  - rewrite FOsubst_f_lookup_ne by lia. rewrite !FOsubst_t_var_ne by lia. reflexivity.
  - destruct (FOfree_in x (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5)
                             (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11)
                             (FOVar 12))) eqn:E; [exfalso|reflexivity].
    apply FOTBLVALID_free in E. cbn [FOin_tm] in E.
    repeat match type of E with
           | _ \/ _ => destruct E as [E|E]; [apply Nat.eqb_eq in E; lia|]
           end.
    lia.
Qed.

Lemma FOsubst_ok_TBLEX : forall x s tg a1 a2 a3 r, 13 <= x ->
  FOtm_avoid s 2 50 -> FOsubst_ok x s (FOTBLEX tg a1 a2 a3 r) = true.
Proof.
  intros x s tg a1 a2 a3 r Hx V. unfold FOTBLEX.
  repeat (apply FOsubst_ok_ex; [apply V; lia|]).
  apply FOsubst_ok_and.
  - apply FOsubst_ok_not_free.
    destruct (FOfree_in x (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5)
                             (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11)
                             (FOVar 12))) eqn:E; [exfalso|reflexivity].
    apply FOTBLVALID_free in E. cbn [FOin_tm] in E.
    repeat match type of E with
           | _ \/ _ => destruct E as [E|E]; [apply Nat.eqb_eq in E; lia|]
           end.
    lia.
  - apply FOsubst_ok_lookup. intros w ? ?. apply V; lia.
Qed.

(** ** The rows of each numeral. *)

Lemma FOPrH_num5_zero : forall n G, FOctx_avoid G 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 5) FOZero FOZero FOZero (FOnumeral 1)).
Proof.
  intros n G HG. apply FOPrH_tab_base; [exact HG | tab_side |].
  apply FOPrH_case5_zero. apply FOPrH_cpair_one.
Qed.

Lemma FOPrH_num5_succ : forall n G x m m',
  FOctx_avoid G 2 500 -> FOtms_avoid [x; m; m'] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 5) x FOZero FOZero m) ->
  FOPrH n G (FOcpairF (FOnumeral 2) m m') ->
  FOPrH n G (FOTBLEX (FOnumeral 5) (FOSucc x) FOZero FOZero m').
Proof.
  intros n G x m m' HG Hav HE HC.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  apply (FOPrH_case5_succ n G' _ _ _ _ _ _ _ _ _ _ _ x m m');
    [ apply (FOPrH_lookup_rebase _ _ 28 54);
      [exact HL | lia | lia | lia | lia | lia | tab_side | tab_side]
    | exact (FOPrH_weaken n G G' _ Hinc HC) | tab_side | tab_side ].
Qed.

Lemma FOPrH_num2_zero : forall n G v s, FOctx_avoid G 2 500 -> FOtms_avoid [v; s] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) v s (FOnumeral 1) (FOnumeral 1)).
Proof.
  intros n G v s HG Hav. apply FOPrH_tab_base; [exact HG | tab_side |].
  apply FOPrH_case2_zero. apply FOPrH_cpair_one.
Qed.

Lemma FOPrH_num2_succ : forall n G v s m m',
  FOctx_avoid G 2 500 -> FOtms_avoid [v; s; m; m'] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 2) v s m m) ->
  FOPrH n G (FOcpairF (FOnumeral 2) m m') ->
  FOPrH n G (FOTBLEX (FOnumeral 2) v s m' m').
Proof.
  intros n G v s m m' HG Hav HE HC.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  pose proof (FOPrH_weaken n G G' _ Hinc HC) as HC'.
  apply (FOPrH_case2_succ n G' _ _ _ _ _ _ _ _ _ _ _ v s m m m' m');
    [ apply (FOPrH_lookup_rebase _ _ 28 54);
      [exact HL | lia | lia | lia | lia | lia | tab_side | tab_side]
    | exact HC' | exact HC' | tab_side | tab_side ].
Qed.

Lemma FOPrH_num0_zero : forall n G y, FOctx_avoid G 2 500 -> FOtms_avoid [y] 2 500 ->
  FOPrH n G (FOTBLEX FOZero y (FOnumeral 1) FOZero FOZero).
Proof.
  intros n G y HG Hav. apply FOPrH_tab_base; [exact HG | tab_side |].
  apply FOPrH_case0_zero. apply FOPrH_cpair_one.
Qed.

Lemma FOPrH_num0_succ : forall n G y m m',
  FOctx_avoid G 2 500 -> FOtms_avoid [y; m; m'] 2 500 ->
  FOPrH n G (FOTBLEX FOZero y m FOZero FOZero) ->
  FOPrH n G (FOcpairF (FOnumeral 2) m m') ->
  FOPrH n G (FOTBLEX FOZero y m' FOZero FOZero).
Proof.
  intros n G y m m' HG Hav HE HC.
  refine (FOPrH_tab_step n G _ _ _ _ _ _ _ _ _ _ HG _ HE _); [tab_side|].
  intros G' Hinc HL.
  apply (FOPrH_case0_succ n G' _ _ _ _ _ _ _ _ _ _ _ y m m' FOZero);
    [ apply (FOPrH_lookup_rebase _ _ 28 52);
      [exact HL | lia | lia | lia | lia | lia | tab_side | tab_side]
    | exact (FOPrH_weaken n G G' _ Hinc HC) | tab_side | tab_side ].
Qed.

Lemma FOPrH_cpair_elim_hi : forall n G a b w C,
  FOctx_avoid G 420 500 ->
  FOtms_avoid [a; b] 420 500 ->
  500 <= w ->
  FOfree_ctx w G -> FOfree_in w C = false ->
  FOtms_avoid [a; b] w (S w) ->
  FOPrH n (G ++ [FOcpairF a b (FOVar w)]) C ->
  FOPrH n G C.
Proof.
  intros n G a b w C HG Hav Hw HGw HCw Hav1 H0.
  pose proof (FOPrH_thm n G _ (FOPr_cpair_total n)) as H.
  assert (V1 : FOtm_avoid a 420 500) by avoid_tm.
  assert (V2 : FOtm_avoid b 420 500) by avoid_tm.
  fo_inst_g H a V1 Hav. fo_inst_g H b V2 Hav.
  exe_named H w.
  subst_goal Hav.
  exact H0.
Qed.

(** ** Every number has a numeral code with its rows.

    [FONUMR x m]: [m] is the tag-[5] row value at [x], every
    substitution into [m] has its tag-[2] row, and every variable has
    its tag-[0] row in [m]. *)

Definition FONUMR (x m : FOTerm) : FOFormula :=
  FOAnd (FOTBLEX (FOnumeral 5) x FOZero FOZero m)
  (FOAnd (FOForall 802 (FOForall 803 (FOTBLEX (FOnumeral 2) (FOVar 802) (FOVar 803) m m)))
         (FOForall 804 (FOTBLEX FOZero (FOVar 804) m FOZero FOZero))).

Ltac free_fm ::=
  lazymatch goal with
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

Lemma FOsubst_f_NUMR : forall z s x m, 13 <= z -> 50 <= z -> z <> 802 -> z <> 803 ->
  z <> 804 -> FOtms_avoid [s] 802 805 ->
  FOsubst_f z s (FONUMR x m) = FONUMR (FOsubst_t z s x) (FOsubst_t z s m).
Proof.
  intros z s x m H1 H2 H3 H4 H5 Hs. unfold FONUMR.
  rewrite !FOsubst_f_and, !FOsubst_f_all_ne by lia. rewrite !FOsubst_f_TBLEX by lia.
  rewrite !FOsubst_t_var_ne by lia. rewrite !FOsubst_t_zero, !FOsubst_t_numeral.
  reflexivity.
Qed.

Theorem FOPr_numr : forall n,
  FOProvesTn n (FOForall 800 (FOExists 801 (FONUMR (FOVar 800) (FOVar 801)))).
Proof.
  intro n. change (FOPrH n [] (FOForall 800 (FOExists 801 (FONUMR (FOVar 800) (FOVar 801))))).
  apply FOPrH_ind; [apply FOfree_ctx_nil|..].
  - rewrite FOsubst_f_ex_ne by lia. rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_var_eq', FOsubst_t_var_ne by lia.
    apply (FOPrH_ex_intro _ _ 801 (FOnumeral 1)); [apply FOsubst_ok_numeral|].
    rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_zero, FOsubst_t_var_eq'.
    unfold FONUMR. apply FOPrH_and_intro; [apply FOPrH_num5_zero; tab_side|].
    apply FOPrH_and_intro.
    + apply FOPrH_all_intro; [apply FOfree_ctx_nil|].
      apply FOPrH_all_intro; [apply FOfree_ctx_nil|].
      apply FOPrH_num2_zero; tab_side.
    + apply FOPrH_all_intro; [apply FOfree_ctx_nil|].
      apply FOPrH_num0_zero; tab_side.
  - rewrite FOsubst_f_ex_ne by lia. rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_var_eq', FOsubst_t_var_ne by lia.
    refine (FOPrH_ex_elim _ _ 801 (FONUMR (FOVar 800) (FOVar 801)) _ _ _ _ _);
      [free_ctx | free_fm | apply FOPrH_last |].
    apply (FOPrH_cpair_elim_hi n _ (FOnumeral 2) (FOVar 801) 805);
      [tab_side | tab_side | lia | tab_side | tab_side | tab_side |].
    apply (FOPrH_ex_intro _ _ 801 (FOVar 805)).
    { assert (V : FOtm_avoid (FOVar 805) 2 50) by avoid_tm.
      unfold FONUMR. apply FOsubst_ok_and; [apply FOsubst_ok_TBLEX; [lia | exact V]|].
      apply FOsubst_ok_and.
      - apply FOsubst_ok_all; [fr_tm|]. apply FOsubst_ok_all; [fr_tm|].
        apply FOsubst_ok_TBLEX; [lia | exact V].
      - apply FOsubst_ok_all; [fr_tm|]. apply FOsubst_ok_TBLEX; [lia | exact V]. }
    rewrite FOsubst_f_NUMR by (lia || avoid_tms).
    rewrite FOsubst_t_succ, !FOsubst_t_var_eq', FOsubst_t_var_ne by lia.
    lazymatch goal with |- FOPrH _ ?Gc _ =>
      assert (IH : FOPrH n Gc (FONUMR (FOVar 800) (FOVar 801))) by wk_in;
      assert (HC : FOPrH n Gc (FOcpairF (FOnumeral 2) (FOVar 801) (FOVar 805))) by wk_in;
      assert (HGc : FOctx_avoid Gc 2 500) by tab_side
    end.
    unfold FONUMR in IH |- *.
    apply FOPrH_and_intro;
      [exact (FOPrH_num5_succ n _ (FOVar 800) (FOVar 801) (FOVar 805) HGc ltac:(tab_side)
                (FOPrH_and_l _ _ _ _ IH) HC)|].
    apply FOPrH_and_intro.
    + apply FOPrH_all_intro; [tab_side|]. apply FOPrH_all_intro; [tab_side|].
      pose proof (FOPrH_all_same _ _ _ _ (FOPrH_all_same _ _ _ _
                    (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ IH)))) as I2.
      exact (FOPrH_num2_succ n _ (FOVar 802) (FOVar 803) (FOVar 801) (FOVar 805)
               ltac:(tab_side) ltac:(tab_side) I2 HC).
    + apply FOPrH_all_intro; [tab_side|].
      pose proof (FOPrH_all_same _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ IH)))
        as I0.
      exact (FOPrH_num0_succ n _ (FOVar 804) (FOVar 801) (FOVar 805)
               ltac:(tab_side) ltac:(tab_side) I0 HC).
Qed.

(** ** A row from rows of two tables.

    The two tables are renamed to [130] .. [140] and [151] .. [161],
    merged column by column at [162] .. [181], and the merged table is
    extended by the new row at [182] .. [191]. *)

Definition FOtabM : FOtab :=
  mkTab (FOVar 164) (FOVar 165) (FOVar 168) (FOVar 169) (FOVar 172) (FOVar 173)
    (FOVar 176) (FOVar 177) (FOVar 180) (FOVar 181)
    (FOPlus (FOPlus (FOVar 140) (FOVar 161)) FOZero).

Ltac tab_avoid ::=
  try unfold FOtabM; try unfold FOtab_terms; try unfold FOtabv; try unfold FOtabx;
  try unfold FOtab0; cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app]; avoid_tms.

Lemma FOPrH_tblex_join : forall n G tg1 a11 a21 a31 r1 tg2 a12 a22 a32 r2 tg a1 a2 a3 r,
  FOctx_avoid G 2 500 ->
  FOtms_avoid [tg1; a11; a21; a31; r1; tg2; a12; a22; a32; r2; tg; a1; a2; a3; r] 2 500 ->
  FOPrH n G (FOTBLEX tg1 a11 a21 a31 r1) -> FOPrH n G (FOTBLEX tg2 a12 a22 a32 r2) ->
  (forall G', (forall X, In X G -> In X G') ->
     FOPrH n G' (FOlookup 28 (FOVar 182) (FOVar 183) (FOVar 184) (FOVar 185) (FOVar 186)
                   (FOVar 187) (FOVar 188) (FOVar 189) (FOVar 190) (FOVar 191)
                   (FOSucc (tlen FOtabM)) tg1 a11 a21 a31 r1) ->
     FOPrH n G' (FOlookup 28 (FOVar 182) (FOVar 183) (FOVar 184) (FOVar 185) (FOVar 186)
                   (FOVar 187) (FOVar 188) (FOVar 189) (FOVar 190) (FOVar 191)
                   (FOSucc (tlen FOtabM)) tg2 a12 a22 a32 r2) ->
     FOPrH n G' (FODISPCASES (FOVar 182) (FOVar 183) (FOVar 184) (FOVar 185) (FOVar 186)
                   (FOVar 187) (FOVar 188) (FOVar 189) (FOVar 190) (FOVar 191)
                   (FOSucc (tlen FOtabM)) tg a1 a2 a3 r)) ->
  FOPrH n G (FOTBLEX tg a1 a2 a3 r).
Proof.
  intros n G tg1 a11 a21 a31 r1 tg2 a12 a22 a32 r2 tg a1 a2 a3 r HG Hav HE1 HE2 HP.
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n G tg1 a11 a21 a31 r1 130 _ _ _ _ _ _ _ _) HE1);
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n _ tg2 a12 a22 a32 r2 151 _ _ _ _ _ _ _ _)
            (FOPrH_weak_app _ _ _ _ HE2));
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (K1 : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 130) (FOVar 131) (FOVar 132)
                   (FOVar 133) (FOVar 134) (FOVar 135) (FOVar 136) (FOVar 137) (FOVar 138)
                   (FOVar 139) (FOVar 140))
                 (FOlookup 28 (FOVar 130) (FOVar 131) (FOVar 132) (FOVar 133) (FOVar 134)
                   (FOVar 135) (FOVar 136) (FOVar 137) (FOVar 138) (FOVar 139) (FOVar 140)
                   tg1 a11 a21 a31 r1))) by wk_in;
    assert (K2 : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 151) (FOVar 152) (FOVar 153)
                   (FOVar 154) (FOVar 155) (FOVar 156) (FOVar 157) (FOVar 158) (FOVar 159)
                   (FOVar 160) (FOVar 161))
                 (FOlookup 28 (FOVar 151) (FOVar 152) (FOVar 153) (FOVar 154) (FOVar 155)
                   (FOVar 156) (FOVar 157) (FOVar 158) (FOVar 159) (FOVar 160) (FOVar 161)
                   tg2 a12 a22 a32 r2))) by wk_in
  end.
  apply (FOPrH_merge3_elim n _ (FOVar 130) (FOVar 131) (FOVar 140) (FOVar 151) (FOVar 152)
           (FOVar 161) FOZero FOZero FOZero 162 163 164 165); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 132) (FOVar 133) (FOVar 140) (FOVar 153) (FOVar 154)
           (FOVar 161) FOZero FOZero FOZero 166 167 168 169); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 134) (FOVar 135) (FOVar 140) (FOVar 155) (FOVar 156)
           (FOVar 161) FOZero FOZero FOZero 170 171 172 173); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 136) (FOVar 137) (FOVar 140) (FOVar 157) (FOVar 158)
           (FOVar 161) FOZero FOZero FOZero 174 175 176 177); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 138) (FOVar 139) (FOVar 140) (FOVar 159) (FOVar 160)
           (FOVar 161) FOZero FOZero FOZero 178 179 180 181); [tab_side.. |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (HM : FOPrH n Gc (FOTABM3 (FOtabv 130) (FOtabv 151) FOtab0 FOtabM));
    [ unfold FOTABM3; apply FOPrH_and_intro; [wk_in|]; apply FOPrH_and_intro; [wk_in|];
      apply FOPrH_and_intro; [wk_in|]; apply FOPrH_and_intro; wk_in |];
    assert (HC1 : FOctx_avoid Gc 18 122) by tab_side;
    assert (HC2 : FOctx_avoid Gc 420 500) by tab_side;
    assert (K1' : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 130) (FOVar 131) (FOVar 132)
                   (FOVar 133) (FOVar 134) (FOVar 135) (FOVar 136) (FOVar 137) (FOVar 138)
                   (FOVar 139) (FOVar 140))
                 (FOlookup 28 (FOVar 130) (FOVar 131) (FOVar 132) (FOVar 133) (FOVar 134)
                   (FOVar 135) (FOVar 136) (FOVar 137) (FOVar 138) (FOVar 139) (FOVar 140)
                   tg1 a11 a21 a31 r1))) by wk K1;
    assert (K2' : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 151) (FOVar 152) (FOVar 153)
                   (FOVar 154) (FOVar 155) (FOVar 156) (FOVar 157) (FOVar 158) (FOVar 159)
                   (FOVar 160) (FOVar 161))
                 (FOlookup 28 (FOVar 151) (FOVar 152) (FOVar 153) (FOVar 154) (FOVar 155)
                   (FOVar 156) (FOVar 157) (FOVar 158) (FOVar 159) (FOVar 160) (FOVar 161)
                   tg2 a12 a22 a32 r2))) by wk K2
  end.
  clear K1 K2.
  assert (HavT : FOtms_avoid (FOtab_terms (FOtabv 130) ++ FOtab_terms (FOtabv 151) ++
                              FOtab_terms FOtab0 ++ FOtab_terms FOtabM) 420 500)
    by (unfold FOtabM; tab_side).
  destruct (FOPrH_tabm3_mono n _ _ _ _ _ HM eq_refl HC2 HavT) as (Hm1 & Hm2 & _).
  pose proof (FOPrH_tblvalid_merge n _ (FOtabv 130) (FOtabv 151) FOtab0 FOtabM 390 391 HM
                eq_refl (FOPrH_and_l _ _ _ _ K1') (FOPrH_and_l _ _ _ _ K2')
                (FOPrH_tbl_empty n _ ltac:(tab_side) ltac:(tab_side))
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(tab_side) ltac:(tab_side) HC1 HC2
                ltac:(unfold FOtabM; tab_side) ltac:(unfold FOtabM; tab_side)
                ltac:(unfold FOtabM; tab_side) ltac:(unfold FOtabM; tab_side)) as HVM.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n _ 28 (FOtabv 130) FOtabM tg1 a11 a21 a31 r1
                Hm1 ltac:(lia) ltac:(tab_side) HC2 ltac:(unfold FOtabM; tab_side)
                ltac:(unfold FOtabM; tab_side))
                (FOPrH_and_r _ _ _ _ K1')) as L1.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n _ 28 (FOtabv 151) FOtabM tg2 a12 a22 a32 r2
                Hm2 ltac:(lia) ltac:(tab_side) HC2 ltac:(unfold FOtabM; tab_side)
                ltac:(unfold FOtabM; tab_side))
                (FOPrH_and_r _ _ _ _ K2')) as L2.
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (HGinc : forall X, In X G -> In X Gc)
      by (intros X HX; repeat (apply in_or_app; left); exact HX)
  end.
  apply (FOPrH_row_new n _ FOtabM tg a1 a2 a3 r 182 _);
    [ exact HVM
    | intros G' Hinc HA1 HA2 Hm;
      apply (HP G' (fun X HX => Hinc X (HGinc X HX)));
      [ refine (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n G' 28 FOtabM _ tg1 a11 a21 a31 r1 Hm
                                    ltac:(lia) _ HA2 _ _) (FOPrH_weaken n _ G' _ Hinc L1));
        [intros w ? ?; apply HA1; lia | unfold FOtabM; tab_side | unfold FOtabM; tab_side]
      | refine (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n G' 28 FOtabM _ tg2 a12 a22 a32 r2 Hm
                                    ltac:(lia) _ HA2 _ _) (FOPrH_weaken n _ G' _ Hinc L2));
        [intros w ? ?; apply HA1; lia | unfold FOtabM; tab_side | unfold FOtabM; tab_side] ]
    | exact HC1 | exact HC2 | tab_side | lia | lia | tab_side
    | unfold FOtabM; tab_side | unfold FOtabM; tab_side | unfold FOtabM; tab_side |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (N : FOPrH n Gc (FOTBLNEW FOtabM (FOtabx 182 (FOSucc (tlen FOtabM)))
                              tg a1 a2 a3 r)) by apply FOPrH_last
  end.
  unfold FOTBLNEW in N.
  apply (FOPrH_tblex_intro n _ (FOtabx 182 (FOSucc (tlen FOtabM))) tg a1 a2 a3 r
           (FOPrH_and_l _ _ _ _ N) (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _ N))).
  unfold FOtabM. tab_side.
Qed.

(** ** Code patterns inside the tower.

    A pattern node [CPair a b] matched at base [B] names its two
    components by bounded witnesses; elimination renames them to
    fresh variables, introduction supplies them. *)

Lemma FOsubst_map_avoid : forall x s env,
  (forall t, In t env -> FOin_tm x t = false) -> map (FOsubst_t x s) env = env.
Proof.
  intros x s env H. induction env as [|t env IH]; [reflexivity|].
  cbn [map]. rewrite (FOsubst_t_not_in t x s (H t (or_introl eq_refl))).
  rewrite IH; [reflexivity|]. intros t' Ht'. apply H. right. exact Ht'.
Qed.

Lemma FOtms_avoid_env : forall env lo hi x, FOtms_avoid env lo hi -> lo <= x -> x < hi ->
  forall t, In t env -> FOin_tm x t = false.
Proof. intros env lo hi x H H1 H2 t Ht. exact (H t Ht x H1 H2). Qed.

(** Existential elimination at a renamed variable, the body cleaned by
    a separate computation before the continuation sees it. *)

Lemma FOPrH_exe_clean : forall n G z w A A' C,
  FOPrH n G (FOExists z A) ->
  FOfree_ctx w G -> FOfree_in w C = false -> FOfree_in w A = false ->
  FOsubst_ok z (FOVar w) A = true ->
  FOPrH n [FOsubst_f z (FOVar w) A] A' ->
  FOPrH n (G ++ [A']) C -> FOPrH n G C.
Proof.
  intros n G z w A A' C H HG HC HA Hok HK H0.
  refine (FOPrH_exe n G z w A C H HG HC HA Hok _).
  refine (FOPrH_cut _ _ A' _ _ _).
  - refine (FOPrH_ctxfree _ _ _ _ HK (FOPrH_last _ _ _)).
  - refine (FOPrH_weaken n _ _ _ _ H0).
    intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
    + apply in_or_app. left. apply in_or_app. left. exact HX.
    + apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_patf_pair_elim : forall n G B env a b d u w C,
  FOPrH n G (FOPATF B env (CPair a b) d) ->
  2 <= u -> 2 <= w -> u <> w ->
  (u < B \/ B + cpat_span (CPair a b) <= u) -> (w < B \/ B + cpat_span (CPair a b) <= w) ->
  FOfree_ctx u G -> FOfree_ctx w G -> FOfree_in u C = false -> FOfree_in w C = false ->
  FOtms_avoid (d :: env) B (B + cpat_span (CPair a b)) ->
  FOtms_avoid (d :: env) u (S u) -> FOtms_avoid (d :: env) w (S w) ->
  FOPrH n (G ++ [FOAnd (FOcpairF (FOVar u) (FOVar w) d)
                   (FOAnd (FOPATF (B + 4) env a (FOVar u))
                          (FOPATF (B + 4 + 4 * cpat_pairs a) env b (FOVar w)))]) C ->
  FOPrH n G C.
Proof.
  intros n G B env a b d u w C H Hu Hw Huw HuB HwB HGu HGw HCu HCw Hav Havu Havw H0.
  pose proof (cpat_span_le a) as Ha. cbn [cpat_span] in HuB, HwB, Hav.
  assert (Henv : FOtms_avoid env B (B + (4 + 4 * cpat_pairs a + cpat_span b))).
  { intros t Ht. apply Hav. right. exact Ht. }
  assert (Hd : FOtm_avoid d B (B + (4 + 4 * cpat_pairs a + cpat_span b))).
  { apply Hav. left. reflexivity. }
  assert (Henvu : FOtms_avoid env u (S u)) by (intros t Ht; apply Havu; right; exact Ht).
  assert (Henvw : FOtms_avoid env w (S w)) by (intros t Ht; apply Havw; right; exact Ht).
  assert (Hdu : FOtm_avoid d u (S u)) by (apply Havu; left; reflexivity).
  assert (Hdw : FOtm_avoid d w (S w)) by (apply Havw; left; reflexivity).
  cbn [FOPATF] in H. rewrite FOBexC_ltv in H.
  set (Clean1 := FOBexC (B + 2) (FOSucc d)
                   (FOAnd (FOcpairF (FOVar u) (FOVar (B + 2)) d)
                      (FOAnd (FOPATF (B + 4) env a (FOVar u))
                         (FOPATF (B + 4 + 4 * cpat_pairs a) env b (FOVar (B + 2)))))).
  refine (FOPrH_exe_clean n G B u _ Clean1 C H HGu HCu _ _ _ _).
  { rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    - apply FOfree_in_ltv; [lia | fr_tm].
    - rewrite FOBexC_ltv. rewrite FOfree_in_FOExists_neq by lia.
      rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split;
        [apply FOfree_in_ltv; [lia | fr_tm]|].
      rewrite !FOfree_in_FOAnd. apply Bool.orb_false_iff. split; [free_fm|].
      apply Bool.orb_false_iff. split; apply FOfree_in_PATF_any; try lia;
        (apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia | exact Henvu]). }
  { apply FOsubst_ok_and.
    - unfold FOltv. apply FOsubst_ok_ex; [apply FOin_tm_var_ne; lia | apply FOsubst_ok_eq].
    - apply FOsubst_ok_bex; [apply FOin_tm_var_ne; lia | apply FOin_tm_var_ne; lia|].
      apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
      apply FOsubst_ok_and; apply FOsubst_ok_PATF; apply FOtm_avoid_var; lia. }
  { unfold Clean1.
    rewrite FOsubst_f_and, FOsubst_f_bex by lia.
    rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_and, !FOsubst_f_PATF by lia.
    rewrite !FOsubst_t_succ, FOsubst_t_var_eq', FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in d B _ (Hd B ltac:(lia) ltac:(lia))).
    rewrite (FOsubst_map_avoid B _ env (FOtms_avoid_env env _ _ B Henv ltac:(lia) ltac:(lia))).
    apply (FOPrH_and_r n _ (FOsubst_f B (FOVar u) (FOltv B (FOSucc d)))).
    apply FOPrH_assum. left. reflexivity. }
  assert (HC1 : FOPrH n (G ++ [Clean1]) Clean1) by apply FOPrH_last.
  unfold Clean1 in HC1. rewrite FOBexC_ltv in HC1.
  refine (FOPrH_exe_clean n _ (B + 2) w _ _ C HC1 _ HCw _ _ _ _).
  { apply FOfree_ctx_app_inv; [exact HGw|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil].
    try unfold Clean1; try rewrite FOBexC_ltv. rewrite FOfree_in_FOExists_neq by lia.
    rewrite !FOfree_in_FOAnd. apply Bool.orb_false_iff. split;
      [apply FOfree_in_ltv; [lia | fr_tm]|].
    apply Bool.orb_false_iff. split; [free_fm|].
    apply Bool.orb_false_iff. split; apply FOfree_in_PATF_any; try lia;
      (apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia | exact Henvw]). }
  { rewrite !FOfree_in_FOAnd. apply Bool.orb_false_iff. split;
      [apply FOfree_in_ltv; [lia | fr_tm]|].
    apply Bool.orb_false_iff. split; [free_fm|].
    apply Bool.orb_false_iff. split; apply FOfree_in_PATF_any; try lia;
      (apply FOtms_avoid_cons; [apply FOtm_avoid_var; lia | exact Henvw]). }
  { apply FOsubst_ok_and.
    - unfold FOltv. apply FOsubst_ok_ex; [apply FOin_tm_var_ne; lia | apply FOsubst_ok_eq].
    - apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
      apply FOsubst_ok_and; apply FOsubst_ok_PATF; apply FOtm_avoid_var; lia. }
  { rewrite FOsubst_f_and. rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_and,
      !FOsubst_f_PATF by lia.
    rewrite FOsubst_t_var_eq', !FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in d (B + 2) _ (Hd (B + 2) ltac:(lia) ltac:(lia))).
    rewrite (FOsubst_map_avoid (B + 2) _ env
               (FOtms_avoid_env env _ _ (B + 2) Henv ltac:(lia) ltac:(lia))).
    apply (FOPrH_and_r n _ (FOsubst_f (B + 2) (FOVar w) (FOltv (B + 2) (FOSucc d)))).
    apply FOPrH_assum. left. reflexivity. }
  refine (FOPrH_weaken n _ _ _ _ H0).
  intros X HX. apply in_app_or in HX. destruct HX as [HX|[<-|[]]].
  - apply in_or_app. left. apply in_or_app. left. exact HX.
  - apply in_or_app. right. left. reflexivity.
Qed.

Lemma FOPrH_le_succ_of_le : forall n G a b,
  FOPrH n G (FOle a b) -> FOtms_avoid [a; b] 498 499 -> FOPrH n G (FOle (FOSucc a) (FOSucc b)).
Proof.
  intros n G a b H Hav. unfold FOle in *.
  refine (FOPrH_mp _ _ _ _ _ H). apply FOPrH_empty. apply FOPrH_intro.
  refine (FOPrH_ex_elim _ _ 498 (FOEq (FOPlus a (FOVar 498)) b) _ _ _ _ _);
    [free_ctx | free_fm | apply FOPrH_last |].
  apply (FOPrH_ex_intro _ _ 498 (FOVar 498)); [cbn [FOsubst_ok]; reflexivity|].
  rewrite FOsubst_f_id.
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (E : FOPrH n Gc (FOEq b (FOPlus a (FOVar 498)))) by (apply FOPrH_eq_sym; wk_in)
  end.
  fo_lin [(.S .0, b, a .+ #498)]; exact E.
Qed.

Lemma FOPrH_patf_pair_intro : forall n G B env a b d u w,
  FOPrH n G (FOcpairF u w d) ->
  FOPrH n G (FOPATF (B + 4) env a u) ->
  FOPrH n G (FOPATF (B + 4 + 4 * cpat_pairs a) env b w) ->
  500 <= B ->
  FOtms_avoid (d :: u :: w :: env) B (B + cpat_span (CPair a b)) ->
  FOtms_avoid [d; u; w] 420 500 ->
  FOPrH n G (FOPATF B env (CPair a b) d).
Proof.
  intros n G B env a b d u w HC Ha Hb HB Hav Hav2.
  pose proof (cpat_span_le a) as Hsa. cbn [cpat_span] in Hav.
  assert (Henv : forall x, B <= x -> x < B + (4 + 4 * cpat_pairs a + cpat_span b) ->
            map (FOsubst_t x (FOVar 0)) env = env) by
    (intros x H1 H2; apply FOsubst_map_avoid; intros t Ht; apply (Hav t); [right; right; right; exact Ht | lia | lia]).
  destruct (FOPrH_cpair_le_cf n G u w d ltac:(avoid_tms) HC) as [Hud Hwd].
  cbn [FOPATF].
  apply (FOPrH_bex_intro_t _ _ B (FOSucc d) u); [lia | lia | avoid_tm | avoid_tm | avoid_tm
    | avoid_tm | apply FOPrH_le_succ_of_le; [exact Hud | avoid_tms] | | ].
  - apply FOsubst_ok_bex; [apply (Hav u); [right; left; reflexivity | lia | lia]
                         | apply (Hav u); [right; left; reflexivity | lia | lia] |].
    apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
    apply FOsubst_ok_and; apply FOsubst_ok_PATF;
      apply (FOtm_avoid_sub u B (B + (4 + 4 * cpat_pairs a + cpat_span b)));
      try (apply Hav; right; left; reflexivity); lia.
  - rewrite FOsubst_f_bex by lia. rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_and,
      !FOsubst_f_PATF by lia.
    rewrite FOsubst_t_succ, FOsubst_t_var_eq', !FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in d B _ (Hav d (or_introl eq_refl) B ltac:(lia) ltac:(lia))).
    rewrite (FOsubst_map_avoid B u env).
    2:{ intros t Ht. apply (Hav t); [right; right; right; exact Ht | lia | lia]. }
    apply (FOPrH_bex_intro_t _ _ (B + 2) (FOSucc d) w); [lia | lia | avoid_tm | avoid_tm
      | avoid_tm | avoid_tm | apply FOPrH_le_succ_of_le; [exact Hwd | avoid_tms] | | ].
    + apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
      apply FOsubst_ok_and; apply FOsubst_ok_PATF;
        apply (FOtm_avoid_sub w B (B + (4 + 4 * cpat_pairs a + cpat_span b)));
        try (apply Hav; right; right; left; reflexivity); lia.
    + rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_and, !FOsubst_f_PATF by lia.
      rewrite FOsubst_t_var_eq'. rewrite ?FOsubst_t_var_ne by lia.
      rewrite (FOsubst_t_not_in d (B + 2) _ (Hav d (or_introl eq_refl) (B + 2) ltac:(lia)
                                               ltac:(lia))).
      rewrite (FOsubst_t_not_in u (B + 2) _ (Hav u (or_intror (or_introl eq_refl)) (B + 2)
                                               ltac:(lia) ltac:(lia))).
      rewrite (FOsubst_map_avoid (B + 2) w env).
      2:{ intros t Ht. apply (Hav t); [right; right; right; exact Ht | lia | lia]. }
      apply FOPrH_and_intro; [exact HC|]. apply FOPrH_and_intro; [exact Ha | exact Hb].
Qed.

Ltac free_fm ::=
  lazymatch goal with
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

(** ** The guard rows of a code, with the table renamed. *)

Lemma FOPrH_guardb_elim : forall n G d k C,
  122 <= k -> k + 11 <= 420 ->
  FOctx_avoid G k (k + 11) ->
  (forall w, k <= w -> w < k + 11 -> FOfree_in w C = false) ->
  FOtms_avoid [d] 2 122 -> FOtms_avoid [d] k (k + 11) ->
  FOPrH n (G ++ [FOAnd (FOTBLVALID 18 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10)))
                       (FOBexC 13 (FOSucc (FOVar (k + 8)))
                          (FOlookup 28 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                             (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                             (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10))
                             (FOnumeral 3) (FOSucc d) FOZero d (FOVar 13)))]) C ->
  FOPrH n G (FOGUARDB d .-> C).
Proof.
  intros n G d k C Hk Hk' HG HC Hr Hrk H.
  unfold FOGUARDB.
  tblex_rename_step Hr k. tblex_rename_step Hr (k + 1). tblex_rename_step Hr (k + 2).
  tblex_rename_step Hr (k + 3). tblex_rename_step Hr (k + 4). tblex_rename_step Hr (k + 5).
  tblex_rename_step Hr (k + 6). tblex_rename_step Hr (k + 7). tblex_rename_step Hr (k + 8).
  tblex_rename_step Hr (k + 9). tblex_rename_step Hr (k + 10).
  apply FOPrH_intro. exact H.
Qed.

(** ** Small facts: [<=] from an equation, the one-element beta code,
    bounded universals over [0] and [1]. *)

Lemma FOPrH_le_of_eq : forall n G a b c,
  FOPrH n G (FOEq (FOPlus a c) b) -> FOtms_avoid [a; b] 498 499 ->
  FOPrH n G (FOle a b).
Proof.
  intros n G a b c H Hav. unfold FOle.
  apply (FOPrH_ex_intro _ _ 498 c); [reflexivity|].
  rewrite FOsubst_f_eq, FOsubst_t_plus, FOsubst_t_var_eq'.
  rewrite (FOsubst_t_not_in a 498 c (Hav a ltac:(in_list) 498 ltac:(lia) ltac:(lia))).
  rewrite (FOsubst_t_not_in b 498 c (Hav b ltac:(in_list) 498 ltac:(lia) ltac:(lia))).
  exact H.
Qed.

Lemma FOPrH_beta_self0 : forall n G v d,
  2 <= v -> v + 4 <= 420 ->
  FOtms_avoid [d] v (v + 4) -> FOtms_avoid [d] 420 500 ->
  FOPrH n G (FObetaF v d d FOZero d).
Proof.
  intros n G v d Hv Hv' Hd1 Hd2. unfold FObetaF.
  apply (FOPrH_bex_intro_t _ _ v (FOSucc d) FOZero); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | | fo_ok_solve | ].
  - apply (FOPrH_le_of_eq _ _ _ _ d); [apply FOPrH_ring; fo_ring | avoid_tms].
  - autorewrite with fosubst. subst_avoid_h Hd1.
    apply FOPrH_and_intro; [apply FOPrH_ring; fo_ring|].
    apply (FOPrH_bex_intro_t _ _ (S (S v)) (FOSucc (FOMult d (FOSucc FOZero))) FOZero);
      [lia | lia | avoid_tm | avoid_tm | avoid_tm | avoid_tm | | fo_ok_solve | ].
    + apply (FOPrH_le_of_eq _ _ _ _ (FOMult d (FOSucc FOZero)));
        [apply FOPrH_ring; fo_ring | avoid_tms].
    + autorewrite with fosubst. subst_avoid_h Hd1. apply FOPrH_ring. fo_ring.
Qed.

Lemma FOPrH_ball_zero : forall n G v P,
  FOfree_ctx v G -> FOfree_ctx (S v) G ->
  FOPrH n G (FOBallC v FOZero P).
Proof.
  intros n G v P HG HG'.
  rewrite FOBallC_ltv. apply FOPrH_all_intro; [exact HG|].
  apply FOPrH_intro. apply FOPrH_efq. unfold FOltv.
  refine (FOPrH_ex_elim _ _ (S v) (FOEq (FOPlus (FOVar v) (FOSucc (FOVar (S v)))) FOZero)
            _ _ _ _ _); [| reflexivity | apply FOPrH_last |].
  { apply FOfree_ctx_app_inv; [exact HG'|].
    apply FOfree_ctx_cons; [|apply FOfree_ctx_nil]. apply FOfree_in_ex_self. }
  apply (FOPrH_Q_succ_nonzero _ _ (FOPlus (FOVar v) (FOVar (S v)))).
  apply (FOPrH_eq_trans _ _ _ (FOPlus (FOVar v) (FOSucc (FOVar (S v)))));
    [apply FOPrH_eq_sym; apply FOPrH_Q_plus_succ | apply FOPrH_last].
Qed.

Lemma FOPrH_ball_one : forall n G v P w,
  FOPrH n G (FOsubst_f v FOZero P) -> FOsubst_ok v FOZero P = true ->
  2 <= v -> v < 399 -> 1 < w -> w <> v -> w <> S v ->
  FOfree_ctx v G -> FOfree_ctx (S v) G -> FOfree_ctx w G ->
  FOfree_in (S v) P = false -> FOfree_in w P = false ->
  FOPrH n G (FOBallC v (FOSucc FOZero) P).
Proof.
  intros n G v P w H Hok Hv Hv' Hw Hwv HwSv HG HG' HGw FSv Fw.
  apply (FOPrH_ball_snoc n G v FOZero P w); try assumption.
  - apply FOPrH_ball_zero; assumption.
  - intros t Ht u Hu1 Hu2. destruct Ht as [<-|[]]. reflexivity.
  - intros t Ht u Hu1 Hu2. destruct Ht as [<-|[]]. reflexivity.
  - intros t Ht u Hu1 Hu2. destruct Ht as [<-|[]]. reflexivity.
Qed.

(** ** Derivations of one line.

    A code whose guard rows exist and which passes the justification
    check of tag [0] (a theory axiom) or [1] (a logical axiom) with
    payload [0] is derivable in one line: the guard's table, the
    one-element formula track [d], and the one-element justification
    track holding the tag, which is its own code. *)

Ltac ok0 :=
  let V := fresh "V" in
  assert (V : FOtm_avoid FOZero 2 500) by (intros ? ? ?; reflexivity);
  solve [auto 100 with fook].

Lemma FOPrH_one_line : forall n G cores d tgn,
  FOctx_avoid G 2 500 -> FOtms_avoid [d] 2 500 -> tgn <= 1 ->
  FOPrH n G (FOGUARDB d) ->
  (forall T, FOPrH n G (FOJDISJ 20 cores (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T)
                          (tc3 T) (td3 T) (tcr T) (tdr T) (tlen T) d d FOZero d
                          (FOnumeral tgn) FOZero)) ->
  FOPrH n G (FOPRMATx cores d).
Proof.
  intros n G cores d tgn HG Hd Htg HB HJ.
  refine (FOPrH_mp _ _ (FOGUARDB d) _ _ HB).
  apply (FOPrH_guardb_elim n G d 260); [lia | lia | intros w H1 H2; apply HG; lia
    | intros w H1 H2; free_fm | avoid_tms | avoid_tms |].
  lazymatch goal with |- FOPrH _ (_ ++ [?GB]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G GB)) as VT;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G GB)) as BX
  end.
  refine (FOPrH_mp _ _ _ _ _ BX).
  apply FOPrH_imp_bexl; [free_ctx | free_fm |].
  apply FOPrH_intro.
  apply (FOPrH_PRMAT_intro n _ cores d (FOVar 260) (FOVar 261) (FOVar 262) (FOVar 263)
           (FOVar 264) (FOVar 265) (FOVar 266) (FOVar 267) (FOVar 268) (FOVar 269)
           (FOVar 270) d d (FOnumeral tgn) (FOnumeral tgn) (FOSucc FOZero));
    [avoid_tms | avoid_tms |].
  unfold FOPRDERp. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen].
  apply FOPrH_and_intro; [wk VT|].
  apply FOPrH_and_intro.
  { apply (FOPrH_bex_intro_t _ _ 18 (FOSucc FOZero) FOZero); [lia | lia | avoid_tm
      | avoid_tm | avoid_tm | avoid_tm | | ok0 |].
    - apply FOPrH_le_refl. avoid_tm.
    - autorewrite with fosubst. subst_avoid_h Hd.
      apply FOPrH_and_intro; [apply FOPrH_ring; fo_ring|].
      apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms]. }
  apply FOPrH_and_intro.
  - apply (FOPrH_ball_one _ _ 18 _ 250); [| ok0 | lia | lia | lia | lia | lia
      | free_ctx | free_ctx | free_ctx | free_fm | free_fm].
    autorewrite with fosubst. subst_avoid_h Hd.
    apply (FOPrH_JUSTCK_intro_t _ _ 20 cores _ _ _ _ _ _ _ _ _ _ _ d d
             (FOnumeral tgn) (FOnumeral tgn) FOZero d (FOnumeral tgn));
      [lia | lia | avoid_tms | avoid_tms | avoid_tms | avoid_tms | | | | |].
    + apply FOPrH_le_refl. avoid_tm.
    + apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms].
    + apply FOPrH_le_refl. avoid_tm.
    + apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms].
    + apply (FOPrH_CHK_intro_t _ _ 20 cores _ _ _ _ _ _ _ _ _ _ _ d d FOZero d
               (FOnumeral tgn) (FOnumeral tgn) FOZero);
        [lia | avoid_tms | avoid_tms | avoid_tms | avoid_tms | | | |].
      * apply FOPrH_le_refl. avoid_tm.
      * destruct tgn as [|[|]]; [apply FOPrH_le_refl; avoid_tm | | lia].
        apply (FOPrH_le_of_eq _ _ _ _ (FOSucc FOZero));
          [cbn [FOnumeral]; apply FOPrH_ring; fo_ring | avoid_tms].
      * destruct tgn as [|[|]]; [| | lia]; unfold FOcpairF; cbn [FOnumeral];
          apply FOPrH_ring; fo_ring.
      * pose proof (HJ (FOtabv 260)) as HJ'. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr
          tlen FOtabv Nat.add] in HJ'. wk HJ'.
  - apply (FOPrH_ball_one _ _ 18 _ 250); [| ok0 | lia | lia | lia | lia | lia
      | free_ctx | free_ctx | free_ctx | free_fm | free_fm].
    autorewrite with fosubst. subst_avoid_h Hd.
    apply (FOPrH_GUARDC_intro_t _ _ 20 (FOtabv 260) d d FOZero d (FOVar 13));
      [lia | tab_avoid | avoid_tms | avoid_tms | tab_avoid | | | |].
    + apply FOPrH_le_refl. avoid_tm.
    + apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms].
    + cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen FOtabv Nat.add].
      apply FOPrH_le_of_ltv; [free_ctx | lia | lia | avoid_tm | avoid_tm |].
      apply FOPrH_assum. in_app.
    + cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen FOtabv Nat.add].
      apply FOPrH_last.
Qed.

(** ** A lookup's result is at most the code of its result column. *)

Lemma FOPrH_lookup_res_le : forall n G B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r,
  FOPrH n G (FOlookup B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r) ->
  2 <= B -> B + 22 <= 420 ->
  FOctx_avoid G B (B + 22) ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; tg; a1; a2; a3; r] B (B + 22) ->
  FOtms_avoid [cr; dr; r] 498 499 ->
  FOPrH n G (FOle r cr).
Proof.
  intros n G B ct dt c1 d1 c2 d2 c3 d3 cr dr len tg a1 a2 a3 r H HB HB' HG Hav Hav2.
  unfold FOlookup in H.
  refine (FOPrH_mp _ _ _ _ _ H).
  apply FOPrH_imp_bexl; [free_ctx | free_fm |].
  apply FOPrH_intro.
  lazymatch goal with |- FOPrH _ (_ ++ [?X]) _ =>
    pose proof (FOPrH_last n (G ++ [FOltv B len]) X) as L0
  end.
  apply FOPrH_and_r, FOPrH_and_r, FOPrH_and_r, FOPrH_and_r in L0.
  refine (FOPrH_mp _ _ _ _ (FOPrH_beta_le _ _ (B + 18) cr dr (FOVar B) r _ _ _ _) L0);
    [ctx_list | lia | avoid_tms | avoid_tms].
Qed.

(** ** The guard rows of [d] from a table row substituting at [S d]
    inside [d]. *)

Lemma FOPrH_guard_of_row : forall n G d r,
  FOctx_avoid G 2 500 -> FOtms_avoid [d; r] 2 500 ->
  FOPrH n G (FOTBLEX (FOnumeral 3) (FOSucc d) FOZero d r) -> FOPrH n G (FOGUARDB d).
Proof.
  intros n G d r HG Hdr H.
  refine (FOPrH_mp _ _ _ _ _ H).
  apply (FOPrH_tblex_elim n G _ _ _ _ _ 260); [lia | lia | intros w H1 H2; apply HG; lia
    | intros w H1 H2; free_fm | avoid_tms | avoid_tms |].
  lazymatch goal with |- FOPrH _ (_ ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G X)) as VT;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_last n G X)) as LK
  end.
  assert (Hav : FOtms_avoid [FOVar 260; FOVar 261; FOVar 262; FOVar 263; FOVar 264;
                  FOVar 265; FOVar 266; FOVar 267; FOVar 268; FOVar 269; FOVar 270; d; r]
                  2 122) by avoid_tms.
  unfold FOGUARDB.
  tblex_intro_step (FOVar 260) Hav. tblex_intro_step (FOVar 261) Hav.
  tblex_intro_step (FOVar 262) Hav. tblex_intro_step (FOVar 263) Hav.
  tblex_intro_step (FOVar 264) Hav. tblex_intro_step (FOVar 265) Hav.
  tblex_intro_step (FOVar 266) Hav. tblex_intro_step (FOVar 267) Hav.
  tblex_intro_step (FOVar 268) Hav. tblex_intro_step (FOVar 269) Hav.
  tblex_intro_step (FOVar 270) Hav.
  cbn [Nat.add] in VT, LK.
  apply FOPrH_and_intro; [exact VT|].
  apply (FOPrH_bex_intro_t _ _ 13 (FOSucc (FOVar 268)) r); [lia | lia | avoid_tm | avoid_tm
    | avoid_tm | avoid_tm | | | ].
  - apply FOPrH_le_succ_of_le; [|avoid_tms].
    apply (FOPrH_lookup_res_le _ _ 28 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ LK);
      [lia | lia | ctx_list | avoid_tms | avoid_tms].
  - let V := fresh "V" in assert (V : FOtm_avoid r 2 122) by avoid_tm;
    solve [auto 100 with fook].
  - autorewrite with fosubst. rewrite ?FOsubst_t_var_eq'. subst_avoid_h Hav. exact LK.
Qed.

(** ** Tables holding a list of rows.

    [FOlookups B T rs]: every row of [rs] is looked up in [T] at base
    [B].  [FOTBLROWS rs]: some valid table at the variables [2] through
    [12] holds every row of [rs]. *)

Definition FOrow : Type := (FOTerm * FOTerm * FOTerm * FOTerm * FOTerm)%type.

Definition FOrow_terms (rw : FOrow) : list FOTerm :=
  let '(tg, a1, a2, a3, r) := rw in [tg; a1; a2; a3; r].

Fixpoint FOrows_terms (rs : list FOrow) : list FOTerm :=
  match rs with
  | [] => []
  | rw :: rs' => FOrow_terms rw ++ FOrows_terms rs'
  end.

Fixpoint FOlookups (B : nat) (T : FOtab) (rs : list FOrow) : FOFormula :=
  match rs with
  | [] => FOTrue
  | (tg, a1, a2, a3, r) :: rs' => FOAnd (FOlookupT B T tg a1 a2 a3 r) (FOlookups B T rs')
  end.

Definition FOtab2 : FOtab :=
  mkTab (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6) (FOVar 7) (FOVar 8) (FOVar 9)
    (FOVar 10) (FOVar 11) (FOVar 12).

Definition FOTBLROWS (rs : list FOrow) : FOFormula :=
  FOExists 2 (FOExists 3 (FOExists 4 (FOExists 5 (FOExists 6 (FOExists 7
  (FOExists 8 (FOExists 9 (FOExists 10 (FOExists 11 (FOExists 12
    (FOAnd (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12))
       (FOlookups 28 FOtab2 rs)))))))))))).

Lemma FOrows_terms_app : forall rs1 rs2,
  FOrows_terms (rs1 ++ rs2) = FOrows_terms rs1 ++ FOrows_terms rs2.
Proof.
  induction rs1 as [|rw rs1 IH]; intros rs2; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

Lemma FOtms_avoid_rows_cons : forall rw rs lo hi,
  FOtms_avoid (FOrows_terms (rw :: rs)) lo hi ->
  FOtms_avoid (FOrow_terms rw) lo hi /\ FOtms_avoid (FOrows_terms rs) lo hi.
Proof.
  intros rw rs lo hi H. cbn in H. split; intros t Ht; apply H; apply in_or_app;
    [left | right]; exact Ht.
Qed.

Lemma FOsubst_f_lookups : forall x s B T rs, x < B ->
  FOtms_avoid (FOrows_terms rs) x (S x) ->
  FOsubst_f x s (FOlookups B T rs) = FOlookups B (FOtab_subst x s T) rs.
Proof.
  intros x s B T rs HB. induction rs as [|[[[[tg a1] a2] a3] r] rs IH]; intros Hav.
  - reflexivity.
  - apply FOtms_avoid_rows_cons in Hav. destruct Hav as [Hh Ht].
    cbn [FOlookups]. rewrite FOsubst_f_and. unfold FOlookupT.
    rewrite FOsubst_f_lookup by exact HB. rewrite (IH Ht).
    cbn [FOrow_terms] in Hh.
    rewrite (FOsubst_t_not_in tg x s) by (apply (Hh tg ltac:(in_list) x); lia).
    rewrite (FOsubst_t_not_in a1 x s) by (apply (Hh a1 ltac:(in_list) x); lia).
    rewrite (FOsubst_t_not_in a2 x s) by (apply (Hh a2 ltac:(in_list) x); lia).
    rewrite (FOsubst_t_not_in a3 x s) by (apply (Hh a3 ltac:(in_list) x); lia).
    rewrite (FOsubst_t_not_in r x s) by (apply (Hh r ltac:(in_list) x); lia).
    reflexivity.
Qed.

Lemma FOsubst_ok_lookups : forall x s B T rs, FOtm_avoid s B (B + 22) ->
  FOsubst_ok x s (FOlookups B T rs) = true.
Proof.
  intros x s B T rs Hs. induction rs as [|[[[[tg a1] a2] a3] r] rs IH].
  - reflexivity.
  - cbn [FOlookups]. apply FOsubst_ok_and; [apply FOsubst_ok_lookup; exact Hs | exact IH].
Qed.

Lemma FOfree_in_lookups : forall w B T rs, 2 <= w ->
  FOtms_avoid (FOtab_terms T ++ FOrows_terms rs) w (S w) ->
  FOfree_in w (FOlookups B T rs) = false.
Proof.
  intros w B T rs Hw. induction rs as [|[[[[tg a1] a2] a3] r] rs IH]; intros Hav.
  - reflexivity.
  - cbn [FOlookups]. rewrite FOfree_in_FOAnd. apply Bool.orb_false_iff. split.
    + unfold FOlookupT. free_by FOlookup_free;
        match goal with E : FOin_tm w ?t = true |- _ =>
          rewrite (Hav t ltac:(cbn; in_list) w ltac:(lia) ltac:(lia)) in E; discriminate E
        end.
    + apply IH. intros t Ht. apply Hav. apply in_app_or in Ht.
      destruct Ht as [Ht|Ht]; apply in_or_app; [left; exact Ht|].
      right. cbn [FOrows_terms]. apply in_or_app. right. exact Ht.
Qed.

(** ** Tables holding three given rows. *)

Definition FOTBLEX3 (tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' : FOTerm)
  : FOFormula :=
  FOExists 2 (FOExists 3 (FOExists 4 (FOExists 5 (FOExists 6 (FOExists 7
  (FOExists 8 (FOExists 9 (FOExists 10 (FOExists 11 (FOExists 12
    (FOAnd (FOTBLVALID 18 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12))
    (FOAnd (FOlookup 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
              tg a1 a2 a3 r)
    (FOAnd (FOlookup 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
              tg' a1' a2' a3' r')
           (FOlookup 28 (FOVar 2) (FOVar 3) (FOVar 4) (FOVar 5) (FOVar 6)
              (FOVar 7) (FOVar 8) (FOVar 9) (FOVar 10) (FOVar 11) (FOVar 12)
              tg'' a1'' a2'' a3'' r'')))))))))))))).

Lemma FOPrH_tblex3_elim : forall n G tg a1 a2 a3 r tg' a1' a2' a3' r'
    tg'' a1'' a2'' a3'' r'' k C,
  122 <= k -> k + 11 <= 420 ->
  FOctx_avoid G k (k + 11) ->
  (forall w, k <= w -> w < k + 11 -> FOfree_in w C = false) ->
  FOtms_avoid [tg; a1; a2; a3; r; tg'; a1'; a2'; a3'; r'; tg''; a1''; a2''; a3''; r'']
    2 122 ->
  FOtms_avoid [tg; a1; a2; a3; r; tg'; a1'; a2'; a3'; r'; tg''; a1''; a2''; a3''; r'']
    k (k + 11) ->
  FOPrH n (G ++ [FOAnd (FOTBLVALID 18 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10)))
                  (FOAnd (FOlookup 28 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10))
                          tg a1 a2 a3 r)
                  (FOAnd (FOlookup 28 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10))
                          tg' a1' a2' a3' r')
                         (FOlookup 28 (FOVar k) (FOVar (k + 1)) (FOVar (k + 2))
                          (FOVar (k + 3)) (FOVar (k + 4)) (FOVar (k + 5)) (FOVar (k + 6))
                          (FOVar (k + 7)) (FOVar (k + 8)) (FOVar (k + 9)) (FOVar (k + 10))
                          tg'' a1'' a2'' a3'' r'')))]) C ->
  FOPrH n G (FOTBLEX3 tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' .-> C).
Proof.
  intros n G tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' k C
    Hk Hk' HG HC Hr Hrk H.
  unfold FOTBLEX3.
  tblex_rename_step Hr k. tblex_rename_step Hr (k + 1). tblex_rename_step Hr (k + 2).
  tblex_rename_step Hr (k + 3). tblex_rename_step Hr (k + 4). tblex_rename_step Hr (k + 5).
  tblex_rename_step Hr (k + 6). tblex_rename_step Hr (k + 7). tblex_rename_step Hr (k + 8).
  tblex_rename_step Hr (k + 9). tblex_rename_step Hr (k + 10).
  apply FOPrH_intro. exact H.
Qed.

Lemma FOPrH_tblex3_intro : forall n G T tg a1 a2 a3 r tg' a1' a2' a3' r'
    tg'' a1'' a2'' a3'' r'',
  FOPrH n G (FOTBLVALID 18 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T)) ->
  FOPrH n G (FOlookup 28 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) tg a1 a2 a3 r) ->
  FOPrH n G (FOlookup 28 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) tg' a1' a2' a3' r') ->
  FOPrH n G (FOlookup 28 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) tg'' a1'' a2'' a3'' r'') ->
  FOtms_avoid (FOtab_terms T ++ [tg; a1; a2; a3; r; tg'; a1'; a2'; a3'; r';
                                 tg''; a1''; a2''; a3''; r'']) 2 122 ->
  FOPrH n G (FOTBLEX3 tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'').
Proof.
  intros n G T tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' HV H1 H2 H3 Hav.
  destruct T as [ct dt c1 d1 c2 d2 c3 d3 cr dr len].
  unfold FOtab_terms in Hav. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app] in *.
  unfold FOTBLEX3.
  tblex_intro_step ct Hav. tblex_intro_step dt Hav. tblex_intro_step c1 Hav.
  tblex_intro_step d1 Hav. tblex_intro_step c2 Hav. tblex_intro_step d2 Hav.
  tblex_intro_step c3 Hav. tblex_intro_step d3 Hav. tblex_intro_step cr Hav.
  tblex_intro_step dr Hav. tblex_intro_step len Hav.
  apply FOPrH_and_intro; [exact HV|].
  apply FOPrH_and_intro; [exact H1|].
  apply FOPrH_and_intro; [exact H2 | exact H3].
Qed.

(** ** Three rows of three tables in one table.

    The tables are renamed to [130] .. [140], [151] .. [161] and
    [192] .. [202] and merged column by column at [162] .. [181]. *)

Definition FOtabM3 : FOtab :=
  mkTab (FOVar 164) (FOVar 165) (FOVar 168) (FOVar 169) (FOVar 172) (FOVar 173)
    (FOVar 176) (FOVar 177) (FOVar 180) (FOVar 181)
    (FOPlus (FOPlus (FOVar 140) (FOVar 161)) (FOVar 202)).

Lemma FOfree_in_TBLEX3_any : forall w tg a1 a2 a3 r tg' a1' a2' a3' r'
    tg'' a1'' a2'' a3'' r'',
  2 <= w ->
  FOtms_avoid [tg; a1; a2; a3; r; tg'; a1'; a2'; a3'; r'; tg''; a1''; a2''; a3''; r'']
    w (S w) ->
  FOfree_in w (FOTBLEX3 tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'') = false.
Proof.
  intros w tg a1 a2 a3 r tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' Hw Hav.
  unfold FOTBLEX3.
  repeat match goal with
         | |- FOfree_in _ (FOExists ?y _) = false =>
             destruct (Nat.eq_dec y w) as [<-|?];
             [apply FOfree_in_ex_self | rewrite FOfree_in_FOExists_neq by assumption]
         end.
  rewrite !FOfree_in_FOAnd. repeat (apply Bool.orb_false_iff; split).
  - free_by FOTBLVALID_free.
  - free_by FOlookup_free.
  - free_by FOlookup_free.
  - free_by FOlookup_free.
Qed.

Ltac free_fm ::=
  lazymatch goal with
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

Ltac tab_avoid ::=
  try unfold FOtabM3; try unfold FOtabM; try unfold FOtab_terms; try unfold FOtabv;
  try unfold FOtabx; try unfold FOtab0;
  cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app]; avoid_tms.

Lemma FOPrH_tblex_join3 : forall n G tg1 a11 a21 a31 r1 tg2 a12 a22 a32 r2
    tg3 a13 a23 a33 r3,
  FOctx_avoid G 2 500 ->
  FOtms_avoid [tg1; a11; a21; a31; r1; tg2; a12; a22; a32; r2; tg3; a13; a23; a33; r3]
    2 500 ->
  FOPrH n G (FOTBLEX tg1 a11 a21 a31 r1) -> FOPrH n G (FOTBLEX tg2 a12 a22 a32 r2) ->
  FOPrH n G (FOTBLEX tg3 a13 a23 a33 r3) ->
  FOPrH n G (FOTBLEX3 tg1 a11 a21 a31 r1 tg2 a12 a22 a32 r2 tg3 a13 a23 a33 r3).
Proof.
  intros n G tg1 a11 a21 a31 r1 tg2 a12 a22 a32 r2 tg3 a13 a23 a33 r3 HG Hav HE1 HE2 HE3.
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n G tg1 a11 a21 a31 r1 130 _ _ _ _ _ _ _ _) HE1);
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n _ tg2 a12 a22 a32 r2 151 _ _ _ _ _ _ _ _)
            (FOPrH_weak_app _ _ _ _ HE2));
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  refine (FOPrH_mp _ _ _ _ (FOPrH_tblex_elim n _ tg3 a13 a23 a33 r3 192 _ _ _ _ _ _ _ _)
            (FOPrH_weak_app _ _ _ _ (FOPrH_weak_app _ _ _ _ HE3)));
    [lia | lia | tab_side | tab_side | tab_side | tab_side |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (K1 : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 130) (FOVar 131) (FOVar 132)
                   (FOVar 133) (FOVar 134) (FOVar 135) (FOVar 136) (FOVar 137) (FOVar 138)
                   (FOVar 139) (FOVar 140))
                 (FOlookup 28 (FOVar 130) (FOVar 131) (FOVar 132) (FOVar 133) (FOVar 134)
                   (FOVar 135) (FOVar 136) (FOVar 137) (FOVar 138) (FOVar 139) (FOVar 140)
                   tg1 a11 a21 a31 r1))) by wk_in;
    assert (K2 : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 151) (FOVar 152) (FOVar 153)
                   (FOVar 154) (FOVar 155) (FOVar 156) (FOVar 157) (FOVar 158) (FOVar 159)
                   (FOVar 160) (FOVar 161))
                 (FOlookup 28 (FOVar 151) (FOVar 152) (FOVar 153) (FOVar 154) (FOVar 155)
                   (FOVar 156) (FOVar 157) (FOVar 158) (FOVar 159) (FOVar 160) (FOVar 161)
                   tg2 a12 a22 a32 r2))) by wk_in;
    assert (K3 : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 192) (FOVar 193) (FOVar 194)
                   (FOVar 195) (FOVar 196) (FOVar 197) (FOVar 198) (FOVar 199) (FOVar 200)
                   (FOVar 201) (FOVar 202))
                 (FOlookup 28 (FOVar 192) (FOVar 193) (FOVar 194) (FOVar 195) (FOVar 196)
                   (FOVar 197) (FOVar 198) (FOVar 199) (FOVar 200) (FOVar 201) (FOVar 202)
                   tg3 a13 a23 a33 r3))) by wk_in
  end.
  apply (FOPrH_merge3_elim n _ (FOVar 130) (FOVar 131) (FOVar 140) (FOVar 151) (FOVar 152)
           (FOVar 161) (FOVar 192) (FOVar 193) (FOVar 202) 162 163 164 165); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 132) (FOVar 133) (FOVar 140) (FOVar 153) (FOVar 154)
           (FOVar 161) (FOVar 194) (FOVar 195) (FOVar 202) 166 167 168 169); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 134) (FOVar 135) (FOVar 140) (FOVar 155) (FOVar 156)
           (FOVar 161) (FOVar 196) (FOVar 197) (FOVar 202) 170 171 172 173); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 136) (FOVar 137) (FOVar 140) (FOVar 157) (FOVar 158)
           (FOVar 161) (FOVar 198) (FOVar 199) (FOVar 202) 174 175 176 177); [tab_side.. |].
  apply (FOPrH_merge3_elim n _ (FOVar 138) (FOVar 139) (FOVar 140) (FOVar 159) (FOVar 160)
           (FOVar 161) (FOVar 200) (FOVar 201) (FOVar 202) 178 179 180 181); [tab_side.. |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (HM : FOPrH n Gc (FOTABM3 (FOtabv 130) (FOtabv 151) (FOtabv 192) FOtabM3));
    [ unfold FOTABM3; apply FOPrH_and_intro; [wk_in|]; apply FOPrH_and_intro; [wk_in|];
      apply FOPrH_and_intro; [wk_in|]; apply FOPrH_and_intro; wk_in |];
    assert (HC1 : FOctx_avoid Gc 18 122) by tab_side;
    assert (HC2 : FOctx_avoid Gc 420 500) by tab_side;
    assert (K1' : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 130) (FOVar 131) (FOVar 132)
                   (FOVar 133) (FOVar 134) (FOVar 135) (FOVar 136) (FOVar 137) (FOVar 138)
                   (FOVar 139) (FOVar 140))
                 (FOlookup 28 (FOVar 130) (FOVar 131) (FOVar 132) (FOVar 133) (FOVar 134)
                   (FOVar 135) (FOVar 136) (FOVar 137) (FOVar 138) (FOVar 139) (FOVar 140)
                   tg1 a11 a21 a31 r1))) by wk K1;
    assert (K2' : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 151) (FOVar 152) (FOVar 153)
                   (FOVar 154) (FOVar 155) (FOVar 156) (FOVar 157) (FOVar 158) (FOVar 159)
                   (FOVar 160) (FOVar 161))
                 (FOlookup 28 (FOVar 151) (FOVar 152) (FOVar 153) (FOVar 154) (FOVar 155)
                   (FOVar 156) (FOVar 157) (FOVar 158) (FOVar 159) (FOVar 160) (FOVar 161)
                   tg2 a12 a22 a32 r2))) by wk K2;
    assert (K3' : FOPrH n Gc (FOAnd (FOTBLVALID 18 (FOVar 192) (FOVar 193) (FOVar 194)
                   (FOVar 195) (FOVar 196) (FOVar 197) (FOVar 198) (FOVar 199) (FOVar 200)
                   (FOVar 201) (FOVar 202))
                 (FOlookup 28 (FOVar 192) (FOVar 193) (FOVar 194) (FOVar 195) (FOVar 196)
                   (FOVar 197) (FOVar 198) (FOVar 199) (FOVar 200) (FOVar 201) (FOVar 202)
                   tg3 a13 a23 a33 r3))) by wk K3
  end.
  clear K1 K2 K3.
  assert (HavT : FOtms_avoid (FOtab_terms (FOtabv 130) ++ FOtab_terms (FOtabv 151) ++
                              FOtab_terms (FOtabv 192) ++ FOtab_terms FOtabM3) 420 500)
    by (unfold FOtabM3; tab_side).
  destruct (FOPrH_tabm3_mono n _ _ _ _ _ HM eq_refl HC2 HavT) as (Hm1 & Hm2 & Hm3).
  pose proof (FOPrH_tblvalid_merge n _ (FOtabv 130) (FOtabv 151) (FOtabv 192) FOtabM3 390 391
                HM eq_refl (FOPrH_and_l _ _ _ _ K1') (FOPrH_and_l _ _ _ _ K2')
                (FOPrH_and_l _ _ _ _ K3')
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(tab_side) ltac:(tab_side) HC1 HC2
                ltac:(unfold FOtabM3; tab_side) ltac:(unfold FOtabM3; tab_side)
                ltac:(unfold FOtabM3; tab_side) ltac:(unfold FOtabM3; tab_side)) as HVM.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n _ 28 (FOtabv 130) FOtabM3 tg1 a11 a21 a31 r1
                Hm1 ltac:(lia) ltac:(tab_side) HC2 ltac:(unfold FOtabM3; tab_side)
                ltac:(unfold FOtabM3; tab_side))
                (FOPrH_and_r _ _ _ _ K1')) as L1.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n _ 28 (FOtabv 151) FOtabM3 tg2 a12 a22 a32 r2
                Hm2 ltac:(lia) ltac:(tab_side) HC2 ltac:(unfold FOtabM3; tab_side)
                ltac:(unfold FOtabM3; tab_side))
                (FOPrH_and_r _ _ _ _ K2')) as L2.
  pose proof (FOPrH_mp _ _ _ _ (FOPrH_lookup_tr' n _ 28 (FOtabv 192) FOtabM3 tg3 a13 a23 a33 r3
                Hm3 ltac:(lia) ltac:(tab_side) HC2 ltac:(unfold FOtabM3; tab_side)
                ltac:(unfold FOtabM3; tab_side))
                (FOPrH_and_r _ _ _ _ K3')) as L3.
  apply (FOPrH_tblex3_intro n _ FOtabM3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HVM L1 L2 L3).
  unfold FOtabM3. tab_side.
Qed.

(** ** One-line derivations whose check reads the table.

    The table holds the guard row of [d] and two further rows; the
    justification code pairs the tag with the payload [pl]. *)

Lemma FOPrH_one_line3 : forall n G cores d tgn pl r0 tg' a1' a2' a3' r'
    tg'' a1'' a2'' a3'' r'',
  FOctx_avoid G 2 500 ->
  FOtms_avoid [d; pl; r0; tg'; a1'; a2'; a3'; r'; tg''; a1''; a2''; a3''; r''] 2 500 ->
  FOPrH n G (FOTBLEX3 (FOnumeral 3) (FOSucc d) FOZero d r0 tg' a1' a2' a3' r'
               tg'' a1'' a2'' a3'' r'') ->
  (forall G', (forall X, In X G -> In X G') ->
     FOPrH n G' (FOlookup 28 (FOVar 260) (FOVar 261) (FOVar 262) (FOVar 263) (FOVar 264)
                   (FOVar 265) (FOVar 266) (FOVar 267) (FOVar 268) (FOVar 269) (FOVar 270)
                   tg' a1' a2' a3' r') ->
     FOPrH n G' (FOlookup 28 (FOVar 260) (FOVar 261) (FOVar 262) (FOVar 263) (FOVar 264)
                   (FOVar 265) (FOVar 266) (FOVar 267) (FOVar 268) (FOVar 269) (FOVar 270)
                   tg'' a1'' a2'' a3'' r'') ->
     FOPrH n G' (FOJDISJ 20 cores (FOVar 260) (FOVar 261) (FOVar 262) (FOVar 263)
                   (FOVar 264) (FOVar 265) (FOVar 266) (FOVar 267) (FOVar 268) (FOVar 269)
                   (FOVar 270) d d FOZero d (FOnumeral tgn) pl)) ->
  FOPrH n G (FOPRMATx cores d).
Proof.
  intros n G cores d tgn pl r0 tg' a1' a2' a3' r' tg'' a1'' a2'' a3'' r'' HG Hd HE HJ.
  refine (FOPrH_mp _ _ _ _ _ HE).
  apply (FOPrH_tblex3_elim n G _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 260); [lia | lia
    | intros w H1 H2; apply HG; lia | intros w H1 H2; free_fm | avoid_tms | avoid_tms |].
  cbn [Nat.add].
  lazymatch goal with |- FOPrH _ (_ ++ [?X]) _ =>
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_last n G X)) as VT;
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _ (FOPrH_last n G X))) as LK1;
    pose proof (FOPrH_and_l _ _ _ _ (FOPrH_and_r _ _ _ _
                  (FOPrH_and_r _ _ _ _ (FOPrH_last n G X)))) as LK2;
    pose proof (FOPrH_and_r _ _ _ _ (FOPrH_and_r _ _ _ _
                  (FOPrH_and_r _ _ _ _ (FOPrH_last n G X)))) as LK3
  end.
  apply (FOPrH_cpair_elim n _ (FOnumeral tgn) pl 280); [ctx_list | avoid_tms | lia | lia
    | free_ctx | free_fm | avoid_tms |].
  lazymatch goal with |- FOPrH _ ?Gc _ =>
    assert (CP : FOPrH n Gc (FOcpairF (FOnumeral tgn) pl (FOVar 280))) by apply FOPrH_last;
    assert (Hinc : forall X, In X G -> In X Gc)
      by (intros X HX; repeat (apply in_or_app; left); exact HX);
    pose proof (HJ Gc Hinc (FOPrH_weak_app _ _ _ _ LK2) (FOPrH_weak_app _ _ _ _ LK3)) as HJ'
  end.
  destruct (FOPrH_cpair_le_cf n _ (FOnumeral tgn) pl (FOVar 280) ltac:(avoid_tms) CP)
    as [Ltg Lpl].
  apply (FOPrH_PRMAT_intro n _ cores d (FOVar 260) (FOVar 261) (FOVar 262) (FOVar 263)
           (FOVar 264) (FOVar 265) (FOVar 266) (FOVar 267) (FOVar 268) (FOVar 269)
           (FOVar 270) d d (FOVar 280) (FOVar 280) (FOSucc FOZero));
    [avoid_tms | avoid_tms |].
  unfold FOPRDERp. cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen].
  apply FOPrH_and_intro; [wk VT|].
  apply FOPrH_and_intro.
  { apply (FOPrH_bex_intro_t _ _ 18 (FOSucc FOZero) FOZero); [lia | lia | avoid_tm
      | avoid_tm | avoid_tm | avoid_tm | | ok0 |].
    - apply FOPrH_le_refl. avoid_tm.
    - autorewrite with fosubst. subst_avoid_h Hd.
      apply FOPrH_and_intro; [apply FOPrH_ring; fo_ring|].
      apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms]. }
  apply FOPrH_and_intro.
  - apply (FOPrH_ball_one _ _ 18 _ 250); [| ok0 | lia | lia | lia | lia | lia
      | free_ctx | free_ctx | free_ctx | free_fm | free_fm].
    autorewrite with fosubst. subst_avoid_h Hd.
    apply (FOPrH_JUSTCK_intro_t _ _ 20 cores _ _ _ _ _ _ _ _ _ _ _ d d
             (FOVar 280) (FOVar 280) FOZero d (FOVar 280));
      [lia | lia | avoid_tms | avoid_tms | avoid_tms | avoid_tms | | | | |].
    + apply FOPrH_le_refl. avoid_tm.
    + apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms].
    + apply FOPrH_le_refl. avoid_tm.
    + apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms].
    + apply (FOPrH_CHK_intro_t _ _ 20 cores _ _ _ _ _ _ _ _ _ _ _ d d FOZero d
               (FOVar 280) (FOnumeral tgn) pl);
        [lia | avoid_tms | avoid_tms | avoid_tms | avoid_tms | | | |].
      * apply FOPrH_le_succ_of_le; [exact Ltg | avoid_tms].
      * apply FOPrH_le_succ_of_le; [exact Lpl | avoid_tms].
      * exact CP.
      * exact HJ'.
  - apply (FOPrH_ball_one _ _ 18 _ 250); [| ok0 | lia | lia | lia | lia | lia
      | free_ctx | free_ctx | free_ctx | free_fm | free_fm].
    autorewrite with fosubst. subst_avoid_h Hd.
    apply (FOPrH_GUARDC_intro_t _ _ 20 (FOtabv 260) d d FOZero d r0);
      [lia | tab_avoid | avoid_tms | avoid_tms | tab_avoid | | | |].
    + apply FOPrH_le_refl. avoid_tm.
    + apply FOPrH_beta_self0; [lia | lia | avoid_tms | avoid_tms].
    + cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen FOtabv Nat.add].
      apply FOPrH_le_succ_of_le; [|avoid_tms].
      apply (FOPrH_lookup_res_le _ _ 28 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (FOPrH_weak_app _ _ _ _ LK1));
        [lia | lia | ctx_list | avoid_tms | avoid_tms].
    + cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen FOtabv Nat.add].
      exact (FOPrH_weak_app _ _ _ _ LK1).
Qed.

(** ** Code patterns introduced at a low base. *)

Lemma FOPrH_patf_pair_intro_lo : forall n G B env a b d u w,
  FOPrH n G (FOcpairF u w d) ->
  FOPrH n G (FOPATF (B + 4) env a u) ->
  FOPrH n G (FOPATF (B + 4 + 4 * cpat_pairs a) env b w) ->
  2 <= B -> B + cpat_span (CPair a b) <= 420 ->
  FOtms_avoid (d :: u :: w :: env) B (B + cpat_span (CPair a b)) ->
  FOtms_avoid [d; u; w] 420 500 ->
  FOPrH n G (FOPATF B env (CPair a b) d).
Proof.
  intros n G B env a b d u w HC Ha Hb HB HB' Hav Hav2.
  pose proof (cpat_span_le a) as Hsa. cbn [cpat_span] in Hav, HB'.
  destruct (FOPrH_cpair_le_cf n G u w d ltac:(avoid_tms) HC) as [Hud Hwd].
  cbn [FOPATF].
  apply (FOPrH_bex_intro_t _ _ B (FOSucc d) u); [lia | lia | avoid_tm | avoid_tm | avoid_tm
    | avoid_tm | apply FOPrH_le_succ_of_le; [exact Hud | avoid_tms] | | ].
  - apply FOsubst_ok_bex; [apply (Hav u); [right; left; reflexivity | lia | lia]
                         | apply (Hav u); [right; left; reflexivity | lia | lia] |].
    apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
    apply FOsubst_ok_and; apply FOsubst_ok_PATF;
      apply (FOtm_avoid_sub u B (B + (4 + 4 * cpat_pairs a + cpat_span b)));
      try (apply Hav; right; left; reflexivity); lia.
  - rewrite FOsubst_f_bex by lia. rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_and,
      !FOsubst_f_PATF by lia.
    rewrite FOsubst_t_succ, FOsubst_t_var_eq', !FOsubst_t_var_ne by lia.
    rewrite (FOsubst_t_not_in d B _ (Hav d (or_introl eq_refl) B ltac:(lia) ltac:(lia))).
    rewrite (FOsubst_map_avoid B u env).
    2:{ intros t Ht. apply (Hav t); [right; right; right; exact Ht | lia | lia]. }
    apply (FOPrH_bex_intro_t _ _ (B + 2) (FOSucc d) w); [lia | lia | avoid_tm | avoid_tm
      | avoid_tm | avoid_tm | apply FOPrH_le_succ_of_le; [exact Hwd | avoid_tms] | | ].
    + apply FOsubst_ok_and; [apply FOsubst_ok_cpairF|].
      apply FOsubst_ok_and; apply FOsubst_ok_PATF;
        apply (FOtm_avoid_sub w B (B + (4 + 4 * cpat_pairs a + cpat_span b)));
        try (apply Hav; right; right; left; reflexivity); lia.
    + rewrite FOsubst_f_and, FOsubst_f_cpairF, FOsubst_f_and, !FOsubst_f_PATF by lia.
      rewrite FOsubst_t_var_eq'. rewrite ?FOsubst_t_var_ne by lia.
      rewrite (FOsubst_t_not_in d (B + 2) _ (Hav d (or_introl eq_refl) (B + 2) ltac:(lia)
                                               ltac:(lia))).
      rewrite (FOsubst_t_not_in u (B + 2) _ (Hav u (or_intror (or_introl eq_refl)) (B + 2)
                                               ltac:(lia) ltac:(lia))).
      rewrite (FOsubst_map_avoid (B + 2) w env).
      2:{ intros t Ht. apply (Hav t); [right; right; right; exact Ht | lia | lia]. }
      apply FOPrH_and_intro; [exact HC|]. apply FOPrH_and_intro; [exact Ha | exact Hb].
Qed.

Lemma FOPrH_patf_lit : forall n G B env k, FOPrH n G (FOPATF B env (CLit k) (FOnumeral k)).
Proof. intros. cbn [FOPATF]. apply FOPrH_thm. apply FOProvesTn_EqRefl. Qed.

Lemma FOPrH_patf_slot : forall n G B env i,
  FOPrH n G (FOPATF B env (CVarP i) (nth i env FOZero)).
Proof. intros. cbn [FOPATF]. apply FOPrH_thm. apply FOProvesTn_EqRefl. Qed.

(** ** The substitution justification at the checker's base. *)

Ltac jbex s H :=
  apply (FOPrH_bex_intro_t _ _ _ _ s);
  [ lia | lia | avoid_tm | avoid_tm | avoid_tm | avoid_tm |
  | let V := fresh "V" in assert (V : FOtm_avoid s 36 110) by avoid_tm;
    solve [auto 100 with fook]
  | autorewrite with fosubst; subst_avoid_h H ].

Lemma FOPrH_jsubst_intro : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl x s a b,
  FOPrH n G (FOcpairF x s pl) ->
  FOPrH n G (FOle a vd) -> FOPrH n G (FOle b vd) ->
  FOPrH n G (FOPATF 44 [x; a; b] pat vd) ->
  FOPrH n G (FOlookup 28 ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 4) x s a
               (FOnumeral 1)) ->
  FOPrH n G (FOlookup 28 ct dt c1 d1 c2 d2 c3 d3 cr dr len (FOnumeral 3) x s a b) ->
  44 + cpat_span pat <= 66 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; vd; pl; x; s; a; b] 28 110 ->
  FOtms_avoid [ct; dt; c1; d1; c2; d2; c3; d3; cr; dr; len; vd; pl; x; s; a; b] 420 500 ->
  FOPrH n G (FOJSUBST 36 ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl).
Proof.
  intros n G ct dt c1 d1 c2 d2 c3 d3 cr dr len pat vd pl x s a b HC Ha Hb HP L4 L3 Hsp
    Hav Hav2.
  destruct (FOPrH_cpair_le_cf n G x s pl ltac:(avoid_tms) HC) as [Hx Hs].
  unfold FOJSUBST.
  jbex x Hav; [apply FOPrH_le_succ_of_le; [exact Hx | avoid_tms]|].
  jbex s Hav; [apply FOPrH_le_succ_of_le; [exact Hs | avoid_tms]|].
  apply FOPrH_and_intro; [exact HC|].
  jbex a Hav; [apply FOPrH_le_succ_of_le; [exact Ha | avoid_tms]|].
  jbex b Hav; [apply FOPrH_le_succ_of_le; [exact Hb | avoid_tms]|].
  apply FOPrH_and_intro; [exact HP|].
  apply FOPrH_and_intro.
  - apply (FOPrH_lookup_rebase n G 28 66 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L4);
      [lia | lia | lia | lia | lia | avoid_tms | avoid_tms].
  - apply (FOPrH_lookup_rebase n G 28 88 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L3);
      [lia | lia | lia | lia | lia | avoid_tms | avoid_tms].
Qed.

Lemma FOPrH_jdisj_allelim : forall n G cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd pl,
  FOPrH n G (FOJSUBST 36 ct dt c1 d1 c2 d2 c3 d3 cr dr len cpatAllElim vd pl) ->
  FOPrH n G (FOJDISJ 20 cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd
               (FOnumeral 2) pl).
Proof.
  intros. unfold FOJDISJ.
  apply FOPrH_or_intro_r. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_thm; apply FOProvesTn_EqRefl | exact H].
Qed.

Lemma FOPrH_jdisj_exintro : forall n G cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd pl,
  FOPrH n G (FOJSUBST 36 ct dt c1 d1 c2 d2 c3 d3 cr dr len cpatExIntro vd pl) ->
  FOPrH n G (FOJDISJ 20 cores ct dt c1 d1 c2 d2 c3 d3 cr dr len cs ds i vd
               (FOnumeral 3) pl).
Proof.
  intros. unfold FOJDISJ.
  apply FOPrH_or_intro_r. apply FOPrH_or_intro_r. apply FOPrH_or_intro_r.
  apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [apply FOPrH_thm; apply FOProvesTn_EqRefl | exact H].
Qed.

(** ** One-line derivations of substitution instances.

    [d] codes [forall x A -> B] (tag [2]) or [B -> exists x A] (tag
    [3]), with [a], [b] the codes of [A], [B]; the table holds the guard
    row of [d], the capture test of [s] for [x] in [a] and the
    substitution row giving [b]; the payload pairs [x] and [s]. *)

Lemma FOPrH_subst_line : forall n G cores d pat tgn pl r0 x s a b,
  (pat = cpatAllElim /\ tgn = 2) \/ (pat = cpatExIntro /\ tgn = 3) ->
  FOctx_avoid G 2 500 ->
  FOtms_avoid [d; pl; r0; x; s; a; b] 2 500 ->
  FOPrH n G (FOTBLEX3 (FOnumeral 3) (FOSucc d) FOZero d r0
               (FOnumeral 4) x s a (FOnumeral 1) (FOnumeral 3) x s a b) ->
  FOPrH n G (FOcpairF x s pl) ->
  FOPrH n G (FOle a d) -> FOPrH n G (FOle b d) ->
  FOPrH n G (FOPATF 44 [x; a; b] pat d) ->
  FOPrH n G (FOPRMATx cores d).
Proof.
  intros n G cores d pat tgn pl r0 x s a b Hpt HG Hav HT HC Ha Hb HP.
  apply (FOPrH_one_line3 n G cores d tgn pl r0 (FOnumeral 4) x s a (FOnumeral 1)
           (FOnumeral 3) x s a b HG ltac:(avoid_tms) HT).
  intros G' Hinc L4 L3.
  assert (J : FOPrH n G' (FOJSUBST 36 (FOVar 260) (FOVar 261) (FOVar 262) (FOVar 263)
                            (FOVar 264) (FOVar 265) (FOVar 266) (FOVar 267) (FOVar 268)
                            (FOVar 269) (FOVar 270) pat d pl)).
  { apply (FOPrH_jsubst_intro n G' _ _ _ _ _ _ _ _ _ _ _ pat d pl x s a b);
      [apply (FOPrH_weaken n G G' _ Hinc HC) | apply (FOPrH_weaken n G G' _ Hinc Ha)
      | apply (FOPrH_weaken n G G' _ Hinc Hb) | apply (FOPrH_weaken n G G' _ Hinc HP)
      | exact L4 | exact L3 | | avoid_tms | avoid_tms].
    destruct Hpt as [[-> _]|[-> _]]; vm_compute; lia. }
  destruct Hpt as [[-> ->]|[-> ->]].
  - apply FOPrH_jdisj_allelim. exact J.
  - apply FOPrH_jdisj_exintro. exact J.
Qed.

(** ** Bounds from pairing. *)

Lemma FOPrH_cpair_lt_l : forall n G a b c,
  FOPrH n G (FOcpairF a b c) -> FOtms_avoid [a; b; c] 420 500 ->
  FOPrH n G (FOle (FOSucc a) (FOSucc c)).
Proof.
  intros n G a b c H Hav.
  destruct (FOPrH_cpair_le_cf n G a b c Hav H) as [Ha _].
  apply FOPrH_le_succ_of_le; [exact Ha | avoid_tms].
Qed.

Lemma FOPrH_cpair_lt_r : forall n G a b c,
  FOPrH n G (FOcpairF a b c) -> FOtms_avoid [a; b; c] 420 500 ->
  FOPrH n G (FOle (FOSucc b) (FOSucc c)).
Proof.
  intros n G a b c H Hav.
  destruct (FOPrH_cpair_le_cf n G a b c Hav H) as [_ Hb].
  apply FOPrH_le_succ_of_le; [exact Hb | avoid_tms].
Qed.

(** ** The binary substitution step.

    [tc] codes a binary node [cpair ktag (cpair a b)]; the table maps
    [a], [b] to [a'], [b'] under tag [lktag]; the result [r] is
    [cpair rtag (cpair a' b')]. *)

Lemma FOPrH_substbin_intro : forall n G T x sc tc r ktag lktag rtag p a b a' b' p',
  FOPrH n G (FOcpairF (FOnumeral ktag) p tc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral lktag) x sc a a') ->
  FOPrH n G (FOlookupT 28 T (FOnumeral lktag) x sc b b') ->
  FOPrH n G (FOcpairF a' b' p') -> FOPrH n G (FOcpairF (FOnumeral rtag) p' r) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; tc; r; p; a; b; a'; b'; p']) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; tc; r; p; a; b; a'; b'; p']) 420 500 ->
  FOPrH n G (FOSTEP_substbin 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc tc r ktag lktag rtag).
Proof.
  intros n G T x sc tc r ktag lktag rtag p a b a' b' p' Hk Hp La Lb Hp' Hr Hav Hav2.
  destruct T as [ct dt c1 d1 c2 d2 c3 d3 cr dr len].
  unfold FOlookupT, FOtab_terms in *.
  cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app] in *.
  unfold FOSTEP_substbin.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex a; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex b; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  destruct (FOPrH_cpair_le_cf n G (FOnumeral rtag) p' r ltac:(avoid_tms) Hr) as [_ Lp'].
  destruct (FOPrH_cpair_le_cf n G a' b' p' ltac:(avoid_tms) Hp') as [La' Lb'].
  row_bex a'.
  { apply FOPrH_le_succ_of_le; [|avoid_tms].
    exact (FOPrH_le_trans _ _ _ _ _ La' Lp' ltac:(avoid_tms)). }
  row_bex b'.
  { apply FOPrH_le_succ_of_le; [|avoid_tms].
    exact (FOPrH_le_trans _ _ _ _ _ Lb' Lp' ltac:(avoid_tms)). }
  apply FOPrH_and_intro.
  { apply (FOPrH_lookup_rebase n G 28 60 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ La);
      [lia | lia | lia | lia | lia | avoid_tms | avoid_tms]. }
  apply FOPrH_and_intro.
  { apply (FOPrH_lookup_rebase n G 28 82 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Lb);
      [lia | lia | lia | lia | lia | avoid_tms | avoid_tms]. }
  row_bex p'; [apply FOPrH_le_succ_of_le; [exact Lp' | avoid_tms]|].
  apply FOPrH_and_intro; [exact Hp' | exact Hr].
Qed.

(** ** Step clauses introduced from component facts.

    Each lemma builds one step formula at base [50], the base the
    dispatch uses, from the pairing facts of the node and the rows of
    its children looked up at base [28]. *)

Ltac tab_open T :=
  destruct T as [ct dt c1 d1 c2 d2 c3 d3 cr dr len];
  unfold FOlookupT, FOtab_terms in *;
  cbn [tct tdt tc1 td1 tc2 td2 tc3 td3 tcr tdr tlen app] in *.

Ltac rebase_to B' L :=
  apply (FOPrH_lookup_rebase _ _ 28 B' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ L);
  [lia | lia | lia | lia | lia | avoid_tms | avoid_tms].

Lemma FOPrH_stepbin_one : forall n G T w pc k tg p a b,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral tg) w a FOZero (FOnumeral 1)) ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; p; a; b]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; p; a; b]) 420 500 ->
  FOPrH n G (FOSTEP_bin 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w pc (FOnumeral 1) k tg).
Proof.
  intros n G T w pc k tg p a b Hk Hp La Hav Hav2. tab_open T.
  unfold FOSTEP_bin.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex a; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex b; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [rebase_to 56 La | apply FOPrH_refl].
Qed.

Lemma FOPrH_stepbin_zero : forall n G T w pc r k tg p a b,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral tg) w a FOZero FOZero) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral tg) w b FOZero r) ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; r; p; a; b]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; r; p; a; b]) 420 500 ->
  FOPrH n G (FOSTEP_bin 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w pc r k tg).
Proof.
  intros n G T w pc r k tg p a b Hk Hp La Lb Hav Hav2. tab_open T.
  unfold FOSTEP_bin.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex a; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex b; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [rebase_to 56 La | rebase_to 78 Lb].
Qed.

Lemma FOPrH_quant0_eq : forall n G T w pc k tg p y bb,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FOEq y w) ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; p; y; bb]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; p; y; bb]) 420 500 ->
  FOPrH n G (FOSTEP_quant0 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w pc FOZero k tg).
Proof.
  intros n G T w pc k tg p y bb Hk Hp E Hav Hav2. tab_open T.
  unfold FOSTEP_quant0.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

Lemma FOPrH_quant0_ne : forall n G T w pc r k tg p y bb,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y w)) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral tg) w bb FOZero r) ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; r; p; y; bb]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [w; pc; r; p; y; bb]) 420 500 ->
  FOPrH n G (FOSTEP_quant0 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w pc r k tg).
Proof.
  intros n G T w pc r k tg p y bb Hk Hp E L Hav Hav2. tab_open T.
  unfold FOSTEP_quant0.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [exact E | rebase_to 56 L].
Qed.

Lemma FOPrH_substquant_eq : forall n G T x sc pc k p y bb,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FOEq y x) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p; y; bb]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p; y; bb]) 420 500 ->
  FOPrH n G (FOSTEP_substquant 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc pc k).
Proof.
  intros n G T x sc pc k p y bb Hk Hp E Hav Hav2. tab_open T.
  unfold FOSTEP_substquant.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

Lemma FOPrH_substquant_ne : forall n G T x sc pc r k p y bb bb' p',
  1 <= k ->
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y x)) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral 3) x sc bb bb') ->
  FOPrH n G (FOcpairF y bb' p') -> FOPrH n G (FOcpairF (FOnumeral k) p' r) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; r; p; y; bb; bb'; p']) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; r; p; y; bb; bb'; p']) 420 500 ->
  FOPrH n G (FOSTEP_substquant 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc r k).
Proof.
  intros n G T x sc pc r k p y bb bb' p' Hk1 Hk Hp E L Hp' Hr Hav Hav2. tab_open T.
  assert (Lp' : FOPrH n G (FOle (FOSucc p') r)).
  { destruct k as [|k']; [lia|].
    exact (FOPrH_cpair_lt n G (FOnumeral k') p' r Hr ltac:(avoid_tms)). }
  destruct (FOPrH_cpair_le_cf n G y bb' p' ltac:(avoid_tms) Hp') as [_ Lb'].
  unfold FOSTEP_substquant.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [exact E|].
  row_bex bb'.
  { apply (FOPrH_le_trans n G (FOSucc bb') (FOSucc p') r); [| exact Lp' | avoid_tms].
    apply FOPrH_le_succ_of_le; [exact Lb' | avoid_tms]. }
  apply FOPrH_and_intro; [rebase_to 58 L|].
  row_bex p'; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hr ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp' | exact Hr].
Qed.

Lemma FOPrH_subokbin_one : forall n G T x sc pc r p a b,
  FOPrH n G (FOcpairF (FOnumeral 2) p pc) -> FOPrH n G (FOcpairF a b p) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral 4) x sc a (FOnumeral 1)) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral 4) x sc b r) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; r; p; a; b]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; r; p; a; b]) 420 500 ->
  FOPrH n G (FOSTEP_subokbin 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc r).
Proof.
  intros n G T x sc pc r p a b Hk Hp La Lb Hav Hav2. tab_open T.
  unfold FOSTEP_subokbin.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex a; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex b; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [rebase_to 56 La | rebase_to 78 Lb].
Qed.

Lemma FOPrH_subokquant_eq : forall n G T x sc pc k p y bb,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FOEq y x) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p; y; bb]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p; y; bb]) 420 500 ->
  FOPrH n G (FOSTEP_subokquant 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc (FOnumeral 1) k).
Proof.
  intros n G T x sc pc k p y bb Hk Hp E Hav Hav2. tab_open T.
  unfold FOSTEP_subokquant.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

Lemma FOPrH_subokquant_nf : forall n G T x sc pc k p y bb,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y x)) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral 1) x bb FOZero FOZero) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p; y; bb]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p; y; bb]) 420 500 ->
  FOPrH n G (FOSTEP_subokquant 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc (FOnumeral 1) k).
Proof.
  intros n G T x sc pc k p y bb Hk Hp E L Hav Hav2. tab_open T.
  unfold FOSTEP_subokquant.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [exact E|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [rebase_to 56 L | apply FOPrH_refl].
Qed.

Lemma FOPrH_subokquant_fr : forall n G T x sc pc r k p y bb,
  FOPrH n G (FOcpairF (FOnumeral k) p pc) -> FOPrH n G (FOcpairF y bb p) ->
  FOPrH n G (FONeg (FOEq y x)) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral 1) x bb FOZero (FOnumeral 1)) ->
  FOPrH n G (FOlookupT 28 T FOZero y sc FOZero FOZero) ->
  FOPrH n G (FOlookupT 28 T (FOnumeral 4) x sc bb r) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; r; p; y; bb]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; r; p; y; bb]) 420 500 ->
  FOPrH n G (FOSTEP_subokquant 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc r k).
Proof.
  intros n G T x sc pc r k p y bb Hk Hp E L1 L0 L4 Hav Hav2. tab_open T.
  unfold FOSTEP_subokquant.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hk ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hk|].
  row_bex y; [exact (FOPrH_cpair_lt_l _ _ _ _ _ Hp ltac:(avoid_tms))|].
  row_bex bb; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hp ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hp|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [exact E|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [rebase_to 56 L1|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [rebase_to 78 L0 | rebase_to 100 L4].
Qed.

(** ** Variable leaves. *)

Lemma FOPrH_step2_var_eq : forall n G T x sc tc y,
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FOEq y x) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; tc; y]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; tc; y]) 420 500 ->
  FOPrH n G (FOSTEP2 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc tc sc).
Proof.
  intros n G T x sc tc y Hc E Hav Hav2. tab_open T.
  unfold FOSTEP2. apply FOPrH_or_intro_l.
  row_bex y; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hc ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hc|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

Lemma FOPrH_step2_var_ne : forall n G T x sc tc y,
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FONeg (FOEq y x)) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; tc; y]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; tc; y]) 420 500 ->
  FOPrH n G (FOSTEP2 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc tc tc).
Proof.
  intros n G T x sc tc y Hc E Hav Hav2. tab_open T.
  unfold FOSTEP2. apply FOPrH_or_intro_l.
  row_bex y; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hc ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hc|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

Lemma FOPrH_step0_var_eq : forall n G T w tc y,
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FOEq y w) ->
  FOtms_avoid (FOtab_terms T ++ [w; tc; y]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [w; tc; y]) 420 500 ->
  FOPrH n G (FOSTEP0 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w tc (FOnumeral 1)).
Proof.
  intros n G T w tc y Hc E Hav Hav2. tab_open T.
  unfold FOSTEP0. apply FOPrH_or_intro_l.
  row_bex y; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hc ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hc|].
  apply FOPrH_or_intro_l. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

Lemma FOPrH_step0_var_ne : forall n G T w tc y,
  FOPrH n G (FOcpairF FOZero y tc) -> FOPrH n G (FONeg (FOEq y w)) ->
  FOtms_avoid (FOtab_terms T ++ [w; tc; y]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [w; tc; y]) 420 500 ->
  FOPrH n G (FOSTEP0 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) w tc FOZero).
Proof.
  intros n G T w tc y Hc E Hav Hav2. tab_open T.
  unfold FOSTEP0. apply FOPrH_or_intro_l.
  row_bex y; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hc ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hc|].
  apply FOPrH_or_intro_r. apply FOPrH_and_intro; [exact E | apply FOPrH_refl].
Qed.

(** ** Leaf clauses of the equation and falsum codes. *)

Lemma FOPrH_step4_eq : forall n G T x sc pc p,
  FOPrH n G (FOcpairF FOZero p pc) ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p]) 20 128 ->
  FOtms_avoid (FOtab_terms T ++ [x; sc; pc; p]) 420 500 ->
  FOPrH n G (FOSTEP4 50 (tct T) (tdt T) (tc1 T) (td1 T) (tc2 T) (td2 T) (tc3 T)
               (td3 T) (tcr T) (tdr T) (tlen T) x sc pc (FOnumeral 1)).
Proof.
  intros n G T x sc pc p Hc Hav Hav2. tab_open T.
  unfold FOSTEP4. apply FOPrH_or_intro_l.
  row_bex p; [exact (FOPrH_cpair_lt_r _ _ _ _ _ Hc ltac:(avoid_tms))|].
  apply FOPrH_and_intro; [exact Hc | apply FOPrH_refl].
Qed.

Lemma FOPrH_step4_false : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc,
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero pc) ->
  FOPrH n G (FOSTEP4 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc (FOnumeral 1)).
Proof.
  intros. unfold FOSTEP4. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [assumption | apply FOPrH_refl].
Qed.

Lemma FOPrH_step3_false : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc,
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero pc) ->
  FOPrH n G (FOSTEP3 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len x sc pc pc).
Proof.
  intros. unfold FOSTEP3. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [assumption | apply FOPrH_refl].
Qed.

Lemma FOPrH_step1_false : forall n G ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc,
  FOPrH n G (FOcpairF (FOnumeral 1) FOZero pc) ->
  FOPrH n G (FOSTEP1 50 ct dt c1 d1 c2 d2 c3 d3 cr dr len w pc FOZero).
Proof.
  intros. unfold FOSTEP1. apply FOPrH_or_intro_r. apply FOPrH_or_intro_l.
  apply FOPrH_and_intro; [assumption | apply FOPrH_refl].
Qed.
