From stdpp Require Import fin_maps.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export proph_map invariants wsat.
From iris.program_logic Require Import atomic.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris_cf.cf_lang Require Export lang.
From iris_cf.cf_lang Require Import notation.
Set Default Proof Using "Type".

Class heapG Σ := HeapG {
  heapG_invG : invG Σ;
  heapG_gen_heapG :> gen_heapG loc val Σ;
  heapG_proph_mapG :> proph_mapG proph_id (val * val) Σ
}.

Instance heapG_irisG `{!heapG Σ} : irisG cf_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs _ :=
    (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id))%I;
  fork_post _ := True%I;
}.

(* MARK: weakest pre with multi-post *)
Section multi_post.

Context `{!heapG Σ}.

Definition multi_post (φn φb φc φr : val -> iPropI Σ) v : iPropI Σ :=
  match v with
  | SVal v => φn v
  | SBreak v => φb v
  | SContinue => φc $ LitV LitUnit
  | SReturn v => φr v
  end.

Definition top (v:val) : iPropI Σ := bi_pure True.
Definition bot (v:val) : iPropI Σ := bi_pure False.

Notation "'WP' e {{ φn } } {{ φb } } {{ φc } } {{ φr } }" := 
  (wp NotStuck ⊤ e%E (multi_post φn φb φc φr)) (at level 20, e, φn, φb, φc, φr at level 200).

Notation "'{{' P } } e {{ φn } } {{ φb } } {{ φc } } {{ φr } }" :=
  (uPred_persistently (P -∗ WP e {{ φn }} {{ φb }} {{ φc }} {{ φr }})) (at level 20).

(* MARK: control flow terminals *)
Lemma tac_wp_break v φ:
  (φ v) ⊢
  WP (EBreak $ Val v) {{ bot }} {{ φ }} {{ bot }} {{ bot }}.
Proof.
  assert ((EBreak $ Val v) = (of_sval $ SBreak v)); auto.
  rewrite H.
  iIntros "Hφ".
  rewrite wp_unfold /wp_pre to_of_val.
  auto.
Qed.

Lemma tac_wp_continue φ:
  (φ $ LitV LitUnit) ⊢
  WP (EContinue) {{ bot }} {{ bot }} {{ φ }} {{ bot }}.
Proof.
  assert (EContinue = (of_sval SContinue)); auto.
  rewrite H.
  iIntros "Hφ".
  rewrite wp_unfold /wp_pre to_of_val.
  auto.
Qed.

Lemma tac_wp_return v φ:
  (φ v) ⊢
  WP (EReturn $ Val v) {{ bot }} {{ bot }} {{ bot }} {{ φ }}.
Proof.
  assert ((EReturn $ Val v) = (of_sval $ SReturn v)); auto.
  rewrite H.
  iIntros "Hφ".
  rewrite wp_unfold /wp_pre to_of_val.
  auto.
Qed.

(* MARK: loop *)
Lemma wp_loop_sval e0 e I φb φr s:
  to_sval e = Some s ->
  ▷ {{ I }} LoopB e0 e0 {{φb}}{{bot}}{{bot}}{{φr}} -∗
  WP e {{ λ v, I }} {{ φb }} {{ λ v, I }} {{ φr }} -∗
  WP LoopB e0 e {{φb}}{{bot}}{{bot}}{{φr}}.
Proof.
  iIntros (eq) "#IH Hwp".
  destruct s; apply of_to_sval in eq; simpl in eq; subst.
  (* value case *)
  - repeat rewrite wp_unfold.
    rewrite <- wp_unfold at 1.
    rewrite /wp_pre; simpl.
    iIntros (σ0 κ0 κs0 _) "Hs".
    iApply fupd_frame_l.
    iSplit.
    + iPureIntro. unfold reducible. simpl.
      exists nil, (LoopB e0 e0), σ0, nil.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (LoopB e0 v) (LoopB e0 e0)); auto.
      apply LoopBS.
    + unfold bi_fupd_fupd. simpl.
      unfold uPred_fupd.
      rewrite seal_eq.
      unfold uPred_fupd_def.
      iIntros "Hw".

      iSpecialize ("Hwp" with "Hw").
      repeat iMod "Hwp".
      iDestruct "Hwp" as "[Hw [Htop H]]".
      
      iApply except_0_bupd.
      iModIntro.
      
      iApply bupd_frame_l.
      iFrame "Hw".
      iApply bupd_frame_r.
      iPoseProof ownE_empty as "Hown_phi".
      iFrame "Hown_phi".

      iIntros (? ? ? Hstep') "[Hw Hphi]".
      repeat iModIntro.
      iFrame "Hw". iFrame "Hphi".
      
      iIntros "!# [Hw _]".

      repeat iModIntro.
      iFrame "Hw". iFrame "Htop".

      assert (a = (LoopB e0 e0) /\ a0 = σ0 /\ κ0 = [] /\ a1 = []) as [? [? [? ?]]].
      {
        inversion Hstep'.
        destruct K; inversion H; subst.
        - simpl in *; subst.
          inversion H1; subst; auto.
          destruct K; inversion H; subst; try congruence.
          destruct K; inversion H7; simpl in *; subst.
          inversion H0.
        - destruct K; inversion H4; simpl in *; subst.
          inversion H1; subst.
          destruct K; inversion H2; simpl in *; subst; congruence.
      }
      subst.
      iFrame "Hs".
      iSplitL; auto.
      iApply "IH"; auto.
  (* break case *)
  - repeat rewrite wp_unfold.
    rewrite <- wp_unfold at 1.
    rewrite /wp_pre; simpl.
    iIntros (σ0 κ0 κs0 _) "Hs".
    iApply fupd_frame_l.
    iSplit.
    + iPureIntro. unfold reducible. simpl.
      exists nil, (Val v), σ0, nil.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (LoopB e0 (EBreak v)) (Val v)); auto.
      apply LoopBBreakS.
    + unfold bi_fupd_fupd. simpl.
      unfold uPred_fupd.
      rewrite seal_eq.
      unfold uPred_fupd_def.
      iIntros "Hw".

      iSpecialize ("Hwp" with "Hw").
      repeat iMod "Hwp".
      iDestruct "Hwp" as "[Hw [Htop H]]".
      
      iApply except_0_bupd.
      iModIntro.
      
      iApply bupd_frame_l.
      iFrame "Hw".
      iApply bupd_frame_r.
      iPoseProof ownE_empty as "Hown_phi".
      iFrame "Hown_phi".

      iIntros (? ? ? Hstep') "[Hw Hphi]".
      repeat iModIntro.
      iFrame "Hw". iFrame "Hphi".
      
      iIntros "!# [Hw _]".

      repeat iModIntro.
      iFrame "Hw". iFrame "Htop".

      assert (a = (Val v) /\ a0 = σ0 /\ κ0 = [] /\ a1 = []) as [? [? [? ?]]].
      {
        inversion Hstep'.
        destruct K; inversion H; subst.
        - simpl in *; subst.
          inversion H1; subst; auto.
          destruct K; inversion H; subst; try congruence.
          destruct K; inversion H7; simpl in *; subst.
          + exfalso; apply H4, BreakImpenLoop.
          + destruct K; inversion H7; subst. inversion H0.
        - destruct K; inversion H4; simpl in *; subst.
          + inversion H1; subst.
            destruct K; inversion H2; simpl in *; subst; try congruence.
            destruct K; inversion H7; simpl in *; subst. inversion H3.
          + destruct K; inversion H2; simpl in *; subst.
            inversion H1; subst.
            destruct K; inversion H2; simpl in *; subst; congruence.
      }
      subst.
      iFrame "Hs".
      iSplitL; auto.
      
      iClear "#".
      rewrite wp_unfold /wp_pre; simpl.
      auto.
  (* continue case *)
  - repeat rewrite wp_unfold.
    rewrite <- wp_unfold at 1.
    rewrite /wp_pre; simpl.
    iIntros (σ0 κ0 κs0 _) "Hs".
    iApply fupd_frame_l.
    iSplit.
    + iPureIntro. unfold reducible. simpl.
      exists nil, (LoopB e0 e0), σ0, nil.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (LoopB e0 EContinue) (LoopB e0 e0)); auto.
      apply LoopBContinueS.
    + unfold bi_fupd_fupd. simpl.
      unfold uPred_fupd.
      rewrite seal_eq.
      unfold uPred_fupd_def.
      iIntros "Hw".

      iSpecialize ("Hwp" with "Hw").
      repeat iMod "Hwp".
      iDestruct "Hwp" as "[Hw [Htop H]]".
      
      iApply except_0_bupd.
      iModIntro.
      
      iApply bupd_frame_l.
      iFrame "Hw".
      iApply bupd_frame_r.
      iPoseProof ownE_empty as "Hown_phi".
      iFrame "Hown_phi".

      iIntros (? ? ? Hstep') "[Hw Hphi]".
      repeat iModIntro.
      iFrame "Hw". iFrame "Hphi".
      
      iIntros "!# [Hw _]".

      repeat iModIntro.
      iFrame "Hw". iFrame "Htop".

      assert (a = (LoopB e0 e0) /\ a0 = σ0 /\ κ0 = [] /\ a1 = []) as [? [? [? ?]]].
      {
        inversion Hstep'.
        destruct K; inversion H; subst.
        - simpl in *; subst.
          inversion H1; subst; auto.
          destruct K; inversion H; subst; try congruence.
          destruct K; inversion H7; simpl in *; subst.
          exfalso; apply H4, ContinueImpenLoop.
        - destruct K; inversion H4; simpl in *; subst.
          + inversion H1; subst.
            destruct K; inversion H2; simpl in *; subst; try congruence.
      }
      subst.
      iFrame "Hs".
      iSplitL; auto.

      iApply "IH"; auto.
  - repeat rewrite wp_unfold.
    rewrite <- wp_unfold at 1.
    rewrite /wp_pre; simpl.
    iIntros (σ0 κ0 κs0 _) "Hs".
    iApply fupd_frame_l.
    iSplit.
    + iPureIntro. unfold reducible. simpl.
      exists nil, (EReturn v), σ0, nil.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (LoopB e0 (EReturn v)) (EReturn v)); auto.
      apply (CFCtxS (EReturn v) (LoopBCtx e0 EmptyCtx)); [apply return_is_cft | auto |].
      unfold not. intros.
      inversion H; subst.
      destruct K'; simpl in *; inversion H0; subst; try congruence.
      destruct K; destruct K'; simpl in *; inversion H5; subst.
      inversion H3; subst.
      destruct K; destruct K'; simpl in *; inversion H2; subst; congruence.
    + unfold bi_fupd_fupd. simpl.
      unfold uPred_fupd.
      rewrite seal_eq.
      unfold uPred_fupd_def.
      iIntros "Hw".

      iSpecialize ("Hwp" with "Hw").
      repeat iMod "Hwp".
      iDestruct "Hwp" as "[Hw [Htop H]]".
      
      iApply except_0_bupd.
      iModIntro.
      
      iApply bupd_frame_l.
      iFrame "Hw".
      iApply bupd_frame_r.
      iPoseProof ownE_empty as "Hown_phi".
      iFrame "Hown_phi".

      iIntros (? ? ? Hstep') "[Hw Hphi]".
      repeat iModIntro.
      iFrame "Hw". iFrame "Hphi".
      
      iIntros "!# [Hw _]".

      repeat iModIntro.
      iFrame "Hw". iFrame "Htop".

      assert (a = (EReturn v) /\ a0 = σ0 /\ κ0 = [] /\ a1 = []) as [? [? [? ?]]].
      {
        inversion Hstep'.
        destruct K; inversion H; subst.
        - simpl in *; subst.
          inversion H1; subst; auto.
          destruct K; inversion H; subst; try congruence.
          destruct K; inversion H7; simpl in *; subst; auto.
          + destruct K; inversion H7; subst. inversion H0.
        - destruct K; inversion H4; simpl in *; subst.
          + inversion H1; subst.
            destruct K; inversion H2; simpl in *; subst; try congruence.
            destruct K; inversion H7; simpl in *; subst. inversion H3.
          + destruct K; inversion H2; simpl in *; subst.
            inversion H1; subst.
            destruct K; inversion H2; simpl in *; subst; congruence.
      }
      subst.
      iFrame "Hs".
      iSplitL; auto.
      
      iClear "#".
      rewrite wp_unfold /wp_pre; simpl.
      auto.
Qed.

Lemma tac_wp_loop e I φb φr:
  {{ I }} e {{ λ v, I }} {{ φb }} {{ λ v, I }} {{ φr }} ⊢
  {{ I }} (loop e) {{ φb }} {{ bot }} {{ bot }} {{ φr }}.
Proof.
  iIntros "#Hbdy !# H".
  iLöb as "IH0".
  destruct (to_sval e) eqn:eq.
  {
    iSpecialize ("Hbdy" with "H").
    iApply wp_loop_sval; [apply eq | auto | auto].
  }
  {
    (* Main proof for the preservation case *)
    iPoseProof ("Hbdy" with "H") as "H1".  
    remember e as e0.
    rewrite -> Heqe0 in *.
    rewrite <- Heqe0 at 2.
    rewrite <- Heqe0 at 2.
    rewrite <- Heqe0 at 3.
    
    clear Heqe0.
    iClear "Hbdy".
    
    iRevert (e eq) "H1".
    iLöb as "IH".
    iIntros (e eq) "H1".

    repeat rewrite wp_unfold.
    rewrite <- wp_unfold at 1.
    rewrite /wp_pre; simpl.
    rewrite eq.

    iIntros (σ1 κ κs ?) "Hs".
    iSpecialize ("H1" $! σ1 κ κs a with "Hs").

    unfold fupd.
    unfold bi_fupd_fupd. simpl.
    unfold uPred_fupd.
    rewrite seal_eq.
    unfold uPred_fupd_def.
    iIntros "Hw".
    iSpecialize ("H1" with "Hw").

    repeat iMod "H1".
    repeat iModIntro.

    iDestruct "H1" as "[Hw [Hphi [% H1]]]".
    iFrame "Hw". iFrame "Hphi".

    iSplitR; [iPureIntro | clear H].
    {
      destruct H as [κ' [e' [σ' [efs Hred]]]].
      exists κ', (LoopB e0 e'), σ', efs.
      inversion Hred; subst.
      apply Ectx_step with (LoopBCtx e0 (comp_ectx K EmptyCtx)) e1' e2'; simpl;
      [rewrite <- fill_comp | rewrite <- fill_comp |]; auto.
    }

    iIntros (e2 σ2 efs0 Hstep) "Hw".

    (* DONE: may be used instead of congruence lemma *)
    assert (exists e1, prim_step e σ1 κ e1 σ2 efs0 /\
          (e2 = LoopB e0 e1 \/ exists v, e1 = e2 /\ e1 = EReturn $ Val v)) as [e1 [Hred ?]].
    {
      inversion Hstep.
      destruct K; inversion H; simpl in *; subst.
      - inversion H1; subst; inversion eq.
        destruct K; inversion H; subst; try congruence.
        clear H H3 H6.
        destruct e2'; inversion H0; subst.
        + exfalso. apply H4. apply BreakImpenLoop.
        + exfalso. apply H4. apply ContinueImpenLoop.
        + assert (¬ impenetrable_ectx (return v) K).
          {
            intros H. apply H4.
            replace (LoopBCtx e0 K) with (comp_ectx (LoopBCtx e0 EmptyCtx) K); auto.
            eapply CompImpenCtx; auto.
          }
          exists (EReturn v).
          split.
          * apply Ectx_step with EmptyCtx (fill K (EReturn v)) (EReturn v); auto.
            apply CFCtxS; auto.
            intros ?; subst.
            inversion eq.
          * right. eauto.
      - exists (fill K e2').
        split.
        + apply Ectx_step with K e1' e2'; auto.
        + auto.
    }

    iSpecialize ("H1" $! e1 σ2 efs0 Hred with "Hw").

    (* DONE: the congruence lemma is no longer needed
    assert (κ' = κ /\ e2 = LoopB e0 e' /\ σ2 = σ' /\ efs0 = efs) as [? [? [? ?]]].
    {
      apply (fill_step _ _ _ _ _ _ (LoopBCtx e0 EmptyCtx)) in Hred.
      simpl in Hred.
      pose proof prim_step_congruence _ _ _ _ _ _ _ _ _ _ Hred Hstep.
      naive_solver.
    }
    subst.

    iSpecialize ("H1" $! e' σ' efs Hred with "Hw"). *)

    repeat iMod "H1".
    repeat iModIntro.
    iDestruct "H1" as "[Hw [Hphi H1]]".
    iFrame "Hw". iFrame "Hphi".
    iNext.

    iIntros "Hw".
    iSpecialize ("H1" with "Hw").

    repeat iMod "H1".
    repeat iModIntro.
    iDestruct "H1" as "[Hw [Hphi H1]]".
    iFrame "Hw". iFrame "Hphi".

    iDestruct "H1" as "[Hs [Hwp Hefs]]".
    iFrame "Hs". iSplitR "Hefs"; auto.

    destruct H.
    - subst. 
      destruct (to_sval e1) eqn:eq'; [| iApply "IH"; auto].
      iApply wp_loop_sval; [apply eq' | auto | auto].
    - destruct H as [v [? ?]]; subst.
      repeat rewrite wp_unfold.
      rewrite <- wp_unfold at 1.
      rewrite /wp_pre; simpl.
      auto.
  }
Qed.


Lemma wp_bind_sval s e K φn φb φc φr:
  to_sval e = Some s ->
  WP e {{ λ v, (WP (fill K (Val v)) {{ φn }} {{ φb }} {{ φc }} {{ φr }}) }}
       {{ λ v, uPred_and (uPred_pure (~ impenetrable_ectx (EBreak v) K)) (φb v) }}
       {{ λ v, uPred_and (uPred_pure (~ impenetrable_ectx EContinue K)) (φc v) }}
       {{ λ v, uPred_and (uPred_pure (~ impenetrable_ectx (EReturn v) K)) (φr v) }}
  ⊢ WP (fill K e) {{ φn }} {{ φb }} {{ φc }} {{ φr }}.
Proof.
  iIntros (eq) "H".
  destruct s; apply of_to_sval in eq; simpl in eq; subst.
  {
    rewrite wp_unfold /wp_pre; simpl.
    iMod "H". auto.
  }
  {
    rewrite wp_unfold /wp_pre; simpl.
    iMod "H".
    iDestruct "H" as "[% H]".

    iRevert (K H).
    iLöb as "IH".
    iIntros (K H).
    
    rewrite wp_unfold /wp_pre; simpl.
    destruct (to_sval (fill K (break v))) eqn:eq;
    [destruct K; inversion eq; try congruence; try (destruct K; inversion eq); auto |].
    
    iIntros (σ1 κ κs _) "Hs".
    unfold fupd.
    unfold bi_fupd_fupd. simpl.
    unfold uPred_fupd.
    rewrite seal_eq.
    unfold uPred_fupd_def.
    iIntros "[Hw Htop]".

    iApply except_0_bupd.
    iModIntro.
    
    iApply bupd_frame_l.
    iFrame "Hw".
    iApply bupd_frame_r.
    iPoseProof ownE_empty as "Hown_phi".
    iFrame "Hown_phi".

    iSplitR.
    {
      iPureIntro.
      unfold reducible.
      exists nil, (EBreak $ Val v), σ1, nil.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (fill K (break v)) (break v)); auto.
      apply CFCtxS; auto.
      - apply break_is_cft.
      - unfold not. intros; subst.
        inversion eq.
    }

    iIntros (e2 σ2 efs Hstep) "[Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Hphi".
    iIntros "!# [Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Htop".

    pose proof break_penetrable_preservation _ _ _ _ _ _ _ H Hstep as [? [? [? [K' [? ?]]]]].
    subst.
    iFrame "Hs".
    iSplitL; auto.
    iApply ("IH" with "[H] []"); auto.
  }
  {
    rewrite wp_unfold /wp_pre; simpl.
    iMod "H".
    iDestruct "H" as "[% H]".

    iRevert (K H).
    iLöb as "IH".
    iIntros (K H).
    
    rewrite wp_unfold /wp_pre; simpl.
    destruct (to_sval (fill K EContinue)) eqn:eq;
    [destruct K; inversion eq; try congruence; try (destruct K; inversion eq); auto |].
    
    iIntros (σ1 κ κs _) "Hs".
    unfold fupd.
    unfold bi_fupd_fupd. simpl.
    unfold uPred_fupd.
    rewrite seal_eq.
    unfold uPred_fupd_def.
    iIntros "[Hw Htop]".

    iApply except_0_bupd.
    iModIntro.
    
    iApply bupd_frame_l.
    iFrame "Hw".
    iApply bupd_frame_r.
    iPoseProof ownE_empty as "Hown_phi".
    iFrame "Hown_phi".

    iSplitR.
    {
      iPureIntro.
      unfold reducible.
      exists nil, (EContinue), σ1, nil.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (fill K EContinue) EContinue); auto.
      apply CFCtxS; auto.
      - apply continue_is_cft.
      - unfold not. intros; subst.
        inversion eq.
    }

    iIntros (e2 σ2 efs Hstep) "[Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Hphi".
    iIntros "!# [Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Htop".

    pose proof continue_penetrable_preservation _ _ _ _ _ _ H Hstep as [? [? [? [K' [? ?]]]]].
    subst.
    iFrame "Hs".
    iSplitL; auto.
    iApply ("IH" with "[H] []"); auto.
  }
  {
    rewrite wp_unfold /wp_pre; simpl.
    iMod "H".
    iDestruct "H" as "[% H]".

    iRevert (K H).
    iLöb as "IH".
    iIntros (K H).
    
    rewrite wp_unfold /wp_pre; simpl.
    destruct (to_sval (fill K (EReturn v))) eqn:eq;
    [destruct K; inversion eq; try congruence; try (destruct K; inversion eq); auto |].
    
    iIntros (σ1 κ κs _) "Hs".
    unfold fupd.
    unfold bi_fupd_fupd. simpl.
    unfold uPred_fupd.
    rewrite seal_eq.
    unfold uPred_fupd_def.
    iIntros "[Hw Htop]".

    iApply except_0_bupd.
    iModIntro.
    
    iApply bupd_frame_l.
    iFrame "Hw".
    iApply bupd_frame_r.
    iPoseProof ownE_empty as "Hown_phi".
    iFrame "Hown_phi".

    iSplitR.
    {
      iPureIntro.
      unfold reducible.
      exists nil, (EReturn v), σ1, nil.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (fill K (EReturn v)) (EReturn v)); auto.
      apply CFCtxS; auto.
      - apply return_is_cft.
      - unfold not. intros; subst.
        inversion eq.
    }

    iIntros (e2 σ2 efs Hstep) "[Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Hphi".
    iIntros "!# [Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Htop".

    pose proof return_penetrable_preservation _ _ _ _ _ _ _ H Hstep as [? [? [? [K' [? ?]]]]].
    subst.
    iFrame "Hs".
    iSplitL; auto.
    iApply ("IH" with "[H] []"); auto.
  }
Qed.

Lemma tac_wp_bind e K φn φb φc φr:
  WP e {{ λ v, (WP (fill K (Val v)) {{ φn }} {{ φb }} {{ φc }} {{ φr }}) }}
       {{ λ v, uPred_and (uPred_pure (~ impenetrable_ectx (EBreak v) K)) (φb v) }}
       {{ λ v, uPred_and (uPred_pure (~ impenetrable_ectx EContinue K)) (φc v) }}
       {{ λ v, uPred_and (uPred_pure (~ impenetrable_ectx (EReturn v) K)) (φr v) }}
  ⊢ WP (fill K e) {{ φn }} {{ φb }} {{ φc }} {{ φr }}.
Proof.
  iIntros "H".

  destruct (to_sval e) eqn:eq.
  {
    iApply (wp_bind_sval s); auto.
  }
  {
    iRevert (e eq) "H".
    iLöb as "IH".
    iIntros (e eq) "H".

    repeat rewrite wp_unfold.
    rewrite /wp_pre; simpl.
    rewrite eq.
    pose proof fill_not_sval K _ eq as eq'.
    rewrite eq'.

    iIntros (σ1 κ κs ?) "Hs".
    iSpecialize ("H" $! σ1 κ κs a with "Hs").

    unfold fupd.
    unfold bi_fupd_fupd. simpl.
    unfold uPred_fupd.
    rewrite seal_eq.
    unfold uPred_fupd_def.
    iIntros "[Hw Htop]".

    iApply except_0_bupd.
    iModIntro.
    
    iApply bupd_frame_l.
    iFrame "Hw".
    iApply bupd_frame_r.
    iPoseProof ownE_empty as "Hown_phi".
    iFrame "Hown_phi".

    iSplitR;
    [iPureIntro;(* FIXME: apply (reducible_fill _ _ eq H) should work *) admit |].

    iIntros (e2 σ2 efs Hstep) "[Hw Hphi]".
    iCombine ("Hw Htop") as "Hw".
    iSpecialize ("H" with "Hw").

    repeat iMod "H".
    

    iDestruct "H" as "[Hw [Hphi' [_ H]]]".

    assert (exists e1, e2 = fill K e1 /\ prim_step e σ1 κ e1 σ2 efs) as [e1 [? Hred]].
    { eapply fill_step_inv; auto. } subst.

    (* destruct H as [κ' [e' [σ' [efs' H]]]].

    (* DONE: congruence lemma is no longer needed *)
    pose proof prim_step_congruence _ _ _ _ _ _ _ _ _ _ Hstep
                                    (fill_step _ _ _ _ _ _ K H) as [? [? [? ?]]].
    subst. *)

    iCombine ("Hw Hphi'") as "Hw".
    iSpecialize ("H" $! e1 σ2 efs Hred with "Hw").

    repeat iMod "H".
    iDestruct "H" as "[Hw [Hphi' H]]".


    repeat iModIntro.
    iFrame "Hw". iFrame "Hphi".

    iNext.

    iIntros "Hw".
    iSpecialize ("H" with "Hw").

    repeat iMod "H".
    repeat iModIntro.

    iDestruct "H" as "[Hw [Htop [Hs [Hwp Hefs]]]]".
    iFrame "Hw". iFrame "Htop". iFrame "Hs".
    iSplitR "Hefs"; auto.

    destruct (to_sval e1) eqn:eq'';
    [iApply (wp_bind_sval s); auto |].
    iApply "IH"; auto.
  }
Admitted.

End multi_post.
