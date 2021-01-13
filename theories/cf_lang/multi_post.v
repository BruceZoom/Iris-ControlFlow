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

(* MARK:  *)
Instance heapG_irisG `{!heapG Σ} : irisG cf_lang Σ := {
  iris_invG := heapG_invG;
  state_interp σ κs _ :=
    (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id) ∗ ⌜no_continue_state σ⌝)%I;
  fork_post _ := True%I;
}.

(** Override the notations so that scopes and coercions work out *)
Notation "l ↦{ q } v" := (mapsto (L:=loc) (V:=val) l q v%V)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" :=
  (mapsto (L:=loc) (V:=val) l 1 v%V) (at level 20) : bi_scope.
Notation "l ↦{ q } -" := (∃ v, l ↦{q} v)%I
  (at level 20, q at level 50, format "l  ↦{ q }  -") : bi_scope.
Notation "l ↦ -" := (l ↦{1} -)%I (at level 20) : bi_scope.


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
  rewrite wp_unfold /wp_pre language.to_of_val.
  auto.
Qed.

Lemma tac_wp_continue φ:
  (φ $ LitV LitUnit) ⊢
  WP (EContinue) {{ bot }} {{ bot }} {{ φ }} {{ bot }}.
Proof.
  assert (EContinue = (of_sval SContinue)); auto.
  rewrite H.
  iIntros "Hφ".
  rewrite wp_unfold /wp_pre language.to_of_val.
  auto.
Qed.

Lemma tac_wp_return v φ:
  (φ v) ⊢
  WP (EReturn $ Val v) {{ bot }} {{ bot }} {{ bot }} {{ φ }}.
Proof.
  assert ((EReturn $ Val v) = (of_sval $ SReturn v)); auto.
  rewrite H.
  iIntros "Hφ".
  rewrite wp_unfold /wp_pre language.to_of_val.
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
          unfold expr_depth.singleton_ectx in H3.
          destruct K; inversion H; subst; [inversion H3 |].
          destruct K; inversion H7; simpl in *; subst.
          inversion H0.
        - destruct K; inversion H4; simpl in *; subst.
          inversion H1; subst.
          unfold expr_depth.singleton_ectx in H4.
          destruct K; inversion H2; simpl in *; subst; inversion H4.
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
          unfold expr_depth.singleton_ectx in H3.
          destruct K; inversion H; subst; [inversion H3 |].
          destruct K; inversion H7; simpl in *; subst.
          + exfalso; apply H4, BreakImpenLoop.
          + destruct K; inversion H7; subst. inversion H0.
        - destruct K; inversion H4; simpl in *; subst.
          + inversion H1; subst.
            unfold expr_depth.singleton_ectx in H4.
            destruct K; inversion H2; simpl in *; subst; [inversion H4 |].
            destruct K; inversion H7; simpl in *; subst. inversion H3.
          + destruct K; inversion H2; simpl in *; subst.
            inversion H1; subst.
            unfold expr_depth.singleton_ectx in H5.
            destruct K; inversion H2; simpl in *; subst; inversion H5.
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
          unfold expr_depth.singleton_ectx in H3.
          destruct K; inversion H; subst; [inversion H3 |].
          destruct K; inversion H7; simpl in *; subst.
          exfalso; apply H4, ContinueImpenLoop.
        - destruct K; inversion H4; simpl in *; subst.
          + inversion H1; subst.
            unfold expr_depth.singleton_ectx in H4.
            destruct K; inversion H2; simpl in *; subst; inversion H4.
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
      apply (CFCtxS (EReturn v) (LoopBCtx e0 EmptyCtx));
      [apply return_is_cft | unfold expr_depth.singleton_ectx; auto |].
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
          unfold expr_depth.singleton_ectx in H3.
          destruct K; inversion H; subst; [inversion H3 |].
          destruct K; inversion H7; simpl in *; subst; auto.
          + destruct K; inversion H7; subst. inversion H0.
        - destruct K; inversion H4; simpl in *; subst.
          + inversion H1; subst.
            unfold expr_depth.singleton_ectx in H4.
            destruct K; inversion H2; simpl in *; subst; [inversion H4 |].
            destruct K; inversion H7; simpl in *; subst. inversion H3.
          + destruct K; inversion H2; simpl in *; subst.
            inversion H1; subst.
            unfold expr_depth.singleton_ectx in H5.
            destruct K; inversion H2; simpl in *; subst; inversion H5.
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

    (* MARK: use fill_step_inv instead of the proof below when using the singleton version *)
    replace (LoopB e0 e) with (fill (LoopBCtx e0 EmptyCtx) e) in Hstep; auto.
    pose proof fill_step_inv _ _ _ _ _ _ _ eq Hstep as [e1 [? Hred]]; subst; simpl.

    (* DONE: may be used instead of congruence lemma *)
    (* assert (exists e1, prim_step e σ1 κ e1 σ2 efs0 /\
          (e2 = LoopB e0 e1 \/ exists v, e1 = e2 /\ e1 = EReturn $ Val v)) as [e1 [Hred ?]].
    {
      inversion Hstep.
      destruct K; inversion H; simpl in *; subst.
      - inversion H1; subst; inversion eq.
        unfold expr_depth.singleton_ectx in H3.
        destruct K; inversion H; subst; [inversion H3 |].
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
            unfold expr_depth.singleton_ectx.
            destruct_inversion K eq; eauto.
            inversion eq.
          * right. eauto.
      - exists (fill K e2').
        split.
        + apply Ectx_step with K e1' e2'; auto.
        + auto.
    } *)

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

    destruct (to_sval e1) eqn:eq'; [| iApply "IH"; auto].
    iApply wp_loop_sval; [apply eq' | auto | auto].

    (* destruct H.
    - subst. 
      destruct (to_sval e1) eqn:eq'; [| iApply "IH"; auto].
      iApply wp_loop_sval; [apply eq' | auto | auto].
    - destruct H as [v [? ?]]; subst.
      repeat rewrite wp_unfold.
      rewrite <- wp_unfold at 1.
      rewrite /wp_pre; simpl.
      auto. *)
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
      apply cf_reducible; auto.
      apply break_is_cft.

      (* unfold reducible.
      exists nil, (EBreak $ Val v), σ1, nil.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (fill K (break v)) (break v)); auto.
      apply CFCtxS; auto.
      - apply break_is_cft.
      - destruct K; inversion eq; unfold expr_depth.singleton_ectx; eauto. *)
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
      apply cf_reducible; auto.
      apply continue_is_cft.

      (* unfold reducible.
      exists nil, (EContinue), σ1, nil.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (fill K EContinue) EContinue); auto.
      apply CFCtxS; auto.
      - apply continue_is_cft.
      - unfold not. intros; subst.
        inversion eq. *)
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
      apply cf_reducible; auto.
      apply return_is_cft.

      (* unfold reducible.
      exists nil, (EReturn v), σ1, nil.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (fill K (EReturn v)) (EReturn v)); auto.
      apply CFCtxS; auto.
      - apply return_is_cft.
      - unfold not. intros; subst.
        inversion eq. *)
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


Lemma tac_wp_bind_inv_sval s e K φn φb φc φr:
  to_sval e = Some s ->
  WP (fill K e) {{ φn }} {{ φb }} {{ φc }} {{ φr }} ⊢
  WP e {{ λ v, (WP (fill K (Val v)) {{ φn }} {{ φb }} {{ φc }} {{ φr }}) }}
       {{ λ v, uPred_and (uPred_pure (~ impenetrable_ectx (EBreak v) K)) (φb v) }}
       {{ λ v, uPred_and (uPred_pure (~ impenetrable_ectx EContinue K)) (φc v) }}
       {{ λ v, uPred_and (uPred_pure (~ impenetrable_ectx (EReturn v) K)) (φr v) }}.
Proof.
  iIntros (eq) "H".
  destruct s; apply of_to_sval in eq; simpl in eq; subst.
  {
    repeat rewrite wp_unfold.
    rewrite <- wp_unfold.
    rewrite /wp_pre; simpl.
    auto.
  }
  {
    iRevert (K) "H".
    iLöb as "IH".
    iIntros (K) "H".
    rewrite wp_unfold /wp_pre; simpl.
    rewrite wp_unfold /wp_pre; simpl.
    destruct (to_sval (fill K (break v))) eqn:eq.
    {
      destruct_inversion K eq; admit.
    }
    {
      admit.
    }
Abort.


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

    iIntros "Hw".
    iSpecialize ("H" with "Hw").
    
    repeat iMod "H".
    repeat iModIntro.

    iDestruct "H" as "[Hw [Hphi [% H]]]".
    
    iFrame "Hw".
    iFrame "Hphi".

    iSplitR;
    [iPureIntro; apply my_reducible_fill; auto |].

    iIntros (e2 σ2 efs Hstep) "[Hw Hphi]".

    assert (exists e1, e2 = fill K e1 /\ prim_step e σ1 κ e1 σ2 efs) as [e1 [? Hred]].
    { apply fill_step_inv; auto. } subst.

    (* destruct H as [κ' [e' [σ' [efs' H]]]].

    (* DONE: congruence lemma is no longer needed *)
    pose proof prim_step_congruence _ _ _ _ _ _ _ _ _ _ Hstep
                                    (fill_step _ _ _ _ _ _ K H) as [? [? [? ?]]].
    subst. *)

    iCombine ("Hw Hphi") as "Hw".
    iSpecialize ("H" $! e1 σ2 efs Hred with "Hw").

    repeat iMod "H".
    iDestruct "H" as "[Hw [Hphi H]]".


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
Qed.

Lemma wp_call_sval s e φ:
  to_sval e = Some s ->
  WP e {{ φ }} {{ bot }} {{ bot }} {{ φ }} ⊢
  WP Call e {{ φ }} {{ bot }} {{ bot }} {{ bot }}.
Proof.
  iIntros (eq) "H".
  destruct s; apply of_to_sval in eq; simpl in eq; subst.
  {
    rewrite wp_unfold /wp_pre; simpl.
    rewrite wp_unfold /wp_pre; simpl.

    unfold fupd.
    unfold bi_fupd_fupd. simpl.
    unfold uPred_fupd.
    rewrite seal_eq.
    unfold uPred_fupd_def.

    iIntros (σ1 κ κs _) "Hs Hw".
    iSpecialize ("H" with "Hw").

    repeat iMod "H".
    iDestruct "H" as "[Hw [Htop H]]".
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
      exists nil, (Val v), σ1, nil.
      apply Ectx_step with EmptyCtx (Call v) (Val v); eauto.
      constructor.
    }

    iIntros (e2 σ2 efs H) "[Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Hphi".
    iIntros "!# [Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Htop".

    assert (e2 = Val v /\ κ = [] /\ σ2 = σ1 /\ efs = []) as [? [? [? ?]]]; subst.
    {
      inversion H; subst.
      destruct K; simpl in *; inversion H0; subst.
      - inversion H2; subst; auto.
        destruct_inversion K H0.
        + inversion H3.
        + destruct_inversion K H7; inversion H3.
      - destruct_inversion K H3. inversion H2; subst.
        destruct_inversion K H3. inversion H4.
    }

    iFrame "Hs".
    iSplitL; auto.
    rewrite wp_unfold /wp_pre; simpl.
    auto.
  }
  {
    rewrite wp_unfold /wp_pre; simpl.
    rewrite wp_unfold /wp_pre; simpl.

    unfold fupd.
    unfold bi_fupd_fupd. simpl.
    unfold uPred_fupd.
    rewrite seal_eq.
    unfold uPred_fupd_def.

    iIntros (? ? ? ?) "? Hw".
    iSpecialize ("H" with "Hw").
    repeat iMod "H".
    iDestruct "H" as "[? [? H]]".
    iExFalso.
    auto.
  }
  {
    rewrite wp_unfold /wp_pre; simpl.
    rewrite wp_unfold /wp_pre; simpl.

    unfold fupd.
    unfold bi_fupd_fupd. simpl.
    unfold uPred_fupd.
    rewrite seal_eq.
    unfold uPred_fupd_def.

    iIntros (? ? ? ?) "? Hw".
    iSpecialize ("H" with "Hw").
    repeat iMod "H".
    iDestruct "H" as "[? [? H]]".
    iExFalso.
    auto.
  }
  {
    rewrite wp_unfold /wp_pre; simpl.
    rewrite wp_unfold /wp_pre; simpl.

    unfold fupd.
    unfold bi_fupd_fupd. simpl.
    unfold uPred_fupd.
    rewrite seal_eq.
    unfold uPred_fupd_def.

    iIntros (σ1 κ κs _) "Hs Hw".
    iSpecialize ("H" with "Hw").

    repeat iMod "H".
    iDestruct "H" as "[Hw [Htop H]]".
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
      exists nil, (Val v), σ1, nil.
      apply Ectx_step with EmptyCtx (Call (return v)) (Val v); eauto.
      constructor.
    }

    iIntros (e2 σ2 efs H) "[Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Hphi".
    iIntros "!# [Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Htop".

    assert (e2 = Val v /\ κ = [] /\ σ2 = σ1 /\ efs = []) as [? [? [? ?]]]; subst.
    {
      inversion H; subst.
      destruct K; simpl in *; inversion H0; subst.
      - inversion H2; subst; auto.
        unfold expr_depth.singleton_ectx in H4.
        destruct_inversion K H0; [inversion H4 |].
        destruct_inversion K H7.
        + exfalso. apply H5; constructor.
        + destruct_inversion K H8. inversion H3.
      - destruct_inversion K H3.
        + inversion H2; subst.
          unfold expr_depth.singleton_ectx in H5.
          destruct_inversion K H3; [inversion H5 |].
          destruct_inversion K H8. inversion H4.
        + destruct_inversion K H4. inversion H2; subst.
          destruct_inversion K H4. inversion H5.
    }

    iFrame "Hs".
    iSplitL; auto.
    rewrite wp_unfold /wp_pre; simpl.
    auto.
  }
Qed.

Lemma tac_wp_call e φ:
  WP e {{ φ }} {{ bot }} {{ bot }} {{ φ }} ⊢
  WP Call e {{ φ }} {{ bot }} {{ bot }} {{ bot }}.
Proof.
  iIntros "H".
  destruct (to_sval e) eqn:eq.
  {
    iApply (wp_call_sval s); auto.
  }
  {
    iRevert (e eq) "H".
    iLöb as "IH".
    iIntros (e eq) "H".

    repeat rewrite wp_unfold.
    rewrite /wp_pre; simpl.
    rewrite eq.

    iIntros (σ1 κ κs ?) "Hs".
    iSpecialize ("H" $! σ1 κ κs a with "Hs").

    unfold fupd.
    unfold bi_fupd_fupd. simpl.
    unfold uPred_fupd.
    rewrite seal_eq.
    unfold uPred_fupd_def.

    iIntros "Hw".
    iSpecialize ("H" with "Hw").
    
    repeat iMod "H".
    repeat iModIntro.

    iDestruct "H" as "[Hw [Hphi [% H]]]".
    
    iFrame "Hw".
    iFrame "Hphi".

    iSplitR.
    {
      iPureIntro.
      replace (Call e) with (fill (CallCtx EmptyCtx) e); auto.
      apply my_reducible_fill; auto.
    }

    iIntros (e2 σ2 efs Hstep) "[Hw Hphi]".


    assert (exists e1, e2 = fill (CallCtx EmptyCtx) e1 /\ prim_step e σ1 κ e1 σ2 efs) as [e1 [? Hred]]; subst.
    {
      replace (Call e) with (fill (CallCtx EmptyCtx) e); auto.
      apply fill_step_inv; auto.
    }
    simpl in *.

    (* destruct H as [κ' [e' [σ' [efs' H]]]].

    (* DONE: congruence lemma is no longer needed *)
    pose proof prim_step_congruence _ _ _ _ _ _ _ _ _ _ Hstep
                                    (fill_step _ _ _ _ _ _ K H) as [? [? [? ?]]].
    subst. *)

    iCombine ("Hw Hphi") as "Hw".
    iSpecialize ("H" $! e1 σ2 efs Hred with "Hw").

    repeat iMod "H".
    iDestruct "H" as "[Hw [Hphi H]]".


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
    [iApply (wp_call_sval s); auto |].
    iApply "IH"; auto.
  }
Qed.

(* Lemma wp_tac_if v e1 e2 φn φb φc φr:
  (bi_pure (v = (LitV (LitBool true))) -∗ WP e1 {{ φn }} {{ φb }} {{ φc }} {{ φr }}) ∧
  (bi_pure (v = (LitV (LitBool false))) -∗ WP e2 {{ φn }} {{ φb }} {{ φc }} {{ φr }}) -∗
  WP (If (Val v) e1 e2) {{ φn }} {{ φb }} {{ φc }} {{ φr }}.
Proof.
  iIntros "H".
   *)

(* if seq
no continue

rev seq: P c1;;c2 Q -> exists R, P c1 R /\ R c2 Q


[P -* wp c1;;c2 Q] ->
exists R, [P -* wp c1 R] /\ [R -* wp c2 Q]


wp c1;;c2 Q |- wp c1 {wp c2 Q}


e no continue ->
wp e {} {} { phi_c_1 } {} -||- wp e {} {} { phi_c_2 } {}


Lemma wp_seq_sval s e1 e2 φn φb φc φr:
  to_sval e1 = Some s ->
  WP e1 {{ λ v, WP e2 {{ φn }} {{ φb }} {{ φc }} {{ φr }} }} {{ φb }} {{ φc }} {{ φr }} ⊢
  WP (Seq e1 e2) {{ φn }} {{ φb }} {{ φc }} {{ φr }}.
Proof.
  iIntros (eq) "H".

  (* replace (App (Rec BAnon BAnon e2) e1) with (fill (AppRCtx (Rec BAnon BAnon e2) EmptyCtx) e1); auto.
  iApply tac_wp_bind; simpl.
  destruct s; apply of_to_sval in eq; simpl in eq; subst.
  {
    rewrite wp_unfold /wp_pre; simpl.
    repeat rewrite wp_unfold.
    rewrite <- wp_unfold at 1.
    rewrite /wp_pre; simpl.
    
    unfold fupd.
    unfold bi_fupd_fupd. simpl.
    unfold uPred_fupd.
    rewrite seal_eq.
    unfold uPred_fupd_def.

    iIntros "Hw".
  } *)

  destruct s; apply of_to_sval in eq; simpl in eq; subst.
  {
    rewrite wp_unfold /wp_pre; simpl.
    repeat rewrite wp_unfold.
    rewrite <- wp_unfold at 1.
    rewrite /wp_pre; simpl.

    unfold fupd.
    unfold bi_fupd_fupd. simpl.
    unfold uPred_fupd.
    rewrite seal_eq.
    unfold uPred_fupd_def.

    iIntros (σ1 κ κs _) "Hs Hw".
    iSpecialize ("H" with "Hw").

    repeat iMod "H".
    iDestruct "H" as "[Hw [Htop H]]".
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
      exists nil, (App (Val $ RecV BAnon BAnon e2) (Val v)), σ1, nil.
      apply Ectx_step with (AppLCtx EmptyCtx v) (Rec BAnon BAnon e2) (Val $ RecV BAnon BAnon e2); auto.
      constructor.
    }

    iIntros (e0 σ2 efs H) "[Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Hphi".
    iIntros "!# [Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Htop".

    assert (σ1 = σ2 /\ κ = [] /\ efs = [] /\ e0 = (App (Val $ RecV BAnon BAnon e2) (Val v))) as [? [? [? ?]]]; subst.
    {
      inversion H.
      destruct_inversion K H0.
      - inversion H2; subst.
        destruct_inversion K H0.
        + inversion H1.
        + unfold expr_depth.singleton_ectx in H4.
          destruct_inversion K H4. simpl in *; subst.
          inversion H1.
        + unfold expr_depth.singleton_ectx in H4. simpl in H4.
          destruct_inversion K H4. simpl in *; subst. inversion H1.
      - destruct_inversion K H4.
        inversion H2; subst.
        + simpl. auto.
        + destruct_inversion K H3.
          unfold expr_depth.singleton_ectx in H5. inversion H5.
      - destruct_inversion K H5.
        inversion H2; subst.
        destruct_inversion K H3.
        inversion H4.
    }

    iFrame.
    iSplitL; auto.

    SearchAbout fupd.
Abort.
 *)

Section strong_no_continue.
  Import NoContinueHeadPreserve.

  Lemma no_continue_fill K e:
    no_continue (fill K e) ->
    no_continue e.
  Proof.
    induction K; intros; simpl; auto;
    try (destruct H; eauto);
    try (destruct H0; eauto).
  Qed.

  Lemma no_continue_fill_subst K e1 e2:
    no_continue (fill K e1) ->
    no_continue e2 ->
    no_continue (fill K e2).
  Proof.
    induction K; intros; simpl; auto;
    try (destruct H; eauto);
    try (destruct H1; eauto).
  Qed.

  Lemma no_continue_preserve e1 σ1 κ e2 σ2 efs :
    no_continue_state σ1 ->
    prim_step e1 σ1 κ e2 σ2 efs ->
    no_continue e1 -> no_continue e2 /\ no_continue_state σ2.
  Proof.
    intro HStateNoContinue.
    intros.
    inversion H; subst.
    pose proof no_continue_fill _ _ H0.
    split.
    - apply no_continue_preserve_head in H3; auto.
      apply (no_continue_fill_subst _ _ _ H0 H3).
    - apply no_continue_state_preserve_head in H3; auto.
  Qed.

  Lemma wp_no_continue_sval e s φn φb φr φ1 φ2:
    to_sval e = Some s ->
    no_continue e ->
    WP e {{ φn }} {{ φb }} {{ φ1 }} {{ φr }} ⊢
    WP e {{ φn }} {{ φb }} {{ φ2 }} {{ φr }}.
  Proof.
    iIntros (eq H) "H".
    destruct s; apply of_to_sval in eq; simpl in eq; subst.
    {
      rewrite wp_unfold /wp_pre; simpl.
      rewrite wp_unfold /wp_pre; simpl.
      auto.
    }
    {
      rewrite wp_unfold /wp_pre; simpl.
      rewrite wp_unfold /wp_pre; simpl.
      auto.
    }
    {
      inversion H.
    }
    {
      rewrite wp_unfold /wp_pre; simpl.
      rewrite wp_unfold /wp_pre; simpl.
      auto.
    }
  Qed.

  (* Definition state_has_no_continue v : iProp Σ := 
    (∀ l: loc, l ↦ v). *)

  

  Lemma wp_no_continue e φn φb φr φ1 φ2:
    no_continue e ->
    (* (∀ l v, l ↦ v -∗ ⌜no_continue_val v⌝) ∗ *)
    (* (∀ σ, gen_heap_ctx (heap σ) -∗ (gen_heap_ctx (heap σ) ∗ ⌜no_continue_state σ⌝ ))%I ∗ *)
    (* also require heap to be well formed *)
    WP e {{ φn }} {{ φb }} {{ φ1 }} {{ φr }} ⊢
    WP e {{ φn }} {{ φb }} {{ φ2 }} {{ φr }}.
  Proof.
    iIntros (H) "H".
    destruct (to_sval e) eqn:eq.
    {
      iApply (wp_no_continue_sval e _ φn φb φr φ1 φ2 eq H with "H").
    }
    {
      iRevert (e eq H) "H".
      iLöb as "IH".
      iIntros (e eq H) "H".
      rewrite wp_unfold /wp_pre; simpl.
      rewrite wp_unfold /wp_pre; simpl.
      rewrite eq.

      iIntros (σ1 κ κs ?) "(Hheap & Hproph & #HNCS)".
      (* iSpecialize ("HNCS" $! σ1 with "Hheap"). *)
      (* iDestruct "HNCS" as "[Hheap %]". *)
      iCombine "Hheap Hproph HNCS" as "Hs".
      iDestruct "HNCS" as %HNCS.
      iSpecialize ("H" $! σ1 κ κs a with "Hs").

      unfold fupd.
      unfold bi_fupd_fupd. simpl.
      unfold uPred_fupd.
      rewrite seal_eq.
      unfold uPred_fupd_def.

      iIntros "Hw".
      iSpecialize ("H" with "Hw").
      
      repeat iMod "H".
      repeat iModIntro.

      iDestruct "H" as "[Hw [Hphi [% H]]]".
      iFrame "Hw".
      iFrame "Hphi".

      iSplitR; auto.
      iIntros (e2 σ2 efs Hstep) "Hw".
      iSpecialize ("H" $! e2 σ2 efs Hstep with "Hw").
      repeat iMod "H".
      repeat iModIntro.

      iDestruct "H" as "[Hw [Hphi H]]".
      iFrame "Hw".
      iFrame "Hphi".
      iNext.
      
      iIntros "Hw".
      iSpecialize ("H" with "Hw").
      repeat iMod "H".
      repeat iModIntro.

      iDestruct "H" as "[Hw [Hphi [Hs [H Hefs]]]]".
      iFrame "Hw".
      iFrame "Hphi".

      iFrame "Hs".
      iFrame "Hefs".

      apply no_continue_preserve in Hstep as [? ?]; auto.
      destruct (to_sval e2) eqn:eq'.
      {
        iApply (wp_no_continue_sval e2 _ φn φb φr φ1 φ2 eq' H1 with "H").
      }
      {
        iApply ("IH" $! e2 eq' H1 with "H").
      }
    }
  Qed.  
End strong_no_continue.

Lemma wp_store l (v w : val) (φ : val -> iPropI Σ) :
  no_continue w ->
  (l ↦ v)%I ∗ ▷ (l ↦ w -∗ φ #()) ⊢
  WP (Store (LitV l) (Val w)) {{ φ }} {{ bot }} {{ bot }} {{ bot }}.
Proof.
  iIntros (?) "[H Hφ]".
  rewrite wp_unfold /wp_pre; simpl.
  
  iIntros (σ1 κ κs _) "(Hs & Hp & %)".
  
  iDestruct (gen_heap_valid with "Hs H") as %?.
  
  unfold fupd.
  unfold bi_fupd_fupd. simpl.
  unfold uPred_fupd.
  rewrite seal_eq.
  unfold uPred_fupd_def.

  iIntros "[Hw Ht]".
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
    exists nil, (Val $ LitV LitUnit), (state_upd_heap <[l:=w]> σ1), nil.
    eapply Ectx_step with (K := EmptyCtx); auto.
    apply StoreS; auto. exists v; auto.
  }

  iIntros (e2 σ2 efs Hstep) "[Hw Hphi]".
  repeat iModIntro.
  iFrame "Hw Hphi".
  iModIntro.
  iIntros "[Hw Hphi]".

  assert (κ = nil /\ e2 = (Val $ LitV LitUnit) /\ σ2 = (state_upd_heap <[l:=w]> σ1) /\ efs = nil) as (? & ? & ? & ?); subst; simpl in *.
  {
    inversion Hstep.
    destruct_inversion K H2.
    - inversion H4; subst; auto.
      unfold expr_depth.singleton_ectx in H6.
      destruct_inversion K H2.
      + simpl in H6; congruence.
      + destruct_inversion K H9. inversion H3.
      + destruct_inversion K H10. inversion H3.
    - destruct_inversion K H6. inversion H4.
      unfold expr_depth.singleton_ectx in H7.
      destruct_inversion K H5. simpl in H7.
      congruence.
    - destruct_inversion K H7. inversion H4.
      unfold expr_depth.singleton_ectx in H7.
      destruct_inversion K H5. simpl in H7.
      congruence.
  }
  
  iMod (gen_heap_update with "Hs H") as "[Hs Hl]".
  
  repeat iModIntro.
  iFrame "Hw Ht".

  iSplitL "Hs Hp".
  {
    iFrame "Hs Hp".
    iPureIntro.
    assert (no_continue (#l <- w)); simpl; auto.
    pose proof no_continue_preserve _ _ _ _ _ _ H0 Hstep H2 as [_ ?].
    auto.
  }

  rewrite wp_unfold /wp_pre; simpl.
  iSplit; auto.
  iModIntro.
  iApply "Hφ".
  iApply "Hl".
Qed.


  

End multi_post.
