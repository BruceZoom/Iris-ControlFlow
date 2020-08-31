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
(* Lemma wp_loop_aux e0 e I φb φr:
  {{ I }} e0 {{ λ v, I }} {{ φb }} {{ λ v, I }} {{ φr }} -∗
  WP e {{ λ v, I }} {{ φb }} {{ λ v, I }} {{ φr }} -∗
  WP LoopB e0 e {{φb}}{{bot}}{{bot}}{{φr}}.
Proof.
  iIntros "#Hbdy H".
  destruct (to_sval e) eqn:eq.
  {
    admit.
  }
  {
    (* iPoseProof ("Hbdy" with "H") as "H1". *)
    (* iClear "Hbdy". *)
    iRevert (e eq) "H".
    iLöb as "IH".
    iIntros (e eq) "H".

    repeat rewrite wp_unfold.
    rewrite <- wp_unfold at 1.
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
    iFrame "Hw". iFrame "Hphi".

    destruct H as [κ' [e' [σ' [efs Hred]]]].

    iSplitR; [iPureIntro | ].
    {
      exists κ', (LoopB e0 e'), σ', efs.
      inversion Hred; subst.
      apply Ectx_step with (LoopBCtx e0 (comp_ectx K EmptyCtx)) e1' e2'; simpl;
      [rewrite <- fill_comp | rewrite <- fill_comp |]; auto.
    }

    iIntros (e2 σ2 efes0 Hstep) "Hw".

    assert (κ' = κ /\ e2 = LoopB e0 e' /\ σ2 = σ' /\ efes0 = efs) as [? [? [? ?]]].
    {
      admit.
    }
    subst.

    iSpecialize ("H" $! e' σ' efs Hred with "Hw").

    repeat iMod "H".
    repeat iModIntro.
    iDestruct "H" as "[Hw [Hphi H]]".
    iFrame "Hw". iFrame "Hphi".
    iNext.

    iIntros "Hw".
    iSpecialize ("H" with "Hw").

    repeat iMod "H".
    repeat iModIntro.
    iDestruct "H" as "[Hw [Hphi H]]".
    iFrame "Hw". iFrame "Hphi".

    iDestruct "H" as "[Hs [Hwp Hefs]]".
    iFrame "Hs". iSplitR "Hefs"; auto.



    iApply "IH"; auto.
  } *)

Lemma tac_wp_loop e I φb φr:
  {{ I }} e {{ λ v, I }} {{ φb }} {{ λ v, I }} {{ φr }} ⊢
  {{ I }} (loop e) {{ φb }} {{ bot }} {{ bot }} {{ φr }}.
Proof.
  iIntros "#Hbdy !# H".
  iLöb as "IH0".
  destruct (to_sval e) eqn:eq.
  {
    iLöb as "IH".
    destruct s;
    apply of_to_sval in eq; simpl in eq; subst.
    
    - rewrite wp_unfold /wp_pre; simpl.
      rewrite wp_unfold. rewrite <- wp_unfold at 1.
      rewrite /wp_pre; simpl.
      iIntros (σ1 κ κs _) "Hs".
      iApply fupd_frame_l.
      iSplit.
      + iPureIntro. unfold reducible. simpl.
        exists nil, (LoopB v v), σ1, nil.
        apply (Ectx_step _ _ _ _ _ _ EmptyCtx (LoopB v v) (LoopB v v)); auto.
        apply LoopBS.
      + 
        (* unfold fupd at 2. *)
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

        iIntros (? ? ? Hstep) "[Hw Hphi]".
        repeat iModIntro.
        iFrame "Hw". iFrame "Hphi".
        
        iIntros "!# [Hw _]".

        repeat iModIntro.
        iFrame "Hw". iFrame "Htop".

        assert (a = (LoopB (Val v) (Val v)) /\ σ1 = a0 /\ κ = [] /\ a1 = []).
        {
          inversion Hstep.
          destruct K; inversion H; subst.
          - simpl in *; subst.
            inversion H1; subst; auto.
            destruct K; inversion H; subst; try congruence.
            destruct K; inversion H7; simpl in *; subst.
            inversion H0.
          - destruct K; inversion H4; simpl in *; subst.
            inversion H1; subst.
            destruct K; inversion H2; simpl in *; subst.
            auto.
        }
        destruct H as [? [? [? ?]]]; subst.

        iFrame "Hs".

        iSplitL; auto.
        iApply "IH".
        auto.
    - admit.
    - admit.
    - admit.
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

    destruct H as [κ' [e' [σ' [efs Hred]]]].

    iSplitR; [iPureIntro | ].
    {
      exists κ', (LoopB e0 e'), σ', efs.
      inversion Hred; subst.
      apply Ectx_step with (LoopBCtx e0 (comp_ectx K EmptyCtx)) e1' e2'; simpl;
      [rewrite <- fill_comp | rewrite <- fill_comp |]; auto.
    }

    iIntros (e2 σ2 efes0 Hstep) "Hw".

    assert (κ' = κ /\ e2 = LoopB e0 e' /\ σ2 = σ' /\ efes0 = efs) as [? [? [? ?]]].
    {
      admit.
    }
    subst.

    iSpecialize ("H1" $! e' σ' efs Hred with "Hw").

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

    destruct (to_sval e') eqn:eq'; [| iApply "IH"; auto].

    (* Cases when body reduces to terminals *)
    iClear "IH".
    destruct s; apply of_to_sval in eq'; simpl in eq'; subst.
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
      + 
        (* unfold fupd at 2. *)
        unfold bi_fupd_fupd. simpl.
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

        assert (a0 = (LoopB e0 e0) /\ a1 = σ0 /\ κ0 = [] /\ a2 = []) as [? [? [? ?]]].
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
            destruct K; inversion H2; simpl in *; subst.
            auto.
        }
        subst.

        iFrame "Hs".

        iSplitL; auto.
        iApply "IH0"; auto.
      - admit.
      - admit.
      - admit.
  }
Admitted.
    

End multi_post.
