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
Lemma tac_wp_loop e I φb φr:
  {{ I }} e {{ λ v, I }} {{ φb }} {{ λ v, I }} {{ φr }} ⊢
  {{ I }} (loop e) {{ φb }} {{ bot }} {{ bot }} {{ φr }}.
Proof.
  iIntros "#Hbdy !# H".
  iLöb as "IH".
  destruct e.
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
Admitted.
    

End multi_post.
