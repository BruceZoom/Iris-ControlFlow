From stdpp Require Import fin_maps.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export proph_map invariants.
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
  destruct e.
  - rewrite wp_unfold /wp_pre; simpl.
    rewrite wp_unfold /wp_pre; simpl.
    iIntros (σ1 κ κs _) "[Hs Hproph]".
    (* iMod (inv_alloc ⊤ _ _ with "Hi") as "Hinv". *)
    iApply fupd_frame_l.
    iSplit.
    + iPureIntro. unfold reducible. simpl.
      exists nil, (LoopB v v), σ1, nil.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (LoopB v v) (LoopB v v)); auto.
      apply LoopBS.
    + iAssert emp%I as "Htmp"; auto.
      iMod (inv_alloc ⊤ _ _ with "Htmp") as "Hinv"; iClear "Htmp".

      iInv "Hinv" as "H1" "Hclose".

      eassert (⊤ = ↑⊤). { auto. }
      epose proof (difference_diag_L (↑⊤)).
      rewrite <- H in H0 at 1.
      (* FIXME: stuck here *)
      rewrite <- H0.
      unfold fupd.
      rewrite H0.

      Search (_ ∖ ↑_).
      SearchAbout UpClose.
      replace ∅ with (⊤ ∖ ↑⊤).
      iModIntro.

      rewrite difference_diag_L.
      epose proof (non_empty_difference (↑⊤) ⊤).
      eassert (↑⊤ ⊂ ⊤); 
      Locate union_difference_L.
      Search (_ ∖ _).
      simpl.
      replace (⊤ ∖ ↑⊤) with ⊤.
      iModIntro. 
    
    iIntros (e2 σ2 efs).

    unfold fupd. unfold bi_fupd_fupd.
    simpl.
    unfold uPred_fupd.
    Search fupd.
    unfold bi_fupd_fupd.

    simpl. unfold uPred_fupd.

    iModIntro.
    
    iFrame "H1 H2".
    destruct s.
    2:{ } 
    + unfold reducible. 
  iApply wp_bind.
    
  iPoseProof "Hinv I" as "H1".
  


End multi_post.
