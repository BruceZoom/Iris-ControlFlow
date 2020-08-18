From stdpp Require Import fin_maps.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export proph_map.
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

Definition multi_post (φn φb φc φr : sval -> iPropI Σ) v : iPropI Σ :=
  match v with
  | SVal _ => φn v
  | SBreak _ => φb v
  | SContinue => φc v
  | SReturn _ => φr v
  end.

Definition top (v:sval) : iPropI Σ := bi_pure True.
Definition bot (v:sval) : iPropI Σ := bi_pure False.

Notation "'WP' e @ s ; E {{ φn } } {{ φb } } {{ φc } } {{ φr } }" := 
  (wp s E e%E (multi_post φn φb φc φr)) (at level 20, e, φn, φb, φc, φr at level 200).


(* MARK: control flow terminals *)
Lemma tac_wp_break s E v φ:
  (φ $ SBreak v) ⊢
  WP (EBreak $ Val v) @ s; E {{ bot }} {{ φ }} {{ bot }} {{ bot }}.
Proof.
  assert ((EBreak $ Val v) = (of_sval $ SBreak v)); auto.
  rewrite H.
  iIntros "Hφ".
  rewrite wp_unfold /wp_pre to_of_val.
  auto.
Qed.

Lemma tac_wp_continue s E φ:
  (φ SContinue) ⊢
  WP (EContinue) @ s; E {{ bot }} {{ bot }} {{ φ }} {{ bot }}.
Proof.
  assert (EContinue = (of_sval SContinue)); auto.
  rewrite H.
  iIntros "Hφ".
  rewrite wp_unfold /wp_pre to_of_val.
  auto.
Qed.

Lemma tac_wp_return s E v φ:
  (φ $ SReturn v) ⊢
  WP (EReturn $ Val v) @ s; E {{ bot }} {{ bot }} {{ bot }} {{ φ }}.
Proof.
  assert ((EReturn $ Val v) = (of_sval $ SReturn v)); auto.
  rewrite H.
  iIntros "Hφ".
  rewrite wp_unfold /wp_pre to_of_val.
  auto.
Qed.

End multi_post.
