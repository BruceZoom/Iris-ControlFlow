From stdpp Require Import fin_maps.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Import tactics.
From iris.algebra Require Import auth gmap.
From iris.base_logic Require Export gen_heap.
From iris.base_logic.lib Require Export proph_map invariants wsat.
From iris.program_logic Require Import atomic.
From iris.program_logic Require Export weakestpre total_weakestpre.
From iris.program_logic Require Import ectx_lifting total_ectx_lifting.
From iris_cf.throw_lang Require Export lang.
From iris_cf.throw_lang Require Import notation.
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
    (gen_heap_ctx σ.(heap) ∗ proph_map_ctx κs σ.(used_proph_id))%I;
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

Definition multi_post (φn φt : val -> iPropI Σ) v : iPropI Σ :=
  match v with
  | SVal v => φn v
  | SThrow v => φt v
  end.

Definition top (v:val) : iPropI Σ := bi_pure True.
Definition bot (v:val) : iPropI Σ := bi_pure False.

Notation "'WP' e {{ φn } } {{ φt } }" := 
  (wp NotStuck ⊤ e%E (multi_post φn φt)) (at level 20, e, φn, φt at level 200).

Notation "'{{' P } } e {{ φn } } {{ φt } }" :=
  (uPred_persistently (P -∗ WP e {{ φn }} {{ φt }})) (at level 20).


(* MARK: control flow terminals *)
Lemma tac_wp_throw v φ:
  (φ v) ⊢
  WP (Throw $ Val v) {{ bot }} {{ φ }}.
Proof.
  assert ((Throw $ Val v) = (of_sval $ SThrow v)); auto.
  rewrite H.
  iIntros "Hφ".
  rewrite wp_unfold /wp_pre language.to_of_val.
  auto.
Qed.


Lemma wp_catch_sval s e φ:
  to_sval e = Some s ->
  WP e {{ φ }} {{ φ }} ⊢
  WP Catch e {{ φ }} {{ bot }}.
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
      apply Ectx_step with EmptyCtx (Catch v) (Val v); eauto.
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
      apply Ectx_step with EmptyCtx (Catch (Throw (Val v))) (Val v); eauto.
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

Lemma tac_wp_catch e φ:
  WP e {{ φ }} {{ φ }} ⊢
  WP Catch e {{ φ }} {{ bot }}.
Proof.
  iIntros "H".
  destruct (to_sval e) eqn:eq.
  {
    iApply (wp_catch_sval s); auto.
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
      replace (Catch e) with (fill (CatchCtx EmptyCtx) e); auto.
      apply my_reducible_fill; auto.
    }

    iIntros (e2 σ2 efs Hstep) "[Hw Hphi]".

    assert (exists e1, e2 = fill (CatchCtx EmptyCtx) e1 /\ prim_step e σ1 κ e1 σ2 efs) as [e1 [? Hred]]; subst.
    {
      replace (Catch e) with (fill (CatchCtx EmptyCtx) e); auto.
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
    [iApply (wp_catch_sval s); auto |].
    iApply "IH"; auto.
  }
Qed.


Lemma wp_bind_sval s e K φn φb:
  to_sval e = Some s ->
  WP e {{ λ v, WP (fill K (Val v)) {{ φn }} {{ φb }} }}
       {{ λ v, uPred_and (uPred_pure (~ impenetrable_ectx (Throw v) K)) (φb v) }}
  ⊢ WP (fill K e) {{ φn }} {{ φb }}.
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
    destruct (to_sval (fill K (Throw v))) eqn:eq;
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
      apply throw_is_cft.

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

    pose proof throw_penetrable_preservation _ _ _ _ _ _ _ H Hstep as [? [? [? [K' [? ?]]]]].
    subst.
    iFrame "Hs".
    iSplitL; auto.
    iApply ("IH" with "[H] []"); auto.
  }
Qed.

Lemma tac_wp_bind e K φn φb:
  WP e {{ λ v, WP (fill K (Val v)) {{ φn }} {{ φb }} }}
       {{ λ v, uPred_and (uPred_pure (~ impenetrable_ectx (Throw v) K)) (φb v) }}
  ⊢ WP (fill K e) {{ φn }} {{ φb }}.
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
(* 

Lemma wp_consequence_sval s e φn φb φc φr φn' φb' φc' φr':
  to_sval e = Some s ->
  (forall v, φn v ⊢ φn' v) ->
  (forall v, φb v ⊢ φb' v) ->
  (forall v, φc v ⊢ φc' v) ->
  (forall v, φr v ⊢ φr' v) ->
  WP e {{ φn }} {{ φb }} {{ φc }} {{ φr }}
  ⊢ WP e {{ φn' }} {{ φb' }} {{ φc' }} {{ φr' }}.
Proof.
  iIntros (eq ????) "H".
  rewrite wp_unfold /wp_pre; simpl.
  rewrite wp_unfold /wp_pre; simpl.
  rewrite eq.
  iMod "H". iModIntro.
  destruct s; apply of_to_sval in eq; simpl in eq; subst; simpl;
  [by iApply H | by iApply H0 | by iApply H1 | by iApply H2].
Qed.

Lemma tac_wp_consequence e φn φb φc φr φn' φb' φc' φr':
  (forall v, φn v ⊢ φn' v) ->
  (forall v, φb v ⊢ φb' v) ->
  (forall v, φc v ⊢ φc' v) ->
  (forall v, φr v ⊢ φr' v) ->
  WP e {{ φn }} {{ φb }} {{ φc }} {{ φr }}
  ⊢ WP e {{ φn' }} {{ φb' }} {{ φc' }} {{ φr' }}.
Proof.
  iIntros (????) "H".

  iRevert (e) "H".
  iLöb as "IH".
  iIntros (e) "H".

  destruct (to_sval e) eqn:eq.
  {
    pose proof wp_consequence_sval  _ _ _ _ _ _ _ _ _ _ eq H H0 H1 H2.
    iApply H3; auto.
  }
  {
    rewrite wp_unfold /wp_pre; simpl.
    rewrite wp_unfold /wp_pre; simpl.
    rewrite eq.

    iIntros (σ1 κ κs n) "Hs".
    iSpecialize ("H" $! _ _ _ n with "Hs").
    iMod "H" as "[Hred H]". iModIntro.
    iFrame "Hred".

    iIntros (e2 σ2 efs) "Hstep".
    iSpecialize ("H" $! _ _ _ with "Hstep").
    iMod "H". iModIntro. iNext.
    iMod "H" as "[Hs [Hw Hefs]]". iModIntro.
    iFrame "Hs". iSplitR "Hefs"; auto.
    iApply "IH"; auto.
  }
Qed.

Lemma wp_lift_step e1 φn φb φc φr:
  to_sval e1 = None →
  (∀ (σ1 : state) (κ κs : list observation),
   gen_heap_ctx (heap σ1)
   ∗ proph_map_ctx (κ ++ κs) (used_proph_id σ1) ∗ ⌜no_continue_state σ1⌝
   ={⊤,∅}=∗ ⌜reducible e1 σ1⌝
            ∗ ▷ (∀ (e2 : expr) (σ2 : state) (efs : list expr),
                 ⌜prim_step e1 σ1 κ e2 σ2 efs⌝
                 ={∅,⊤}=∗ (gen_heap_ctx (heap σ2)
                              ∗ proph_map_ctx κs (used_proph_id σ2)
                                ∗ ⌜no_continue_state σ2⌝)
                             ∗ WP e2 {{φn}}{{φb}}{{φc}}{{φr} }
                               ∗ ([∗ list] ef ∈ efs, WP ef {{ _, True }})))
  ⊢ WP e1 {{ φn }} {{ φb }} {{ φc }} {{ φr }}.
Proof.
  iIntros (?) "H".
  rewrite wp_unfold /wp_pre; simpl.
  destruct (to_sval e1); subst; [inversion H |].
  iIntros (????) "Hσ".
  iMod ("H" with "Hσ") as "[$ H]".
  iIntros "!> * % !> !>".
  by iApply "H".
Qed.

Lemma wp_lift_pure_step_no_fork E' e1 φn φb φc φr:
  (forall σ1, reducible e1 σ1) →
  (∀ κ σ1 e2 σ2 efs, prim_step e1 σ1 κ e2 σ2 efs → κ = [] ∧ σ2 = σ1 ∧ efs = []) →
  (|={⊤,E'}▷=> ∀ κ e2 efs σ, ⌜prim_step e1 σ κ e2 σ efs⌝ → WP e2 {{ φn }} {{ φb }} {{ φc }} {{ φr }})
  ⊢ WP e1 {{ φn }} {{ φb }} {{ φc }} {{ φr }}.
Proof.
  iIntros (Hsafe Hstep) "H". iApply wp_lift_step.
  { specialize (Hsafe inhabitant). eauto using reducible_not_val. }
  iIntros (σ1 κ κs) "Hσ". iMod "H".
  iMod fupd_intro_mask' as "Hclose"; last iModIntro; first by set_solver. iSplit.
  { iPureIntro. auto. }
  iNext.
  iIntros (e2 σ2 efs ?).
  destruct (Hstep κ σ1 e2 σ2 efs) as (-> & <- & ->); auto.
  iMod "Hclose" as "_". iMod "H". iModIntro.
  iDestruct ("H" with "[//]") as "H". simpl. iFrame.
Qed.

Lemma wp_lift_pure_det_step_no_fork E' e1 e2 φn φb φc φr:
  (forall σ1, reducible e1 σ1) →
  (∀ σ1 κ e2' σ2 efs', prim_step e1 σ1 κ e2' σ2 efs' →
    κ = [] ∧ σ2 = σ1 ∧ e2' = e2 ∧ efs' = []) →
  (|={⊤,E'}▷=> WP e2 {{ φn }} {{ φb }} {{ φc }} {{ φr }})
  ⊢ WP e1 {{ φn }} {{ φb }} {{ φc }} {{ φr }}.
Proof.
  iIntros (? Hpuredet) "H". iApply (wp_lift_pure_step_no_fork E'); try done.
  { naive_solver. }
  iApply (step_fupd_wand with "H"); iIntros "H".
  iIntros (κ e' efs' σ (_&?&->&?)%Hpuredet); auto.
Qed.

Lemma wp_pure_step_fupd E' e1 e2 φ n φn φb φc φr :
  PureExec φ n e1 e2 →
  φ →
  (|={⊤,E'}▷=>^n WP e2 {{ φn }} {{ φb }} {{ φc }} {{ φr }})
  ⊢ WP e1 {{ φn }} {{ φb }} {{ φc }} {{ φr }}.
Proof.
  iIntros (Hexec Hφ) "Hwp".
  unfold PureExec in Hexec.
  specialize (Hexec Hφ).
  iInduction Hexec as [e|n e1 e2 e3 [Hsafe ?]] "IH"; simpl; first done.
  simpl in *.
  iApply wp_lift_pure_det_step_no_fork.
  - intros σ. specialize (Hsafe σ).
    unfold reducible_no_obs in Hsafe.
    unfold reducible.
    destruct Hsafe as [e' [sigma' [efs H]]].
    exists nil, e', sigma', efs. auto.
  - done.
  - by iApply (step_fupd_wand with "Hwp").
Qed.

Lemma wp_pure_step_later e1 e2 φ n φn φb φc φr :
  PureExec φ n e1 e2 →
  φ →
  ▷^n WP e2 {{ φn }} {{ φb }} {{ φc }} {{ φr }} ⊢ WP e1 {{ φn }} {{ φb }} {{ φc }} {{ φr }}.
Proof.
  intros Hexec ?. rewrite -wp_pure_step_fupd //. clear Hexec.
  induction n as [|n IH]; by rewrite //= -step_fupd_intro // IH.
Qed.

Lemma wp_seq_sval s e1 e2 φn φb φc φr:
  to_sval e1 = Some s ->
  WP e1 {{ λ v, ▷ ▷ WP e2 {{ φn }} {{ φb }} {{ φc }} {{ φr }} }} {{ φb }} {{ φc }} {{ φr }} ⊢
  WP (Seq e1 e2) {{ φn }} {{ φb }} {{ φc }} {{ φr }}.
Proof.
  iIntros (eq) "H".

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

    assert (PureExec True 1 ((λ: <>, e2)%V v) e2).
    {
      unfold PureExec.
      intros _.
      eapply relations.nsteps_l; [| apply relations.nsteps_O].
      eapply Build_pure_step; simpl.
      - intros. unfold reducible_no_obs.
        exists e2, σ1, nil.
        apply (Ectx_step _ _ _ _ _ _ EmptyCtx ((λ: <>, e2)%V v) e2); auto.
        constructor; auto.
      - intros.
        inversion H0.
        destruct_inversion K H1.
        + inversion H3; subst; auto.
          unfold expr_depth.singleton_ectx in H5.
          destruct_inversion K H1; simpl in *; try congruence.
          * destruct_inversion K H5. simpl in *. subst.
            inversion H2.
          * destruct_inversion K H5. simpl in *. subst.
            inversion H2.
        + destruct_inversion K H5.
          inversion H3; subst.
          destruct_inversion K H4.
          inversion H5.
        + destruct_inversion K H6.
          inversion H3; subst.
          destruct_inversion K H4.
          inversion H5.
    }
    iApply wp_pure_step_later; auto.
  }
  1, 2, 3:
    rewrite wp_unfold /wp_pre; simpl;
    rewrite wp_unfold /wp_pre; simpl;

    unfold fupd;
    unfold bi_fupd_fupd; simpl;
    unfold uPred_fupd;
    rewrite seal_eq;
    unfold uPred_fupd_def;

    iIntros (σ1 κ κs _) "Hs Hw";
    iSpecialize ("H" with "Hw");

    repeat iMod "H";
    iDestruct "H" as "[Hw [Htop H]]";
    iApply except_0_bupd;
    iModIntro;
    
    iApply bupd_frame_l;
    iFrame "Hw";
    iApply bupd_frame_r;
    iPoseProof ownE_empty as "Hown_phi";
    iFrame "Hown_phi".

  {
    iSplitR.
    {
      iPureIntro.
      exists nil, (EBreak v), σ1, nil.
      pose proof Ectx_step.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (fill (AppRCtx (Rec BAnon BAnon e2) EmptyCtx) (EBreak v)) (EBreak v)); auto.
      constructor.
      - apply break_is_cft.
      - unfold expr_depth.singleton_ectx. auto.
      - unfold not; inversion 1; subst; simpl in *.
        destruct_inversion K' H1; try congruence.
        destruct_inversion K' H6.
        inversion H4; subst; simpl in *.
        destruct_inversion K' H5; simpl in *; try congruence.
    }
    iIntros (e0 σ2 efs H) "[Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Hphi".
    iIntros "!# [Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Htop".

    assert (σ1 = σ2 /\ κ = [] /\ efs = [] /\ e0 = EBreak (Val v)) as [? [? [? ?]]]; subst.
    {
      inversion H; subst; simpl in *.
      destruct_inversion K H0.
      + inversion H2; subst; simpl in *.
        unfold expr_depth.singleton_ectx in H4.
        destruct_inversion K H0; simpl in *; try congruence.
        destruct_inversion K H8; auto.
        destruct_inversion K H7. inversion H3.
      + destruct_inversion K H4.
        - sval_head_step_inv H2.
        - destruct_inversion K H3.
          sval_head_step_inv H2.
    }

    iFrame.
    iSplitL; auto.

    rewrite wp_unfold /wp_pre; simpl.
    auto.
  }

  {
      iSplitR.
      {
        iPureIntro.
        exists nil, EContinue, σ1, nil.
        pose proof Ectx_step.
        apply (Ectx_step _ _ _ _ _ _ EmptyCtx (fill (AppRCtx (Rec BAnon BAnon e2) EmptyCtx) EContinue) EContinue); auto.
        constructor.
        - apply continue_is_cft.
        - unfold expr_depth.singleton_ectx. auto.
        - unfold not; inversion 1; subst; simpl in *.
          destruct_inversion K' H1; try congruence.
          destruct_inversion K' H6.
          inversion H4; subst; simpl in *.
          destruct_inversion K' H5; simpl in *; try congruence.
      }
      iIntros (e0 σ2 efs H) "[Hw Hphi]".
      repeat iModIntro.
      iFrame "Hw". iFrame "Hphi".
      iIntros "!# [Hw Hphi]".
      repeat iModIntro.
      iFrame "Hw". iFrame "Htop".

    assert (σ1 = σ2 /\ κ = [] /\ efs = [] /\ e0 = EContinue) as [? [? [? ?]]]; subst.
    {
      inversion H; subst; simpl in *.
      destruct_inversion K H0.
      + inversion H2; subst; simpl in *.
        unfold expr_depth.singleton_ectx in H4.
        destruct_inversion K H0; simpl in *; try congruence.
        destruct_inversion K H8; auto.
      + destruct_inversion K H4.
        sval_head_step_inv H2.
    }

    iFrame.
    iSplitL; auto.

    rewrite wp_unfold /wp_pre; simpl.
    auto.
  }

  {
    iSplitR.
    {
      iPureIntro.
      exists nil, (EReturn v), σ1, nil.
      pose proof Ectx_step.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx (fill (AppRCtx (Rec BAnon BAnon e2) EmptyCtx) (EReturn v)) (EReturn v)); auto.
      constructor.
      - apply return_is_cft.
      - unfold expr_depth.singleton_ectx. auto.
      - unfold not; inversion 1; subst; simpl in *.
        destruct_inversion K' H1; try congruence.
        destruct_inversion K' H6.
        inversion H4; subst; simpl in *.
        destruct_inversion K' H5; simpl in *; try congruence.
    }
    iIntros (e0 σ2 efs H) "[Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Hphi".
    iIntros "!# [Hw Hphi]".
    repeat iModIntro.
    iFrame "Hw". iFrame "Htop".

    assert (σ1 = σ2 /\ κ = [] /\ efs = [] /\ e0 = EReturn (Val v)) as [? [? [? ?]]]; subst.
    {
      inversion H; subst; simpl in *.
      destruct_inversion K H0.
      + inversion H2; subst; simpl in *.
        unfold expr_depth.singleton_ectx in H4.
        destruct_inversion K H0; simpl in *; try congruence.
        destruct_inversion K H8; auto.
        destruct_inversion K H7. inversion H3.
      + destruct_inversion K H4.
        - sval_head_step_inv H2.
        - destruct_inversion K H3.
          sval_head_step_inv H2.
    }

    iFrame.
    iSplitL; auto.

    rewrite wp_unfold /wp_pre; simpl.
    auto.
  }
Qed.

Lemma seq_pure_exec (v : val) e2:
  PureExec True 2 (v;; e2) e2.
Proof.
  unfold PureExec.
  intros _.
  eapply relations.nsteps_l with ((λ: <>, e2)%V v).
  {
    apply Build_pure_step.
    + intros. unfold reducible_no_obs.
      exists ((λ: <>, e2)%V v), σ1, nil.
      apply (Ectx_step _ _ _ _ _ _ (AppLCtx EmptyCtx v) (Rec BAnon BAnon e2) (RecV BAnon BAnon e2)); auto.
      constructor.
    + intros.
      inversion H; subst; simpl in *.
      destruct_inversion K H0; simpl in *.
      - inversion H2; subst; simpl in *.
        unfold expr_depth.singleton_ectx in H4.
        destruct_inversion K H0; simpl in *; try congruence.
        * destruct_inversion K H7. inversion H3.
        * destruct_inversion K H8; inversion H3.
      - destruct_inversion K H0.
        inversion H2; subst; simpl in *; auto.
        unfold expr_depth.singleton_ectx in H5.
        destruct_inversion K H1; simpl in *; try congruence.
      - destruct_inversion K H4.
        sval_head_step_inv H2.
  }
  eapply relations.nsteps_l; [| apply relations.nsteps_O].
  {
    apply Build_pure_step.
    + intros. unfold reducible_no_obs.
      exists e2, σ1, nil.
      apply (Ectx_step _ _ _ _ _ _ EmptyCtx ((λ: <>, e2)%V v) e2); auto.
      constructor. auto.
    + intros.
      inversion H; subst; simpl in *.
      destruct_inversion K H0; simpl in *.
      - inversion H2; subst; simpl in *; auto.
        unfold expr_depth.singleton_ectx in H4.
        destruct_inversion K H0; simpl in *; try congruence.
        * destruct_inversion K H7. inversion H3.
        * destruct_inversion K H8; inversion H3.
      - destruct_inversion K H0.
        inversion H2; subst; simpl in *; auto.
        unfold expr_depth.singleton_ectx in H5.
        destruct_inversion K H1; simpl in *; try congruence.
      - destruct_inversion K H4.
        sval_head_step_inv H2.
  }
Qed.

Lemma tac_wp_seq e1 e2 φn φb φc φr:
  WP e1 {{ λ v, ▷ ▷ WP e2 {{ φn }} {{ φb }} {{ φc }} {{ φr }} }} {{ φb }} {{ φc }} {{ φr }} ⊢
  WP (Seq e1 e2) {{ φn }} {{ φb }} {{ φc }} {{ φr }}.
Proof.
  iIntros "H".
  destruct (to_sval e1) eqn:eq.
  {
    iApply (wp_seq_sval s); auto.
  }
  {
    replace (App (Rec BAnon BAnon e2) e1) with (fill (AppRCtx (Rec BAnon BAnon e2) EmptyCtx) e1); auto.
    iApply tac_wp_bind.
    iApply (tac_wp_consequence with "H").
    {
      iIntros (?) "H".
      pose proof seq_pure_exec v e2. simpl.
      pose proof wp_pure_step_later (v;; e2) e2 _ 2 φn φb φc φr H.
      simpl in H0.
      iApply H0; auto.
    }
    {
      simpl.
      iIntros (v) "H".
      iSplit; auto.
      iPureIntro.
      unfold not.
      intros H; inversion H; subst; simpl in *.
      destruct_inversion K' H0; try congruence.
      destruct_inversion K' H5; try congruence.
      inversion H3; subst; simpl in *.
      destruct_inversion K' H4; simpl in H5; congruence.
    }
    {
      simpl.
      iIntros (v) "H".
      iSplit; auto.
      iPureIntro.
      unfold not.
      intros H; inversion H; subst; simpl in *.
      destruct_inversion K' H0; try congruence.
      destruct_inversion K' H5; try congruence.
      inversion H3; subst; simpl in *.
      destruct_inversion K' H4; simpl in H5; congruence.
    }
    {
      simpl.
      iIntros (v) "H".
      iSplit; auto.
      iPureIntro.
      unfold not.
      intros H; inversion H; subst; simpl in *.
      destruct_inversion K' H0; try congruence.
      destruct_inversion K' H5; try congruence.
      inversion H3; subst; simpl in *.
      destruct_inversion K' H4; simpl in H5; congruence.
    }
  }
Qed.

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
Qed. *)

Print Assumptions tac_wp_break.
Print Assumptions tac_wp_continue.
Print Assumptions tac_wp_return.
Print Assumptions tac_wp_bind.
Print Assumptions tac_wp_loop.
Print Assumptions tac_wp_call.
Print Assumptions tac_wp_consequence.
Print Assumptions tac_wp_seq.
Print Assumptions wp_no_continue.

End multi_post.