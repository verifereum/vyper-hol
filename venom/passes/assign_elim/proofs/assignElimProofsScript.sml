(*
 * Assign Elimination — Function-Level Proofs
 *
 * Composes per-instruction soundness (assignElimSound) with
 * convergence (assignElimConvergence) to prove full function-level
 * correctness: assign_elim_function_correct_proof.
 *
 * TOP-LEVEL: assign_elim_function_correct_proof
 *)

Theory assignElimProofs
Ancestors
  assignElimSound assignElimConvergence
  analysisSimProps analysisSimProofsBase
  passSimulationProps venomWf venomInstProps
  cfgAnalysisProps

open assignElimDefsTheory assignElimSoundTheory assignElimConvergenceTheory
     passSharedDefsTheory passSharedPropsTheory
     venomStateTheory venomWfTheory
     analysisSimDefsTheory analysisSimPropsTheory
     passSimulationPropsTheory passSimulationDefsTheory
     stateEquivTheory stateEquivPropsTheory
     execEquivParamDefsTheory execEquivParamPropsTheory
     venomExecSemanticsTheory finite_mapTheory
     listTheory pred_setTheory venomInstTheory
     dfAnalyzeDefsTheory dfAnalyzeProofsTheory
     cfgHelpersTheory worklistDefsTheory arithmeticTheory
     cfgAnalysisPropsTheory

(* ===== Copy-prop specific: function-level simulation ===== *)

(* Forward-specialized fixpoint/transfer theorems *)
val fixpoint_restricted_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_analyze_fixpoint_process_restricted));
val intra_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_at_intra_transfer_proof));
val boundary_fixpoint_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_boundary_fixpoint_proof));

(* copy_prop_join from right preserves soundness when b <> NONE *)
Theorem copy_sound_join_right[local]:
  !a b s. copy_sound_opt b s /\ b <> NONE ==>
          copy_sound_opt (copy_prop_join a b) s
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[copy_sound_opt_def, copy_prop_join_def] >>
  rpt strip_tac >>
  rename1 `copy_sound (copy_prop_join_raw m1 m2) s` >>
  fs[copy_sound_def, copy_prop_join_raw_def] >>
  rpt strip_tac >>
  fs[FLOOKUP_DRESTRICT, copy_agree_def] >>
  Cases_on `FLOOKUP m2 x` >> gvs[]
QED

Theorem copy_sound_join_left[local]:
  !a b s. copy_sound_opt a s /\ a <> NONE ==>
          copy_sound_opt (copy_prop_join a b) s
Proof
  Cases_on `a` >> Cases_on `b` >>
  simp[copy_sound_opt_def, copy_prop_join_def] >>
  rpt strip_tac >>
  rename1 `copy_sound (copy_prop_join_raw m1 m2) s` >>
  fs[copy_sound_def, copy_prop_join_raw_def] >>
  rpt strip_tac >>
  fs[FLOOKUP_DRESTRICT]
QED

Theorem foldl_join_sound_gen[local]:
  !vals acc v s.
    MEM v (acc :: vals) /\ v <> NONE /\ copy_sound_opt v s ==>
    copy_sound_opt (FOLDL copy_prop_join acc vals) s
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum (qspecl_then [`copy_prop_join acc h`] mp_tac) >>
  disch_then irule
  >- (qexists_tac `copy_prop_join acc h` >> simp[] >>
      conj_tac
      >- (Cases_on `acc` >> Cases_on `h` >> fs[copy_prop_join_def])
      >- (irule copy_sound_join_left >> fs[]))
  >- (qexists_tac `copy_prop_join acc h` >> simp[] >>
      conj_tac
      >- (Cases_on `acc` >> Cases_on `h` >> fs[copy_prop_join_def])
      >- (irule copy_sound_join_right >> fs[]))
  >- (qexists_tac `v` >> fs[])
QED

Theorem foldl_join_sound[local]:
  !vals v s.
    MEM v vals /\ v <> NONE /\ copy_sound_opt v s ==>
    copy_sound_opt (FOLDL copy_prop_join NONE vals) s
Proof
  rpt strip_tac >>
  irule foldl_join_sound_gen >> metis_tac[MEM]
QED

(* cfg_analyze field accessor lemmas — avoids repeated pair destruct.
   Common tactic pattern: after simp[cfg_analyze_def, LET_THM], need
   Cases_on entry_block, Cases_on dfs_post_walk, Cases_on dfs_pre_walk *)

(* copy_sound_opt does not depend on vs_inst_idx *)
Theorem copy_sound_opt_inst_idx[local]:
  !v s k. copy_sound_opt v s <=> copy_sound_opt v (s with vs_inst_idx := k)
Proof
  Cases_on `v` >> rw[copy_sound_opt_def, copy_sound_def] >>
  eq_tac >> rpt strip_tac >> res_tac >>
  Cases_on `op` >> fs[eval_operand_def, lookup_var_def]
QED

(* After run_block OK (non-halted), soundness transfers from entry to exit.
   Requires: no non-last instruction is a terminator. *)
(* Fixpoint property of copy_prop analysis *)
Triviality copy_prop_is_fixpoint[local]:
  !fn. fn_inst_wf fn ==>
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
Proof
  gen_tac >> strip_tac >>
  irule fixpoint_restricted_fwd >>
  conj_tac
  >- (match_mp_tac (SIMP_RULE std_ss [LET_THM]
        dfAnalyzeProofsTheory.df_process_deps_complete_proof |>
        SPEC ``Forward : direction`` |>
        SIMP_RULE std_ss [dfAnalyzeDefsTheory.direction_case_def]) >>
      rw[copy_prop_join_absorption] >>
      metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond])
  >>
  qexistsl_tac [
    `copy_prop_measure_inv fn`,
    `copy_prop_measure_bound fn`,
    `copy_prop_measure fn`,
    `\lbl. MEM lbl (cfg_analyze fn).cfg_dfs_pre`] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule copy_prop_measure_bounded >>
      fs[copy_prop_measure_inv_def])
  >- (rpt strip_tac >> fs[] >>
      metis_tac[copy_prop_measure_inv_preserved])
  >- (rpt strip_tac >> fs[] >>
      metis_tac[copy_prop_measure_monotone])
  >- (rpt strip_tac >> fs[] >>
      imp_res_tac analysisSimPropsTheory.cfg_dfs_pre_succs_closed >>
      fs[EVERY_MEM])
  >- simp[EVERY_MEM]
  >- (mp_tac (SPEC_ALL copy_prop_measure_inv_initial) >>
      Cases_on `fn_entry_label fn` >> simp[] >> metis_tac[])
QED

(* Remove is_fixpoint_def from srw_ss() — its expansion breaks
   imp_res_tac intra_fwd / boundary_fixpoint_fwd when is_fixpoint
   is an assumption. *)
val _ = delsimps ["is_fixpoint_def"];

(* ===== Pre-instantiated dataflow theorems for copy_prop ===== *)
(* These eliminate the generic polymorphic parameters so drule/drule_all
   can match directly against copy_prop-specific assumptions. *)

Triviality copy_prop_intra_fwd[local]:
  !fn lbl bb idx.
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    SUC idx <= LENGTH bb.bb_instructions
    ==>
    df_at NONE
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
      lbl (SUC idx) =
    copy_prop_transfer (phi_used_vars fn) (EL idx bb.bb_instructions)
      (df_at NONE
        (df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
        lbl idx)
Proof
  rpt strip_tac >> imp_res_tac intra_fwd >> simp_tac std_ss []
QED

Triviality copy_prop_boundary_fixpoint[local]:
  !fn lbl bb.
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb
    ==>
    df_boundary NONE
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
      lbl =
    copy_prop_join
      (df_boundary NONE
        (df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
        lbl)
      (df_at NONE
        (df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
        lbl (LENGTH bb.bb_instructions))
Proof
  rpt strip_tac >> imp_res_tac boundary_fixpoint_fwd >> first_assum ACCEPT_TAC
QED

(* copy_prop_inter_fwd_gen: like inter_fwd but doesn't require lookup_block.
   For Forward direction, df_at lbl 0 = joined regardless of block existence.
   Proof: at fixpoint, df_process_block writes (lbl,0) -> joined to ds_inst
   via df_fold_forward (even with empty instrs when lookup_block = NONE). *)
Triviality copy_prop_inter_fwd_gen[local]:
  !fn lbl.
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre
    ==>
    df_at NONE
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
      lbl 0 =
    copy_prop_joined fn
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
      lbl
Proof
  rpt strip_tac >>
  qabbrev_tac `result = df_analyze Forward NONE copy_prop_join copy_prop_transfer
    copy_prop_edge_transfer (phi_used_vars fn)
    (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn` >>
  (* At fixpoint, process lbl result = result *)
  fs[worklistDefsTheory.is_fixpoint_def] >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >>
  simp[dfAnalyzeDefsTheory.df_process_block_def,
       dfAnalyzeDefsTheory.df_joined_val_def] >>
  pairarg_tac >> simp[] >>
  strip_tac >>
  (* inst_map SUBMAP result.ds_inst *)
  `inst_map ⊌ result.ds_inst = result.ds_inst` by
    (qpat_x_assum `<|ds_inst := _; ds_boundary := _|> = result` mp_tac >>
     rw[dfAnalyzeDefsTheory.df_state_component_equality]) >>
  `inst_map ⊑ result.ds_inst` by
    metis_tac[finite_mapTheory.SUBMAP_FUNION_ABSORPTION] >>
  (* Unfold df_fold_block, then use df_fold_forward_at *)
  fs[dfAnalyzeDefsTheory.df_fold_block_def] >>
  drule dfAnalyzeProofsTheory.df_fold_forward_at >> strip_tac >>
  `FLOOKUP result.ds_inst (lbl, 0) =
   FLOOKUP inst_map (lbl, 0)` by
    metis_tac[finite_mapTheory.SUBMAP_FLOOKUP_EQN] >>
  fs[dfAnalyzeDefsTheory.df_at_def] >>
  simp[copy_prop_joined_def, copy_prop_edge_transfer_def, LET_THM] >>
  Cases_on `fn_entry_label fn` >> gvs[]
QED

Triviality copy_prop_df_at_not_none[local]:
  !fn lbl bb.
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb.bb_instructions <> []
    ==>
    df_at NONE
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
      lbl (LENGTH bb.bb_instructions) <> NONE
Proof
  rpt strip_tac >>
  `SUC (LENGTH bb.bb_instructions - 1) <= LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  drule_all copy_prop_intra_fwd >> strip_tac >>
  `copy_prop_transfer (phi_used_vars fn)
     (EL (LENGTH bb.bb_instructions - 1) bb.bb_instructions)
     (df_at NONE
       (df_analyze Forward NONE copy_prop_join copy_prop_transfer
          copy_prop_edge_transfer (phi_used_vars fn)
          (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
       lbl (LENGTH bb.bb_instructions - 1)) <> NONE` by
    simp_tac std_ss [copy_prop_transfer_def, LET_THM] >>
  `SUC (LENGTH bb.bb_instructions - 1) = LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  metis_tac[]
QED

(* Pre-instantiated: entry soundness ==> exit soundness for copy_prop *)
Triviality copy_prop_exit_sound[local]:
  !fn bb fuel ctx s v.
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    wf_function fn /\
    fn_inst_wf fn /\ ALL_DISTINCT (fn_labels fn) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    copy_sound_opt
      (df_at NONE
        (df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
        bb.bb_label 0) s /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK v
    ==>
    copy_sound_opt
      (df_at NONE
        (df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
        bb.bb_label (LENGTH bb.bb_instructions)) v
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by
    metis_tac[venomExecPropsTheory.run_block_ok_nonempty] >>
  (* Find the terminator index *)
  qabbrev_tac `ti = PRE (LENGTH bb.bb_instructions)` >>
  `ti < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[Abbr `ti`]) >>
  `is_terminator (EL ti bb.bb_instructions).inst_opcode` by (
    `bb_well_formed bb` by (fs[wf_function_def] >> metis_tac[]) >>
    fs[bb_well_formed_def, Abbr `ti`] >>
    Cases_on `bb.bb_instructions` >> fs[LAST_EL]) >>
  `!j. j < ti ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode` by (
    rpt strip_tac >> first_x_assum (qspec_then `bb` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    disch_then (qspec_then `j` mp_tac) >>
    impl_tac >- fs[Abbr `ti`] >> simp[]) >>
  `SUC ti = LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[Abbr `ti`]) >>
  (* Use transfer_sound_exit *)
  `copy_sound_opt
     (df_at NONE
       (df_analyze Forward NONE copy_prop_join copy_prop_transfer
          copy_prop_edge_transfer (phi_used_vars fn)
          (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
       bb.bb_label (SUC ti)) v` by (
    mp_tac (ISPECL [
      ``state_equiv {} : venom_state -> venom_state -> bool``,
      ``execution_equiv {} : venom_state -> venom_state -> bool``,
      ``copy_sound_opt``,
      ``copy_prop_transfer``,
      ``phi_used_vars fn``,
      ``bb : basic_block``,
      ``NONE : copy_lattice option``,
      ``df_analyze Forward NONE copy_prop_join copy_prop_transfer
          copy_prop_edge_transfer (phi_used_vars fn)
          (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn``]
      analysisSimPropsTheory.transfer_sound_exit) >>
    impl_tac >- (
      rpt conj_tac
      >- simp[state_equiv_execution_equiv_valid_state_rel]
      >- metis_tac[copy_prop_transfer_sound]
      >- (rpt strip_tac >> metis_tac[copy_sound_opt_state_equiv])
      >- (rpt strip_tac >> imp_res_tac intra_fwd >> simp_tac std_ss [])) >>
    disch_then (qspecl_then [`fuel`, `ctx`, `s`, `v`, `ti`] mp_tac) >>
    simp[]) >>
  metis_tac[]
QED

(* If one predecessor boundary is sound/non-NONE, then copy_prop_joined is sound.
   Abstracts over the entry-label wrapping. *)
Triviality copy_prop_joined_sound_from_pred[local]:
  !fn result lbl v nbr.
    MEM nbr (cfg_preds_of (cfg_analyze fn) lbl) /\
    df_boundary NONE result nbr <> NONE /\
    copy_sound_opt (df_boundary NONE result nbr) v
    ==>
    copy_sound_opt (copy_prop_joined fn result lbl) v
Proof
  rpt strip_tac >>
  simp[copy_prop_joined_def, LET_THM] >>
  (* MEM nbr implies MAP is non-empty *)
  `MAP (\nbr. df_boundary NONE result nbr)
       (cfg_preds_of (cfg_analyze fn) lbl) <> []` by
    (strip_tac >> fs[MAP_EQ_NIL, MEM]) >>
  Cases_on `MAP (\nbr. df_boundary NONE result nbr)
                (cfg_preds_of (cfg_analyze fn) lbl)`
  >- fs[]
  >>
  simp[] >>
  (* Base = FOLDL NONE (h::t) is sound *)
  `MEM (df_boundary NONE result nbr) (h::t)` by (
    qpat_assum `MAP _ _ = _` (fn th => REWRITE_TAC [SYM th]) >>
    simp[MEM_MAP] >> qexists_tac `nbr` >> simp[]) >>
  `copy_sound_opt (FOLDL copy_prop_join NONE (h::t)) v` by
    metis_tac[foldl_join_sound] >>
  (* Entry wrapping preserves soundness *)
  Cases_on `fn_entry_label fn` >> gvs[] >>
  TRY (IF_CASES_TAC >> gvs[]) >>
  TRY (irule copy_prop_join_sound >> simp[copy_sound_opt_fempty])
QED

(* After running a block OK with entry soundness at fixpoint,
   the successor has entry soundness too *)
Triviality successor_entry_sound[local]:
  !fn bb fuel ctx s v.
    let pv = phi_used_vars fn in
    let ev = OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) in
    let result = df_analyze Forward NONE copy_prop_join
      copy_prop_transfer copy_prop_edge_transfer pv ev fn in
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer pv ev (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    wf_function fn /\
    fn_inst_wf fn /\ ALL_DISTINCT (fn_labels fn) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    bb.bb_label = s.vs_current_bb /\
    MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\
    copy_sound_opt (df_at NONE result s.vs_current_bb 0) s /\
    run_block fuel ctx bb s = OK v
    ==>
    copy_sound_opt (df_at NONE result v.vs_current_bb 0) v
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `bb.bb_instructions <> []` by metis_tac[venomExecPropsTheory.run_block_ok_nonempty] >>
  `EVERY inst_wf bb.bb_instructions` by (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by metis_tac[] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule venomExecPropsTheory.MEM_lookup_block >> simp[GSYM fn_labels_def]) >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by metis_tac[] >>
  (* Normalize: use bb.bb_label everywhere instead of s.vs_current_bb *)
  qpat_x_assum `bb.bb_label = s.vs_current_bb`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  (* Step 1: Exit soundness (entry → exit via intra-block transfer) *)
  drule_all copy_prop_exit_sound >> strip_tac >>
  (* Step 2: df_at exit <> NONE *)
  drule_all copy_prop_df_at_not_none >> strip_tac >>
  (* Step 3: Boundary fixpoint equation *)
  drule_all copy_prop_boundary_fixpoint >> strip_tac >>
  (* Step 4: Boundary soundness via join_right *)
  `copy_sound_opt (df_boundary NONE
     (df_analyze Forward NONE copy_prop_join copy_prop_transfer
        copy_prop_edge_transfer (phi_used_vars fn)
        (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
     bb.bb_label) v` by metis_tac[copy_sound_join_right] >>
  (* Step 5: Successor location *)
  `MEM v.vs_current_bb (bb_succs bb)` by
    metis_tac[venomExecPropsTheory.run_block_current_bb_in_succs] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfgAnalysisPropsTheory.bb_succs_in_cfg_succs] >>
  `MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
    (imp_res_tac analysisSimPropsTheory.cfg_dfs_pre_succs_closed >> gvs[EVERY_MEM]) >>
  `MEM bb.bb_label (cfg_preds_of (cfg_analyze fn) v.vs_current_bb)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  (* Step 6: Successor entry via inter-block transfer (no lookup_block needed) *)
  mp_tac (Q.SPECL [`fn`, `v.vs_current_bb`] copy_prop_inter_fwd_gen) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (fn inter_th => REWRITE_TAC [inter_th]) >>
  (* Step 6b: use helper — boundary <> NONE + sound implies joined is sound *)
  irule copy_prop_joined_sound_from_pred >>
  qexists_tac `bb.bb_label` >> rpt conj_tac
  >- ( (* df_boundary <> NONE: fixpoint boundary = join(boundary, exit), exit <> NONE *)
      strip_tac >>
      Cases_on `df_at NONE
         (df_analyze Forward NONE copy_prop_join copy_prop_transfer
            copy_prop_edge_transfer (phi_used_vars fn)
            (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
         bb.bb_label (LENGTH bb.bb_instructions)` >>
      gvs[copy_prop_join_def])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
QED

Triviality copy_prop_join_FEMPTY[local]:
  !x. copy_prop_join (SOME FEMPTY) x = SOME FEMPTY
Proof
  Cases >> simp[copy_prop_join_def, copy_prop_join_raw_def, DRESTRICT_FEMPTY]
QED

Triviality copy_sound_opt_at_entry[local]:
  fn_inst_wf fn /\
  fn_entry_label fn = SOME lbl
  ==>
  copy_sound_opt (df_at NONE (copy_prop_analyze fn) lbl 0) s
Proof
  rpt strip_tac >>
  (* Derive MEM lbl cfg_dfs_pre from fn_entry_label *)
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by (
    fs[fn_entry_label_def] >>
    Cases_on `entry_block fn` >> gvs[] >>
    drule cfgAnalysisPropsTheory.cfg_analyze_preorder_entry_first >>
    strip_tac >>
    metis_tac[rich_listTheory.HEAD_MEM]) >>
  drule copy_prop_is_fixpoint >> strip_tac >>
  mp_tac (Q.SPECL [`fn`, `lbl`] copy_prop_inter_fwd_gen) >>
  impl_tac >- simp[] >>
  disch_then (fn th =>
    simp_tac std_ss [copy_prop_analyze_def, LET_THM, th]) >>
  simp[copy_prop_joined_def, LET_THM] >>
  gvs[copy_prop_join_FEMPTY, copy_sound_opt_fempty]
QED

(* Phase 1 function-level: use df_analysis_pass_correct_sound framework *)
Theorem assign_subst_function_eq[local]:
  !fuel ctx fn s.
    let result = copy_prop_analyze fn in
    let fn_subst = analysis_function_transform NONE result
                     (\v inst. [assign_subst_inst v inst]) fn in
    wf_function fn /\
    fn_inst_wf fn /\
    ALL_DISTINCT (fn_labels fn) /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode)
    ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_function fuel ctx fn s)
      (run_function fuel ctx fn_subst s)
Proof
  rpt GEN_TAC >> simp_tac std_ss [LET_THM] >> rpt strip_tac
  (* Expand copy_prop_analyze in goal BEFORE adding framework *)
  \\ simp_tac std_ss [copy_prop_analyze_def, LET_THM]
  \\ mp_tac (ISPECL [
       ``state_equiv {} : venom_state -> venom_state -> bool``,
       ``execution_equiv {} : venom_state -> venom_state -> bool``,
       ``NONE : copy_lattice option``,
       ``copy_prop_join``,
       ``copy_prop_transfer``,
       ``copy_prop_edge_transfer : (string -> bool) -> string -> string ->
            copy_lattice option -> copy_lattice option``,
       ``phi_used_vars fn``,
       ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : copy_lattice)))
            (fn_entry_label fn)``,
       ``fn : ir_function``,
       ``copy_sound_opt``,
       ``\v inst. [assign_subst_inst v inst]``]
     (SIMP_RULE std_ss [LET_THM]
       analysisSimPropsTheory.df_analysis_pass_correct_sound))
  \\ impl_tac
  >- (rpt conj_tac
      >- simp[state_equiv_execution_equiv_valid_state_rel]
      >- metis_tac[state_equiv_trans]
      >- metis_tac[execution_equiv_trans]
      >- metis_tac[copy_prop_is_fixpoint]
      >- metis_tac[copy_prop_transfer_sound]
      >- (rpt strip_tac >>
          metis_tac[REWRITE_RULE [SIMP_RULE std_ss [LET_THM]
            copy_prop_analyze_def] copy_sound_opt_at_entry])
      >- (rpt strip_tac >> rpt conj_tac
          >- metis_tac[analysisSimPropsTheory.successor_in_cfg_dfs_pre]
          >- (mp_tac (SIMP_RULE std_ss [LET_THM] successor_entry_sound) >>
              disch_then irule >> rpt conj_tac >>
              TRY (first_assum ACCEPT_TAC) >>
              metis_tac[copy_prop_is_fixpoint]))
      >- metis_tac[assign_subst_inst_simulates]
      >- first_assum ACCEPT_TAC
      >- metis_tac[copy_sound_opt_state_equiv]
      >- (rpt strip_tac >>
          fs[state_equiv_def, execution_equiv_def, lookup_var_def]))
  \\ disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac)
  \\ simp[]
QED

(* ===== Combined: function-level correctness ===== *)

(* Monotonicity: lift_result for stronger relation implies lift_result for weaker *)
Theorem lift_result_weaken[local]:
  !R1_ok R2_ok R1_term R2_term r1 r2.
    (!s1 s2. R1_ok s1 s2 ==> R2_ok s1 s2) /\
    (!s1 s2. R1_term s1 s2 ==> R2_term s1 s2) /\
    lift_result R1_ok R1_term r1 r2 ==>
    lift_result R2_ok R2_term r1 r2
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> fs[lift_result_def]
QED

Theorem assign_elim_function_correct_proof:
  !fuel ctx fn s.
    let elim = assign_elim_eliminated_vars fn in
    let result = copy_prop_analyze fn in
    let fn_subst = analysis_function_transform NONE result
                     (\v inst. [assign_subst_inst v inst]) fn in
    wf_function fn /\
    fn_inst_wf fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (!bb inst x.
       MEM bb fn_subst.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN elim)
    ==>
    (?e. run_function fuel ctx fn s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
      (run_function fuel ctx fn s)
      (run_function fuel ctx (assign_elim_function fn) s)
Proof
  rpt GEN_TAC >> simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  (* Phase 1: fn → fn_subst gives state_equiv {} (or fn errors) *)
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (ISPECL [``fuel:num``, ``ctx:venom_context``,
             ``fn:ir_function``, ``s:venom_state``]
     assign_subst_function_eq)) >>
  impl_tac >- (fs[wf_function_def]) >>
  strip_tac >- (
    (* Phase 1 gave Error — just forward it *)
    simp[]
  ) >>
  (* Have: lift_result state_equiv {} fn fn_subst *)
  (* Need: Error fn ∨ lift_result state_equiv elim fn (assign_elim_function fn) *)
  (* Apply Phase 2 *)
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (ISPECL [``fuel:num``, ``ctx:venom_context``,
             ``fn:ir_function``, ``s:venom_state``]
     assign_nop_dead_writes_correct)) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  (* Now: Phase 2 conclusion is disjunction about fn_subst → fn_elim *)
  strip_tac >- (
    (* Phase 2 gave Error on fn_subst *)
    Cases_on `run_function fuel ctx fn s` >>
    fs[lift_result_def]
  ) >>
  (* Have: Phase 1 lift_result (∅), Phase 2 lift_result (elim) *)
  (* Compose Phases 1+2+3 *)
  DISJ2_TAC >>
  (* Phase 3: clear_nops gives result_equiv {} *)
  qabbrev_tac `fn_elim = analysis_function_transform NONE
     (copy_prop_analyze fn)
     (\v inst. [assign_elim_inst (phi_used_vars fn) v inst]) fn` >>
  `assign_elim_function fn = clear_nops_function fn_elim` by
    simp[assign_elim_function_def, Abbr `fn_elim`] >>
  `result_equiv {}
     (run_function fuel ctx fn_elim s)
     (run_function fuel ctx (assign_elim_function fn) s)` by (
    pop_assum (fn th => REWRITE_TAC [th]) >>
    irule clear_nops_function_correct >> simp[]) >>
  fs[result_equiv_is_lift_result] >>
  (* Weaken Phase 1 from state_equiv {} to state_equiv elim *)
  `lift_result (state_equiv (assign_elim_eliminated_vars fn))
     (execution_equiv (assign_elim_eliminated_vars fn) (execution_equiv (assign_elim_eliminated_vars fn))
     (run_function fuel ctx fn s)
     (run_function fuel ctx
        (analysis_function_transform NONE (copy_prop_analyze fn)
           (\v inst. [assign_subst_inst v inst]) fn) s)` by (
    irule lift_result_weaken >>
    qexistsl_tac [`state_equiv {}`, `execution_equiv {}`] >>
    simp[] >> rpt strip_tac >>
    metis_tac[state_equiv_subset, execution_equiv_subset, EMPTY_SUBSET]
  ) >>
  (* Compose Phases 1+2 via lift_result_trans *)
  `lift_result (state_equiv (assign_elim_eliminated_vars fn))
     (execution_equiv (assign_elim_eliminated_vars fn) (execution_equiv (assign_elim_eliminated_vars fn))
     (run_function fuel ctx fn s)
     (run_function fuel ctx fn_elim s)` by (
    irule lift_result_trans >>
    conj_tac >- (rpt strip_tac >> metis_tac[state_equiv_trans]) >>
    conj_tac >- (rpt strip_tac >> metis_tac[execution_equiv_trans]) >>
    qexists_tac `run_function fuel ctx
      (analysis_function_transform NONE (copy_prop_analyze fn)
         (\v inst. [assign_subst_inst v inst]) fn) s` >>
    simp[]) >>
  (* Compose with Phase 3 (clear_nops) *)
  irule lift_result_trans >>
  conj_tac >- (rpt strip_tac >> metis_tac[state_equiv_trans]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[execution_equiv_trans]) >>
  qexists_tac `run_function fuel ctx fn_elim s` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule lift_result_weaken >>
  qexistsl_tac [`state_equiv {}`, `execution_equiv {}`] >>
  simp[] >> rpt strip_tac >>
  metis_tac[state_equiv_subset, execution_equiv_subset, EMPTY_SUBSET]
QED
