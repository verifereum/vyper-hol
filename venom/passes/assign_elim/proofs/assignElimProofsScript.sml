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
  assignElimDefs assignElimSound assignElimConvergence
  passSharedDefs passSharedProps
  passSimulationDefs passSimulationProps
  venomState venomWf venomInst venomInstProps
  analysisSimDefs analysisSimProps analysisSimProofsBase
  stateEquiv stateEquivProps
  execEquivParamDefs execEquivParamProps
  venomExecSemantics venomExecProofs
  dfAnalyzeDefs dfAnalyzeProofs
  cfgHelpers worklistDefs
  cfgAnalysisProps
  finite_map list pred_set arithmetic

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
val inter_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_at_inter_transfer_proof));

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

Theorem copy_sound_opt_inst_idx_update[local]:
  !v s k1 k2.
    copy_sound_opt v (s with vs_inst_idx := k1) <=>
    copy_sound_opt v (s with vs_inst_idx := k2)
Proof
  simp[GSYM copy_sound_opt_inst_idx]
QED

Triviality copy_prop_transfer_sound_wf[local]:
  !pv. transfer_sound_wf copy_sound_opt copy_prop_transfer pv
Proof
  rw[transfer_sound_wf_def] >>
  mp_tac (Q.SPEC `pv` copy_prop_transfer_sound) >>
  simp[transfer_sound_def] >>
  disch_then (qspecl_then [`fuel`, `run_ctx`, `v`, `inst`, `s`, `s'`] mp_tac) >>
  simp[]
QED

Triviality copy_prop_analyze_eq[local]:
  !fn.
    df_analyze Forward NONE copy_prop_join copy_prop_transfer
      copy_prop_edge_transfer (phi_used_vars fn)
      (OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : copy_lattice)))
        (fn_entry_label fn)) fn =
    copy_prop_analyze fn
Proof
  simp[copy_prop_analyze_def, LET_THM]
QED

(* When copy_prop_transfer receives NONE input for a PHI instruction,
   the result is a FEMPTY-derived map with no entries. *)
Triviality copy_prop_transfer_phi_none[local]:
  !phi_vars inst x op.
    inst.inst_opcode = PHI /\
    copy_prop_transfer phi_vars inst NONE = SOME copies /\
    FLOOKUP copies x = SOME op ==> F
Proof
  rpt strip_tac >>
  `~is_forwardable_assign phi_vars inst` by
    fs[is_forwardable_assign_def] >>
  gvs[copy_prop_transfer_def, LET_THM, DRESTRICT_FEMPTY, FLOOKUP_EMPTY]
QED

(* After copy_prop_transfer processes a PHI instruction, surviving entries
   don't reference the PHI's output variables. *)
Theorem copy_prop_transfer_phi_restriction[local]:
  !phi_vars inst copies copies'.
    inst.inst_opcode = PHI /\
    copy_prop_transfer phi_vars inst (SOME copies) = SOME copies' ==>
    !x op. FLOOKUP copies' x = SOME op ==>
      FLOOKUP copies x = SOME op /\
      x NOTIN set inst.inst_outputs /\
      (!y. op = Var y ==> y NOTIN set inst.inst_outputs)
Proof
  rpt strip_tac >>
  `~is_forwardable_assign phi_vars inst` by
    fs[is_forwardable_assign_def] >>
  rpt strip_tac >> gvs[copy_prop_transfer_def, is_forwardable_assign_def, inst_defs_def] >> pop_assum (assume_tac o GSYM) >> gvs[FLOOKUP_DRESTRICT, COMPL_DEF] >> rw[] >> fs[]
QED

(* copy_sound_opt is preserved when state changes only touch variables
   not referenced by the copy map entries. *)
Theorem copy_sound_opt_vars_agree[local]:
  !copies s1 s2.
    copy_sound_opt (SOME copies) s1 /\
    (!x. FLOOKUP copies x <> NONE ==> lookup_var x s2 = lookup_var x s1) /\
    (!x y. FLOOKUP copies x = SOME (Var y) ==> lookup_var y s2 = lookup_var y s1) /\
    s1.vs_labels = s2.vs_labels ==>
    copy_sound_opt (SOME copies) s2
Proof
  rpt strip_tac >> fs[copy_sound_opt_def, copy_sound_def] >>
  rpt strip_tac >> res_tac >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
  Cases_on `op` >> fs[eval_operand_def, lookup_var_def]
QED

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
  >- ((* Existential: measure + invariant witnesses *)
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
        Cases_on `fn_entry_label fn` >> simp[] >> metis_tac[]))
  >>
  (* wl_deps_complete *)
  match_mp_tac (SIMP_RULE std_ss [LET_THM]
    dfAnalyzeProofsTheory.df_process_deps_complete_proof |>
    SPEC ``Forward : direction`` |>
    SIMP_RULE std_ss [dfAnalyzeDefsTheory.direction_case_def]) >>
  rw[copy_prop_join_absorption] >>
  metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond]
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
    wf_function fn /\
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
  rpt strip_tac >> imp_res_tac intra_fwd
QED

Triviality copy_prop_boundary_fixpoint[local]:
  !fn lbl bb.
    wf_function fn /\
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
  rpt strip_tac >> imp_res_tac boundary_fixpoint_fwd
QED

Triviality cfg_dfs_pre_lookup_block[local]:
  wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
  ?bb. lookup_block lbl fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >>
  drule cfgAnalysisPropsTheory.cfg_analyze_reachable_sets >> strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) lbl` by (fs[EXTENSION] >> metis_tac[]) >>
  drule cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels >> strip_tac >>
  fs[fn_labels_def, MEM_MAP] >>
  metis_tac[venomExecPropsTheory.MEM_lookup_block, wf_function_def, fn_labels_def]
QED

(* copy_prop_inter_fwd_gen: df_at lbl 0 = copy_prop_joined at fixpoint.
   Uses inter_fwd; derives lookup_block from wf_function + MEM cfg_dfs_pre. *)
Triviality copy_prop_inter_fwd_gen[local]:
  !fn lbl.
    wf_function fn /\
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
  rpt strip_tac
  \\ drule_all cfg_dfs_pre_lookup_block \\ strip_tac
  \\ drule_all inter_fwd \\ strip_tac
  \\ simp[copy_prop_joined_def, copy_prop_edge_transfer_def, LET_THM,
       dfAnalyzeDefsTheory.df_joined_val_def]
  \\ Cases_on `fn_entry_label fn` \\ gvs[]
QED

Triviality copy_prop_df_at_not_none[local]:
  !fn lbl bb.
    wf_function fn /\
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
        bb.bb_label s.vs_inst_idx) s /\
    s.vs_inst_idx <= PRE (LENGTH bb.bb_instructions) /\
    exec_block fuel ctx bb s = OK v
    ==>
    copy_sound_opt
      (df_at NONE
        (df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
        bb.bb_label (LENGTH bb.bb_instructions)) v
Proof
  rpt strip_tac >>
  `bb_well_formed bb` by (fs[wf_function_def] >> metis_tac[]) >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
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
  (* Use arbitrary-start transfer_sound_exit_from_wf_len for the post-PHI
     exec_block entry point. *)
  `copy_sound_opt
     (df_at NONE
       (df_analyze Forward NONE copy_prop_join copy_prop_transfer
          copy_prop_edge_transfer (phi_used_vars fn)
          (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
       bb.bb_label s.vs_inst_idx) (s with vs_inst_idx := 0)` by
    fs[GSYM copy_sound_opt_inst_idx] >>
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
    analysisSimProofsTheory.transfer_sound_exit_from_wf_len) >>
  impl_tac >- (
    gvs[state_equiv_execution_equiv_valid_state_rel,
        copy_prop_transfer_sound_wf] >>
    rpt strip_tac >>
    metis_tac[copy_sound_opt_state_equiv, intra_fwd]) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`, `v`] mp_tac) >>
  simp[]
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
    s.vs_inst_idx <= PRE (LENGTH bb.bb_instructions) /\
    copy_sound_opt (df_at NONE result s.vs_current_bb s.vs_inst_idx) s /\
    exec_block fuel ctx bb s = OK v
    ==>
    copy_sound_opt (df_at NONE result v.vs_current_bb 0) v
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `bb_well_formed bb` by (fs[wf_function_def] >> metis_tac[]) >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `EVERY inst_wf bb.bb_instructions` by (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by metis_tac[] >>
  `s.vs_inst_idx <= LENGTH bb.bb_instructions` by decide_tac >>
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
    metis_tac[venomExecPropsTheory.exec_block_current_bb_in_succs] >>
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

Triviality successor_entry_sound_result[local]:
  !fn bb fuel ctx st v result.
    result = copy_prop_analyze fn /\
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    wf_function fn /\
    fn_inst_wf fn /\ ALL_DISTINCT (fn_labels fn) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    bb.bb_label = st.vs_current_bb /\
    MEM st.vs_current_bb (cfg_analyze fn).cfg_dfs_pre /\
    st.vs_inst_idx <= PRE (LENGTH bb.bb_instructions) /\
    copy_sound_opt (df_at NONE result st.vs_current_bb st.vs_inst_idx) st /\
    exec_block fuel ctx bb st = OK v
    ==>
    copy_sound_opt (df_at NONE result v.vs_current_bb 0) v
Proof
  rpt strip_tac >> gvs[] >>
  mp_tac (SIMP_RULE std_ss [LET_THM] successor_entry_sound) >>
  disch_then (qspecl_then [`fn`, `bb`, `fuel`, `ctx`, `st`, `v`] mp_tac) >>
  impl_tac >- gvs[copy_prop_analyze_def, LET_THM] >>
  simp[copy_prop_analyze_def, LET_THM]
QED

Triviality copy_prop_join_FEMPTY[local]:
  !x. copy_prop_join (SOME FEMPTY) x = SOME FEMPTY
Proof
  Cases >> simp[copy_prop_join_def, copy_prop_join_raw_def, DRESTRICT_FEMPTY]
QED

Triviality copy_sound_opt_at_entry[local]:
  wf_function fn /\
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

(* Index in PHI prefix has opcode PHI *)
Triviality phi_prefix_length_el_phi[local]:
  !l i. i < phi_prefix_length l ==> (EL i l).inst_opcode = PHI
Proof
  Induct_on `l` >> simp[phi_prefix_length_def] >> rw[] >>
  Cases_on `i` >> simp[phi_prefix_length_def]
QED

Triviality phi_prefix_length_lt_wf[local]:
  !bb. bb_well_formed bb ==>
       phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions
Proof
  rpt strip_tac >> fs[bb_well_formed_def] >>
  `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le] >>
  CCONTR_TAC >>
  `phi_prefix_length bb.bb_instructions = LENGTH bb.bb_instructions` by
    decide_tac >>
  `PRE (LENGTH bb.bb_instructions) < phi_prefix_length bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  `(EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[phi_prefix_length_el_phi] >>
  `EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions = LAST bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[LAST_EL]) >>
  gvs[is_terminator_def]
QED

(* Direct indexed variant of eval_phis_flookup_not_phi_output.
   Uses the indexed condition that df_at_phi_prefix_no_phi_output_at_end
   already provides directly, avoiding the need for bb_well_formed bridge. *)
Theorem eval_phis_flookup_idx[local]:
  !s insts x.
    (!i. i < phi_prefix_length insts ==> ~MEM x (EL i insts).inst_outputs) ==>
    !s'. eval_phis s insts = OK s' ==> FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x
Proof
  Induct_on `insts` >> simp[eval_phis_def] >>
  rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[eval_phis_def, AllCaseEqs()] >>
  (* Derive IH hypothesis for recursive case *)
  `!i. i < phi_prefix_length insts ==> ~MEM x (EL i insts).inst_outputs` by (
    rpt strip_tac >>
    first_x_assum (qspec_then `SUC i` mp_tac) >>
    simp[phi_prefix_length_def]
  ) >>
  (* IH gives FLOOKUP preserved through recursive eval_phis *)
  `FLOOKUP s''.vs_vars x = FLOOKUP s.vs_vars x` by (
    first_x_assum drule >> simp[]
  ) >>
  (* out is not x (not written by this PHI) *)
  `~MEM x h.inst_outputs` by (
    last_x_assum (fn th =>
      mp_tac (Q.SPEC `0` th) >> simp[phi_prefix_length_def])
  ) >>
  `MEM out h.inst_outputs` by (
    drule eval_one_phi_output_mem >> simp[]
  ) >>
  `out <> x` by (CCONTR_TAC >> fs[]) >>
  gvs[update_var_def, FLOOKUP_UPDATE]
QED

(* Corollary of eval_phis_flookup_idx for Var-valued copy map entries.
   Factored out to avoid assumption-selection issues in the complex proof
   context of copy_sound_opt_phi_prefix_eval_phis. *)
Triviality eval_phis_flookup_var_val[local]:
  !insts s s_phi copies x y.
    eval_phis s insts = OK s_phi /\
    FLOOKUP copies x = SOME (Var y) /\
    (!i. i < phi_prefix_length insts ==>
         !x' op. FLOOKUP copies x' = SOME op ==>
                 ~MEM x' (EL i insts).inst_outputs /\
                 (!y'. op = Var y' ==> ~MEM y' (EL i insts).inst_outputs))
    ==> FLOOKUP s_phi.vs_vars y = FLOOKUP s.vs_vars y
Proof
  rpt strip_tac >>
  `!i. i < phi_prefix_length insts ==> ~MEM y (EL i insts).inst_outputs` by (
    rpt strip_tac >>
    qpat_x_assum `!i. i < phi_prefix_length _ ==> !x' op. _`
      (qspec_then `i` mp_tac) >>
    simp[] >>
    qexistsl [`x`, `Var y`] >>
    simp[]
  ) >>
  mp_tac (Q.SPECL [`s`, `insts`, `y`] eval_phis_flookup_idx) >>
  simp[]
QED

(* PHI prefix analysis transfer preserves copy_sound_opt on the same state.
   Under final semantics PHIs are not sequential steps; the transfer only
   kills PHI outputs and entries that reference them. *)
Triviality copy_prop_transfer_phi_sound[local]:
  !pv inst v st.
    inst.inst_opcode = PHI /\ copy_sound_opt v st ==>
    copy_sound_opt (copy_prop_transfer pv inst v) st
Proof
  rpt strip_tac >> Cases_on `v`
  >- (
    Cases_on `copy_prop_transfer pv inst NONE` >>
    simp[copy_sound_opt_def, copy_sound_def] >>
    rpt strip_tac >> metis_tac[copy_prop_transfer_phi_none])
  >- (
    Cases_on `copy_prop_transfer pv inst (SOME x)` >>
    simp[copy_sound_opt_def, copy_sound_def] >>
    rpt strip_tac >>
    drule_all copy_prop_transfer_phi_restriction >> strip_tac >>
    fs[copy_sound_opt_def, copy_sound_def] >> res_tac >> simp[])
QED

(* copy_sound_opt propagates through one PHI instruction in the prefix.
   Since step_inst_base for PHI is a no-op (OK s), and copy_prop_transfer
   for PHI only kills entries (shrinks the map), soundness is preserved. *)
Theorem copy_sound_opt_phi_prefix_step[local]:
  !fn bb st k.
    wf_function fn /\ fn_inst_wf fn /\
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM bb fn.fn_blocks /\
    k < phi_prefix_length bb.bb_instructions /\
    copy_sound_opt
      (df_at NONE
         (df_analyze Forward NONE copy_prop_join copy_prop_transfer
            copy_prop_edge_transfer (phi_used_vars fn)
            (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
         bb.bb_label k) st
    ==>
    copy_sound_opt
      (df_at NONE
         (df_analyze Forward NONE copy_prop_join copy_prop_transfer
            copy_prop_edge_transfer (phi_used_vars fn)
            (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
         bb.bb_label (SUC k)) st
Proof
  rpt strip_tac >>
  `(EL k bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[phi_prefix_length_el_phi] >>
  `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le] >>
  `SUC k <= LENGTH bb.bb_instructions` by decide_tac >>
  (* Abbreviate the huge df_at term to avoid metis/simp blowup *)
  qmatch_asmsub_abbrev_tac `df_at NONE result lbl k` >>
  `df_at NONE result lbl (SUC k) =
      copy_prop_transfer (phi_used_vars fn) (EL k bb.bb_instructions)
        (df_at NONE result lbl k)` by
    metis_tac[copy_prop_intra_fwd] >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
  irule copy_prop_transfer_phi_sound >> simp[]
QED

(* Soundness at df_at lbl phi_prefix_length for state s, stepping through
   all PHI prefix instructions. *)
Theorem copy_sound_opt_phi_prefix_on_s[local]:
  !fn bb s k.
    wf_function fn /\ fn_inst_wf fn /\
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM bb fn.fn_blocks /\
    k <= phi_prefix_length bb.bb_instructions /\
    copy_sound_opt
      (df_at NONE
         (df_analyze Forward NONE copy_prop_join copy_prop_transfer
            copy_prop_edge_transfer (phi_used_vars fn)
            (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
         bb.bb_label 0) s
    ==>
    copy_sound_opt
      (df_at NONE
         (df_analyze Forward NONE copy_prop_join copy_prop_transfer
            copy_prop_edge_transfer (phi_used_vars fn)
            (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
         bb.bb_label k) s
Proof
  Induct_on `k` >- simp[] >>
  rpt strip_tac >>
  (* IH: sound at index k *)
  `copy_sound_opt
     (df_at NONE
        (df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
        bb.bb_label k) s` by (
    first_x_assum irule >> simp[] >> metis_tac[]
  ) >>
  (* Step: sound at index SUC k from sound at index k *)
  mp_tac copy_sound_opt_phi_prefix_step >> simp[]
QED

(* After one copy_prop_transfer step for a PHI instruction,
   surviving entries' keys are not in the instruction's outputs. *)
Triviality copy_prop_transfer_phi_no_output_key[local]:
  !phi_vars inst copies copies'.
    inst.inst_opcode = PHI /\
    copy_prop_transfer phi_vars inst (SOME copies) = SOME copies' /\
    FLOOKUP copies' x = SOME op
    ==>
    ~MEM x inst.inst_outputs
Proof
  rpt strip_tac >>
  `~is_forwardable_assign phi_vars inst` by
    fs[is_forwardable_assign_def] >>
  imp_res_tac copy_prop_transfer_phi_restriction >>
  first_x_assum (qspecl_then [`x`, `op`] mp_tac) >> simp[]
QED

(* After one copy_prop_transfer step for a PHI instruction,
   surviving entries' Var-values are not in the instruction's outputs. *)
Triviality copy_prop_transfer_phi_no_output_val[local]:
  !phi_vars inst copies copies'.
    inst.inst_opcode = PHI /\
    copy_prop_transfer phi_vars inst (SOME copies) = SOME copies' /\
    FLOOKUP copies' x = SOME (Var y)
    ==>
    ~MEM y inst.inst_outputs
Proof
  rpt strip_tac >>
  `~is_forwardable_assign phi_vars inst` by
    fs[is_forwardable_assign_def] >>
  metis_tac[copy_prop_transfer_phi_restriction]
QED

(* After stepping through the PHI prefix in df_at, surviving entries
   are not outputs of any PHI instruction in the list.
   Proved by induction on k: if FLOOKUP(df_at lbl k) x exists,
   then x is not in outputs of any PHI at index < k. *)
Theorem df_at_phi_prefix_no_phi_output[local]:
  !fn bb k x op.
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
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    k <= phi_prefix_length bb.bb_instructions /\
    df_at NONE
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
      bb.bb_label k = SOME copies /\
    FLOOKUP copies x = SOME op
    ==>
    !i. i < k ==>
        ~MEM x (EL i bb.bb_instructions).inst_outputs /\
        (!y. op = Var y ==>
             ~MEM y (EL i bb.bb_instructions).inst_outputs)
Proof
  qid_spec_tac `copies` >>
  Induct_on `k` >- (rpt gen_tac >> strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `k < phi_prefix_length bb.bb_instructions` by decide_tac >>
  `(EL k bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[phi_prefix_length_el_phi] >>
  `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le] >>
  `SUC k <= LENGTH bb.bb_instructions` by decide_tac >>
  qabbrev_tac `df_an = df_analyze Forward NONE copy_prop_join
    copy_prop_transfer copy_prop_edge_transfer (phi_used_vars fn)
    (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn` >>
  `df_at NONE df_an bb.bb_label (SUC k) =
    copy_prop_transfer (phi_used_vars fn) (EL k bb.bb_instructions)
      (df_at NONE df_an bb.bb_label k)` by
    metis_tac[copy_prop_intra_fwd] >>
  Cases_on `df_at NONE df_an bb.bb_label k`
  >- metis_tac[copy_prop_transfer_phi_none] >>
  `~is_forwardable_assign (phi_used_vars fn) (EL k bb.bb_instructions)` by
    fs[is_forwardable_assign_def] >>
  (* Establish the copy_prop_transfer equation to enable drule_all *)
  `copy_prop_transfer (phi_used_vars fn) (EL k bb.bb_instructions)
      (SOME x') = SOME copies` by metis_tac[] >>
  gen_tac >> strip_tac >>
  (* Now have i < SUC k as assumption *)
  Cases_on `i = k`
  >- ((* i = k *)
      conj_tac
      >- metis_tac[copy_prop_transfer_phi_no_output_key]
      >- (rpt strip_tac >>
          metis_tac[copy_prop_transfer_phi_no_output_val]))
  >- ((* i < k: derive restriction then apply IH with copies := x' *)
      `i < k` by decide_tac >>
      `k <= phi_prefix_length bb.bb_instructions` by decide_tac >>
      `FLOOKUP x' x = SOME op` by
        (drule_all copy_prop_transfer_phi_restriction >> simp[]) >>
      (* IH ∀-quantifies copies,fn,bb,x,op — specialize copies to x' *)
      (* Use drule to match first antecedent, then simp resolves rest *)
      first_x_assum (qspecl_then [`x'`] mp_tac) >>
      simp[Abbr `df_an`] >>
      rw[] >> metis_tac[])
QED

(* Helper: specializing df_at_phi_prefix_no_phi_output to the phi_prefix_length.
   Avoids ISPECL with huge df_at terms in consumer proofs. *)
Theorem df_at_phi_prefix_no_phi_output_at_end[local]:
  !fn bb copies x op.
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
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    df_at NONE
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn)
      bb.bb_label (phi_prefix_length bb.bb_instructions) = SOME copies /\
    FLOOKUP copies x = SOME op
    ==>
    !i. i < phi_prefix_length bb.bb_instructions ==>
        ~MEM x (EL i bb.bb_instructions).inst_outputs /\
        (!y. op = Var y ==> ~MEM y (EL i bb.bb_instructions).inst_outputs)
Proof
  rpt strip_tac >>
  `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le] >>
  `phi_prefix_length bb.bb_instructions <= phi_prefix_length bb.bb_instructions` by
    decide_tac >>
  drule_all df_at_phi_prefix_no_phi_output >>
  simp[]
QED

(* Key eval_phis preservation: copy_sound_opt at df_at lbl phi_prefix_length
   is preserved when transitioning from original state s to s_phi.
   Part (a): copy_sound_opt propagates through PHI prefix on state s
             (PHI step_inst is a no-op, transfer only kills entries).
   Part (b): copy_sound_opt at phi_prefix_length transfers from s to s_phi
             (surviving entries don't reference PHI outputs, eval_phis preserves
             FLOOKUP for non-PHI-output variables). *)
Theorem copy_sound_opt_phi_prefix_eval_phis[local]:
  !fn bb s s_phi.
    wf_function fn /\ fn_inst_wf fn /\
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (df_analyze Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn)) fn) /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM bb fn.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    copy_sound_opt (df_at NONE (copy_prop_analyze fn) bb.bb_label 0) s
    ==>
    copy_sound_opt (df_at NONE (copy_prop_analyze fn) bb.bb_label
      (phi_prefix_length bb.bb_instructions)) (s_phi with vs_inst_idx := 0)
Proof
  rpt strip_tac >>
  RULE_ASSUM_TAC (BETA_RULE o REWRITE_RULE[copy_prop_analyze_def, LET_THM]) >>
  simp_tac std_ss [copy_prop_analyze_def, LET_THM] >>
  BETA_TAC >>
  (* Part (a): copy_sound_opt propagates through PHI prefix on state s *)
  `copy_sound_opt
     (df_at NONE (df_analyze Forward NONE copy_prop_join copy_prop_transfer
        copy_prop_edge_transfer (phi_used_vars fn)
        (OPTION_MAP (\lbl. (lbl,SOME FEMPTY)) (fn_entry_label fn)) fn)
        bb.bb_label (phi_prefix_length bb.bb_instructions)) s` by (
    mp_tac copy_sound_opt_phi_prefix_on_s >> simp[] >> decide_tac
  ) >>
  (* Part (b): Transport from s to s_phi.
     Key insight: PHI outputs are not in surviving copy map entries,
     and eval_phis preserves FLOOKUP for non-PHI-output variables. *)
  Cases_on `df_at NONE (df_analyze Forward NONE copy_prop_join copy_prop_transfer
      copy_prop_edge_transfer (phi_used_vars fn)
      (OPTION_MAP (\lbl. (lbl,SOME FEMPTY)) (fn_entry_label fn)) fn)
      bb.bb_label (phi_prefix_length bb.bb_instructions)` >- (
    simp[copy_sound_opt_def]
  ) >>
  rename1 `SOME copies` >>
  (* Derive the indexed FLOOKUP-preservation condition.
     Uses eval_phis_flookup_idx (direct induction on insts) to avoid
     needing bb_well_formed bridge from indexed to MEM-level condition. *)
  `!i. i < phi_prefix_length bb.bb_instructions ==>
       !x op. FLOOKUP copies x = SOME op ==>
              ~MEM x (EL i bb.bb_instructions).inst_outputs /\
              (!y. op = Var y ==> ~MEM y (EL i bb.bb_instructions).inst_outputs)` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`fn`,`bb`,`copies`,`x`,`op`]
      df_at_phi_prefix_no_phi_output_at_end) >>
    simp[] >> metis_tac[]
  ) >>
  (* Key FLOOKUP preservation: for any variable in copies, FLOOKUP is preserved.
     This covers both conditions needed by copy_sound_opt_vars_agree:
     (1) FLOOKUP copies x ≠ NONE ⟹ FLOOKUP s_phi.vs_vars x = FLOOKUP s.vs_vars x
     (2) FLOOKUP copies x = SOME (Var y) ⟹ FLOOKUP s_phi.vs_vars y = FLOOKUP s.vs_vars y *)
  `!z. FLOOKUP copies z <> NONE ==>
       FLOOKUP (s_phi with vs_inst_idx := 0).vs_vars z =
       FLOOKUP s.vs_vars z` by (
    gen_tac >> strip_tac >>
    Cases_on `FLOOKUP copies z` >> fs[] >>
    rename1 `SOME op` >>
    `lookup_var z (s_phi with vs_inst_idx := 0) = lookup_var z s_phi`
      by simp[lookup_var_def] >>
    mp_tac (Q.SPECL [`s`, `bb.bb_instructions`, `z`] eval_phis_flookup_idx) >>
    simp[] >> strip_tac >>
    (* Prove indexed antecedent for z from indexed condition *)
    first_x_assum match_mp_tac >>
    metis_tac[]
  ) >>
  (* Derive the two specific conditions from copy_sound_opt_vars_agree *)
  `!x. FLOOKUP copies x <> NONE ==>
       lookup_var x (s_phi with vs_inst_idx := 0) = lookup_var x s` by (
    gen_tac >> strip_tac >>
    qpat_x_assum `!z. FLOOKUP copies z <> NONE ==> _`
      (qspec_then `x` mp_tac) >> simp[] >>
    fs[lookup_var_def]
  ) >>
  `!x y. FLOOKUP copies x = SOME (Var y) ==>
       lookup_var y (s_phi with vs_inst_idx := 0) = lookup_var y s` by (
    rpt strip_tac >>
    simp[lookup_var_def] >>
    mp_tac (Q.SPECL [`bb.bb_instructions`, `s`, `s_phi`, `copies`, `x`, `y`]
      eval_phis_flookup_var_val) >>
    simp[] >> strip_tac >> metis_tac[]
  ) >>
  match_mp_tac (Q.SPECL [`copies`, `s`, `s_phi with vs_inst_idx := 0`] copy_sound_opt_vars_agree) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  simp[] >>
  metis_tac[venomExecPropsTheory.eval_phis_preserves_labels]
QED

Theorem copy_sound_opt_phi_prefix_eval_phis_result[local]:
  !fn bb s s_phi result.
    result = copy_prop_analyze fn /\
    wf_function fn /\ fn_inst_wf fn /\
    is_fixpoint
      (df_process_block Forward NONE copy_prop_join copy_prop_transfer
         copy_prop_edge_transfer (phi_used_vars fn)
         (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre result /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    MEM bb fn.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    copy_sound_opt (df_at NONE result bb.bb_label 0) s
    ==>
    copy_sound_opt (df_at NONE result bb.bb_label
      (phi_prefix_length bb.bb_instructions)) (s_phi with vs_inst_idx := 0)
Proof
  rpt strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`fn`, `bb`, `s`, `s_phi`]
    copy_sound_opt_phi_prefix_eval_phis) >>
  impl_tac >- gvs[copy_prop_analyze_def, LET_THM] >>
  simp[copy_prop_analyze_def, LET_THM]
QED

Theorem run_block_successor_in_cfg_dfs_pre[local]:
  !fn bb fuel ctx s v.
    fn_inst_wf fn /\ ALL_DISTINCT (fn_labels fn) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    s.vs_current_bb = bb.bb_label /\
    run_block fuel ctx bb s = OK v
    ==>
    MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `bb.bb_instructions <> []` by
    metis_tac[venomExecPropsTheory.run_block_ok_nonempty] >>
  `MEM v.vs_current_bb (bb_succs bb)` by
    metis_tac[venomExecPropsTheory.run_block_current_bb_in_succs] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfgAnalysisPropsTheory.bb_succs_in_cfg_succs] >>
  imp_res_tac analysisSimPropsTheory.cfg_dfs_pre_succs_closed >>
  gvs[EVERY_MEM]
QED

(* After run_block OK with entry soundness at fixpoint,
   the successor has entry soundness too.
   Updated for parallel PHI semantics: run_block = eval_phis + exec_block *)
Theorem run_block_successor_entry_sound[local]:
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
  qabbrev_tac `pv = phi_used_vars fn` >>
  qabbrev_tac `ev = OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : copy_lattice))) (fn_entry_label fn)` >>
  qabbrev_tac `result = df_analyze Forward NONE copy_prop_join
    copy_prop_transfer copy_prop_edge_transfer pv ev fn` >>
  qpat_x_assum `bb.bb_label = s.vs_current_bb`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> assume_tac th) >>
  qspecl_then [`s`,`bb.bb_instructions`] mp_tac
    venomExecSemanticsTheory.eval_phis_ok_or_error_defs >>
  rpt strip_tac >>
  gvs[Once venomExecSemanticsTheory.run_block_def, AllCaseEqs()] >>
  (* eval_phis preserves current_bb *)
  `s'.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  (* PHI prefix length bound *)
  `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le] >>
  (* eval_phis preserves copy_sound_opt: transfer kills PHI outputs,
     and surviving copy-map entries do not reference PHI outputs. *)
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    metis_tac[venomExecPropsTheory.MEM_lookup_block, fn_labels_def] >>
  `result = copy_prop_analyze fn` by
    simp[Abbr `result`, Abbr `pv`, Abbr `ev`, copy_prop_analyze_def, LET_THM] >>
  `copy_sound_opt (df_at NONE result bb.bb_label
      (phi_prefix_length bb.bb_instructions))
    (s' with vs_inst_idx := 0)` by (
    mp_tac (Q.SPECL [`fn`, `bb`, `s`, `s'`, `result`]
      copy_sound_opt_phi_prefix_eval_phis_result) >>
    impl_tac >- (
      rpt conj_tac
      >- (qpat_x_assum `result = copy_prop_analyze fn` ACCEPT_TAC)
      >- (qpat_x_assum `wf_function fn` ACCEPT_TAC)
      >- (qpat_x_assum `fn_inst_wf fn` ACCEPT_TAC)
      >- (qpat_x_assum `is_fixpoint _ _ result` mp_tac >> simp[Abbr `pv`, Abbr `ev`])
      >- fs[]
      >- (qpat_x_assum `lookup_block bb.bb_label fn.fn_blocks = SOME bb` ACCEPT_TAC)
      >- (qpat_x_assum `MEM bb fn.fn_blocks` ACCEPT_TAC)
      >- (qpat_x_assum `eval_phis s bb.bb_instructions = OK s'` ACCEPT_TAC)
      >- fs[]) >>
    simp[]) >>
  `copy_sound_opt (df_at NONE result bb.bb_label
      (phi_prefix_length bb.bb_instructions))
    (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by (
    qpat_x_assum `copy_sound_opt _ (s' with vs_inst_idx := 0)` mp_tac >>
    simp[GSYM copy_sound_opt_inst_idx]) >>

  (* Now apply the exec_block-based successor soundness from the
     post-PHI entry point. *)
  `bb_well_formed bb` by (fs[wf_function_def] >> metis_tac[]) >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
    (irule phi_prefix_length_lt_wf >> first_assum ACCEPT_TAC) >>
  `phi_prefix_length bb.bb_instructions <= PRE (LENGTH bb.bb_instructions)` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`,
      `s' with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
      `v`, `result`]
    successor_entry_sound_result) >>
  impl_tac >- (
    rpt conj_tac
    >- (qpat_x_assum `result = copy_prop_analyze fn` ACCEPT_TAC)
    >- (qpat_x_assum `is_fixpoint _ _ result` mp_tac >> simp[Abbr `pv`, Abbr `ev`])
    >- (qpat_x_assum `wf_function fn` ACCEPT_TAC)
    >- (qpat_x_assum `fn_inst_wf fn` ACCEPT_TAC)
    >- (qpat_x_assum `ALL_DISTINCT (fn_labels fn)` ACCEPT_TAC)
    >- (qpat_x_assum `!bb. MEM bb fn.fn_blocks ==> _` ACCEPT_TAC)
    >- (qpat_x_assum `MEM bb fn.fn_blocks` ACCEPT_TAC)
    >- fs[]
    >- fs[]
    >- fs[]
    >- (qpat_x_assum `copy_sound_opt _
          (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` mp_tac >>
        fs[])
    >- (qpat_x_assum `exec_block fuel ctx bb
          (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK v` ACCEPT_TAC)) >>
  simp[]
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
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn_subst s)
Proof
  rpt GEN_TAC >> simp_tac std_ss [LET_THM] >> rpt strip_tac
  (* Expand copy_prop_analyze in goal BEFORE adding framework *)
  \\ simp_tac std_ss [copy_prop_analyze_def, LET_THM]
  \\ irule (ISPECL [
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
  \\ rpt conj_tac
  >- (rpt strip_tac >> fs[state_equiv_def, execution_equiv_def, lookup_var_def])
  >- (rpt strip_tac >> rpt conj_tac
      >- metis_tac[run_block_successor_in_cfg_dfs_pre]
      >- metis_tac[run_block_successor_entry_sound, copy_prop_is_fixpoint])
  >- (rpt strip_tac >>
      rename1 `eval_phis st0 bb.bb_instructions = OK st_phi` >>
      mp_tac (Q.SPECL [`fn`, `bb`, `st0`, `st_phi`,
        `df_analyze Forward NONE copy_prop_join copy_prop_transfer
           copy_prop_edge_transfer (phi_used_vars fn)
           (OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : copy_lattice)))
             (fn_entry_label fn)) fn`]
        copy_sound_opt_phi_prefix_eval_phis_result) >>
      impl_tac >- (
        rpt conj_tac
        >- metis_tac[copy_prop_analyze_eq]
        >- qpat_x_assum `wf_function fn` ACCEPT_TAC
        >- qpat_x_assum `fn_inst_wf fn` ACCEPT_TAC
        >- (irule copy_prop_is_fixpoint >> qpat_x_assum `fn_inst_wf fn` ACCEPT_TAC)
        >- first_assum ACCEPT_TAC
        >- (irule venomExecPropsTheory.MEM_lookup_block >> simp[GSYM fn_labels_def])
        >- first_assum ACCEPT_TAC
        >- qpat_x_assum `eval_phis st0 bb.bb_instructions = OK st_phi` ACCEPT_TAC
        >- qpat_x_assum `copy_sound_opt _ st0` ACCEPT_TAC) >>
      simp[])
  >- metis_tac[copy_sound_opt_state_equiv]
  >- (rpt strip_tac >>
      irule (REWRITE_RULE [SIMP_RULE std_ss [LET_THM]
        copy_prop_analyze_def] copy_sound_opt_at_entry) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- metis_tac[execution_equiv_trans]
  >- metis_tac[state_equiv_trans]
  >- simp[state_equiv_execution_equiv_valid_state_rel]
  >- (qpat_x_assum `wf_function fn` ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- metis_tac[copy_sound_opt_state_equiv]
  >- simp[state_equiv_execution_equiv_valid_state_rel]
  >- (irule copy_prop_is_fixpoint >> qpat_x_assum `fn_inst_wf fn` ACCEPT_TAC)
  >- (irule copy_prop_transfer_sound)
  >- (irule assign_subst_inst_simulates)
QED

(* ===== Combined: function-level correctness ===== *)

Triviality find_some_mem_local[local]:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> simp[FIND_thm] >> rpt strip_tac >>
  Cases_on `P h` >> fs[] >> metis_tac[]
QED

Triviality assign_elim_inst_terminator[local]:
  !pv v inst.
    is_terminator (assign_elim_inst pv v inst).inst_opcode <=>
    is_terminator inst.inst_opcode
Proof
  rw[assign_elim_inst_def, LET_THM, mk_nop_inst_def,
     is_forwardable_assign_def] >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def]
QED

Triviality assign_elim_inst_phi[local]:
  !pv v inst.
    (assign_elim_inst pv v inst).inst_opcode = PHI <=>
    inst.inst_opcode = PHI
Proof
  rw[assign_elim_inst_def, LET_THM, mk_nop_inst_def,
     is_forwardable_assign_def] >>
  Cases_on `inst.inst_opcode` >> fs[]
QED

Triviality assign_elim_analysis_blocks_wf[local]:
  !fn result bb.
    wf_function fn /\
    MEM bb (analysis_function_transform NONE result
      (\v inst. [assign_elim_inst (phi_used_vars fn) v inst]) fn).fn_blocks
    ==>
    bb_well_formed bb
Proof
  rpt strip_tac >>
  gvs[analysis_function_transform_def, function_map_transform_def, MEM_MAP] >>
  rename1 `MEM bb0 fn.fn_blocks` >>
  fs[analysis_block_transform_def, flat_mapi_singleton] >>
  irule mapi_transform_bb_well_formed >>
  fs[wf_function_def] >>
  rpt conj_tac >> rpt strip_tac >>
  fs[assign_elim_inst_terminator, assign_elim_inst_phi]
QED

Triviality lookup_block_clear_nops_local[local]:
  !lbl bbs. lookup_block lbl (MAP clear_nops_block bbs) =
            OPTION_MAP clear_nops_block (lookup_block lbl bbs)
Proof
  gen_tac >> Induct >>
  simp[lookup_block_def, listTheory.FIND_thm, clear_nops_block_def] >>
  rw[] >> fs[lookup_block_def, clear_nops_block_def]
QED

Triviality clear_nops_function_correct_blocks_wf[local]:
  !fuel ctx fn s.
    (!bb. MEM bb fn.fn_blocks ==> bb_well_formed bb) /\ s.vs_inst_idx = 0 ==>
    result_equiv {}
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (clear_nops_function fn) s)
Proof
  Induct_on `fuel` >- (
    rpt strip_tac >> simp[run_blocks_def, result_equiv_def]) >>
  rpt strip_tac >>
  once_rewrite_tac[run_blocks_unfold] >>
  simp[clear_nops_function_def, lookup_block_clear_nops_local] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >-
    simp[result_equiv_def] >>
  rename1 `SOME bb` >>
  `bb_well_formed bb` by (
    fs[lookup_block_def] >> drule find_some_mem_local >> metis_tac[]) >>
  `result_equiv {} (run_block fuel ctx bb s)
     (run_block fuel ctx (clear_nops_block bb) s)` by
    simp[clear_nops_run_block_equiv] >>
  Cases_on `run_block fuel ctx bb s`
  >- (
    Cases_on `run_block fuel ctx (clear_nops_block bb) s` >>
    gvs[result_equiv_def] >>
    TRY (imp_res_tac state_equiv_empty_eq >> gvs[result_equiv_def]) >>
    imp_res_tac state_equiv_empty_eq >> gvs[] >>
    imp_res_tac run_block_OK_inst_idx_0 >>
    Cases_on `v.vs_halted` >> gvs[result_equiv_def]
    >- simp[result_equiv_def, execution_equiv_def] >>
    once_rewrite_tac[GSYM clear_nops_function_def] >>
    first_x_assum irule >> simp[] >>
    rpt strip_tac >>
    gvs[clear_nops_function_def, MEM_MAP] >>
    irule clear_nops_block_preserves_wf >> metis_tac[])
  >- (Cases_on `run_block fuel ctx (clear_nops_block bb) s` >>
      gvs[result_equiv_def])
  >- (Cases_on `run_block fuel ctx (clear_nops_block bb) s` >>
      gvs[result_equiv_def])
  >- (Cases_on `run_block fuel ctx (clear_nops_block bb) s` >>
      gvs[result_equiv_def]) >>
  Cases_on `run_block fuel ctx (clear_nops_block bb) s` >>
  gvs[result_equiv_def]
QED

(* Monotonicity: lift_result for stronger relation implies lift_result for weaker *)
Theorem lift_result_weaken[local]:
  !R1_ok R2_ok R1_term R2_term r1 r2.
    (!s1 s2. R1_ok s1 s2 ==> R2_ok s1 s2) /\
    (!s1 s2. R1_term s1 s2 ==> R2_term s1 s2) /\
    lift_result R1_ok R1_term R1_term r1 r2 ==>
    lift_result R2_ok R2_term R2_term r1 r2
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
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (assign_elim_function fn) s)
Proof
  rpt GEN_TAC >> simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  (* Phase 1: fn → fn_subst gives state_equiv {} (or fn errors) *)
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (ISPECL [``fuel:num``, ``ctx:venom_context``,
             ``fn:ir_function``, ``s:venom_state``]
     assign_subst_function_eq)) >>
  impl_tac >- (fs[wf_function_def]) >>
  strip_tac >- (
    simp[]
  ) >>
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (ISPECL [``fuel:num``, ``ctx:venom_context``,
             ``fn:ir_function``, ``s:venom_state``]
     assign_nop_dead_writes_correct)) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  strip_tac >- (
    Cases_on `run_blocks fuel ctx fn s` >>
    fs[lift_result_def]
  ) >>
  DISJ2_TAC >>
  (* Phase 3: clear_nops gives result_equiv {} *)
  qabbrev_tac `fn_elim = analysis_function_transform NONE
     (copy_prop_analyze fn)
     (\v inst. [assign_elim_inst (phi_used_vars fn) v inst]) fn` >>
  `assign_elim_function fn = clear_nops_function fn_elim` by
    simp[assign_elim_function_def, Abbr `fn_elim`] >>
  `!bb. MEM bb fn_elim.fn_blocks ==> bb_well_formed bb` by
    (simp[Abbr `fn_elim`] >> metis_tac[assign_elim_analysis_blocks_wf]) >>
  `result_equiv {}
     (run_blocks fuel ctx fn_elim s)
     (run_blocks fuel ctx (assign_elim_function fn) s)` by (
    qpat_x_assum `assign_elim_function fn = clear_nops_function fn_elim`
      (fn th => REWRITE_TAC [th]) >>
    irule clear_nops_function_correct_blocks_wf >> simp[]) >>
  fs[result_equiv_is_lift_result] >>
  `lift_result (state_equiv (assign_elim_eliminated_vars fn))
     (execution_equiv (assign_elim_eliminated_vars fn))
                  (execution_equiv (assign_elim_eliminated_vars fn))
     (run_blocks fuel ctx fn s)
     (run_blocks fuel ctx
        (analysis_function_transform NONE (copy_prop_analyze fn)
           (\v inst. [assign_subst_inst v inst]) fn) s)` by (
    irule lift_result_weaken >>
    qexistsl_tac [`state_equiv {}`, `execution_equiv {}`] >>
    simp[] >> rpt strip_tac >>
    metis_tac[state_equiv_subset, execution_equiv_subset, EMPTY_SUBSET]
  ) >>
  `lift_result (state_equiv (assign_elim_eliminated_vars fn))
     (execution_equiv (assign_elim_eliminated_vars fn))
                  (execution_equiv (assign_elim_eliminated_vars fn))
     (run_blocks fuel ctx fn s)
     (run_blocks fuel ctx fn_elim s)` by (
    irule lift_result_trans >>
    conj_tac >- (rpt strip_tac >> metis_tac[state_equiv_trans]) >>
    conj_tac >- (rpt strip_tac >> metis_tac[execution_equiv_trans]) >>
    qexists_tac `run_blocks fuel ctx
      (analysis_function_transform NONE (copy_prop_analyze fn)
         (\v inst. [assign_subst_inst v inst]) fn) s` >>
    simp[]) >>
  irule lift_result_trans >>
  conj_tac >- (rpt strip_tac >> metis_tac[state_equiv_trans]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[execution_equiv_trans]) >>
  qexists_tac `run_blocks fuel ctx fn_elim s` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule lift_result_weaken >>
  qexistsl_tac [`state_equiv {}`, `execution_equiv {}`] >>
  simp[] >> rpt strip_tac >>
  metis_tac[state_equiv_subset, execution_equiv_subset, EMPTY_SUBSET]
QED
