(* Range analysis soundness for algebraic optimization.
 *
 * All theorems fully proved (no cheats).
 *
 * range_analyze_sound: if in_range_state holds at program point (lbl, idx),
 *   then any operand that evaluates to v has v in the computed range.
 *
 * range_intra_transfer: range_at_inst at SUC idx equals the transfer
 *   function applied at idx (connects fixpoint to per-instruction state).
 *
 * range_entry_eq_at_inst: range_at_inst at index 0 equals range_entry_state.
 *
 * range_step_inv: step_inst preserves in_range_state for the next
 *   instruction, given that inst is the actual instruction at (lbl, idx).
 *
 * Integration (aoBlockSimLocalScript.sml / aoPhase3ProofScript.sml):
 *   Use in_range_state as block_inv component (via range_at_inst ... 0).
 *   Per-instruction, derive H_range from in_range_state + range_analyze_sound.
 *   Thread in_range_state through block via range_step_inv.
 *   See ao_block_sim_local in aoBlockSimLocalScript.sml.
 *)
Theory aoRangeObligation
Ancestors
  algebraicOptDefs rangeAnalysisDefs rangeAnalysisProofs
  rangeEvalDefs valueRangeDefs venomExecSemantics venomState
  dfAnalyzeWidenProps cfgDefs venomWf

(* Proved: if range state is sound at (lbl, idx) and operand
   evaluates to v, then range_get_range returns containing range. *)
Theorem range_analyze_sound:
  !ra lbl idx s op v.
    in_range_state (range_at_inst ra lbl idx) s.vs_vars /\
    eval_operand op s = SOME v ==>
    in_range (range_get_range ra lbl idx op) v
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`ra`, `lbl`, `idx`, `op`, `v`,
               `s.vs_vars`] mp_tac range_get_range_sound_proof >>
  impl_tac >- (
    rpt conj_tac >> simp[] >>
    Cases_on `op` >> fs[eval_operand_def, lookup_var_def]) >>
  simp[]
QED

(* Helper: range_transfer_opt unwraps to range_evaluate_inst *)
Theorem range_unwrap_transfer:
  !dfg bbs inst rs.
    range_unwrap (range_transfer_opt (dfg, bbs) inst rs) =
    range_evaluate_inst dfg inst (range_unwrap rs)
Proof
  rpt gen_tac >> Cases_on `rs` >>
  simp[range_transfer_opt_def, range_unwrap_def]
QED

(* Intra-block transfer for range analysis: range_at_inst at SUC idx
   equals the transfer function applied at idx. *)
Theorem range_intra_transfer:
  !fn0 lbl bb idx.
    wf_function fn0 /\
    MEM lbl (cfg_analyze fn0).cfg_dfs_pre /\
    lookup_block lbl fn0.fn_blocks = SOME bb /\
    SUC idx <= LENGTH bb.bb_instructions ==>
    range_at_inst (range_analyze fn0) lbl (SUC idx) =
    range_evaluate_inst (dfg_build_function fn0)
      (EL idx bb.bb_instructions)
      (range_at_inst (range_analyze fn0) lbl idx)
Proof
  rpt strip_tac >>
  simp[range_at_inst_def] >>
  `df_widen_at NONE (range_analyze fn0) lbl (SUC idx) =
   range_transfer_opt (dfg_build_function fn0, fn0.fn_blocks)
     (EL idx bb.bb_instructions)
     (df_widen_at NONE (range_analyze fn0) lbl idx)` by (
    mp_tac (SIMP_RULE std_ss [LET_THM]
      (REWRITE_RULE [GSYM (SIMP_RULE std_ss [LET_THM] range_analyze_def)]
      (ISPECL [
        ``Forward``,
        ``NONE : (string |-> value_range) option``,
        ``range_join_opt``,
        ``range_widen_opt : (string |-> value_range) option
            -> (string |-> value_range) option
            -> (string |-> value_range) option``,
        ``WIDEN_THRESHOLD``,
        ``range_transfer_opt``,
        ``range_edge_transfer_opt``,
        ``(dfg_build_function fn0, fn0.fn_blocks)``,
        ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
            (fn_entry_label fn0)``,
        ``fn0 : ir_function``,
        ``lbl : string``,
        ``bb : basic_block``,
        ``idx : num``]
      df_widen_at_intra_transfer))) >>
    impl_tac >- (
      conj_tac >- first_assum ACCEPT_TAC >>
      mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >> simp[]) >>
    simp[]) >>
  simp[range_unwrap_transfer]
QED

(* Entry state equals range_at_inst at index 0 *)
Theorem range_entry_eq_at_inst:
  !fn0 lbl bb.
    wf_function fn0 /\
    MEM lbl (cfg_analyze fn0).cfg_dfs_pre /\
    lookup_block lbl fn0.fn_blocks = SOME bb ==>
    range_at_inst (range_analyze fn0) lbl 0 =
    range_entry_state (range_analyze fn0) lbl
Proof
  rpt strip_tac >>
  simp[range_at_inst_def, range_entry_state_def] >>
  mp_tac (SIMP_RULE std_ss [LET_THM]
    (REWRITE_RULE [GSYM (SIMP_RULE std_ss [LET_THM] range_analyze_def)]
    (ISPECL [
      ``Forward``,
      ``NONE : (string |-> value_range) option``,
      ``range_join_opt``,
      ``range_widen_opt : (string |-> value_range) option
          -> (string |-> value_range) option
          -> (string |-> value_range) option``,
      ``WIDEN_THRESHOLD``,
      ``range_transfer_opt``,
      ``range_edge_transfer_opt``,
      ``(dfg_build_function fn0, fn0.fn_blocks)``,
      ``OPTION_MAP (\lbl. (lbl, SOME (FEMPTY : string |-> value_range)))
          (fn_entry_label fn0)``,
      ``fn0 : ir_function``,
      ``lbl : string``,
      ``bb : basic_block``]
    df_widen_at_inter_transfer))) >>
  impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    mp_tac (SIMP_RULE std_ss [LET_THM] range_fixpoint) >> simp[]) >>
  simp[]
QED

(* step_inst preserves in_range_state for the next instruction.
   Requires that inst is the actual instruction at (lbl, idx). *)
Theorem range_step_inv:
  !fn0 lbl bb idx inst fuel ctx s s'.
    let ra = range_analyze fn0 in
    wf_function fn0 /\
    MEM lbl (cfg_analyze fn0).cfg_dfs_pre /\
    lookup_block lbl fn0.fn_blocks = SOME bb /\
    inst = EL idx bb.bb_instructions /\
    SUC idx <= LENGTH bb.bb_instructions /\
    in_range_state (range_at_inst ra lbl idx) s.vs_vars /\
    step_inst fuel ctx inst s = OK s' ==>
    in_range_state (range_at_inst ra lbl (SUC idx)) s'.vs_vars
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `range_at_inst (range_analyze fn0) lbl (SUC idx) =
   range_evaluate_inst (dfg_build_function fn0) inst
     (range_at_inst (range_analyze fn0) lbl idx)` by (
    gvs[] >> irule range_intra_transfer >> simp[]) >>
  gvs[] >>
  irule per_inst_range_sound >>
  qexistsl_tac [`ctx`, `fuel`, `s`] >> simp[]
QED
