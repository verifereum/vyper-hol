Theory loadElimStructuralCurrentness
Ancestors
  loadElimHomogeneousCurrentness loadElimGeneratorPostValidity
  loadElimReachedNormalize loadElimOperandValidity loadElimNormalizeHelpers
  loadElimSingletonAvailability loadElimSingletonSuffix loadElimOccurrence
  loadElimKeyShapeInvariant loadElimKeyRead loadElimTransferProvenance loadElimDefs
  analysisSimProofsBase dfgDefs dfAnalyzeDefs cfgDefs venomWf venomState
  basePtrDefs list finite_map

Theorem le_occ_step_operands_valid:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_occ_prefix C fn s0 es i s /\ MEM (StepOcc bb n k u t) es ==>
  le_inst_operands_valid (dfg_build_function fn) (EL n bb.bb_instructions) u
Proof
  strip_tac >> drule_all le_occ_prefix_step_before >> strip_tac >>
  drule_all le_occ_step_static >> strip_tac >>
  simp[le_inst_operands_valid_def, EVERY_MEM] >> rpt strip_tac >>
  irule le_frame_use_chain_valid >> metis_tac[le_occ_prefix_forget]
QED

Theorem le_occ_prefix_homogeneous_current_structural:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME vs /\
  vs <> [] /\ EVERY (\op. normalize_operand ctx.lctx_dfg [] op = r) vs ==>
  le_key_read ctx.lctx_addr_space key s = eval_operand r s
Proof
  strip_tac >> irule le_occ_prefix_homogeneous_current_local >> simp[] >>
  qexistsl [`C`, `es`, `fn`, `i`, `s0`, `vs`] >> simp[] >>
  conj_tac
  >- metis_tac[le_occ_generator_post_chain_valid] >>
  metis_tac[le_occ_step_operands_valid]
QED

Theorem le_occ_prefix_store_test_current_structural:
  le_occ_prefix C fn s0 es i s /\
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  wf_alias_sets ctx.lctx_aliases /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  is_fixpoint (df_process_block Forward NONE load_join load_transfer
    load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
    (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
    (load_analyze ctx fn) /\
  i.inst_opcode <> PHI /\ MEM value i.inst_operands /\
  FLOOKUP (unwrap_load_lattice
    (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME vs /\
  vs <> [] /\
  EVERY (\a. case (a,value) of (Var _,Var _) =>
    normalize_operand ctx.lctx_dfg [] a = normalize_operand ctx.lctx_dfg [] value
    | _ => a = value) vs ==>
  le_key_read ctx.lctx_addr_space key s = eval_operand value s
Proof
  strip_tac >>
  `EVERY (\op. normalize_operand ctx.lctx_dfg [] op =
     normalize_operand ctx.lctx_dfg [] value) vs` by
    (gvs[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> Cases_on `op` >> Cases_on `value` >> simp[]) >>
  `le_key_read ctx.lctx_addr_space key s =
     eval_operand (normalize_operand ctx.lctx_dfg [] value) s` by
    (irule le_occ_prefix_homogeneous_current_structural >> simp[] >>
     qexistsl [`C`, `es`, `fn`, `i`, `s0`, `vs`] >> gvs[] >>
     first_assum ACCEPT_TAC) >>
  `eval_operand (normalize_operand (dfg_build_function fn) [] value) s =
     eval_operand value s` by
    (irule le_frame_use_normalize_eval >> metis_tac[le_occ_prefix_forget]) >>
  gvs[]
QED
