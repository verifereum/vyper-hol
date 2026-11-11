Theory loadElimGeneratorPostValidity
Ancestors
  loadElimReachedNormalize loadElimNormalizeHelpers loadElimNormalizedCuts
  loadElimConfiguredGeneration loadElimGenerationSound loadElimKeyShapeInvariant
  loadElimTransferProvenance loadElimSingletonAvailability loadElimSingletonSuffix
  loadElimOccurrence loadElimDefs analysisSimProofsBase
  simplifyCfgLabelProps dfgDefs venomWf venomState venomInst venomExecProofs list finite_map

Theorem le_frame_generator_post_chain_valid:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  frame_reach C fn s0 gi u /\ gi.inst_opcode <> PHI /\
  MEM gi (fn_insts fn) /\ le_transfer_generates ctx gi key op /\
  step_inst k C gi u = OK t ==>
  le_chain_valid ctx.lctx_dfg [] op t
Proof
  strip_tac >>
  `ssa_form fn` by metis_tac[loadElimReachableSSATheory.le_reachable_ssa_unique] >>
  fs[le_transfer_generates_def]
  >- (gvs[] >> irule le_nonassign_output_chain_valid >>
      simp[] >> qexists_tac `gi` >> simp[] >>
      drule_all le_configured_load_opcode >> simp[] >> strip_tac >> gvs[]) >>
  drule_all le_configured_store_opcode >> strip_tac >>
  drule_all le_generating_store_address_exists >> strip_tac >>
  drule_all le_generating_store_state >> strip_tac >>
  `le_chain_valid (dfg_build_function fn) [] op u` by
    (irule le_frame_use_chain_valid >> metis_tac[MEM]) >>
  `!v. lookup_var v t = lookup_var v u` by simp[lookup_var_def] >>
  drule_all le_chain_valid_frame >> gvs[]
QED

Theorem le_occ_generator_post_chain_valid:
  wf_function fn /\ fn_inst_wf fn /\ le_reachable_ssa fn /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
  le_occ_prefix C fn s0 es i s /\ MEM (StepOcc bb n k u t) es /\
  le_transfer_generates ctx (EL n bb.bb_instructions) key op ==>
  le_chain_valid ctx.lctx_dfg [] op t
Proof
  strip_tac >>
  drule_all le_occ_prefix_step_before >> strip_tac >>
  drule_all le_occ_step_static >> strip_tac >>
  `le_occ_valid C fn (StepOcc bb n k u t)` by
    metis_tac[le_occ_prefix_member] >>
  fs[le_occ_valid_def] >>
  `MEM (EL n bb.bb_instructions) (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_mem] >> metis_tac[EL_MEM]) >>
  `frame_reach C fn s0 (EL n bb.bb_instructions) u` by
    metis_tac[le_occ_prefix_forget] >>
  metis_tac[le_frame_generator_post_chain_valid]
QED
