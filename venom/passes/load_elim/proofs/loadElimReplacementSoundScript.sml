Theory loadElimReplacementSound
Ancestors
  loadElimGenerationSound loadElimKeyShapeInvariant loadElimPaddedSimHelpers
  loadElimMemoryRel
  passSharedProps venomExecSemantics venomState venomMemProps venomMemDefs
  loadElimDefs loadElimKeyRead finite_map words vfmState

Theorem le_configured_load_state:
  le_configured_context ctx /\
  i.inst_opcode = ctx.lctx_config.lc_load /\
  i.inst_operands = [addr] /\ i.inst_outputs = [out] /\
  eval_operand addr s = SOME a /\
  le_key_address ctx.lctx_addr_space key s = SOME (w2n a) /\
  le_key_read ctx.lctx_addr_space key s = SOME w /\
  step_inst k C i s = OK s' ==>
  s' = update_var out w s
Proof
  strip_tac >>
  `MEM (i.inst_opcode,ctx.lctx_addr_space)
    [(MLOAD,AddrSp_Memory); (SLOAD,AddrSp_Storage);
     (TLOAD,AddrSp_Transient); (CALLDATALOAD,AddrSp_Calldata);
     (DLOAD,AddrSp_Data)]` by
    (gvs[le_configured_context_def, memory_config_def, storage_config_def,
         transient_config_def, dload_config_def, calldataload_config_def]) >>
  drule_all le_generating_load_state >> strip_tac >>
  gvs[le_key_read_def]
QED

Theorem le_configured_load_replacement:
  le_configured_context ctx /\ padded_exec_equiv V s t /\
  i.inst_opcode = ctx.lctx_config.lc_load /\
  i.inst_operands = [addr] /\ i.inst_outputs = [out] /\
  eval_operand addr s = SOME a /\
  le_key_address ctx.lctx_addr_space key s = SOME (w2n a) /\
  le_key_read ctx.lctx_addr_space key s = SOME w /\
  eval_operand replacement t = SOME w /\
  step_inst k C i s = OK s' ==>
  ?t'. step_inst k C (mk_assign_inst i replacement) t = OK t' /\
       padded_exec_equiv V s' t' /\
       s'.vs_current_bb = s.vs_current_bb /\
       s'.vs_prev_bb = s.vs_prev_bb /\ s'.vs_inst_idx = s.vs_inst_idx /\
       t'.vs_current_bb = t.vs_current_bb /\
       t'.vs_prev_bb = t.vs_prev_bb /\ t'.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >> drule_all le_configured_load_state >> strip_tac >>
  qexists_tac `update_var out w t` >>
  simp[mk_assign_inst_correct] >>
  simp[padded_exec_equiv_update_var]
QED

Theorem le_configured_redundant_store_state:
  le_configured_context ctx /\
  ctx.lctx_config.lc_store = SOME i.inst_opcode /\
  i.inst_operands = [addr; value] /\ i.inst_outputs = [] /\
  eval_operand addr s = SOME a /\ eval_operand value s = SOME w /\
  le_read_address ctx.lctx_addr_space (w2n a) s = SOME w /\
  step_inst k C i s = OK s' ==>
  padded_exec_equiv V s' s /\
  s'.vs_current_bb = s.vs_current_bb /\
  s'.vs_prev_bb = s.vs_prev_bb /\ s'.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  gvs[le_configured_context_def, memory_config_def, storage_config_def,
      transient_config_def, dload_config_def, calldataload_config_def] >>
  simp[Once step_inst_def] >>
  simp[step_inst_base_opcode_eqs, exec_write2_def, eval_operands_def] >>
  rpt IF_CASES_TAC >> strip_tac >> gvs[]
  >- (conj_tac
      >- metis_tac[padded_exec_equiv_mstore_mload, padded_exec_equiv_sym] >>
      simp[mstore_def])
  >- (simp[sstore_def, sload_def, contract_storage_def,
           lookup_storage_def, update_storage_def, lookup_account_def,
           combinTheory.APPLY_UPDATE_ID,
           vfmStateTheory.account_state_component_equality,
           venom_state_component_equality, padded_exec_equiv_refl])
  >> simp[tstore_def, tload_def, contract_transient_def,
          lookup_storage_def, update_storage_def,
          combinTheory.APPLY_UPDATE_ID,
          venom_state_component_equality, padded_exec_equiv_refl]
QED

Theorem le_configured_store_replacement:
  le_configured_context ctx /\ padded_exec_equiv V s t /\
  ctx.lctx_config.lc_store = SOME i.inst_opcode /\
  i.inst_operands = [addr; value] /\ i.inst_outputs = [] /\
  eval_operand addr s = SOME a /\ eval_operand value s = SOME w /\
  le_read_address ctx.lctx_addr_space (w2n a) s = SOME w /\
  step_inst k C i s = OK s' ==>
  ?t'. step_inst k C (mk_nop_inst i) t = OK t' /\
       padded_exec_equiv V s' t' /\
       s'.vs_current_bb = s.vs_current_bb /\
       s'.vs_prev_bb = s.vs_prev_bb /\ s'.vs_inst_idx = s.vs_inst_idx /\
       t'.vs_current_bb = t.vs_current_bb /\
       t'.vs_prev_bb = t.vs_prev_bb /\ t'.vs_inst_idx = t.vs_inst_idx
Proof
  strip_tac >> drule_all le_configured_redundant_store_state >> strip_tac >>
  qexists_tac `t` >> simp[mk_nop_inst_correct] >>
  metis_tac[padded_exec_equiv_trans]
QED
