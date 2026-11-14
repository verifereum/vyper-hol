Theory readonlyInvokeCopyFwdExecutionLocal
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdOpaqueReturn
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdValues
  frameViewFacts frameRel unitShapeDefs o1PassContract
  readonlyInvokeCopyFwdGlobalSupport readonlyInvokeCopyFwdRel
  internalReturnCopyFwdSim ptrDiscipline taintAgree
  contextCodegenRel o1LowerDloadOccurrence
  venomExecSemantics venomState venomInst finite_map list pred_set

Theorem ricf_execution_param_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ssa_form fn /\
  active_inst fn inst s /\ inst.inst_opcode = PARAM /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u rt)
Proof
  strip_tac >>
  `w2n idx < LENGTH s.vs_params /\
   u = update_var out (EL (w2n idx) s.vs_params) s` by
    gvs[step_inst_def, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     metis_tac[MEM_EL]) >>
  `~retpc_var fn out` by
    (irule noncopy_output_not_retpc >> simp[] >> qexists_tac `inst` >> simp[]) >>
  `ricf_opaque_frame_agree fn D
    (ircf_dead (ricf_original_copy_ids C) s stk) sites
    (ricf_complete_params PG s.vs_params) G rt s t` by
    fs[ricf_execution_invariant_def] >>
  `ricf_opaque_params_agree sites (ricf_complete_params PG s.vs_params)
    s.vs_params t.vs_params` by metis_tac[ricf_opaque_frame_params] >>
  `LENGTH PG <= LENGTH s.vs_params` by
    (fs[ricf_opaque_params_agree_def, ricf_complete_params_def] >> decide_tac) >>
  `ricf_opaque_value_agree sites
    (if w2n idx < LENGTH PG then EL (w2n idx) PG else NONE) {}
    (EL (w2n idx) s.vs_params) (EL (w2n idx) t.vs_params)` by
    (fs[ricf_opaque_params_agree_def] >>
     first_x_assum (qspec_then `w2n idx` mp_tac) >>
     simp[ricf_complete_params_el]) >>
  qexists_tac `update_var out (EL (w2n idx) t.vs_params) t` >>
  conj_asm1_tac >-
    gvs[step_inst_def, step_inst_base_opcode_eqs, ricf_opaque_params_agree_def] >>
  gvs[] >> irule ricf_execution_bind_next >>
  simp[step_prov_def, out_prov_def, step_taint_def,
    out_taint_def, mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, taint_component_equality, occurrence_sites_step_def,
    codegenRelTheory.source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, eval_operand_def, is_terminator_def, SF CONJ_ss] >>
  metis_tac[update_var_def]
QED

Theorem ricf_execution_nop_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = NOP /\ inst.inst_outputs = [] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u rt)
Proof
  strip_tac >> `u = s` by gvs[step_inst_def, step_inst_base_opcode_eqs] >>
  `!tau. step_taint inst s s tau = tau` by
    (gen_tac >> simp[step_taint_def, mem_taint_def, adopt_reset_def,
       store_taint_def, imm_taint_def, new_site_bytes_def, step_writes_def,
       written_taint_def, range_bytes_def, taint_component_equality,
       set_var_taint_def, DRESTRICT_UNIV,
       codegenRelTheory.source_memory_write_ranges_def, FLOOKUP_DEF,
       EXTENSION, SF CONJ_ss] >>
     namedCases_on `inst.inst_operands` ["", "a ops1"] >> simp[] >>
     namedCases_on `ops1` ["", "b ops2"] >> simp[] >>
     namedCases_on `ops2` ["", "c ops3"] >> simp[] >>
     Cases_on `ops3` >> simp[]) >>
  qexists_tac `t` >> conj_tac >- simp[step_inst_def, step_inst_base_opcode_eqs] >>
  irule ricf_execution_next >>
  simp[is_terminator_def, step_prov_def, out_prov_def, set_prov_def,
    occurrence_sites_step_def, DRESTRICT_UNIV] >>
  fs[ricf_execution_invariant_def] >> metis_tac[]
QED

Theorem ricf_execution_retpc_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets rt /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  active_inst fn inst s /\ inst.inst_opcode = RETPC_PARAM /\
  inst.inst_operands = [Lit idx] /\ inst.inst_outputs = [out] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u rt)
Proof
  strip_tac >>
  `u = update_var out s.vs_return_pc_token s` by
    gvs[step_inst_def, step_inst_base_opcode_eqs] >>
  `MEM inst (fn_insts fn)` by
    (fs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `retpc_var fn out` by
    (simp[retpc_var_def] >> irule copy_phi_var_seed >> metis_tac[MEM]) >>
  qexists_tac `update_var out t.vs_return_pc_token t` >>
  conj_asm1_tac >- simp[step_inst_def, step_inst_base_opcode_eqs] >>
  gvs[] >>
  irule (Q.INST [`p` |-> `NONE`, `m` |-> `{}`] ricf_execution_bind_next) >>
  simp[ricf_opaque_value_agree_def, ricf_value_agree_def, o1LowerDloadRelocationKernelTheory.ld_value_agree_def,
    ptrDisciplineTheory.word_agree_except_def,
    step_prov_def, out_prov_def, first_prov_def, step_taint_def, out_taint_def, mem_taint_def,
    adopt_reset_def, store_taint_def, imm_taint_def, new_site_bytes_def,
    step_writes_def, written_taint_def, range_bytes_def, taint_component_equality,
    occurrence_sites_step_def, codegenRelTheory.source_memory_write_ranges_def,
    update_var_def, FLOOKUP_DEF, eval_operand_def, is_terminator_def, SF CONJ_ss] >>
  metis_tac[update_var_def]
QED
