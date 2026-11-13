Theory readonlyInvokeCopyFwdExecutionShift
Ancestors
  allocaFrontierBound
  pointerConfinedDefs
  readonlyInvokeCopyFwdExecutionMemoryScalars readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdValues
  o1LowerDloadOccurrence o1LowerDloadRelocationKernel
  internalReturnCopyFwdSim frameViewFacts ptrDiscipline taintAgree
  venomExecSemantics venomExecProps venomState venomInst codegenRel
  finite_map list pred_set words

Theorem ricf_execution_shift_operands[local]:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  ptr_discipline lo C vs /\ opaque_use_ok fn /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SHL;SHR;SAR] /\ inst.inst_operands = [amount;data] /\
  eval_operand amount s = SOME k /\ eval_operand data s = SOME x ==>
  ?y. eval_operand amount t = SOME k /\ eval_operand data t = SOME y /\
    word_agree_except (op_taint tn data) x y
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `op_taint tn amount = {}` by
    (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  `eval_operand amount t = SOME k` by
    (drule ricf_execution_nonaddress_operand >> disch_then irule >> fs[MEM] >>
     simp[is_pointer_preserving_op_def, memLocDefsTheory.mem_read_ops_def,
       memLocDefsTheory.mem_write_ops_def] >> metis_tac[]) >>
  `op_prov G data = NONE` by
    (drule ricf_execution_nonaddress_no_provenance >> disch_then irule >> fs[MEM] >>
     simp[is_pointer_preserving_op_def, memLocDefsTheory.mem_read_ops_def,
       memLocDefsTheory.mem_write_ops_def] >> metis_tac[]) >>
  `!name. data = Var name ==> ~retpc_var fn name` by
    (rpt gen_tac >> strip_tac >> irule ordinary_operand_not_retpc >> simp[] >>
     qexists_tac `inst` >> fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
  `ricf_opaque_frame_agree fn D (ircf_dead (ricf_original_copy_ids C) s stk)
    sites (ricf_complete_params PG s.vs_params) G tn s t` by
    fs[ricf_execution_invariant_def] >>
  drule_all (Q.INST [`op` |-> `data`] ricf_opaque_frame_operand) >> strip_tac >>
  qexists_tac `y` >>
  gvs[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
    ricf_value_agree_def, ld_value_agree_def]
QED

Theorem ricf_execution_shift_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ssa_form fn /\ opaque_use_ok fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [SHL;SHR;SAR] /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `?amount data out k x. inst.inst_operands = [amount;data] /\
    inst.inst_outputs = [out] /\ eval_operand amount s = SOME k /\
    eval_operand data s = SOME x /\
    u = update_var out
      (if inst.inst_opcode = SHL then word_lsl x (w2n k)
       else if inst.inst_opcode = SHR then word_lsr x (w2n k)
       else word_asr x (w2n k)) s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     fs[MEM] >> gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all ricf_execution_shift_operands >> strip_tac >>
  `~retpc_var fn out` by
    (irule noncopy_output_not_retpc >> simp[] >> qexists_tac `inst` >>
     fs[MEM] >> metis_tac[active_inst_mem_fn_insts]) >>
  qabbrev_tac `z = if inst.inst_opcode = SHL then word_lsl y (w2n k)
    else if inst.inst_opcode = SHR then word_lsr y (w2n k)
    else word_asr y (w2n k)` >>
  `word_agree_except (out_taint tn inst s)
    (if inst.inst_opcode = SHL then word_lsl x (w2n k)
     else if inst.inst_opcode = SHR then word_lsr x (w2n k)
     else word_asr x (w2n k)) z` by
    (fs[MEM] >> gvs[out_taint_def, Abbr `z`] >>
     metis_tac[word_agree_except_shl, word_agree_except_shr, word_agree_except_sar]) >>
  `step_inst fuel Ct inst t = OK (update_var out z t)` by
    (fs[MEM] >> simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_pure2_def, Abbr `z`]) >>
  qexists_tac `update_var out z t` >> simp[] >> gvs[] >>
  irule (Q.INST [`p` |-> `NONE`, `m` |-> `out_taint tn inst s`]
    ricf_execution_bind_next) >>
  simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
    ricf_value_agree_def, ld_value_agree_def] >> fs[MEM] >>
  gvs[step_prov_def, out_prov_def, step_taint_def, mem_taint_def,
    adopt_reset_def, store_taint_def, imm_taint_def, new_site_bytes_def,
    step_writes_def, written_taint_def, range_bytes_def, taint_component_equality,
    occurrence_sites_step_def, source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, is_terminator_def, SF CONJ_ss] >> metis_tac[update_var_def]
QED
