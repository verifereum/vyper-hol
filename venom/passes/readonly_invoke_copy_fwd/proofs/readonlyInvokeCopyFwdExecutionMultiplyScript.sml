Theory readonlyInvokeCopyFwdExecutionMultiply
Ancestors
  allocaFrontierBound
  pointerConfinedDefs
  readonlyInvokeCopyFwdExecutionMemoryScalars readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdOpaque readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdValues
  o1LowerDloadOccurrence o1LowerDloadRelocationKernel frameRelocationGuardedValues
  internalReturnCopyFwdSim frameViewFacts ptrDiscipline taintAgree memLocDefs
  venomExecSemantics venomExecProps venomState venomInst codegenRel
  finite_map list pred_set words

Theorem ricf_execution_mul_next:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\ ssa_form fn /\ opaque_use_ok fn /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\ inst.inst_opcode = MUL /\
  step_inst fuel C inst s = OK u /\
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
  `?lhs rhs out x y. inst.inst_operands = [lhs;rhs] /\
    inst.inst_outputs = [out] /\ eval_operand lhs s = SOME x /\
    eval_operand rhs s = SOME y /\ u = update_var out (x*y) s` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def,
       AllCaseEqs()] >> metis_tac[]) >>
  `?x'. eval_operand lhs t = SOME x' /\ word_agree_except (op_taint tn lhs) x x'` by
    (drule ricf_execution_nonaddress_value >> disch_then irule >>
     simp[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
     metis_tac[]) >>
  `?y'. eval_operand rhs t = SOME y' /\ word_agree_except (op_taint tn rhs) y y'` by
    (drule ricf_execution_nonaddress_value >> disch_then irule >>
     simp[is_pointer_preserving_op_def, mem_read_ops_def, mem_write_ops_def] >>
     metis_tac[]) >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `taint_ok fn tn inst s` by metis_tac[ptr_discipline_def] >>
  `(op_taint tn lhs = {} \/
      (op_taint tn rhs = {} /\ (y = 0w \/ y = 1w))) /\
   (op_taint tn rhs = {} \/
      (op_taint tn lhs = {} /\ (x = 0w \/ x = 1w)))` by
    (qpat_x_assum `taint_ok fn tn inst s` (fn th =>
       let val use = CONJUNCT1 (REWRITE_RULE [taint_ok_def] th)
       in MAP_EVERY mp_tac [Q.SPEC `lhs` use, Q.SPEC `rhs` use] end) >>
     Cases_on `op_taint tn lhs = {}` >> Cases_on `op_taint tn rhs = {}` >>
     gvs[] >> rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `word_agree_except
    ((if x = 1w then op_taint tn rhs else {}) UNION
     (if y = 1w then op_taint tn lhs else {})) (x*y) (x'*y')` by
    (irule word_agree_except_selector_mul >> simp[]) >>
  `word_agree_except (out_taint tn inst s) (x*y) (x'*y')` by
    gvs[out_taint_def] >>
  `~retpc_var fn out` by
    (irule noncopy_output_not_retpc >> simp[] >> qexists_tac `inst` >>
     simp[] >> metis_tac[active_inst_mem_fn_insts]) >>
  `step_inst fuel Ct inst t = OK (update_var out (x'*y') t)` by
    simp[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_pure2_def] >>
  qexists_tac `update_var out (x'*y') t` >> simp[] >> gvs[] >>
  irule (Q.INST [`p` |-> `NONE`, `m` |-> `out_taint tn inst s`]
    ricf_execution_bind_next) >>
  simp[ricf_opaque_value_agree_def, ricf_is_zero_prov_def,
    ricf_value_agree_def, ld_value_agree_def] >>
  gvs[step_prov_def, out_prov_def, step_taint_def, mem_taint_def,
    adopt_reset_def, store_taint_def, imm_taint_def, new_site_bytes_def,
    step_writes_def, written_taint_def, range_bytes_def, taint_component_equality,
    occurrence_sites_step_def, source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, is_terminator_def, SF CONJ_ss] >> metis_tac[update_var_def]
QED
