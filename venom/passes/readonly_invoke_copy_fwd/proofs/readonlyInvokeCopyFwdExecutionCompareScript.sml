Theory readonlyInvokeCopyFwdExecutionCompare
Ancestors
  readonlyInvokeCopyFwdExecutionLocal readonlyInvokeCopyFwdExecution
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdValues
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdEndpointBounds
  o1LowerDloadPtrDiscipline o1LowerDloadGhost o1LowerDloadRelocationKernel
  o1LowerDloadOccurrence allocaFrontierBound internalReturnCopyFwdSim
  unitMemInv taintAgree ptrDiscipline pointerConfinedDefs memLocDefs
  venomExecSemantics venomState venomInst codegenRel finite_map list pred_set words

Theorem ricf_execution_comparison_values[local]:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [LT;GT;EQ] /\ inst.inst_operands = [p;q] /\
  eval_operand p s = SOME x /\ eval_operand q s = SOME y ==>
  ?x' y'. eval_operand p t = SOME x' /\ eval_operand q t = SOME y' /\
    (w2n x < w2n y <=> w2n x' < w2n y') /\
    (w2n y < w2n x <=> w2n y' < w2n x') /\ (x = y <=> x' = y')
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    (fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
     metis_tac[occ_frame_reachable_projection]) >>
  `access_ok lo G fn inst s /\ taint_ok fn tn inst s` by
    metis_tac[ptr_discipline_def] >>
  `op_taint tn p = {} /\ op_taint tn q = {}` by
    (fs[MEM] >> gvs[taint_ok_def] >> metis_tac[]) >>
  `ricf_frame_agree D (ircf_dead (ricf_original_copy_ids C) s stk) sites
    (ricf_complete_params PG s.vs_params) G tn s t /\
   ricf_map_origins vs C ctx0 log stk PG G tn fn inst s U B sites` by
    fs[ricf_execution_invariant_def] >>
  `?x'. eval_operand p t = SOME x' /\
    ricf_value_agree sites (op_prov G p) {} x x'` by
    metis_tac[ricf_frame_agree_operand] >>
  `?y'. eval_operand q t = SOME y' /\
    ricf_value_agree sites (op_prov G q) {} y y'` by
    metis_tac[ricf_frame_agree_operand] >>
  qexistsl_tac [`x'`,`y'`] >> simp[] >>
  Cases_on `op_prov G p = NONE /\ op_prov G q = NONE`
  >- (gvs[ricf_value_agree_def] >>
      imp_res_tac ld_value_agree_clean >> gvs[]) >>
  `?P. FDOM G SUBSET fn_pv P fn /\ ptr_use_ok P (fn_pv P fn) inst` by
    (`?P. EVERY (fn_ptr_ok P) C.ctx_functions` by
       metis_tac[ptr_discipline_fn_ptr_ok] >>
     `MEM fn C.ctx_functions /\ FDOM G SUBSET fn_pv P fn` by
       metis_tac[frame_reachable_prov_support] >>
     qexists_tac `P` >> simp[] >>
     `MEM inst (fn_insts fn)` by metis_tac[active_inst_mem_fn_insts] >>
     gvs[EVERY_MEM, fn_ptr_ok_def] >> metis_tac[]) >>
  `?u w. p = Var u /\ q = Var w /\ (u IN FDOM G \/ w IN FDOM G)` by
    (Cases_on `p` >> Cases_on `q` >>
     gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF, ptr_use_ok_def,
       mem_read_ops_def, mem_write_ops_def, is_pointer_preserving_op_def, MEM] >>
     metis_tac[]) >>
  gvs[] >>
  (`?b z. FLOOKUP G u = SOME (b,z) /\ FLOOKUP G w = SOME (b,z) /\
    0 < z /\ b <= w2n x /\ w2n x <= b+z /\
    b <= w2n y /\ w2n y <= b+z` by
    (qpat_x_assum `access_ok _ _ _ _ _` mp_tac >>
     gvs[access_ok_def, MEM] >> metis_tac[]) >>
  namedCases_on `FLOOKUP sites (b,z)` ["", "endpoint_tr"]
  >- (`(b,z) NOTIN FDOM sites` by fs[FLOOKUP_DEF] >>
      `ld_value_agree sites NONE {} x x' /\ ld_value_agree sites NONE {} y y'` by
        gvs[ricf_value_agree_def, op_prov_def] >>
      imp_res_tac ld_value_agree_clean >> gvs[]) >>
  PairCases_on `endpoint_tr : num # num # num` >>
  `endpoint_tr0 = b /\ endpoint_tr2 = z` by
    (fs[ricf_frame_agree_def, ricf_sites_ok_def] >> metis_tac[]) >>
  qpat_x_assum `endpoint_tr0 = b` SUBST_ALL_TAC >>
  qpat_x_assum `endpoint_tr2 = z` SUBST_ALL_TAC >>
  `b+z < dimword (:256) /\ endpoint_tr1+z < dimword (:256)` by
    (fs[ricf_map_origins_def] >>
     metis_tac[ricf_translation_origin_endpoint_bounds]) >>
  `ricf_sites_ok sites` by fs[ricf_frame_agree_def] >>
  gvs[op_prov_def] >> metis_tac[ricf_value_agree_comparisons])
QED

Theorem ricf_execution_comparison_next:
  ricf_execution_invariant vs C ctx0 log D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  EVERY wf_function C.ctx_functions /\ mem_inv raw_mem_ok C vs /\
  ptr_discipline lo C vs /\ active_inst fn inst s /\
  MEM inst.inst_opcode [LT;GT;EQ] /\
  step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ?v. step_inst fuel Ct inst t = OK v /\
    ricf_execution_invariant vs C ctx0 log D stk PG (step_prov PG G inst u)
      (step_taint inst s u tn) fn next
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (v with vs_inst_idx := SUC s.vs_inst_idx)
      n a U (occurrence_sites_step a B inst u) HP
      (occurrence_step a HP H inst u) ledger E sites maps targets
      (step_taint inst s u tn)
Proof
  strip_tac >>
  `?p q out x y. inst.inst_operands = [p;q] /\ inst.inst_outputs = [out] /\
    eval_operand p s = SOME x /\ eval_operand q s = SOME y` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >> fs[MEM] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all ricf_execution_comparison_values >> strip_tac >>
  `?value. u = update_var out value s /\
    step_inst fuel Ct inst t = OK (update_var out value t)` by
    (qpat_x_assum `step_inst fuel C inst s = OK u` mp_tac >> fs[MEM] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs,
       exec_pure2_def, arithmeticTheory.GREATER_DEF] >> metis_tac[]) >>
  qexists_tac `update_var out value t` >> simp[] >> gvs[] >>
  `out_taint tn inst s = {} /\ written_taint tn inst s = {}` by
    (fs[MEM] >> gvs[out_taint_def, written_taint_def] >> rpt CASE_TAC >> simp[]) >>
  irule (Q.INST [`p` |-> `NONE`, `m` |-> `{}`] ricf_execution_bind_next) >>
  simp[ricf_value_agree_def, ld_value_agree_def, word_agree_except_def] >>
  fs[MEM] >>
  gvs[step_prov_def, out_prov_def, step_taint_def, out_taint_def,
    mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
    range_bytes_def, taint_component_equality, occurrence_sites_step_def,
    source_memory_write_ranges_def, update_var_def,
    FLOOKUP_DEF, is_terminator_def, SF CONJ_ss] >>
  metis_tac[update_var_def]
QED
