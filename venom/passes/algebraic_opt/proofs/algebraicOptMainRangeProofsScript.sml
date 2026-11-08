Theory algebraicOptMainRangeProofs
Ancestors
  algebraicOptMainScalarProofs algebraicOptRangeClosureProofs
  algebraicOptTraceProofs algebraicOptShapeProofs algebraicOptRelationProofs
  algebraicOptDefs venomExecSemantics venomWf unitShapeDefs
Libs
  listTheory

Theorem ao_pre_flip_operand_mem:
  !i a. MEM a (ao_pre_flip_inst i).inst_operands <=> MEM a i.inst_operands
Proof
  rpt gen_tac >> simp[ao_pre_flip_inst_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  IF_CASES_TAC >> simp[] >> metis_tac[]
QED

Theorem ao_main_resolved_operand_range:
  !ctx fn s0 n k s inst bb V r p a w.
  ao_source_prefix ctx fn s0 n k F s /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  s0.vs_inst_idx = 0 /\ s0.vs_prev_bb = NONE /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==> lookup_var x s0 = NONE) /\
  MEM inst (fn_insts fn) /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> PHI /\ ~is_truthy_inst inst.inst_opcode /\
  inst.inst_opcode <> ISZERO /\
  ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  (!b. MEM b inst.inst_operands ==> ?v. eval_operand b s = SOME v) /\
  p = ao_pre_flip_inst (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst) /\
  MEM a p.inst_operands /\ eval_operand a r = SOME w ==>
  in_range (range_get_range (range_analyze fn) s.vs_current_bb s.vs_inst_idx a) w
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_source_prefix_has_trace >> strip_tac >>
  `?b. MEM b inst.inst_operands /\
       a = ao_resolve_iszero_op (ao_compute_fn_iszero_targets fn) inst.inst_opcode b` by
    (gvs[ao_pre_flip_operand_mem, ao_resolve_iszero_inst_def, MEM_MAP] >>
     metis_tac[]) >>
  `?v. eval_operand b s = SOME v` by metis_tac[] >>
  `eval_operand a r = SOME v` by
    (qpat_assum `a = _` (fn th => pure_rewrite_tac[th]) >>
     irule ao_source_resolved_operand_exact >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `eval_operand a s = SOME v` by
    (qpat_assum `a = _` (fn th => pure_rewrite_tac[th]) >>
     irule ao_source_resolved_operand_exact >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `V` >> simp[ao_main_observations_def] >> metis_tac[]) >>
  metis_tac[ao_source_prefix_operand_range_sound]
QED

Theorem ao_scalar_success_operand_reads:
  !inst s t.
  MEM inst.inst_opcode
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT] /\
  step_inst_base inst s = OK t ==>
  !a. MEM a inst.inst_operands ==> ?w. eval_operand a s = SOME w
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `MEM inst.inst_opcode _` mp_tac >>
  pure_rewrite_tac[MEM] >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, exec_pure2_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem ao_main_scalar_operand_ranges:
  !ctx fn s0 n k s inst bb V r p t.
  ao_source_prefix ctx fn s0 n k F s /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  s0.vs_inst_idx = 0 /\ s0.vs_prev_bb = NONE /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==> lookup_var x s0 = NONE) /\
  MEM inst (fn_insts fn) /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT] /\
  step_inst_base inst s = OK t /\
  ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  p = ao_pre_flip_inst (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst) ==>
  !a w. MEM a p.inst_operands /\ eval_operand a r = SOME w ==>
    in_range (range_get_range (range_analyze fn) s.vs_current_bb s.vs_inst_idx a) w
Proof
  rpt gen_tac >> strip_tac >>
  `!a. MEM a inst.inst_operands ==> ?w. eval_operand a s = SOME w` by
    metis_tac[ao_scalar_success_operand_reads] >>
  `inst.inst_opcode <> PHI /\ ~is_truthy_inst inst.inst_opcode /\
   inst.inst_opcode <> ISZERO` by gvs[MEM, is_truthy_inst_def] >>
  rpt strip_tac >> irule ao_main_resolved_operand_range >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
