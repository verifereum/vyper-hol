Theory bodyPtrBopInScalarTransport
Ancestors
  bodyPtrBopInLiteralSuffix varsExt fragGasSeqPtr emitHelperProps
  ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
  finite_map list codegenRel contextCodegenRel fragExec exprLoweringProps instIdxIndep

Theorem scalar_success_update:
  MEM opc [EQ; OR; AND; ISZERO] /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u ==>
  ?w. u = update_var out w s
Proof
  strip_tac >> gvs[] >>
  gvs[mk_inst_def, step_inst_base_opcode_eqs] >>
  ALL_TAC
  >>~- ([`exec_pure1 _ _ _ = OK _`],
        drule (cj 1 exec_pure_ok_update) >> simp[] >> metis_tac[]) >>
  drule (cj 2 exec_pure_ok_update) >> simp[] >> metis_tac[]
QED

Theorem scalar_step_prov:
  MEM opc [EQ; OR; AND; ISZERO] ==>
  step_prov PG G (mk_inst id opc ops [out]) u =
  step_prov PG G (mk_inst id opc ops [out]) u1
Proof
  strip_tac >> gvs[step_prov_def, out_prov_def, mk_inst_def]
QED

Theorem scalar_step_taint:
  MEM opc [EQ; OR; AND; ISZERO] /\
  (LENGTH ops = 1 \/ LENGTH ops = 2) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u /\
  step_inst_base (mk_inst id opc ops [out]) s1 = OK u1 ==>
  step_taint (mk_inst id opc ops [out]) s u tn =
  step_taint (mk_inst id opc ops [out]) s1 u1 tn
Proof
  strip_tac >>
  `?w. u = update_var out w s` by metis_tac[scalar_success_update] >>
  `?w1. u1 = update_var out w1 s1` by metis_tac[scalar_success_update] >>
  `MEM opc [EQ; OR; AND; ISZERO; GT]` by gvs[] >>
  simp[membership_scalar_ghost_frame]
QED

Theorem scalar_ptr_check_vars_ext:
  MEM opc [EQ; OR; AND; ISZERO] /\ vars_ext s s1 /\
  ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id opc ops [out]) s1 = OK u1 /\
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops [out]) s ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops [out]) s1
Proof
  strip_tac >>
  drule_all scalar_success_update >> strip_tac >>
  gvs[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
      mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[GSYM mk_inst_def, step_inst_non_invoke] >>
  gvs[update_var_def, vars_ext_def] >>
  rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qexistsl_tac [`b`, `sz`, `x`, `y`] >> simp[] >>
  metis_tac[eval_operand_vars_ext, optionTheory.NOT_NONE_SOME]
QED

Theorem instruction_mk_inst[local]:
  instruction id opc ops outs = mk_inst id opc ops outs
Proof
  simp[mk_inst_def, instruction_component_equality]
QED

Theorem scalar_instruction_transport:
  MEM i.inst_opcode [EQ; OR; AND; ISZERO] /\
  (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
  LENGTH i.inst_outputs = 1 /\ vars_ext s s1 /\ ~ctx_has_dalloca ctx /\
  step_inst_base i s = OK u /\ step_inst_base i s1 = OK u1 /\
  ptr_inst_ok D 0 0 ctx fn G tn i s ==>
  ptr_inst_ok D 0 0 ctx fn G tn i s1 /\
  step_prov PG G i u = step_prov PG G i u1 /\
  step_taint i s u tn = step_taint i s1 u1 tn
Proof
  Cases_on `i` >> simp[LENGTH_EQ_NUM_compute] >> rpt gen_tac >> strip_tac >>
  gvs[instruction_mk_inst] >>
  (conj_tac
   >- (irule scalar_ptr_check_vars_ext >> simp[] >> metis_tac[]) >>
   simp[scalar_step_prov] >>
   irule scalar_step_taint >> simp[] >> metis_tac[])
QED

Theorem vars_ext_idx[local]:
  vars_ext s s1 ==> s.vs_inst_idx = s1.vs_inst_idx /\
    vars_ext (s with vs_inst_idx := n) (s1 with vs_inst_idx := n)
Proof
  simp[vars_ext_def] >> strip_tac >>
  gvs[venom_state_component_equality]
QED

Theorem successful_seq_idx[local]:
  EVERY (\i. ~is_terminator i.inst_opcode) code /\
  (?u. run_inst_seq code s = OK u) ==>
  ?u. run_inst_seq code (s with vs_inst_idx := n) = OK u
Proof
  strip_tac >> simp[run_inst_seq_inst_idx, exec_result_map_def]
QED

Theorem scalar_sequence_check_vars_ext:
  !code s s1 G tn G' tn'.
  EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO] /\
    (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
    LENGTH i.inst_outputs = 1) code /\
  ~ctx_has_dalloca ctx /\ vars_ext s s1 /\
  (?u. run_inst_seq code s = OK u) /\
  inst_seq_ptr D 0 ctx fn PG G tn code s G' tn' ==>
  inst_seq_ptr D 0 ctx fn PG G tn code s1 G' tn'
Proof
  Induct >- simp[inst_seq_ptr_def] >>
  rpt gen_tac >>
  pure_rewrite_tac [EVERY_DEF] >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = OK _` mp_tac >>
  pure_rewrite_tac [run_inst_seq_def] >>
  Cases_on `step_inst_base h s` >> simp[] >> strip_tac >>
  rename1 `step_inst_base h s = OK v` >>
  `vars_ext_result (step_inst_base h s) (step_inst_base h s1)` by
    (irule step_inst_base_vars_ext_state >>
     gvs[is_terminator_def, is_ext_call_op_def]) >>
  qpat_x_assum `vars_ext_result _ _` mp_tac >>
  asm_rewrite_tac[] >> rewrite_tac[vars_ext_result_def] >> strip_tac >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ (_::_) _ _ _` mp_tac >>
  pure_rewrite_tac [inst_seq_ptr_def] >> asm_rewrite_tac[] >> strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn h s1 /\
   step_prov PG G h v = step_prov PG G h t' /\
   step_taint h s v tn = step_taint h s1 t' tn` by
    (irule scalar_instruction_transport >> asm_rewrite_tac[] >>
     qpat_x_assum `(\i. _) h` mp_tac >> simp[]) >>
  asm_rewrite_tac[] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by
    (qpat_x_assum `EVERY _ code` mp_tac >>
     rewrite_tac[EVERY_MEM] >> strip_tac >> rpt strip_tac >>
     first_x_assum drule >> rpt strip_tac >> gvs[is_terminator_def]) >>
  `?u. run_inst_seq code (v with vs_inst_idx := SUC s.vs_inst_idx) = OK u` by
    (irule successful_seq_idx >> metis_tac[]) >>
  `s.vs_inst_idx = s1.vs_inst_idx` by metis_tac[vars_ext_idx] >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >> simp[] >>
  first_x_assum irule >> asm_rewrite_tac[] >>
  qexists_tac `v with vs_inst_idx := SUC s.vs_inst_idx` >>
  simp[] >> metis_tac[vars_ext_idx]
QED

Theorem scalar_inst_seq_ptr_vars_ext:
  EVERY (\i. MEM i.inst_opcode [EQ; OR; AND; ISZERO] /\
    (LENGTH i.inst_operands = 1 \/ LENGTH i.inst_operands = 2) /\
    LENGTH i.inst_outputs = 1) code /\
  ~ctx_has_dalloca ctx /\ vars_ext s s1 /\
  run_inst_seq code s = OK u /\
  inst_seq_ptr D 0 ctx fn PG G tn code s G' tn' ==>
  ?u1. run_inst_seq code s1 = OK u1 /\ vars_ext u u1 /\
       inst_seq_ptr D 0 ctx fn PG G tn code s1 G' tn'
Proof
  strip_tac >>
  `inst_seq_ptr D 0 ctx fn PG G tn code s1 G' tn'` by
    (irule scalar_sequence_check_vars_ext >> asm_rewrite_tac[] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
               ~is_ext_call_op i.inst_opcode) code` by
    (qpat_x_assum `EVERY _ code` mp_tac >>
     rewrite_tac[EVERY_MEM] >> strip_tac >> rpt strip_tac >>
     first_x_assum drule >> rpt strip_tac >>
     gvs[is_terminator_def, is_ext_call_op_def]) >>
  drule_all run_inst_seq_vars_ext >> asm_rewrite_tac[] >>
  rewrite_tac[vars_ext_result_def] >> metis_tac[]
QED
