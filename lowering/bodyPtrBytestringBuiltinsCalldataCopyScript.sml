Theory bodyPtrBytestringBuiltinsCalldataCopy
Ancestors
  fragExecPtr bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics
  venomInst venomState finite_map codegenRel memLocDefs contextCodegenRel

Theorem ptr_inst_ok_calldatacopy_operand:
  !D ctx fn G tn s id dst src count n fuel.
    eval_operand count s = SOME n /\ op_taint tn count = {} /\
    op_taint tn src = {} /\ ptr_covers G tn dst s (w2n n) /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn
      (mk_inst id CALLDATACOPY [Var dst; src; count] []) s
Proof
  rpt strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, sized_source_write_range_def,
       eval_operand_def, mem_write_ops_def] >>
  rpt conj_tac
  >- (Cases_on `eval_operand src s` >> simp[] >> rpt strip_tac >> gvs[])
  >- (metis_tac[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, combinTheory.K_THM,
                   opcode_case_def] >>
  Cases_on `eval_operand src s` >>
  simp[eval_operand_def, write_memory_with_expansion_def]
QED

Theorem calldatacopy_step:
  !dst s d src a count n fuel ctx id.
  eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
  eval_operand count s = SOME n ==>
  step_inst fuel ctx (mk_inst id CALLDATACOPY [dst; src; count] []) s =
    OK (write_memory_with_expansion (w2n d)
      (TAKE (w2n n) (DROP (w2n a) s.vs_call_ctx.cc_calldata ++
                     REPLICATE (w2n n) 0w)) s)
Proof
  rpt strip_tac >> simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def]
QED

Theorem calldatacopy_step_prov:
  !PG G id dst src count s'.
    step_prov PG G (mk_inst id CALLDATACOPY [dst; src; count] []) s' = G
Proof
  simp[step_prov_def, set_prov_def, mk_inst_def, DRESTRICT_UNIV]
QED

Theorem calldatacopy_step_taint:
  !dst src count s d a n id tn bytes.
    eval_operand dst s = SOME d /\ eval_operand src s = SOME a /\
    eval_operand count s = SOME n ==>
    step_taint (mk_inst id CALLDATACOPY [dst; src; count] []) s
      (write_memory_with_expansion (w2n d) bytes s) tn =
    tn with t_mem := tn.t_mem DIFF {i | w2n d <= i /\ i < w2n d + w2n n}
Proof
  rpt strip_tac >>
  simp[step_taint_def, mk_inst_def, set_var_taint_def, DRESTRICT_UNIV,
       store_taint_def, adopt_reset_def, imm_taint_def, mem_taint_def,
       step_writes_def, source_memory_write_ranges_def,
       sized_source_write_range_def, written_taint_def, range_bytes_def,
       new_site_bytes_def, write_memory_with_expansion_def,
       FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[taint_component_equality]
QED
