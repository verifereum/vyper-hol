Theory bodyFullIfExpWidenAlloc
Ancestors
  bodyPtrIfExpAllocOrdered bodyPtrIfExpAllocSource bodyPtrIfExpAllocCompiler
  fragGasSeqPtr fragGasOriginPtr fragExecPtr ptrSafetyTransport
  instMemFrontier unitTransformDefs memSafeRun ptrSafeRun ptrDiscipline
  venomInst venomState venomExecSemantics venomInstProofs finite_map
  exprLoweringProps contextCodegenRel codegenRel

Theorem ifexp_alloca_origin_ptr_edge:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  lo <= s.vs_alloca_next /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ALLOCA [Lit n] [p]) /\
  step_inst_base (mk_inst id ALLOCA [Lit n] [p]) s = OK u ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst id ALLOCA [Lit n] [p]) u,
     step_taint (mk_inst id ALLOCA [Lit n] [p]) s u tn)
Proof
  strip_tac >>
  irule (SRULE [instruction_accessors, is_terminator_def]
    (Q.INST [`i` |-> `mk_inst id ALLOCA [Lit n] [p]`]
      straight_line_origin_ptr_edge)) >> simp[] >>
  simp[inst_mem_below_frontier_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, inst_dload_in_section_def,
       mk_inst_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       op_taint_def, step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_alloca_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED
