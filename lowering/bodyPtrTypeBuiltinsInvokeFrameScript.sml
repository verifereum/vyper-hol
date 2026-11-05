Theory bodyPtrTypeBuiltinsInvokeFrame
Ancestors
  ptrSafeRun venomExecSemantics fragGasPathPtr fragExec venomInst finite_map list

Theorem ghost_step_invoke_prov_cases:
  inst.inst_opcode = INVOKE ==>
  FST (ghost_step fuel ctx PG G tn inst s) = G \/
  FST (ghost_step fuel ctx PG G tn inst s) =
    DRESTRICT G (COMPL (set inst.inst_outputs))
Proof
  strip_tac >> simp[Once ghost_step_def] >>
  Cases_on `decode_invoke inst` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >> simp[] >>
  Cases_on `eval_operands x1 s` >> simp[] >>
  Cases_on `setup_callee x x' s` >> simp[Once ghost_step_def]
QED

Theorem ghost_step_invoke_prov_frame:
  inst.inst_opcode = INVOKE /\ ~MEM x inst.inst_outputs ==>
  FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) x = FLOOKUP G x
Proof
  strip_tac >>
  `FLOOKUP (DRESTRICT G (COMPL (set inst.inst_outputs))) x = FLOOKUP G x`
    by simp[FLOOKUP_DRESTRICT] >>
  metis_tac[ghost_step_invoke_prov_cases]
QED

Theorem ghost_step_invoke_prov_none:
  inst.inst_opcode = INVOKE /\ FLOOKUP G x = NONE ==>
  FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) x = NONE
Proof
  strip_tac >>
  `FLOOKUP (DRESTRICT G (COMPL (set inst.inst_outputs))) x = FLOOKUP G x`
    by simp[FLOOKUP_DRESTRICT] >>
  metis_tac[ghost_step_invoke_prov_cases]
QED

Theorem ghost_step_invoke_output_none:
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  MEM x inst.inst_outputs ==>
  FLOOKUP (FST (ghost_step fuel ctx PG G tn inst s)) x = NONE
Proof
  strip_tac >> drule_all ghost_step_invoke >>
  simp[FLOOKUP_DRESTRICT]
QED

Theorem ghost_step_invoke_OK_prov:
  inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst s = OK t ==>
  FST (ghost_step fuel ctx PG G tn inst s) =
    DRESTRICT G (COMPL (set inst.inst_outputs))
Proof
  strip_tac >>
  Cases_on `decode_invoke inst` >>
  gvs[Once step_inst_def] >>
  PairCases_on `x` >> gvs[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >> gvs[] >>
  Cases_on `eval_operands x1 s` >> gvs[] >>
  Cases_on `setup_callee x x' s` >> gvs[] >>
  simp[Once ghost_step_def]
QED

Theorem gas_path_ptr_edge_invoke_prov:
  gas_path_ptr_edge D lo ctx fn PG G tn s n G' tn' (OK t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE ==>
  G' = DRESTRICT G (COMPL (set inst.inst_outputs))
Proof
  strip_tac >>
  gvs[gas_path_ptr_edge_def, is_terminator_def, exit_result_def]
  >- metis_tac[ghost_step_invoke_OK_prov, pairTheory.FST] >>
  qpat_x_assum `OK t = _` (assume_tac o SYM) >>
  gvs[exit_result_def]
QED
