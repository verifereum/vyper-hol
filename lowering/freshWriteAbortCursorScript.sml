Theory freshWriteAbortCursor
Ancestors
  freshWrites createSizeExit opcodeClass[qualified]
  venomExecSemantics venomInst venomState list

Theorem fresh_write_exhalt_step[local]:
  fresh_write_op i.inst_opcode /\ step_inst_base i u = Abort ExHalt_abort v ==>
  i.inst_opcode = ASSERT_UNREACHABLE /\ v = halt_state (set_returndata [] u)
Proof
  simp[fresh_write_op_def] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[opcodeClassTheory.exec_result_helpers_no_halt_abort, AllCaseEqs()] >>
  strip_tac >> simp[]
QED

Theorem fetched_fresh_write_abort_not_oversized:
  writes_fresh sa code /\ MEM i code /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME i /\
  step_inst_base i u = Abort a v /\ MEM fn ctx.ctx_functions /\
  ALL_DISTINCT (FLAT (MAP fn_labels ctx.ctx_functions)) ==>
  ~oversized_create_abort ctx (Abort a v)
Proof
  strip_tac >>
  `fresh_write_op i.inst_opcode` by fs[writes_fresh_def, EVERY_MEM] >>
  Cases_on `a` >> simp[] >>
  drule_all fresh_write_exhalt_step >> strip_tac >> gvs[] >>
  strip_tac >> drule_all oversized_create_abort_at_cursor >> simp[]
QED
