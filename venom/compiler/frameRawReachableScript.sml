Theory frameRawReachable
Ancestors
  contextRawReachable ptrDiscipline venomExecSemantics venomInst

Theorem raw_reachable_completed_invoke:
  !vs ctx caller callinst s nm ops callee args cs fuel ret se sr inst'.
  raw_reachable vs ctx caller callinst s /\ active_inst caller callinst s /\
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  run_blocks fuel ctx callee cs = IntRet ret se /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se)) = SOME sr /\
  active_inst caller inst' (sr with vs_inst_idx := SUC s.vs_inst_idx) ==>
  raw_reachable vs ctx caller inst' (sr with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx callinst s = OK sr` by
    simp[Once step_inst_def] >>
  irule raw_reachable_next >>
  conj_tac >- simp[] >>
  qexistsl [`fuel`,`callinst`] >> simp[is_terminator_def]
QED
