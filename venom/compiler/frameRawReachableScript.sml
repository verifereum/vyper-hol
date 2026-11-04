Theory frameRawReachable
Ancestors
  contextRawReachable ptrDiscipline venomExecSemantics venomInst contextCodegenRel

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

(* The block lookup is explicit: active_inst alone uses membership, which
   need not identify the block returned by lookup_block without uniqueness. *)
Theorem run_blocks_immediate_return:
  !ctx fn cs bb sp s1 rinst fuel ret se.
  lookup_block cs.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis cs bb.bb_instructions = OK sp /\
  s1 = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
  get_instruction bb s1.vs_inst_idx = SOME rinst /\
  step_inst fuel ctx rinst s1 = IntRet ret se ==>
  run_blocks (SUC fuel) ctx fn cs = IntRet ret se
Proof
  rpt strip_tac >> gvs[] >>
  `exec_block fuel ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = IntRet ret se` by
    simp[Once exec_block_def] >>
  simp[Once run_blocks_unfold, run_block_def]
QED
