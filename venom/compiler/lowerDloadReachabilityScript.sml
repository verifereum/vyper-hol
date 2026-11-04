(* Completed-call boundaries for the LowerDload reachability proof.
 * These lemmas consume a completed callee execution; they do not assert
 * that ghost frame reachability alone supplies that execution.
 *)
Theory lowerDloadReachability
Ancestors
  contextRawReachable venomExecSemantics o1PassLift o1PassContract
  venomWf venomInst list

Theorem completed_callee_invoke_ok:
  callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME cs /\
  run_blocks fuel ctx callee cs = IntRet ret s_end /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s s_end)) = SOME s' ==>
  step_inst fuel ctx callinst s = OK s'
Proof
  strip_tac >> simp[Once step_inst_def]
QED

Theorem raw_reachable_completed_call:
  raw_reachable vs0 ctx caller callinst s /\
  active_inst caller callinst s /\
  ~is_terminator callinst.inst_opcode /\
  callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME cs /\
  run_blocks fuel ctx callee cs = IntRet ret s_end /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s s_end)) = SOME s' /\
  active_inst caller inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  raw_reachable vs0 ctx caller inst'
    (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all completed_callee_invoke_ok >> strip_tac >>
  irule raw_reachable_next >> goal_assum drule >> simp[] >>
  metis_tac[]
QED

(* The stage shape supplies the uniqueness required when relating
 * active_inst's member block to lookup_block's selected block. *)
Theorem o1_ctx_shape_distinct_block_labels:
  o1_ctx_shape C ==>
  EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks))
    C.ctx_functions
Proof
  simp[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
       fn_labels_def, EVERY_MEM] >> metis_tac[]
QED
