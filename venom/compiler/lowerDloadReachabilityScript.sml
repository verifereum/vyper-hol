(* Completed-call boundaries for the LowerDload reachability proof.
 * These lemmas consume a completed callee execution; they do not assert
 * that ghost frame reachability alone supplies that execution.
 *)
Theory lowerDloadReachability
Ancestors
  contextRawReachable venomExecSemantics o1PassLift o1PassContract
  venomWf venomInst list ptrDiscipline

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

(* Saved caller prefixes certify each live frame's origin independently
 * of block-label uniqueness or any completed execution. *)
Inductive ld_stack_origin:
[~base:]
  (!vs C name fn lbl.
    C.ctx_entry = SOME name /\
    lookup_function name C.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl ==>
    ld_stack_origin vs C [] fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))
[~push:]
  (!vs C stk f caller0 nm ops callee args cs.
    ld_stack_origin vs C stk f.cf_fn caller0 /\
    frame_reach C f.cf_fn caller0 f.cf_inst f.cf_state /\
    f.cf_inst.inst_opcode = INVOKE /\
    decode_invoke f.cf_inst = SOME (nm, ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops f.cf_state = SOME args /\
    setup_callee callee args f.cf_state = SOME cs ==>
    ld_stack_origin vs C (f::stk) callee cs)
End

Theorem ld_stack_origin_cons:
  ld_stack_origin vs C (f::stk) callee cs <=>
  ?caller0 nm ops args.
    ld_stack_origin vs C stk f.cf_fn caller0 /\
    frame_reach C f.cf_fn caller0 f.cf_inst f.cf_state /\
    f.cf_inst.inst_opcode = INVOKE /\
    decode_invoke f.cf_inst = SOME (nm, ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops f.cf_state = SOME args /\
    setup_callee callee args f.cf_state = SOME cs
Proof
  simp[SimpLHS, Once ld_stack_origin_cases]
QED

Theorem ld_stack_origin_member:
  !vs C stk fn s0. ld_stack_origin vs C stk fn s0 ==>
    MEM fn C.ctx_functions
Proof
  ho_match_mp_tac ld_stack_origin_ind >> rpt strip_tac >>
  metis_tac[lookup_function_MEM]
QED

Theorem ld_stack_origin_raw_reachable:
  !vs C stk fn s0. ld_stack_origin vs C stk fn s0 ==>
    !inst s. frame_reach C fn s0 inst s ==>
      raw_reachable vs C fn inst s
Proof
  ho_match_mp_tac ld_stack_origin_ind >> rpt conj_tac >> rpt strip_tac
  >- (irule frame_reach_entry >> metis_tac[])
  >> irule frame_reach_callee >>
  metis_tac[frame_reach_active]
QED
