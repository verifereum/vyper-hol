(* The INVOKE boundary, with a single fuel shared by the concrete callee
   run, its pointer check, its ghost and its GAS count.  No S1 erasure is
   used: the caller check contains the actual callee pointer execution. *)
Theory bodyPtrIntCallInvokeBridge
Ancestors
  fragGasPathPtr ptrSafeRun ptrDiscipline gasCount fragExec
  venomExecSemantics venomExecProofs venomInstProofs venomInst venomState
  finite_map list

Theorem intcall_invoke_counted_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME cs /\
  ptr_inst_ok D lo fuel ctx fn G tn inst s /\
  ptr_safe_blocks D lo fuel ctx callee (MAP (op_prov G) ops)
    FEMPTY (tn with t_var := FEMPTY) cs /\
  run_blocks fuel ctx callee cs = IntRet ret cs' /\
  bind_outputs inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s cs')) = SOME t /\
  ~t.vs_halted /\
  ghost_blocks fuel ctx callee (MAP (op_prov G) ops)
    FEMPTY (tn with t_var := FEMPTY) cs = (CG,ctn) ==>
  gas_path_ptr_edge D lo ctx fn PG G tn s
    (gas_count_blocks fuel ctx callee cs)
    (DRESTRICT G (COMPL (set inst.inst_outputs)))
    (ctn with t_var := DRESTRICT tn.t_var (COMPL (set inst.inst_outputs)))
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  simp[gas_path_ptr_edge_def] >>
  qexists_tac `fuel` >>
  simp[Once step_inst_def, gas_count_step_def, ptr_safe_step_def,
       ghost_step_def, is_terminator_def]
QED

(* An escaping callee halt or abort keeps the caller ghost: ghost_step
   is used only when execution resumes after the INVOKE. *)
Theorem intcall_invoke_exit_counted_ptr:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME cs /\
  ptr_inst_ok D lo fuel ctx fn G tn inst s /\
  ptr_safe_blocks D lo fuel ctx callee (MAP (op_prov G) ops)
    FEMPTY (tn with t_var := FEMPTY) cs /\
  run_blocks fuel ctx callee cs = r /\
  ((?t. r = Halt t) \/ (?a t. r = Abort a t)) ==>
  gas_path_ptr_edge D lo ctx fn PG G tn s
    (gas_count_blocks fuel ctx callee cs) G tn r
Proof
  strip_tac >>
  `step_inst fuel ctx inst s = r` by
    (gvs[] >> simp[Once step_inst_def]) >>
  `exit_result r` by gvs[exit_result_def] >>
  simp[gas_path_ptr_edge_def] >>
  qexists_tac `fuel` >>
  simp[gas_count_step_def, ptr_safe_step_def, exit_result_def]
QED
