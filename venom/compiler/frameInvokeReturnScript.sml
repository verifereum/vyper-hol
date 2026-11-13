Theory frameInvokeReturn
Ancestors frameActivationSeparation venomExecSemantics venomState

(* The run witness is from setup_callee, before entry PHI evaluation.
   step_inst uses the same fuel as run_blocks, not its successor. *)
Theorem matched_run_invoke_return:
  callinst.inst_opcode = INVOKE /\ decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops caller = SOME args /\
  setup_callee callee args caller = SOME cs /\
  run_blocks fuel ctx callee cs = IntRet ret send /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller send)) = SOME post ==>
  step_inst fuel ctx callinst caller = OK post /\
  post.vs_allocas = caller.vs_allocas /\
  post.vs_alloca_next = caller.vs_alloca_next
Proof
  strip_tac >> conj_tac
  >- simp[Once step_inst_def] >>
  metis_tac[return_bind_allocation_frame]
QED
