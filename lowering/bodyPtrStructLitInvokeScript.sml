(* INVOKE transports the actual callee representation, not a guessed ghost. *)
Theory bodyPtrStructLitInvoke
Ancestors ptrSafeRun venomExecSemantics venomInstProofs1 venomState
  robustCopyTransportPtr valueEncoding

Theorem invoke_return_memory:
 !fuel ctx inst s nm ops callee args cs ir sr sf.
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  run_blocks fuel ctx callee cs = IntRet ir sr /\
  step_inst fuel ctx inst s = OK sf ==>
  sf.vs_memory = sr.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[Once step_inst_def, AllCaseEqs()] >> strip_tac >>
  mp_tac (Q.ISPEC `\s:venom_state. s.vs_memory` bind_outputs_preserves) >>
  simp[update_var_def] >> disch_then drule >>
  Cases_on `ir.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem invoke_return_memory_taint:
 !fuel ctx inst s nm ops callee args cs PG G tn.
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  (SND (ghost_step fuel ctx PG G tn inst s)).t_mem =
  (SND (ghost_blocks fuel ctx callee (MAP (op_prov G) ops)
     FEMPTY (tn with t_var := FEMPTY) cs)).t_mem
Proof
  rpt gen_tac >> strip_tac >> simp[Once ghost_step_def]
QED

Theorem invoke_robust_return_transport:
 !fuel ctx inst s nm ops callee args cs ir sr sf PG G tn tv v base.
  inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  run_blocks fuel ctx callee cs = IntRet ir sr /\
  step_inst fuel ctx inst s = OK sf /\
  (!mem. mem_agree_outside
    (SND (ghost_blocks fuel ctx callee (MAP (op_prov G) ops)
       FEMPTY (tn with t_var := FEMPTY) cs)).t_mem sr.vs_memory mem ==>
    val_in_memory tv v base mem) ==>
  !mem. mem_agree_outside (SND (ghost_step fuel ctx PG G tn inst s)).t_mem
    sf.vs_memory mem ==> val_in_memory tv v base mem
Proof
  rpt gen_tac >> strip_tac >>
  drule_all invoke_return_memory >> strip_tac >>
  drule_all invoke_return_memory_taint >> strip_tac >> simp[]
QED
