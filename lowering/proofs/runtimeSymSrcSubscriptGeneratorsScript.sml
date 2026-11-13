Theory runtimeSymSrcSubscriptGenerators
Ancestors
  runtimeSymSrcSubscriptPrimitives runtimeSymSrcArraySubscript
  runtimeSymSrcContext runtimeSymSrcInterfaces

Theorem runtime_sym_array_subscript:
  !ce loc bop idx dyn count ws sz signed s out s'.
    runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    ~is_label_operand bop /\ ~is_label_operand idx /\
    compile_array_subscript bop idx dyn count ws sz signed
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) s = (out,s') ==>
    EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand out
Proof
  rpt gen_tac >> strip_tac >>
  `!p t v t'. EVERY runtime_sym_inst (state_insts t) /\
    ~is_label_operand p /\
    compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc p t = (v,t') ==>
    EVERY runtime_sym_inst (state_insts t') /\ ~is_label_operand v` by
    (rpt gen_tac >> strip_tac >> irule runtime_sym_ptr_load >>
     gvs[runtime_sym_env_def] >> metis_tac[]) >>
  drule runtime_sym_array_subscript_loader >>
  disch_then drule_all >> simp[]
QED
