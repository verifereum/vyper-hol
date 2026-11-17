(* Semantic run existence for the unsigned clamp, including reversion. *)
Theory bodyPtrTypeBuiltinsUintClampSemantics
Ancestors bodyPtrTypeBuiltinsUnsignedSemantics builtinIntClamp
  exprLoweringProps exprLowering emitHelperProps compileEnv venomExecSemantics
  venomState venomInst venomInstProofs fragExec words vyperValue






Theorem uint_clamp_exact:
  compile_int_clamp F b v sa = (r,sb) /\
  eval_operand v ss = SOME x /\ fresh_vars_wrt sa ss /\
  0 < b /\ b <= 256 ==>
  if within_int_bound (Unsigned b) (&(w2n x)) then
    ?sf. run_inst_seq (emitted_insts sa sb) ss = OK sf /\
      eval_operand r sf = SOME x /\ fresh_vars_wrt sb sf /\
      sf.vs_memory = ss.vs_memory /\ sf.vs_allocas = ss.vs_allocas /\
      (!p w. eval_operand p ss = SOME w ==> eval_operand p sf = SOME w)
  else ?sf. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort sf
Proof
  strip_tac >> drule_all exprSimConvertFromBytesTheory.dynamic_uint_clamp_raw_exact >> simp[exprSimConvertFromBytesTheory.dynamic_uint_clamp_test]
QED
