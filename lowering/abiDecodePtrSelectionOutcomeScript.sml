Theory abiDecodePtrSelectionOutcome
Ancestors
  abiDecodePtrHead abiDecoderGuard abiDecoderRange arithmeticProps
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState words list

(* Defined scalar operands make the underflow guard either succeed or revert. *)
Theorem abi_decode_ge_guard_outcome:
  abi_decode_ge_guard a b sa = ((),sb) /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  fresh_vars_wrt sa s ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u \/
      run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort u
Proof
  simp[abi_decode_ge_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op LT [a;b] sa = (underflow,c1)` >>
  rename1 `emit_op ISZERO [underflow] c1 = (ok,c2)` >>
  drule_all emit_op_LT_correct >> strip_tac >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac emit_void_extends >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  `c2.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa c2` by
    fs[inst_extends_def] >>
  drule_all assert_chain >> strip_tac >> metis_tac[]
QED
