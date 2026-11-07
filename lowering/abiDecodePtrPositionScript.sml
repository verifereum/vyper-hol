(* Value-only boundary for a dynamic member's relative position. *)
Theory abiDecodePtrPosition
Ancestors
  abiDecoderGuard abiEncoderWindowSequence freshWrites emitHelperProps
  exprLoweringProps emitHelper compileEnv venomExecSemantics venomState
  words list finite_map

Theorem abi_decode_ge_guard_straight_fresh:
  straight_fresh (abi_decode_ge_guard a b)
Proof
  simp[abi_decode_ge_guard_def] >>
  irule straight_fresh_bind >>
  simp[straight_fresh_emit_op, fresh_write_op_def] >> gen_tac >>
  irule straight_fresh_bind >>
  simp[straight_fresh_emit_op, straight_fresh_emit_void, fresh_write_op_def]
QED

Theorem abi_decode_position_suffix_result:
  emit_op ADD [pos;offset] sa = (v,mid) /\
  (if hi = Lit 0w then sb = mid
   else abi_decode_ge_guard v pos mid = ((),sb)) /\
  eval_operand pos s = SOME z /\ eval_operand offset s = SOME w /\
  run_inst_seq (emitted_insts sa sb) s = OK u ==>
  ?out. v = Var out /\ not_fresh_at sb out /\
    lookup_var out u = SOME (z+w)
Proof
  strip_tac >> drule_all window_emit_add_pure >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  Cases_on `hi = Lit 0w`
  >- (gvs[window_pure_seq_def, window_seq_def, eval_operand_def] >> metis_tac[]) >>
  `abi_decode_ge_guard v pos mid = ((),sb)` by gvs[] >>
  mp_tac (Q.INST [`a` |-> `v`, `b` |-> `pos`] abi_decode_ge_guard_straight_fresh) >>
  simp_tac bool_ss [straight_fresh_def] >>
  disch_then drule >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa mid ++ emitted_insts mid sb` by
    (irule emitted_insts_append >> fs[window_pure_seq_def, window_seq_def, inst_extends_def]) >>
  `run_inst_seq (emitted_insts mid sb) t = OK u` by
    metis_tac[run_inst_seq_append, window_pure_seq_def, window_seq_def] >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  gvs[eval_operand_def, lookup_var_def] >>
  fs[not_fresh_at_def]
QED
