Theory abiDecodePtrBytesMember
Ancestors
  abiDecodePtrBytesTail abiDecodePtrRead abiDecodePtrPrims
  abiDecoderBytesBound abiDecoderRange emitHelperProps exprLoweringProps
  abiEncoder compileEnv emitHelper venomExecSemantics venomInst venomState
  words arithmetic arithmeticProps list rich_list

Theorem abi_decode_range_success_bounds:
  compile_abi_decode_range_check src e hi st = ((),st') /\
  fresh_vars_wrt st s /\ eval_operand src s = SOME p /\
  eval_operand e s = SOME q /\ eval_operand hi s = SOME h /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  w2n p <= w2n q /\ w2n q <= w2n h
Proof
  simp[compile_abi_decode_range_check_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename1 `emit_op LT [e;src] st = (wrapped,c1)` >>
  rename1 `emit_op ISZERO [wrapped] c1 = (no_wrap,c2)` >>
  rename1 `emit_op GT [e;hi] c2 = (oob,c3)` >>
  rename1 `emit_op ISZERO [oob] c3 = (in_bounds,c4)` >>
  rename1 `emit_op AND [no_wrap;in_bounds] c4 = (ok,c5)` >>
  drule_all emit_op_LT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand e s2 = SOME q /\ eval_operand hi s2 = SOME h` by metis_tac[] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 c4) s3 = OK s4` >>
  `eval_operand no_wrap s4 = SOME (bool_to_word (bool_to_word (w2n q < w2n p) = 0w))` by metis_tac[] >>
  drule_all emit_op_AND_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c4 c5) s4 = OK s5` >>
  imp_res_tac inst_extends_emit_op >>
  imp_res_tac inst_extends_emit_void >>
  ntac 4 (drule_all abi_decode_sequence_chain >> strip_tac) >>
  `run_inst_seq (emitted_insts c5 st') s5 = OK t` by
    metis_tac[run_inst_seq_emit_extend] >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[run_inst_seq_def, mk_inst_def, Once step_inst_base_def,
      AllCaseEqs()]
QED

(* The same checked addition occurs in both head and payload guards. *)
Theorem abi_decode_add_range_success_bounds:
  emit_op ADD [src;len] sa = (e,sb) /\
  compile_abi_decode_range_check src e hi sb = ((),sc) /\
  fresh_vars_wrt sa s /\ eval_operand src s = SOME (p:bytes32) /\
  eval_operand len s = SOME c /\ eval_operand hi s = SOME h /\
  run_inst_seq (emitted_insts sa sc) s = OK t ==>
  w2n p + w2n c <= w2n h
Proof
  strip_tac >> drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK u` >>
  `eval_operand src u = SOME p /\ eval_operand hi u = SOME h` by metis_tac[] >>
  drule compile_abi_decode_range_check_shape >> strip_tac >>
  `run_inst_seq (emitted_insts sb sc) u = OK t` by
    metis_tac[run_inst_seq_emit_extend] >>
  drule_all abi_decode_range_success_bounds >> strip_tac >>
  `w2n p + w2n c < dimword(:256)` by
    (spose_not_then assume_tac >>
     `dimword(:256) <= w2n p + w2n c` by decide_tac >>
     drule w2n_add_overflow >> decide_tac) >>
  gvs[w2n_add_2]
QED

Theorem abi_decode_bytes_head_success_bound:
  abi_decode_bytes_head src hi sa = (head,sb) /\ hi <> Lit 0w /\
  fresh_vars_wrt sa s /\ eval_operand src s = SOME p /\
  eval_operand hi s = SOME h /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  w2n p + 32 <= w2n h
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_head _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_head_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_range_success_bounds >> simp[dimword_def]
QED

Theorem abi_decode_bytes_payload_success_bound:
  abi_decode_bytes_payload_guard head len hi sa = ((),sb) /\ hi <> Lit 0w /\
  fresh_vars_wrt sa s /\ eval_operand head s = SOME p /\
  eval_operand len s = SOME c /\ eval_operand hi s = SOME h /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  w2n p + w2n c <= w2n h
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_bytes_payload_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bytes_payload_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all abi_decode_add_range_success_bounds >> simp[]
QED
