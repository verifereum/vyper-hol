(* Total primitive clamp execution, independent of source validity. *)
Theory abiBoundedLeafExecution
Ancestors
  abiDecoderRange abiDecoderContract abiDecoderClamp abiDecoderUnsignedClamp
  abiDecoderClampedWord abiDecoderTypedCompose abiEncoder emitHelper
  emitHelperProps exprLoweringProps compileEnv venomExecSemantics venomState
  words arithmetic arithmeticProps

Theorem abi_decoder_unsigned_clamp_reverts:
  compile_abi_int_clamp val_op bits F st = ((),st') /\
  eval_operand val_op s = SOME w /\
  w >>> w2n (n2w bits : bytes32) <> 0w /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp_tac bool_ss [compile_abi_int_clamp_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SHR [Lit (n2w bits); val_op] st = (shifted,c1)` >>
  rename1 `emit_op ISZERO [shifted] c1 = (ok,c2)` >>
  `eval_operand (Lit (n2w bits)) s = SOME (n2w bits)` by simp[eval_operand_def] >>
  drule_all emit_op_SHR_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_decoder_unsigned_clamp_total:
  compile_abi_int_clamp val_op bits F st = ((),st') /\
  eval_operand val_op s = SOME w /\ bits <= 256 /\ fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (w2n w < 2 ** bits /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
     (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section /\ inst_extends st st')
Proof
  strip_tac >> Cases_on `w2n w < 2 ** bits`
  >- (disj2_tac >> simp[] >> drule_all abi_decoder_unsigned_clamp_sequence >> simp[]) >>
  disj1_tac >>
  `bits < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `w >>> w2n (n2w bits : bytes32) <> 0w` by
    (once_rewrite_tac[GSYM w2n_eq_0] >>
     asm_simp_tac std_ss [w2n_lsr, w2n_n2w, LESS_MOD] >>
     strip_tac >>
     `0 < 2 ** bits` by simp[] >>
     drule arithmeticTheory.DIVISION >>
     disch_then (qspec_then `w2n (w:bytes32)` mp_tac) >> simp[] >> decide_tac) >>
  drule_all abi_decoder_unsigned_clamp_reverts >> simp[]
QED

Theorem abi_decoder_signed_clamp_reverts:
  compile_abi_int_clamp val_op bits T st = ((),st') /\
  eval_operand val_op s = SOME w /\
  sign_extend (n2w (bits DIV 8 - 1)) w <> w /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp_tac bool_ss [compile_abi_int_clamp_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SIGNEXTEND [Lit (n2w (bits DIV 8 - 1)); val_op] st = (canon,c1)` >>
  rename1 `emit_op EQ [val_op;canon] c1 = (ok,c2)` >>
  `?s1. run_inst_seq (emitted_insts st c1) s = OK s1 /\
    eval_operand canon s1 = SOME (sign_extend (n2w (bits DIV 8 - 1)) w) /\
    same_blocks st c1 /\ fresh_vars_wrt c1 s1 /\
    (!op v. eval_operand op s = SOME v ==> eval_operand op s1 = SOME v) /\
    (!a. a < LENGTH s.vs_memory ==> EL a s1.vs_memory = EL a s.vs_memory) /\
    LENGTH s1.vs_memory = LENGTH s.vs_memory` by
    (qspecl_then [`SIGNEXTEND`, `\(x:bytes32) (y:bytes32). sign_extend x y`]
       (ho_match_mp_tac o BETA_RULE) emit_op_pure2_correct >>
     goal_assum $ drule_at (Pat `emit_op`) >> simp[eval_operand_def] >>
     irule step_SIGNEXTEND >> simp[eval_operand_def]) >>
  `eval_operand val_op s1 = SOME w` by metis_tac[] >>
  drule_all emit_op_EQ_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_decoder_bytes_clamp_reverts:
  compile_abi_bytes_clamp val_op m st = ((),st') /\
  eval_operand val_op s = SOME w /\
  w << w2n (n2w (m * 8) : bytes32) <> 0w /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp_tac bool_ss [compile_abi_bytes_clamp_def, comp_bind_def,
    comp_ignore_bind_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `emit_op SHL [Lit (n2w (8 * m)); val_op] st = (shifted,c1)` >>
  rename1 `emit_op ISZERO [shifted] c1 = (ok,c2)` >>
  `?s1. run_inst_seq (emitted_insts st c1) s = OK s1 /\
    eval_operand shifted s1 = SOME (w << w2n (n2w (8 * m) : bytes32)) /\
    same_blocks st c1 /\ fresh_vars_wrt c1 s1 /\
    (!op v. eval_operand op s = SOME v ==> eval_operand op s1 = SOME v) /\
    (!a. a < LENGTH s.vs_memory ==> EL a s1.vs_memory = EL a s.vs_memory) /\
    LENGTH s1.vs_memory = LENGTH s.vs_memory` by
    (qspecl_then [`SHL`, `\(x:bytes32) (y:bytes32). y << w2n x`]
       (ho_match_mp_tac o BETA_RULE) emit_op_pure2_correct >>
     goal_assum $ drule_at (Pat `emit_op`) >> gvs[] >>
     conj_tac >- simp[eval_operand_def] >>
     qspecl_then [`Lit (n2w (8 * m))`, `val_op`] mp_tac step_SHL >>
     simp[eval_operand_def]) >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_decoder_clamp_total:
  compile_abi_clamp_basetype val_op clamp st = ((),st') /\
  eval_operand val_op s = SOME w /\
  (!bits. clamp = IntClamp bits F ==> bits <= 256) /\
  fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (abi_decoder_clamp_valid clamp w /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
     (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section /\ inst_extends st st')
Proof
  strip_tac >> Cases_on `abi_decoder_clamp_valid clamp w`
  >- (disj2_tac >> simp[] >> drule_all abi_decoder_clamp_sequence >> simp[]) >>
  disj1_tac >> Cases_on `clamp` >>
  gvs[abi_decoder_clamp_valid_def, compile_abi_clamp_basetype_def]
  >- (Cases_on `b` >> gvs[abi_decoder_clamp_valid_def]
      >- (drule_all abi_decoder_signed_clamp_reverts >> simp[]) >>
      drule_all abi_decoder_unsigned_clamp_total >> simp[])
  >- (drule abi_decoder_bytes_clamp_reverts >>
      disch_then (qspecl_then [`w`, `s`] mp_tac) >> simp[]) >>
  `compile_abi_int_clamp val_op 1 F st = ((),st')` by
    simp[compile_abi_int_clamp_def] >>
  drule abi_decoder_unsigned_clamp_total >>
  disch_then (qspecl_then [`w`, `s`] mp_tac) >> simp[]
QED

Theorem abi_decoder_clamped_word_reverts:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\
  ~abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w (B + pos):bytes32) s) /\
  (!bits. clamp = IntClamp bits F ==> bits <= 256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_abi_dec_addr base_op src st = (addr,addr_st)` >>
  rename1 `compile_abi_clamp_basetype val_op clamp c1 = ((),c2)` >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st addr_st) s = OK sa` >>
  `abi_decode_load opc (n2w (B + pos):bytes32) sa =
   abi_decode_load opc (n2w (B + pos):bytes32) s` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts addr_st c1) sa = OK s1` >>
  gvs[] >> drule_all abi_decoder_clamp_total >> simp[] >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends st addr_st` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  `run_inst_seq (emitted_insts st c1) s = OK s1 /\ inst_extends st c1` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`sa`, `addr_st`] >> simp[]) >>
  drule abi_decoder_clamp_shape >> strip_tac >>
  `inst_extends c1 c2` by
    (irule abi_decoder_inst_extends_prefix >> first_assum ACCEPT_TAC) >>
  `run_inst_seq (emitted_insts st c2) s = Abort Revert_abort t` by
    (drule_all run_inst_seq_emit_extend >> gvs[]) >>
  `inst_extends st c2` by metis_tac[inst_extends_trans] >>
  qexists_tac `t` >> irule run_inst_seq_abort_extends >>
  qexists_tac `c2` >> simp[]
QED

Theorem abi_decoder_clamped_word_total:
  compile_abi_decode_to_buf dst src opc base_op hi (DecPrimWord clamp) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  (!bits. clamp = IntClamp bits F ==> bits <= 256) /\ fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w (B + pos):bytes32) s) /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\
     mem_word_at d t.vs_memory = abi_decode_load opc (n2w (B + pos):bytes32) s /\
     abi_decode_frame d 32 s t /\ fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     inst_extends st st')
Proof
  strip_tac >>
  Cases_on `abi_decoder_clamp_valid clamp (abi_decode_load opc (n2w (B + pos):bytes32) s)`
  >- (disj2_tac >> simp[] >> drule_all abi_decoder_clamped_word_sequence >> simp[]) >>
  disj1_tac >> drule_all abi_decoder_clamped_word_reverts >> simp[]
QED
