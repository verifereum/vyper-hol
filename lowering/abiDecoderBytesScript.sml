(* Bytestring decoder execution; sentinel and bounded source paths are separate. *)
Theory abiDecoderBytes
Ancestors
  abiDecoderGuards abiDecoderCopy abiDecoderComposition abiDecoderContract abiDecoderBytesBound
  abiDecoderGuard abiCanonicalBytes abiEncoder emitHelperProps exprLoweringProps compileEnv
  emitHelper valueEncoding venomExecSemantics venomState words

Definition abi_decode_bytes_copy_size_def:
  abi_decode_bytes_copy_size n = 32 + 32 * ((n + 31) DIV 32)
End

Theorem abi_decode_bytes_phases:
  abi_decode_source_opcode opc ==>
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) =
    do count_op <- abi_decode_count_guard opc src n;
       abi_decode_bytes_end_guard src count_op hi;
       emit_void (abi_decode_copy_opcode opc)
         [dst; src; Lit (n2w (abi_decode_bytes_copy_size n))]
    od
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >> Cases_on `hi = Lit 0w` >>
  simp[FUN_EQ_THM, compile_abi_decode_to_buf_def, abi_decode_count_guard_def,
       abi_decode_bytes_end_guard_def, abi_decode_bytes_end_def, abi_decode_le_guard_def,
       abi_decode_bytes_copy_size_def, abi_decode_copy_opcode_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_bytes_sentinel:
  abi_decode_source_opcode opc ==>
  compile_abi_decode_to_buf dst src opc (Lit 0w) (DecBytestring n) =
    do count_op <- abi_decode_count_guard opc src n;
       emit_void (abi_decode_copy_opcode opc)
         [dst; src; Lit (n2w (abi_decode_bytes_copy_size n))]
    od
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >>
  simp[FUN_EQ_THM, compile_abi_decode_to_buf_def, abi_decode_count_guard_def,
       abi_decode_bytes_copy_size_def, abi_decode_copy_opcode_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_bytes_sentinel_sequence:
  compile_abi_decode_to_buf dst src opc (Lit 0w) (DecBytestring n) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME p /\
  eval_operand dst s = SOME d /\ abi_decode_load opc p s = n2w cnt /\
  cnt <= n /\ n < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at (w2n d) (abi_decode_bytes_copy_size n) t.vs_memory =
      mem_bytes_at (w2n p) (abi_decode_bytes_copy_size n) (abi_decode_source opc s) /\
    abi_decode_frame (w2n d) (abi_decode_bytes_copy_size n) s t /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_sentinel, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_count_guard opc src n st = (count_op,c1)` >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME p /\ eval_operand dst s1 = SOME d` by metis_tac[] >>
  `eval_operand (Lit (n2w (abi_decode_bytes_copy_size n))) s1 =
    SOME (n2w (abi_decode_bytes_copy_size n))` by simp[eval_operand_def] >>
  drule_all abi_decode_copy_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `fresh_vars_wrt st' t` by (drule_all abi_decode_copy_fresh >> simp[]) >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >>
  gvs[w2n_n2w, abi_decode_copy_bytes_def, mem_bytes_at_def,
      abi_decode_source_def, abi_decode_frame_def] >> metis_tac[]
QED

Theorem abi_decode_bytes_sequence:
  compile_abi_decode_to_buf dst src opc hi (DecBytestring n) st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ abi_decode_load opc (n2w sb : bytes32) s = n2w cnt /\
  cnt <= n /\ n < dimword (:256) /\ sb < dimword (:256) /\ d < dimword (:256) /\
  abi_decode_bytes_copy_size n < dimword (:256) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     sb + 32 + cnt <= h /\ h < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at d (abi_decode_bytes_copy_size n) t.vs_memory =
      mem_bytes_at sb (abi_decode_bytes_copy_size n) (abi_decode_source opc s) /\
    abi_decode_frame d (abi_decode_bytes_copy_size n) s t /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  Cases_on `hi = Lit 0w`
  >- (rw[] >> drule_all abi_decode_bytes_sentinel_sequence >> gvs[w2n_n2w]) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_phases, comp_bind_def,
                       comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_count_guard opc src n st = (count_op,c1)` >>
  rename1 `abi_decode_bytes_end_guard src count_op hi c1 = (u,c2)` >>
  Cases_on `u` >>
  rename1 `eval_operand hi s = SOME (n2w h)` >>
  drule_all abi_decode_count_guard_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb)` by metis_tac[] >>
  `eval_operand hi s1 = SOME (n2w h)` by metis_tac[] >>
  mp_tac (Q.INST [`st` |-> `c1`, `st'` |-> `c2`, `s` |-> `s1`,
    `len` |-> `count_op`] abi_decode_bytes_end_guard_sequence) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> qexists_tac `h` >> simp[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand src s2 = SOME (n2w sb) /\ eval_operand dst s2 = SOME (n2w d)` by
    metis_tac[] >>
  `eval_operand (Lit (n2w (abi_decode_bytes_copy_size n))) s2 =
    SOME (n2w (abi_decode_bytes_copy_size n))` by simp[eval_operand_def] >>
  drule_all abi_decode_copy_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  `fresh_vars_wrt st' t` by (drule_all abi_decode_copy_fresh >> simp[]) >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  drule inst_extends_emit_void >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >> qexists_tac `t` >>
  gvs[w2n_n2w, abi_decode_copy_bytes_def, mem_bytes_at_def,
      abi_decode_source_def, abi_decode_frame_def] >> metis_tac[]
QED
