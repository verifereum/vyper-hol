Theory abiDecodePtrRejectCapacity
Ancestors
  abiDecodePtrRejectChecks abiDecodePtrOverCapacity abiDecoderBytesBound abiDecoderBytesPrefix
  abiDecoderBytesPhases abiDecoderBytesFrame abiDecoderGuards abiDecoderVarSequence
  abiDecoderReentryPointer abiDecoderComposition abiDecoderRange abiDecoderContract
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper fragExec
  venomExecSemantics venomExecProofs venomState venomInst words arithmetic list rich_list

Theorem abi_decode_reject_witness_suffix:
  abi_decode_reject_witness insts s u ==>
  abi_decode_reject_witness (insts ++ suffix) s u
Proof
  rw[abi_decode_reject_witness_def] >>
  qexistsl_tac [`pre`, `bad`, `post ++ suffix`, `r`] >> simp[APPEND_ASSOC]
QED

Theorem abi_decode_emit_reject_suffix:
  inst_extends st mid /\ inst_extends mid last /\
  abi_decode_reject_witness (emitted_insts st mid) s u ==>
  abi_decode_reject_witness (emitted_insts st last) s u
Proof
  strip_tac >>
  `emitted_insts st last = emitted_insts st mid ++ emitted_insts mid last` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  simp[] >> irule abi_decode_reject_witness_suffix >> simp[]
QED

Theorem abi_decode_count_guard_reject_witness:
  abi_decode_count_guard opc src limit st = (count_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME p /\
  limit < dimword (:256) /\ limit < w2n (abi_decode_load opc p s) /\
  fresh_vars_wrt st s ==>
  ?t. abi_decode_reject_witness (emitted_insts st st') s t
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [count_op; Lit (n2w limit)] c1 = (too_many,c2)` >>
  rename1 `emit_op ISZERO [too_many] c2 = (ok,c3)` >>
  rename1 `emit_void ASSERT [ok] c3 = ((),last)` >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit (n2w limit)) s1 = SOME (n2w limit)` by simp[eval_operand_def] >>
  drule_all emit_op_GT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[w2n_n2w, bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  gvs[bool_to_word_def] >>
  drule_all abi_decode_ASSERT_reject_witness >>
  disch_then assume_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends c1 last /\ inst_extends c2 last` by metis_tac[inst_extends_trans] >>
  qexists_tac `revert_state (set_returndata [] s3)` >>
  irule abi_decode_emit_reject_chain >> qexistsl_tac [`c1`, `s1`] >>
  simp[] >> conj_tac >- suspend "read_code" >>
  irule abi_decode_emit_op_reject_chain >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  qexists_tac `s2` >> simp[abi_decoder_reentry_opcode_def] >>
  irule abi_decode_emit_op_reject_chain >>
  goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
  qexists_tac `s3` >> simp[abi_decoder_reentry_opcode_def]
QED

Resume abi_decode_count_guard_reject_witness[read_code]:
  Cases_on `opc = MLOAD` >>
  gvs[abi_decode_source_opcode_def] >>
  qpat_x_assum `emit_op _ [src] st = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >>
  simp[mk_inst_def, abi_decoder_reentry_opcode_def]
QED

Finalise abi_decode_count_guard_reject_witness

Theorem abi_decode_bytes_capacity_reject_witness:
  compile_abi_decode_to_buf dst pos opc base_op hi (DecBytestring n) st = ((),st') /\
  abi_decode_source_opcode opc /\ hi <> Lit 0w /\
  eval_operand pos s = SOME (n2w p) /\
  eval_operand base_op s = SOME (n2w b) /\
  eval_operand hi s = SOME (n2w h) /\
  p+32 <= h /\ h < dimword (:256) /\ n < dimword (:256) /\
  n < w2n (abi_decode_load opc (n2w (b+p) : bytes32) s) /\
  fresh_vars_wrt st s ==>
  ?t. abi_decode_reject_witness (emitted_insts st st') s t
Proof
  strip_tac >>
  drule_all abi_decoder_bytes_reentry_code >> strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bytes_position_phases] >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `abi_decode_bytes_head pos hi st = (head,sh)` >>
  rename1 `compile_abi_dec_addr base_op pos sh = (addr,sa)` >>
  rename1 `abi_decode_count_guard opc addr n sa = (cnt,sc)` >>
  rename1 `abi_decode_bytes_payload_guard _ _ _ sc = ((),sd)` >>
  drule_all abi_decode_bytes_head_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st sh) s = OK s1` >>
  `eval_operand base_op s1 = SOME (n2w b) /\
   eval_operand pos s1 = SOME (n2w p)` by metis_tac[] >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sh sa) s1 = OK s2` >>
  `n < w2n (abi_decode_load opc (n2w (b+p) : bytes32) s2)` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  drule_all abi_decode_count_guard_reject_witness >> strip_tac >>
  `inst_extends sh sa` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  drule abi_decode_count_guard_shape >> strip_tac >>
  `inst_extends sc st'` by suspend "suffix" >>
  `run_inst_seq (emitted_insts st sa) s = OK s2 /\ inst_extends st sa` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `sh`] >> simp[]) >>
  `inst_extends sa st'` by metis_tac[inst_extends_trans] >>
  `emitted_insts st st' = emitted_insts st sa ++ emitted_insts sa st'` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  qexists_tac `t` >> irule abi_decode_emit_reject_chain >>
  qexistsl_tac [`sa`, `s2`] >> simp[] >>
  conj_tac >- metis_tac[EVERY_APPEND] >>
  irule abi_decode_emit_reject_suffix >> qexists_tac `sc` >> simp[]
QED

Resume abi_decode_bytes_capacity_reject_witness[suffix]:
  drule abi_decode_bytes_payload_guard_shape >> strip_tac >>
  Cases_on `base_op = Lit 0w` >> gvs[]
  >- (drule inst_extends_emit_void >> metis_tac[inst_extends_trans]) >>
  drule abi_decode_bytes_runtime_tail_shape >> metis_tac[inst_extends_trans]
QED

Finalise abi_decode_bytes_capacity_reject_witness
