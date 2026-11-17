(* Total guarded navigation over arbitrary bounded ABI memory. *)
Theory abiDecoderNavigationTotal
Ancestors
  abiDecoderAbortReentry abiDecoderReentryPointer abiDecoderReentry
  abiDecoderVarExtend abiBoundedBytesExecution abiDecoderMemberBound
  abiDecoderGuard abiDecoderGuards abiDecoderContract abiDecoderRange
  abiEncoder emitHelper emitHelperProps exprLoweringProps compileEnv
  venomExecSemantics venomState words arithmetic

Theorem abi_decode_ge_guard_reverts:
  abi_decode_ge_guard a b st = ((),st') /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  w2n va < w2n vb /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  simp[abi_decode_ge_guard_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op LT [a;b] st = (oob,c1)` >>
  rename1 `emit_op ISZERO [oob] c1 = (ok,c2)` >>
  drule_all emit_op_LT_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  gvs[bool_to_word_def] >>
  drule_all emit_op_ISZERO_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[bool_to_word_def] >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all run_inst_seq_emit_extend >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem abi_decode_ge_guard_total:
  abi_decode_ge_guard a b st = ((),st') /\
  eval_operand a s = SOME va /\ eval_operand b s = SOME vb /\
  fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (w2n vb <= w2n va /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\ fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section)
Proof
  strip_tac >> Cases_on `w2n vb <= w2n va`
  >- (disj2_tac >> simp[] >> drule_all abi_decode_ge_guard_sequence >> simp[]) >>
  disj1_tac >> irule abi_decode_ge_guard_reverts >>
  reverse conj_tac >- simp[] >>
  qexistsl [`a`,`b`,`va`,`vb`] >> simp[]
QED

Theorem abi_decode_dynamic_member_total:
  compile_getelemptr_abi src T off opc base_op hi st = (member_op,st') /\
  hi <> Lit 0w /\ abi_decode_source_opcode opc /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand base_op s = SOME (n2w src_base) /\
  abi_decode_load opc (n2w (src_base + (sb + off)) : bytes32) s = n2w payload_off /\
  sb < dimword (:256) /\ payload_off < dimword (:256) /\ fresh_vars_wrt st s ==>
  (?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t) \/
  (sb + payload_off < dimword (:256) /\
   ?t. run_inst_seq (emitted_insts st st') s = OK t /\
     eval_operand member_op t = SOME (n2w (sb + payload_off)) /\
     fresh_vars_wrt st' t /\
     (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
     t.vs_data_section = s.vs_data_section)
Proof
  strip_tac >>
  qpat_x_assum `compile_getelemptr_abi _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bounded_member_phases, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi src T off opc base_op (Lit 0w) st = (member_op,c1)` >>
  rename1 `abi_decode_ge_guard member_op src c1 = (guard_result,st')` >>
  Cases_on `guard_result` >> gvs[] >>
  drule_all (SRULE [AC ADD_ASSOC ADD_COMM] abi_decode_dynamic_member_pointer_sentinel) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb)` by metis_tac[] >>
  drule_all abi_decode_ge_guard_total >> strip_tac
  >- (disj1_tac >> drule abi_decode_ge_guard_shape >> strip_tac >>
      drule_all run_inst_seq_emit_extend >> simp[]) >>
  disj2_tac >>
  `sb + payload_off < dimword (:256)` by
    (gvs[w2n_n2w] >>
     Cases_on `sb + payload_off < dimword (:256)` >> simp[] >>
     `sb + payload_off < 2 * dimword (:256)` by decide_tac >>
     `((sb + payload_off) MOD dimword (:256)) = sb + payload_off - dimword (:256)` by
       (irule MOD_UNIQUE >> qexists `1` >> simp[] >> decide_tac) >>
     gvs[ADD_COMM] >> decide_tac) >>
  simp[AC ADD_ASSOC ADD_COMM] >>
  drule abi_decode_ge_guard_shape >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem abi_decode_dynamic_member_total_reentry:
  compile_getelemptr_abi src T off opc base_op hi st = (member_op,st') /\
  hi <> Lit 0w /\ abi_decode_source_opcode opc /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand base_op initial = SOME (n2w src_base) /\
  abi_decode_load opc (n2w (src_base + (sb + off)) : bytes32) initial = n2w payload_off /\
  sb < dimword (:256) /\ payload_off < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var base_op /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  (?t. run_inst_seq (emitted_insts st st') initial = Abort Revert_abort t) \/
  (sb + payload_off < dimword (:256) /\
   ?t. run_inst_seq (emitted_insts st st') initial = OK t /\
     eval_operand member_op t = SOME (n2w (sb + payload_off)) /\
     fresh_vars_wrt limit_st t /\
     (!op w. abi_decoder_operand_live st.cs_next_var op /\
       eval_operand op initial = SOME w ==> eval_operand op t = SOME w) /\
     t.vs_memory = initial.vs_memory /\ t.vs_call_ctx = initial.vs_call_ctx /\
     t.vs_data_section = initial.vs_data_section)
Proof
  strip_tac >>
  `eval_operand src (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w sb)` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `eval_operand base_op (abi_decoder_prune_vars st.cs_next_var initial) = SOME (n2w src_base)` by
    asm_simp_tac bool_ss [abi_decoder_prune_eval] >>
  `abi_decode_load opc (n2w (src_base + (sb + off)) : bytes32)
     (abi_decoder_prune_vars st.cs_next_var initial) = n2w payload_off` by
    fs[abi_decode_load_def, abi_decode_source_def, abi_decoder_prune_vars_def, mload_def] >>
  `fresh_vars_wrt st (abi_decoder_prune_vars st.cs_next_var initial)` by
    irule abi_decoder_prune_fresh >>
  drule_all abi_decoder_member_pointer_code >> strip_tac >>
  drule_all abi_decode_dynamic_member_total >> strip_tac
  >- (disj1_tac >> drule_all abi_decoder_sequence_revert_reentry >> simp[]) >>
  disj2_tac >> simp[] >>
  drule_all abi_decoder_sequence_reentry_prefix >> strip_tac >>
  drule_all abi_decoder_vars_extend_eval >> strip_tac >>
  drule_all abi_decoder_vars_extend_observations >> strip_tac >>
  goal_assum (drule_at Any) >> gvs[abi_decoder_prune_vars_def]
QED

Theorem abi_decode_truncated_head_probe[local]:
  compile_abi_decode_range_check (Lit 0w) (Lit 32w) (Lit 31w) st = ((),st') /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  `eval_operand (Lit 0w) s = SOME (0w:bytes32) /\
   eval_operand (Lit 32w) s = SOME (32w:bytes32) /\
   eval_operand (Lit 31w) s = SOME (31w:bytes32)` by simp[eval_operand_def] >>
  drule_all compile_abi_decode_range_check_total >> simp[dimword_def]
QED

Theorem abi_decode_wrapped_member_probe[local]:
  compile_getelemptr_abi src T off MLOAD base_op hi st = (member_op,st') /\
  hi <> Lit 0w /\ eval_operand src s = SOME (1w:bytes32) /\
  eval_operand base_op s = SOME (n2w src_base) /\
  abi_decode_load MLOAD (n2w (src_base + (1 + off)) : bytes32) s =
    n2w (dimword (:256) - 1) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = Abort Revert_abort t
Proof
  strip_tac >>
  `eval_operand src s = SOME (n2w 1 : bytes32)` by simp[] >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  `1 < dimword (:256) /\ dimword (:256) - 1 < dimword (:256)` by
    simp[dimword_def] >>
  drule_all abi_decode_dynamic_member_total >> simp[dimword_def]
QED
