(* Reentrant primitive calldata decoding: older operands may be absent. *)
Theory calldataWordLive
Ancestors
  valueEncodingDefs calldataDynOwned calldataWordLeaf abiDecoderClampedWord entryDecodeProps abiEncoder abiDecoderReentry
  abiDecoderGuards abiDecoderRange abiDecoderContract valueEncodingProps safeSequence
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words arithmetic list rich_list finite_map

Theorem calldata_two_tests_repeat:
  emit_op opc ops st = (a,c1) /\
  emit_op test tops c1 = (b,c2) /\
  emit_void ASSERT [b] c2 = ((),last) /\
  step_inst_base (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) s = OK s1 /\
  step_inst_base (mk_inst c1.cs_next_id test tops
    [STRING #"%" (toString c1.cs_next_var)]) s1 =
      OK (update_var (STRING #"%" (toString c1.cs_next_var)) z s1) ==>
  run_inst_seq (emitted_insts st last) s =
    if z <> 0w then OK (update_var (STRING #"%" (toString c1.cs_next_var)) z s1)
    else Abort Revert_abort (revert_state (set_returndata []
      (update_var (STRING #"%" (toString c1.cs_next_var)) z s1)))
Proof
  strip_tac >> imp_res_tac emitted_insts_emit_op >>
  drule emitted_insts_emit_void >> strip_tac >>
  `inst_extends st c1 /\ inst_extends c1 c2 /\ inst_extends c2 last` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `emitted_insts st last = emitted_insts st c1 ++
    (emitted_insts c1 c2 ++ emitted_insts c2 last)` by
    (metis_tac[emitted_insts_append, inst_extends_trans, inst_extends_def]) >>
  gvs[run_inst_seq_def, eval_operand_def, lookup_var_update_var] >>
  Cases_on `z = 0w` >>
  simp[step_inst_base_def, mk_inst_def, eval_operand_def, lookup_var_update_var]
QED

Theorem calldata_two_tests_frame:
  emit_op opc ops st = (a,c1) /\
  emit_op test tops c1 = (b,c2) /\
  emit_void ASSERT [b] c2 = ((),last) /\
  step_inst_base (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) /\
  step_inst_base (mk_inst c1.cs_next_id test tops
    [STRING #"%" (toString c1.cs_next_var)])
    (update_var (STRING #"%" (toString st.cs_next_var)) w s) =
      OK (update_var (STRING #"%" (toString c1.cs_next_var)) z
        (update_var (STRING #"%" (toString st.cs_next_var)) w s)) ==>
  ?t. (run_inst_seq (emitted_insts st last) s =
       if z <> 0w then OK t else Abort Revert_abort t) /\
    (!v. abi_decoder_operand_live st.cs_next_var v ==>
      eval_operand v t = eval_operand v s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all calldata_two_tests_repeat >>
  imp_res_tac emitted_insts_emit_op >>
  Cases_on `z = 0w` >> simp[] >> disch_tac >> gvs[] >>
  simp[revert_state_def, set_returndata_def, update_var_def] >>
  rpt strip_tac >> Cases_on `v` >>
  gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  first_assum (qspec_then `st.cs_next_var` assume_tac) >>
  first_x_assum (qspec_then `st.cs_next_var + 1` assume_tac) >> gvs[]
QED

Theorem calldata_zero_test_frame:
  emit_op opc ops st = (a,c1) /\
  emit_op ISZERO [a] c1 = (b,c2) /\
  emit_void ASSERT [b] c2 = ((),last) /\
  step_inst_base (mk_inst st.cs_next_id opc ops
    [STRING #"%" (toString st.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) ==>
  ?t. (run_inst_seq (emitted_insts st last) s =
       if w = 0w then OK t else Abort Revert_abort t) /\
    (!v. abi_decoder_operand_live st.cs_next_var v ==>
      eval_operand v t = eval_operand v s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `step_inst_base (mk_inst c1.cs_next_id ISZERO [a]
    [STRING #"%" (toString c1.cs_next_var)])
    (update_var (STRING #"%" (toString st.cs_next_var)) w s) =
    OK (update_var (STRING #"%" (toString c1.cs_next_var)) (bool_to_word (w = 0w))
      (update_var (STRING #"%" (toString st.cs_next_var)) w s))` by
    (rev_drule emitted_insts_emit_op >> strip_tac >>
     irule step_ISZERO >> simp[eval_operand_def, lookup_var_update_var]) >>
  drule_all calldata_two_tests_frame >> Cases_on `w = 0w` >> simp[bool_to_word_def]
QED

Theorem calldata_unsigned_clamp_repeat:
  compile_abi_int_clamp op bits F st = ((),last) /\
  eval_operand op s = SOME w ==>
  ?t. (run_inst_seq (emitted_insts st last) s =
       if word_lsr w (w2n (n2w bits : bytes32)) = 0w then OK t
       else Abort Revert_abort t) /\
    (!v. abi_decoder_operand_live st.cs_next_var v ==>
      eval_operand v t = eval_operand v s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[compile_abi_int_clamp_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `step_inst_base (mk_inst st.cs_next_id SHR [Lit (n2w bits);op]
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var))
      (word_lsr w (w2n (n2w bits : bytes32))) s)` by
    (irule step_SHR >> simp[eval_operand_def]) >>
  drule_all calldata_zero_test_frame >> simp[]
QED

Theorem calldata_bytes_clamp_repeat:
  compile_abi_bytes_clamp op m st = ((),last) /\
  eval_operand op s = SOME w ==>
  ?t. (run_inst_seq (emitted_insts st last) s =
       if word_lsl w (w2n (n2w (m * 8) : bytes32)) = 0w then OK t
       else Abort Revert_abort t) /\
    (!v. abi_decoder_operand_live st.cs_next_var v ==>
      eval_operand v t = eval_operand v s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[compile_abi_bytes_clamp_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `step_inst_base (mk_inst st.cs_next_id SHL [Lit (n2w (8 * m));op]
    [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var))
      (word_lsl w (w2n (n2w (8 * m) : bytes32))) s)` by
    (irule step_SHL >> simp[eval_operand_def]) >>
  drule_all calldata_zero_test_frame >> simp[]
QED

Theorem calldata_signed_clamp_repeat:
  compile_abi_int_clamp op bits T st = ((),last) /\
  eval_operand op s = SOME w /\ abi_decoder_operand_live st.cs_next_var op ==>
  ?t. (run_inst_seq (emitted_insts st last) s =
       if sign_extend (n2w (bits DIV 8 - 1)) w = w then OK t
       else Abort Revert_abort t) /\
    (!v. abi_decoder_operand_live st.cs_next_var v ==>
      eval_operand v t = eval_operand v s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  simp[compile_abi_int_clamp_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op SIGNEXTEND _ st = (canonical,c1)` >>
  qmatch_goalsub_abbrev_tac `if extended = w then _ else _` >>
  `step_inst_base (mk_inst st.cs_next_id SIGNEXTEND
    [Lit (n2w (bits DIV 8 - 1));op] [STRING #"%" (toString st.cs_next_var)]) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) extended s)` by
    (simp[Abbr `extended`] >> irule step_SIGNEXTEND >> simp[eval_operand_def]) >>
  `eval_operand op (update_var (STRING #"%" (toString st.cs_next_var)) extended s) = SOME w` by
    metis_tac[calldata_update_protected] >>
  `step_inst_base (mk_inst c1.cs_next_id EQ [op;canonical]
    [STRING #"%" (toString c1.cs_next_var)])
    (update_var (STRING #"%" (toString st.cs_next_var)) extended s) =
    OK (update_var (STRING #"%" (toString c1.cs_next_var)) (bool_to_word (extended = w))
      (update_var (STRING #"%" (toString st.cs_next_var)) extended s))` by
    (rev_drule emitted_insts_emit_op >> strip_tac >>
     simp[step_inst_base_def, exec_pure2_def, eval_operand_update_var, mk_inst_def] >>
     Cases_on `extended = w` >> gvs[bool_to_word_def]) >>
  drule_all calldata_two_tests_frame >> Cases_on `extended = w` >> simp[bool_to_word_def]
QED

Theorem calldata_clamp_repeat:
  !cl op st last s w.
  compile_abi_clamp_basetype op cl st = ((),last) /\
  eval_operand op s = SOME w /\ abi_decoder_operand_live st.cs_next_var op ==>
  ?t. (run_inst_seq (emitted_insts st last) s =
       if abi_clamp_ok cl w then OK t else Abort Revert_abort t) /\
    (!v. abi_decoder_operand_live st.cs_next_var v ==>
      eval_operand v t = eval_operand v s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  Cases >> simp[compile_abi_clamp_basetype_def, abi_clamp_ok_def]
  >- (rw[comp_return_def] >> qexists_tac `s` >>
      simp[emitted_insts_def, run_inst_seq_def, DROP_LENGTH_NIL])
  >- (rpt gen_tac >> rename1 `compile_abi_int_clamp op bits signed st = _` >>
      Cases_on `signed` >> strip_tac
      >- (drule_all calldata_signed_clamp_repeat >> simp[]) >>
      drule_all calldata_unsigned_clamp_repeat >> simp[])
  >- (rpt strip_tac >> drule_all calldata_bytes_clamp_repeat >> simp[]) >>
  rpt strip_tac >>
  `compile_abi_int_clamp op 1 F st = ((),last)` by
    simp[compile_abi_int_clamp_def] >>
  drule_all calldata_unsigned_clamp_repeat >> simp[]
QED

Theorem calldata_mstore_repeat:
  emit_void MSTORE [dst;value] st = ((),last) /\
  eval_operand dst s = SOME p /\ eval_operand value s = SOME w ==>
  run_inst_seq (emitted_insts st last) s = OK (mstore (w2n p) w s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id MSTORE [dst;value] []) s =
      OK (mstore (w2n p) w s)` by (irule step_MSTORE >> simp[]) >>
  simp[run_inst_seq_def]
QED

Theorem calldata_word_accepted_live:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecPrimWord clamp) st = ((),last) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_clamp_ok clamp (abi_decode_load CALLDATALOAD p s) ==>
  ?t. run_inst_seq (emitted_insts st last) s = OK t /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s /\
    abi_decode_frame d 32 s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_return_def, pairTheory.UNCURRY_DEF, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (value,c1)` >>
  rename1 `compile_abi_clamp_basetype value clamp c1 = ((),c2)` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  qpat_x_assum `s1 = update_var _ _ s` kall_tac >>
  `abi_decoder_operand_live c1.cs_next_var value` by
    metis_tac[abi_decoder_operand_live_emit] >>
  drule_all calldata_clamp_repeat >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `st.cs_next_var <= c1.cs_next_var` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `eval_operand dst s2 = SOME (n2w d) /\
   eval_operand value s2 = SOME (abi_decode_load CALLDATALOAD p s)` by
    metis_tac[abi_decoder_operand_live_mono] >>
  drule_all calldata_mstore_repeat >> strip_tac >>
  imp_res_tac inst_extends_emit_void >>
  drule compile_abi_clamp_structure >> strip_tac >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`,`c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st last) s =
      OK (mstore d (abi_decode_load CALLDATALOAD p s) s2)` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`s2`,`c2`] >> simp[]) >>
  goal_assum (drule_at Any) >>
  simp[w2n_n2w, mstore_mem_word_at_same] >>
  conj_tac
  >- (simp[abi_decode_frame_def] >> rpt strip_tac >>
      qpat_x_assum `s2.vs_memory = s.vs_memory` (SUBST1_TAC o SYM) >>
      irule mstore_mem_bytes_at_disjoint >> simp[]) >>
  simp[mstore_def, write_memory_with_expansion_def] >>
  rpt strip_tac >>
  `abi_decoder_operand_live c1.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `eval_operand op (mstore d (abi_decode_load CALLDATALOAD p s) s2) =
      eval_operand op s2` by
    (Cases_on `op` >> simp[eval_operand_def, lookup_var_def, mstore_def,
       write_memory_with_expansion_def]) >>
  gvs[mstore_def, write_memory_with_expansion_def] >> metis_tac[]
QED

Theorem calldata_word_rejected_live:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecPrimWord clamp) st = ((),last) /\
  eval_operand src s = SOME p /\ abi_decoder_operand_live st.cs_next_var src /\
  ~abi_clamp_ok clamp (abi_decode_load CALLDATALOAD p s) ==>
  ?t. run_inst_seq (emitted_insts st last) s = Abort Revert_abort t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_return_def, pairTheory.UNCURRY_DEF, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (value,c1)` >>
  rename1 `compile_abi_clamp_basetype value clamp c1 = ((),c2)` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  qpat_x_assum `s1 = update_var _ _ s` kall_tac >>
  `abi_decoder_operand_live c1.cs_next_var value` by
    metis_tac[abi_decoder_operand_live_emit] >>
  drule_all calldata_clamp_repeat >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = Abort Revert_abort t` >>
  imp_res_tac inst_extends_emit_void >>
  drule compile_abi_clamp_structure >> strip_tac >>
  `run_inst_seq (emitted_insts c1 last) s1 = Abort Revert_abort t` by
    (irule run_inst_seq_abort_extends >> qexists_tac `c2` >> simp[]) >>
  `inst_extends c1 last` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st last) s = Abort Revert_abort t` by
    (drule_all run_inst_seq_emit_extend >> simp[]) >>
  qexists_tac `t` >> simp[] >> rpt strip_tac >>
  `st.cs_next_var <= c1.cs_next_var` by
    (drule emitted_insts_emit_op >> simp[]) >>
  metis_tac[abi_decoder_operand_live_mono]
QED

Theorem calldata_clamp_store_prefix_live:
  compile_abi_clamp_basetype value clamp st = ((),last) /\
  eval_operand value s = SOME w /\ abi_decoder_operand_live st.cs_next_var value /\
  abi_decoder_operand_live st.cs_next_var dst /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  d + 32 <= s.vs_alloca_next ==>
  !pre i post u.
    emitted_insts st last ++ [mk_inst id MSTORE [dst;value] []] = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  strip_tac >> ho_match_mp_tac calldata_prefix_safe_append >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >>
      drule calldata_clamp_instruction_safe >> simp[]) >>
  gen_tac >> strip_tac >> drule_all calldata_clamp_repeat >>
  Cases_on `abi_clamp_ok clamp w` >> simp[] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL calldata_mstore_prefix_safe) >>
  qexists_tac `d` >> simp[]
QED

Theorem calldata_word_prefix_live:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecPrimWord clamp) st = ((),last) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\ d + 32 <= s.vs_alloca_next /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var src ==>
  !pre i post u. emitted_insts st last = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  simp_tac bool_ss [compile_abi_decode_to_buf_def, compile_abi_dec_addr_def, compile_abi_decode_range_check_def, comp_return_def, pairTheory.UNCURRY_DEF, compile_abi_decode_static_def,
    comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (value,c1)` >>
  rename1 `compile_abi_clamp_basetype value clamp c1 = ((),c2)` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  qpat_x_assum `s1 = update_var _ _ s` kall_tac >>
  imp_res_tac inst_extends_emit_void >>
  drule compile_abi_clamp_structure >> strip_tac >>
  `inst_extends c1 last` by metis_tac[inst_extends_trans] >>
  `emitted_insts st last = emitted_insts st c1 ++ emitted_insts c1 last /\
   emitted_insts c1 last = emitted_insts c1 c2 ++ emitted_insts c2 last` by
    (conj_tac >> irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. !u. inst_mem_below_frontier i u) (emitted_insts st c1)` by
    (drule emitted_insts_emit_op >> simp[] >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]) >>
  asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `s1` >> asm_rewrite_tac[] >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >> simp[]) >>
  drule emitted_insts_emit_void >> simp[] >> strip_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL calldata_clamp_store_prefix_live) >>
  qexistsl_tac [`abi_decode_load CALLDATALOAD p s`, `d`, `clamp`] >> simp[] >>
  `st.cs_next_var <= c1.cs_next_var` by
    (drule emitted_insts_emit_op >> simp[]) >>
  metis_tac[abi_decoder_operand_live_emit, abi_decoder_operand_live_mono]
QED

Theorem calldata_word_live_frag_mem:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) (Lit 0w) (DecPrimWord clamp) st = ((),last) /\
  eval_operand src initial = SOME p /\ eval_operand dst initial = SOME (n2w d) /\
  d < dimword (:256) /\ d + 32 <= initial.vs_alloca_next /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var src ==>
  frag_exec_mem ctx st last (\s. s = initial)
    (\t. abi_clamp_ok clamp (abi_decode_load CALLDATALOAD p initial) /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p initial /\
      abi_decode_frame d 32 initial t /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      t.vs_allocas = initial.vs_allocas /\ t.vs_alloca_next = initial.vs_alloca_next)
    (\r. ?z. r = Abort Revert_abort z)
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_clamped_word_shape >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st last)` by (fs[EVERY_MEM] >> metis_tac[]) >>
  drule calldata_word_opcodes >> strip_tac >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> simp[] >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      ho_match_mp_tac (GEN_ALL calldata_word_prefix_live) >>
      qexistsl_tac [`src`,`p`,`dst`,`d`,`clamp`] >> simp[]) >>
  Cases_on `abi_clamp_ok clamp (abi_decode_load CALLDATALOAD p initial)`
  >- (drule_all calldata_word_accepted_live >> strip_tac >>
      disj1_tac >> qexists_tac `t` >>
      gvs[abi_decode_frame_def, instIdxIndepTheory.eval_op_inst_idx] >> metis_tac[]) >>
  drule_all calldata_word_rejected_live >> strip_tac >>
  disj2_tac >> qexists_tac `t` >>
  simp[instIdxIndepTheory.eval_op_inst_idx]
QED
