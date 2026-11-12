(* Instruction-check boundaries for scalar Log encoding. *)
Theory stmtLogEncodeMemory
Ancestors
  stmtSimLogMembersRun stmtSimLogScalarMembers stmtSimLogEncodeLayout abiEncoderInput
  abiEncoderLeaves abiDecoderGuards abiDecoderLoop abiBuiltinPrefix
  abiEncoderChildPrefix abiEncoderCounters abiDecoderReentryAddress abiDecoderReentry
  abiEncoderMemberCode abiEncoder abiEncoderComplexCode abiBuiltinAllocation
  stmtSimLogScalarPrefix context stmtSimLogAllocResource venomMemDefs
  stmtSimLogScalarEncode abiEncoderInputFrame abiEncoderMembersInput abiEncoderComplexPrefix
  abiEncoderComplexDynamic abiEncoderTuple abiEncoderOpenInput abiDecoderFrameCompose abiDecoderFrame
  valueEncodingProofs abiCanonicalWindows abiEncoderBytes abiDecoderDynamicLoopSetup
  abiEncoderWindowBytesMem fragExecMem contractABI words arithmetic
  abiEncoderChildCode emitHelper emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs list rich_list
  instMemFrontier venomExecSemantics venomInst venomState stmtReasonMemory moduleLoweringProps

(* The child reads an unrounded payload; its destination zeroing is rounded. *)
Theorem log_bytes_encode_mem_ok:
  compile_abi_encode_to_buf dst src (AbiBytestring maxlen) st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ mload sb s = n2w cnt /\
  eval_operand dst s = SOME (n2w db) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at st x) /\
  sb + 32 + cnt <= s.vs_alloca_next /\
  db + 32 + contractABI$ceil32 cnt <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >>
  `cnt <= contractABI$ceil32 cnt /\
   cnt + 31 < 32 + contractABI$ceil32 cnt` by
    (mp_tac abiEncoderRoundingTheory.abi_encoder_ceil32_bounds >> decide_tac) >>
  drule window_bytes_mem_checks >> disch_then irule >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`cnt`, `db`, `sb`] >> simp[] >> decide_tac
QED

Theorem log_child_prefix_mem_ok:
  abi_encode_child_prefix dst ho dp st = (ops,en) /\
  eval_operand dp s = SOME (n2w slot) /\
  (!x. dp = Var x ==> not_fresh_at st x) /\
  slot < dimword (:256) /\ slot+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_child_prefix _ _ _ _ = _` mp_tac >>
  simp[abi_encode_child_prefix_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, Once run_inst_seq_mem_ok_cons] >>
  (conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def])) >>
  simp[step_add_eq, eval_operand_def] >>
  Cases_on `eval_operand dst s` >> simp[] >>
  `eval_operand dp (update_var (STRING #"%" (toString st.cs_next_var))
    (x + n2w ho) s) = SOME (n2w slot)` by
    (Cases_on `dp` >> gvs[eval_operand_def] >>
     metis_tac[lookup_var_update_not_fresh, LESS_EQ_REFL]) >>
  simp[Once run_inst_seq_mem_ok_cons, below_frontier_MLOAD, update_var_def] >>
  Cases_on `step_inst_base
    (mk_inst (st.cs_next_id + 1) MLOAD [dp]
      [STRING #"%" (toString (st.cs_next_var + 1))])
    (s with vs_vars := s.vs_vars |+
      (STRING #"%" (toString st.cs_next_var),x + n2w ho))` >> simp[] >>
  irule run_inst_seq_mem_ok_every >> simp[] >> rpt strip_tac >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem log_child_suffix_mem_ok:
  abi_encode_child_suffix head dp offset len st = (out,en) /\
  eval_operand head s = SOME (n2w hp) /\
  eval_operand dp s = SOME (n2w slot) /\
  (!x. dp = Var x ==> not_fresh_at st x) /\
  hp < dimword (:256) /\ slot < dimword (:256) /\
  hp+32 <= s.vs_alloca_next /\ slot+32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_child_suffix _ _ _ _ _ = _` mp_tac >>
  simp[abi_encode_child_suffix_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
    fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, Once run_inst_seq_mem_ok_cons, below_frontier_MSTORE] >>
  simp[step_mstore_eq] >>
  Cases_on `eval_operand offset s` >> simp[] >>
  simp[Once run_inst_seq_mem_ok_cons] >>
  (conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def])) >>
  simp[step_add_eq, eval_operand_mstore] >>
  Cases_on `eval_operand len s` >> simp[] >>
  `eval_operand dp (update_var (STRING #"%" (toString st.cs_next_var))
    (x + x') (mstore hp x s)) = SOME (n2w slot)` by
    (Cases_on `dp` >> gvs[eval_operand_def, eval_operand_mstore] >>
     metis_tac[lookup_var_update_not_fresh, LESS_EQ_REFL,
       lookup_var_mstore]) >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE,
    update_var_def, mstore_def, write_memory_with_expansion_def]
QED

Theorem log_bytes_input_count[local]:
  abi_encoder_input (AbiBytestring mx) ty av b cap s.vs_memory ==>
  ?cnt. mload b s = n2w cnt /\ 32+cnt <= cap /\
    LENGTH (enc ty av) = 32+contractABI$ceil32 cnt
Proof
  simp_tac bool_ss [abi_encoder_input_bytes_iff] >> strip_tac >>
  qexists_tac `LENGTH bs` >>
  `LENGTH (enc ty av) = 32+contractABI$ceil32 (LENGTH bs)` by
    metis_tac[abi_encoder_bytes_encoding] >>
  fs[valueEncodingPropsTheory.mem_word_at_eq_mload]
QED

Theorem log_copy_child_mem_ok[local]:
  compile_abi_encode_child dst src (AbiCopy 32) F ho dp st = (out,en) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  sb+32 <= s.vs_alloca_next /\ d+ho+32 <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts st en) s
Proof
  strip_tac >> drule abi_encode_static_child_trace >> strip_tac >>
  drule abi_encode_copy_code >> strip_tac >>
  qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
  qpat_x_assum `emit_void MCOPY _ _ = _` mp_tac >>
  simp[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, Once run_inst_seq_mem_ok_cons] >>
  (conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def])) >>
  simp[step_add_eq, eval_operand_def] >>
  `eval_operand src (update_var (STRING #"%" (toString st.cs_next_var))
      (n2w d + n2w ho) s) = SOME (n2w sb)` by
    (Cases_on `src` >> gvs[eval_operand_def] >>
     metis_tac[lookup_var_update_not_fresh, LESS_EQ_REFL]) >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY,
    eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE,
    word_add_n2w, w2n_n2w] >>
  decide_tac
QED

Theorem log_members_child_mem_ok:
  compile_abi_encode_child dst elem_src ei dyn ho dp st = (out,end_st) /\
  log_members_run_pre ((ei,asz,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap st limit_st src dst dp p s /\
  eval_operand elem_src s = SOME (n2w (sb+so)) /\
  abi_decoder_operand_live st.cs_next_var elem_src /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  sb+so+abi_encoder_member_span ((ei,asz,mz,dyn)::infos) <= s.vs_alloca_next /\
  d+outcap <= s.vs_alloca_next /\ p+32 <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts st end_st) s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `log_members_run_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[log_members_run_pre_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule log_members_layout_cons_input >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule log_members_layout_bounds >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `log_scalar_enc_info ei` mp_tac >>
  simp_tac bool_ss [log_scalar_enc_info_def] >> strip_tac
  >- suspend "copy" >>
  suspend "bytes"
QED

Resume log_members_child_mem_ok[copy]:
  gvs[abi_encoder_input_copy_iff] >> (
  `LENGTH (enc ty av) = 32` by
    metis_tac[LENGTH_mem_bytes_at_proof] >>
  drule log_copy_child_mem_ok >> disch_then irule >>
  (conj_tac >- (rpt strip_tac >>
    gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def])) >>
  simp[] >> conj_tac
  >- (qexists_tac `d` >> simp[] >> decide_tac) >>
  qexists_tac `sb+so` >> simp[] >> decide_tac)
QED
Resume log_members_child_mem_ok[bytes]:
  qpat_x_assum `ei = AbiBytestring _` SUBST_ALL_TAC >>
  `dyn = T` by (fs[abi_encoder_input_bytes_iff] >> gvs[]) >>
  qpat_x_assum `dyn = T` SUBST_ALL_TAC >>
  drule abi_encode_dynamic_child_trace >> strip_tac >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\
   child_end.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_encode_child_prefix_sequence >>
  disch_then (qx_choose_then `ready` strip_assume_tac) >>
  `sb+so < dimword (:256) /\
   d+(hl+LENGTH (FLAT (abi_tuple_tails pre pvs)))+LENGTH (enc ty av) < dimword (:256)` by
    (fs[] >> decide_tac) >>
  drule log_scalar_bytes_body_run >> disch_then drule >> disch_then drule >>
  disch_then (qspecl_then [`p`, `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`,
    `limit_st`, `d`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[abi_encoder_member_span_def] >> decide_tac)) >>
  disch_then (qx_choose_then `ready2` (qx_choose_then `encoded` strip_assume_tac)) >>
  `ready2 = ready` by fs[abi_builtin_prefix_def] >>
  qpat_x_assum `ready2 = ready` SUBST_ALL_TAC >>
  `ready.vs_memory = s.vs_memory /\ ready.vs_alloca_next = s.vs_alloca_next /\
   eval_operand elem_src ready = SOME (n2w (sb+so))` by
    metis_tac[abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  suspend "bytes_checks"
QED

Resume log_members_child_mem_ok[bytes_checks]:
  `!x. dp = Var x ==> not_fresh_at st x` by
    (rpt strip_tac >> fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def]) >>
  `run_inst_seq_mem_ok (emitted_insts st prepared) s` by
    (drule log_child_prefix_mem_ok >> disch_then irule >> simp[] >>
     qexists_tac `p` >> simp[]) >>
  `?cnt. mload (sb+so) ready = n2w cnt /\ 32+cnt <= mz /\
    LENGTH (enc ty av) = 32+contractABI$ceil32 cnt` by
    (drule log_bytes_input_count >>
     simp[mload_def]) >>
  `!x. SND (SND ops) = Var x \/ elem_src = Var x ==> not_fresh_at prepared x` by
    (rpt strip_tac >> fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts prepared child_end) ready` by
    (drule log_bytes_encode_mem_ok >> disch_then irule >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     simp[] >> qexistsl_tac [`cnt`, `d+(hl+LENGTH (FLAT (abi_tuple_tails pre pvs)))`, `sb+so`] >>
     simp[] >> fs[abi_encoder_member_span_def] >> decide_tac) >>
  `eval_operand dp encoded = SOME (n2w p)` by metis_tac[] >>
  `!x. dp = Var x ==> not_fresh_at child_end x` by
    (rpt strip_tac >> fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      not_fresh_at_def] >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts child_end end_st) encoded` by
    (drule log_child_suffix_mem_ok >> disch_then irule >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac
     >- (qexists_tac `p` >> simp[]) >>
     qexists_tac `d+ho` >> simp[] >> fs[] >> decide_tac) >>
  suspend "bytes_compose"
QED

Resume log_members_child_mem_ok[bytes_compose]:
  `emitted_insts prepared end_st = emitted_insts prepared child_end ++
     emitted_insts child_end end_st` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  `emitted_insts st end_st = emitted_insts st prepared ++
     emitted_insts prepared end_st` by
    metis_tac[emitted_insts_append, inst_extends_def, inst_extends_trans] >>
  `run_inst_seq (emitted_insts st prepared) s = OK ready` by
    fs[abi_builtin_prefix_def] >>
  asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
  simp[] >> rpt strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_append >> simp[]
QED
Finalise log_members_child_mem_ok

Theorem log_members_list_mem_ok:
  !infos dst src so ho dp st out final tys avs pre pvs sb d hl outcap limit_st p s.
  compile_abi_encode_complex_elems dst src infos so ho dp st = (out,final) /\
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap st limit_st src dst dp p s /\
  final.cs_next_var <= limit_st.cs_next_var /\
  sb+so+abi_encoder_member_span infos <= s.vs_alloca_next /\
  d+outcap <= s.vs_alloca_next /\ p+32 <= s.vs_alloca_next /\
  s.vs_alloca_next < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts st final) s
Proof
  Induct >- suspend "nil" >>
  qx_gen_tac `info` >> PairCases_on `info` >> rpt gen_tac >> strip_tac >>
  drule log_members_run_pre_lengths >> strip_tac >>
  Cases_on `tys` >- fs[] >> Cases_on `avs` >- fs[] >>
  rename1 `log_members_run_pre _ (ty::tys) (av::avs) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` >>
  drule abi_encoder_member_cons_trace >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  drule abi_encoder_child_bounds >> strip_tac >>
  `child_end.cs_next_var <= limit_st.cs_next_var /\
   prepared.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_members_run_source_add >>
  disch_then (qx_choose_then `ready` strip_assume_tac) >>
  drule_all log_members_run_child >>
  disch_then (qx_choose_then `encoded` strip_assume_tac) >>
  `ready.vs_alloca_next = s.vs_alloca_next /\
   encoded.vs_alloca_next = s.vs_alloca_next` by fs[log_members_run_post_def] >>
  `run_inst_seq_mem_ok (emitted_insts prepared child_end) ready` by
    (drule log_members_child_mem_ok >> disch_then drule >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts child_end final) encoded` by
    (first_x_assum drule >> disch_then drule >> simp[] >>
     fs[abi_encoder_member_span_def] >> decide_tac) >>
  suspend "compose"
QED

Resume log_members_list_mem_ok[compose]:
  `run_inst_seq_mem_ok (emitted_insts st prepared) s` by
    (drule emitted_insts_emit_op >> strip_tac >> simp[] >>
     irule run_inst_seq_mem_ok_every >> simp[] >>
     rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  drule_all log_members_run_list >>
  disch_then (qx_choose_then `actual` strip_assume_tac) >>
  `inst_extends st prepared /\ inst_extends prepared child_end /\
   inst_extends child_end final /\
   run_inst_seq (emitted_insts st prepared) s = OK ready /\
   run_inst_seq (emitted_insts prepared child_end) ready = OK encoded` by
    fs[log_members_run_post_def] >>
  `emitted_insts prepared final = emitted_insts prepared child_end ++
     emitted_insts child_end final` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  `emitted_insts st final = emitted_insts st prepared ++ emitted_insts prepared final` by
    metis_tac[emitted_insts_append, inst_extends_def, inst_extends_trans] >>
  asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
  simp[] >> rpt strip_tac >> gvs[] >>
  irule run_inst_seq_mem_ok_append >> simp[]
QED

Resume log_members_list_mem_ok[nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ [] _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, run_inst_seq_mem_ok_def]
QED
Finalise log_members_list_mem_ok

Theorem log_scalar_cursor_frontier:
  ((FLOOKUP initial.vs_allocas site = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas site = SOME (p,32)) /\
  (FLOOKUP initial.vs_allocas site <> NONE ==> p+32 <= initial.vs_alloca_next) ==>
  initial.vs_alloca_next <= (abi_builtin_allocate_state site 32 initial).vs_alloca_next /\
  p+32 <= (abi_builtin_allocate_state site 32 initial).vs_alloca_next
Proof
  strip_tac >> gvs[abi_builtin_allocate_state_def]
QED

Theorem log_scalar_cursor_prefix_mem_ok:
  abi_encode_complex_prefix infos st = (dyn_ptr,st') /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32)) /\
  p < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (FLOOKUP initial.vs_allocas st.cs_next_id <> NONE ==> p+32 <= initial.vs_alloca_next) ==>
  run_inst_seq_mem_ok (emitted_insts st st') initial
Proof
  strip_tac >>
  qpat_x_assum `abi_encode_complex_prefix _ _ = _` mp_tac >>
  simp[abi_encode_complex_prefix_def, compile_alloc_buffer_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, Once run_inst_seq_mem_ok_cons] >>
  (conj_tac >- (irule below_frontier_no_ranges >> simp[mk_inst_def])) >>
  simp[step_alloca_eq, run_inst_seq_mem_ok_last, below_frontier_MSTORE,
    eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[w2n_n2w, dimword_def] >> decide_tac
QED

(* The Log caller keeps statement state through source stores and output
   allocation; its cursor ALLOCA is an instruction of the same function. *)
Theorem log_scalar_cursor_stmt_resources:
  stmt_state_rel ctx func ce cx es initial /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w 32)] ==>
  ?p. ((FLOOKUP initial.vs_allocas inst.inst_id = NONE /\ p = initial.vs_alloca_next) \/
       FLOOKUP initial.vs_allocas inst.inst_id = SOME (p,32)) /\
    p < dimword (:256) /\
    (FLOOKUP initial.vs_allocas inst.inst_id <> NONE ==> p+32 <= initial.vs_alloca_next) /\
    (abi_builtin_allocate_state inst.inst_id 32 initial).vs_alloca_next < dimword (:256)
Proof
  strip_tac >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all log_event_buffer_resource >> strip_tac >>
  `alloca_next_valid initial /\ alloca_room ctx func initial` by
    fs[stmt_state_rel_def, alloca_inv_def] >>
  `initial.vs_alloca_next < dimword (:256)` by
    (drule alloca_room_next_lt >> simp[]) >>
  qexists_tac `p` >>
  gvs[abi_builtin_allocate_state_def, alloca_next_valid_def] >>
  metis_tac[DECIDE ``p+32 < n ==> p < n``]
QED

Theorem log_scalar_memory_layout_frame[local]:
  abi_encoder_input (AbiComplex infos) (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  abi_decode_frame p 32 initial ready /\ (sb+cap <= p \/ p+32 <= sb) ==>
  log_members_layout infos ats avs [] [] sb 0 0 db (head_lengths ats 0) outcap ready.vs_memory /\
  abi_encoder_member_span infos <= cap /\
  SUM (MAP (\(_,asz,_,_). asz) infos) = head_lengths ats 0
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_footprint_frame [(p,32)] initial ready` by
    (irule (iffLR abi_decode_frame_footprint) >> first_assum ACCEPT_TAC) >>
  `abi_footprint_disjoint sb cap [(p,32)]` by simp[abi_footprint_disjoint_def] >>
  `abi_encoder_input (AbiComplex infos) (Tuple ats) (ListV avs) sb cap ready.vs_memory` by
    (drule_all abi_encoder_input_frame >> simp[]) >>
  conj_tac >- (irule log_members_layout_initial >> asm_simp_tac bool_ss [] >>
    qexists_tac `cap` >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_x_assum `abi_encoder_input _ _ _ _ _ initial.vs_memory` mp_tac >>
      simp_tac bool_ss [abi_encoder_complex_input_iff] >> rpt strip_tac >> first_assum ACCEPT_TAC) >>
  drule abi_encoder_complex_input_metadata >> simp[]
QED

Theorem log_scalar_tuple_mem_ok:
  compile_abi_encode_to_buf dst src ei st = (out,end_st) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
     EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb+cap < dimword (:256) /\ db+outcap < dimword (:256) /\
  (sb+cap <= db \/ db+outcap <= sb) /\
  fresh_vars_wrt limit_st initial /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  ((?infos. ei = AbiComplex infos) ==>
    ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
      FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32)) /\
    p < dimword (:256) /\ (sb+cap <= p \/ p+32 <= sb) /\
    (db+outcap <= p \/ p+32 <= db) /\
    (FLOOKUP initial.vs_allocas st.cs_next_id <> NONE ==> p+32 <= initial.vs_alloca_next) /\
    (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_alloca_next < dimword (:256)) /\
  sb+cap <= initial.vs_alloca_next /\ db+outcap <= initial.vs_alloca_next /\
  initial.vs_alloca_next < dimword (:256) ==>
  run_inst_seq_mem_ok (emitted_insts st end_st) initial /\
  !actual. run_inst_seq (emitted_insts st end_st) initial = OK actual ==>
    initial.vs_alloca_next <= actual.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse conj_tac >- suspend "frontier" >>
  qpat_x_assum `(?n. _ /\ _) \/ (?infos. _ /\ _ /\ _)`
    (DISJ_CASES_THEN strip_assume_tac)
  >- suspend "copy" >>
  qpat_x_assum `ei = _` SUBST_ALL_TAC >>
  qpat_x_assum `(?infos'. _ = AbiComplex infos') ==> _` mp_tac >>
  simp_tac (srw_ss()) [Excl "enc_def"] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_complex_dynamic_trace >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var /\
   middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_scalar_cursor_prefix_run >>
  disch_then (qx_choose_then `ready` strip_assume_tac) >>
  `log_members_run_pre infos ats avs [] [] sb 0 0 db (head_lengths ats 0) outcap
     prepared limit_st src dst dyn_ptr p ready` by suspend "prepare" >>
  `initial.vs_alloca_next <= ready.vs_alloca_next /\
   p+32 <= ready.vs_alloca_next` by
    (drule log_scalar_cursor_frontier >> simp[]) >>
  `abi_encoder_member_span infos <= cap` by
    (qpat_assum `abi_encoder_input _ _ _ _ _ _` mp_tac >>
     simp_tac bool_ss [abi_encoder_complex_input_iff] >> rpt strip_tac >>
     first_assum ACCEPT_TAC) >>
  `run_inst_seq_mem_ok (emitted_insts st prepared) initial` by
    (drule log_scalar_cursor_prefix_mem_ok >> simp[] >> metis_tac[]) >>
  `run_inst_seq_mem_ok (emitted_insts prepared middle) ready` by
    (drule log_members_list_mem_ok >> disch_then drule >> simp[] >> decide_tac) >>
  drule_all log_members_run_list >>
  disch_then (qx_choose_then `encoded` strip_assume_tac) >>
  suspend "finish"
QED

Resume log_scalar_tuple_mem_ok[frontier]:
  drule log_scalar_tuple_run >> disch_then drule >>
  disch_then (qspecl_then [`p`,`outcap`,`limit_st`,`db`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >> rpt strip_tac >>
  gvs[] >> simp[abi_builtin_allocate_state_def] >>
  Cases_on `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` >> simp[]
QED
Resume log_scalar_tuple_mem_ok[copy]:
  qpat_x_assum `ei = _` SUBST_ALL_TAC >>
  drule abi_encode_copy_code >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  qpat_x_assum `abi_encoder_input _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[abi_encoder_input_copy_iff] >> strip_tac >>
  `LENGTH (enc (Tuple ats) (ListV avs)) = n` by
    (drule_all (cj 1 enc_has_static_length) >> simp[]) >>
  simp[run_inst_seq_mem_ok_last, below_frontier_MCOPY,
    eval_operand_def, w2n_n2w] >> decide_tac
QED
Resume log_scalar_tuple_mem_ok[prepare]:
  drule_all log_scalar_memory_layout_frame >>
  disch_then (qspec_then `db` strip_assume_tac) >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `eval_operand src ready = SOME (n2w sb)` by (first_x_assum irule >> simp[]) >>
  `eval_operand dst ready = SOME (n2w db)` by (first_x_assum irule >> simp[]) >>
  `abi_decoder_operand_live prepared.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live prepared.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_decoder_operand_live prepared.cs_next_var dyn_ptr` by
    (asm_simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> decide_tac) >>
  simp_tac bool_ss [log_members_run_pre_def] >>
  asm_simp_tac (srw_ss()) [abi_tuple_tails_def, Excl "enc_def"] >>
  rpt conj_tac >> decide_tac
QED
Resume log_scalar_tuple_mem_ok[finish]:
  `eval_operand dyn_ptr encoded = SOME (n2w p)` by
    fs[log_members_run_pre_def] >>
  `encoded.vs_alloca_next = ready.vs_alloca_next /\
   run_inst_seq (emitted_insts prepared middle) ready = OK encoded /\
   inst_extends prepared middle` by fs[log_members_run_post_def] >>
  `run_inst_seq_mem_ok (emitted_insts middle end_st) encoded` by
    simp[run_inst_seq_mem_ok_last, below_frontier_MLOAD, w2n_n2w] >>
  `inst_extends middle end_st` by simp[inst_extends_def] >>
  `emitted_insts st end_st = emitted_insts st prepared ++
    emitted_insts prepared middle ++ emitted_insts middle end_st` by
    metis_tac[emitted_insts_append, inst_extends_trans, inst_extends_def] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule run_inst_seq_mem_ok_append >>
  simp[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
  qpat_x_assum `run_inst_seq_mem_ok (emitted_insts middle end_st) encoded` mp_tac >>
  simp[]
QED
Finalise log_scalar_tuple_mem_ok
