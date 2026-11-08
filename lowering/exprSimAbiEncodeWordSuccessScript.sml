Theory exprSimAbiEncodeWordSuccess
Ancestors
  exprSimAbiEncodeStagedObserver exprSimAbiEncodePrefixWindow
  abiBuiltinEncodeWord abiBuiltinAllocation exprSimHash abiDecoderGuards context emitHelper emitHelperProps
  exprLoweringProps compileEnv venomState venomInst list rich_list
  abiBuiltinEncodeCode abiCopyExecution abiEncoder
  words finite_map compileEnv venomMemDefs
  exprSimAbiEncodeBoundaryProbe exprSimAbiEncodeTranslatedNoBlock
  abiEncoderCounters abiBuiltinEncodeSetup abiDecoderReentry localPtrsProps
  abiTupleValueEncoding venomWf exprSimAbiEncodeSourceRoom

Theorem abi_encode_word_staging_path:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;op] sm = ((),sh) /\
  fn_has_code sa sh func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sm) s = OK allocated /\
  run_inst_seq (emitted_insts sm sh) allocated = OK staged ==>
  gas_marked_path F ctx func s 0
    (OK (staged with vs_inst_idx := LENGTH sh.cs_current_insts)) /\
  ~staged.vs_halted /\ staged.vs_current_bb = sh.cs_current_bb
Proof
  strip_tac >>
  drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  `inst_extends sm sh` by metis_tac[inst_extends_emit_void] >>
  `inst_extends sa sm` by metis_tac[inst_extends_emit_op] >>
  `run_inst_seq (emitted_insts sa sh) s = OK staged` by
    (irule run_inst_seq_compose_ok >>
     qexistsl_tac [`allocated`, `sm`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh` by
    (fs[inst_extends_def]) >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sh)) = 0` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     fs[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC, mk_inst_def]) >>
  drule_all hash_run_path >> disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

Theorem abi_encode_word_encoder_no_blocks:
  is_word_type ty /\
  lower_abi_encode ensure mid src (type_to_abi_enc_info sf ce ty) maxlen st = (out,final) ==>
  final.cs_blocks = st.cs_blocks /\ final.cs_current_bb = st.cs_current_bb
Proof
  strip_tac >>
  `type_to_abi_enc_info sf ce ty = AbiCopy 32` by
    (irule (cj 2 abi_builtin_encode_word_info) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `lower_abi_encode _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac [] >> strip_tac >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp[compile_abi_copy_shape, compile_copy_memory_dynamic_def,
    emit_void_def, emit_def, fresh_id_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[]
QED

Theorem abi_encode_word_allocation_geometry:
  abi_builtin_encode_setup mid 32 st = (ops,ready) /\
  fn_has_code st ready func /\ stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas source_id = SOME (sb,32) /\
  source_id <> st.cs_next_id ==>
  let m = case mid of NONE => 0 | SOME _ => 4 in
  let w = case mid of NONE => 0 | SOME _ => 32 in
  let outsz = 32+32*word_size (32+m) in
  let a = abi_builtin_allocate_state st.cs_next_id outsz s in
  alloca_inv a /\ alloca_room ctx func a /\ sb+32 <= a.vs_alloca_next /\
  ?p. ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
       FLOOKUP s.vs_allocas st.cs_next_id = SOME(p,outsz)) /\
    outsz < dimword (:256) /\ p < dimword (:256) /\
    (mid <> NONE ==> p+32 < dimword (:256)) /\
    p+(32+m)+32 <= a.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,32) (p+(32+m),32) /\
    (sb+32 <= p+32 \/ p+32+w <= sb) /\
    venomMemDefs$regions_disjoint (p+32,m) (p+(32+m),32) /\
    32+w <= outsz /\ p <= p+(32+m) /\ p+(32+m)+32 <= p+outsz
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `32+32*word_size (32+(case (mid:bytes32 option) of NONE => 0 | SOME _ => 4))
    < dimword (:256)` by
    (Cases_on `mid` >> simp[vfmConstantsTheory.word_size_def, dimword_def]) >>
  drule_all (SRULE [] (Q.INST [`maxlen` |-> `32`] abi_encode_word_setup_resources)) >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `alloca_inv a` >>
  `FLOOKUP a.vs_allocas source_id = SOME(sb,32)` by
    simp[Abbr `a`, abiEncodeWindowBuiltinTheory.abi_window_allocate_other_row] >>
  `sb+32 <= p \/ p+(32+32*word_size (32+(case mid of NONE => 0 | SOME _ => 4))) <= sb` by
    (fs[alloca_inv_def, allocas_non_overlapping_def] >>
     first_x_assum drule_all >> simp[]) >>
  `a.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt] >>
  `((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas st.cs_next_id = SOME(p,32+32*word_size
      (32+(case mid of NONE => 0 | SOME _ => 4))))` by
    (qpat_x_assum `FLOOKUP a.vs_allocas st.cs_next_id = _` mp_tac >>
     Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
     simp[Abbr `a`, abi_builtin_allocate_state_def, FLOOKUP_UPDATE] >>
     Cases_on `x` >> simp[]) >>
  qexists_tac `p` >>
  Cases_on `mid` >>
  gvs[vfmConstantsTheory.word_size_def, venomMemDefsTheory.regions_disjoint_def]
QED

Theorem abi_encode_word_staged_observer:
  is_word_type ty /\
  abi_builtin_encode_setup mid 32 st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src (type_to_abi_enc_info sf ce ty)
    ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len
    (case mid of NONE => 0 | SOME _ => 4) body_end = ((),final) /\
  fn_has_code st ready func /\
  fn_has_code st ready obs /\ fn_has_code ready body_end obs /\
  fn_has_code body_end final obs /\ fn_inst_ids_distinct obs /\
  obs.fn_name = func.fn_name /\
  stmt_state_rel ctx func ce cx es initial /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\
  FLOOKUP initial.vs_allocas source_id = SOME(sb,32) /\ source_id <> st.cs_next_id /\
  abi_encoder_window_input (type_to_abi_enc_info sf ce ty) at av sb 32 initial.vs_memory /\
  LENGTH (enc at av) = 32 /\ eval_operand src initial = SOME(n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!j. MEM j (fn_insts obs) /\ j.inst_opcode <> STOP /\ j.inst_opcode <> NOP ==>
    MEM j (fn_insts func)) /\
  (!j. MEM j (fn_insts obs) ==> j.inst_opcode <> INVOKE) ==>
  ?p actual. abi_decode_sim ctx obs initial actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_exec_frame obs initial actual /\
    abi_encode_staged_observation ctx func ce cx es st (FST ops) mid
      (32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4))) p at av initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_word_allocation_geometry >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_translated_operand_liveness >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var` by
    (qpat_assum `ready.cs_next_var = _` mp_tac >> Cases_on `mid` >> simp[] >> decide_tac) >>
  `abi_encoder_admissible (type_to_abi_enc_info sf ce ty)` by
    (`type_to_abi_enc_info sf ce ty = AbiCopy 32` by
       (irule (cj 2 abi_builtin_encode_word_info) >> first_assum ACCEPT_TAC) >>
     asm_rewrite_tac [] >> simp[abiEncoderAdmissibleTheory.abi_encoder_admissible_def]) >>
  `alloca_room (ctx with ctx_functions := [obs]) obs
    (abi_builtin_allocate_state st.cs_next_id
      (32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4))) initial)` by
    (irule abi_encode_bridge_local_room >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexists_tac `func` >> asm_rewrite_tac []) >>
  `!inst. MEM inst (fn_insts obs) /\ inst.inst_id IN frag_ids ready body_end ==>
    inst.inst_opcode <> ALLOCA` by
    metis_tac[abi_encode_word_body_no_alloca] >>
  qexists_tac `p` >>
  irule abi_encode_staged_observer >>
  qpat_assum `abi_builtin_encode_setup _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `abi_builtin_encode_finish _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `abi_encoder_window_input _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`case mid of NONE => 0 | SOME _ => 32`, `limit_st`,
    `p+32+(case mid of NONE => 0 | SOME _ => 4)`] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
  asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >>
  rpt strip_tac >> metis_tac[]
QED
