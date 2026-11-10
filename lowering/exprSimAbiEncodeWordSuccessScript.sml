Theory exprSimAbiEncodeWordSuccess
Ancestors
  exprSimHashBoundary
    loweringStateRelDefs
  exprSimAbiEncodeStagedObserver exprSimAbiEncodePrefixWindow exprSimAbiEncodeStagedFrame
  abiBuiltinEncodeWord abiBuiltinAllocation exprSimHash abiDecoderGuards context emitHelper emitHelperProps
  exprLoweringProps compileEnv venomState venomInst list rich_list
  abiBuiltinEncodeCode abiEncoder copyExecution
  words finite_map compileEnv venomMemDefs
  exprSimAbiEncodeBoundaryProbe exprSimAbiEncodeTranslatedNoBlock
  abiEncoderCounters abiBuiltinEncodeSetup abiDecoderReentry localPtrsProps
  abiTupleValueEncoding venomWf exprSimAbiEncodeSourceRoom
  exprSimAbiEncodeTranslatedPhases exprSimAbiEncodeCallerSuffix
  exprSimAbiEncodeExecFrame exprSimAbiEncodeStateTransport
  exprSimAbiEncodeNoBlockBoundary exprSimAbiEncodeNoBlockSafety
  exprSimAbiEncodeOblivious exprSimAbiGasBridge exprSimAlloc fragExec
  exprSimAbiEncodeOriginFrame loweringPosts

Theorem compile_abi_copy_shape[local]:
  compile_abi_encode_to_buf dst src (AbiCopy n) cs = (result,cs') <=>
  result = Lit (n2w n) /\
  compile_copy_memory_dynamic dst src (Lit (n2w n)) cs = ((),cs')
Proof
  simp[Once compile_abi_encode_child_def, compile_copy_memory_dynamic_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `emit_void MCOPY [dst;src;Lit (n2w n)] cs` >> simp[] >> metis_tac[]
QED

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

Theorem abi_encode_word_no_block_phases:
  is_word_type ty /\
  abi_builtin_encode_setup mid 32 st = (ops,ready) /\
  compile_abi_encode_to_buf (SND ops) src (type_to_abi_enc_info sf ce ty)
    ready = (len,body_end) /\
  abi_builtin_encode_finish (FST ops) len
    (case mid of NONE => 0 | SOME _ => 4) body_end = ((),final) /\
  fn_has_code st ready func /\ fn_has_code ready body_end func /\
  fn_has_code body_end final func /\ fn_inst_ids_distinct func /\
  st.cs_blocks = final.cs_blocks /\
  stmt_state_rel ctx func ce cx es initial /\ local_ptrs_reserved ce st /\
  FLOOKUP initial.vs_allocas source_id = SOME(sb,32) /\ source_id <> st.cs_next_id /\
  abi_encoder_window_input (type_to_abi_enc_info sf ce ty) at av sb 32 initial.vs_memory /\
  LENGTH (enc at av) = 32 /\ eval_operand src initial = SOME(n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?p raw. run_inst_seq (emitted_insts st final) initial = OK raw /\
    let actual = raw with vs_inst_idx := LENGTH final.cs_current_insts in
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    abi_encode_exec_frame func initial actual /\
    abi_encode_staged_observation ctx func ce cx es st (FST ops) mid
      (32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4))) p at av initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_word_allocation_geometry >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_translated_operand_liveness >> strip_tac >>
  `abi_encoder_admissible (type_to_abi_enc_info sf ce ty)` by
    (`type_to_abi_enc_info sf ce ty = AbiCopy 32` by
       (irule (cj 2 abi_builtin_encode_word_info) >> first_assum ACCEPT_TAC) >>
     asm_rewrite_tac [] >> simp[abiEncoderAdmissibleTheory.abi_encoder_admissible_def]) >>
  `!inst. MEM inst (fn_insts func) /\ inst.inst_id IN frag_ids ready body_end ==>
    inst.inst_opcode <> ALLOCA` by metis_tac[abi_encode_word_body_no_alloca] >>
  `?raw. run_inst_seq (emitted_insts st final) initial = OK raw /\
    let actual = raw with vs_inst_idx := LENGTH final.cs_current_insts in
    eval_operand (FST ops) actual = SOME(n2w p) /\
    mload p actual = n2w (LENGTH(enc at av)+(case mid of NONE => 0 | SOME _ => 4)) /\
    mem_bytes_at (p+32+(case mid of NONE => 0 | SOME _ => 4)) (LENGTH(enc at av)) actual.vs_memory = enc at av /\
    (case mid of NONE => T | SOME selector => mem_bytes_at (p+32) 4 actual.vs_memory = abi_builtin_encode_method_bytes selector) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_exec_frame func initial actual /\
    ?prepared body_state.
      abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id
        (32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4))) p
        (case mid of NONE => 0 | SOME _ => 32) initial prepared /\
      window_strong_result ctx func ready body_end len at av
        (p+32+(case mid of NONE => 0 | SOME _ => 4)) prepared body_state /\
      abi_encoder_registered_effect {} [(p,32)] body_state actual /\
      actual.vs_allocas = body_state.vs_allocas /\
      actual.vs_alloca_next = body_state.vs_alloca_next /\
      (!op v. abi_decoder_operand_live body_end.cs_next_var op /\
        eval_operand op body_state = SOME v ==> eval_operand op actual = SOME v) /\
      prepared.vs_accounts = initial.vs_accounts /\ prepared.vs_transient = initial.vs_transient /\
      prepared.vs_logs = initial.vs_logs /\ prepared.vs_requests = initial.vs_requests /\
      prepared.vs_pending_deletions = initial.vs_pending_deletions /\ actual.vs_labels = initial.vs_labels` by
    (irule abi_encode_translated_concrete_phases >>
     qpat_assum `abi_builtin_encode_setup _ _ _ = _` (irule_at Any) >>
     qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `abi_builtin_encode_finish _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `abi_encoder_window_input _ _ _ _ _ _` (irule_at Any) >>
     RULE_ASSUM_TAC (PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
     `32 <> 0 /\ 0 < (32:num)` by decide_tac >>
     asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >> rpt strip_tac >>
     metis_tac[arithmeticTheory.ADD_ASSOC]) >>
  qpat_x_assum `let actual = _ in _`
    (strip_assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  qmatch_asmsub_abbrev_tac `abi_encode_exec_frame func initial actual` >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `st.cs_next_var <= ready.cs_next_var /\ st.cs_next_var <= body_end.cs_next_var` by
    (qpat_assum `ready.cs_next_var = _` mp_tac >> Cases_on `mid` >> simp[] >> decide_tac) >>
  drule_all abi_encode_caller_phase_allocations >> strip_tac >>
  `stmt_state_rel ctx func ce cx es actual /\
   (!name b n. local_region ce es.scopes initial name b n ==>
     mem_bytes_at b n actual.vs_memory = mem_bytes_at b n initial.vs_memory) /\
   FLOOKUP actual.vs_allocas st.cs_next_id =
     SOME(p,32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4))) /\
   p+(32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4))) <= actual.vs_alloca_next /\
   actual.vs_alloca_next < dimword (:256)` by
    (irule abi_encode_phases_caller_state >>
     qpat_assum `abi_builtin_encode_setup _ _ _ = _` (irule_at Any) >>
     qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     RULE_ASSUM_TAC (PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
     asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >> rpt strip_tac >>
     metis_tac[arithmeticTheory.ADD_ASSOC]) >>
  `alloca_inv actual` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ actual` mp_tac >>
     simp_tac bool_ss [stmt_state_rel_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `st.cs_next_id <= ready.cs_next_id` by
    (qpat_assum `ready.cs_next_id = _` (fn th => rewrite_tac[th]) >>
     Cases_on `mid` >> simp[]) >>
  `!aid off sz. FLOOKUP initial.vs_allocas aid = SOME(off,sz) /\ aid < st.cs_next_id ==>
    mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz initial.vs_memory` by
    (rpt gen_tac >> strip_tac >> irule abi_encode_caller_phase_old_rows >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qexists_tac `aid` >>
     RULE_ASSUM_TAC (PURE_REWRITE_RULE [arithmeticTheory.ADD_ASSOC]) >>
     asm_rewrite_tac [arithmeticTheory.ADD_ASSOC] >> metis_tac[arithmeticTheory.ADD_ASSOC]) >>
  `!x v. not_fresh_at st x /\ lookup_var x initial = SOME v ==>
    lookup_var x actual = SOME v` by
    (rpt gen_tac >> strip_tac >>
     `abi_decoder_operand_live st.cs_next_var (Var x)` by
       (qpat_assum `not_fresh_at st x` mp_tac >>
        simp_tac (srw_ss()) [abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF]) >>
     irule abi_encode_caller_phase_registers >>
     qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `window_strong_result _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `abi_encode_exec_frame func initial actual` mp_tac >>
  simp_tac bool_ss [abi_encode_exec_frame_def] >> strip_tac >>
  qexistsl_tac [`p`, `raw`] >>
  simp_tac bool_ss [LET_THM] >>
  qpat_x_assum `Abbrev (actual = _)`
    (fn th => rewrite_tac[GSYM (PURE_REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  rewrite_tac [abi_encode_staged_observation_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_word_no_block_run:
  is_word_type ty /\
  lower_abi_encode F mid src (type_to_abi_enc_info sf ce ty) 32 st = (out,final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es initial /\ local_ptrs_reserved ce st /\
  FLOOKUP initial.vs_allocas source_id = SOME(sb,32) /\ source_id <> st.cs_next_id /\
  abi_encoder_window_input (type_to_abi_enc_info sf ce ty) at av sb 32 initial.vs_memory /\
  LENGTH (enc at av) = 32 /\ eval_operand src initial = SOME(n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?p raw. run_inst_seq (emitted_insts st final) initial = OK raw /\
    let actual = raw with vs_inst_idx := LENGTH final.cs_current_insts in
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    abi_encode_exec_frame func initial actual /\
    abi_encode_staged_observation ctx func ce cx es st out mid
      (32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4))) p at av initial actual
Proof
  strip_tac >>
  drule_all abi_encode_word_encoder_no_blocks >> strip_tac >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  `cs_extends st ready` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `cs_extends ready body_end` by metis_tac[abiEncoderAppendTheory.cs_extends_abi_encode] >>
  `cs_extends body_end final` by
    (irule cs_extends_same_block >> fs[inst_extends_def]) >>
  `fn_has_code st ready func /\ fn_has_code ready body_end func /\
   fn_has_code body_end final func` by
    metis_tac[fragExecTheory.fn_has_code_split, cs_extends_trans] >>
  `st.cs_blocks = final.cs_blocks` by metis_tac[] >>
  drule_all abi_encode_word_no_block_phases >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  qexistsl_tac [`p`, `raw`] >> simp_tac bool_ss [LET_THM] >>
  asm_rewrite_tac[]
QED

Theorem abi_encode_word_no_block_observer:
  is_word_type ty /\
  lower_abi_encode F mid src (type_to_abi_enc_info sf ce ty) 32 st = (out,final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es initial /\ local_ptrs_reserved ce st /\
  FLOOKUP initial.vs_allocas source_id = SOME(sb,32) /\ source_id <> st.cs_next_id /\
  abi_encoder_window_input (type_to_abi_enc_info sf ce ty) at av sb 32 initial.vs_memory /\
  LENGTH (enc at av) = 32 /\ eval_operand src initial = SOME(n2w sb) /\
  (!x. src = Var x ==> not_fresh_at st x) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\ fn_has_code st final observer ==>
  ?p actual. abi_decode_sim ctx observer initial actual /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_exec_frame func initial actual /\
    abi_encode_staged_observation ctx func ce cx es st out mid
      (32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4))) p at av initial actual
Proof
  strip_tac >> drule_all abi_encode_word_no_block_run >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_encode_word_encoder_no_blocks >> strip_tac >>
  `st.cs_blocks = final.cs_blocks` by metis_tac[] >>
  drule_all lower_abi_encode_no_blocks_safe >> strip_tac >>
  drule_all lower_abi_encode_no_block_run_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`p`, `raw with vs_inst_idx := LENGTH final.cs_current_insts`] >>
  gvs[]
QED

Theorem abi_encode_word_counted_encoder:
  is_word_type ty /\
  lower_abi_encode F mid src (type_to_abi_enc_info sf ce ty) 32 st = (out,final) /\
  fn_has_code st final func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es initial /\ local_ptrs_reserved ce st /\
  FLOOKUP initial.vs_allocas source_id = SOME(sb,32) /\ source_id <> st.cs_next_id /\
  abi_encoder_window_input (type_to_abi_enc_info sf ce ty) at av sb 32 initial.vs_memory /\
  LENGTH (enc at av) = 32 /\ eval_operand src initial = SOME(n2w sb) /\
  (!l. src <> Label l) /\ (!x. src = Var x ==> not_fresh_at st x) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?p actual. gas_marked_path F ctx func initial 0 (OK actual) /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_staged_observation ctx func ce cx es st out mid
      (32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4))) p at av initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all lower_abi_encode_frag_facts >> strip_tac >>
  drule_all abi_encode_word_encoder_no_blocks >> strip_tac >>
  qabbrev_tac `Q = \actual. ?p.
    abi_encode_staged_observation ctx func ce cx es st out mid
      (32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4))) p at av initial actual` >>
  `!t rd. Q t ==> Q (t with vs_returndata := rd)` by
    simp[Abbr `Q`] >>
  `?t. gas_marked_path F ctx func initial 0 (OK t) /\ Q t /\ ~t.vs_halted /\
    t.vs_current_bb = final.cs_current_bb /\ t.vs_inst_idx = LENGTH final.cs_current_insts`
    suffices_by
    (strip_tac >> qpat_x_assum `Q t` mp_tac >>
     simp_tac bool_ss [Abbr `Q`] >> strip_tac >>
     qexistsl_tac [`p`, `t`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  irule exprSimAbiGasBridgeTheory.abi_decode_sim_gas_path >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `st` >> reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encode_word_no_block_observer >> strip_tac >>
  qexists_tac `actual` >> asm_rewrite_tac[] >>
  simp_tac bool_ss [Abbr `Q`] >> qexists_tac `p` >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_word_staged_counted:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ vyper_to_abi (get_tenv cx) (expr_type e) v = SOME av /\
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;op] sm = ((),sh) /\
  lower_abi_encode F mid buf.buf_operand
    (type_to_abi_enc_info sf ce (expr_type e)) 32 sh = (out,final) /\
  fn_has_code sa sh func /\ fn_has_code sh final func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  local_ptrs_reserved ce origin /\ origin.cs_next_var <= sa.cs_next_var /\
  origin.cs_next_id <= sa.cs_next_id /\ MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p ct rv initial actual.
    gas_marked_path F ctx func s 0 (OK initial) /\
    gas_marked_path F ctx func initial 0 (OK actual) /\
    enc ct rv = enc (vyper_to_abi_type (get_tenv cx) (expr_type e)) av /\
    LENGTH (enc ct rv) = 32 /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    abi_encode_staged_observation ctx func ce cx es' sh out mid
      (32+32*word_size(32+(case mid of NONE => 0 | SOME _ => 4)))
      p ct rv initial actual /\ wb_frame ce es es' origin s0 actual
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  `fn_has_code sa sm func` by
    (irule (cj 1 fn_has_code_split) >> conj_tac
     >- (qpat_x_assum `emit_op ALLOCA _ sa = _` mp_tac >>
         simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
           emit_def, comp_return_def] >> strip_tac >> gvs[] >>
         irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
     qexists_tac `sh` >> asm_rewrite_tac[] >>
     qpat_x_assum `emit_void MSTORE _ sm = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
       emit_def, comp_return_def] >> strip_tac >> gvs[] >>
     irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all abi_encode_word_expr_post >> strip_tac >>
  drule_all abi_builtin_encode_word_stage_shape >> strip_tac >>
  drule_all abi_encode_word_source_window >>
  disch_then (qspecl_then [`sf`, `ce`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func ce cx es' staged` >>
  drule_all abi_encode_word_staging_path >> strip_tac >>
  qabbrev_tac `initial = staged with vs_inst_idx := LENGTH sh.cs_current_insts` >>
  `local_ptrs_reserved ce sh` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `FLOOKUP initial.vs_allocas sa.cs_next_id = SOME(w2n addr,32)` by
    simp[Abbr `initial`, Abbr `staged`, mstore_def] >>
  `sa.cs_next_id <> sh.cs_next_id` by decide_tac >>
  `stmt_state_rel ctx func ce cx es' initial /\
   abi_encoder_window_input (type_to_abi_enc_info sf ce (expr_type e))
     ct rv (w2n addr) 32 initial.vs_memory /\
   LENGTH (enc ct rv) = 32 /\
   eval_operand buf.buf_operand initial = SOME(n2w (w2n addr)) /\
   ~initial.vs_halted /\ initial.vs_current_bb = sh.cs_current_bb /\
   initial.vs_inst_idx = LENGTH sh.cs_current_insts` by
    (simp[Abbr `initial`, stmt_state_rel_inst_idx] >>
     simp[Abbr `staged`, mstore_def, eval_operand_def] >>
     Cases_on `buf.buf_operand` >> gvs[eval_operand_def]) >>
  `(!l. buf.buf_operand <> Label l) /\
   (!x. buf.buf_operand = Var x ==> not_fresh_at sh x)` by
    (qpat_x_assum `emit_op ALLOCA _ sa = _` mp_tac >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `buf.buf_operand` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `stmt_state_rel ctx func ce cx es' s /\
   eval_operand op s = SOME(typed_val_to_w256 tv v)` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  drule_all hash_alloc_mstore_frame >> strip_tac >>
  `run_inst_seq (emitted_insts sa sh) s = OK staged` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`allocated`, `sm`] >>
     metis_tac[inst_extends_emit_op, inst_extends_emit_void]) >>
  `t = staged` by gvs[] >>
  qpat_x_assum `t = staged` SUBST_ALL_TAC >>
  `wb_frame ce es es' origin s0 staged` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_then Any irule abi_encode_nonword_origin_frame) >>
     simp[] >> metis_tac[]) >>
  `wb_frame ce es es' origin s0 initial` by
    (qunabbrev_tac `initial` >>
     qpat_assum `wb_frame _ _ _ _ _ staged` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[wb_frame_def, lookup_var_def, locals_kept_def] >>
     metis_tac[]) >>
  drule_all abi_encode_word_counted_encoder >> strip_tac >>
  `origin.cs_next_var <= sh.cs_next_var /\
   origin.cs_next_id <= sh.cs_next_id` by decide_tac >>
  drule_all abi_encode_staged_origin_frame >> strip_tac >>
  qexistsl_tac [`p`, `ct`, `rv`, `initial`, `actual`] >>
  asm_rewrite_tac[] >> simp[Abbr `initial`]
QED
