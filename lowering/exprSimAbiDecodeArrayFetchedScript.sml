(* Fetched execution keeps the registered resource function separate from code. *)
Theory exprSimAbiDecodeArrayFetched
Ancestors
  exprSimAbiDecodeArraySetup exprSimAbiDecodeArrayBulk
  abiDecoderArrayInit abiDecoderArrayLoopInit abiDecoderSequenceReach
  abiDecoderSiteEffect abiDecoderContract instIdxIndep
  abiDecoderBulk abiDecoderBulkExecute abiDecoderBytestringOutcome
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderArrayHeader
  abiDecoderBytesBound abiDecoderCopy abiDecoderWordOutcome fragExec
  abiDecoderGuards abiDecoderComposition exprLoweringProps arithmetic pred_set
  abiDecoderIndexInit abiEncoder compileEnv emitHelper
  venomExecSemantics venomState venomInst valueEncoding
  vyperABI vyperValue contractABI words list rich_list

Theorem abi_decode_array_setup_fetched_outcome:
  abi_decode_dynarray_position_prefix src opc base_op hi maxn
    (abi_member_head_size at) st = (addr,guard_st) /\
  abi_decode_array_header dst addr opc guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_source_opcode opc /\ hi <> Lit 0w /\
  eval_operand src s = SOME(n2w pos) /\
  eval_operand base_op s = SOME(n2w b) /\
  eval_operand hi s = SOME(n2w h) /\
  eval_operand dst s = SOME(n2w d) /\ d < dimword(:256) /\
  abi_decode_load opc (n2w (b+pos):bytes32) s = n2w n /\
  n = w2n (mem_word_at (b+pos) s.vs_memory) /\
  bs = mem_bytes_at (b+pos) (h-pos) s.vs_memory /\
  pos < dimword(:256) /\ h < dimword(:256) /\ maxn < dimword(:256) /\
  (n <= maxn ==> n * abi_member_head_size at < dimword(:256)) /\
  fresh_vars_wrt st s /\ decode_site_resources ctx func s /\
  fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas output = SOME(root,outsz) /\
  d = root+off /\ off+32 <= outsz /\ output <> header_st.cs_next_id /\
  q+len <= s.vs_alloca_next /\
  venomMemDefs$regions_disjoint (q,len) (d,32) /\
  (!b sz. FLOOKUP s.vs_allocas header_st.cs_next_id = SOME(b,sz) ==>
    venomMemDefs$regions_disjoint (q,len) (b,sz)) /\
  MEM (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString header_st.cs_next_var)]) (fn_insts func) /\
  fn_has_code st loop_st fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (n <= maxn /\ pos+32+n*abi_member_head_size at <= h /\
   ?t p. decoder_straight_prefix fn s t /\
     t.vs_current_bb = loop_st.cs_current_bb /\
     t.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
     eval_operand ip t = SOME(n2w p) /\ eval_operand cnt t = SOME(n2w n) /\
     mload p t = 0w /\ mem_word_at d t.vs_memory = n2w n /\
     fresh_vars_wrt loop_st t /\
     decode_site_effect ctx func st.cs_next_var
       ({a | d <= a /\ a < d+32} UNION {a | p <= a /\ a < p+32}) s t /\
     FLOOKUP t.vs_allocas header_st.cs_next_id = SOME(p,32) /\
     (!id. id <> header_st.cs_next_id ==>
       FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
     mem_bytes_at q len t.vs_memory = mem_bytes_at q len s.vs_memory /\
     venomMemDefs$regions_disjoint (root,outsz) (p,32) /\ ~t.vs_halted) \/
  (?encoded ix. run_inst_seq (emitted_insts st loop_st) s = Abort Revert_abort encoded /\
    run_from 0 ctx fn s = Abort Revert_abort (encoded with vs_inst_idx := ix) /\
    ~(vyper_decode_valid_enc (Array NONE at) bs /\
      ?v. abi_to_vyper env (ArrayT ty (Dynamic maxn))
        (dec (Array NONE at) bs) = SOME v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_array_loop_init dst src opc base_op hi maxn
     (abi_member_head_size at) st = ((ip,cnt),loop_st)` by
    simp[abi_decode_array_loop_init_def, comp_bind_def, comp_return_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_array_setup_site_outcome >>
  disch_then (qspecl_then [`ty`, `env`] strip_assume_tac)
  >- (disj1_tac >> simp[] >>
      drule_all abi_decoder_run_sequence_prefix >> strip_tac >>
      qexistsl [`t'`, `p`] >>
      gvs[fresh_vars_wrt_def, eval_op_inst_idx, mload_def]) >>
  disj2_tac >> drule_all abi_decoder_run_sequence_abort >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  metis_tac[]
QED

(* Bulk memory decoding uses only the already-framed bytestring opcode set. *)
Theorem abi_decode_array_bulk_memory_opcodes:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei ==>
  EVERY (\i. abi_bytes_opcode i.inst_opcode \/ i.inst_opcode = MUL)
    (emitted_insts st st')
Proof
  strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  simp[abi_decode_bulk_phases, abi_decode_source_opcode_def,
       comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  gvs[abi_decode_dynarray_position_prefix_def, abi_decode_bytes_head_def,
      compile_abi_dec_addr_def, abi_decode_count_guard_def,
      abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
      abi_decode_bulk_body_def, abi_decode_array_header_def,
      abi_decode_bulk_payload_def, abi_decode_copy_opcode_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  gvs[DROP_LENGTH_APPEND, mk_inst_def, abi_bytes_opcode_def, abi_word_opcode_def]
QED

Theorem abi_decode_array_bulk_step_static[local]:
  (abi_bytes_opcode inst.inst_opcode \/ inst.inst_opcode = MUL) /\
  step_inst_base inst s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  disch_then (CONJUNCTS_THEN2 strip_assume_tac assume_tac)
  >- (drule_all abi_bytes_step_static >> simp[]) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  asm_rewrite_tac[venomInstTheory.opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def] >> simp[venom_state_component_equality]
QED

Theorem abi_decode_array_bulk_sequence_static:
  !insts s t. EVERY (\i. abi_bytes_opcode i.inst_opcode \/ i.inst_opcode = MUL) insts /\
  run_inst_seq insts s = OK t ==>
  t = s with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory|>
Proof
  Induct >> simp[run_inst_seq_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  `v = s with <|vs_vars := v.vs_vars; vs_memory := v.vs_memory|>` by
    metis_tac[abi_decode_array_bulk_step_static] >>
  first_x_assum drule_all >> strip_tac >>
  fs[venom_state_component_equality]
QED

Theorem abi_decode_array_bulk_success_effect:
  compile_abi_decode_to_buf dst src MLOAD base_op hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\
  eval_operand src s = SOME (n2w pos) /\ eval_operand dst s = SOME (n2w d) /\
  eval_operand base_op s = SOME (n2w b) /\
  abi_decode_load MLOAD (n2w (b+pos):bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword(:256) /\
  b+pos+32 < dimword(:256) /\ d+32 < dimword(:256) /\
  n*mem_sz < dimword(:256) /\
  (b+pos+32+n*mem_sz <= d \/ d+32 <= b+pos+32) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME(n2w h) /\
    pos+32+n*abi_sz <= h /\ h < dimword(:256)) /\
  fresh_vars_wrt st s /\ decode_site_resources ctx func s /\
  {a | d <= a /\ a < d+32+n*mem_sz} SUBSET writes ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = n2w n /\
    mem_bytes_at (d+32) (n*mem_sz) t.vs_memory =
      mem_bytes_at (b+pos+32) (n*mem_sz) s.vs_memory /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    decode_site_effect ctx func next writes s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decode_bulk_sequence >>
  disch_then (qspecl_then [`b`, `pos`, `s`, `n`, `d`] mp_tac) >>
  (impl_tac >- (simp[] >> disj2_tac >> qexists `h` >>
    simp[] >> once_rewrite_tac[MULT_COMM] >> decide_tac)) >> strip_tac >>
  drule_all abi_decode_array_bulk_memory_opcodes >> strip_tac >>
  drule_all abi_decode_array_bulk_sequence_static >> strip_tac >>
  `decode_static_frame s t` by
    fs[decode_static_frame_def, venom_state_component_equality] >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_fmp = s.vs_fmp` by fs[venom_state_component_equality] >>
  qpat_x_assum `t = s with <|vs_vars := _; vs_memory := _|>` kall_tac >>
  `decode_site_resources ctx func t` by metis_tac[decode_site_resources_fields] >>
  `0 < 32+n*mem_sz` by simp[] >>
  `decode_memory_frame writes s t` by
    (irule abi_bytes_frame_memory >> qexistsl [`32+n*mem_sz`, `d`] >>
     pure_rewrite_tac[ADD_ASSOC] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexists `t` >> simp[decode_site_effect_def, abi_decode_source_def]
QED
