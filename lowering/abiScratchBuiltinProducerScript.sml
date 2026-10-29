(* TOP-LEVEL: actual physical scratch execution produces an owned Bytes input
   for either a fresh tuple allocation or an existing outer tuple buffer.
   Allocation rows and alloca_inv establish separation; output bytes come from
   execution, with no assumed final layout or numeric-arena separation. *)
Theory abiScratchBuiltinProducer
Ancestors
  abiScratchBuiltinCaller abiScratchBuiltinRun abiScratchBuiltinPre abiScratchBuiltinEffect
  abiScratchFootprint abiBuiltinEncodeProducer abiBuiltinEncodeReusedInput abiBuiltinEncodeRun
  abiBuiltinAllocation abiTupleEncodeOwnedBytes abiTupleEncodeInput abiEncoderInput
  abiDecoderAllocation abiDecoderReentry abiDecoderContract abiDecoderLoop compileEnv builtinAbi
  exprLowering valueEncoding vyperABI contractABI venomMemDefs venomState venomExecSemantics
  finite_map pred_set words list arithmetic

Theorem abi_scratch_builtin_producer_bounds:
  p+(maxlen+32+(case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4)) < dimword (:256) /\
  payload_size <= maxlen ==>
  p < dimword (:256) /\ maxlen+LENGTH (abi_builtin_encode_prefix method_id_opt) < dimword (:256) /\
  LENGTH (abi_builtin_encode_prefix method_id_opt)+payload_size <=
    maxlen+LENGTH (abi_builtin_encode_prefix method_id_opt)
Proof
  Cases_on `method_id_opt` >> simp[abi_scratch_builtin_prefix_length] >> decide_tac
QED

Theorem abi_scratch_builtin_producer_site:
  site < first ==> ~(site IN abi_decoder_ids first last)
Proof
  simp[abi_decoder_ids_def] >> decide_tac
QED

Theorem abi_scratch_builtin_producer_frontier:
  alloca_next_valid s /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  abi_scratch_builtin_effect first last st final limit_st p outsz write_size b cap s t ==>
  p+outsz <= t.vs_alloca_next
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_allocate_frontier >> disch_then assume_tac >>
  qpat_assum `abi_scratch_builtin_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o
      PURE_REWRITE_RULE [abi_scratch_builtin_effect_def, abi_scratch_evolution_def]) >>
  irule LESS_EQ_TRANS >>
  qexists_tac `(abi_builtin_allocate_state st.cs_next_id outsz s).vs_alloca_next` >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_builtin_producer_input:
  p < dimword (:256) /\ type_memory_bytes ce (BaseT (BytesT (Dynamic n))) < dimword (:256) /\
  abi_decoder_operand_live next op /\ eval_operand op s = SOME (n2w p) /\
  mload p s = n2w (LENGTH bytes) /\ mem_bytes_at (p+32) (LENGTH bytes) s.vs_memory = bytes /\
  LENGTH bytes <= n /\ n < dimword (:256) /\ (p+(n+32) <= lo \/ hi <= p) ==>
  abi_tuple_encode_input sf ce (BaseT (BytesT (Dynamic n)))
    (vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))) (contractABI$BytesV bytes)
    op next lo hi s
Proof
  strip_tac >> irule abi_tuple_encode_owned_bytes_source_input >> asm_rewrite_tac[] >>
  qexists_tac `n2w p:bytes32` >> gvs[w2n_n2w, AC ADD_COMM ADD_ASSOC] >> decide_tac
QED

Theorem lower_abi_encode_scratch_produced_tuple_input:
  let outsz = maxlen+32+(case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4) in
  let allocated = abi_builtin_allocate_state start.cs_next_id outsz initial in
  let cap = allocated.vs_alloca_next+32*CARD (abi_decoder_missing first last allocated) in
  let n = maxlen+LENGTH (abi_builtin_encode_prefix method_id_opt) in
  let bytes = abi_builtin_encode_prefix method_id_opt ++ enc at av in
  lower_abi_encode ensure method_id_opt src (type_to_abi_enc_info sf ce ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv initial /\ cap < dimword (:256) /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_cap) /\ source_id <> start.cs_next_id /\
  ((FLOOKUP initial.vs_allocas start.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas start.cs_next_id = SOME (p,outsz)) /\
  start.cs_next_id < first /\ first <= start.cs_next_id+(case method_id_opt of NONE => 2 | SOME _ => 4) /\
  ~(source_id IN abi_decoder_ids first last) /\
  (!id off sz. id IN abi_decoder_ids first last /\
    FLOOKUP allocated.vs_allocas id = SOME (off,sz) ==> sz = 32) /\
  abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live start.cs_next_var src /\
  LENGTH (enc at av) <= maxlen /\
  (method_id_opt = NONE \/ sb+source_cap <= p+32 \/ p+64 <= sb) /\
  type_memory_bytes ce (BaseT (BytesT (Dynamic n))) < dimword (:256) /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH bytes) /\
    mem_bytes_at (p+32) (LENGTH bytes) actual.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic n))) (vyperValue$BytesV bytes) p actual.vs_memory /\
    FLOOKUP actual.vs_allocas start.cs_next_id = SOME (p,outsz) /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb source_cap actual.vs_memory /\
    abi_scratch_builtin_effect first last start final limit_st p outsz
      (case method_id_opt of NONE => 0 | SOME _ => 32) 0 cap initial actual /\
    (!hi. abi_tuple_encode_input consumer_sf ce (BaseT (BytesT (Dynamic n)))
      (vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))) (contractABI$BytesV bytes)
      out final.cs_next_var actual.vs_alloca_next hi actual) /\
    (!outer_id q outer_size.
      FLOOKUP initial.vs_allocas outer_id = SOME (q,outer_size) /\ outer_id <> start.cs_next_id /\
      (outer_id < start.cs_next_id \/ final.cs_next_id <= outer_id) ==>
      FLOOKUP actual.vs_allocas outer_id = SOME (q,outer_size) /\
      abi_tuple_encode_input consumer_sf ce (BaseT (BytesT (Dynamic n)))
        (vyper_to_abi_type env (BaseT (BytesT (Dynamic n)))) (contractABI$BytesV bytes)
        out final.cs_next_var q (q+outer_size) actual) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `alloca_inv initial`
    (assume_tac o CONJUNCT2 o PURE_REWRITE_RULE [alloca_inv_def]) >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
    (Q.INST [`st` |-> `start:compile_state`] abi_scratch_builtin_pre_caller))) >> disch_tac >>
  drule_all lower_abi_encode_scratch >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  drule abi_builtin_encode_output_live >> disch_then assume_tac >>
  qpat_assum `abi_scratch_builtin_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_scratch_builtin_pre_def, LET_THM]) >>
  drule_all abi_scratch_builtin_producer_bounds >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [GSYM LENGTH_APPEND]) >>
  mp_tac (Q.INST [`site` |-> `start.cs_next_id`, `first` |-> `first:num`, `last` |-> `last:num`]
    abi_scratch_builtin_producer_site) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then assume_tac >>
  drule_all abi_scratch_builtin_effect_output_row >> disch_then assume_tac >>
  drule_all abi_scratch_builtin_producer_frontier >>
  disch_then (assume_tac o PURE_REWRITE_RULE
    [GSYM abi_scratch_builtin_prefix_length, AC ADD_COMM ADD_ASSOC]) >>
  qexists_tac `actual` >> asm_rewrite_tac[] >> conj_tac
  >- (gen_tac >> irule abi_scratch_builtin_producer_input >> asm_rewrite_tac[] >>
      qexists_tac `p` >> asm_rewrite_tac[] >>
      qpat_assum `p+_ <= actual.vs_alloca_next` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[AC ADD_COMM ADD_ASSOC]) >>
  map_every qx_gen_tac [`outer_id`, `q`, `outer_size`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_allocate_separate >>
  disch_then (assume_tac o PURE_REWRITE_RULE
    [GSYM abi_scratch_builtin_prefix_length, AC ADD_COMM ADD_ASSOC]) >>
  qpat_assum `abi_scratch_builtin_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_builtin_effect_def]) >>
  `FLOOKUP actual.vs_allocas outer_id = SOME (q,outer_size)` by
    (qpat_x_assum `!id. id < start.cs_next_id \/ final.cs_next_id <= id ==> _`
       (qspec_then `outer_id` mp_tac) >> asm_simp_tac bool_ss []) >>
  asm_rewrite_tac[] >> irule abi_scratch_builtin_producer_input >> asm_rewrite_tac[] >>
  qexists_tac `p` >> asm_rewrite_tac[] >>
  qpat_assum `p+_ <= q \/ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> simp[AC ADD_COMM ADD_ASSOC]
QED
