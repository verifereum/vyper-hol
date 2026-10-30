Theory abiBuiltinEncodeCorrect
Ancestors
  abiBuiltinAllocation abiBuiltinEncodeSetup abiDecoderEffect compileEnv venomState finite_map
  abiBuiltinEncodeCode abiEncoderWrites abiBuiltinPrefix abiEncoderBytesPrefix
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderReentryAddress abiDecoderFrameCompose
  abiDecoderFrame abiDecoderArrayInitExec abiDecoderContract abiDecoderGuards
  abiDecoderArrayHeader emitHelperProps exprLoweringProps emitHelper venomExecSemantics
  venomMemProps words list arithmetic abiEncoderSequence abiDecoderCorrectLeaves abiDecoderLoop
  fragExec instIdxIndep abiEncoderComplexDynamic abiDecoderAllocation abiEncoderCorrectRecursive
  abiEncoderCorrect abiEncoderAppend abiEncoderCounters abiDecoderAppend exprLowering
  valueEncoding abiBuiltinEncodePre abiBuiltinEncodeContext abiBuiltinDecodeEffect
  abiEncoderInput builtinAbi valueEncodingProps

(* TOP-LEVEL: preserve the actual output allocation through encoder execution.
   Fresh allocation and reuse both retain the same physical allocation row. *)
Theorem abi_builtin_allocate_state_row:
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas site = SOME (p,outsz)) ==>
  FLOOKUP (abi_builtin_allocate_state site outsz s).vs_allocas site = SOME (p,outsz)
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]
QED

Theorem abi_builtin_allocation_frame_row:
  abi_builtin_allocation_frame next site outsz s t /\
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas site = SOME (p,outsz)) ==>
  FLOOKUP t.vs_allocas site = SOME (p,outsz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_allocate_state_row >>
  fs[abi_builtin_allocation_frame_def]
QED

Theorem abi_builtin_encode_setup_frame_row:
  abi_builtin_encode_setup_frame next site outsz p write_size s t /\
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas site = SOME (p,outsz)) ==>
  FLOOKUP t.vs_allocas site = SOME (p,outsz)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_allocate_state_row >>
  fs[abi_builtin_encode_setup_frame_def]
QED

Theorem abi_builtin_encode_body_allocation_row:
  abi_decoder_effect first last lo hi next limit_st d sz b cap s t /\
  (site < lo \/ hi <= site) /\ FLOOKUP s.vs_allocas site = SOME (p,outsz) ==>
  FLOOKUP t.vs_allocas site = SOME (p,outsz)
Proof
  simp_tac bool_ss [abi_decoder_effect_def, abi_decoder_scratch_frame_def] >>
  strip_tac >>
  qpat_x_assum `!id. id < lo \/ hi <= id ==> _` (qspec_then `site` mp_tac) >> simp[]
QED

(* ===== Sequence ===== *)

(* Execute the actual builtin length store, preserving old operands and all
   memory outside the length word. Supports a method-ID prefix of any size. *)

Theorem abi_builtin_store_sequence:
  emit_void MSTORE [buf;value_op] st = ((),final) /\
  eval_operand buf s = SOME (n2w p) /\ eval_operand value_op s = SOME w /\
  p < dimword (:256) /\ fresh_vars_wrt limit_st s ==>
  run_inst_seq (emitted_insts st final) s = OK (mstore p w s) /\ inst_extends st final /\
  fresh_vars_wrt limit_st (mstore p w s) /\ mload p (mstore p w s) = w /\
  abi_decode_frame p 32 s (mstore p w s) /\
  (mstore p w s).vs_allocas = s.vs_allocas /\
  (mstore p w s).vs_alloca_next = s.vs_alloca_next /\
  (mstore p w s).vs_halted = s.vs_halted /\
  (!op. eval_operand op (mstore p w s) = eval_operand op s)
Proof
  strip_tac >> drule_all abi_encoder_emit_store >>
  simp[abi_decode_mstore_frame, mload_mstore_same, eval_operand_mstore]
QED

Theorem abi_builtin_encode_finish_sequence:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\
  eval_operand buf initial = SOME (n2w p) /\ eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\
  p < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\ inst_extends st final /\
    fresh_vars_wrt limit_st actual /\ mload p actual = n2w (len+mid_size) /\
    abi_decode_frame p 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w)
Proof
  Cases_on `mid_size > 0`
  >- (asm_simp_tac bool_ss [abi_builtin_encode_finish_def, comp_bind_def, LET_THM] >>
      pairarg_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[] >>
      rename1 `emit_op ADD [encoded_len;Lit (n2w mid_size)] st = (total_op,prepared_st)` >>
      imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
      `prepared_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
      mp_tac (Q.INST [`lhs` |-> `encoded_len`, `rhs` |-> `Lit (n2w mid_size)`,
        `out` |-> `total_op`, `a` |-> `n2w len:bytes32`, `b` |-> `n2w mid_size:bytes32`,
        `st'` |-> `prepared_st`, `s` |-> `initial:venom_state`] abi_builtin_emit_add) >>
      impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def] >> strip_tac >>
      rename1 `abi_builtin_prefix st prepared_st limit_st initial prepared` >>
      `eval_operand buf prepared = SOME (n2w p)` by
        (drule_all abi_encoder_prefix_eval >> simp[]) >>
      qpat_assum `abi_builtin_prefix _ _ _ _ _`
        (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
      mp_tac (Q.INST [`value_op` |-> `total_op`, `st` |-> `prepared_st`,
        `s` |-> `prepared:venom_state`, `w` |-> `n2w (len+mid_size):bytes32`] abi_builtin_store_sequence) >>
      impl_tac >- asm_simp_tac (srw_ss()) [word_add_n2w] >> strip_tac >>
      `run_inst_seq (emitted_insts st final) initial = OK (mstore p (n2w (len+mid_size)) prepared) /\
       inst_extends st final` by
        (mp_tac (Q.INST [`st1` |-> `prepared_st`, `st2` |-> `final`,
          `s` |-> `initial:venom_state`, `s1` |-> `prepared:venom_state`,
          `s2` |-> `mstore p (n2w (len+mid_size)) prepared`] abi_decode_sequence_chain) >>
         asm_simp_tac bool_ss []) >>
      qpat_assum `abi_decoder_address_frame _ _ _`
        (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
      `abi_decode_frame p 32 initial (mstore p (n2w (len+mid_size)) prepared)` by
        (irule abi_decode_frame_trans >> qexists_tac `prepared` >>
         asm_simp_tac bool_ss [abi_decode_frame_def]) >>
      qexists_tac `mstore p (n2w (len+mid_size)) prepared` >> asm_simp_tac bool_ss [] >>
      rpt strip_tac >> first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `mid_size = 0` by decide_tac >> gvs[abi_builtin_encode_finish_def] >> strip_tac >>
  drule_all abi_builtin_store_sequence >> strip_tac >>
  qexists_tac `mstore p (n2w len) initial` >> asm_simp_tac bool_ss []
QED

(* ===== Builtin Encode Finish ===== *)

(* The actual length store reaches its containing-function endpoint and
   preserves both the method-ID bytes and completed ABI payload. *)

Theorem abi_builtin_encode_finish_reach:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\ fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\ eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\
  p < dimword (:256) /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (len+mid_size) /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame p 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule_all abi_builtin_encode_finish_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st final) initial = OK encoded` >>
  `eval_operand buf encoded = SOME (n2w p)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  drule_all abi_encoder_run_sequence_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH final.cs_current_insts` >>
  gvs[abi_decode_frame_def, fresh_vars_wrt_def, eval_op_inst_idx, mload_def] >>
  first_assum ACCEPT_TAC
QED

Theorem abi_builtin_encode_finish:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\ fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\ eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\
  p < dimword (:256) /\ 32 <= output_size /\
  (p+output_size <= b \/ b+cap <= p) /\ abi_decoder_budget first last b cap initial /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (len+mid_size) /\
    (!q n. p+32 <= q ==> mem_bytes_at q n actual.vs_memory = mem_bytes_at q n initial.vs_memory) /\
    abi_decoder_effect first last lo hi st.cs_next_var limit_st p output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_finish_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decode_frame p output_size initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`p`, `32`] >> asm_simp_tac (srw_ss()) []) >>
  `abi_decoder_effect first last lo hi st.cs_next_var limit_st p output_size b cap initial actual` by
    (irule abi_decoder_scratch_free_effect >> asm_simp_tac (srw_ss()) []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  qpat_assum `abi_decode_frame p 32 initial actual`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac (srw_ss()) []
QED

(* Finish a real recursive encoding without disturbing its method-ID prefix. *)
Theorem abi_builtin_encode_prefix_frame:
  abi_decoder_effect first last lo hi next limit_st (p+32+mid_size) len b cap s t /\
  (p+32+mid_size+len <= b \/ b+cap <= p) ==>
  mem_bytes_at (p+32) mid_size t.vs_memory = mem_bytes_at (p+32) mid_size s.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  irule abi_decode_footprint_frame_slice >> qexists_tac `[(p+32+mid_size,len);(b,cap)]` >>
  asm_simp_tac (srw_ss()) [abi_footprint_disjoint_def] >> decide_tac
QED

Theorem abi_builtin_encode_compose:
  abi_decoder_effect first last ready.cs_next_id body_end.cs_next_id ready.cs_next_var
    limit_st (p+32+mid_size) len b cap initial encoded /\
  mem_bytes_at (p+32+mid_size) len encoded.vs_memory = bytes /\
  eval_operand buf initial = SOME (n2w p) /\ abi_decoder_operand_live ready.cs_next_var buf /\
  eval_operand encoded_len encoded = SOME (n2w len) /\
  abi_builtin_encode_finish buf encoded_len mid_size body_end = ((),final) /\
  fn_has_code body_end final func /\ ready.cs_next_var <= body_end.cs_next_var /\
  body_end.cs_next_id <= final.cs_next_id /\
  p < dimword (:256) /\ (p+32+mid_size+len <= b \/ b+cap <= p) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  ~encoded.vs_halted /\ encoded.vs_current_bb = body_end.cs_current_bb /\
  encoded.vs_inst_idx = LENGTH body_end.cs_current_insts /\ abi_decode_sim ctx func initial encoded ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (len+mid_size) /\
    mem_bytes_at (p+32+mid_size) len actual.vs_memory = bytes /\
    mem_bytes_at (p+32) mid_size actual.vs_memory = mem_bytes_at (p+32) mid_size initial.vs_memory /\
    abi_decoder_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
      limit_st p (32+mid_size+len) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_prefix_frame >> strip_tac >>
  qpat_assum `abi_decoder_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_effect_def]) >>
  `~initial.vs_halted` by fs[] >>
  `eval_operand buf encoded = SOME (n2w p)` by
    (first_x_assum irule >> asm_simp_tac bool_ss []) >>
  `abi_decoder_operand_live body_end.cs_next_var buf` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `ready.cs_next_var` >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.INST [`st` |-> `body_end`, `initial` |-> `encoded:venom_state`,
    `output_size` |-> `32+mid_size+len:num`, `lo` |-> `ready.cs_next_id`,
    `hi` |-> `final.cs_next_id`] abi_builtin_encode_finish) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> decide_tac) >> strip_tac >>
  `abi_decoder_effect first last ready.cs_next_id body_end.cs_next_id ready.cs_next_var
     limit_st p (32+mid_size+len) b cap initial encoded` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`p+32+mid_size`, `body_end.cs_next_id`, `ready.cs_next_id`,
       `ready.cs_next_var`, `len`] >> asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  `abi_decoder_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
     limit_st p (32+mid_size+len) b cap initial actual` by
    (drule_all abi_decoder_effect_sequence >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> asm_simp_tac bool_ss []
QED

(* Execute every translated recursive descriptor followed by the actual builtin
   length store. Setup and producer input establishment are separate obligations. *)
Theorem abi_builtin_encode_body_finish:
  compile_abi_encode_to_buf dst src (type_to_abi_enc_info sf ce ty) ready = (len_op,body_end) /\
  abi_builtin_encode_finish buf len_op mid_size body_end = ((),final) /\
  fn_has_code ready final func /\
  (ready.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_pre (type_to_abi_enc_info sf ce ty) at av ready src dst sb source_cap
    (p+32+mid_size) b cap initial /\
  eval_operand buf initial = SOME (n2w p) /\ abi_decoder_operand_live ready.cs_next_var buf /\
  (p+32+mid_size+LENGTH (enc at av) <= b \/ b+cap <= p) /\
  abi_decoder_budget first last b cap initial /\ first <= ready.cs_next_id /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = ready.cs_current_bb /\
  initial.vs_inst_idx = LENGTH ready.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH (enc at av)+mid_size) /\
    mem_bytes_at (p+32+mid_size) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    mem_bytes_at (p+32) mid_size actual.vs_memory = mem_bytes_at (p+32) mid_size initial.vs_memory /\
    abi_decoder_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
      limit_st p (32+mid_size+LENGTH (enc at av)) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule cs_extends_abi_encode >> strip_tac >>
  `cs_extends body_end final` by
    (irule cs_extends_same_block >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`ready`, `body_end`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_encoder_correct (type_to_abi_enc_info sf ce ty)` by simp[abi_encoder_correct_translation] >>
  `body_end.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_id <= last /\
   body_end.cs_next_id <= final.cs_next_id` by (Cases_on `mid_size > 0` >> gvs[] >> decide_tac) >>
  qpat_assum `final.cs_blocks = body_end.cs_blocks` (fn blocks =>
    qpat_assum `final.cs_current_bb = body_end.cs_current_bb` (fn label =>
    qpat_assum `ready.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [blocks,label]))) >>
  mp_tac (Q.INST [`start` |-> `ready`, `end_st` |-> `body_end`, `out` |-> `len_op`,
    `d` |-> `p+32+mid_size:num`, `ctx` |-> `ctx`,
    `ei` |-> `type_to_abi_enc_info sf ce ty`] abi_encoder_correct_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial encoded` >>
  `p < dimword (:256)` by
    (qpat_assum `abi_encoder_pre _ _ _ _ _ _ _ _ _ _ _ _`
      (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_pre_def]) >> decide_tac) >>
  mp_tac (Q.INST [`encoded_len` |-> `len_op`, `len` |-> `LENGTH (enc at av)`,
    `bytes` |-> `enc at av`] abi_builtin_encode_compose) >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp[]
QED

(* End-to-end lower_abi_encode without a method ID: actual setup, every
   translated recursive descriptor, and the final length word. *)
Theorem lower_abi_encode_no_method:
  lower_abi_encode ensure NONE src (type_to_abi_enc_info sf ce ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_builtin_encode_no_method_pre (type_to_abi_enc_info sf ce ty) at av start src sb source_cap
    p maxlen first last b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH (enc at av)) /\
    mem_bytes_at (p+32) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    val_in_memory (BaseTV (BytesT (Dynamic maxlen))) (vyperValue$BytesV (enc at av)) p actual.vs_memory /\
    FLOOKUP actual.vs_allocas start.cs_next_id = SOME (p,maxlen+32) /\
    fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual /\
    (!op w. abi_decoder_operand_live start.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    abi_decode_footprint_frame [(p,maxlen+32);(b,cap)] initial actual /\
    (!id. id < start.cs_next_id \/ final.cs_next_id <= id ==>
      FLOOKUP actual.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  qpat_assum `abi_builtin_encode_no_method_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_no_method_pre_def]) >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) []) >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ maxlen+32 < dimword (:256) /\
   first <= ready.cs_next_id` by (asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  mp_tac (Q.INST [`st` |-> `start`, `ctx` |-> `ctx`] abi_builtin_encode_setup_none_reach) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all abi_builtin_encode_no_method_ready >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `ready.cs_blocks = start.cs_blocks` (fn blocks =>
    qpat_assum `start.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [GSYM blocks])) >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`mid_size` |-> `0:num`] abi_builtin_encode_body_finish)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func prepared actual` >>
  `abi_decoder_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st p (maxlen+32) b cap prepared actual` by
    (irule abi_decoder_effect_widen >>
     qexistsl_tac [`p`, `final.cs_next_id`, `ready.cs_next_id`, `ready.cs_next_var`,
       `32+LENGTH (enc at av)`] >> asm_simp_tac (srw_ss()) [] >> decide_tac) >>
  `start.cs_next_id < ready.cs_next_id /\ ready.cs_next_id <= final.cs_next_id` by decide_tac >>
  `FLOOKUP prepared.vs_allocas start.cs_next_id = SOME (p,maxlen+32)` by
    (drule_all abi_builtin_allocation_frame_row >> simp[]) >>
  `FLOOKUP actual.vs_allocas start.cs_next_id = SOME (p,maxlen+32)` by
    (mp_tac (Q.INST [`site` |-> `start.cs_next_id`, `lo` |-> `ready.cs_next_id`,
      `next` |-> `ready.cs_next_var`, `d` |-> `p:num`,
      `sz` |-> `maxlen+32:num`, `outsz` |-> `maxlen+32:num`,
      `hi` |-> `final.cs_next_id`, `s` |-> `prepared:venom_state`,
      `t` |-> `actual:venom_state`] abi_builtin_encode_body_allocation_row) >>
     impl_tac >- asm_simp_tac (srw_ss()) [] >> simp[]) >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`st` |-> `start`, `site` |-> `start.cs_next_id`, `outsz` |-> `maxlen+32:num`,
      `d` |-> `p:num`] abi_builtin_decode_effect_compose)) >> strip_tac >>
  qpat_assum `abi_builtin_decode_effect _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_decode_effect_def]) >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [val_in_memory_def, mem_word_at_eq_mload] >>
  first_assum ACCEPT_TAC
QED
