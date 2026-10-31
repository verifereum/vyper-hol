Theory abiScratchBuiltinSource
Ancestors
  abiBuiltinEncodeCorrect abiScratchLeafEffect abiScratchEncoderContract abiDecoderFrame
  abiDecoderFrameCompose abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract
  abiDecoderLoop compileEnv venomState words list arithmetic abiBuiltinEncodeSetup
  abiBuiltinEncodeMethod abiBuiltinEncodeRun abiBuiltinAllocation valueEncoding finite_map
  abiScratchEffect abiScratchSubset abiScratchFootprint abiEncoderArrayFrame
  abiBuiltinEncodeCode abiDecoderAllocation abiDecoderFootprint pred_set abiScratchEncoderCaller
  abiScratchEncoderRun abiEncoderAppend abiEncoderCounters abiDecoderAppend fragExec
  exprLowering contractABI abiScratchBuiltinPre abiScratchBuiltinEffect abiBuiltinEncodeContext
  abiEncoderMemory abiEncoderInput builtinAbi valueEncodingProps abiScratchArrayEntry
  abiCallerAllocation venomMemDefs abiBuiltinEncodeSource vyperContext vyperABI vyperAST
  vyperTypeSystem

(* Execute the builtin length store with physical scratch ownership.
   TOP-LEVEL: abi_scratch_builtin_finish preserves completed payload/prefix
   bytes and records the actual register and allocator-preserving write. *)
Theorem abi_scratch_builtin_finish:
  abi_builtin_encode_finish buf encoded_len mid_size st = ((),final) /\ fn_has_code st final func /\
  eval_operand buf initial = SOME (n2w p) /\ eval_operand encoded_len initial = SOME (n2w len) /\
  abi_decoder_operand_live st.cs_next_var buf /\ p < dimword (:256) /\ 32 <= output_size /\
  abi_decoder_budget first last b cap initial /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (len+mid_size) /\
    (!q n. p+32 <= q ==> mem_bytes_at q n actual.vs_memory = mem_bytes_at q n initial.vs_memory) /\
    abi_scratch_effect first last lo hi st.cs_next_var limit_st p output_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_builtin_encode_finish_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  `abi_decode_frame p output_size initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`p`, `32`] >> asm_simp_tac (srw_ss()) []) >>
  `actual.vs_halted = initial.vs_halted` by simp[] >>
  `abi_scratch_effect first last lo hi st.cs_next_var limit_st p output_size b cap initial actual` by
    (irule abi_scratch_leaf_effect >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  qpat_assum `abi_decode_frame p 32 initial actual`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  rpt strip_tac >> first_x_assum irule >> asm_simp_tac (srw_ss()) []
QED

(* Execute actual builtin output allocation, address setup and optional method ID.
   TOP-LEVEL: abi_scratch_builtin_setup_reach exposes a common physical setup
   frame for both options, retaining the full 32-byte method-store width. *)
Theorem abi_scratch_builtin_none_frame:
  abi_builtin_allocation_frame next site outsz initial actual ==>
  abi_builtin_encode_setup_frame next site outsz p 0 initial actual
Proof
  simp[abi_builtin_allocation_frame_def, abi_builtin_encode_setup_frame_def, abi_decode_frame_def]
QED

Theorem abi_scratch_builtin_setup_reach:
  abi_builtin_encode_setup method_id_opt maxlen st = (ops,ready) /\ fn_has_code st ready func /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id =
      SOME (p,maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4))) /\
  p+maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4) < dimword (:256) /\
  ready.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. eval_operand (FST ops) actual = SOME (n2w p) /\
    eval_operand (SND ops) actual = SOME (n2w (p+32+(case method_id_opt of NONE => 0 | SOME _ => 4))) /\
    mem_bytes_at (p+32) (LENGTH (abi_builtin_encode_prefix method_id_opt)) actual.vs_memory =
      abi_builtin_encode_prefix method_id_opt /\ fresh_vars_wrt limit_st actual /\
    abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id
      (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4)) p
      (case method_id_opt of NONE => 0 | SOME _ => 32) initial actual /\
    actual.vs_current_bb = ready.cs_current_bb /\ actual.vs_inst_idx = LENGTH ready.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  Cases_on `method_id_opt` >>
  simp_tac (srw_ss()) [abi_builtin_encode_prefix_def, abi_builtin_encode_method_bytes_length] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS)
  >- (`maxlen+32 < dimword (:256)` by decide_tac >>
      drule_all abi_builtin_encode_setup_none_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
      rename1 `abi_decode_sim ctx func initial actual` >>
      drule abi_scratch_builtin_none_frame >> disch_then (qspec_then `p` assume_tac) >>
      qexists_tac `actual` >> asm_simp_tac (srw_ss()) [mem_bytes_at_def]) >>
  `maxlen+36 < dimword (:256) /\ p+32 < dimword (:256)` by decide_tac >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [GSYM ADD_ASSOC]) >>
  drule_all abi_builtin_encode_method_setup_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [GSYM ADD_ASSOC]
QED

(* Preserve a method prefix through recursive encoding and the final length store.
   TOP-LEVEL: abi_scratch_builtin_compose returns one physical enclosing effect.
   Its prefix observation follows from physical windows and owned scratch IDs. *)
Theorem abi_scratch_builtin_prefix_frame:
  abi_scratch_effect first last lo hi next limit_st (p+32+mid_size) len b cap s t /\
  first <= lo /\ hi <= last /\
  abi_footprint_disjoint p (32+mid_size+len)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s) ==>
  mem_bytes_at (p+32) mid_size t.vs_memory = mem_bytes_at (p+32) mid_size s.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `abi_footprint_disjoint (p+32) mid_size
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap s)` by
    (irule abi_footprint_disjoint_subwindow >> qexistsl_tac [`p`, `32+mid_size+len`] >> simp[]) >>
  `abi_footprint_disjoint (p+32) mid_size
    (abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` by
    (irule abi_scratch_disjoint_subset >> qexists_tac `abi_decoder_ids first last` >>
     simp[SUBSET_DEF, abi_decoder_ids_def] >> decide_tac) >>
  irule abi_decode_footprint_frame_slice >>
  qexists_tac `((p+32+mid_size,len)::abi_decoder_child_scratch (abi_decoder_ids lo hi) b cap s)` >>
  simp[abi_scratch_disjoint_cons] >> fs[abi_scratch_effect_def]
QED

Theorem abi_scratch_builtin_compose:
  abi_scratch_effect first last ready.cs_next_id body_end.cs_next_id ready.cs_next_var
    limit_st (p+32+mid_size) len b cap initial encoded /\
  mem_bytes_at (p+32+mid_size) len encoded.vs_memory = bytes /\
  eval_operand buf initial = SOME (n2w p) /\ abi_decoder_operand_live ready.cs_next_var buf /\
  eval_operand encoded_len encoded = SOME (n2w len) /\
  abi_builtin_encode_finish buf encoded_len mid_size body_end = ((),final) /\
  fn_has_code body_end final func /\ ready.cs_next_var <= body_end.cs_next_var /\
  body_end.cs_next_id <= final.cs_next_id /\
  p < dimword (:256) /\ first <= ready.cs_next_id /\ final.cs_next_id <= last /\
  abi_footprint_disjoint p (32+mid_size+len)
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  final.cs_next_var <= limit_st.cs_next_var /\
  ~encoded.vs_halted /\ encoded.vs_current_bb = body_end.cs_current_bb /\
  encoded.vs_inst_idx = LENGTH body_end.cs_current_insts /\ abi_decode_sim ctx func initial encoded ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (len+mid_size) /\
    mem_bytes_at (p+32+mid_size) len actual.vs_memory = bytes /\
    mem_bytes_at (p+32) mid_size actual.vs_memory = mem_bytes_at (p+32) mid_size initial.vs_memory /\
    abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
      limit_st p (32+mid_size+len) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `body_end.cs_next_id <= last` by decide_tac >>
  drule_all abi_scratch_builtin_prefix_frame >> disch_tac >>
  `eval_operand buf encoded = SOME (n2w p)` by
    (drule_all abi_scratch_effect_operand >> simp[]) >>
  `abi_decoder_operand_live body_end.cs_next_var buf` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `ready.cs_next_var` >> simp[]) >>
  `fresh_vars_wrt limit_st encoded /\ abi_decoder_budget first last b cap encoded` by
    fs[abi_scratch_effect_def] >>
  mp_tac (Q.INST [`st` |-> `body_end`, `initial` |-> `encoded:venom_state`,
    `output_size` |-> `32+mid_size+len:num`, `lo` |-> `ready.cs_next_id`,
    `hi` |-> `final.cs_next_id`] abi_scratch_builtin_finish) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> decide_tac) >> strip_tac >>
  `abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st p (32+mid_size+len) b cap initial encoded` by
    (irule abi_scratch_effect_widen >> qexistsl_tac [`p+32+mid_size`, `body_end.cs_next_id`,
       `ready.cs_next_id`, `ready.cs_next_var`, `len`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st p (32+mid_size+len) b cap encoded actual` by
    (irule abi_scratch_effect_widen >> qexistsl_tac [`p`, `final.cs_next_id`,
       `ready.cs_next_id`, `body_end.cs_next_var`, `32+mid_size+len`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL]) >>
  `abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
    limit_st p (32+mid_size+len) b cap initial actual` by
    (irule abi_scratch_effect_trans >> asm_simp_tac bool_ss [] >> qexists_tac `encoded` >> simp[]) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [] >>
  irule abi_decode_sim_trans >> qexists_tac `encoded` >> asm_simp_tac bool_ss []
QED

(* Execute an actual translated encoder followed by the builtin length store.
   TOP-LEVEL: abi_scratch_builtin_body_finish keeps the optional method prefix
   and composes one physical effect for the complete used output buffer. *)
Theorem abi_scratch_builtin_body_finish:
  compile_abi_encode_to_buf dst src (type_to_abi_enc_info sf ce ty) ready = (len_op,body_end) /\
  abi_builtin_encode_finish buf len_op mid_size body_end = ((),final) /\
  fn_has_code ready final func /\
  (ready.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_input (type_to_abi_enc_info sf ce ty) at av ready src dst sb source_cap
    (p+32+mid_size) (LENGTH (enc at av)) first last b cap initial /\
  eval_operand buf initial = SOME (n2w p) /\ abi_decoder_operand_live ready.cs_next_var buf /\
  abi_footprint_disjoint p (32+mid_size+LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial) /\
  abi_decoder_budget first last b cap initial /\ first <= ready.cs_next_id /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = ready.cs_current_bb /\
  initial.vs_inst_idx = LENGTH ready.cs_current_insts ==>
  ?actual. eval_operand buf actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH (enc at av)+mid_size) /\
    mem_bytes_at (p+32+mid_size) (LENGTH (enc at av)) actual.vs_memory = enc at av /\
    mem_bytes_at (p+32) mid_size actual.vs_memory = mem_bytes_at (p+32) mid_size initial.vs_memory /\
    abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var
      limit_st p (32+mid_size+LENGTH (enc at av)) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_builtin_encode_finish_shape >> strip_tac >>
  drule cs_extends_abi_encode >> strip_tac >>
  `cs_extends body_end final` by (irule cs_extends_same_block >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`ready`, `body_end`, `final`, `func`] fn_has_code_split) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  `abi_scratch_encoder (type_to_abi_enc_info sf ce ty)` by simp[abi_scratch_encoder_translation] >>
  `body_end.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_id <= last /\
   body_end.cs_next_id <= final.cs_next_id` by (Cases_on `mid_size > 0` >> gvs[] >> decide_tac) >>
  qpat_assum `final.cs_blocks = body_end.cs_blocks` (fn blocks =>
    qpat_assum `final.cs_current_bb = body_end.cs_current_bb` (fn label =>
    qpat_assum `ready.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [blocks,label]))) >>
  mp_tac (Q.INST [`start` |-> `ready`, `end_st` |-> `body_end`, `out` |-> `len_op`,
    `d` |-> `p+32+mid_size:num`, `ctx` |-> `ctx`,
    `ei` |-> `type_to_abi_enc_info sf ce ty`] abi_scratch_encoder_run) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial encoded` >>
  `p < dimword (:256)` by
    (qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >> decide_tac) >>
  mp_tac (Q.INST [`encoded_len` |-> `len_op`, `len` |-> `LENGTH (enc at av)`,
    `bytes` |-> `enc at av`] abi_scratch_builtin_compose) >>
  impl_tac >- asm_simp_tac bool_ss [] >> simp[]
QED

(* Complete actual lower_abi_encode through its precise recursive core.
   TOP-LEVEL: lower_abi_encode_scratch covers both method-ID choices, exact
   returned Bytes, complete source preservation and physical write ownership. *)
Theorem abi_scratch_builtin_prefix_length:
  LENGTH (abi_builtin_encode_prefix method_id_opt) =
    (case method_id_opt of NONE => 0 | SOME _ => 4)
Proof
  Cases_on `method_id_opt` >> simp[abi_builtin_encode_prefix_def]
QED

Theorem abi_scratch_builtin_value:
  mload p s = n2w (LENGTH bytes+LENGTH prefix) /\
  mem_bytes_at (p+32) (LENGTH prefix) s.vs_memory = prefix /\
  mem_bytes_at (p+32+LENGTH prefix) (LENGTH bytes) s.vs_memory = bytes ==>
  mem_bytes_at (p+32) (LENGTH (prefix++bytes)) s.vs_memory = prefix++bytes /\
  val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH prefix))))
    (vyperValue$BytesV (prefix++bytes)) p s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at (p+32) (LENGTH (prefix++bytes)) s.vs_memory = prefix++bytes` by
    (simp_tac bool_ss [LENGTH_APPEND] >> ONCE_REWRITE_TAC [abi_encoder_mem_split] >> simp[]) >>
  asm_simp_tac (srw_ss()) [val_in_memory_def, mem_word_at_eq_mload, ADD_COMM]
QED

Theorem lower_abi_encode_scratch:
  lower_abi_encode ensure method_id_opt src (type_to_abi_enc_info sf ce ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_builtin_pre (type_to_abi_enc_info sf ce ty) at av start method_id_opt src sb source_cap
    p maxlen first last b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (abi_builtin_encode_prefix method_id_opt ++ enc at av)) /\
    mem_bytes_at (p+32) (LENGTH (abi_builtin_encode_prefix method_id_opt ++ enc at av)) actual.vs_memory =
      abi_builtin_encode_prefix method_id_opt ++ enc at av /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_builtin_encode_prefix method_id_opt)))))
      (vyperValue$BytesV (abi_builtin_encode_prefix method_id_opt ++ enc at av)) p actual.vs_memory /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb source_cap actual.vs_memory /\
    abi_scratch_builtin_effect first last start final limit_st p
      (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4))
      (case method_id_opt of NONE => 0 | SOME _ => 32) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >> drule abi_builtin_encode_setup_live >> strip_tac >>
  qpat_assum `abi_scratch_builtin_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_scratch_builtin_pre_def, LET_THM]) >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ first <= ready.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `ctx` |-> `ctx`] abi_scratch_builtin_setup_reach) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all (Q.INST [`st` |-> `start`, `dst` |-> `SND (ops:operand # operand)`]
    abi_scratch_builtin_ready) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `ready.cs_blocks = start.cs_blocks` (fn blocks =>
    qpat_assum `start.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [GSYM blocks])) >>
  drule_all (Q.INST [`dst` |-> `SND (ops:operand # operand)`, `buf` |-> `FST (ops:operand # operand)`,
    `initial` |-> `prepared:venom_state`, `len_op` |-> `len:operand`,
    `mid_size` |-> `case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4`]
    abi_scratch_builtin_body_finish) >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func prepared actual` >>
  `abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var limit_st p
    (maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4)) b cap prepared actual` by
    (irule abi_scratch_effect_widen >> qexistsl_tac [`p`, `final.cs_next_id`, `ready.cs_next_id`,
       `ready.cs_next_var`, `32+(case method_id_opt of NONE => 0 | SOME _ => 4)+LENGTH (enc at av)`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  mp_tac (Q.INST [`st` |-> `start`, `outsz` |-> `maxlen+32+
    (case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4)`,
    `write_size` |-> `case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 32`]
    abi_scratch_builtin_effect_compose) >> impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> disch_tac >>
  drule_all abi_scratch_builtin_source >> disch_tac >>
  mp_tac (Q.INST [`bytes` |-> `enc at av`, `prefix` |-> `abi_builtin_encode_prefix method_id_opt`,
    `s` |-> `actual:venom_state`] abi_scratch_builtin_value) >>
  impl_tac >- gvs[abi_scratch_builtin_prefix_length, Excl "enc_def"] >> strip_tac >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [LENGTH_APPEND, abi_scratch_builtin_prefix_length, ADD_COMM]
QED

(* Establish builtin resources from ordinary allocation history and numeric credit.
   TOP-LEVEL: abi_scratch_builtin_pre_caller derives all physical input/budget
   conditions. Complete producer memory and full method-store separation remain
   explicit; source and output allocations may both lie inside the numeric arena. *)
Theorem abi_scratch_builtin_allocate_inv:
  alloca_inv s ==> alloca_inv (abi_builtin_allocate_state site outsz s)
Proof
  Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  simp_tac bool_ss [abi_builtin_allocate_state_def] >> asm_rewrite_tac[] >>
  fs[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def, FLOOKUP_UPDATE] >>
  rw[] >> gvs[AllCaseEqs()] >> res_tac >> fs[]
QED

Theorem abi_scratch_builtin_allocate_buffers:
  alloca_inv s /\ FLOOKUP s.vs_allocas source_id = SOME (sb,source_cap) /\ source_id <> site /\
  ((FLOOKUP s.vs_allocas site = NONE /\ p = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas site = SOME (p,outsz)) ==>
  alloca_inv (abi_builtin_allocate_state site outsz s) /\
  FLOOKUP (abi_builtin_allocate_state site outsz s).vs_allocas source_id = SOME (sb,source_cap) /\
  FLOOKUP (abi_builtin_allocate_state site outsz s).vs_allocas site = SOME (p,outsz)
Proof
  strip_tac >> drule abi_scratch_builtin_allocate_inv >> disch_tac >>
  asm_simp_tac bool_ss [] >> Cases_on `FLOOKUP s.vs_allocas site = NONE` >>
  gvs[abi_builtin_allocate_state_def, FLOOKUP_UPDATE]
QED

Theorem abi_scratch_builtin_store_separate:
  (sb+source_cap <= p \/ p+(maxlen+32+(case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4)) <= sb) /\
  (method_id_opt = NONE \/ sb+source_cap <= p+32 \/ p+64 <= sb) ==>
  sb+source_cap <= p+32 \/ p+32+(case method_id_opt of NONE => 0 | SOME _ => 32) <= sb
Proof
  Cases_on `method_id_opt` >> simp[] >> decide_tac
QED

Theorem abi_scratch_builtin_pre_caller:
  let outsz = maxlen+32+(case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4) in
  let allocated = abi_builtin_allocate_state st.cs_next_id outsz initial in
  let cap = allocated.vs_alloca_next+32*CARD (abi_decoder_missing first last allocated) in
  alloca_inv initial /\ cap < dimword (:256) /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_cap) /\ source_id <> st.cs_next_id /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  st.cs_next_id < first /\ first <= st.cs_next_id+(case method_id_opt of NONE => 2 | SOME _ => 4) /\
  ~(source_id IN abi_decoder_ids first last) /\
  (!id off sz. id IN abi_decoder_ids first last /\
    FLOOKUP allocated.vs_allocas id = SOME (off,sz) ==> sz = 32) /\
  abi_encoder_input ei at av sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  LENGTH (enc at av) <= maxlen /\
  (method_id_opt = NONE \/ sb+source_cap <= p+32 \/ p+64 <= sb) ==>
  abi_scratch_builtin_pre ei at av st method_id_opt src sb source_cap p maxlen first last 0 cap initial
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`s` |-> `initial:venom_state`, `site` |-> `st.cs_next_id`,
    `outsz` |-> `maxlen+32+(case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4)`]
    abi_scratch_builtin_allocate_buffers) >> impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `allocated = abi_builtin_allocate_state st.cs_next_id
    (maxlen+32+(case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4)) initial` >>
  qabbrev_tac `cap = allocated.vs_alloca_next+32*CARD (abi_decoder_missing first last allocated)` >>
  `abi_decoder_budget first last 0 cap allocated` by
    (qunabbrev_tac `cap` >> irule abi_caller_allocation_budget_zero >>
     asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  `~(st.cs_next_id IN abi_decoder_ids first last)` by (simp[abi_decoder_ids_def] >> decide_tac) >>
  mp_tac (Q.INST [`initial` |-> `allocated:venom_state`, `ids` |-> `abi_decoder_ids first last`,
    `output_id` |-> `st.cs_next_id`, `d` |-> `p:num`, `b` |-> `0:num`,
    `output_size` |-> `maxlen+32+(case (method_id_opt:bytes32 option) of NONE => 0 | SOME _ => 4)`]
    abi_scratch_array_entry_buffers) >>
  impl_tac >- (asm_simp_tac (srw_ss()) [] >> decide_tac) >> strip_tac >>
  qpat_assum `abi_footprint_disjoint sb source_cap
    [(p,maxlen+32+(case method_id_opt of NONE => 0 | SOME _ => 4))]`
    (assume_tac o SIMP_RULE (srw_ss()) [abi_footprint_disjoint_def]) >>
  drule_all abi_scratch_builtin_store_separate >> disch_tac >>
  PURE_REWRITE_TAC [abi_scratch_builtin_pre_def, LET_THM] >> BETA_TAC >>
  qpat_assum `Abbrev (allocated = _)` (fn th =>
    PURE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem lower_abi_encode_scratch_caller:
  let outsz = maxlen+32+(case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4) in
  let allocated = abi_builtin_allocate_state start.cs_next_id outsz initial in
  let cap = allocated.vs_alloca_next+32*CARD (abi_decoder_missing first last allocated) in
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
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (abi_builtin_encode_prefix method_id_opt ++ enc at av)) /\
    mem_bytes_at (p+32) (LENGTH (abi_builtin_encode_prefix method_id_opt ++ enc at av)) actual.vs_memory =
      abi_builtin_encode_prefix method_id_opt ++ enc at av /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_builtin_encode_prefix method_id_opt)))))
      (vyperValue$BytesV (abi_builtin_encode_prefix method_id_opt ++ enc at av)) p actual.vs_memory /\
    abi_encoder_input (type_to_abi_enc_info sf ce ty) at av sb source_cap actual.vs_memory /\
    abi_scratch_builtin_effect first last start final limit_st p outsz
      (case method_id_opt of NONE => 0 | SOME _ => 32) 0 cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  PURE_REWRITE_TAC [LET_THM] >> BETA_TAC >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
    (Q.INST [`st` |-> `start:compile_state`] abi_scratch_builtin_pre_caller))) >> disch_tac >>
  drule_all lower_abi_encode_scratch >> disch_then (qspec_then `ctx` ACCEPT_TAC)
QED

(* Source-level result of the complete physical lower_abi_encode action.
   TOP-LEVEL: lower_abi_encode_scratch_source covers singleton unwrapping,
   tuple payloads and either method ID while preserving complete source data. *)
Theorem lower_abi_encode_scratch_source:
  let enc_ty = abi_builtin_encode_type ensure tys in
  let bytes = abi_encode_method_id_bytes method_id ++ enc (vyper_to_abi_type (get_tenv cx) enc_ty) av in
  well_typed_type_builtin_args (AbiEncode ensure method_id) (TupleT tys) tys /\
  LENGTH vs = LENGTH tys /\
  vyper_to_abi (get_tenv cx) enc_ty (abi_builtin_encode_value ensure tys vs) = SOME av /\
  lower_abi_encode ensure (OPTION_MAP bytes_method_id_word method_id) src
    (type_to_abi_enc_info ce.ce_struct_fields ce enc_ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_scratch_builtin_pre (type_to_abi_enc_info ce.ce_struct_fields ce enc_ty)
    (vyper_to_abi_type (get_tenv cx) enc_ty) av start (OPTION_MAP bytes_method_id_word method_id)
    src sb source_cap p maxlen first last b cap initial /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) arg_tys vs = INL (BytesV bytes) /\
    eval_operand out actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH bytes) /\
    mem_bytes_at (p+32) (LENGTH bytes) actual.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_encode_method_id_bytes method_id)))))
      (BytesV bytes) p actual.vs_memory /\
    abi_encoder_input (type_to_abi_enc_info ce.ce_struct_fields ce enc_ty)
      (vyper_to_abi_type (get_tenv cx) enc_ty) av sb source_cap actual.vs_memory /\
    abi_scratch_builtin_effect first last start final limit_st p
      (maxlen+32+LENGTH (abi_encode_method_id_bytes method_id))
      (case method_id of NONE => 0 | SOME _ => 32) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_checked_prefix >> strip_tac >>
  qpat_assum `well_typed_type_builtin_args _ _ _`
    (assume_tac o CONJUNCT1 o SIMP_RULE (srw_ss()) [well_typed_type_builtin_args_def]) >>
  drule_all abi_builtin_encode_source_result >> disch_then (qspec_then `method_id` assume_tac) >>
  drule_all lower_abi_encode_scratch >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_builtin_encode_prefix _ = _` (fn prefix =>
    let val size = REWRITE_RULE [abi_scratch_builtin_prefix_length]
          (AP_TERM ``LENGTH:word8 list -> num`` prefix) in
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [prefix, size, abi_builtin_encode_store_case]) end) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_scratch_builtin_prefix_length]
QED
