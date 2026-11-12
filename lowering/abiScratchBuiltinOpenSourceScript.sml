(* Open-input companion: retain complete builtin finish and frame guarantees. *)
Theory abiScratchBuiltinOpenSource
Ancestors
  abiScratchBuiltinSource abiEncoderSharedRecursive abiEncoderSharedContract
  abiEncoderProps builtinAbi exprLoweringProps compileEnv context emitHelperProps
  abiDecoderContract abiScratchEncoderContract contractABI words arithmetic
  abiEncoderCounters abiBuiltinEncodeCode abiEncoderAppend fragExec
  abiBuiltinEncodeSetup abiBuiltinEncodeContext abiEncoderOpenInputFrame abiEncoderOpenInput
  abiBuiltinAllocation abiDecoderAllocation abiDecoderFootprint finite_map
  abiDecoderReentry abiEncoderArrayFrame abiScratchBuiltinEffect abiScratchFootprint abiDecoderFrame
  abiScratchEffect abiDecoderLoop list abiBuiltinEncodeSource vyperTypeSystem
  vyperContext vyperABI vyperAST

Theorem abi_scratch_builtin_body_finish_open:
  compile_abi_encode_to_buf dst src (type_to_abi_enc_info sf ce ty) ready = (len_op,body_end) /\
  abi_builtin_encode_finish buf len_op mid_size body_end = ((),final) /\
  fn_has_code ready final func /\
  (ready.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_shared_input (type_to_abi_enc_info sf ce ty,at,av) (ready,src,dst)
    (sb,source_cap) (p+32+mid_size,LENGTH (enc at av)) (first,last,b,cap) initial /\
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
  `cs_extends body_end final` by (irule cs_extends_same_block >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `abi_encoder_shared (type_to_abi_enc_info sf ce ty)` by
    simp[abi_encoder_shared_translation] >>
  `body_end.cs_next_var <= limit_st.cs_next_var /\ body_end.cs_next_id <= last /\
   body_end.cs_next_id <= final.cs_next_id` by
    (Cases_on `mid_size > 0` >> gvs[] >> decide_tac) >>
  qpat_assum `final.cs_blocks = body_end.cs_blocks` (fn blocks =>
    qpat_assum `final.cs_current_bb = body_end.cs_current_bb` (fn label =>
    qpat_assum `ready.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [blocks,label]))) >>
  drule_all abi_encoder_shared_run >> strip_tac >>
  first_x_assum (qspec_then `ctx` strip_assume_tac) >>
  drule abi_encoder_shared_endpoint_sim >> strip_tac >>
  qpat_x_assum `abi_encoder_shared_endpoint _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_shared_endpoint_def]) >>
  `p < dimword (:256)` by
    (qpat_x_assum `abi_encoder_shared_input _ _ _ _ _ _` mp_tac >>
     simp[abi_encoder_shared_input_def] >> strip_tac >> decide_tac) >>
  irule abi_scratch_builtin_compose >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`body_end`, `len_op`] >> fs[AC ADD_COMM ADD_ASSOC]
QED

Theorem abi_builtin_encode_setup_frame_open_input:
  abi_builtin_encode_setup_frame next site outsz p write_size s t /\
  abi_encoder_open_input ei at av sb source_cap s.vs_memory /\
  (sb+source_cap <= p+32 \/ p+32+write_size <= sb) ==>
  mem_bytes_at sb source_cap s.vs_memory = mem_bytes_at sb source_cap t.vs_memory /\
  abi_encoder_open_input ei at av sb source_cap t.vs_memory
Proof
  strip_tac >>
  qpat_assum `abi_builtin_encode_setup_frame _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_encode_setup_frame_def]) >>
  qpat_assum `abi_decode_frame _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  `mem_bytes_at sb source_cap s.vs_memory = mem_bytes_at sb source_cap t.vs_memory` by
    (irule EQ_SYM >> first_x_assum irule >> simp[]) >>
  drule abi_encoder_open_input_mem_agree >>
  disch_then (qspec_then `t.vs_memory` mp_tac) >>
  qpat_x_assum `!p' k. _` kall_tac >> metis_tac[]
QED

Theorem abi_scratch_builtin_ready_open:
  let mid_size = case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4 in
  let write_size = case method_id_opt of NONE => 0 | SOME _ => 32 in
  let outsz = 32+32*word_size (maxlen+mid_size) in
  let allocated = abi_builtin_allocate_state st.cs_next_id outsz initial in
  abi_encoder_open_input ei at av sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live st.cs_next_var src /\
  sb+source_cap < dimword (:256) /\ p+outsz < dimword (:256) /\ LENGTH (enc at av) <= maxlen /\
  (sb+source_cap <= p \/ p+outsz <= sb) /\
  (sb+source_cap <= p+32 \/ p+32+write_size <= sb) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,outsz)) /\
  st.cs_next_id < first /\ first <= st.cs_next_id+(case method_id_opt of NONE => 2 | SOME _ => 4) /\
  abi_decoder_budget first last b cap allocated /\
  abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated) /\
  abi_footprint_disjoint p outsz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated) /\
  abi_builtin_encode_setup_frame st.cs_next_var st.cs_next_id outsz p write_size initial prepared /\
  eval_operand dst prepared = SOME (n2w (p+32+mid_size)) /\
  st.cs_next_var <= ready.cs_next_var /\ abi_decoder_operand_live ready.cs_next_var dst ==>
  abi_encoder_shared_input (ei,at,av) (ready,src,dst) (sb,source_cap)
    (p+32+mid_size,LENGTH (enc at av)) (first,last,b,cap) prepared /\
  abi_decoder_budget first last b cap prepared /\
  abi_footprint_disjoint p (32+mid_size+LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared) /\
  mem_bytes_at sb source_cap initial.vs_memory = mem_bytes_at sb source_cap prepared.vs_memory
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qspec_then `maxlen+(case method_id_opt of NONE => 0 | SOME _ => 4)`
    assume_tac abi_builtin_word_size_capacity >>
  drule_all abi_builtin_encode_setup_frame_open_input >> strip_tac >>
  `abi_decoder_budget first last b cap prepared` by
    (drule abi_builtin_encode_setup_frame_budget >> asm_simp_tac bool_ss []) >>
  `abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared =
    abi_decoder_child_scratch (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state st.cs_next_id
        (32+32*word_size (maxlen+(case method_id_opt of NONE => 0 | SOME _ => 4))) initial)` by
    fs[abi_builtin_encode_setup_frame_def, abi_decoder_child_scratch_def] >>
  `eval_operand src prepared = SOME (n2w sb)` by fs[abi_builtin_encode_setup_frame_def] >>
  `abi_decoder_operand_live ready.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_footprint_disjoint p (32+(case method_id_opt of NONE => 0 | SOME _ => 4)+LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`p`, `32+32*word_size (maxlen+(case method_id_opt of NONE => 0 | SOME _ => 4))`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  `abi_footprint_disjoint (p+32+(case method_id_opt of NONE => 0 | SOME _ => 4)) (LENGTH (enc at av))
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap prepared)` by
    (irule abi_footprint_disjoint_subwindow >>
     qexistsl_tac [`p`, `32+32*word_size (maxlen+(case method_id_opt of NONE => 0 | SOME _ => 4))`] >>
     asm_simp_tac bool_ss [] >> decide_tac) >>
  asm_simp_tac bool_ss [abi_encoder_shared_input_def, LESS_EQ_REFL,
    abi_encoder_zero_aware_separation] >> decide_tac
QED

Theorem abi_scratch_builtin_source_open:
  abi_encoder_open_input ei at av sb source_cap initial.vs_memory /\
  (sb+source_cap <= p \/ p+outsz <= sb) /\
  (sb+source_cap <= p+32 \/ p+32+write_size <= sb) /\
  abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap
      (abi_builtin_allocate_state st.cs_next_id outsz initial)) /\
  abi_scratch_builtin_effect first last st final limit_st p outsz write_size b cap initial actual ==>
  mem_bytes_at sb source_cap initial.vs_memory = mem_bytes_at sb source_cap actual.vs_memory /\
  abi_encoder_open_input ei at av sb source_cap actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_builtin_effect _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_builtin_effect_def]) >>
  `abi_footprint_disjoint sb source_cap
    ([(p,outsz);(p+32,write_size)] ++
      abi_decoder_child_scratch (abi_decoder_ids first last) b cap
        (abi_builtin_allocate_state st.cs_next_id outsz initial))` by
    asm_simp_tac (srw_ss()) [abi_scratch_disjoint_cons] >>
  `mem_bytes_at sb source_cap initial.vs_memory = mem_bytes_at sb source_cap actual.vs_memory` by
    (irule EQ_SYM >>
     qpat_x_assum `abi_decode_footprint_frame _ _ _` mp_tac >>
     simp_tac bool_ss [abi_decode_footprint_frame_def] >> strip_tac >>
     first_x_assum irule >> first_assum ACCEPT_TAC) >>
  drule abi_encoder_open_input_mem_agree >>
  disch_then (qspec_then `actual.vs_memory` mp_tac) >> metis_tac[]
QED

Theorem lower_abi_encode_scratch_open:
  let mid_size = case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4 in
  let write_size = case method_id_opt of NONE => 0 | SOME _ => 32 in
  let outsz = 32+32*word_size (maxlen+mid_size) in
  let allocated = abi_builtin_allocate_state start.cs_next_id outsz initial in
  lower_abi_encode ensure method_id_opt src (type_to_abi_enc_info sf ce ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live start.cs_next_var src /\
  sb+source_cap < dimword (:256) /\ p+outsz < dimword (:256) /\ LENGTH (enc at av) <= maxlen /\
  (sb+source_cap <= p \/ p+outsz <= sb) /\
  (sb+source_cap <= p+32 \/ p+32+write_size <= sb) /\
  ((FLOOKUP initial.vs_allocas start.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas start.cs_next_id = SOME (p,outsz)) /\
  start.cs_next_id < first /\ first <= start.cs_next_id+(case method_id_opt of NONE => 2 | SOME _ => 4) /\
  abi_decoder_budget first last b cap allocated /\
  abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated) /\
  abi_footprint_disjoint p outsz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated) /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. eval_operand out actual = SOME (n2w p) /\
    mload p actual = n2w (LENGTH (abi_builtin_encode_prefix method_id_opt ++ enc at av)) /\
    mem_bytes_at (p+32) (LENGTH (abi_builtin_encode_prefix method_id_opt ++ enc at av)) actual.vs_memory =
      abi_builtin_encode_prefix method_id_opt ++ enc at av /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_builtin_encode_prefix method_id_opt)))))
      (vyperValue$BytesV (abi_builtin_encode_prefix method_id_opt ++ enc at av)) p actual.vs_memory /\
    mem_bytes_at sb source_cap initial.vs_memory = mem_bytes_at sb source_cap actual.vs_memory /\
    abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av sb source_cap actual.vs_memory /\
    abi_scratch_builtin_effect first last start final limit_st p outsz write_size b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_encode_trace >> strip_tac >>
  drule_all abi_builtin_encode_code >> strip_tac >>
  drule abi_builtin_encode_setup_shape >> strip_tac >>
  drule abi_builtin_encode_setup_live >> strip_tac >>
  qspec_then `maxlen+(case method_id_opt of NONE => 0 | SOME _ => 4)`
    assume_tac abi_builtin_word_size_capacity >>
  `ready.cs_next_var <= limit_st.cs_next_var /\ first <= ready.cs_next_id` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start:compile_state`, `ctx` |-> `ctx`] abi_scratch_builtin_setup_reach) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac)) >> strip_tac >>
  rename1 `abi_decode_sim ctx func initial prepared` >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
    (Q.INST [`st` |-> `start:compile_state`, `dst` |-> `SND (ops:operand # operand)`]
      abi_scratch_builtin_ready_open))) >> strip_tac >>
  qpat_assum `ready.cs_blocks = start.cs_blocks` (fn blocks =>
    qpat_assum `start.cs_blocks = final.cs_blocks \/ _`
      (assume_tac o PURE_REWRITE_RULE [GSYM blocks])) >>
  drule_all abi_scratch_builtin_body_finish_open >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func prepared actual` >>
  `abi_scratch_effect first last ready.cs_next_id final.cs_next_id ready.cs_next_var limit_st p
    (32+32*word_size (maxlen+(case method_id_opt of NONE => 0 | SOME _ => 4))) b cap prepared actual` by
    (irule abi_scratch_effect_widen >> qexistsl_tac [`p`, `final.cs_next_id`, `ready.cs_next_id`,
       `ready.cs_next_var`, `32+(case method_id_opt of NONE => 0 | SOME _ => 4)+LENGTH (enc at av)`] >>
     asm_simp_tac bool_ss [LESS_EQ_REFL] >> decide_tac) >>
  `start.cs_next_id < ready.cs_next_id` by
    (qpat_x_assum `ready.cs_next_id = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `method_id_opt` >> simp[]) >>
  `ready.cs_next_id <= final.cs_next_id` by decide_tac >>
  drule_all abi_scratch_builtin_effect_compose >> disch_tac >>
  drule_all abi_scratch_builtin_source_open >> strip_tac >>
  mp_tac (Q.INST [`bytes` |-> `enc at av`, `prefix` |-> `abi_builtin_encode_prefix method_id_opt`,
    `s` |-> `actual:venom_state`] abi_scratch_builtin_value) >>
  (impl_tac >-
    (qpat_x_assum `mload p actual = _` mp_tac >>
     qpat_x_assum `mem_bytes_at _ _ actual.vs_memory = enc at av` mp_tac >>
     qpat_x_assum `mem_bytes_at _ _ actual.vs_memory = mem_bytes_at _ _ prepared.vs_memory` mp_tac >>
     qpat_x_assum `mem_bytes_at _ _ prepared.vs_memory = abi_builtin_encode_prefix _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac (srw_ss()) [abi_scratch_builtin_prefix_length, ADD_COMM])) >> strip_tac >>
  `abi_decode_sim ctx func initial actual` by
    (irule abi_decode_sim_trans >> qexists_tac `prepared` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac (srw_ss()) [LENGTH_APPEND, abi_scratch_builtin_prefix_length, ADD_COMM]
QED

(* The source result depends only on encoding equality, not representative has_type. *)
Theorem lower_abi_encode_scratch_source_open_rep:
  let enc_ty = abi_builtin_encode_type ensure tys in
  let bytes = abi_encode_method_id_bytes method_id ++ enc (vyper_to_abi_type (get_tenv cx) enc_ty) av in
  let method_id_opt = OPTION_MAP bytes_method_id_word method_id in
  let mid_size = case method_id_opt of NONE => 0 | SOME (_:bytes32) => 4 in
  let write_size = case method_id_opt of NONE => 0 | SOME _ => 32 in
  let outsz = 32+32*word_size (maxlen+mid_size) in
  let allocated = abi_builtin_allocate_state start.cs_next_id outsz initial in
  well_typed_type_builtin_args (AbiEncode ensure method_id) (TupleT tys) tys /\
  LENGTH vs = LENGTH tys /\
  vyper_to_abi (get_tenv cx) enc_ty (abi_builtin_encode_value ensure tys vs) = SOME av /\
  enc ct rv = enc (vyper_to_abi_type (get_tenv cx) enc_ty) av /\
  lower_abi_encode ensure method_id_opt src
    (type_to_abi_enc_info ce.ce_struct_fields ce enc_ty) maxlen start = (out,final) /\
  fn_has_code start final func /\
  (start.cs_blocks = final.cs_blocks \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  abi_encoder_open_input (type_to_abi_enc_info ce.ce_struct_fields ce enc_ty) ct rv sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ abi_decoder_operand_live start.cs_next_var src /\
  sb+source_cap < dimword (:256) /\ p+outsz < dimword (:256) /\ LENGTH (enc ct rv) <= maxlen /\
  (sb+source_cap <= p \/ p+outsz <= sb) /\
  (sb+source_cap <= p+32 \/ p+32+write_size <= sb) /\
  ((FLOOKUP initial.vs_allocas start.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas start.cs_next_id = SOME (p,outsz)) /\
  start.cs_next_id < first /\ first <= start.cs_next_id+(case method_id_opt of NONE => 2 | SOME _ => 4) /\
  abi_decoder_budget first last b cap allocated /\
  abi_footprint_disjoint sb source_cap
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated) /\
  abi_footprint_disjoint p outsz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap allocated) /\
  final.cs_next_id <= last /\ final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. evaluate_type_builtin cx (AbiEncode ensure method_id) (TupleT tys) arg_tys vs = INL (BytesV bytes) /\
    eval_operand out actual = SOME (n2w p) /\ mload p actual = n2w (LENGTH bytes) /\
    mem_bytes_at (p+32) (LENGTH bytes) actual.vs_memory = bytes /\
    val_in_memory (BaseTV (BytesT (Dynamic (maxlen+LENGTH (abi_encode_method_id_bytes method_id)))))
      (BytesV bytes) p actual.vs_memory /\
    mem_bytes_at sb source_cap initial.vs_memory = mem_bytes_at sb source_cap actual.vs_memory /\
    abi_encoder_open_input (type_to_abi_enc_info ce.ce_struct_fields ce enc_ty) ct rv sb source_cap actual.vs_memory /\
    abi_scratch_builtin_effect first last start final limit_st p
      (32+32*word_size (maxlen+LENGTH (abi_encode_method_id_bytes method_id)))
      (case method_id of NONE => 0 | SOME _ => 32) b cap initial actual /\
    actual.vs_current_bb = final.cs_current_bb /\ actual.vs_inst_idx = LENGTH final.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_builtin_encode_checked_prefix >> strip_tac >>
  qpat_assum `well_typed_type_builtin_args _ _ _`
    (assume_tac o CONJUNCT1 o SIMP_RULE (srw_ss()) [well_typed_type_builtin_args_def]) >>
  drule_all abi_builtin_encode_source_result >> disch_then (qspec_then `method_id` assume_tac) >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM] lower_abi_encode_scratch_open)) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  qpat_assum `abi_builtin_encode_prefix _ = _` (fn prefix =>
    let val size = REWRITE_RULE [abi_scratch_builtin_prefix_length]
          (AP_TERM ``LENGTH:word8 list -> num`` prefix) in
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [prefix, size, abi_builtin_encode_store_case]) end) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [abi_scratch_builtin_prefix_length] >>
  gvs[]
QED
