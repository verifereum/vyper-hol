Theory abiScratchArrayCount
Ancestors
  abiCallerAllocation abiEncoderArrayCount abiEncoderArrayPrefix abiEncoderInputFrame
  abiEncoderInput abiDecoderArrayHeader abiDecoderFrameCompose abiDecoderFrame
  abiDecoderContract abiDecoderReentry compileEnv valueEncoding valueEncodingProps contractABI
  venomState finite_map words list arithmetic abiScratchLeafEffect abiScratchInput
  abiScratchEncoderContract abiDecodeRanges abiDecoderArrayLoopInit abiDecoderGuards
  abiDecoderLoop venomInst

(* ===== Scratch Array Count ===== *)

(* Actual array count copying preserves the complete source outside its output.
   TOP-LEVEL: abi_scratch_array_count_caller derives this separation from
   distinct live allocations; no separation from a scratch arena is required. *)

Theorem abi_scratch_array_count_separate:
  alloca_inv s /\ FLOOKUP s.vs_allocas source_id = SOME (sb,source_cap) /\
  FLOOKUP s.vs_allocas output_id = SOME (d,output_size) /\
  source_id <> output_id /\ 32 <= output_size ==>
  abi_footprint_disjoint sb source_cap [(d,32)]
Proof
  strip_tac >> drule_all abi_caller_allocation_separate >>
  simp[abi_footprint_disjoint_def] >> decide_tac
QED

Theorem abi_scratch_array_count_reach:
  abi_decode_array_header dst src MLOAD st = (cnt,st') /\ fn_has_code st st' func /\
  abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ d < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  abi_footprint_disjoint sb source_cap [(d,32)] /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    eval_operand cnt actual = SOME (n2w (LENGTH avs)) /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >>
  `mload sb initial = n2w (LENGTH avs)` by
    fs[abi_encoder_array_input_iff, mem_word_at_eq_mload] >>
  drule_all abi_encoder_array_count_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_decode_footprint_frame [(d,32)] initial actual` by
    fs[abi_decode_frame_footprint] >>
  drule_all abi_encoder_input_frame >> disch_then assume_tac >>
  `abi_encoder_array_prefix ty avs 0 d actual.vs_memory` by
    (irule abi_encoder_array_prefix_empty >> simp[]) >>
  qexists_tac `actual` >> simp[]
QED

Theorem abi_scratch_array_count_caller:
  abi_decode_array_header dst src MLOAD st = (cnt,st') /\ fn_has_code st st' func /\
  abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    sb source_cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ sb < dimword (:256) /\ d < dimword (:256) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  alloca_inv initial /\
  FLOOKUP initial.vs_allocas source_id = SOME (sb,source_cap) /\
  FLOOKUP initial.vs_allocas output_id = SOME (d,output_size) /\
  source_id <> output_id /\ 32 <= output_size /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_encoder_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      sb source_cap actual.vs_memory /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    eval_operand cnt actual = SOME (n2w (LENGTH avs)) /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d 32 initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op initial = SOME w ==>
      eval_operand op actual = SOME w) /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  strip_tac >> drule_all abi_scratch_array_count_separate >> disch_then assume_tac >>
  drule_all abi_scratch_array_count_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >> qexists_tac `actual` >> simp[]
QED

(* ===== Prepare ===== *)

(* The actual count copy establishes the complete precise loop input.
   TOP-LEVEL: abi_scratch_array_count_prepare preserves source data and
   physical separation and records an output-only effect with fixed allocation.
   Helper: complete array input supplies the layout, count and count-word bounds. *)

Theorem abi_scratch_array_input_facts:
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap s ==>
  has_type (Array NONE ty) (ListV avs) /\ asz = abi_member_head_size ty /\ active = is_dynamic ty /\
  mload sb s = n2w (LENGTH avs) /\ sb < dimword (:256) /\ d < dimword (:256) /\
  32 <= output_size /\ abi_footprint_disjoint sb source_cap [(d,32)]
Proof
  simp_tac bool_ss [abi_scratch_input_def] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `ct` (qx_choose_then `values` (MAP_EVERY assume_tac o CONJUNCTS)) o
      REWRITE_RULE [abi_encoder_array_input_iff]) >>
  `has_type (Array NONE ty) (ListV avs)` by gvs[] >>
  drule canonical_array_length >> strip_tac >>
  gvs[mem_word_at_eq_mload, Excl "enc_def"] >>
  simp[abi_footprint_disjoint_def] >> decide_tac
QED

Theorem abi_scratch_array_count_prepare:
  abi_decode_array_header dst src MLOAD st = (cnt,st') /\ fn_has_code st st' func /\
  abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st src dst sb source_cap d output_size first last b cap initial /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\ st'.cs_next_id <= last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
      st' src dst sb source_cap d output_size first last b cap actual /\
    abi_encoder_array_prefix ty avs 0 d actual.vs_memory /\
    abi_decoder_operand_live st'.cs_next_var cnt /\ eval_operand cnt actual = SOME (n2w (LENGTH avs)) /\
    abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial actual /\
    actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_scratch_array_input_facts >> strip_tac >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  drule abi_encoder_array_count_live >> disch_tac >>
  mp_tac (Q.INST [`opc` |-> `MLOAD`] abi_decode_array_header_shape) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_decode_source_opcode_def] >> strip_tac >>
  drule_all abi_scratch_array_count_reach >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func initial actual` >>
  `abi_decode_frame d output_size initial actual` by
    (irule abi_decode_frame_widen >> qexistsl_tac [`d`, `32`] >> simp[]) >>
  `abi_scratch_effect first last st.cs_next_id st'.cs_next_id st.cs_next_var
    limit_st d output_size b cap initial actual` by
    (irule abi_scratch_leaf_effect >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`ei` |-> `AbiDynArray ei asz msz active`, `at` |-> `Array NONE ty`, `av` |-> `ListV avs`,
    `lo` |-> `st.cs_next_id`, `hi` |-> `st'.cs_next_id`, `next` |-> `st.cs_next_var`,
    `sz` |-> `output_size:num`] abi_scratch_input_effect) >>
  impl_tac >- asm_simp_tac bool_ss [LESS_EQ_REFL] >> disch_tac >>
  `st.cs_next_var <= st'.cs_next_var` by decide_tac >>
  `abi_scratch_input (AbiDynArray ei asz msz active) (Array NONE ty) (ListV avs)
    st' src dst sb source_cap d output_size first last b cap actual` by
    (irule abi_scratch_input_mono >> qexists_tac `st` >> asm_simp_tac bool_ss []) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED
