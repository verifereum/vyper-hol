(* Pure compiler boundaries for actual-site canonical array execution. *)
Theory ctorAbiActualArrayLayout
Ancestors
  abiDecoderArrayLoopInit abiDecoderLoopEmit abiDecoderRecursiveLoopLayout
  abiDecoderRecursiveLoopContext abiDecoderLoopCode abiDecoderIndexInit
  abiDecoderCode abiDecoderCounters abiDecoderExecution abiDecoderArraySetupCode
  abiDecoderContract abiDecoderArraySetupInputs abiDecoderAppend exprLoweringProps
  actualDecoderSites ctorAbiActualSites ctorAbiActualAlloc abiEncoderProps
  fragExec emitHelperProps emitHelper compileEnv venomInst venomExecSemantics
  words list rich_list arithmetic pred_set

Theorem ctor_actual_array_loop_trace:
  compile_abi_decode_to_buf dst src DLOAD hi
    (DecDynArray ei asz msz elem_dyn maxn) st = ((),st') /\
  (elem_dyn \/ dec_info_needs_clamp ei) ==>
  ?guard_st header_st loop_st cnt ip labels body_st ops middle end_st.
    abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),guard_st) /\
    abi_decode_array_header dst src DLOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\
    abi_decode_loop_prefix ip src DLOAD loop_st = (labels,body_st) /\
    abi_decode_array_element_setup ip src dst DLOAD hi ei asz msz body_st = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD hi ei middle = ((),end_st) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),st')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_loop_array_trace >> strip_tac >>
  drule abi_decode_array_loop_init_trace >> strip_tac >>
  gvs[] >> drule abi_decode_dyn_loop_trace >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ctor_actual_array_setup_code:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),guard_st) /\
  abi_decode_array_header dst src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src DLOAD loop_st = (labels,body_st) /\
  abi_decode_array_element_setup ip src dst DLOAD hi ei asz msz body_st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD hi ei middle = ((),end_st) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),st') /\
  fn_has_code st st' func ==>
  fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
  fn_has_code header_st loop_st func /\ fn_has_code loop_st st' func /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func))
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule abi_decoder_loop_prefix_extends >> strip_tac >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  `cs_extends st guard_st /\ cs_extends guard_st header_st /\
   cs_extends header_st loop_st /\ cs_extends body_st middle` by
    (rpt conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, IS_PREFIX_APPEND, APPEND_ASSOC]) >>
  `cs_extends end_st st'` by
    (qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [] >> metis_tac[abi_decoder_loop_suffix_extends]) >>
  `cs_extends loop_st st'` by
    metis_tac[cs_extends_trans] >>
  `cs_extends header_st st'` by metis_tac[cs_extends_trans] >>
  `cs_extends guard_st st'` by metis_tac[cs_extends_trans] >>
  drule_all fn_has_code_split >> strip_tac >>
  `fn_has_code guard_st header_st func /\ fn_has_code header_st st' func` by
    (irule fn_has_code_split >> simp[]) >>
  `fn_has_code header_st loop_st func /\ fn_has_code loop_st st' func` by
    (irule fn_has_code_split >> simp[]) >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `?bb. lookup_block loop_st.cs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX loop_st.cs_current_insts bb.bb_instructions` by
    (irule fn_has_code_start >> qexists `st'` >> simp[]) >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  fs[emitted_insts_def, IS_PREFIX_APPEND, MEM_APPEND] >>
  metis_tac[MEM_DROP_IMP]
QED

Theorem ctor_actual_array_index_site:
  abi_decode_index_init header_st = (ip,loop_st) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
  st.cs_next_id <= header_st.cs_next_id /\ loop_st.cs_next_id <= st'.cs_next_id ==>
  header_st.cs_next_id IN ctor_actual_sites func (frag_ids st st')
Proof
  strip_tac >> drule_all actual_index_init_function_site >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  simp[ctor_actual_sites_def, frag_ids_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem ctor_actual_array_loop_compiled:
  abi_decode_dynarray_prefix src DLOAD hi maxn
    (abi_embedded_static_size ce.ce_struct_fields ty) st = ((),guard_st) /\
  abi_decode_array_header dst src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src DLOAD loop_st = (labels,body_st) /\
  abi_decode_array_element_setup ip src dst DLOAD hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
    body_st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),st') /\
  fn_has_code st st' func /\
  (!bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  st'.cs_next_var <= limit_st.cs_next_var ==>
  abi_decoder_recursive_loop_compiled ce sf ty func body_st middle end_st ops ip src dst
    DLOAD hi (FST labels) (SND (SND labels)) (loop_st.cs_next_id+1)
    loop_st.cs_next_var st.cs_next_id st'.cs_next_id st.cs_next_id st'.cs_next_id
    loop_st.cs_next_var limit_st header_st.cs_next_id
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_setup_code >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  irule abi_decoder_recursive_loop_layout >>
  asm_rewrite_tac[] >>
  simp[]
QED

Theorem ctor_actual_array_loop_intervals:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),guard_st) /\
  abi_decode_array_header dst src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src DLOAD loop_st = (labels,body_st) /\
  abi_decode_array_element_setup ip src dst DLOAD hi ei asz msz body_st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD hi ei middle = ((),end_st) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),st') ==>
  st.cs_next_id <= header_st.cs_next_id /\ loop_st.cs_next_id <= st'.cs_next_id /\
  frag_ids body_st end_st SUBSET frag_ids st st' /\
  header_st.cs_next_id NOTIN frag_ids middle end_st
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  drule_all abi_decoder_to_buf_code >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  fs[abi_decoder_code_def, frag_ids_def, SUBSET_DEF] >> rpt strip_tac >> decide_tac
QED

Theorem ctor_actual_array_loop_changes_blocks:
  abi_decode_dynarray_prefix src DLOAD hi maxn asz st = ((),guard_st) /\
  abi_decode_array_header dst src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src DLOAD loop_st = (labels,body_st) /\
  abi_decode_array_element_setup ip src dst DLOAD hi ei asz msz body_st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD hi ei middle = ((),end_st) /\
  abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),st') ==>
  st.cs_blocks <> st'.cs_blocks
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [] >> strip_tac >>
  drule abi_decoder_loop_suffix_facts >> strip_tac >>
  fs[cs_extends_def] >> strip_tac >>
  `LENGTH st.cs_blocks = LENGTH st'.cs_blocks` by asm_rewrite_tac[] >>
  fs[]
QED

Theorem ctor_actual_array_loop_layout:
  compile_abi_decode_to_buf dst src DLOAD hi
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) elem_dyn maxn)
    st = ((),st') /\
  (elem_dyn \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  fn_has_code st st' func /\
  (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
  st'.cs_next_var <= limit_st.cs_next_var ==>
  ?guard_st header_st loop_st cnt ip labels body_st ops middle end_st.
    abi_decode_dynarray_prefix src DLOAD hi maxn
      (abi_embedded_static_size ce.ce_struct_fields ty) st = ((),guard_st) /\
    abi_decode_array_header dst src DLOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\
    abi_decode_loop_prefix ip src DLOAD loop_st = (labels,body_st) /\
    abi_decode_array_element_setup ip src dst DLOAD hi (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      body_st = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD hi
      (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
    abi_decode_loop_suffix ip (FST ops) (FST labels) (SND (SND labels)) end_st = ((),st') /\
    fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
    fn_has_code header_st loop_st func /\ fn_has_code loop_st st' func /\
    (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
    abi_decoder_recursive_loop_compiled ce sf ty func body_st middle end_st ops ip src dst
      DLOAD hi (FST labels) (SND (SND labels)) (loop_st.cs_next_id+1)
      loop_st.cs_next_var st.cs_next_id st'.cs_next_id st.cs_next_id st'.cs_next_id
      loop_st.cs_next_var limit_st header_st.cs_next_id /\
    frag_ids body_st end_st SUBSET frag_ids st st' /\
    header_st.cs_next_id NOTIN frag_ids middle end_st /\
    header_st.cs_next_id IN ctor_actual_sites func (frag_ids st st')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_actual_array_loop_trace >> strip_tac >>
  drule_all ctor_actual_array_loop_changes_blocks >> strip_tac >>
  `!bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  drule_all ctor_actual_array_setup_code >> strip_tac >>
  drule_all ctor_actual_array_loop_intervals >> strip_tac >>
  drule_all ctor_actual_array_index_site >> strip_tac >>
  drule_all ctor_actual_array_loop_compiled >> strip_tac >>
  qexistsl [`guard_st`, `header_st`, `loop_st`, `cnt`, `ip`, `labels`,
    `body_st`, `ops`, `middle`, `end_st`] >> asm_rewrite_tac[]
QED
