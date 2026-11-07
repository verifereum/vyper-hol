(* Conditional source-only dynamic-array endpoint. *)
Theory entryReachBodySourceNonbulkConstructor
Ancestors
  entryReachBodySourceArrayConstructor entryReachBodySourceIterationCallback
  entryReachBodySourceArrayBounds entryReachBodySourceArrayInputs
  entryReachBodySourceMemberEntry entryReachBodySourceProducer
  entryReachBodyConditionalArrayConstructor entryReachBodyCanonicalArrayIteration
  entryReachBodyCanonicalArrayChild entryReachBodyOwnedRegion
  entryReachBodyOwnedLoop entryReachBodyOperationalPath entryReachBodyOperationalLoop
  entryReachBodyExactArrayLoop abiEncoderRegisteredEffect abiDecoderReentry
  abiDecoderCoherence abiDecoderContract abiDecoderExecution abiDecoderLoopCode
  abiDecoderRecursiveArray allocaFrontierBound abiAllocationHistory venomMemDefs
  compileEnv venomState venomInst venomExecSemantics valueEncoding valueEncodingTyping
  valueTypingMemoryProps vyperTyping vyperABI words list pred_set arithmetic

Theorem source_constructor_values[local]:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    root_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  sb+LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) ==>
  LENGTH avs = LENGTH xs /\ LENGTH xs < dimword (:256) /\ EVERY (val_wf tv) xs /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = type_memory_size (ArrayTV tv (Dynamic maxn)) /\
  32+LENGTH xs*type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  LENGTH xs <= maxn /\ 32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))
Proof
  strip_tac >>
  `LENGTH xs = LENGTH avs /\ LENGTH xs <= maxn` by
    (irule entry_source_dynamic_array_alignment >>
     gvs[entry_source_metadata_def, Excl "enc_def"] >> metis_tac[]) >>
  `LENGTH avs < dimword (:256)` by
    (irule entry_source_array_count_word_bound >>
     qexistsl_tac [`Dynamic maxn`, `env`, `sb`,
       `ArrayTV tv (Dynamic maxn)`, `ty`, `ArrayV (DynArrayV xs)`] >>
     gvs[entry_source_metadata_def, Once vyper_to_abi_type_def, Excl "enc_def"]) >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  drule abi_decoder_coherent_header >> strip_tac >>
  `type_memory_bytes ce ty = type_memory_size tv` by fs[abi_decoder_header_def] >>
  `EVERY (value_has_type tv) xs` by
    fs[entry_source_metadata_def, value_has_type_def, all_have_type_EVERY, Excl "enc_def"] >>
  `EVERY (val_wf tv) xs` by
    (fs[EVERY_MEM] >> metis_tac[cj 1 value_has_type_val_wf]) >>
  fs[entry_source_metadata_def, type_memory_bytes_def, Excl "enc_def"]
QED

Theorem entry_source_nonbulk_array_constructor:
  parent_di = DecDynArray (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) dyn maxn /\
  (dyn \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) parent_di st = ((),final) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    root_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb+LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st final fn /\ abi_decoder_code st final /\
  (final.cs_current_insts = [] ==> !bb.
    lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  oid NOTIN abi_decoder_ids st.cs_next_id final.cs_next_id /\
  window_alloca_sites fn (abi_decoder_ids st.cs_next_id final.cs_next_id) SUBSET ambient /\
  oid NOTIN ambient /\ entry_scratch_ready ambient b reserve s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  entry_owned_region oid root extent d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!j. j < LENGTH xs ==> entry_source_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0)
    ce env sf ty tv (EL j avs) (EL j xs)
    ctx fn oid root extent ambient b reserve site limit_st) ==>
  ?t. array_child_result ctx fn oid root extent ambient
    (window_alloca_sites fn (abi_decoder_ids st.cs_next_id final.cs_next_id))
    b reserve site limit_st st final d (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `parent_di = _` SUBST_ALL_TAC >>
  drule_all entry_source_array_compiler_config >> strip_tac >>
  rename1 `abi_decode_index_init header_st = (ip,loop_st)` >>
  drule_all source_constructor_values >> strip_tac >>
  drule abi_decoder_coherent_array_capacity >> disch_tac >>
  suspend "initialize"
QED
Resume entry_source_nonbulk_array_constructor[initialize]:
  `header_st.cs_next_id IN ambient` by metis_tac[SUBSET_DEF] >>
  `LENGTH avs <= maxn` by metis_tac[] >>
  drule_all conditional_array_initialization >>
  disch_then (qx_choose_then `pnum` (qx_choose_then `prepared` strip_assume_tac)) >>
  `iteration_callback_config
    ((ce,env,ty,tv,maxn,root_di,avs,xs),
     (ip,src,dst,body_st,ops,middle,last,limit_st,loop_st.cs_next_var,last.cs_next_var),
     (ctx,fn,site,header_st.cs_next_id,oid,root,extent,d,b,reserve,prepared,n2w pnum,sb,ambient),
     (FST labels,FST (SND labels),SND (SND labels),loop_st.cs_next_id+1,
      <|bb_label := last.cs_current_bb; bb_instructions := last.cs_current_insts ++
        abi_decode_backedge_insts last.cs_next_id (STRING #"%" (toString body_st.cs_next_var))
          (STRING #"%" (toString last.cs_next_var)) ip (FST labels)|>))` by
    (first_x_assum irule >> simp[]) >>
  qmatch_asmsub_abbrev_tac `iteration_callback_config cfg` >>
  suspend "iterate"
QED
Resume entry_source_nonbulk_array_constructor[iterate]:
  `last.cs_current_insts = [] ==> !bb.
    lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `iteration_callback_config cfg` mp_tac >>
     simp_tac bool_ss [Abbr `cfg`, iteration_callback_config_def] >>
     rpt strip_tac >> gvs[] >>
     simp[abi_decode_backedge_insts_def, phi_prefix_length_def, mk_inst_def]) >>
  `iteration_semantic_callback cfg` by
    (irule entry_source_certified_iteration_callback >> simp[Abbr `cfg`, Excl "enc_def"] >>
     goal_assum (drule_at Any) >> simp[Excl "enc_def"] >>
     goal_assum (drule_at Any) >> fs[Excl "enc_def"]) >>
  `pnum < dimword (:256)` by
    (qpat_x_assum `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ prepared` mp_tac >>
     simp[entry_owned_loop_resources_def, alloca_inv_def, alloca_next_valid_def] >>
     rpt strip_tac >>
     `prepared.vs_alloca_next < dimword (:256)` by
       (drule_all alloca_frontier_inv_bound >> simp[]) >>
     first_x_assum drule >> simp[] >> decide_tac) >>
  `?hdr_bb. lookup_block (FST labels) fn.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0` by
    (unabbrev_all_tac >> qhdtm_assum `iteration_callback_config`
       (strip_assume_tac o PURE_REWRITE_RULE [iteration_callback_config_def]) >>
     qhdtm_x_assum `abi_decode_loop_cfg`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_decode_loop_cfg_def]) >>
     qpat_assum `lookup_block (FST labels) fn.fn_blocks = SOME _` (irule_at Any) >>
     simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def]) >>
  drule_at (Pat `iteration_callback_config _`)
    (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] callback_array_prepared_endpoint) >>
  simp[Abbr `cfg`] >>
  disch_then (qspec_then `loop_st` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  suspend "result"
QED
Resume entry_source_nonbulk_array_constructor[result]:
  `abi_encoder_registered_effect
    (window_alloca_sites fn (abi_decoder_ids st.cs_next_id final.cs_next_id))
    [(d,type_memory_size (ArrayTV tv (Dynamic maxn)))] s t` by
    (irule abi_encoder_registered_effect_trans >> qexists_tac `prepared` >>
     conj_tac >-
       (irule abi_encoder_registered_effect_enlarge >>
        qpat_assum `abi_encoder_registered_effect _ _ s prepared` (irule_at Any) >>
        simp[SUBSET_DEF] >> rpt strip_tac >> decide_tac) >>
     irule abi_encoder_registered_effect_enlarge >>
     qpat_assum `abi_encoder_registered_effect _ _ prepared t` (irule_at Any) >>
     simp[INSERT_SUBSET] >> rpt strip_tac >> decide_tac) >>
  `entry_decode_path ctx fn s t` by metis_tac[entry_decode_path_trans] >>
  `entry_loop_fields s t` by fs[entry_loop_fields_def] >>
  qpat_x_assum `iteration_frame _ _ _ _ _ _ _ t`
    (strip_assume_tac o PURE_REWRITE_RULE [iteration_frame_def]) >>
  qpat_x_assum `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ t`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_owned_loop_resources_def]) >>
  qexists_tac `t` >> simp_tac bool_ss [array_child_result_def] >>
  simp[] >> rpt strip_tac >>
  `abi_decoder_operand_live loop_st.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  first_x_assum irule >> simp[]
QED
Finalise entry_source_nonbulk_array_constructor
