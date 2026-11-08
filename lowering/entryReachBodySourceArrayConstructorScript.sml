(* Source-only nonbulk array compiler configuration. *)
Theory entryReachBodySourceArrayConstructor
Ancestors
  valueEncodingDefs entryReachBodySourceIterationCallback entryReachBodySourceIterationInputs
  entryReachBodySourceArrayInputs entryReachBodySourceMemberEntry
  entryReachBodySourceArrayBounds
  entryReachBodyConditionalArrayConstructor entryReachBodyCanonicalArrayIteration
  entryReachBodyCanonicalBytesArray calldataRecursiveProducers
  abiDecoderLoop abiDecoderArrayLoopInit abiDecoderRecursiveLoopLayout
  abiDecoderRecursiveLoopEntry abiDecoderRecursiveArray abiDecoderArraySetupInputs
  abiDecoderCounters abiDecoderCode abiDecoderReentry abiDecoderArrayInit
  abiDecoderLoopCode abiDecoderContract abiDecoderExecution abiDecoderCoherence
  actualDecoderSites abiEncoderWindowContract abiDecoderAllocation
  exprLoweringProps fragExec compileEnv venomInst venomState venomExecSemantics
  vyperTyping valueEncoding words list rich_list pred_set arithmetic

Theorem entry_source_array_compiler_config:
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w)
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) dyn maxn)
    st = ((),final) /\
  (dyn \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  fn_has_code st final fn /\ final.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  (final.cs_current_insts = [] ==> !bb. lookup_block final.cs_current_bb fn.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) ==>
  ?guard_st header_st loop_st ip cnt labels body_st ops middle last.
    abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn
      (abi_embedded_static_size ce.ce_struct_fields ty) st = ((),guard_st) /\
    abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\
    fn_has_code st loop_st fn /\
    (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
    (!i. MEM i (emitted_insts st loop_st) ==> MEM i (fn_insts fn)) /\
    header_st.cs_next_id IN window_alloca_sites fn (abi_decoder_ids st.cs_next_id final.cs_next_id) /\
    loop_st.cs_next_var <= limit_st.cs_next_var /\
    st.cs_next_var <= loop_st.cs_next_var /\
    window_alloca_sites fn (abi_decoder_ids middle.cs_next_id last.cs_next_id) SUBSET
      window_alloca_sites fn (abi_decoder_ids st.cs_next_id final.cs_next_id) /\
    final.cs_current_bb = SND (SND labels) /\ final.cs_current_insts = [] /\
    lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME
      <|bb_label := loop_st.cs_current_bb; bb_instructions := loop_st.cs_current_insts ++
        [mk_inst loop_st.cs_next_id JMP [Label (FST labels)] []]|> /\
    abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) (abi_embedded_static_size ce.ce_struct_fields ty)
      (type_memory_bytes ce ty) body_st = (ops,middle) /\
    compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) middle = ((),last) /\
    (!prepared pnum root_di sb d env tv avs xs ctx (site : instruction) oid (root : num) (extent : num) ambient (b : num) (reserve : num).
      abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
      entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
        root_di (ListV avs) (ArrayV (DynArrayV xs)) /\
      mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
        (abi_decode_source CALLDATALOAD prepared) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
      sb+LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
      d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
      eval_operand ip prepared = SOME (n2w pnum) /\
      eval_operand src prepared = SOME (n2w sb) /\ eval_operand dst prepared = SOME (n2w d) /\
      abi_decode_load CALLDATALOAD (n2w sb : bytes32) prepared = n2w (LENGTH xs) /\
      fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
      oid NOTIN abi_decoder_ids st.cs_next_id final.cs_next_id /\
      window_alloca_sites fn (abi_decoder_ids st.cs_next_id final.cs_next_id) SUBSET ambient /\
      oid NOTIN ambient /\ LENGTH xs < dimword (:256) /\ EVERY (val_wf tv) xs /\
      type_memory_bytes ce ty = type_memory_size tv /\
      32+LENGTH xs*type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) ==>
      iteration_callback_config
        ((ce,env,ty,tv,maxn,root_di,avs,xs),
         (ip,src,dst,body_st,ops,middle,last,limit_st,loop_st.cs_next_var,last.cs_next_var),
         (ctx,fn,site,header_st.cs_next_id,oid,root,extent,d,b,reserve,prepared,n2w pnum,sb,ambient),
         (FST labels,FST (SND labels),SND (SND labels),loop_st.cs_next_id+1,
          <|bb_label := last.cs_current_bb; bb_instructions := last.cs_current_insts ++
            abi_decode_backedge_insts last.cs_next_id (STRING #"%" (toString body_st.cs_next_var))
              (STRING #"%" (toString last.cs_next_var)) ip (FST labels)|>)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_nonbulk_parent_shell_conditional >> strip_tac >>
  rename1 `abi_decode_index_init header_st = (ip,loop_st)` >>
  rename1 `abi_decode_array_element_setup _ _ _ _ _ _ _ _ body_st = (ops,middle)` >>
  rename1 `compile_abi_decode_to_buf _ _ _ _ _ middle = ((),last)` >>
  drule_all entry_bytes_array_initial_live >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  qpat_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ body_st = _`
    (mp_then Any strip_assume_tac abi_decode_array_element_setup_operands) >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ middle = _`
    (mp_then Any strip_assume_tac abi_decoder_variable_counter) >>
  qpat_assum `abi_decode_loop_suffix _ _ _ _ last = _` mp_tac >>
  qpat_assum `FST ops = _` (fn th => pure_rewrite_tac [th]) >>
  disch_then (mp_then Any strip_assume_tac abi_decoder_loop_suffix_facts) >>
  `st.cs_next_var <= loop_st.cs_next_var` by
    (drule abi_decode_array_loop_init_shape >> simp[abi_decode_source_opcode_def] >>
     rpt strip_tac >> decide_tac) >>
  `window_alloca_sites fn (abi_decoder_ids middle.cs_next_id last.cs_next_id) SUBSET
    window_alloca_sites fn (abi_decoder_ids st.cs_next_id final.cs_next_id)` by
    (simp[window_alloca_sites_def, abi_decoder_ids_def, SUBSET_DEF] >>
     rpt strip_tac >> simp[] >> decide_tac) >>
  `loop_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `header_st.cs_next_id < final.cs_next_id` by decide_tac >>
  `header_st.cs_next_id IN window_alloca_sites fn (abi_decoder_ids st.cs_next_id final.cs_next_id)` by
    (drule_all actual_index_init_function_site >> strip_tac >>
     simp[window_alloca_sites_def, abi_decoder_ids_def] >> metis_tac[]) >>
  `!i. MEM i (emitted_insts st loop_st) ==> MEM i (fn_insts fn)` by
    suspend "initializer_contained" >>
  qexistsl_tac [`guard_st`,`header_st`,`loop_st`,`ip`,`cnt`,`labels`,`body_st`,`ops`,`middle`,`last`] >>
  asm_rewrite_tac[] >> conj_tac >- suspend "entry_lookup" >>
  suspend "source_config"
QED
Resume entry_source_array_compiler_config[initializer_contained]:
  `?bb. lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX loop_st.cs_current_insts bb.bb_instructions` by
    (drule abi_decoder_loop_prefix_extends >> strip_tac >>
     drule_all fn_has_code_start >> simp[]) >>
  rpt strip_tac >> irule lookup_block_fn_insts >>
  qexistsl_tac [`bb`,`loop_st.cs_current_bb`] >> simp[] >>
  irule IS_PREFIX_MEM >> qexists_tac `loop_st.cs_current_insts` >> simp[] >>
  irule MEM_DROP_IMP >> qexists_tac `LENGTH st.cs_current_insts` >>
  drule abi_decode_array_loop_init_shape >> simp[abi_decode_source_opcode_def] >>
  strip_tac >> fs[emitted_insts_def]
QED
Resume entry_source_array_compiler_config[entry_lookup]:
  qpat_x_assum `fn_has_code loop_st body_st fn` mp_tac >>
  qpat_x_assum `body_st.cs_blocks = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[fn_has_code_def, emitted_blocks_def] >> rpt strip_tac >>
  first_x_assum (qspec_then
    `<|bb_label := loop_st.cs_current_bb; bb_instructions := loop_st.cs_current_insts ++
       [mk_inst loop_st.cs_next_id JMP [Label (FST labels)] []]|>` mp_tac) >> simp[]
QED
Resume entry_source_array_compiler_config[source_config]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_code middle last` by
    (qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ middle = _`
       (mp_then Any mp_tac abi_decoder_to_buf_code) >>
     simp[abi_decode_source_opcode_def]) >>
  `oid <> header_st.cs_next_id` by metis_tac[SUBSET_DEF] >>
  `oid NOTIN abi_decoder_ids middle.cs_next_id last.cs_next_id` by
    (fs[abi_decoder_ids_def] >> decide_tac) >>
  `window_alloca_sites fn (abi_decoder_ids middle.cs_next_id last.cs_next_id) SUBSET ambient` by
    (fs[window_alloca_sites_def, abi_decoder_ids_def, SUBSET_DEF] >>
     rpt strip_tac >> first_x_assum irule >> simp[] >> decide_tac) >>
  `LENGTH xs <= maxn /\ 32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (conj_tac
     >- (irule (cj 2 entry_source_dynamic_array_alignment) >>
         fs[entry_source_metadata_def, Excl "enc_def"] >> metis_tac[]) >>
     simp[type_memory_bytes_def]) >>
  simp_tac bool_ss [iteration_callback_config_def] >>
  asm_rewrite_tac[] >> simp[] >>
  simp_tac bool_ss [abi_decode_loop_cfg_def] >>
  asm_rewrite_tac[] >> metis_tac[]
QED
Finalise entry_source_array_compiler_config
