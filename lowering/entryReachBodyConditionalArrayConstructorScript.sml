(* Operational entry boundary for conditional nonbulk array constructors. *)
Theory entryReachBodyConditionalArrayConstructor
Ancestors
  entryReachBodyConditionalArray entryReachBodyOperationalHeader
  entryReachBodyCanonicalArrayIteration entryReachBodyOwnedRegion
  entryReachBodyExactArrayLoop abiDecoderFrame entryReachBodyOperationalLoop
  entryReachBodyConditionalProducer entryReachBodyReentryResources
  entryReachBodyRecursiveInterface entryReachBodyCanonicalBytesArray
  ctorAbiActualArrayRun abiDecoderArrayLoopInit compileEnv
  entryReachBodyScratchSet entryReachBodyOwnedLoop entryReachBodyOperationalPath
  allocaBudgetProps allocaFrontierBound abiAllocationHistory venomMemDefs
  abiDecoderLoop abiDecoderExecution abiDecoderContract
  abiEncoderRegisteredEffect venomState venomInst exprLoweringProps compileEnv
  entryReachBodyOwnedBytesArray abiCanonicalHeadSize abiDecoderTypedContract
  calldataRecursiveProducers abiDecoderRecursiveArray abiDecoderArrayInvariant
  abiDecoderCoherence abiDecoderRecursiveLoopLayout abiDecoderArraySetupInputs
  abiDecoderRecursiveLoopEntry abiDecoderCounters valueTypingMemoryProps vyperTyping
  actualDecoderSites abiEncoderWindowContract abiDecoderArrayInit abiDecoderLoopCode abiDecoderAllocation
  rich_list fragExec abiDecoderCode pred_set valueEncoding
  entryReachBodyCanonicalArrayChild abiDecoderReentry
  venomExecSemantics finite_map words list arithmetic

Theorem conditional_array_header_entry[local]:
  ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
  lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := loop_st.cs_current_bb; bb_instructions :=
      loop_st.cs_current_insts ++ [mk_inst loop_st.cs_next_id JMP [Label hdr] []]|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d capacity prepared /\
  eval_operand ip prepared = SOME p /\ eval_operand src prepared = SOME srcaddr /\
  mload (w2n p) prepared = 0w /\
  abi_decode_load CALLDATALOAD srcaddr prepared = n2w (LENGTH xs) /\
  fresh_vars_wrt limit_st prepared /\ mem_word_at d prepared.vs_memory = n2w (LENGTH xs) /\
  entry_scratch_ready ambient b reserve prepared ==>
  entry_decode_path ctx fn prepared (jump_to hdr prepared) /\
  entry_owned_loop_inv ctx fn site hdr ip src p srcaddr tv xs
    d capacity cid oid root extent 0 (jump_to hdr prepared) /\
  iteration_frame next limit_st prepared ambient b reserve
    (\m. mem_word_at d m = n2w (LENGTH xs)) (jump_to hdr prepared) /\
  entry_loop_fields prepared (jump_to hdr prepared) /\
  abi_encoder_registered_effect ids outs prepared (jump_to hdr prepared)
Proof
  strip_tac >> conj_tac
  >- (`prepared with vs_inst_idx := LENGTH loop_st.cs_current_insts = prepared` by
        simp[venom_state_component_equality] >>
      drule_all entry_initializer_header_jump_path >> simp[]) >>
  `remaining_alloca_budget (fn_insts fn) (jump_to hdr prepared) =
   remaining_alloca_budget (fn_insts fn) prepared` by
    (irule remaining_alloca_budget_domain_cong >> simp[jump_to_def]) >>
  gvs[entry_owned_loop_inv_def, entry_owned_loop_resources_def, entry_owned_region_def,
     abi_decode_loop_ready_def, entry_loop_prefix_def, iteration_frame_def,
     entry_scratch_ready_def, entry_scratch_missing_def,
     entry_loop_fields_def, abi_encoder_registered_effect_def,
     jump_to_def, alloca_frontier_inv_def, abi_alloca_history_def, alloca_inv_def,
     allocas_non_overlapping_def, alloca_next_valid_def,
     fresh_vars_wrt_def, eval_operand_def, lookup_var_def,
     abi_decode_load_def, abi_decode_source_def, mload_def,
     abi_decode_footprint_frame_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem callback_array_prepared_endpoint:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\ iteration_callback_config cfg /\
  iteration_semantic_callback cfg /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = ploop.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH ploop.cs_current_insts /\
  lookup_block ploop.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := ploop.cs_current_bb; bb_instructions :=
      ploop.cs_current_insts ++ [mk_inst ploop.cs_next_id JMP [Label hdr] []]|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) prepared /\
  eval_operand ip prepared = SOME p /\ eval_operand src prepared = SOME (n2w sb) /\
  mload (w2n p) prepared = 0w /\
  abi_decode_load CALLDATALOAD (n2w sb : bytes32) prepared = n2w (LENGTH xs) /\
  fresh_vars_wrt limit_st prepared /\ mem_word_at d prepared.vs_memory = n2w (LENGTH xs) /\
  entry_scratch_ready ambient b reserve prepared ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t /\
    iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)) t /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_loop_fields prepared t /\ entry_decode_path ctx fn prepared t /\
    abi_encoder_registered_effect
      (cid INSERT window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
      [(d,32+LENGTH xs*type_memory_size tv)] prepared t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `entry_decode_path ctx fn prepared (jump_to hdr prepared) /\
   entry_owned_loop_inv ctx fn site hdr ip src p (n2w sb) tv xs d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) cid oid root extent 0
     (jump_to hdr prepared) /\
   iteration_frame next limit_st prepared ambient b reserve
     (\m. mem_word_at d m = n2w (LENGTH xs)) (jump_to hdr prepared) /\
   entry_loop_fields prepared (jump_to hdr prepared) /\
   abi_encoder_registered_effect
     (cid INSERT window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
     [(d,32+LENGTH xs*type_memory_size tv)] prepared (jump_to hdr prepared)` by
    (irule conditional_array_header_entry >> simp[] >>
     qexists_tac `ploop` >> simp[] >> goal_assum (drule_at Any)) >>
  drule_all entry_generic_array_callback_iteration >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac[] >>
  qhdtm_x_assum `entry_loop_trace`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_loop_trace_def]) >>
  `entry_loop_fields prepared t` by fs[iteration_frame_def] >>
  asm_rewrite_tac[] >> conj_tac
  >- metis_tac[entry_decode_path_trans] >>
  irule abi_encoder_registered_effect_trans >>
  qexists_tac `jump_to hdr prepared` >> simp[]
QED

Theorem conditional_array_prepared_endpoint[local]:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\ iteration_static_config cfg /\
  (!k. k < LENGTH xs ==> entry_conditional_array_child_producer ce env ty tv
    (EL k avs) (EL k xs) ctx fn oid root extent ambient b reserve site limit_st) /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = ploop.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH ploop.cs_current_insts /\
  lookup_block ploop.cs_current_bb fn.fn_blocks = SOME
    <|bb_label := ploop.cs_current_bb; bb_instructions :=
      ploop.cs_current_insts ++ [mk_inst ploop.cs_next_id JMP [Label hdr] []]|> /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\ phi_prefix_length hdr_bb.bb_instructions = 0 /\
  entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) prepared /\
  eval_operand ip prepared = SOME p /\ eval_operand src prepared = SOME (n2w sb) /\
  mload (w2n p) prepared = 0w /\
  abi_decode_load CALLDATALOAD (n2w sb : bytes32) prepared = n2w (LENGTH xs) /\
  fresh_vars_wrt limit_st prepared /\ mem_word_at d prepared.vs_memory = n2w (LENGTH xs) /\
  entry_scratch_ready ambient b reserve prepared ==>
  ?t. ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0 /\
    entry_owned_loop_resources ctx fn site cid (w2n p) oid root extent d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t /\
    iteration_frame next limit_st prepared ambient b reserve
      (\m. mem_word_at d m = n2w (LENGTH xs)) t /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
    entry_loop_fields prepared t /\ entry_decode_path ctx fn prepared t /\
    abi_encoder_registered_effect
      (cid INSERT window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
      [(d,32+LENGTH xs*type_memory_size tv)] prepared t
Proof
  strip_tac >> drule iteration_static_callback_config >> strip_tac >>
  drule_all iteration_conditional_semantic_callback >> strip_tac >>
  drule_all callback_array_prepared_endpoint >> simp[]
QED

Theorem conditional_array_initializer_resources[local]:
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  alloca_inv s /\ abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  entry_owned_region oid root extent d sz s /\ 32 <= sz /\
  entry_scratch_ready ambient b reserve s /\ header_st.cs_next_id IN ambient ==>
  ?q. entry_array_init_resources dst src maxn abi_sz
      (st,guard_st,header_st,loop_st,ip,cnt)
      (ctx,fn,site,d,sz,b,reserve,q,s)
Proof
  strip_tac >> drule_all entry_index_counter_readiness >> strip_tac >>
  drule_all entry_scratch_initializer_room >> strip_tac >>
  qexists_tac `p` >> simp_tac bool_ss [entry_array_init_resources_def] >>
  `abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st)` by
    simp[abi_decode_array_loop_init_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def] >>
  `d+sz <= s.vs_alloca_next` by
    (fs[entry_owned_region_def, alloca_inv_def, alloca_next_valid_def] >>
     `root+extent <= s.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  drule ctor_actual_function_ids >> strip_tac >> fs[] >> metis_tac[]
QED

Theorem conditional_array_initializer_scratch[local]:
  entry_scratch_ready ambient b reserve s /\ cid IN ambient /\
  FLOOKUP t.vs_allocas cid = SOME (q,32) /\
  (!id. id <> cid ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (if FLOOKUP s.vs_allocas cid = NONE then
     q = s.vs_alloca_next /\ t.vs_alloca_next = s.vs_alloca_next+32
   else FLOOKUP s.vs_allocas cid = SOME (q,32) /\
     t.vs_alloca_next = s.vs_alloca_next) ==>
  entry_scratch_ready ambient b reserve t
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas cid = NONE` >> gvs[]
  >- (`t.vs_allocas = s.vs_allocas |+ (cid,(s.vs_alloca_next,32))` by
        (simp[fmap_eq_flookup, FLOOKUP_UPDATE] >> gen_tac >>
         Cases_on `x = cid` >> simp[]) >>
      irule entry_scratch_ready_insert >> qexistsl_tac [`cid`,`s`] >> simp[]) >>
  `t.vs_allocas = s.vs_allocas` by
    (simp[fmap_eq_flookup] >> gen_tac >> Cases_on `x = cid` >> simp[]) >>
  metis_tac[entry_scratch_ready_frame]
QED

Theorem conditional_array_initialized_scratch[local]:
  entry_array_init_resources dst src maxn asz
    (st,guard_st,header_st,loop_st,ip,cnt) (ctx,fn,site,d,sz,b,cap,p,s) /\
  entry_scratch_ready ambient b cap s /\ header_st.cs_next_id IN ambient /\
  entry_owned_loop_resources ctx fn site header_st.cs_next_id p oid root extent d sz t /\
  (!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
  (if FLOOKUP s.vs_allocas header_st.cs_next_id = NONE then
     t.vs_alloca_next = s.vs_alloca_next+32 else t.vs_alloca_next = s.vs_alloca_next) ==>
  entry_scratch_ready ambient b cap t
Proof
  strip_tac >> irule conditional_array_initializer_scratch >>
  qexistsl_tac [`header_st.cs_next_id`,`p`,`s`] >>
  gvs[entry_owned_loop_resources_def, entry_array_init_resources_def]
QED

(* Use the actual counter's 32-byte allocation, not the entire ambient
   scratch interval, for the initializer's disjointness precondition. *)
Theorem conditional_array_initialization:
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn asz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  (!i. MEM i (emitted_insts st loop_st) ==> MEM i (fn_insts fn)) /\
  fn_has_code st loop_st fn /\ fn_inst_ids_distinct fn /\
  unit_alloca_budget ctx < dimword (:256) /\
  alloca_inv s /\ abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  entry_owned_region oid root extent d sz s /\ 32 <= sz /\
  entry_scratch_ready ambient b reserve s /\ header_st.cs_next_id IN ambient /\ oid NOTIN ambient /\
  mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (Array NONE aty) (ListV avs) /\
  sb+LENGTH (enc (Array NONE aty) (ListV avs)) < dimword (:256) /\
  d+sz < dimword (:256) /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ LENGTH avs <= maxn /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?p t. entry_decode_path ctx fn s t /\
    entry_owned_loop_resources ctx fn site header_st.cs_next_id p oid root extent d sz t /\
    abi_encoder_registered_effect {header_st.cs_next_id} [(d,32)] s t /\
    entry_scratch_ready ambient b reserve t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    mem_word_at d t.vs_memory = n2w (LENGTH avs) /\
    abi_decode_load CALLDATALOAD (n2w sb : bytes32) t = n2w (LENGTH avs) /\
    entry_loop_fields s t /\ fresh_vars_wrt limit_st t /\ ~t.vs_halted /\
    t.vs_current_bb = loop_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    eval_operand src t = SOME (n2w sb) /\ eval_operand dst t = SOME (n2w d) /\
    mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV avs)))
      (abi_decode_source CALLDATALOAD t) = enc (Array NONE aty) (ListV avs)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all conditional_array_initializer_resources >>
  disch_then (qx_choose_then `p` assume_tac) >>
  `oid <> header_st.cs_next_id` by metis_tac[] >>
  `d+sz <= p \/ p+32 <= d` by
    (irule (cj 2 entry_owned_region_counter_separation) >>
     qexistsl_tac [`header_st.cs_next_id`,`extent`,`oid`,`root`,`s`] >>
     fs[entry_array_init_resources_def] >> metis_tac[]) >>
  `entry_array_init_resources dst src maxn asz
    (st,guard_st,header_st,loop_st,ip,cnt) (ctx,fn,site,d,sz,p,32,p,s)` by
    fs[entry_array_init_resources_def] >>
  `abi_decoder_ranges CALLDATALOAD (Lit 0w) src dst sb
    (LENGTH (enc (Array NONE aty) (ListV avs))) d sz p 32 s` by
    simp[abi_decoder_ranges_def, abi_decode_source_opcode_def] >>
  drule_all owned_array_canonical_initializer >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  drule_all conditional_array_initialized_scratch >> disch_tac >>
  `abi_decode_load CALLDATALOAD (n2w sb : bytes32) t = n2w (LENGTH avs)` by
    (irule canonical_dynamic_array_count_load >> qexists_tac `aty` >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`p`,`t`] >> asm_rewrite_tac[] >>
  qpat_x_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ t` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[abi_decoder_ranges_def]
QED

Theorem conditional_array_counter_in_window[local]:
  abi_decode_index_init header_st = (ip,loop_st) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  first <= header_st.cs_next_id /\ header_st.cs_next_id < stop ==>
  header_st.cs_next_id IN window_alloca_sites fn (abi_decoder_ids first stop)
Proof
  strip_tac >> drule_all actual_index_init_function_site >> strip_tac >>
  simp[window_alloca_sites_def, abi_decoder_ids_def] >> metis_tac[]
QED

Theorem conditional_array_initializer_contained[local]:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn asz st = ((ip,cnt),loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD loop_st = (labels,body_st) /\
  fn_has_code loop_st body_st fn ==>
  !i. MEM i (emitted_insts st loop_st) ==> MEM i (fn_insts fn)
Proof
  strip_tac >>
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

(* Compiler-only extraction: semantic states are quantified after witnesses. *)
Theorem callback_array_compiler_config:
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
      abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
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
              (STRING #"%" (toString last.cs_next_var)) ip (FST labels)|>))
    )
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
  drule_all conditional_array_counter_in_window >> disch_tac >>
  `!i. MEM i (emitted_insts st loop_st) ==> MEM i (fn_insts fn)` by
    (match_mp_tac (conditional_array_initializer_contained |>
       Q.INST [`asz` |-> `abi_embedded_static_size ce.ce_struct_fields ty`]) >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`guard_st`,`header_st`,`loop_st`,`ip`,`cnt`,`labels`,`body_st`,`ops`,`middle`,`last`] >>
  asm_rewrite_tac[] >> conj_tac >- suspend "entry_lookup" >>
  suspend "static_config"
QED
Resume callback_array_compiler_config[entry_lookup]:
  qpat_x_assum `fn_has_code loop_st body_st fn` mp_tac >>
  qpat_x_assum `body_st.cs_blocks = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[fn_has_code_def, emitted_blocks_def] >> rpt strip_tac >>
  first_x_assum (qspec_then
    `<|bb_label := loop_st.cs_current_bb; bb_instructions := loop_st.cs_current_insts ++
       [mk_inst loop_st.cs_next_id JMP [Label (FST labels)] []]|>` mp_tac) >> simp[]
QED
Resume callback_array_compiler_config[static_config]:
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
    (drule abi_decoder_dynarray_values >> simp[] >>
     drule abi_decoder_coherent_array_capacity >> simp[]) >>
  simp_tac bool_ss [iteration_callback_config_def] >>
  asm_rewrite_tac[] >> simp[] >>
  simp_tac bool_ss [abi_decode_loop_cfg_def] >>
  asm_rewrite_tac[] >> metis_tac[]
QED
Finalise callback_array_compiler_config

Theorem entry_conditional_nonbulk_array_constructor:
  parent_di = DecDynArray (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) dyn maxn /\
  (dyn \/ dec_info_needs_clamp (type_to_abi_dec_info ce.ce_struct_fields ce ty)) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) parent_di st = ((),final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\
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
  (!j. j < LENGTH xs ==> entry_conditional_array_child_producer ce env ty tv (EL j avs) (EL j xs)
    ctx fn oid root extent ambient b reserve site limit_st) ==>
  ?t. array_child_result ctx fn oid root extent ambient
    (window_alloca_sites fn (abi_decoder_ids st.cs_next_id final.cs_next_id))
    b reserve site limit_st st final d (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) s t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `parent_di = _` SUBST_ALL_TAC >>
  drule_all callback_array_compiler_config >> strip_tac >>
  rename1 `abi_decode_index_init header_st = (ip,loop_st)` >>
  suspend "initialize"
QED
Resume entry_conditional_nonbulk_array_constructor[initialize]:
  drule_all abi_decoder_dynarray_values >> strip_tac >>
  drule abi_decoder_coherent_array_capacity >> disch_tac >>
  `EVERY (val_wf tv) xs` by
    (qpat_x_assum `all_have_type tv xs` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     simp[all_have_type_EVERY, EVERY_MEM] >> metis_tac[value_has_type_memory_wf]) >>
  `type_memory_bytes ce ty = type_memory_size tv /\
   type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = type_memory_size (ArrayTV tv (Dynamic maxn))` by
    (qpat_assum `abi_decoder_coherent _ _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     drule abi_decoder_coherent_header >> strip_tac >>
     fs[abi_decoder_header_def, abi_decoder_coherent_array_iff] >>
     metis_tac[abi_decoder_coherent_header, abi_decoder_header_def]) >>
  suspend "phases"
QED
Resume entry_conditional_nonbulk_array_constructor[phases]:
  `header_st.cs_next_id IN ambient` by metis_tac[SUBSET_DEF] >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    simp[type_memory_size_def] >>
  mp_tac (conditional_array_initialization |> Q.INST
    [`asz` |-> `abi_embedded_static_size ce.ce_struct_fields ty`,
     `aty` |-> `vyper_to_abi_type env ty`,
     `sz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `pnum` (qx_choose_then `prepared` strip_assume_tac)) >>
  qpat_x_assum `!prepared pnum root_di sb d env tv avs xs ctx site oid root extent ambient b reserve. _`
    (qspecl_then [`prepared`,`pnum`,
      `DecDynArray (type_to_abi_dec_info ce.ce_struct_fields ce ty)
        (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) dyn maxn`] assume_tac) >>
  `32+LENGTH xs*type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (simp[type_memory_size_def] >> decide_tac) >>
  `LENGTH xs < dimword (:256)` by decide_tac >>
  qpat_x_assum `!sb d env tv avs xs ctx site oid root extent ambient b reserve. _`
    (mp_tac o SPEC_ALL) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `iteration_callback_config cfg` >>
  `iteration_static_config cfg` by
    (fs[Abbr `cfg`, iteration_callback_config_def, iteration_static_config_def,
        Excl "enc_def"] >> gvs[iteration_callback_config_def, Excl "enc_def"]) >>
  `pnum < dimword (:256)` by
    (qpat_x_assum `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ prepared` mp_tac >>
     simp[entry_owned_loop_resources_def, alloca_inv_def, alloca_next_valid_def] >>
     rpt strip_tac >>
     `prepared.vs_alloca_next < dimword (:256)` by
       (drule_all alloca_frontier_inv_bound >> simp[]) >>
     first_x_assum drule >> simp[] >> decide_tac) >>
  `?hdr_bb. lookup_block (FST labels) fn.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0` by
    (qpat_x_assum `iteration_static_config cfg` mp_tac >>
     simp[Abbr `cfg`, iteration_static_config_def, abi_decode_loop_cfg_def] >>
     rpt strip_tac >> simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def]) >>
  drule_at (Pat `iteration_static_config _`)
    (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] conditional_array_prepared_endpoint) >>
  simp[Abbr `cfg`] >>
  disch_then (qspec_then `loop_st` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  suspend "result"
QED
Resume entry_conditional_nonbulk_array_constructor[result]:
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
  suspend "finish"
QED
Resume entry_conditional_nonbulk_array_constructor[finish]:
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
Finalise entry_conditional_nonbulk_array_constructor
