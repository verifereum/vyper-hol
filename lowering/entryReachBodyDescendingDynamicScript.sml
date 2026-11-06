(* Navigation through the actual descending dynamic-array descriptor. *)
Theory entryReachBodyDescendingDynamic
Ancestors
  entryReachBodyDescendingProducer entryReachBodyDescendingMetadata entryReachBodyCanonicalArrayEntry
  entryReachBodyCanonicalArrayChild entryReachBodyConditionalArrayConstructor
  abiDecoderArraySetupInputs abiDecoderArraySlice abiDecoderArrayInvariant
  abiDecoderDynamic abiDecoderOffset abiCanonicalHeadSize
  entryReachBodyMemberSetup entryReachBodyOwnedRegion
  abiDecoderContract abiDecoderCoherence compileEnv venomState words list rich_list arithmetic
  abiDecoderExecution venomInst venomExecSemantics abiEncoderWindowContract
  abiDecoderAllocation abiEncoder pred_set entryReachBodyCanonicalArrayIteration
  entryReachBodyOwnedLoop abiEncoderRegisteredEffect finite_map abiDecoderReentry
  abiDecoderRecursiveArray valueTypingMemoryProps vyperTyping
  allocaFrontierBound abiAllocationHistory venomMemDefs valueEncoding
  entryReachBodyOperationalPath entryReachBodyOperationalLoop entryReachBodyExactArrayLoop

Theorem descending_array_navigation_split[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    (abi_decode_source CALLDATALOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))) < dimword (:256) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w (LENGTH pre) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st mid fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. array_entry_navigation ctx fn st mid limit_st ops sb
    (abi_array_child_offset NONE (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))
    d (LENGTH pre) (type_memory_bytes ce ty) s u
Proof
  strip_tac >> drule_all abi_decoder_dynarray_child_layout >> strip_tac >>
  drule abi_decoder_array_child_offset >> strip_tac >>
  `abi_decoder_header ce env ty tv` by metis_tac[abi_decoder_coherent_header] >>
  `abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty)` by
    fs[abi_decoder_header_def] >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- suspend "dynamic" >>
  drule array_entry_static_endpoint >> asm_simp_tac bool_ss [] >>
  disch_then drule_all >> disch_then (qspec_then `ctx` strip_assume_tac) >> qexists_tac `u` >>
  pure_rewrite_tac[array_entry_navigation_def] >>
  qpat_assum `LENGTH pre = LENGTH vpre` (fn th => pure_rewrite_tac[GSYM th]) >>
  pure_rewrite_tac[abi_array_child_offset_append] >> gvs[Excl "enc_def"]
QED
Resume descending_array_navigation_split[dynamic]:
  `abi_decode_load CALLDATALOAD
     (n2w (sb+32+LENGTH pre * abi_embedded_static_size ce.ce_struct_fields ty) : bytes32) s =
     n2w (LENGTH (pre ++ av::post) * abi_member_head_size (vyper_to_abi_type env ty) +
       SUM (MAP (abi_member_tail_size (vyper_to_abi_type env ty)) pre))` by
    (drule abi_decoder_canonical_dynamic_setup_inputs >>
     asm_simp_tac bool_ss [] >>
     disch_then (qspecl_then [`sb`, `s`, `CALLDATALOAD`, `Lit 0w`] mp_tac) >>
     (impl_tac >- gvs[Excl "enc_def"]) >> simp[]) >>
  gvs[Excl "enc_def"] >>
  drule array_entry_dynamic_endpoint >> asm_simp_tac bool_ss [] >>
  disch_then drule_all >> disch_then (qspec_then `ctx` strip_assume_tac) >> qexists_tac `u` >>
  pure_rewrite_tac[array_entry_navigation_def] >>
  qpat_assum `LENGTH pre = LENGTH vpre` (fn th => pure_rewrite_tac[GSYM th]) >>
  pure_rewrite_tac[abi_array_child_offset_append] >> gvs[Excl "enc_def"]
QED
Finalise descending_array_navigation_split

Theorem descending_array_owned_entry[local]:
  !off cell total.
  off = abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j /\
  cell = d+32+j*type_memory_bytes ce ty /\
  total = type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\ j < LENGTH xs /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  d+total < dimword (:256) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st mid fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ entry_owned_region oid root extent d total s /\
  entry_scratch_ready sites b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s ==>
  ?u. array_entry_navigation ctx fn st mid limit_st ops sb off d j (type_memory_bytes ce ty) s u /\
    abi_decoder_coherent ce env sf ty tv /\
    entry_descending_metadata ce env sf ty tv (type_to_abi_dec_info sf ce ty) (EL j avs) (EL j xs) /\
    mem_bytes_at (sb+off) (LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)))
      (abi_decode_source CALLDATALOAD u) = enc (vyper_to_abi_type env ty) (EL j avs) /\
    sb+off+LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)) < dimword (:256) /\
    cell+type_memory_size tv < dimword (:256) /\
    entry_owned_region oid root extent cell (type_memory_size tv) u /\
    entry_scratch_ready sites b cap u /\ alloca_inv u /\
    abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u
Proof
  rpt gen_tac >> strip_tac >> drule abi_decoder_dynarray_values >> strip_tac >>
  qabbrev_tac `av = EL j avs` >> qabbrev_tac `v = EL j xs` >>
  `?pre post vpre vpost.
    avs = pre ++ av::post /\ xs = vpre ++ v::vpost /\
    LENGTH pre = j /\ LENGTH vpre = j` by
    (qexistsl_tac [`TAKE j avs`, `DROP (SUC j) avs`, `TAKE j xs`, `DROP (SUC j) xs`] >>
     simp[LENGTH_TAKE, Abbr `av`, Abbr `v`] >> metis_tac[TAKE_DROP_SUC, APPEND_ASSOC, APPEND]) >>
  `?u. array_entry_navigation ctx fn st mid limit_st ops sb off d j (type_memory_bytes ce ty) s u` by
    (asm_rewrite_tac[] >> qpat_assum `LENGTH pre = j` (fn th => pure_rewrite_tac[GSYM th]) >>
     irule descending_array_navigation_split >> asm_rewrite_tac[] >> metis_tac[]) >>
  suspend "resources"
QED
Resume descending_array_owned_entry[resources]:
  qpat_x_assum `avs = _` SUBST_ALL_TAC >>
  qpat_x_assum `xs = _` SUBST_ALL_TAC >>
  qpat_x_assum `_ = type_memory_bytes ce (ArrayT ty (Dynamic maxn))` SUBST_ALL_TAC >>
  `LENGTH pre = LENGTH vpre` by decide_tac >>
  drule_all abi_decoder_dynarray_child_source >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_decoder_dynarray_child_layout >> strip_tac >>
  `entry_scratch_ready sites b cap u /\ entry_owned_region oid root extent d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) u /\ alloca_inv u /\
   abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u` by
    (irule entry_member_resource_frame >> qexists_tac `s` >> fs[Excl "enc_def", array_entry_navigation_def]) >>
  `abi_decode_source CALLDATALOAD u = abi_decode_source CALLDATALOAD s` by
    (irule abi_decoder_address_frame_source >> fs[Excl "enc_def", array_entry_navigation_def] >> goal_assum (drule_at Any)) >>
  `entry_owned_region oid root extent cell (type_memory_size tv) u` by
    (qpat_x_assum `entry_owned_region oid root extent d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) u` mp_tac >>
     simp_tac bool_ss [entry_owned_region_def] >> strip_tac >> gvs[Excl "enc_def"] >> decide_tac) >>
  qexists_tac `u` >> gvs[entry_descending_metadata_transport, Excl "enc_def"] >> decide_tac
QED
Finalise descending_array_owned_entry

Theorem descending_array_child[local]:
  !off cell total.
  off = abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j /\
  cell = d+32+j*type_memory_bytes ce ty /\
  total = type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\ j < LENGTH xs /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb+LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  d+total < dimword (:256) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var ip /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ fn_has_code st mid fn /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts /\
  entry_owned_region oid root extent d total s /\ entry_scratch_ready ambient b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) mid = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code mid last fn /\ abi_decoder_code mid last /\
  fn_inst_ids_distinct fn /\ unit_alloca_budget ctx < dimword (:256) /\
  oid NOTIN abi_decoder_ids mid.cs_next_id last.cs_next_id /\
  child_ids = window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id) /\
  child_ids SUBSET ambient /\ oid NOTIN ambient /\
  cid < mid.cs_next_id /\ oid <> cid /\ FLOOKUP s.vs_allocas cid = SOME (w2n p,32) /\
  FST ops = Var iv /\ lookup_block last.cs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = last.cs_current_insts ++ abi_decode_backedge_insts bid iv nv ip hdr /\
  abi_decode_load CALLDATALOAD (n2w sb : bytes32) s = n2w n /\
  entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0)
    ce env sf ty tv (EL j avs) (EL j xs) ctx fn oid root extent ambient b cap site limit_st ==>
  ?t. array_child_result ctx fn oid root extent ambient child_ids b cap site limit_st
      st last cell tv (EL j xs) s t /\
    entry_loop_child_end fn last.cs_current_bb last.cs_current_insts bid iv nv ip hdr
      src p (n2w sb) n j t /\
    mload (w2n p) t = n2w j /\ FLOOKUP t.vs_allocas cid = SOME (w2n p,32)
Proof
  rpt gen_tac >> strip_tac >> drule_all descending_array_owned_entry >> strip_tac >>
  qhdtm_x_assum `array_entry_navigation`
    (strip_assume_tac o PURE_REWRITE_RULE [array_entry_navigation_def]) >>
  `last.cs_current_insts = [] ==>
    !bb'. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb' ==>
      phi_prefix_length bb'.bb_instructions = 0` by
    (rpt strip_tac >> gvs[] >>
     simp[abi_decode_backedge_insts_def, phi_prefix_length_def, mk_inst_def]) >>
  qhdtm_x_assum `entry_descending_certified_child_producer`
    (mp_tac o PURE_REWRITE_RULE [entry_descending_certified_child_producer_def]) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`sb+off`, `cell`, `u`] mp_tac) >>
  asm_simp_tac bool_ss [] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  `child_ids SUBSET abi_decoder_ids mid.cs_next_id last.cs_next_id` by
    metis_tac[window_alloca_sites_subset] >>
  `cid NOTIN child_ids` by
    (fs[SUBSET_DEF, abi_decoder_ids_def] >> metis_tac[NOT_LESS, LESS_IMP_LESS_OR_EQ]) >>
  qexists_tac `t` >> irule array_child_backedge >>
  qpat_assum `array_child_result _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  gvs[Excl "enc_def"]
QED

Theorem descending_iteration_callback:
  cfg = ((ce,env,ty,tv,maxn,parent_di,avs,xs),
     (ip,src,dst,st,ops,mid,last,limit_st,next,nv),
     (ctx,fn,site,cid,oid,root,extent,d,b,reserve,prepared,p,sb,ambient),
     (hdr,body_lbl,exit,hid,bb)) /\ iteration_callback_config cfg /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) mid = ((),last) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    root_di (ListV avs) (ArrayV (DynArrayV xs)) /\
  (!j. j < LENGTH xs ==> entry_descending_certified_child_producer
    (\z. z.cs_current_insts = [] ==> !bb.
      lookup_block z.cs_current_bb fn.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0)
    ce env sf ty tv (EL j avs) (EL j xs) ctx fn oid root extent ambient b reserve site limit_st) ==>
  iteration_semantic_callback cfg
Proof
  strip_tac >> qpat_x_assum `cfg = _` SUBST_ALL_TAC >>
  qhdtm_x_assum `iteration_callback_config`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [iteration_callback_config_def]) >>
  simp_tac bool_ss [iteration_semantic_callback_def] >> rpt strip_tac >>
  qhdtm_x_assum `iteration_body`
    (strip_assume_tac o PURE_REWRITE_RULE [iteration_body_def]) >>
  drule_all iteration_frame_inputs >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var ip /\
   abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono, LESS_EQ_TRANS, DECIDE ``n <= n+4``] >>
  `fresh_vars_wrt limit_st u /\ entry_scratch_ready ambient b reserve u` by
    fs[iteration_frame_def] >>
  qpat_assum `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [entry_owned_loop_resources_def]) >>
  `eval_operand ip u = SOME p` by fs[iteration_frame_def] >>
  suspend "execute"
QED
Resume descending_iteration_callback[execute]:
  `?t. array_child_result ctx fn oid root extent ambient
      (window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id))
      b reserve site limit_st st last (d+32+j*type_memory_bytes ce ty) tv (EL j xs) u t /\
    entry_loop_child_end fn last.cs_current_bb last.cs_current_insts last.cs_next_id
      (STRING #"%" (toString st.cs_next_var)) (STRING #"%" (toString nv))
      ip hdr src p (n2w sb) (LENGTH xs) j t /\
    mload (w2n p) t = n2w j /\ FLOOKUP t.vs_allocas cid = SOME (w2n p,32)` by
    (irule (SIMP_RULE bool_ss [] descending_array_child) >>
     simp[Excl "enc_def"] >>
     qexistsl_tac [`avs`,`dst`,`env`,`maxn`,`ops`,`root_di`,`sf`] >>
     gvs[Excl "enc_def"]) >>
  qhdtm_x_assum `array_child_result`
    (strip_assume_tac o PURE_REWRITE_RULE [array_child_result_def]) >>
  `oid NOTIN window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id)` by
    metis_tac[SUBSET_DEF] >>
  `entry_owned_region oid root extent d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) t` by
    (irule entry_owned_region_preserved >>
     qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >> simp[]) >>
  qexists_tac `t` >> asm_simp_tac bool_ss [entry_owned_loop_resources_def] >>
  gvs[Excl "enc_def"] >>
  irule iteration_array_child_frame >>
  qpat_assum `abi_encoder_registered_effect _ _ _ _` (irule_at Any) >>
  simp[] >> qexistsl_tac [`type_memory_bytes ce (ArrayT ty (Dynamic maxn))`,
    `root`,`oid`,`extent`,`st.cs_next_var`] >> simp[]
QED
Finalise descending_iteration_callback

Theorem entry_descending_nonbulk_array_constructor:
  parent_di = DecDynArray (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) dyn maxn /\
  (dyn \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
  compile_abi_decode_to_buf dst src CALLDATALOAD (Lit 0w) parent_di st = ((),final) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
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
  (!j. j < LENGTH xs ==> entry_descending_certified_child_producer
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
  drule_all callback_array_compiler_config >> strip_tac >>
  rename1 `abi_decode_index_init header_st = (ip,loop_st)` >>
  suspend "initialize"
QED
Resume entry_descending_nonbulk_array_constructor[initialize]:
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
Resume entry_descending_nonbulk_array_constructor[phases]:
  `header_st.cs_next_id IN ambient` by metis_tac[SUBSET_DEF] >>
  `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    simp[type_memory_size_def] >>
  mp_tac (conditional_array_initialization |> Q.INST
    [`asz` |-> `abi_embedded_static_size ce.ce_struct_fields ty`,
     `aty` |-> `vyper_to_abi_type env ty`,
     `sz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `pnum` (qx_choose_then `prepared` strip_assume_tac)) >>
  qpat_x_assum `!prepared pnum sb d env tv avs xs ctx site oid root extent ambient b reserve. _`
    (qspecl_then [`prepared`,`pnum`] assume_tac) >>
  `32+LENGTH xs*type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (simp[type_memory_size_def] >> decide_tac) >>
  `LENGTH xs < dimword (:256)` by decide_tac >>
  qpat_x_assum `!sb d env tv avs xs ctx site oid root extent ambient b reserve. _`
    (mp_tac o SPEC_ALL) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `iteration_callback_config cfg` >>
  suspend "iterate"
QED
Resume entry_descending_nonbulk_array_constructor[iterate]:
  `iteration_semantic_callback cfg` by
    (irule descending_iteration_callback >> simp[Abbr `cfg`] >>
     goal_assum (drule_at Any) >> gvs[Excl "enc_def"] >>
     goal_assum (drule_at Any)) >>
  `pnum < dimword (:256)` by
    (qpat_x_assum `entry_owned_loop_resources _ _ _ _ _ _ _ _ _ _ prepared` mp_tac >>
     simp[entry_owned_loop_resources_def, alloca_inv_def, alloca_next_valid_def] >>
     rpt strip_tac >>
     `prepared.vs_alloca_next < dimword (:256)` by
       (drule_all alloca_frontier_inv_bound >> simp[]) >>
     first_x_assum drule >> simp[] >> decide_tac) >>
  `?hdr_bb. lookup_block (FST labels) fn.fn_blocks = SOME hdr_bb /\
    phi_prefix_length hdr_bb.bb_instructions = 0` by
    (qpat_x_assum `iteration_callback_config cfg` mp_tac >>
     simp[Abbr `cfg`, iteration_callback_config_def, abi_decode_loop_cfg_def] >>
     rpt strip_tac >> simp[abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def]) >>
  drule_at (Pat `iteration_callback_config _`)
    (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] callback_array_prepared_endpoint) >>
  simp[Abbr `cfg`] >>
  disch_then (qspec_then `loop_st` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  suspend "result"
QED
Resume entry_descending_nonbulk_array_constructor[result]:
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
Finalise entry_descending_nonbulk_array_constructor
