(* Source-certified decoder endpoint across actual array element setup. *)
Theory entryReachBodySourceArrayChild
Ancestors
  entryReachBodySourceProducer entryReachBodySourceArrayEntry
  entryReachBodyCanonicalArrayChild entryReachBodyActiveCounter
  entryReachBodyOperationalPath entryReachBodyExactArrayLoop
  abiEncoderRegisteredEffect abiEncoderWindowContract abiDecoderContract
  abiDecoderReentry abiDecoderAllocation entryReachBodyOwnedRegion
  abiDecoderDynamicLoopSetup entryReachBodyScratchSet
  venomState venomInst venomExecSemantics abiDecoderExecution
  pred_set arithmetic

Theorem source_array_child_prepend[local]:
  array_child_result ctx fn oid root extent ambient ids b cap site limit_st
    mid last cell tv v u t /\
  entry_decode_path ctx fn s u /\ entry_loop_fields s u /\
  abi_decoder_address_frame st.cs_next_var s u /\ st.cs_next_var <= mid.cs_next_var ==>
  array_child_result ctx fn oid root extent ambient ids b cap site limit_st
    st last cell tv v s t
Proof
  simp_tac bool_ss [array_child_result_def] >> strip_tac >>
  `entry_decode_path ctx fn s t` by
    (irule entry_decode_path_trans >> qexists_tac `u` >> simp[]) >>
  `entry_loop_fields s t` by fs[entry_loop_fields_def] >>
  `abi_encoder_registered_effect ids [(cell,type_memory_size tv)] s u` by
    fs[abi_encoder_registered_effect_def, abi_decoder_address_frame_def,
       entry_loop_fields_def] >>
  `abi_encoder_registered_effect ids [(cell,type_memory_size tv)] s t` by
    metis_tac[abi_encoder_registered_effect_trans] >>
  asm_rewrite_tac[] >> rpt strip_tac >>
  `eval_operand op u = SOME w` by fs[abi_decoder_address_frame_def] >>
  `abi_decoder_operand_live mid.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem source_array_counter_excluded[local]:
  cid < lo ==> cid NOTIN window_alloca_sites fn (abi_decoder_ids lo hi)
Proof
  strip_tac >>
  `window_alloca_sites fn (abi_decoder_ids lo hi) SUBSET abi_decoder_ids lo hi` by
    metis_tac[window_alloca_sites_subset] >>
  fs[SUBSET_DEF, abi_decoder_ids_def] >> metis_tac[NOT_LESS, LESS_IMP_LESS_OR_EQ]
QED

Theorem entry_source_certified_array_child:
  !off cell total.
  off = abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j /\
  cell = d+32+j*type_memory_bytes ce ty /\
  total = type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\ j < LENGTH xs /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  d + total < dimword (:256) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var ip /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  st.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ fn_has_code st mid fn /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ entry_owned_region oid root extent d total s /\
  entry_scratch_ready ambient b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty) mid = ((),last) /\
  last.cs_next_var <= limit_st.cs_next_var /\ fn_has_code mid last fn /\
  abi_decoder_code mid last /\ fn_inst_ids_distinct fn /\
  unit_alloca_budget ctx < dimword (:256) /\
  oid NOTIN abi_decoder_ids mid.cs_next_id last.cs_next_id /\
  child_ids = window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id) /\
  child_ids SUBSET ambient /\ oid NOTIN ambient /\
  cid < mid.cs_next_id /\ oid <> cid /\ FLOOKUP s.vs_allocas cid = SOME (w2n p,32) /\
  FST ops = Var iv /\ lookup_block last.cs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = last.cs_current_insts ++ abi_decode_backedge_insts bid iv nv ip hdr /\
  abi_decode_load CALLDATALOAD (n2w sb : bytes32) s = n2w n /\
  entry_source_certified_child_producer cert ce env sf ty tv (EL j avs) (EL j xs) ctx fn oid root extent
    ambient b cap site limit_st /\ cert last ==>
  ?t. array_child_result ctx fn oid root extent ambient child_ids b cap site limit_st
      st last cell tv (EL j xs) s t /\
    entry_loop_child_end fn last.cs_current_bb last.cs_current_insts bid iv nv ip hdr
      src p (n2w sb) n j t /\
    mload (w2n p) t = n2w j /\ FLOOKUP t.vs_allocas cid = SOME (w2n p,32)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all entry_source_array_owned_entry >> strip_tac >>
  qhdtm_x_assum `entry_source_certified_child_producer`
    (mp_tac o PURE_REWRITE_RULE [entry_source_certified_child_producer_def]) >>
  disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`sb+off`, `cell`, `u`] mp_tac) >>
  asm_simp_tac bool_ss [] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  `array_child_result ctx fn oid root extent ambient child_ids b cap site limit_st
    st last cell tv (EL j xs) s t` by
    (drule_all source_array_child_prepend >> asm_rewrite_tac[]) >>
  qexists_tac `t` >> asm_rewrite_tac[] >> suspend "counter"
QED
Resume entry_source_certified_array_child[counter]:
  qhdtm_x_assum `abi_decode_array_element_setup` kall_tac >>
  qhdtm_x_assum `compile_abi_decode_to_buf` kall_tac >>
  rpt (qhdtm_x_assum `abi_decoder_coherent` kall_tac) >>
  rpt (qhdtm_x_assum `entry_source_metadata` kall_tac) >>
  rpt (qhdtm_x_assum `mem_bytes_at` kall_tac) >>
  qpat_x_assum `sb + LENGTH _ < _` kall_tac >>
  qpat_x_assum `sb + off + LENGTH _ < _` kall_tac >>
  qpat_x_assum `cell = _` SUBST_ALL_TAC >>
  qpat_x_assum `child_ids = _` SUBST_ALL_TAC >>
  qpat_x_assum `array_child_result _ _ _ _ _ _ _ _ _ _ _ mid _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [array_child_result_def]) >>
  `eval_operand ip u = SOME p /\ eval_operand src u = SOME (n2w sb)` by
    fs[abi_decoder_address_frame_def] >>
  `abi_decoder_operand_live mid.cs_next_var ip /\ abi_decoder_operand_live mid.cs_next_var src` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `eval_operand (Var iv) t = SOME (n2w j) /\ eval_operand ip t = SOME p /\
    eval_operand src t = SOME (n2w sb)` by metis_tac[] >>
  `mload (w2n p) u = n2w j` by fs[mload_def] >>
  `abi_decode_load CALLDATALOAD (n2w sb : bytes32) u = n2w n` by
    fs[entry_loop_fields_def, abi_decode_load_def, abi_decode_source_def] >>
  `FLOOKUP u.vs_allocas cid = SOME (w2n p,32)` by simp[] >>
  `cid <> oid /\ eval_operand (Var iv) u = SOME (n2w j) /\
    abi_decoder_operand_live mid.cs_next_var (Var iv)` by metis_tac[] >>
  `cid NOTIN window_alloca_sites fn (abi_decoder_ids mid.cs_next_id last.cs_next_id)` by
    (irule source_array_counter_excluded >> simp[] >> goal_assum (drule_at Any)) >>
  drule_all entry_active_counter_child_end >> simp[]
QED
Finalise entry_source_certified_array_child
