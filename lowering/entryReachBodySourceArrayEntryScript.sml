Theory entryReachBodySourceArrayEntry
Ancestors
  entryReachBodySourceArrayInputs entryReachBodyCanonicalArrayEntry
  entryReachBodyMemberSetup entryReachBodyOwnedRegion entryReachBodySourceMemberEntry
  abiDecoderCoherence abiDecoderOffset abiDecoderDynamic abiDecoderContract
  abiDecoderReentry abiDecoderArraySlice abiDecoderTypedContract abiDecoderArraySetupInputs
  abiEncoder exprLoweringProps compileEnv vyperTyping vyperValue vyperABI
  venomState venomInst words list rich_list arithmetic

Theorem source_array_child_offset_kind[local]:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\ j < LENGTH xs ==>
  dec_info_needs_offset (type_to_abi_dec_info sf ce ty) = is_dynamic (vyper_to_abi_type env ty)
Proof
  strip_tac >> drule_all entry_source_dynamic_array_child_metadata >> strip_tac >>
  `type_to_abi_dec_info sf ce ty <> DecComplex T []` by
    (strip_tac >> gvs[abi_decoder_empty_dynamic_translation] >>
     gvs[entry_source_metadata_def, value_has_type_def, Once evaluate_type_def,
         AllCaseEqs(), type_slot_size_def, Excl "enc_def"] >>
     gvs[Once evaluate_type_def, AllCaseEqs(), type_slot_size_def, Excl "enc_def"]) >>
  metis_tac[abi_decoder_nonempty_offset, abi_decoder_coherent_dynamic]
QED

Theorem source_array_navigation[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\ j < LENGTH xs /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st mid fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. array_entry_navigation ctx fn st mid limit_st ops sb
    (abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j)
    d j (type_memory_bytes ce ty) s u
Proof
  strip_tac >> drule_all entry_source_dynamic_array_child_metadata >> strip_tac >>
  drule_all source_array_child_offset_kind >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  drule_all entry_layout_dynamic_array_offset_inputs >> strip_tac >>
  Cases_on `is_dynamic (vyper_to_abi_type env ty)`
  >- (`abi_decode_load CALLDATALOAD
        (n2w (sb+(j*abi_embedded_static_size ce.ce_struct_fields ty+32)) : bytes32) s =
        n2w (abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j - 32)` by
        (asm_simp_tac bool_ss [] >> metis_tac[ADD_ASSOC, ADD_COMM]) >>
      `32 <= abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j` by
        simp[abi_array_child_offset_def] >>
      `dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` by metis_tac[] >>
      drule_all array_entry_dynamic_endpoint >>
      disch_then (qspec_then `ctx` strip_assume_tac) >> qexists `u` >>
      `sb+32+(abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j-32) =
       sb+abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j` by decide_tac >>
      asm_simp_tac bool_ss [array_entry_navigation_def]) >>
  `~dec_info_needs_offset (type_to_abi_dec_info sf ce ty)` by metis_tac[] >>
  drule_all array_entry_static_endpoint >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> qexists `u` >>
  asm_simp_tac bool_ss [array_entry_navigation_def, ADD_ASSOC]
QED

Theorem entry_source_array_owned_entry:
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
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st mid fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\ entry_owned_region oid root extent d total s /\
  entry_scratch_ready sites b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s ==>
  ?u. entry_decode_path ctx fn s u /\ entry_loop_fields s u /\
    abi_decoder_address_frame st.cs_next_var s u /\ fresh_vars_wrt limit_st u /\
    eval_operand (FST ops) u = SOME (n2w j) /\
    eval_operand (FST (SND ops)) u = SOME (n2w (sb+off)) /\
    eval_operand (SND (SND ops)) u = SOME (n2w cell) /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live mid.cs_next_var (SND (SND ops)) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts /\
    abi_decoder_coherent ce env sf ty tv /\
    entry_source_metadata ce env sf ty tv (type_to_abi_dec_info sf ce ty) (EL j avs) (EL j xs) /\
    mem_bytes_at (sb+off) (LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)))
      (abi_decode_source CALLDATALOAD u) = enc (vyper_to_abi_type env ty) (EL j avs) /\
    sb+off+LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)) < dimword (:256) /\
    cell+type_memory_size tv < dimword (:256) /\
    entry_owned_region oid root extent cell (type_memory_size tv) u /\
    entry_scratch_ready sites b cap u /\ alloca_inv u /\
    abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u
Proof
  map_every qx_gen_tac [`off`, `cell`, `outsz`] >> strip_tac >>
  drule_all source_array_navigation >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256)` by metis_tac[] >>
  drule_all (PURE_REWRITE_RULE [vyper_to_abi_type_def, LET_THM]
    entry_source_dynamic_array_child_window) >> simp_tac bool_ss [] >> strip_tac >>
  qpat_x_assum `abi_decode_array_element_setup _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `entry_source_metadata _ _ _ (ArrayT _ _) _ _ _ _` kall_tac >>
  qpat_x_assum `mem_bytes_at sb _ _ = _` kall_tac >>
  qpat_x_assum `sb + LENGTH _ < _` kall_tac >>
  `entry_scratch_ready sites b cap u /\
   entry_owned_region oid root extent d outsz u /\ alloca_inv u /\
   abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u` by
    (irule entry_member_resource_frame >> qexists `s` >> fs[array_entry_navigation_def, Excl "enc_def"]) >>
  `abi_decode_source CALLDATALOAD u = abi_decode_source CALLDATALOAD s` by
    (irule abi_decoder_address_frame_source >> fs[array_entry_navigation_def, Excl "enc_def"] >>
     goal_assum (drule_at Any)) >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    fs[entry_source_metadata_def, Excl "enc_def"] >>
  `cell+type_memory_size tv < dimword (:256)` by decide_tac >>
  `entry_owned_region oid root extent cell (type_memory_size tv) u` by
    (qpat_x_assum `entry_owned_region oid root extent d outsz u` mp_tac >>
     simp_tac bool_ss [entry_owned_region_def] >> strip_tac >>
     asm_rewrite_tac[] >> decide_tac) >>
  qexists `u` >> fs[array_entry_navigation_def, Excl "enc_def"]
QED
