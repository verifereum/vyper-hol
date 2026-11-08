(* Actual array-element navigation, with canonical bounds independent of scratch. *)
Theory entryReachBodyCanonicalArrayEntry
Ancestors
  valueEncodingDefs loweringStateRelDefs entryReachBodyMemberSetup entryReachBodySequenceObservations entryReachBodyOwnedRegion
  entryReachBodyExactArrayLoop entryReachBodyOperationalPath entrySinkExtraction
  abiDecoderArraySetupInputs abiDecoderStaticLoopSetup abiDecoderDynamicLoopSetup
  abiDecoderContract abiDecoderReentry abiDecoderDynamic abiDecoderIndexedAddress abiDecoderLoopSetup
  abiDecoderOffset abiDecoderCoherence abiDecoderArraySlice abiDecoderArrayInvariant
  abiEncoder emitHelper emitHelperProps exprLoweringProps compileEnv
  venomState venomInst words list rich_list arithmetic

Theorem array_entry_observation_code[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di az mz st = (ops,mid) /\
  mid.cs_next_var <= limit_st.cs_next_var ==>
  mid.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. MEM i.inst_opcode
    [MLOAD; ADD; MUL; CALLDATALOAD; GT; ISZERO; ASSERT; CALLDATACOPY] /\
    EVERY (\x. ?k. x = STRING #"%" (toString k) /\ k < limit_st.cs_next_var)
      i.inst_outputs) (emitted_insts st mid) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st mid)
Proof
  Cases_on `dec_info_needs_offset di` >>
  simp[abi_decode_array_element_setup_def, abi_decode_indexed_address_def,
       compile_abi_decode_dyn_elem_ptr_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]
QED

Theorem array_entry_sequence_path[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di az mz st = (ops,mid) /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  run_inst_seq (emitted_insts st mid) s = OK t /\ inst_extends st mid /\
  fn_has_code st mid fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  entry_decode_path ctx fn s (t with vs_inst_idx := LENGTH mid.cs_current_insts) /\
  entry_loop_fields s (t with vs_inst_idx := LENGTH mid.cs_current_insts) /\
  ~t.vs_halted /\ t.vs_current_bb = mid.cs_current_bb
Proof
  strip_tac >> drule_all array_entry_observation_code >> strip_tac >>
  drule_all entry_sequence_observations >> strip_tac >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `entry_decode_path ctx fn s (t with vs_inst_idx := LENGTH mid.cs_current_insts)` by
    (irule entry_decode_emitted_path >> simp[] >> qexists_tac `st` >>
     fs[inst_extends_def, IS_PREFIX_APPEND]) >>
  gvs[entry_loop_fields_def]
QED

Theorem array_entry_static_endpoint:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di az mz st = (ops,mid) /\
  ~dec_info_needs_offset di /\ eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st mid fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. entry_decode_path ctx fn s u /\ entry_loop_fields s u /\
    abi_decoder_address_frame st.cs_next_var s u /\ fresh_vars_wrt limit_st u /\
    eval_operand (FST ops) u = SOME (n2w j) /\
    eval_operand (FST (SND ops)) u = SOME (n2w (sb+32+j*az)) /\
    eval_operand (SND (SND ops)) u = SOME (n2w (d+32+j*mz)) /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live mid.cs_next_var (SND (SND ops)) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts
Proof
  strip_tac >> drule_all abi_decode_static_element_setup_reentry >> strip_tac >>
  drule_all array_entry_sequence_path >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_operand_def]
QED

Theorem array_entry_dynamic_endpoint:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w) di az mz st = (ops,mid) /\
  dec_info_needs_offset di /\ eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load CALLDATALOAD (n2w (sb+(j*az+32)) : bytes32) s = n2w child_off /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st mid fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. entry_decode_path ctx fn s u /\ entry_loop_fields s u /\
    abi_decoder_address_frame st.cs_next_var s u /\ fresh_vars_wrt limit_st u /\
    eval_operand (FST ops) u = SOME (n2w j) /\
    eval_operand (FST (SND ops)) u = SOME (n2w (sb+32+child_off)) /\
    eval_operand (SND (SND ops)) u = SOME (n2w (d+32+j*mz)) /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live mid.cs_next_var (SND (SND ops)) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts
Proof
  strip_tac >>
  `abi_decode_load CALLDATALOAD (n2w (sb+32+j*az) : bytes32) s = n2w child_off` by
    (`sb+32+j*az = sb+(j*az+32)` by decide_tac >> asm_rewrite_tac[]) >>
  `abi_decode_source_opcode CALLDATALOAD /\ abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decode_source_opcode_def, abi_decoder_operand_live_def] >>
  drule abi_decode_dynamic_element_setup_reentry >> asm_simp_tac bool_ss [] >>
  disch_then drule_all >> strip_tac >>
  drule_all array_entry_sequence_path >> strip_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  gvs[abi_decoder_address_frame_def, fresh_vars_wrt_def, eval_operand_def]
QED

Definition array_entry_navigation_def:
  array_entry_navigation ctx fn st mid limit_st ops sb off d j mz s u <=>
    entry_decode_path ctx fn s u /\ entry_loop_fields s u /\
    abi_decoder_address_frame st.cs_next_var s u /\ fresh_vars_wrt limit_st u /\
    eval_operand (FST ops) u = SOME (n2w j) /\
    eval_operand (FST (SND ops)) u = SOME (n2w (sb+off)) /\
    eval_operand (SND (SND ops)) u = SOME (n2w (d+32+j*mz)) /\
    abi_decoder_operand_live mid.cs_next_var (FST ops) /\
    abi_decoder_operand_live mid.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live mid.cs_next_var (SND (SND ops)) /\
    u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
    u.vs_alloca_next = s.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = mid.cs_current_bb /\ u.vs_inst_idx = LENGTH mid.cs_current_insts
End

Theorem array_entry_canonical_split[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
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
  >- (`abi_decode_load CALLDATALOAD
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
      pure_rewrite_tac[abi_array_child_offset_append] >> gvs[Excl "enc_def"]) >>
  drule array_entry_static_endpoint >> asm_simp_tac bool_ss [] >>
  disch_then drule_all >> disch_then (qspec_then `ctx` strip_assume_tac) >> qexists_tac `u` >>
  pure_rewrite_tac[array_entry_navigation_def] >>
      qpat_assum `LENGTH pre = LENGTH vpre` (fn th => pure_rewrite_tac[GSYM th]) >>
      pure_rewrite_tac[abi_array_child_offset_append] >> gvs[Excl "enc_def"]
QED

Theorem array_entry_owned_split[local]:
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    (abi_decode_source CALLDATALOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w (LENGTH pre) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  mid.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st mid fn /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  entry_owned_region oid root extent d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) s /\
  entry_scratch_ready sites b cap s /\ alloca_inv s /\
  abi_alloca_history (fn_insts fn) s /\ alloca_frontier_inv ctx fn site s ==>
  ?u. array_entry_navigation ctx fn st mid limit_st ops sb
      (abi_array_child_offset NONE (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))
      d (LENGTH pre) (type_memory_bytes ce ty) s u /\
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
    mem_bytes_at (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))
      (LENGTH (enc (vyper_to_abi_type env ty) av)) (abi_decode_source CALLDATALOAD u) = enc (vyper_to_abi_type env ty) av /\
    sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre) +
      LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
    d+32+LENGTH pre * type_memory_bytes ce ty + type_memory_size tv < dimword (:256) /\
    entry_owned_region oid root extent (d+32+LENGTH pre * type_memory_bytes ce ty) (type_memory_size tv) u /\
    entry_scratch_ready sites b cap u /\ alloca_inv u /\
    abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u
Proof
  strip_tac >> drule_all array_entry_canonical_split >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_decoder_dynarray_child_source >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_decoder_dynarray_child_layout >> strip_tac >>
  `entry_scratch_ready sites b cap u /\
   entry_owned_region oid root extent d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) u /\ alloca_inv u /\
   abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u` by
    (irule entry_member_resource_frame >> qexists_tac `s` >> fs[Excl "enc_def", array_entry_navigation_def]) >>
  `abi_decode_source CALLDATALOAD u = abi_decode_source CALLDATALOAD s` by
    (irule abi_decoder_address_frame_source >> fs[Excl "enc_def", array_entry_navigation_def] >> goal_assum (drule_at Any)) >>
  `entry_owned_region oid root extent (d+32+LENGTH pre * type_memory_bytes ce ty) (type_memory_size tv) u` by
    (qpat_x_assum `entry_owned_region oid root extent d _ u` mp_tac >>
     simp_tac bool_ss [entry_owned_region_def] >> strip_tac >> gvs[Excl "enc_def"] >> decide_tac) >>
  qexists_tac `u` >> gvs[Excl "enc_def"] >> decide_tac
QED

Theorem entry_canonical_array_owned_entry:
  !off cell total.
  off = abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j /\
  cell = d+32+j*type_memory_bytes ce ty /\
  total = type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  abi_decode_array_element_setup ip src dst CALLDATALOAD (Lit 0w)
    (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,mid) /\
  abi_decoder_coherent ce env ce.ce_struct_fields (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
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
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) (EL j avs) (EL j xs) /\
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
  `?u. array_entry_navigation ctx fn st mid limit_st ops sb off d j (type_memory_bytes ce ty) s u /\
    abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
    abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
    mem_bytes_at (sb+off) (LENGTH (enc (vyper_to_abi_type env ty) av))
      (abi_decode_source CALLDATALOAD u) = enc (vyper_to_abi_type env ty) av /\
    sb+off+LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
    cell+type_memory_size tv < dimword (:256) /\
    entry_owned_region oid root extent cell (type_memory_size tv) u /\
    entry_scratch_ready sites b cap u /\ alloca_inv u /\
    abi_alloca_history (fn_insts fn) u /\ alloca_frontier_inv ctx fn site u` by
    (asm_rewrite_tac[] >>
     qpat_assum `LENGTH pre = j` (fn th => pure_rewrite_tac[GSYM th]) >>
     irule array_entry_owned_split >> asm_rewrite_tac[] >> metis_tac[]) >>
  qexists_tac `u` >> gvs[array_entry_navigation_def, Excl "enc_def"]
QED
