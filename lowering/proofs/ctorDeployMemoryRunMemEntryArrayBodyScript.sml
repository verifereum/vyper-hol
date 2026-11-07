Theory ctorDeployMemoryRunMemEntryArrayBody
Ancestors
  ctorDeployMemoryRunMemEntryArraySteps ctorAbiActualArrayInvariant
  abiDecoderArraySetupInputs abiDecoderCoherence abiDecoderContract abiDecodeRanges
  abiEncoder contractABI list rich_list arithmetic words
  abiDecoderArrayInvariant abiDecoderTypedContract venomInst
  ctorDeployMemoryRunMemEntryMembers ctorAbiActualArrayBody ctorAbiActualFrame
  abiEncoderRegisteredEffect ctorAbiActualObservations pred_set abiDecoderReentry compileEnv
  allocaFrontierBound abiDecoderArraySetupCode fragGasPathMem venomMemDefs fragExec abiEncoderProps abiDecoderLoop ctorAbiActualSites

Theorem ctor_checked_array_child_section_at_index:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\ j < LENGTH vs /\
  abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  prepared.vs_data_section = initial.vs_data_section /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <=
    LENGTH initial.vs_data_section ==>
  sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j +
    LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)) <= LENGTH prepared.vs_data_section
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  `TAKE j avs ++ EL j avs::DROP (SUC j) avs = avs` by
    (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `TAKE j vs ++ EL j vs::DROP (SUC j) vs = vs` by
    (mp_tac (Q.ISPEC `vs:vyperValue$value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j /\ LENGTH (TAKE j vs) = j` by simp[LENGTH_TAKE, MIN_DEF] >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
   d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256)` by
    fs[abi_decoder_ranges_def] >>
  mp_tac (Q.INST [`pre` |-> `TAKE j (avs:abi_value list)`,
    `av` |-> `EL j (avs:abi_value list)`, `post` |-> `DROP (SUC j) (avs:abi_value list)`,
    `vpre` |-> `TAKE j (vs:vyperValue$value list)`,
    `v` |-> `EL j (vs:vyperValue$value list)`, `vpost` |-> `DROP (SUC j) (vs:vyperValue$value list)`,
    `s` |-> `initial:venom_state`, `opc` |-> `DLOAD`]
    abi_decoder_dynarray_child_source) >>
  (impl_tac >- (asm_simp_tac bool_ss [abi_decode_source_def] >>
    simp[Excl "enc_def"])) >>
  asm_simp_tac bool_ss [LET_THM] >> strip_tac >> decide_tac
QED

Theorem ctor_checked_array_setup_at_index:
  abi_decode_array_element_setup ip src dst DLOAD hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\ j < LENGTH vs /\
  abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV avs))) s.vs_data_section =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV avs)) <= LENGTH s.vs_data_section /\
  eval_operand ip s = SOME (n2w slot) /\ slot < dimword (:256) /\
  slot+32 <= s.vs_alloca_next /\ mload slot s = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\ s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST ops) t = SOME (n2w j) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb + abi_array_child_offset NONE
      (vyper_to_abi_type env ty) avs j)) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d + 32 + j * type_memory_bytes ce ty)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st' /\ t.vs_labels = s.vs_labels /\
    abi_encoder_registered_effect {} [] s t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    gas_path_mem ctx func s 0 (OK t) /\ t.vs_gas_readings = s.vs_gas_readings /\
    alloca_history func t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  `TAKE j avs ++ EL j avs::DROP (SUC j) avs = avs` by
    (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `TAKE j vs ++ EL j vs::DROP (SUC j) vs = vs` by
    (mp_tac (Q.ISPEC `vs:vyperValue$value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j /\ LENGTH (TAKE j vs) = j` by simp[LENGTH_TAKE, MIN_DEF] >>
  mp_tac (Q.INST [`pre` |-> `TAKE j (avs:abi_value list)`,
    `av` |-> `EL j (avs:abi_value list)`, `post` |-> `DROP (SUC j) (avs:abi_value list)`,
    `vpre` |-> `TAKE j (vs:vyperValue$value list)`,
    `v` |-> `EL j (vs:vyperValue$value list)`, `vpost` |-> `DROP (SUC j) (vs:vyperValue$value list)`]
    ctor_checked_array_setup_labels) >>
  (impl_tac >- asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss []
QED

val C = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= LENGTH initial.vs_data_section /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\ unit_alloca_budget ctx < dimword (:256) /\
 alloca_history func initial /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\
 gas_path_mem ctx func initial 0 (OK actual) /\ actual.vs_gas_readings = initial.vs_gas_readings /\
 alloca_history func actual``;

Theorem ctor_checked_array_child_at_index:
  (^C) ty tv /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code middle end_st func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\
  ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j prepared /\ j < LENGTH vs /\
  abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= LENGTH initial.vs_data_section /\
  prepared.vs_data_section = initial.vs_data_section /\
  (hi = Lit 0w \/ !w. eval_operand hi initial = SOME w ==> eval_operand hi prepared = SOME w) /\
  eval_operand (FST ops) prepared = SOME (n2w j) /\
  eval_operand (FST (SND ops)) prepared = SOME (n2w (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j)) /\
  eval_operand (SND (SND ops)) prepared = SOME (n2w (d+32+j*type_memory_bytes ce ty)) /\
  eval_operand ip prepared = SOME (n2w slot) /\
  abi_decoder_operand_live middle.cs_next_var (FST ops) /\
  abi_decoder_operand_live middle.cs_next_var (FST (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var (SND (SND ops)) /\
  abi_decoder_operand_live middle.cs_next_var hi /\
  abi_decoder_operand_live middle.cs_next_var ip /\
  next <= middle.cs_next_var /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  unit_alloca_budget ctx < dimword (:256) /\ alloca_history func prepared /\
  D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  frag_ids middle end_st SUBSET ids /\ slot_id NOTIN frag_ids middle end_st /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?t. ctor_actual_array_observation ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (SUC j) j t /\
    val_in_memory tv (EL j vs) (d+32+j*type_memory_bytes ce ty) t.vs_memory /\
    eval_operand (FST ops) t = SOME (n2w j) /\ eval_operand ip t = SOME (n2w slot) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ abi_decode_sim ctx func prepared t /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle end_st))
      [(d+32+j*type_memory_bytes ce ty,type_memory_bytes ce ty)] prepared t /\
    gas_path_mem ctx func prepared 0 (OK t) /\ t.vs_gas_readings = prepared.vs_gas_readings /\
    alloca_history func t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all ctor_actual_array_child_inputs_at_index >>
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all ctor_checked_array_child_section_at_index >> disch_tac >>
  `alloca_inv prepared /\ alloca_frontier_inv ctx func site prepared /\
   ctor_actual_scratch func ids D N prepared /\ D+N <= prepared.vs_alloca_next /\
   fresh_vars_wrt limit_st prepared` by
    (asm_x "child" kall_tac >> fs[ctor_actual_array_observation_def]) >>
  `!x. FST (SND ops) = Var x \/ SND (SND ops) = Var x \/ hi = Var x ==>
    not_fresh_at middle x` by
    (asm_x "child" kall_tac >> rpt strip_tac >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF]) >>
  `D <= d+32+j*type_memory_bytes ce ty /\
   d+32+j*type_memory_bytes ce ty+type_memory_bytes ce ty <= D+N` by decide_tac >>
  asm "child" (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`) o BETA_RULE) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand (FST (SND ops)) _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand (SND (SND ops)) _ = _`)) >>
  disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ _`)) >>
  disch_then (qspecl_then [`ctx`, `site`, `limit_st`] mp_tac) >>
  (impl_tac >- (asm_x "child" kall_tac >> asm_simp_tac bool_ss [] >>
    first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  asm_x "child" kall_tac >>
  `venomMemDefs$regions_disjoint (slot,32)
    (d+32+j*type_memory_bytes ce ty,type_memory_bytes ce ty)` by
    (qpat_x_assum `venomMemDefs$regions_disjoint _ _` mp_tac >>
     qpat_x_assum `_ + type_memory_bytes ce ty <= d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial (SUC j) j t` by
    (irule ctor_actual_array_observation_child >>
     asm_simp_tac bool_ss [] >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     asm_simp_tac bool_ss [] >>
     qexists `middle` >> asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
  `eval_operand (FST ops) t = SOME (n2w j)` by
    (irule ctor_actual_old_operand >> qexistsl [`prepared`, `middle`] >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF]) >>
  `eval_operand ip t = SOME (n2w slot)` by
    (irule ctor_actual_old_operand >> qexistsl [`prepared`, `middle`] >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF]) >>
  qexists `t` >> asm_simp_tac bool_ss []
QED

Theorem ctor_checked_array_observation_setup_facts[local]:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s ==>
  fresh_vars_wrt limit_st s /\ s.vs_data_section = initial.vs_data_section /\
  mload slot s = n2w j /\ slot+32 <= s.vs_alloca_next
Proof
  simp_tac bool_ss [ctor_actual_array_observation_def] >> strip_tac >>
  asm_simp_tac bool_ss [] >> fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]
QED

Theorem ctor_checked_array_body_at_index:
  (^C) ty tv /\
  abi_decode_array_element_setup ip src dst DLOAD hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\
  ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j s /\ j < LENGTH vs /\
  abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= LENGTH initial.vs_data_section /\
  eval_operand ip initial = SOME (n2w slot) /\ slot < dimword (:256) /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\ abi_decoder_operand_live next ip /\
  next <= st.cs_next_var /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  unit_alloca_budget ctx < dimword (:256) /\ alloca_history func s /\
  D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  frag_ids st end_st SUBSET ids /\ slot_id NOTIN frag_ids middle end_st /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. ctor_actual_array_observation ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (SUC j) j t /\
    val_in_memory tv (EL j vs) (d+32+j*type_memory_bytes ce ty) t.vs_memory /\
    eval_operand (FST ops) t = SOME (n2w j) /\ eval_operand ip t = SOME (n2w slot) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ abi_decode_sim ctx func s t /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st end_st))
      [(d+32+j*type_memory_bytes ce ty,type_memory_bytes ce ty)] s t /\
    gas_path_mem ctx func s 0 (OK t) /\ t.vs_gas_readings = s.vs_gas_readings /\
    alloca_history func t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  drule_all ctor_checked_array_observation_setup_facts >> strip_tac >>
  `abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s` by
    (asm_x "child" kall_tac >> metis_tac[ctor_actual_array_observation_ranges]) >>
  drule_all ctor_actual_array_observation_setup_inputs >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var hi /\
   abi_decoder_operand_live st.cs_next_var ip` by
    (asm_x "child" kall_tac >> metis_tac[abi_decoder_operand_live_mono]) >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= LENGTH s.vs_data_section` by asm_simp_tac bool_ss [] >>
  `mload slot s = n2w j` by first_assum ACCEPT_TAC >>
  drule_all ctor_checked_array_setup_at_index >>
  disch_then (qspec_then `ctx` mp_tac) >>
  disch_then (qx_choose_then `prepared` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j prepared` by
    (asm_x "child" kall_tac >> metis_tac[ctor_actual_array_observation_address]) >>
  `abi_decoder_operand_live middle.cs_next_var hi /\
   abi_decoder_operand_live middle.cs_next_var ip` by
    (asm_x "child" kall_tac >> metis_tac[abi_decoder_operand_live_mono]) >>
  `prepared.vs_data_section = initial.vs_data_section` by
    (drule ctor_checked_array_observation_setup_facts >> simp[]) >>
  `!w. eval_operand hi initial = SOME w ==> eval_operand hi prepared = SOME w` by
    (asm_x "child" kall_tac >> metis_tac[ctor_actual_array_observation_operand]) >>
  `eval_operand ip prepared = SOME (n2w slot)` by
    (asm_x "child" kall_tac >> metis_tac[ctor_actual_array_observation_operand]) >>
  `next <= middle.cs_next_var` by decide_tac >>
  `st.cs_next_id <= middle.cs_next_id` by
    (drule abi_decoder_array_setup_head >> strip_tac >> decide_tac) >>
  `frag_ids middle end_st SUBSET ids` by
    (irule SUBSET_TRANS >> qexists `frag_ids st end_st` >>
     simp[] >> simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
  drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`) ctor_checked_array_child_at_index >>
  disch_then (drule_at (Pat `ctor_actual_array_observation _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand ip prepared = _`)) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> asm "child" (ACCEPT_TAC o BETA_RULE))) >>
  asm_x "child" kall_tac >>
  disch_then (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (qpat_x_assum `gas_path_mem ctx func s 0 (OK prepared)` mp_tac >>
     qpat_x_assum `gas_path_mem ctx func prepared 0 (OK t)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_path_mem_then, ADD]) >>
  `abi_decode_sim ctx func s t` by
    (qpat_x_assum `gas_path_mem ctx func s 0 (OK t)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     drule gas_path_mem_exec >>
     simp[fragExecTheory.exit_result_def, abi_decode_sim_def] >>
     metis_tac[]) >>
  qexists `t` >> asm_simp_tac bool_ss [] >>
  irule abi_encoder_registered_effect_trans >> qexists `prepared` >>
  conj_tac
  >- (irule abi_encoder_registered_effect_enlarge >>
      qexistsl [`{}`, `[]`] >> simp[]) >>
  irule abi_encoder_registered_effect_enlarge >>
  qexistsl [`ctor_actual_sites func (frag_ids middle end_st)`,
    `[(d+32+j*type_memory_bytes ce ty,type_memory_bytes ce ty)]`] >>
  asm_simp_tac bool_ss [] >>
  irule ctor_actual_sites_mono >>
  simp[frag_ids_def, SUBSET_DEF] >> decide_tac
QED

Theorem ctor_checked_array_iteration:
  (^C) ty tv /\
  abi_decode_array_element_setup ip src dst DLOAD hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\
  ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j s /\ j < LENGTH vs /\
  abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <=
    LENGTH initial.vs_data_section /\ alloca_history func s /\
  eval_operand ip initial = SOME (n2w slot) /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\ abi_decoder_operand_live next ip /\
  next <= st.cs_next_var /\ end_st.cs_next_var < limit_st.cs_next_var /\
  next <= end_st.cs_next_var /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  frag_ids st end_st SUBSET ids /\ slot_id NOTIN frag_ids middle end_st /\
  slot_id IN ctor_actual_sites func ids /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  32 + LENGTH vs * type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  slot < dimword (:256) /\ LENGTH vs < dimword (:256) /\
  FST ops = Var iv /\
  lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = end_st.cs_current_insts ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString end_st.cs_next_var)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. ctor_actual_array_observation ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t /\ gas_path_mem ctx func s 0 (OK t) /\
    t.vs_gas_readings = s.vs_gas_readings /\ alloca_history func t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `end_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  asm "child" assume_tac >>
  drule_all ctor_checked_array_body_at_index >>
  disch_then (qx_choose_then `body_result` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  asm_x "child" kall_tac >>
  `all_have_type tv vs` by metis_tac[abi_decoder_dynarray_values] >>
  `lookup_block body_result.vs_current_bb func.fn_blocks = SOME bb /\
   eval_operand (Var iv) body_result = SOME (n2w j)` by
    (asm_simp_tac bool_ss [] >> metis_tac[]) >>
  drule_all ctor_checked_array_backedge_run >>
  disch_then (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists `t` >> asm_simp_tac bool_ss [] >> conj_tac
  >- metis_tac[abi_decode_sim_trans] >>
  qpat_x_assum `gas_path_mem ctx func s 0 (OK body_result)` mp_tac >>
  qpat_x_assum `gas_path_mem ctx func body_result 0 (OK t)` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[gas_path_mem_then, ADD]
QED
