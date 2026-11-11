Theory ctorAbiActualArrayBody
Ancestors
  ctorAbiActualArrayInvariant ctorAbiActualArrayIteration ctorAbiActualFrame
  ctorAbiActualSites abiDecoderDynamicLoopSetup abiDecoderReentry
  abiEncoderRegisteredEffect abiDecoderTypedContract venomState valueEncoding
  compileEnv finite_map words list arithmetic pred_set
  abiDecoderArraySetupInputs abiDecoderContract abiDecoderLoop fragExec
  abiDecoderVarSequence abiDecoderDynamic abiEncoderProps instIdxIndep venomExecSemantics
  exprLoweringProps abiDecoderArrayInvariant rich_list abiDecoderArraySetupCode
  abiDecoderCounters abiDecoderAppend ctorAbiActualObservations
  abiDecoderCode abiDecoderLoopSetup abiDecoderIndexedAddress entryDecodeStructure
  emitHelper abiDecoderArrayBackedge abiDecoderExecution

Theorem ctor_actual_array_observation_address:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor s /\
  abi_decoder_address_frame body_next s t /\ next <= body_next /\
  fresh_vars_wrt limit_st t /\ t.vs_labels = s.vs_labels /\
  abi_encoder_registered_effect {} [] s t ==>
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial prefix cursor t
Proof
  strip_tac >>
  `alloca_inv t = alloca_inv s /\
   alloca_frontier_inv ctx func site t = alloca_frontier_inv ctx func site s /\
   ctor_actual_scratch func ids D N t = ctor_actual_scratch func ids D N s` by
    metis_tac[ctor_actual_address_allocations] >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] s t` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`{}`, `[]`] >> simp[]) >>
  fs[ctor_actual_array_observation_def, abi_decoder_address_frame_def, mload_def] >>
  simp[] >>
  reverse conj_tac >- metis_tac[abi_encoder_registered_effect_trans] >>
  rpt strip_tac >>
  `lookup_var x s = SOME w` by metis_tac[] >>
  `abi_decoder_operand_live body_next (Var x)` by
    (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, IN_DEF] >>
     metis_tac[LESS_EQ_TRANS]) >>
  qpat_x_assum `!op w. _` (qspec_then `Var x` mp_tac) >>
  simp[eval_operand_def]
QED

Theorem ctor_actual_array_sequence_endpoint[local]:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
  run_inst_seq (emitted_insts st st') s = OK t /\
  fn_has_code st st' func /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let u = t with vs_inst_idx := LENGTH st'.cs_current_insts in
  ~u.vs_halted /\ u.vs_current_bb = st'.cs_current_bb /\
  u.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s u
Proof
  strip_tac >>
  `frag_exec ctx st st' (\u. u = s)
    (\u. u = t with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >> metis_tac[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]
QED

Theorem ctor_actual_array_setup_sim:
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  abi_decoder_ranges DLOAD (Lit 0w) hi src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post))))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) s.vs_data_section =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w (LENGTH pre) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. eval_operand (FST ops) t = SOME (n2w (LENGTH pre)) /\
    eval_operand (FST (SND ops)) t = SOME (n2w (sb + abi_array_child_offset NONE
      (vyper_to_abi_type env ty) (pre ++ av::post) (LENGTH pre))) /\
    eval_operand (SND (SND ops)) t = SOME (n2w (d + 32 + LENGTH pre * type_memory_bytes ce ty)) /\
    abi_decoder_operand_live st'.cs_next_var (FST ops) /\
    abi_decoder_operand_live st'.cs_next_var (FST (SND ops)) /\
    abi_decoder_operand_live st'.cs_next_var (SND (SND ops)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_address_frame st.cs_next_var s t /\
    inst_extends st st' /\ t.vs_labels = s.vs_labels /\
    abi_encoder_registered_effect {} [] s t /\
    ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all ctor_actual_array_setup_labels >> strip_tac >>
  drule_all ctor_actual_array_sequence_endpoint >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qexists `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[eval_op_inst_idx, fresh_vars_wrt_def, abi_decoder_address_frame_def,
    abi_encoder_registered_effect_def]
QED

Theorem ctor_actual_array_setup_ids[local]:
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) hi di esz msz st = (ops,middle) ==>
  st.cs_next_id <= middle.cs_next_id
Proof
  simp_tac bool_ss [abi_decode_array_element_setup_def,
    abi_decode_indexed_address_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  Cases_on `dec_info_needs_offset di` >>
  gvs[] >> strip_tac >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_next_id >>
  `!src data hi sz a v z.
    compile_abi_decode_dyn_elem_ptr DLOAD (Lit 0w) src data hi sz a = (v,z) ==>
    a.cs_next_id <= z.cs_next_id` by
    (rpt strip_tac >>
     qpat_x_assum `compile_abi_decode_dyn_elem_ptr DLOAD _ _ _ _ _ a = (v,z)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     mp_tac (GEN_ALL (Q.INST [`opc` |-> `DLOAD`] abi_decoder_code_dyn_elem_ptr)) >>
     simp[abi_decoder_code_def] >> metis_tac[pairTheory.SND]) >>
  first_x_assum imp_res_tac >> gvs[comp_return_def] >> decide_tac
QED

(* Same child interface as MemberRun: labels are an execution observation. *)
val C = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
 abi_decoder_coherent ce env sf ty tv /\
 abi_decoder_metadata ce env ty tv root_di av v /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av)) initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\ sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/ !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==> phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\ unit_alloca_budget ctx < dimword (:256) /\
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
 actual.vs_labels = initial.vs_labels``;

Theorem ctor_actual_array_body_at_index:
  (^C) ty tv /\
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD (Lit 0w) hi
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
  abi_decoder_ranges DLOAD (Lit 0w) hi src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  eval_operand ip initial = SOME (n2w slot) /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\ abi_decoder_operand_live next ip /\
  next <= st.cs_next_var /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  unit_alloca_budget ctx < dimword (:256) /\
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
      [(d+32+j*type_memory_bytes ce ty,type_memory_bytes ce ty)] s t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  `TAKE j avs ++ EL j avs::DROP (SUC j) avs = avs` by
    (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `TAKE j vs ++ EL j vs::DROP (SUC j) vs = vs` by
    (mp_tac (Q.ISPEC `vs:vyperValue$value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j /\ LENGTH (TAKE j vs) = j` by simp[LENGTH_TAKE, MIN_DEF] >>
  `abi_decoder_ranges DLOAD (Lit 0w) hi src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s` by
    metis_tac[ctor_actual_array_observation_ranges] >>
  drule_all ctor_actual_array_observation_setup_inputs >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var hi /\
   abi_decoder_operand_live st.cs_next_var ip` by
    (asm_x "child" kall_tac >> metis_tac[abi_decoder_operand_live_mono]) >>
  `fresh_vars_wrt limit_st s` by fs[ctor_actual_array_observation_def] >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`pre` |-> `TAKE j (avs:abi_value list)`,
    `av` |-> `EL j (avs:abi_value list)`, `post` |-> `DROP (SUC j) (avs:abi_value list)`,
    `vpre` |-> `TAKE j (vs:vyperValue$value list)`,
    `v` |-> `EL j (vs:vyperValue$value list)`, `vpost` |-> `DROP (SUC j) (vs:vyperValue$value list)`,
    `st'` |-> `middle:compile_state`, `p` |-> `n2w slot:bytes32`]
    ctor_actual_array_setup_sim) >>
  (impl_tac >- (asm_x "child" kall_tac >> asm_simp_tac bool_ss [])) >>
  disch_then (qx_choose_then `prepared` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `ctor_actual_array_observation ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j prepared` by
    (asm_x "child" kall_tac >> metis_tac[ctor_actual_array_observation_address]) >>
  `prepared.vs_data_section = initial.vs_data_section /\
   (!w. eval_operand hi initial = SOME w ==> eval_operand hi prepared = SOME w)` by
    (asm_x "child" kall_tac >> conj_tac
     >- fs[ctor_actual_array_observation_def] >>
     metis_tac[ctor_actual_array_observation_operand]) >>
  mp_tac (Q.INST [`prepared` |-> `prepared:venom_state`,
    `initial` |-> `initial:venom_state`] ctor_actual_array_child_inputs_at_index) >>
  (impl_tac >- (asm_x "child" kall_tac >> asm_simp_tac bool_ss [])) >>
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `alloca_inv prepared /\ alloca_frontier_inv ctx func site prepared /\
   ctor_actual_scratch func ids D N prepared /\ D+N <= prepared.vs_alloca_next` by
    (asm_x "child" kall_tac >> fs[ctor_actual_array_observation_def]) >>
  `abi_decoder_operand_live middle.cs_next_var hi /\
   abi_decoder_operand_live middle.cs_next_var ip` by
    (asm_x "child" kall_tac >> metis_tac[abi_decoder_operand_live_mono]) >>
  `!x. FST (SND ops) = Var x \/ SND (SND ops) = Var x \/ hi = Var x ==>
    not_fresh_at middle x` by
    (asm_x "child" kall_tac >> rpt strip_tac >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF]) >>
  `st.cs_next_id <= middle.cs_next_id` by
    (asm_x "child" kall_tac >> drule ctor_actual_array_setup_ids >> simp[]) >>
  `frag_ids middle end_st SUBSET ids` by
    (irule SUBSET_TRANS >> qexists `frag_ids st end_st` >>
     simp[] >> simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
  `D <= d+32+j*type_memory_bytes ce ty /\
   d+32+j*type_memory_bytes ce ty+type_memory_bytes ce ty <= D+N` by
    (qpat_x_assum `D <= d` mp_tac >>
     qpat_x_assum `d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N` mp_tac >>
     qpat_x_assum `_ + type_memory_bytes ce ty <= d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  qpat_x_assum `eval_operand (FST (SND ops)) prepared = _` mp_tac >>
  pure_asm_rewrite_tac [] >> disch_tac >>
  qpat_x_assum `eval_operand (SND (SND ops)) prepared = _` mp_tac >>
  pure_asm_rewrite_tac [] >> disch_tac >>
  asm "child" (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`) o BETA_RULE) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand (FST (SND ops)) _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand (SND (SND ops)) _ = _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `ctor_actual_scratch _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
  (impl_tac >- (asm_x "child" kall_tac >> asm_simp_tac bool_ss [] >>
    first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  asm_x "child" kall_tac >>
  `next <= middle.cs_next_var` by metis_tac[LESS_EQ_TRANS] >>
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
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, IN_DEF]) >>
  `eval_operand ip prepared = SOME (n2w slot)` by
    metis_tac[ctor_actual_array_observation_operand] >>
  `eval_operand ip t = SOME (n2w slot)` by
    (irule ctor_actual_old_operand >> qexistsl [`prepared`, `middle`] >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, IN_DEF]) >>
  qexists `t` >> asm_simp_tac bool_ss [] >>
  conj_tac >- metis_tac[abi_decode_sim_trans] >>
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

Theorem ctor_actual_array_backedge_run:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j s /\
  slot_id IN ctor_actual_sites func ids /\ all_have_type tv vs /\
  32 + LENGTH vs * type_memory_size tv <= outsz /\
  venomMemDefs$regions_disjoint (slot,32) (d,outsz) /\
  next <= nv /\ nv < limit_st.cs_next_var /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  bb.bb_instructions = prefix ++ abi_decode_backedge_insts id iv
    (STRING #"%" (toString nv)) ip hdr /\
  lookup_block hdr func.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 /\
  s.vs_inst_idx = LENGTH prefix /\ ~s.vs_halted /\
  eval_operand (Var iv) s = SOME (n2w j) /\
  eval_operand ip s = SOME (n2w slot) /\ abi_decoder_operand_live next ip /\
  slot < dimword (:256) /\ j < LENGTH vs /\ LENGTH vs < dimword (:256) ==>
  ?t. ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t
Proof
  strip_tac >>
  `ip <> Var (STRING #"%" (toString nv))` by
    metis_tac[abi_decoder_live_excludes_output] >>
  drule_all abi_decode_backedge_sim >> disch_then (qspec_then `ctx` mp_tac) >>
  simp[w2n_n2w] >> disch_tac >>
  drule_all ctor_actual_array_observation_backedge >> strip_tac >>
  qexists `jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) s))` >>
  asm_simp_tac bool_ss [] >>
  simp[jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]
QED

Theorem ctor_actual_array_iteration:
  (^C) ty tv /\
  abi_decode_array_element_setup ip src dst DLOAD (Lit 0w) hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD (Lit 0w) hi
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
  abi_decoder_ranges DLOAD (Lit 0w) hi src dst 0 sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
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
    abi_decode_sim ctx func s t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `end_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  asm "child" assume_tac >>
  drule_all ctor_actual_array_body_at_index >>
  disch_then (qx_choose_then `body_result` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  asm_x "child" kall_tac >>
  `all_have_type tv vs` by metis_tac[abi_decoder_dynarray_values] >>
  `lookup_block body_result.vs_current_bb func.fn_blocks = SOME bb /\
   eval_operand (Var iv) body_result = SOME (n2w j)` by
    (asm_simp_tac bool_ss [] >> metis_tac[]) >>
  drule_all ctor_actual_array_backedge_run >>
  disch_then (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists `t` >> asm_simp_tac bool_ss [] >>
  metis_tac[abi_decode_sim_trans]
QED
