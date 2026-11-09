Theory ctorDeployLoweringEntryCompleteArrayBody
Ancestors
  loweringStateRelDefs
 ctorDeployLoweringEntryCompleteRecursiveBoundary ctorDeployLoweringEntryArrayRun
 abiDecoderArrayInvariant abiDecoderContract abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs
 abiDecoderReentry abiDecoderTypedContract abiEncoderRegisteredEffect
 compileEnv venomState venomExecSemantics valueEncoding words list rich_list arithmetic
 ctorDeployMemoryFrontier ctorAbiActualSites abiDecoderArrayBackedge
 abiDecoderLoopRegisters abiDecoderLoopSetup abiDecoderExecution
 venomMemDefs venomMemProofs ASCIInumbers finite_map pred_set
 ctorAbiActualArrayInvariant abiDecoderLoop ctorAbiActualFrame
 ctorAbiActualChildFrame abiEncoderProps ctorAbiActualObservations
 abiDecoderIndexedAddress abiDecoderCode emitHelper entryDecodeStructure
 abiDecoderArraySetupCode abiDecoderArraySetupInputs abiDecoderReentryAddress
 ctorAbiActualArrayBody ctorDeployLoweringEntryArrayFrame ctorDeployLoweringEntryArrayOps

Theorem deploy_ctor_array_setup_complete_at_index:
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
  eval_operand ip s = SOME p /\ mload (w2n p) s = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  fn_has_code st st' func /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
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
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t /\
    t.vs_gas_readings = s.vs_gas_readings /\ t.vs_code = s.vs_code /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx
Proof
  strip_tac >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  `?pre av post. avs = pre ++ av::post /\ LENGTH pre = j` by
    (qexistsl [`TAKE j avs`, `EL j avs`, `DROP (SUC j) avs`] >>
     simp[LENGTH_TAKE, MIN_DEF, TAKE_DROP_SUC]) >>
  `?vpre v vpost. vs = vpre ++ v::vpost /\ LENGTH vpre = j` by
    (qexistsl [`TAKE j vs`, `EL j vs`, `DROP (SUC j) vs`] >>
     simp[LENGTH_TAKE, MIN_DEF, TAKE_DROP_SUC]) >>
  qpat_x_assum `avs = _` SUBST_ALL_TAC >>
  qpat_x_assum `vs = _` SUBST_ALL_TAC >>
  qpat_x_assum `LENGTH pre = j` (SUBST_ALL_TAC o SYM) >>
  `LENGTH pre = LENGTH vpre` by decide_tac >>
  drule_all deploy_ctor_array_setup_complete_sim >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `t` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

val Ok = ``\k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot base prefix cursor s.
    prefix <= LENGTH vs /\ cursor <= LENGTH vs /\
    elems_in_memory (TAKE prefix vs) (d+32) tv s.vs_memory /\
    mload d s = n2w (LENGTH vs) /\
    FLOOKUP s.vs_allocas slot_id = SOME (slot,32) /\ mload slot s = n2w cursor /\
    alloca_inv s /\ alloca_frontier_inv_from k ctx func site s /\
    ctor_actual_scratch func ids D N s /\ D+N <= s.vs_alloca_next /\
    fresh_vars_wrt limit_st s /\ s.vs_data_section = base.vs_data_section /\
    s.vs_call_ctx = base.vs_call_ctx /\ s.vs_labels = base.vs_labels /\
    (!x w. abi_decoder_older_vars next x /\ lookup_var x base = SOME w ==>
      lookup_var x s = SOME w) /\
    abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] base s /\
    s.vs_gas_readings = base.vs_gas_readings /\ s.vs_code = base.vs_code``;

Theorem deploy_ctor_array_backedge_complete_run:
  (^Ok) k ctx func site ids D N d outsz next limit_st
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
  ?t. (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx
Proof
  strip_tac >>
  `ip <> Var (STRING #"%" (toString nv))` by
    metis_tac[abi_decoder_live_excludes_output] >>
  drule_all abi_decode_backedge_sim >> disch_then (qspec_then `ctx` mp_tac) >>
  simp[w2n_n2w] >> disch_tac >>
  drule_all deploy_ctor_array_observation_backedge >>
  disch_then (qspec_then `hdr` assume_tac) >>
  qexists `jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) s))` >>
  conj_tac >- (fs[] >> NO_TAC) >>
  asm_simp_tac bool_ss [] >>
  simp[jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def]
QED

(* Assemble the child decoder's input contract on a supplied setup witness. *)
Theorem deploy_ctor_array_prepared_child_inputs:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\ j < LENGTH vs /\
  abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  (^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j prepared /\
  (!w. eval_operand hi initial = SOME w ==> eval_operand hi prepared = SOME w) /\
  eval_operand child_src prepared = SOME (n2w (sb + abi_array_child_offset NONE
    (vyper_to_abi_type env ty) avs j)) /\
  eval_operand child_dst prepared = SOME (n2w (d+32+j*type_memory_bytes ce ty)) /\
  abi_decoder_operand_live middle.cs_next_var child_src /\
  abi_decoder_operand_live middle.cs_next_var child_dst /\
  abi_decoder_operand_live middle.cs_next_var hi /\
  compile_abi_decode_to_buf child_dst child_src DLOAD (Lit 0w) hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  fn_has_code middle end_st func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  frag_ids middle end_st SUBSET ids /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  all_have_type tv vs /\ type_memory_size tv = type_memory_bytes ce ty /\
  d+32+j*type_memory_bytes ce ty+type_memory_bytes ce ty <=
    d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\
  compile_abi_decode_to_buf child_dst child_src DLOAD (Lit 0w) hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (EL j avs) (EL j vs) /\
  eval_operand child_src prepared = SOME (n2w (sb + abi_array_child_offset NONE
    (vyper_to_abi_type env ty) avs j)) /\
  eval_operand child_dst prepared = SOME (n2w (d+32+j*type_memory_bytes ce ty)) /\
  sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j +
    LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)) < dimword (:256) /\
  mem_bytes_at (sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j)
    (LENGTH (enc (vyper_to_abi_type env ty) (EL j avs))) prepared.vs_data_section =
    enc (vyper_to_abi_type env ty) (EL j avs) /\
  (hi = Lit 0w \/ ?h. eval_operand hi prepared = SOME (n2w h) /\
    sb + abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j +
    LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)) <= h /\ h < dimword (:256)) /\
  (!x. child_src = Var x \/ child_dst = Var x \/ hi = Var x ==> not_fresh_at middle x) /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st prepared /\
  fn_has_code middle end_st func /\ fn_inst_ids_distinct func /\
  (middle.cs_blocks = end_st.cs_blocks \/ !bb.
    lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d+32+j*type_memory_bytes ce ty /\
  d+32+j*type_memory_bytes ce ty+type_memory_bytes ce ty <= D+N /\
  D+N <= prepared.vs_alloca_next /\
  frag_ids middle end_st SUBSET ids /\ ctor_actual_scratch func ids D N prepared /\
  ~prepared.vs_halted /\ prepared.vs_current_bb = middle.cs_current_bb /\
  prepared.vs_inst_idx = LENGTH middle.cs_current_insts
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `prepared.vs_data_section = initial.vs_data_section` by fs[] >>
  mp_tac (Q.INST [`prepared` |-> `prepared:venom_state`,
    `initial` |-> `initial:venom_state`] ctor_actual_array_child_inputs_at_index) >>
  (impl_tac >- asm_simp_tac bool_ss []) >>
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!x. child_src = Var x \/ child_dst = Var x \/ hi = Var x ==>
    not_fresh_at middle x` by
    (rpt strip_tac >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF]) >>
  `D <= d+32+j*type_memory_bytes ce ty /\
   d+32+j*type_memory_bytes ce ty+type_memory_bytes ce ty <= D+N` by
    (qpat_x_assum `D <= d` mp_tac >>
     qpat_x_assum `d+type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N` mp_tac >>
     qpat_x_assum `_ + type_memory_bytes ce ty <= d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  fs[] >> metis_tac[]
QED

(* Post-child assembly never chooses a second decoder witness. *)
Theorem deploy_ctor_array_post_child:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j prepared /\
  j < LENGTH vs /\ all_have_type tv vs /\ type_memory_size tv = msz /\
  D <= d /\ d+32+j*msz+msz <= d+outsz /\ d+outsz <= D+N /\
  child SUBSET whole /\ whole SUBSET ids /\ slot_id NOTIN child /\
  venomMemDefs$regions_disjoint (slot,32) (d+32+j*msz,msz) /\
  next <= middle.cs_next_var /\
  abi_encoder_registered_effect {} [] s prepared /\ abi_decode_sim ctx func s prepared /\
  prepared.vs_outcomes = s.vs_outcomes /\ prepared.vs_tx_ctx = s.vs_tx_ctx /\
  prepared.vs_block_ctx = s.vs_block_ctx /\
  eval_operand index prepared = SOME (n2w j) /\
  eval_operand ip prepared = SOME (n2w slot) /\
  abi_decoder_operand_live middle.cs_next_var index /\
  abi_decoder_operand_live middle.cs_next_var ip /\
  abi_encoder_registered_effect (ctor_actual_sites func child)
    [(d+32+j*msz,msz)] prepared t /\
  val_in_memory tv (EL j vs) (d+32+j*msz) t.vs_memory /\
  alloca_inv t /\ alloca_frontier_inv_from k ctx func site t /\
  ctor_actual_scratch func ids D N t /\ D+N <= t.vs_alloca_next /\
  fresh_vars_wrt limit_st t /\ t.vs_data_section = prepared.vs_data_section /\
  t.vs_call_ctx = prepared.vs_call_ctx /\ t.vs_labels = prepared.vs_labels /\
  (!x w. not_fresh_at middle x /\ lookup_var x prepared = SOME w ==> lookup_var x t = SOME w) /\
  t.vs_gas_readings = prepared.vs_gas_readings /\ t.vs_code = prepared.vs_code /\
  abi_decode_sim ctx func prepared t /\
  t.vs_outcomes = prepared.vs_outcomes /\ t.vs_tx_ctx = prepared.vs_tx_ctx /\
  t.vs_block_ctx = prepared.vs_block_ctx ==>
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j t /\
  val_in_memory tv (EL j vs) (d+32+j*msz) t.vs_memory /\
  eval_operand index t = SOME (n2w j) /\ eval_operand ip t = SOME (n2w slot) /\
  abi_decode_sim ctx func s t /\
  abi_encoder_registered_effect (ctor_actual_sites func whole) [(d+32+j*msz,msz)] s t /\
  t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `child SUBSET ids` by metis_tac[SUBSET_TRANS] >>
  `(^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j t` by
    (irule deploy_ctor_array_observation_child >>
     asm_simp_tac bool_ss [] >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     asm_simp_tac bool_ss [] >>
     qexists `middle` >> asm_simp_tac bool_ss [] >>
     qpat_assum `_ k ctx func site ids D N d outsz next limit_st tv vs slot_id slot initial j j prepared`
       (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
     asm_simp_tac bool_ss []) >>
  `eval_operand index t = SOME (n2w j) /\ eval_operand ip t = SOME (n2w slot)` by
    (conj_tac >> irule ctor_actual_old_operand >> qexistsl [`prepared`, `middle`] >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF]) >>
  asm_simp_tac bool_ss [] >>
  conj_tac >- metis_tac[abi_decode_sim_trans] >>
  irule abi_encoder_registered_effect_trans >> qexists `prepared` >> conj_tac
  >- (irule abi_encoder_registered_effect_enlarge >> qexistsl [`{}`, `[]`] >> simp[]) >>
  irule abi_encoder_registered_effect_enlarge >>
  qexistsl [`ctor_actual_sites func child`, `[(d+32+j*msz,msz)]`] >>
  asm_simp_tac bool_ss [] >> metis_tac[ctor_actual_sites_mono]
QED

Theorem deploy_ctor_array_setup_ids_complete[local]:
  abi_decode_array_element_setup ip src dst DLOAD hi di esz msz st = (ops,middle) ==>
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
     qpat_x_assum `compile_abi_decode_dyn_elem_ptr DLOAD (Lit 0w) _ _ _ _ a = (v,z)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     mp_tac (GEN_ALL (Q.INST [`opc` |-> `DLOAD`] abi_decoder_code_dyn_elem_ptr)) >>
     simp[abi_decoder_code_def] >> metis_tac[pairTheory.SND]) >>
  first_x_assum imp_res_tac >> gvs[comp_return_def] >> decide_tac
QED

val Ccomplete = ``\ty tv.
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
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\ k + unit_alloca_budget ctx < dimword (:256) /\
 D <= d /\ d + type_memory_bytes ce ty <= D+N /\ D+N <= initial.vs_alloca_next /\
 frag_ids st st' SUBSET ids /\ ctor_actual_scratch func ids D N initial /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual. val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st')) [(d,type_memory_bytes ce ty)] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 ctor_actual_scratch func ids D N actual /\ D+N <= actual.vs_alloca_next /\
 actual.vs_data_section = initial.vs_data_section /\ actual.vs_call_ctx = initial.vs_call_ctx /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==> lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\ actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\ fresh_vars_wrt limit_st actual /\
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx``;

Theorem deploy_ctor_array_body_complete_at_index:
  (^Ccomplete) ty tv /\
  abi_decode_array_element_setup ip src dst DLOAD hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD (Lit 0w) hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\
  (^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j s /\ j < LENGTH vs /\
  abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  eval_operand ip initial = SOME (n2w slot) /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\ abi_decoder_operand_live next ip /\
  next <= st.cs_next_var /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  frag_ids st end_st SUBSET ids /\ slot_id NOTIN frag_ids middle end_st /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn))) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. (^Ok) k ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (SUC j) j t /\
    val_in_memory tv (EL j vs) (d+32+j*type_memory_bytes ce ty) t.vs_memory /\
    eval_operand (FST ops) t = SOME (n2w j) /\ eval_operand ip t = SOME (n2w slot) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ abi_decode_sim ctx func s t /\
    abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st end_st))
      [(d+32+j*type_memory_bytes ce ty,type_memory_bytes ce ty)] s t /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s` by
    (drule_all deploy_ctor_array_observation_ranges >> simp[]) >>
  drule_all deploy_ctor_array_observation_setup_inputs >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var hi /\
   abi_decoder_operand_live st.cs_next_var ip` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `fresh_vars_wrt limit_st s` by (BETA_TAC >> fs[]) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all deploy_ctor_array_setup_complete_at_index >>
  disch_then (qspec_then `ctx` (qx_choose_then `prepared` (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `(^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j prepared` by
    (drule_all deploy_ctor_array_observation_address >> simp[]) >>
  `!w. eval_operand hi initial = SOME w ==> eval_operand hi prepared = SOME w` by
    (rpt strip_tac >>
     qpat_assum `_ k ctx func site ids D N d _ next limit_st tv vs slot_id slot initial j j prepared`
       (mp_then Any mp_tac deploy_ctor_array_observation_operand) >>
     disch_then irule >> simp[]) >>
  `abi_decoder_operand_live middle.cs_next_var hi /\
   abi_decoder_operand_live middle.cs_next_var ip` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `st.cs_next_id <= middle.cs_next_id` by
    (drule deploy_ctor_array_setup_ids_complete >> simp[]) >>
  `frag_ids middle end_st SUBSET frag_ids st end_st` by
    (simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
  `frag_ids middle end_st SUBSET ids` by metis_tac[SUBSET_TRANS] >>
  drule_all deploy_ctor_array_prepared_child_inputs >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm "child" (drule_all o BETA_RULE) >>
  disch_then (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  asm_x "child" kall_tac >>
  `next <= middle.cs_next_var` by metis_tac[LESS_EQ_TRANS] >>
  `venomMemDefs$regions_disjoint (slot,32)
    (d+32+j*type_memory_bytes ce ty,type_memory_bytes ce ty)` by
    (qpat_x_assum `venomMemDefs$regions_disjoint _ _` mp_tac >>
     qpat_x_assum `_ + type_memory_bytes ce ty <= d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `eval_operand ip prepared = SOME (n2w slot)` by
    (qpat_assum `_ k ctx func site ids D N d _ next limit_st tv vs slot_id slot initial j j prepared`
       (mp_then Any mp_tac deploy_ctor_array_observation_operand) >>
     disch_then irule >> simp[]) >>
  drule_all deploy_ctor_array_post_child >> strip_tac >>
  qexists `t` >> asm_simp_tac bool_ss []
QED

Theorem deploy_ctor_array_iteration_complete:
  (^Ccomplete) ty tv /\
  abi_decode_array_element_setup ip src dst DLOAD hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) DLOAD (Lit 0w) hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\ fn_inst_ids_distinct func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\
  (^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j s /\ j < LENGTH vs /\
  abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  eval_operand ip initial = SOME (n2w slot) /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi /\ abi_decoder_operand_live next ip /\
  next <= st.cs_next_var /\ end_st.cs_next_var < limit_st.cs_next_var /\
  next <= end_st.cs_next_var /\
  k + unit_alloca_budget ctx < dimword (:256) /\
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
  ?t. (^Ok) k ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t /\
    t.vs_outcomes = s.vs_outcomes /\ t.vs_tx_ctx = s.vs_tx_ctx /\
    t.vs_block_ctx = s.vs_block_ctx
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `end_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  asm "child" assume_tac >>
  drule_all deploy_ctor_array_body_complete_at_index >>
  disch_then (qx_choose_then `body_state` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  asm_x "child" kall_tac >>
  `all_have_type tv vs` by metis_tac[abi_decoder_dynarray_values] >>
  `lookup_block body_state.vs_current_bb func.fn_blocks = SOME bb /\
   eval_operand (Var iv) body_state = SOME (n2w j)` by
    (asm_simp_tac bool_ss [] >> metis_tac[]) >>
  drule_all deploy_ctor_array_backedge_complete_run >>
  disch_then (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists `t` >> asm_simp_tac bool_ss [] >>
  metis_tac[abi_decode_sim_trans]
QED
