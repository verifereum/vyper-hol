(* One-element operational boundaries for the shifted constructor decoder. *)
Theory ctorDeployLoweringEntryArrayRun
Ancestors
  loweringStateRelDefs valueEncodingDefs
  ctorDeployLoweringEntryArrayOps ctorDeployLoweringEntryRegistration
  ctorAbiActualArrayBody ctorAbiActualArrayIteration ctorAbiActualArrayInvariant
  ctorAbiActualFrame ctorAbiActualWorld ctorAbiActualNarrow
  abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs abiDecoderContract
  abiDecoderReentry abiDecoderVarSequence abiDecoderArraySetupCode
  abiDecoderLoop fragExec instIdxIndep compileEnv venomExecSemantics venomState
  ctorDeployLoweringEntryArrayFrame ctorDeployMemoryFrontier ctorAbiActualChildFrame
  ctorAbiActualMemory ctorAbiActualSites abiDecoderArrayPrefix valueEncodingTyping
  abiDecoderArrayInvariant abiEncoderRegisteredEffect valueEncoding words list rich_list arithmetic
  finite_map pred_set venomMemDefs venomMemProofs vyperTyping abiDecoderLoopRegisters
  abiDecoderExecution abiDecoderArrayBackedge abiDecoderReentryAddress
  valueEncodingProps abiEncoderPrimitiveEffect abiEncoderProps abiDecoderCode
  abiDecoderIndexedAddress entryDecodeStructure emitHelper abiDecoderLoopSetup
  ctorAbiActualObservations abiDecoderRecursiveLoopContext abiCanonicalHeadSize
  ctorAbiActualArrayFinite abiDecoderTypedContract ctorAbiActualArrayRun
  ctorAbiActualArrayLayout ctorAbiActualArrayContext ctorAbiActualArrayEntry
  abiDecoderCorrectPrimitiveArray exprLowering ctorDeployLoweringEntryAllocation
  abiDecoderIndexInit ASCIInumbers abiDecoderArrayLoopInit abiDecoderRecursiveLoopEntry
  abiDecoderRecursiveLoopLayout

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

Theorem deploy_ctor_array_setup_sim:
  abi_decode_array_element_setup ip src dst DLOAD hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,st') /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV (pre ++ av::post)) (ArrayV (DynArrayV (vpre ++ v::vpost))) /\
  LENGTH pre = LENGTH vpre /\
  abi_decoder_ranges DLOAD hi src dst sb
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
    t.vs_inst_idx = LENGTH st'.cs_current_insts /\ abi_decode_sim ctx func s t /\
    t.vs_gas_readings = s.vs_gas_readings /\ t.vs_code = s.vs_code
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule_all ctor_actual_array_setup_labels >> strip_tac >>
  drule ctor_actual_array_setup_opcodes >> strip_tac >>
  drule_all deploy_ctor_decoder_sequence_observations >> strip_tac >>
  `frag_exec ctx st st' (\u. u = s)
    (\u. u = t with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >> metis_tac[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[] >> strip_tac >>
  qexists `t with vs_inst_idx := LENGTH st'.cs_current_insts` >>
  gvs[eval_op_inst_idx, fresh_vars_wrt_def, abi_decoder_address_frame_def,
    abi_encoder_registered_effect_def]
QED

Theorem deploy_ctor_array_setup_at_index:
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
    t.vs_gas_readings = s.vs_gas_readings /\ t.vs_code = s.vs_code
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
  drule_all deploy_ctor_array_setup_sim >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `t` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem deploy_ctor_array_observation_child:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j prepared /\
  j < LENGTH vs /\ all_have_type tv vs /\ D <= d /\
  d+32+j*type_memory_size tv+type_memory_size tv <= d+outsz /\
  d+outsz <= D+N /\ child SUBSET ids /\ slot_id NOTIN child /\
  venomMemDefs$regions_disjoint (slot,32) (d+32+j*type_memory_size tv,type_memory_size tv) /\
  next <= middle.cs_next_var /\
  abi_encoder_registered_effect (ctor_actual_sites func child)
    [(d+32+j*type_memory_size tv,type_memory_size tv)] prepared t /\
  val_in_memory tv (EL j vs) (d+32+j*type_memory_size tv) t.vs_memory /\
  alloca_inv t /\ alloca_frontier_inv_from k ctx func site t /\
  ctor_actual_scratch func ids D N t /\ D+N <= t.vs_alloca_next /\
  fresh_vars_wrt limit_st t /\ t.vs_data_section = prepared.vs_data_section /\
  t.vs_call_ctx = prepared.vs_call_ctx /\ t.vs_labels = prepared.vs_labels /\
  (!x w. not_fresh_at middle x /\ lookup_var x prepared = SOME w ==> lookup_var x t = SOME w) /\
  t.vs_gas_readings = prepared.vs_gas_readings /\ t.vs_code = prepared.vs_code ==>
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j t
Proof
  BETA_TAC >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `LENGTH (TAKE j vs) = j` by simp[LENGTH_TAKE, MIN_DEF] >>
  `D <= d+32 /\ d+32+j*type_memory_size tv <= D+N` by
    (qpat_x_assum `D <= d` mp_tac >>
     qpat_x_assum `d+outsz <= D+N` mp_tac >>
     qpat_x_assum `_ + type_memory_size tv <= d+outsz` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `all_have_type tv (TAKE j vs)` by
    (fs[all_have_type_EVERY] >> simp[EVERY_TAKE]) >>
  `elems_in_memory (TAKE j vs ++ [EL j vs]) (d+32) tv t.vs_memory` by
    (irule ctor_actual_child_append_element >> asm_simp_tac bool_ss [] >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     qexistsl [`D`, `N`, `ids`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `mload slot t = mload slot prepared` by
    (metis_tac[ctor_actual_child_preserves_slot]) >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 prepared.vs_memory` by
    (irule ctor_actual_registered_window >>
     qexistsl [`ctor_actual_sites func child`,
       `[(d+32+j*type_memory_size tv,type_memory_size tv)]`] >>
     asm_simp_tac bool_ss [] >> conj_tac
     >- (rpt strip_tac >> irule (cj 2 ctor_actual_sites_scratch_contained) >>
         goal_assum (drule_at (Pat `FLOOKUP _ _ = _`)) >>
         qexistsl [`child`, `D`, `func`, `ids`, `N`] >>
         asm_simp_tac bool_ss [] >>
         qpat_x_assum `d+32+j*type_memory_size tv <= D+N` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
     simp[venomMemDefsTheory.regions_disjoint_def] >> rpt strip_tac >> decide_tac) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] prepared t` by
    (irule ctor_actual_child_narrow_effect >>
     goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  asm_simp_tac bool_ss [TAKE_SUC, TAKE1_DROP] >>
  conj_tac >- simp[] >>
  conj_tac >- fs[mload_def, mem_bytes_at_def] >>
  conj_tac >- fs[abi_encoder_registered_effect_def] >>
  reverse conj_tac >- metis_tac[abi_encoder_registered_effect_trans] >>
  rpt strip_tac >>
  `lookup_var x prepared = SOME w` by metis_tac[] >>
  `not_fresh_at middle x` by
    (fs[abi_decoder_older_vars_def, not_fresh_at_def] >> decide_tac) >>
  metis_tac[]
QED

Theorem deploy_ctor_array_observation_backedge:
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) j s /\
  slot_id IN ctor_actual_sites func ids /\ all_have_type tv vs /\
  32 + LENGTH vs * type_memory_size tv <= outsz /\
  venomMemDefs$regions_disjoint (slot,32) (d,outsz) /\
  next <= nv /\ nv < limit_st.cs_next_var ==>
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial (SUC j) (SUC j)
    (jump_to hdr (mstore slot (n2w (SUC j))
      (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) s)))
Proof
  BETA_TAC >> strip_tac >>
  qabbrev_tac `t = jump_to hdr (mstore slot (n2w (SUC j))
    (update_var (STRING #"%" (toString nv)) (n2w (SUC j)) s))` >>
  `t.vs_vars = s.vs_vars |+ (STRING #"%" (toString nv),n2w (SUC j)) /\
   t.vs_labels = s.vs_labels` by
    simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `abi_decode_frame slot 32 s t` by
    (simp[abi_decode_frame_def, Abbr `t`, jump_to_def, update_var_def] >>
     rpt strip_tac >> irule EQ_TRANS >>
     irule_at Any mstore_mem_bytes_at_disjoint >> simp[]) >>
  `all_have_type tv (TAKE (SUC j) vs)` by
    (fs[all_have_type_EVERY] >> irule EVERY_TAKE >> first_assum ACCEPT_TAC) >>
  `SUC j * type_memory_size tv <= LENGTH vs * type_memory_size tv` by
    simp[LE_MULT_RCANCEL] >>
  `elems_in_memory (TAKE (SUC j) vs) (d+32) tv t.vs_memory` by
    (irule abi_decode_frame_preserves_elements >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`s`, `slot`, `32`] >>
     full_simp_tac bool_ss [venomMemDefsTheory.regions_disjoint_def] >>
     asm_simp_tac bool_ss [LENGTH_TAKE] >> decide_tac) >>
  `mem_bytes_at d 32 t.vs_memory = mem_bytes_at d 32 s.vs_memory` by
    (qpat_x_assum `abi_decode_frame slot 32 s t` mp_tac >>
     simp_tac bool_ss [abi_decode_frame_def] >> strip_tac >>
     first_x_assum irule >>
     fs[venomMemDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mload d t = mload d s` by
    (qpat_x_assum `mem_bytes_at d 32 _ = _` mp_tac >>
     simp_tac bool_ss [mem_bytes_at_def, mload_def, LET_THM] >>
     disch_then SUBST1_TAC >> REFL_TAC) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] s t` by
    (`abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] s
       (mstore slot (n2w (SUC j)) s)` by
       (irule abi_encoder_registered_slot_store >> qexists `slot_id` >> simp[]) >>
     pop_assum mp_tac >>
     simp[Abbr `t`, jump_to_def, abi_encoder_registered_effect_def,
       update_var_def, mstore_def, write_memory_with_expansion_def]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_data_section = s.vs_data_section /\ t.vs_call_ctx = s.vs_call_ctx /\
   t.vs_gas_readings = s.vs_gas_readings /\ t.vs_code = s.vs_code` by
    simp[Abbr `t`, jump_to_def, mstore_def, update_var_def, write_memory_with_expansion_def] >>
  `alloca_inv t = alloca_inv s /\
   alloca_frontier_inv_from k ctx func site t = alloca_frontier_inv_from k ctx func site s /\
   ctor_actual_scratch func ids D N t = ctor_actual_scratch func ids D N s` by
    metis_tac[deploy_ctor_array_allocation_state] >>
  `mload slot t = n2w (SUC j)` by
    (simp[Abbr `t`, abi_decode_mload_jump,
       venomMemProofsTheory.mload_mstore_same_proof]) >>
  asm_simp_tac bool_ss [] >> conj_tac
  >- (rpt strip_tac >>
      `lookup_var x s = SOME w` by metis_tac[] >>
      `abi_decoder_operand_live nv (Var x)` by
        (fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, IN_DEF] >>
         metis_tac[LESS_EQ_TRANS]) >>
      qpat_x_assum `!op. _` (qspec_then `Var x` mp_tac) >>
      simp[eval_operand_def]) >>
  irule abi_encoder_registered_effect_trans >> qexists `s` >>
  asm_simp_tac bool_ss []
QED

Theorem deploy_ctor_array_backedge_run:
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
    abi_decode_sim ctx func s t
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

Theorem deploy_ctor_array_setup_ids[local]:
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
    compile_abi_decode_dyn_elem_ptr DLOAD src data hi sz a = (v,z) ==>
    a.cs_next_id <= z.cs_next_id` by
    (rpt strip_tac >>
     qpat_x_assum `compile_abi_decode_dyn_elem_ptr DLOAD _ _ _ _ a = (v,z)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     mp_tac (GEN_ALL (Q.INST [`opc` |-> `DLOAD`] abi_decoder_code_dyn_elem_ptr)) >>
     simp[abi_decoder_code_def] >> metis_tac[pairTheory.SND]) >>
  first_x_assum imp_res_tac >> gvs[comp_return_def] >> decide_tac
QED

val Ck = ``\ty tv.
 !dst src hi st st' ctx func site initial limit_st sb d D N ids av v root_di.
 compile_abi_decode_to_buf dst src DLOAD hi (type_to_abi_dec_info sf ce ty) st = ((),st') /\
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
 actual.vs_labels = initial.vs_labels /\ actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code``;

Theorem deploy_ctor_array_body_at_index:
  (^Ck) ty tv /\
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
      [(d+32+j*type_memory_bytes ce ty,type_memory_bytes ce ty)] s t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `abi_decoder_ranges DLOAD hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s` by
    (asm_x "child" kall_tac >>
     drule_all deploy_ctor_array_observation_ranges >> simp[]) >>
  drule_all deploy_ctor_array_observation_setup_inputs >> strip_tac >>
  `abi_decoder_operand_live st.cs_next_var src /\
   abi_decoder_operand_live st.cs_next_var dst /\
   abi_decoder_operand_live st.cs_next_var hi /\
   abi_decoder_operand_live st.cs_next_var ip` by
    (asm_x "child" kall_tac >> metis_tac[abi_decoder_operand_live_mono]) >>
  `fresh_vars_wrt limit_st s` by (BETA_TAC >> fs[]) >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_array_body_code >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all deploy_ctor_array_setup_at_index >>
  disch_then (qspec_then `ctx` (qx_choose_then `prepared` (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `(^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j prepared` by
    (asm_x "child" kall_tac >>
     `next <= st.cs_next_var` by first_assum ACCEPT_TAC >>
     drule_all deploy_ctor_array_observation_address >> simp[]) >>
  `prepared.vs_data_section = initial.vs_data_section /\
   (!w. eval_operand hi initial = SOME w ==> eval_operand hi prepared = SOME w)` by
    (asm_x "child" kall_tac >> conj_tac
     >- fs[] >> rpt strip_tac >>
     qpat_assum `_ k ctx func site ids D N d _ next limit_st tv vs slot_id slot initial j j prepared`
       (mp_then Any mp_tac deploy_ctor_array_observation_operand) >>
     disch_then irule >> simp[]) >>
  mp_tac (Q.INST [`prepared` |-> `prepared:venom_state`,
    `initial` |-> `initial:venom_state`] ctor_actual_array_child_inputs_at_index) >>
  (impl_tac >- (asm_x "child" kall_tac >> asm_simp_tac bool_ss [])) >>
  simp_tac bool_ss [LET_THM] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared /\
   ctor_actual_scratch func ids D N prepared /\ D+N <= prepared.vs_alloca_next` by
    (asm_x "child" kall_tac >> fs[]) >>
  `abi_decoder_operand_live middle.cs_next_var hi /\
   abi_decoder_operand_live middle.cs_next_var ip` by
    (asm_x "child" kall_tac >> metis_tac[abi_decoder_operand_live_mono]) >>
  `!x. FST (SND ops) = Var x \/ SND (SND ops) = Var x \/ hi = Var x ==>
    not_fresh_at middle x` by
    (asm_x "child" kall_tac >> rpt strip_tac >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def, IN_DEF]) >>
  `st.cs_next_id <= middle.cs_next_id` by
    (asm_x "child" kall_tac >> drule deploy_ctor_array_setup_ids >> simp[]) >>
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
  asm "child" (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`) o BETA_RULE) >>
  disch_then (drule_at (Pat `abi_decoder_metadata _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand (FST (SND ops)) _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand (SND (SND ops)) _ = _`)) >>
  disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >>
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
  `(^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial (SUC j) j t` by
    (irule deploy_ctor_array_observation_child >>
     asm_simp_tac bool_ss [] >>
     goal_assum (drule_at (Pat `abi_encoder_registered_effect _ _ _ _`)) >>
     asm_simp_tac bool_ss [] >>
     qexists `middle` >> asm_simp_tac bool_ss [] >>
     qpat_assum `_ k ctx func site ids D N d _ next limit_st tv vs slot_id slot initial j j prepared`
       (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
     qpat_assum `_ k ctx func site ids D N d _ next limit_st tv vs slot_id slot initial j j s`
       (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
     asm_simp_tac bool_ss []) >>
  `eval_operand (FST ops) t = SOME (n2w j)` by
    (irule ctor_actual_old_operand >> qexistsl [`prepared`, `middle`] >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, IN_DEF]) >>
  `eval_operand ip prepared = SOME (n2w slot)` by
    (qpat_assum `_ k ctx func site ids D N d _ next limit_st tv vs slot_id slot initial j j prepared`
       (mp_then Any mp_tac deploy_ctor_array_observation_operand) >>
     disch_then irule >> simp[]) >>
  `eval_operand ip t = SOME (n2w slot)` by
    (irule ctor_actual_old_operand >> qexistsl [`prepared`, `middle`] >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, IN_DEF]) >>
  qexists `t` >> asm_simp_tac bool_ss [] >>
  conj_tac >- metis_tac[abi_decode_sim_trans] >>
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

Theorem deploy_ctor_array_iteration:
  (^Ck) ty tv /\
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
    abi_decode_sim ctx func s t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `end_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  asm "child" assume_tac >>
  drule_all deploy_ctor_array_body_at_index >>
  disch_then (qx_choose_then `body_state` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  asm_x "child" kall_tac >>
  `all_have_type tv vs` by metis_tac[abi_decoder_dynarray_values] >>
  `lookup_block body_state.vs_current_bb func.fn_blocks = SOME bb /\
   eval_operand (Var iv) body_state = SOME (n2w j)` by
    (asm_simp_tac bool_ss [] >> metis_tac[]) >>
  drule_all deploy_ctor_array_backedge_run >>
  disch_then (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists `t` >> asm_simp_tac bool_ss [] >>
  metis_tac[abi_decode_sim_trans]
QED

Theorem deploy_ctor_array_header_reach:
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD hi
    hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD hi ip src dst
    sb d slot b cap next initial /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  (^Ok) k ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot initial j j s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?h. (^Ok) k ctx func site ids D N d outsz next limit_st
      tv vs slot_id slot initial j j h /\
    ~h.vs_halted /\ h.vs_current_bb = (if j < LENGTH vs then st.cs_current_bb else exit_lbl) /\
    h.vs_inst_idx = 0 /\ abi_decode_sim ctx func s h
Proof
  strip_tac >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  `eval_operand ip s = SOME (n2w slot) /\ eval_operand src s = SOME (n2w sb)` by
    (`!op w. abi_decoder_operand_live next op /\ eval_operand op initial = SOME w ==>
        eval_operand op s = SOME w` by
       (rpt strip_tac >> drule_all deploy_ctor_array_observation_operand >> simp[]) >>
     fs[abi_decoder_ranges_def, Excl "enc_def"] >> conj_tac >>
     first_x_assum irule >> simp[]) >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source DLOAD s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[abi_decode_source_def, Excl "enc_def"] >>
  `sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256)` by
    fs[abi_decoder_ranges_def, Excl "enc_def"] >>
  drule_all canonical_dynamic_array_count_load >> strip_tac >>
  `abi_decode_load DLOAD (n2w sb : bytes32) s = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ _ = _` mp_tac >> asm_rewrite_tac[]) >>
  drule_all deploy_ctor_array_header_run >> simp[]
QED

val Pk = ``
  abi_decoder_recursive_loop_compiled ce sf ty func st middle end_st ops ip src dst DLOAD hi
    hdr exit_lbl hid header_var first last lo hi_id next limit_st slot_id /\
  abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD hi ip src dst
    sb d slot b cap next initial /\
  fn_inst_ids_distinct func /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  k + unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
  frag_ids st end_st SUBSET ids /\ slot_id NOTIN frag_ids middle end_st /\
  slot_id IN ctor_actual_sites func ids /\
  venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))``;

Theorem deploy_ctor_array_loop_step:
  (^Ck) ty tv /\ ^Pk /\
  (^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j s /\ j < LENGTH vs /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. (^Ok) k ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (SUC j) (SUC j) t /\
    ~t.vs_halted /\ t.vs_current_bb = hdr /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  drule_all deploy_ctor_array_header_reach >>
  disch_then (qx_choose_then `h` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `h.vs_current_bb = st.cs_current_bb` by gvs[] >>
  drule abi_decoder_recursive_data_facts >> strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decoder_recursive_compiled_facts >> strip_tac >>
  qpat_assum `abi_decoder_recursive_loop_compiled _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_compiled_def]) >>
  qpat_assum `abi_decoder_recursive_loop_data _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_data_def]) >>
  `32 + LENGTH vs * type_memory_size tv <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
    (asm_simp_tac bool_ss [] >> simp[]) >>
  qpat_x_assum `?bb. lookup_block end_st.cs_current_bb _ = _ /\ _` strip_assume_tac >>
  `~h.vs_halted /\ h.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  asm "child" assume_tac >>
  drule_all deploy_ctor_array_iteration >>
  disch_then (qx_choose_then `t` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qexists `t` >> asm_simp_tac bool_ss [] >> metis_tac[abi_decode_sim_trans]
QED

Theorem deploy_ctor_array_finite_bridge[local]:
  i <= n /\ R i s /\
  (!j u. j < n /\ R j u ==> ?v. R (SUC j) v /\ abi_decode_sim ctx func u v) /\
  (!u. R n u ==> ?v. Post v /\ abi_decode_sim ctx func u v) ==>
  ?v. Post v /\ abi_decode_sim ctx func s v
Proof
  strip_tac >> irule abi_decode_finite_iteration >>
  qexistsl [`n`, `i`, `R`] >> simp[]
QED

Theorem deploy_ctor_array_loop_finite:
  (^Ck) ty tv /\ ^Pk /\
  (^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial i i s /\
  ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
  ?t. (^Ok) k ctx func site ids D N d
      (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
      tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) t /\
    ~t.vs_halted /\ t.vs_current_bb = exit_lbl /\ t.vs_inst_idx = 0 /\
    abi_decode_sim ctx func s t
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
  qabbrev_tac `R = \j u. (^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial j j u /\
    ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0` >>
  qabbrev_tac `Post = \u. (^Ok) k ctx func site ids D N d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
    tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) u /\
    ~u.vs_halted /\ u.vs_current_bb = exit_lbl /\ u.vs_inst_idx = 0` >>
  `i <= LENGTH vs /\ R i s` by
    (simp[Abbr `R`] >> fs[]) >>
  `!j u. j < LENGTH vs /\ R j u ==>
    ?v. R (SUC j) v /\ abi_decode_sim ctx func u v` by
    (simp[Abbr `R`] >> rpt strip_tac >> asm "child" assume_tac >>
     `(^Ok) k ctx func site ids D N d
       (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
       tv vs slot_id slot initial j j u` by simp[] >>
     drule_all deploy_ctor_array_loop_step >> simp[CONJ_ASSOC]) >>
  `!u. R (LENGTH vs) u ==> ?v. Post v /\ abi_decode_sim ctx func u v` by
    (simp[Abbr `R`, Abbr `Post`] >> rpt strip_tac >>
     `(^Ok) k ctx func site ids D N d
       (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
       tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) u` by simp[] >>
     drule_all (Q.INST [`s` |-> `u:venom_state`, `j` |-> `LENGTH (vs:vyperValue$value list)`]
       deploy_ctor_array_header_reach) >> simp[CONJ_ASSOC]) >>
  `?t. Post t /\ abi_decode_sim ctx func s t` by
    (irule deploy_ctor_array_finite_bridge >> qexistsl [`R`, `i`, `LENGTH vs`] >>
     asm_simp_tac bool_ss []) >>
  gvs[Abbr `Post`] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem deploy_ctor_array_prepared_run:
 (^Ck) ty tv /\ ^(subst [``initial:venom_state`` |-> ``prepared:venom_state``] Pk) /\
 (^Ok) k ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
   tv vs slot_id slot initial 0 0 prepared /\ earlier <= next /\
 lookup_block prepared.vs_current_bb func.fn_blocks = SOME bb /\
 bb.bb_instructions = prefix ++ [mk_inst id JMP [Label hdr] []] /\
 lookup_block hdr func.fn_blocks = SOME hdr_bb /\
 phi_prefix_length hdr_bb.bb_instructions = 0 /\
 ~prepared.vs_halted /\ prepared.vs_inst_idx = LENGTH prefix /\
 abi_decode_sim ctx func initial prepared ==>
 ?actual.
   val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d actual.vs_memory /\
   (^Ok) k ctx func site ids D N d
     (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
     tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) actual /\
   ~actual.vs_halted /\ actual.vs_current_bb = exit_lbl /\ actual.vs_inst_idx = 0 /\
   abi_decode_sim ctx func initial actual
Proof
 disch_then (CONJUNCTS_THEN2 (mk_asm "child") (MAP_EVERY assume_tac o CONJUNCTS)) >>
 `(^Ok) k ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) next limit_st
   tv vs slot_id slot prepared 0 0 prepared` by
   (irule deploy_ctor_array_observation_self >> goal_assum (drule_at Any)) >>
 drule_all deploy_ctor_array_entry_jump >>
 disch_then (qx_choose_then `h` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 asm "child" assume_tac >>
 drule_all deploy_ctor_array_loop_finite >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 `(^Ok) k ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
   tv vs slot_id slot initial (LENGTH vs) (LENGTH vs) actual` by
   (irule deploy_ctor_array_observation_compose >> goal_assum (drule_at Any) >> simp[]) >>
 qexists `actual` >> asm_simp_tac bool_ss [] >> conj_tac
 >- (irule deploy_ctor_array_observation_exit >> goal_assum (drule_at Any)) >>
 irule abi_decode_sim_trans >> qexists `prepared` >> asm_simp_tac bool_ss [] >>
 irule abi_decode_sim_trans >> qexists `h` >> simp[]
QED

Theorem deploy_ctor_array_setup_ranges:
 (^Ok) k ctx func site ids D N d outsz earlier limit_st
   tv vs slot_id slot initial 0 0 prepared /\
 abi_decoder_operand_live earlier src /\ abi_decoder_operand_live earlier dst /\
 abi_decoder_operand_live earlier hi /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + len < dimword (:256) /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
   sb + len <= h /\ h < dimword (:256)) /\
 0 < outsz /\ D <= d /\ d + outsz <= D+N /\
 k + unit_alloca_budget ctx < dimword (:256) /\ slot_id IN ctor_actual_sites func ids ==>
 abi_decoder_ranges DLOAD hi src dst sb len d outsz slot 32 prepared /\
 slot < dimword (:256) /\ venomMemDefs$regions_disjoint (slot,32) (d,outsz)
Proof
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `eval_operand src prepared = SOME (n2w sb)` by
   (qpat_assum `(^Ok) k ctx func site ids D N d outsz earlier limit_st
      tv vs slot_id slot initial 0 0 prepared`
      (mp_then Any mp_tac deploy_ctor_array_observation_operand) >>
    disch_then irule >> simp[]) >>
 `eval_operand dst prepared = SOME (n2w d)` by
   (qpat_assum `(^Ok) k ctx func site ids D N d outsz earlier limit_st
      tv vs slot_id slot initial 0 0 prepared`
      (mp_then Any mp_tac deploy_ctor_array_observation_operand) >>
    disch_then irule >> simp[]) >>
 `hi = Lit 0w \/ ?h. eval_operand hi prepared = SOME (n2w h) /\
   sb + len <= h /\ h < dimword (:256)` by
   (Cases_on `hi = Lit 0w` >- simp[] >>
    qpat_x_assum `hi = Lit 0w \/ _` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
    qexists `h` >> simp[] >>
    qpat_assum `(^Ok) k ctx func site ids D N d outsz earlier limit_st
      tv vs slot_id slot initial 0 0 prepared`
      (mp_then Any mp_tac deploy_ctor_array_observation_operand) >>
    disch_then irule >> simp[]) >>
 qpat_assum `(^Ok) k ctx func site ids D N d outsz earlier limit_st
   tv vs slot_id slot initial 0 0 prepared`
   (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
 `slot < dimword (:256)` by
   (drule_all deploy_ctor_index_slot_bound >> simp[]) >>
 drule_all ctor_actual_sites_scratch >> strip_tac >>
 `venomMemDefs$regions_disjoint (d,outsz) (slot,32)` by
   (irule ctor_actual_region_contained >> qexistsl [`D`, `N`] >> simp[]) >>
 `d + outsz < dimword (:256)` by
   (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >>
    metis_tac[LESS_EQ_TRANS, LESS_EQ_LESS_TRANS]) >>
 asm_simp_tac (srw_ss()) [abi_decoder_ranges_def, abi_decode_source_opcode_def] >>
 gvs[venomMemDefsTheory.regions_disjoint_def] >>
 disj2_tac >> qexists `h` >> simp[]
QED

Theorem deploy_ctor_array_setup_context:
 abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
 abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
   (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
   (ListV avs) (ArrayV (DynArrayV vs)) /\
 (^Ok) k ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) earlier limit_st
   tv vs slot_id slot initial 0 0 prepared /\
 abi_decode_index_init header_st = (ip,loop_st) /\ earlier <= loop_st.cs_next_var /\
 eval_operand ip prepared = SOME (n2w slot) /\
 abi_decoder_operand_live earlier src /\ abi_decoder_operand_live earlier dst /\
 abi_decoder_operand_live earlier hi /\
 eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
   initial.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
   sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) <= h /\
   h < dimword (:256)) /\
 D <= d /\ d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) <= D+N /\
 k + unit_alloca_budget ctx < dimword (:256) /\ slot_id IN ctor_actual_sites func ids ==>
 abi_decoder_recursive_loop_data ce env sf ty tv maxn avs vs DLOAD hi ip src dst
   sb d slot slot 32 loop_st.cs_next_var prepared /\
 mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
   prepared.vs_data_section = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
 (^Ok) k ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) loop_st.cs_next_var limit_st
   tv vs slot_id slot prepared 0 0 prepared /\
 venomMemDefs$regions_disjoint (slot,32) (d,type_memory_bytes ce (ArrayT ty (Dynamic maxn)))
Proof
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `0 < type_memory_bytes ce (ArrayT ty (Dynamic maxn))` by
   simp[Once type_memory_bytes_def] >>
 drule_all deploy_ctor_array_setup_ranges >> strip_tac >>
 drule abi_decode_index_init_shape >> strip_tac >>
 `abi_decoder_operand_live loop_st.cs_next_var ip` by
   (simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def, IN_DEF,
      ASCIInumbersTheory.toString_inj] >> rpt strip_tac >> decide_tac) >>
 `abi_decoder_operand_live loop_st.cs_next_var src /\
  abi_decoder_operand_live loop_st.cs_next_var dst /\
  abi_decoder_operand_live loop_st.cs_next_var hi` by
   metis_tac[abi_decoder_operand_live_mono] >>
 `(^Ok) k ctx func site ids D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) loop_st.cs_next_var limit_st
   tv vs slot_id slot prepared 0 0 prepared` by
   (irule deploy_ctor_array_observation_self >> goal_assum (drule_at Any)) >>
 fs[abi_decoder_recursive_loop_data_def, Excl "enc_def"]
QED

Theorem deploy_ctor_array_scratch_enlarge[local]:
 small SUBSET ids /\ ctor_actual_scratch func small D N final /\
 abi_encoder_registered_effect (ctor_actual_sites func small) regions initial final /\
 ctor_actual_scratch func ids D N initial ==>
 ctor_actual_scratch func ids D N final
Proof
 strip_tac >> simp_tac bool_ss [ctor_actual_scratch_def] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 Cases_on `inst.inst_id IN small`
 >- (qpat_x_assum `ctor_actual_scratch func small _ _ final` mp_tac >>
     simp_tac bool_ss [ctor_actual_scratch_def] >>
     disch_then (qspecl_then [`inst`, `b`, `sz`] mp_tac) >> asm_rewrite_tac[]) >>
 `inst.inst_id NOTIN ctor_actual_sites func small` by simp[ctor_actual_sites_def] >>
 qpat_x_assum `abi_encoder_registered_effect _ _ initial final` mp_tac >>
 simp_tac bool_ss [abi_encoder_registered_effect_def] >> strip_tac >>
 `FLOOKUP initial.vs_allocas inst.inst_id = SOME (b,sz)` by metis_tac[] >>
 qpat_x_assum `ctor_actual_scratch func ids _ _ initial` mp_tac >>
 simp_tac bool_ss [ctor_actual_scratch_def] >>
 disch_then (qspecl_then [`inst`, `b`, `sz`] mp_tac) >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_dynamic_array_loop_run:
 (^Ck) ty tv /\
 (is_abi_dynamic ce.ce_struct_fields ty \/
   dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) ==>
 (^Ck) (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
Proof
 qabbrev_tac `Child = (^Ck) ty tv` >>
 disch_then (CONJUNCTS_THEN2 (mk_asm "child") assume_tac) >>
 simp_tac bool_ss [] >> rpt gen_tac >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule abi_decoder_dynarray_metadata_shape >> strip_tac >> gnvs[Excl "enc_def"] >>
 `abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    (type_to_abi_dec_info ce.ce_struct_fields ce (ArrayT ty (Dynamic maxn)))
    (ListV avs) (ArrayV (DynArrayV vs))` by fs[abi_decoder_metadata_def] >>
 `compile_abi_decode_to_buf dst src DLOAD hi
    (DecDynArray (type_to_abi_dec_info sf ce ty)
      (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty)
      (is_abi_dynamic ce.ce_struct_fields ty) maxn) st = ((),st')` by
    (qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [Once type_to_abi_dec_info_def]) >>
 drule_all ctor_actual_array_loop_layout >> strip_tac >>
 drule_all ctor_actual_array_prefix_inputs >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 `abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi` by
   (Cases_on `src` >> Cases_on `dst` >> Cases_on `hi` >>
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
 `loop_st.cs_next_var <= limit_st.cs_next_var` by
   fs[abi_decoder_recursive_loop_compiled_def] >>
 `32 <= type_memory_bytes ce (ArrayT ty (Dynamic maxn)) /\ d+32 <= D+N` by
   fs[Once type_memory_bytes_def] >>
 `d < dimword (:256)` by
   (drule_all deploy_ctor_shifted_frontier_bound >> strip_tac >> decide_tac) >>
 `ctor_actual_scratch func (frag_ids st st') D N initial` by
   (irule ctor_actual_scratch_restrict >> goal_assum (drule_at Any) >> simp[]) >>
 `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func))` by
   (irule ctor_actual_function_ids >> simp[]) >>
 drule_all deploy_ctor_array_prefix_header_index_entry >>
 disch_then (qspec_then `tv`
   (qx_choose_then `prepared` (qx_choose_then `slot` (MAP_EVERY assume_tac o CONJUNCTS)))) >>
 `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
 `st.cs_next_var <= loop_st.cs_next_var` by
   (drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
    drule_all abi_decode_array_header_shape >> strip_tac >>
    drule abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
 drule_all deploy_ctor_array_setup_context >>
 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
 drule_all abi_decoder_loop_phase_entry >> disch_tac >>
 drule_all abi_decoder_recursive_compiled_facts >> strip_tac >>
 `?bb. lookup_block prepared.vs_current_bb func.fn_blocks = SOME bb /\
   bb.bb_instructions = loop_st.cs_current_insts ++
     [mk_inst loop_st.cs_next_id JMP [Label (FST labels)] []]` by simp[] >>
 pop_assum strip_assume_tac >>
 asm_x "child" mp_tac >> simp_tac bool_ss [Abbr `Child`] >> disch_tac >>
 `(^Ck) ty tv` by (BETA_TAC >> first_assum ACCEPT_TAC) >>
 drule_all deploy_ctor_array_prepared_run >>
 disch_then (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS)) >>
 qpat_assum `(^Ok) k ctx func site (frag_ids st st') D N d
   (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) st.cs_next_var limit_st
   tv vs header_st.cs_next_id slot initial (LENGTH vs) (LENGTH vs) actual`
   (MAP_EVERY assume_tac o CONJUNCTS o BETA_RULE) >>
 `ctor_actual_scratch func ids D N actual` by
   (irule deploy_ctor_array_scratch_enlarge >> goal_assum (drule_at Any) >> simp[]) >>
 qexists `actual` >> asm_simp_tac bool_ss [] >>
 conj_tac
 >- (rpt strip_tac >> first_x_assum irule >>
     fs[abi_decoder_older_vars_def, not_fresh_at_def]) >>
 drule abi_decoder_array_setup_head >> strip_tac >>
 qpat_x_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
 asm_rewrite_tac[] >> disch_then (mp_tac o MATCH_MP abi_decoder_loop_suffix_facts) >> simp[]
QED
