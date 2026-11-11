(* Counted complex constructors reuse physical invariant boundaries. *)
Theory bodyIntCallEncoderCountedComplex
Ancestors
  bodyIntCallEncoderCountedMembers bodyIntCallEncoderCountedSpine
  bodyIntCallEncoderCountedPhases bodyIntCallEncoderCountedPrefix
  abiScratchMembers abiScratchMembersIndex abiScratchMemberContract
  abiScratchMembersInterpret abiScratchComplex abiScratchEncoderContract
  abiEncoderMemberSpine abiEncoderComplexCode abiEncoderComplexDynamic
  abiEncoderMembersContract abiEncoderMembersDefs abiEncoderMembersInput
  abiEncoderMemberCode abiEncoderInput abiEncoder abiDecoderLoop abiDecoderContract
  compileEnv valueEncoding contractABI venomState words list arithmetic fragGasPath
  venomExecSemantics abiScratchOwnedPrefix abiScratchPrefix abiEncoderComplexPrefix
  abiDecoderAllocation abiScratchAddress abiDecoderDynamicLoopSetup pred_set
  abiDecoderProtectedScratch abiDecoderIndexInit abiEncoderAddressReach emitHelper

Theorem intcall_encoder_path_sim:
  gas_path ctx func initial n (OK actual) ==> abi_decode_sim ctx func initial actual
Proof
  disch_then (mp_tac o MATCH_MP gas_path_normal) >> simp[abi_decode_sim_def]
QED

Theorem intcall_scratch_complex_prepare:
  abi_encode_complex_prefix infos st = (dyn_ptr,prepared) /\ fn_has_code st prepared func /\
  abi_scratch_members_pre infos tys avs st src dst sb 0 d output_size first last b cap initial /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= output_size /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  prepared.cs_next_id <= last /\ prepared.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st initial /\ ~initial.vs_halted /\
  initial.vs_current_bb = st.cs_current_bb /\ initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ready slot n.
    abi_scratch_members_inv infos tys avs [] [] T dyn_ptr st.cs_next_id slot first last
      st.cs_next_id prepared limit_st src dst sb 0 0 d (head_lengths tys 0) output_size b cap ready /\
    abi_scratch_effect first last st.cs_next_id prepared.cs_next_id st.cs_next_var
      limit_st d output_size b cap initial ready /\ abi_decode_sim ctx func initial ready /\
    gas_path ctx func initial n (OK ready)
Proof
  strip_tac >>
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >>
  drule abi_encoder_complex_input_metadata >> strip_tac >>
  drule abi_encoder_complex_prefix_shape >> strip_tac >>
  `st.cs_next_id < prepared.cs_next_id /\ st.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  `st.cs_next_id IN abi_decoder_ids first last` by (simp[abi_decoder_ids_def] >> decide_tac) >>
  `FINITE (abi_decoder_ids first last)` by simp[] >>
  drule_all (Q.INST [`ids` |-> `abi_decoder_ids first last`] intcall_scratch_encoder_prefix_counted) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_scratch_owned_prefix_frame >> disch_tac >>
  drule_all abi_scratch_prefix_effect >>
  disch_then (qspecl_then [`output_size`, `d`] assume_tac) >>
  drule_all abi_scratch_members_pre_effect >> disch_tac >>
  drule_all abi_scratch_members_pre_mono >> disch_tac >>
  drule_all abi_scratch_prefix_cursor >> strip_tac >>
  `fresh_vars_wrt limit_st actual /\ abi_decoder_budget first last b cap actual` by
    fs[abi_scratch_effect_def] >>
  mp_tac (Q.INST [`active` |-> `T`, `site` |-> `st.cs_next_id`, `lo` |-> `st.cs_next_id`,
    `st` |-> `prepared`, `initial` |-> `actual:venom_state`, `hl` |-> `head_lengths tys 0`]
    abi_scratch_members_initial_inv) >>
  impl_tac >- (gvs[Excl "enc_def"] >> decide_tac) >> disch_tac >>
  drule intcall_encoder_path_sim >> disch_tac >>
  qexistsl_tac [`actual`, `slot`, `n`] >> asm_simp_tac bool_ss []
QED

Theorem intcall_scratch_complex_static:
  (!y ei cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_members_child_pre (first,last,b,cap,limit_st) y (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_members_child_post (ctx,func) (first,last,b,cap,limit_st)
        y (ei,cd,cs,cst,cen,co) r u) /\
  EVERY (\(ei,az,mz,dyn). P ei) infos /\
  EVERY (\(ei,az,mz,dyn). abi_scratch_encoder ei) infos /\
  ~EXISTS (\(_,_,_,dyn). dyn) infos /\
  abi_encoder_spine_core_code func (AbiComplex infos,dst,src,start,end_st,out) /\
  abi_scratch_member_core_pre (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
    (AbiComplex infos,dst,src,start,end_st,out) initial ==>
  ?actual. intcall_encoder_core_path ctx func (AbiComplex infos,dst,src,start,end_st,out)
      initial actual /\
    abi_scratch_member_core_post (ctx,func) (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
      (AbiComplex infos,dst,src,start,end_st,out) initial actual
Proof
  strip_tac >> simp_tac bool_ss [abi_scratch_member_core_post_def] >>
  qpat_x_assum `abi_encoder_spine_core_code _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_core_code_def]) >>
  qpat_x_assum `abi_scratch_member_core_pre _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_member_core_pre_def]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  disch_then (qx_choose_then `tys` (qx_choose_then `avs`
    (MAP_EVERY assume_tac o CONJUNCTS)) o REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  drule_all abi_scratch_members_root_pre >> strip_tac >>
  qpat_assum `enc at (ListV avs) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  qpat_assum `abi_scratch_members_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_scratch_members_pre_def]) >> strip_tac >>
  drule_all abi_encoder_complex_static_length >> disch_tac >>
  drule abi_encoder_complex_static_flags >> disch_tac >>
  drule_all abi_encoder_complex_static_trace >> strip_tac >>
  drule abi_encoder_members_bounds >> strip_tac >>
  `start.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`active` |-> `F`, `dyn_ptr` |-> `Lit 0w`, `site` |-> `0:num`,
    `slot` |-> `0:num`, `lo` |-> `start.cs_next_id`, `st` |-> `start`,
    `hl` |-> `head_lengths tys 0`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_members_initial_inv) >>
  impl_tac >- asm_simp_tac (srw_ss()) [abi_encoder_cursor_def, Excl "enc_def"] >> strip_tac >>
  `abi_encoder_spine_code func limit_st end_st.cs_next_id (dst,src,Lit 0w)
    infos (start,0,0) (ignored,end_st)` by simp[abi_encoder_spine_code_def] >>
  drule_all intcall_scratch_members_run >> strip_tac >>
  rename1 `gas_path ctx func initial n (OK actual)` >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual`
    (assume_tac o SIMP_RULE bool_ss [APPEND, ADD_CLAUSES]) >>
  drule abi_scratch_members_final_output >> strip_tac >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  qexists_tac `actual` >>
  asm_simp_tac (srw_ss()) [intcall_encoder_core_path_def, abi_scratch_member_core_post_def,
    eval_operand_def, Excl "enc_def"] >> goal_assum (drule_at Any)
QED

Theorem intcall_scratch_complex_finish:
  abi_scratch_members_inv [] [] [] tys avs T dyn_ptr site slot first last lo st limit_st
    src dst sb so ho d hl output_size b cap encoded /\
  emit_op MLOAD [dyn_ptr] st = (out,end_st) /\ fn_has_code st end_st func /\
  end_st.cs_next_id <= last /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual n.
    mem_bytes_at d (LENGTH (enc (Tuple tys) (ListV avs))) actual.vs_memory =
      enc (Tuple tys) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple tys) (ListV avs)))) /\
    abi_scratch_effect first last lo end_st.cs_next_id st.cs_next_var
      limit_st d output_size b cap encoded actual /\
    actual.vs_current_bb = end_st.cs_current_bb /\ actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ~actual.vs_halted /\ abi_decode_sim ctx func encoded actual /\
    gas_path ctx func encoded n (OK actual)
Proof
  strip_tac >> drule abi_encoder_emit_address_shape >> strip_tac >>
  `st.cs_next_id <= end_st.cs_next_id` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[]) >>
  drule abi_scratch_members_final_output >> strip_tac >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ encoded`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_members_inv_def]) >>
  qpat_x_assum `abi_encoder_cursor T _ _ _ _ _ _ (LENGTH _) _`
    (MAP_EVERY assume_tac o CONJUNCTS o SIMP_RULE bool_ss [abi_encoder_cursor_def]) >>
  `site IN abi_decoder_ids first last` by
    (simp_tac std_ss [abi_decoder_ids_def, GSPECIFICATION] >> decide_tac) >>
  drule_all abi_decoder_budget_site_bounds >> strip_tac >>
  drule abi_decoder_budget_word_bound >> strip_tac >> `slot < dimword (:256)` by decide_tac >>
  drule_all intcall_encoder_load_counted >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all abi_scratch_address_effect >>
  disch_then (qspecl_then [`output_size`, `lo`, `end_st.cs_next_id`, `d`] assume_tac) >>
  drule intcall_encoder_path_sim >> disch_tac >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  qexistsl_tac [`ready`, `n`] >> asm_simp_tac (srw_ss()) [w2n_n2w, Excl "enc_def"]
QED

Theorem intcall_scratch_complex_dynamic:
  (!y ei cd cs cst cen co r. P ei /\
    abi_encoder_spine_core_code func (ei,cd,cs,cst,cen,co) /\
    abi_scratch_members_child_pre (first,last,b,cap,limit_st) y (ei,cd,cs,cst,cen,co) r ==>
    ?u. intcall_encoder_core_path ctx func (ei,cd,cs,cst,cen,co) r u /\
      abi_scratch_members_child_post (ctx,func) (first,last,b,cap,limit_st)
        y (ei,cd,cs,cst,cen,co) r u) /\
  EVERY (\(ei,az,mz,dyn). P ei) infos /\
  EVERY (\(ei,az,mz,dyn). abi_scratch_encoder ei) infos /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  abi_encoder_spine_core_code func (AbiComplex infos,dst,src,start,end_st,out) /\
  abi_scratch_member_core_pre (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
    (AbiComplex infos,dst,src,start,end_st,out) initial ==>
  ?actual. intcall_encoder_core_path ctx func (AbiComplex infos,dst,src,start,end_st,out)
      initial actual /\
    abi_scratch_member_core_post (ctx,func) (at,av,sb,source_cap,d) (first,last,b,cap,limit_st)
      (AbiComplex infos,dst,src,start,end_st,out) initial actual
Proof
  strip_tac >> simp_tac bool_ss [abi_scratch_member_core_post_def] >>
  qpat_x_assum `abi_encoder_spine_core_code _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_encoder_spine_core_code_def]) >>
  qpat_x_assum `abi_scratch_member_core_pre _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_member_core_pre_def]) >>
  qpat_assum `abi_scratch_input _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_scratch_input_def]) >>
  disch_then (qx_choose_then `tys` (qx_choose_then `avs`
    (MAP_EVERY assume_tac o CONJUNCTS)) o REWRITE_RULE [abi_encoder_complex_input_iff]) >>
  qpat_x_assum `av = ListV avs` SUBST_ALL_TAC >>
  drule_all abi_scratch_members_root_pre >> strip_tac >>
  qpat_assum `enc at (ListV avs) = _`
    (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th]) >> PURE_REWRITE_TAC [th]) >>
  drule_all abi_encoder_complex_dynamic_context >>
  disch_then (qx_choose_then `dyn_ptr` (qx_choose_then `prepared`
    (qx_choose_then `ignored` (qx_choose_then `middle` (MAP_EVERY assume_tac o CONJUNCTS))))) >>
  `prepared.cs_next_id <= last /\ middle.cs_next_id <= last /\
    prepared.cs_next_var <= limit_st.cs_next_var /\ middle.cs_next_var <= limit_st.cs_next_var /\
    start.cs_next_var <= prepared.cs_next_var` by decide_tac >>
  mp_tac (Q.INST [`st` |-> `start`, `output_size` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    intcall_scratch_complex_prepare) >>
  impl_tac >- asm_simp_tac (srw_ss()) [Excl "enc_def"] >> strip_tac >>
  `abi_encoder_spine_code func limit_st middle.cs_next_id (dst,src,dyn_ptr)
    infos (prepared,0,0) (ignored,middle)` by simp[abi_encoder_spine_code_def] >>
  drule_all intcall_scratch_members_run >> strip_tac >>
  rename1 `abi_decode_sim ctx func ready encoded` >>
  qpat_assum `abi_scratch_members_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ encoded`
    (assume_tac o SIMP_RULE bool_ss [APPEND, ADD_CLAUSES]) >>
  drule_all intcall_scratch_complex_finish >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `abi_decode_sim ctx func encoded actual` >>
  mp_tac (Q.INST [`st` |-> `start`, `sz` |-> `LENGTH (enc (Tuple tys) (ListV avs))`]
    abi_scratch_complex_compose) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> strip_tac >>
  `?k. gas_path ctx func initial k (OK actual)` by
    metis_tac[gas_path_then] >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [intcall_encoder_core_path_def] >>
  goal_assum (drule_at Any) >> simp[]
QED
