Theory ctorDeployLoweringEntryCompleteRegister
Ancestors
  loweringStateRelDefs
 ctorDeployLoweringEntryRegisterRun ctorDeployLoweringEntryCompleteRecursive
 ctorDeployLoweringEntryCompleteRegisterBoundary ctorDeployLoweringEntryCanonical
 abiDecoderLoop abiDecoderCounters abiDecoderCode abiDecoderContract abiDecoderCoherence
 abiDecoderTypedContract abiDecoderReentryAddress abiEncoder abiEncoderProps
 ctorAbiActualSites ctorAbiActualFrame ctorRegisterArgs abiEncoderRegisteredEffect
 ctorDeployMemoryFrontier actualAllocCredit allocaFrontierBound allocaBudgetProps
 compileEnv exprLowering exprLoweringProps emitHelperProps
 entryArgPtrs localPtrsProps ctorDeployLoweringEntryAllocation
 actualAllocExec fragExec instIdxIndep loweringHalt vyperCompiler ctorAbiActualArrayRun
 compileVyper moduleLowering rich_list abiDecoderVarSequence
 venomExecSemantics venomState venomInst venomMemDefs
 vyperABI words list finite_map pred_set arithmetic

Theorem deploy_ctor_decode_buffer_old_prefix_complete:
 !k dst src hi ce env ty tv av v st st' ctx func site initial sb d.
 compile_abi_decode_to_buf dst src DLOAD hi
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) st = ((),st') /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
 abi_decoder_metadata ce env ty tv
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) av v /\
 eval_operand src initial = SOME (n2w sb) /\
 eval_operand dst initial = SOME (n2w d) /\
 sb + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
 mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) av))
   initial.vs_data_section = enc (vyper_to_abi_type env ty) av /\
 (hi = Lit 0w \/ ?h. eval_operand hi initial = SOME (n2w h) /\
   sb + LENGTH (enc (vyper_to_abi_type env ty) av) <= h /\ h < dimword (:256)) /\
 (!x. src = Var x \/ dst = Var x \/ hi = Var x ==> not_fresh_at st x) /\
 fresh_vars_wrt st initial /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
   val_in_memory tv v d actual.vs_memory /\
   abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
     [(d,type_memory_bytes ce ty)] initial actual /\
   ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual /\
   initial.vs_alloca_next <= actual.vs_alloca_next /\
   alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
   fresh_vars_wrt st' actual /\
   actual.vs_data_section = initial.vs_data_section /\
   actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
   (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
     lookup_var x actual = SOME w) /\
   ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
   actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
   abi_decode_sim ctx func initial actual /\
   actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
   actual.vs_outcomes = initial.vs_outcomes /\
   actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 `st.cs_next_var <= st'.cs_next_var` by
   (drule abi_decoder_variable_counter >> simp[]) >>
 `fresh_vars_wrt st' initial` by
   (irule fresh_vars_wrt_mono >> qexists `st` >> simp[GREATER_EQ]) >>
 `ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next initial` by
   (simp_tac bool_ss [ctor_actual_scratch_def, frag_ids_def, GSPECIFICATION] >>
    rpt strip_tac >> res_tac >> gvs[]) >>
 drule (BETA_RULE deploy_ctor_coherent_run_complete) >>
 disch_then (drule_at Any) >>
 disch_then (drule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ = _`)) >>
 disch_then (drule_at (Pat `eval_operand dst initial = _`)) >>
 disch_then (drule_at (Pat `fresh_vars_wrt _ _`)) >>
 simp_tac bool_ss [LESS_EQ_REFL, SUBSET_REFL] >>
 disch_then (qspecl_then [`k`, `ctx`, `site`, `d`] mp_tac) >>
 simp_tac bool_ss [ADD, ZERO_LESS_EQ, LESS_EQ_REFL] >>
 disch_then drule_all >> strip_tac >>
 qexists `actual` >> asm_rewrite_tac[]
QED

Theorem deploy_ctor_effect_scratch_extend_complete[local]:
 abi_encoder_registered_effect (ctor_actual_sites fn child) outs s t /\
 ctor_actual_scratch fn child d n t /\
 (!i. i IN full /\ i NOTIN child ==> FLOOKUP s.vs_allocas i = NONE) ==>
 ctor_actual_scratch fn full d n t
Proof
 simp_tac bool_ss [ctor_actual_scratch_def, abi_encoder_registered_effect_def] >>
 strip_tac >> rpt gen_tac >> strip_tac >> Cases_on `inst.inst_id IN child`
 >- metis_tac[] >>
 `inst.inst_id NOTIN ctor_actual_sites fn child` by simp[ctor_actual_sites_def] >>
 metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem deploy_ctor_effect_future_absent_complete[local]:
 abi_encoder_registered_effect ids outs s t /\
 (!i. k <= i ==> FLOOKUP s.vs_allocas i = NONE) /\
 (!i. k <= i ==> i NOTIN ids) ==>
 !i. k <= i ==> FLOOKUP t.vs_allocas i = NONE
Proof
 simp_tac bool_ss [abi_encoder_registered_effect_def] >> metis_tac[]
QED

Theorem deploy_ctor_decode_constructor_arg_old_prefix_complete:
 !k ce env fargs avs atys encoded i name ty tv v off data_size
  pvar d st st' ctx func site initial.
 i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
 EL i fargs = (name,ty) /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 compile_decode_args ce [build_positional_arg ce (name,ty)] off
   DLOAD (Lit (n2w data_size)) 0 st = ((),st') /\
 FLOOKUP ce.ce_vars name = SOME (PtrVar (Var pvar) (type_memory_bytes ce ty)) /\
 lookup_var pvar initial = SOME (n2w d) /\ not_fresh_at st pvar /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
 abi_decoder_metadata ce env ty tv
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) (EL i avs) v /\
 fresh_vars_wrt st initial /\ fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 d + type_memory_bytes ce ty <= initial.vs_alloca_next /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 val_in_memory tv v d actual.vs_memory /\
 abi_encoder_registered_effect (frag_ids st st')
   [(d,type_memory_bytes ce ty)] initial actual /\
 abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
   [(d,type_memory_bytes ce ty)] initial actual /\
 ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 d + type_memory_bytes ce ty <= actual.vs_alloca_next /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\
 actual.vs_tx_ctx = initial.vs_tx_ctx /\ actual.vs_block_ctx = initial.vs_block_ctx
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 `!tys. vyper_to_abi_types env tys = MAP (vyper_to_abi_type env) tys` by
   (Induct >> simp[vyper_to_abi_type_def]) >>
 `LENGTH atys = LENGTH fargs /\ EL i atys = vyper_to_abi_type env ty` by
   simp[MAP_COMPOSE, EL_MAP] >>
 `i < LENGTH atys /\ LENGTH avs = LENGTH atys` by metis_tac[] >>
 drule_all deploy_ctor_canonical_singleton_prefix >>
 disch_then (qspec_then `ctx`
   (qx_choose_then `src` (qx_choose_then `middle`
     (qx_choose_then `prepared` (qx_choose_then `sb` (map_every assume_tac o CONJUNCTS)))))) >>
 `alloca_inv prepared /\ alloca_frontier_inv_from k ctx func site prepared` by
   (qpat_assum `alloca_inv initial` mp_tac >>
    qpat_assum `alloca_frontier_inv_from _ _ _ _ initial` mp_tac >>
    pure_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def,
      alloca_frontier_inv_from_def, remaining_alloca_budget_def] >>
    asm_simp_tac bool_ss []) >>
 `!aid. middle.cs_next_id <= aid ==> FLOOKUP prepared.vs_allocas aid = NONE` by
   metis_tac[LESS_EQ_TRANS] >>
 `d + type_memory_bytes ce ty <= prepared.vs_alloca_next` by metis_tac[] >>
 Q.SUBGOAL_THEN
   `(Lit (n2w data_size : bytes32) = Lit 0w \/ ?h.
    eval_operand (Lit (n2w data_size)) prepared = SOME (n2w h) /\
    sb + LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) <= h /\
    h < dimword (:256))` assume_tac
 >- (Cases_on `data_size = 0` >- simp[] >>
     disj2_tac >> qexists `data_size` >>
     `data_size < dimword (:256)` by metis_tac[] >>
     simp[eval_operand_def, w2n_n2w]) >>
 `mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env ty) (EL i avs))) initial.vs_data_section =
   enc (vyper_to_abi_type env ty) (EL i avs)` by metis_tac[] >>
 drule_all deploy_ctor_decode_buffer_old_prefix_complete >>
 disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
 suspend "finish"
QED

Resume deploy_ctor_decode_constructor_arg_old_prefix_complete[finish]:
 qpat_assum `prepared.vs_alloca_next = initial.vs_alloca_next`
   (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
 `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle st'))
    [(d,type_memory_bytes ce ty)] initial prepared` by
   (irule abi_encoder_registered_effect_enlarge >>
    qexistsl [`{}:num set`, `[]:(num#num) list`] >> simp[]) >>
 `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids middle st'))
    [(d,type_memory_bytes ce ty)] initial actual` by
   metis_tac[abi_encoder_registered_effect_trans] >>
 `ctor_actual_sites func (frag_ids middle st') SUBSET ctor_actual_sites func (frag_ids st st')` by
   metis_tac[ctor_actual_sites_mono] >>
 `abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st st'))
    [(d,type_memory_bytes ce ty)] initial actual` by
   (irule abi_encoder_registered_effect_enlarge >>
    qexistsl [`ctor_actual_sites func (frag_ids middle st')`, `[(d,type_memory_bytes ce ty)]`] >> simp[]) >>
 `abi_encoder_registered_effect (frag_ids st st')
    [(d,type_memory_bytes ce ty)] initial actual` by
   (irule abi_encoder_registered_effect_enlarge >>
    qexistsl [`ctor_actual_sites func (frag_ids st st')`, `[(d,type_memory_bytes ce ty)]`] >>
    simp[ctor_actual_sites_subset]) >>
 `ctor_actual_scratch func (frag_ids st st') 0 initial.vs_alloca_next actual` by
   (irule deploy_ctor_effect_scratch_extend_complete >>
    qexistsl [`frag_ids middle st'`, `[(d,type_memory_bytes ce ty)]`, `initial`] >>
    asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
    `st.cs_next_id <= i'` by fs[frag_ids_def] >> metis_tac[]) >>
 `middle.cs_next_id <= st'.cs_next_id` by
   (drule abi_decoder_to_buf_code >> simp[abi_decode_source_opcode_def, abi_decoder_code_def]) >>
 `!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE` by
   (gen_tac >> strip_tac >> irule deploy_ctor_effect_future_absent_complete >>
    qexistsl [`ctor_actual_sites func (frag_ids middle st')`, `st'.cs_next_id`, `[(d,type_memory_bytes ce ty)]`, `initial`] >>
    asm_rewrite_tac[] >> conj_tac
    >- simp[ctor_actual_sites_def, frag_ids_def] >>
    rpt strip_tac >>
    qpat_x_assum `!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE` irule >>
    qpat_x_assum `st.cs_next_id <= middle.cs_next_id` mp_tac >>
    qpat_x_assum `middle.cs_next_id <= st'.cs_next_id` mp_tac >>
    qpat_assum `_ <= i'` mp_tac >>
    rpt (pop_last_assum kall_tac) >> decide_tac) >>
 `prepared.vs_outcomes = initial.vs_outcomes /\
  prepared.vs_tx_ctx = initial.vs_tx_ctx /\ prepared.vs_block_ctx = initial.vs_block_ctx` by
   (qpat_x_assum `_ with <|vs_vars := _; vs_inst_idx := _|> = initial` mp_tac >>
    simp[venom_state_component_equality]) >>
 qexists `actual` >> asm_rewrite_tac[] >>
 conj_tac >- (qpat_x_assum `d + type_memory_bytes ce ty <= initial.vs_alloca_next` mp_tac >>
   qpat_x_assum `initial.vs_alloca_next <= actual.vs_alloca_next` mp_tac >>
   rpt (pop_last_assum kall_tac) >> decide_tac) >>
 conj_tac
 >- (rpt strip_tac >>
     `not_fresh_at middle x` by
       (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     metis_tac[]) >>
 metis_tac[abi_decode_sim_trans]
QED

Finalise deploy_ctor_decode_constructor_arg_old_prefix_complete

Theorem deploy_ctor_register_alloc_state_complete[local]:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ initial.vs_alloca_next < dimword (:256) /\
 local_ptrs_rel func ce scopes initial /\ fresh_vars_wrt st initial /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 a = (update_var (STRING #"%" (toString st.cs_next_var))
     (n2w initial.vs_alloca_next)
     (initial with <| vs_allocas := initial.vs_allocas |+
       (st.cs_next_id,(initial.vs_alloca_next,n));
       vs_alloca_next := initial.vs_alloca_next+n |>))
     with vs_inst_idx := LENGTH sa.cs_current_insts ==>
 buf.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
 local_ptrs_rel func ce scopes a /\
 local_backed func (STRING #"%" (toString st.cs_next_var)) a initial.vs_alloca_next n /\
 fresh_vars_wrt sa a /\ not_fresh_at sa (STRING #"%" (toString st.cs_next_var)) /\
 (!aid. sa.cs_next_id <= aid ==> FLOOKUP a.vs_allocas aid = NONE) /\
 (!name b sz. local_region ce scopes a name b sz ==>
   compileEnv$regions_disjoint initial.vs_alloca_next n b sz) /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x a = SOME w) /\
 abi_encoder_registered_effect (frag_ids st sa) [] initial a
Proof
 strip_tac >>
 `not_scope_ptr ce scopes (STRING #"%" (toString st.cs_next_var))` by
   (irule local_ptrs_rel_fresh_not_scope_ptr >>
    qexistsl [`func`, `initial`, `st`] >> simp[GREATER_EQ]) >>
 `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]) initial (n2w n : bytes32) =
    OK (a with vs_inst_idx := initial.vs_inst_idx)` by
   gvs[exec_alloca_def, mk_inst_def, update_var_def, w2n_n2w,
       venom_state_component_equality] >>
 drule local_ptrs_rel_exec_alloca_fresh >> simp[mk_inst_def] >>
 disch_then (qspecl_then [`func`, `ce`, `scopes`] mp_tac) >>
 simp[local_ptrs_rel_inst_idx] >> strip_tac >>
 drule compile_alloc_buffer_parts >> strip_tac >> simp[] >>
 conj_tac
 >- (simp[local_backed_def] >> disj1_tac >>
     qexists `mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString st.cs_next_var)]` >>
     drule_all entry_alloc_buffer_inst >> gvs[mk_inst_def]) >>
 conj_tac
 >- (fs[fresh_vars_wrt_def, update_var_def, GREATER_EQ] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 conj_tac
 >- (simp[FLOOKUP_UPDATE] >> rpt strip_tac >>
     IF_CASES_TAC >> gvs[] >> first_x_assum irule >> decide_tac) >>
 conj_tac
 >- (rpt strip_tac >> qpat_x_assum `!name b sz. local_region _ _ _ _ _ _ ==> _` mp_tac >>
     fs[local_region_def, lookup_var_def] >> metis_tac[]) >>
 conj_tac
 >- (rpt strip_tac >> simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     IF_CASES_TAC >> gvs[lookup_var_def]) >>
 simp[abi_encoder_registered_effect_def, frag_ids_def, GSPECIFICATION,
      update_var_def, FLOOKUP_UPDATE] >>
 rpt strip_tac >> IF_CASES_TAC >> gvs[] >>
 `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` by simp[] >> gvs[]
QED

Theorem deploy_ctor_register_alloc_run_complete[local]:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ alloca_inv initial /\
 alloca_frontier_inv_from k ctx func site initial /\ fn_inst_ids_distinct func /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?a. a = (update_var (STRING #"%" (toString st.cs_next_var))
     (n2w initial.vs_alloca_next)
     (initial with <| vs_allocas := initial.vs_allocas |+
       (st.cs_next_id,(initial.vs_alloca_next,n));
       vs_alloca_next := initial.vs_alloca_next+n |>))
     with vs_inst_idx := LENGTH sa.cs_current_insts /\
 alloca_inv a /\ alloca_frontier_inv_from k ctx func site a /\
 initial.vs_alloca_next+n < dimword (:256) /\
 ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
 abi_decode_sim ctx func initial a
Proof
 strip_tac >>
 `MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
   [STRING #"%" (toString st.cs_next_var)]) (fn_insts func)` by
   (drule_all entry_alloc_buffer_inst >> simp[]) >>
 `initial.vs_alloca_next + n < dimword (:256)` by
   (drule deploy_ctor_alloca_frontier_credit >>
    disch_then drule >>
    simp[mk_inst_def, alloca_size_def, w2n_n2w] >> strip_tac >> decide_tac) >>
 qabbrev_tac `raw = update_var (STRING #"%" (toString st.cs_next_var))
   (n2w initial.vs_alloca_next)
   (initial with <|vs_allocas := initial.vs_allocas |+
     (st.cs_next_id,(initial.vs_alloca_next,n));
     vs_alloca_next := initial.vs_alloca_next+n |>)` >>
 `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString st.cs_next_var)]) initial (n2w n : bytes32) = OK raw` by
   simp[exec_alloca_def, mk_inst_def, w2n_n2w, Abbr `raw`] >>
 `alloca_inv raw` by metis_tac[alloca_inv_exec_alloca] >>
 `alloca_frontier_inv_from k ctx func site raw` by
   (irule deploy_ctor_alloca_frontier_preserved >>
    conj_tac >- metis_tac[ctor_actual_function_ids] >>
    qexistsl [`mk_inst st.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString st.cs_next_var)]`, `initial`, `site`] >>
    fs[mk_inst_def, step_inst_base_def]) >>
 `frag_exec ctx st sa (\u. u = initial)
    (\u. u = raw with vs_inst_idx := LENGTH sa.cs_current_insts) (K F)` by
   (irule compile_alloc_buffer_fresh_frag >> qexistsl [`buf`, `n`] >>
    simp[Abbr `raw`]) >>
 qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
 simp[frag_exec_def] >> disch_then (qspec_then `func` mp_tac) >>
 simp[] >> strip_tac >> simp[abi_decode_sim_def] >>
 irule deploy_ctor_alloca_frontier_fields >>
 goal_assum (drule_at Any) >> simp[]
QED

Theorem deploy_ctor_register_alloc_actual_complete:
 compile_alloc_buffer n st = (buf,sa) /\ fn_has_code st sa func /\
 n < dimword (:256) /\ local_ptrs_rel func ce scopes initial /\
 fresh_vars_wrt st initial /\ alloca_inv initial /\
 alloca_frontier_inv_from k ctx func site initial /\ fn_inst_ids_distinct func /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?a. buf.buf_operand = Var (STRING #"%" (toString st.cs_next_var)) /\
   local_ptrs_rel func ce scopes a /\
   lookup_var (STRING #"%" (toString st.cs_next_var)) a =
     SOME (n2w initial.vs_alloca_next) /\
   local_backed func (STRING #"%" (toString st.cs_next_var)) a initial.vs_alloca_next n /\
   FLOOKUP a.vs_allocas st.cs_next_id = SOME (initial.vs_alloca_next,n) /\
   a.vs_alloca_next = initial.vs_alloca_next+n /\
   a.vs_alloca_next < dimword (:256) /\
   alloca_inv a /\ alloca_frontier_inv_from k ctx func site a /\
   fresh_vars_wrt sa a /\ not_fresh_at sa (STRING #"%" (toString st.cs_next_var)) /\
   (!aid. sa.cs_next_id <= aid ==> FLOOKUP a.vs_allocas aid = NONE) /\
   (!name b sz. local_region ce scopes a name b sz ==>
     compileEnv$regions_disjoint initial.vs_alloca_next n b sz) /\
   a.vs_memory = initial.vs_memory /\
   a.vs_data_section = initial.vs_data_section /\
   a.vs_call_ctx = initial.vs_call_ctx /\ a.vs_labels = initial.vs_labels /\
   a.vs_gas_readings = initial.vs_gas_readings /\ a.vs_code = initial.vs_code /\
   a.vs_outcomes = initial.vs_outcomes /\ a.vs_tx_ctx = initial.vs_tx_ctx /\
   a.vs_block_ctx = initial.vs_block_ctx /\
   (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
     lookup_var x a = SOME w) /\
   abi_encoder_registered_effect (frag_ids st sa) [] initial a /\
   ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
   a.vs_inst_idx = LENGTH sa.cs_current_insts /\
   abi_decode_sim ctx func initial a
Proof
 strip_tac >>
 `FLOOKUP initial.vs_allocas st.cs_next_id = NONE` by simp[] >>
 drule_all deploy_ctor_register_alloc_run_complete >> strip_tac >>
 `initial.vs_alloca_next < dimword (:256)` by decide_tac >>
 drule_all deploy_ctor_register_alloc_state_complete >> strip_tac >>
 qexists `a` >> asm_rewrite_tac[] >>
 gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem deploy_ctor_register_one_actual_complete:
 !k ce env fargs avs atys encoded i name ty entry off data_size old
  buf sa ce' st st' ctx func site initial.
 i < LENGTH fargs /\ LENGTH avs = LENGTH fargs /\
 EL i fargs = (name,ty) /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 off = SUM (MAP abi_member_head_size (TAKE i atys)) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 FLOOKUP ce.ce_vars name = SOME (MemLoc old (type_memory_bytes ce ty)) /\
 lookup_scopes name [scope] = SOME entry /\
 val_wf entry.type entry.value /\
 type_memory_size entry.type <= type_memory_bytes ce ty /\
 abi_decoder_coherent ce env ce.ce_struct_fields ty entry.type /\
 abi_decoder_metadata ce env ty entry.type
   (type_to_abi_dec_info ce.ce_struct_fields ce ty) (EL i avs) entry.value /\
 type_memory_bytes ce ty < dimword (:256) /\
 compile_alloc_buffer (type_memory_bytes ce ty) st = (buf,sa) /\
 ce' = (ce with ce_vars := ce.ce_vars |+
   (name,PtrVar buf.buf_operand (type_memory_bytes ce ty))) /\
 compile_decode_args ce' [build_positional_arg ce (name,ty)] off
   DLOAD (Lit (n2w data_size)) 0 sa = ((),st') /\
 local_ptrs_rel func ce [scope] initial /\ fresh_vars_wrt st initial /\
 fn_has_code st sa func /\ fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
 (sa.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 local_ptrs_rel func ce' [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all deploy_ctor_register_alloc_actual_complete >>
 disch_then (qx_choose_then `a` (map_every assume_tac o CONJUNCTS)) >>
 `ce' = ce with ce_vars := ce.ce_vars |+
   (name,PtrVar (Var (STRING #"%" (toString st.cs_next_var))) (type_memory_bytes ce ty))` by simp[] >>
 `abi_decoder_coherent ce' env ce'.ce_struct_fields ty entry.type /\
  abi_decoder_metadata ce' env ty entry.type
    (type_to_abi_dec_info ce'.ce_struct_fields ce' ty) (EL i avs) entry.value` by simp[] >>
 `compile_decode_args ce' [build_positional_arg ce' (name,ty)] off
     DLOAD (Lit (n2w data_size)) 0 sa = ((),st')` by gnvs[] >>
 `FLOOKUP ce'.ce_vars name = SOME (PtrVar
   (Var (STRING #"%" (toString st.cs_next_var))) (type_memory_bytes ce' ty))` by simp[FLOOKUP_UPDATE] >>
 `initial.vs_alloca_next + type_memory_bytes ce' ty <= a.vs_alloca_next` by simp[] >>
 `mem_bytes_at 0 (LENGTH encoded) a.vs_data_section = encoded` by
   (qpat_assum `a.vs_data_section = _` (fn th => pure_rewrite_tac[th]) >>
    first_assum ACCEPT_TAC) >>
 drule_all deploy_ctor_decode_constructor_arg_old_prefix_complete >>
 disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
 `type_memory_bytes ce' ty = type_memory_bytes ce ty` by simp[] >>
 ntac 10 (pop_last_assum kall_tac) >>
 qpat_x_assum `abi_decoder_coherent ce _ _ _ _` kall_tac >>
 qpat_x_assum `abi_decoder_metadata ce _ _ _ _ _ _` kall_tac >>
 qpat_x_assum `abi_decoder_coherent ce' _ _ _ _` kall_tac >>
 qpat_x_assum `abi_decoder_metadata ce' _ _ _ _ _ _` kall_tac >>
 qpat_x_assum `mem_bytes_at _ _ a.vs_data_section = _` kall_tac >>
 suspend "finish"
QED

Resume deploy_ctor_register_one_actual_complete[finish]:
 drule compile_alloc_buffer_parts >> strip_tac >>
 `st.cs_next_id <= sa.cs_next_id /\ st.cs_next_var <= sa.cs_next_var` by decide_tac >>
 `sa.cs_next_id <= st'.cs_next_id` by
   (qpat_assum `compile_decode_args ce' [build_positional_arg ce' _] _ _ _ _ _ = _` mp_tac >>
    metis_tac[ctor_decode_args_next_id, pairTheory.SND]) >>
 qexists `actual` >> asm_rewrite_tac[] >>
 conj_tac >- suspend "locals" >>
 conj_tac >- suspend "effect" >>
 conj_tac >- suspend "registers" >>
 conj_tac >- metis_tac[abi_decode_sim_trans] >>
 conj_tac >- suspend "frontier" >>
 suspend "memory"
QED

Resume deploy_ctor_register_one_actual_complete[locals]:
 qpat_assum `ce' = ce with ce_vars := ce.ce_vars |+ (name,PtrVar (Var _) _)`
   (fn th => pure_once_rewrite_tac[th]) >>
 irule ctor_scratch_decode_bind_ptr >>
 conj_tac >- simp[] >>
 qexistsl [`initial.vs_alloca_next`, `entry`, `frag_ids sa st'`, `a`, `sa`,
   `n2w initial.vs_alloca_next : bytes32`] >>
 asm_rewrite_tac[] >>
 `initial.vs_alloca_next < dimword (:256)` by decide_tac >>
 simp[w2n_n2w] >> gnvs[]
QED

Resume deploy_ctor_register_one_actual_complete[effect]:
 irule ctor_registered_alloc_decode_effect >>
 qexistsl [`a`, `st.cs_next_id`, `frag_ids st sa`, `initial.vs_alloca_next`,
   `frag_ids sa st'`, `type_memory_bytes ce' ty`] >>
 asm_rewrite_tac[] >> simp[frag_ids_def, SUBSET_DEF] >> decide_tac
QED

Resume deploy_ctor_register_one_actual_complete[registers]:
 rpt strip_tac >>
 `not_fresh_at sa x` by
   (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 metis_tac[]
QED

Resume deploy_ctor_register_one_actual_complete[frontier]:
 qpat_x_assum `a.vs_alloca_next = initial.vs_alloca_next + _` mp_tac >>
 qpat_x_assum `a.vs_alloca_next <= actual.vs_alloca_next` mp_tac >>
 rpt (pop_last_assum kall_tac) >> decide_tac
QED

Resume deploy_ctor_register_one_actual_complete[memory]:
 `ctor_actual_scratch func (frag_ids sa st') 0 initial.vs_alloca_next actual` by
   (irule ctor_actual_scratch_subregion >>
    qexistsl [`0`, `a.vs_alloca_next`] >> simp[]) >>
 rpt strip_tac >>
 `mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 a.vs_memory` by
   (irule deploy_ctor_actual_registered_memory_prefix >>
    qexistsl [`func`, `frag_ids sa st'`, `[(initial.vs_alloca_next,type_memory_bytes ce' ty)]`,
      `initial.vs_alloca_next`] >> simp[]) >>
 simp[]
QED

Finalise deploy_ctor_register_one_actual_complete

Theorem deploy_ctor_register_suffix_actual_complete:
 !rest k ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial.
 rest = DROP i fargs /\ i <= LENGTH fargs /\
 ALL_DISTINCT (MAP FST rest) /\ LENGTH avs = LENGTH fargs /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 EVERY (\a. ?off. FLOOKUP vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) rest /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) rest /\
 (!j. j < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL j fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL j fargs)) /\
     abi_decoder_coherent ce0 env ce0.ce_struct_fields
       (SND (EL j fargs)) entry.type /\
     abi_decoder_metadata ce0 env (SND (EL j fargs)) entry.type
       (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL j fargs)))
       (EL j avs) entry.value) /\
 compile_register_constructor_args (ce0 with ce_vars := vars)
   (build_positional_args ce0 rest)
   (SUM (MAP abi_member_head_size (TAKE i atys))) data_size st = (ce,st') /\
 local_ptrs_rel func (ce0 with ce_vars := vars) [scope] initial /\ fresh_vars_wrt st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 local_ptrs_rel func ce [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory)
Proof
 Induct >- (rpt gen_tac >> strip_tac >>
   gvs[build_positional_args_def, compile_register_constructor_args_def, comp_return_def] >>
   qexists `initial` >> simp[abi_encoder_registered_effect_refl, abi_decode_sim_refl]) >>
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 PairCases_on `h` >>
 `i < LENGTH fargs` by
   (`LENGTH ((h0,h1)::rest) = LENGTH (DROP i fargs)` by metis_tac[] >>
    fs[LENGTH_DROP] >> decide_tac) >>
 `EL i fargs = (h0,h1) /\ rest = DROP (SUC i) fargs` by
   (qspecl_then [`fargs`, `i`] mp_tac DROP_EL_CONS >>
    (impl_tac >- simp[]) >>
    pure_rewrite_tac[GSYM ADD1] >>
    disch_then (fn th => qpat_assum `_::rest = DROP i fargs`
      (mp_tac o REWRITE_RULE [th])) >> simp[]) >>
 qpat_assum `!j. j < LENGTH fargs ==> _` (qspec_then `i` mp_tac) >>
 (impl_tac >- simp[]) >>
 disch_then (qx_choose_then `entry` (map_every assume_tac o CONJUNCTS)) >>
 qpat_x_assum `!k ce0 vars env fargs avs atys encoded scope i data_size st ce st' ctx func site initial. _`
   (mk_asm "suffix_ih") >>
 qpat_x_assum `EVERY (\a. ?off. _) (_::rest)` mp_tac >>
 SIMP_TAC pure_ss [EVERY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
 qpat_x_assum `EVERY _ (_::rest)` mp_tac >>
 SIMP_TAC pure_ss [EVERY_DEF, pairTheory.FST, pairTheory.SND] >> strip_tac >>
 `FLOOKUP (ce0 with ce_vars := vars).ce_vars h0 =
    SOME (MemLoc off (type_memory_bytes (ce0 with ce_vars := vars) h1))` by simp[] >>
 drule ctor_register_cons >>
 disch_then (fn th => qpat_x_assum `compile_register_constructor_args _ _ _ _ st = _`
   (mp_tac o PURE_REWRITE_RULE [SRULE[] th])) >>
 Cases_on `compile_alloc_buffer (type_memory_bytes ce0 h1) st` >>
 rename1 `compile_alloc_buffer _ st = (buf,sa)` >>
 simp[IgnAsm `atys = _`, IgnAsm `rest = _`, comp_bind_def, comp_ignore_bind_def] >>
 qmatch_goalsub_abbrev_tac `compile_decode_args next _ _ _ _ _` >>
 Cases_on `compile_decode_args next [build_positional_arg ce0 (h0,h1)]
   (SUM (MAP abi_member_head_size (TAKE i atys))) DLOAD (Lit (n2w data_size)) 0 sa` >>
 rename1 `compile_decode_args _ _ _ _ _ _ sa = (u,sd)` >>
 Cases_on `u` >>
 simp[IgnAsm `atys = _`, IgnAsm `rest = _`, comp_bind_def, comp_ignore_bind_def] >>
 strip_tac >>
 drule_all ctor_registration_code_phases >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 drule_all ctor_registration_phi_phases >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 `compile_alloc_buffer (type_memory_bytes (ce0 with ce_vars := vars) h1) st = (buf,sa)` by simp[] >>
 `next = ((ce0 with ce_vars := vars) with ce_vars :=
     ((ce0 with ce_vars := vars).ce_vars |+
     (h0,PtrVar buf.buf_operand (type_memory_bytes (ce0 with ce_vars := vars) h1))))` by
   simp[Abbr `next`] >>
 `lookup_scopes h0 [scope] = SOME entry /\
  type_memory_size entry.type <= type_memory_bytes (ce0 with ce_vars := vars) h1 /\
  abi_decoder_coherent (ce0 with ce_vars := vars) env
    (ce0 with ce_vars := vars).ce_struct_fields h1 entry.type /\
  abi_decoder_metadata (ce0 with ce_vars := vars) env h1 entry.type
    (type_to_abi_dec_info (ce0 with ce_vars := vars).ce_struct_fields
      (ce0 with ce_vars := vars) h1) (EL i avs) entry.value` by
   (qpat_assum `EL i fargs = _` (fn th => fs[th])) >>
 `compile_decode_args next [build_positional_arg (ce0 with ce_vars := vars) (h0,h1)]
   (SUM (MAP abi_member_head_size (TAKE i atys))) DLOAD (Lit (n2w data_size)) 0 sa = ((),sd)` by
   (pure_rewrite_tac[ctor_positional_arg_vars] >> first_assum ACCEPT_TAC) >>
 drule_at (Pat `compile_decode_args _ _ _ _ _ _ _ = _`) deploy_ctor_register_one_actual_complete >>
 disch_then (drule_at (Pat `EL _ _ = _`)) >>
 disch_then (drule_at (Pat `_ = enc _ _`)) >>
 disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
 disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
 disch_then (drule_at (Pat `lookup_scopes _ _ = _`)) >>
 disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >>
 disch_then (qspecl_then [`env`, `off`] mp_tac) >>
 (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
 disch_then (qx_choose_then `middle` (map_every assume_tac o CONJUNCTS)) >>
 suspend "recurse"
QED

Resume deploy_ctor_register_suffix_actual_complete[recurse]:
 `!tys. vyper_to_abi_types env tys = MAP (vyper_to_abi_type env) tys` by
   (Induct >> simp[vyper_to_abi_type_def]) >>
 `LENGTH atys = LENGTH fargs /\ EL i atys = vyper_to_abi_type env h1` by
   simp[MAP_COMPOSE, EL_MAP] >>
 `abi_embedded_static_size ce0.ce_struct_fields h1 = abi_member_head_size (EL i atys)` by
   (drule ctor_coherent_head_size >> simp[]) >>
 `SUM (MAP abi_member_head_size (TAKE (SUC i) atys)) =
   SUM (MAP abi_member_head_size (TAKE i atys)) +
   abi_embedded_static_size ce0.ce_struct_fields h1` by
   (irule EQ_TRANS >> irule_at Any ctor_canonical_offset_step >> simp[]) >>
 `EVERY (\a. ?off. FLOOKUP
    (vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1))) (FST a) =
    SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) rest` by
   (qpat_assum `EVERY (\a. ?off. _) rest` mp_tac >>
    qpat_assum `ALL_DISTINCT (MAP FST (_::rest))` mp_tac >>
    rpt (pop_assum kall_tac) >>
    simp[EVERY_MEM, MEM_MAP, FLOOKUP_UPDATE] >> rpt strip_tac >>
    first_x_assum drule >> strip_tac >>
    `FST a <> h0` by metis_tac[] >> simp[]) >>
 `compile_register_constructor_args
   (ce0 with ce_vars := vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1)))
   (build_positional_args ce0 rest)
   (SUM (MAP abi_member_head_size (TAKE (SUC i) atys))) data_size sd = (ce,st')` by
   (qpat_assum `compile_register_constructor_args next _ _ _ sd = _` mp_tac >>
    qpat_assum `SUM (MAP abi_member_head_size (TAKE (SUC i) atys)) = _`
      (fn th => pure_rewrite_tac[th]) >>
    simp[Abbr `next`, NoAsms]) >>
 `local_ptrs_rel func
   (ce0 with ce_vars := vars |+ (h0,PtrVar buf.buf_operand (type_memory_bytes ce0 h1)))
   [scope] middle` by
   (qpat_assum `local_ptrs_rel func next _ middle` mp_tac >> simp[Abbr `next`, NoAsms]) >>
 `mem_bytes_at 0 (LENGTH encoded) middle.vs_data_section = encoded` by
   (qpat_assum `middle.vs_data_section = _` (fn th => pure_rewrite_tac[th]) >>
    first_assum ACCEPT_TAC) >>
 `ALL_DISTINCT (MAP FST rest)` by
   (qpat_assum `ALL_DISTINCT (MAP FST (_::rest))` mp_tac >>
    rpt (pop_assum kall_tac) >> simp[MAP, ALL_DISTINCT]) >>
 asm "suffix_ih" (drule_at (Pat `compile_register_constructor_args _ _ _ _ _ = _`)) >>
 disch_then (drule_at (Pat `_ = DROP _ _`)) >>
 disch_then (drule_at (Pat `_ = enc _ _`)) >>
 disch_then (drule_at (Pat `local_ptrs_rel _ _ _ _`)) >>
 disch_then (drule_at (Pat `alloca_frontier_inv_from _ _ _ _ _`)) >>
 disch_then (qspec_then `env` mp_tac) >>
 (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
 disch_then (qx_choose_then `actual` (map_every assume_tac o CONJUNCTS)) >>
 asm_x "suffix_ih" kall_tac >>
 qexists `actual` >> asm_rewrite_tac[] >>
 conj_tac >- suspend "suffix_effect" >>
 conj_tac >- suspend "suffix_registers" >>
 conj_tac >- metis_tac[abi_decode_sim_trans] >>
 conj_tac >- suspend "frontier" >>
 suspend "memory"
QED

Resume deploy_ctor_register_suffix_actual_complete[suffix_effect]:
 `st.cs_next_id <= sd.cs_next_id` by
   (drule compile_alloc_buffer_parts >> strip_tac >>
    `sa.cs_next_id <= sd.cs_next_id` by
      metis_tac[ctor_decode_args_next_id, pairTheory.SND] >> decide_tac) >>
 `sd.cs_next_id <= st'.cs_next_id` by metis_tac[ctor_registration_next_id] >>
 `frag_ids st sd SUBSET frag_ids st st'` by
   (simp[frag_ids_def, SUBSET_DEF] >> decide_tac) >>
 irule abi_encoder_registered_effect_trans >> qexists `middle` >> conj_tac
 >- (irule abi_encoder_registered_effect_enlarge >>
     qexistsl [`frag_ids st sd`, `[]:(num#num) list`] >> simp[]) >>
 irule abi_encoder_registered_effect_enlarge >>
 qexistsl [`frag_ids sd st'`, `[]:(num#num) list`] >> simp[]
QED

Resume deploy_ctor_register_suffix_actual_complete[suffix_registers]:
 `st.cs_next_var <= sd.cs_next_var` by
   (drule compile_alloc_buffer_parts >> strip_tac >>
    `sa.cs_next_var <= sd.cs_next_var` by
      metis_tac[ctor_decode_args_vars_mono, abi_decoder_vars_mono_def, pairTheory.SND] >>
    decide_tac) >>
 rpt strip_tac >>
 `not_fresh_at sd x` by
   (fs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
 metis_tac[]
QED

Resume deploy_ctor_register_suffix_actual_complete[frontier]:
 qpat_x_assum `initial.vs_alloca_next <= middle.vs_alloca_next` mp_tac >>
 qpat_x_assum `middle.vs_alloca_next <= actual.vs_alloca_next` mp_tac >>
 rpt (pop_last_assum kall_tac) >> decide_tac
QED

Resume deploy_ctor_register_suffix_actual_complete[memory]:
 rpt strip_tac >>
 `p < middle.vs_alloca_next` by
   (qpat_x_assum `initial.vs_alloca_next <= middle.vs_alloca_next` mp_tac >>
    qpat_assum `p < initial.vs_alloca_next` mp_tac >>
    rpt (pop_last_assum kall_tac) >> decide_tac) >>
 metis_tac[]
QED

Finalise deploy_ctor_register_suffix_actual_complete

Theorem deploy_ctor_register_args_actual_complete:
 !k ce0 env fargs avs atys encoded scope data_size st ce st' ctx func site initial.
 ALL_DISTINCT (MAP FST fargs) /\ LENGTH avs = LENGTH fargs /\
 atys = vyper_to_abi_types env (MAP SND fargs) /\ has_types atys avs /\
 encoded = enc (Tuple atys) (ListV avs) /\
 LENGTH encoded < dimword (:256) /\
 mem_bytes_at 0 (LENGTH encoded) initial.vs_data_section = encoded /\
 (data_size = 0 \/ LENGTH encoded <= data_size /\ data_size < dimword (:256)) /\
 EVERY (\a. ?off. FLOOKUP ce0.ce_vars (FST a) =
   SOME (MemLoc off (type_memory_bytes ce0 (SND a)))) fargs /\
 EVERY (\a. type_memory_bytes ce0 (SND a) < dimword (:256)) fargs /\
 (!i. i < LENGTH fargs ==>
   ?entry. lookup_scopes (FST (EL i fargs)) [scope] = SOME entry /\
     val_wf entry.type entry.value /\
     type_memory_size entry.type <= type_memory_bytes ce0 (SND (EL i fargs)) /\
     abi_decoder_coherent ce0 env ce0.ce_struct_fields
       (SND (EL i fargs)) entry.type /\
     abi_decoder_metadata ce0 env (SND (EL i fargs)) entry.type
       (type_to_abi_dec_info ce0.ce_struct_fields ce0 (SND (EL i fargs)))
       (EL i avs) entry.value) /\
 compile_register_constructor_args ce0 (build_positional_args ce0 fargs)
   0 data_size st = (ce,st') /\
 local_ptrs_rel func ce0 [scope] initial /\ fresh_vars_wrt st initial /\
 fn_has_code st st' func /\ fn_inst_ids_distinct func /\
 (st.cs_blocks = st'.cs_blocks \/
   !bb. lookup_block st'.cs_current_bb func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0) /\
 alloca_inv initial /\ alloca_frontier_inv_from k ctx func site initial /\
 k + unit_alloca_budget ctx < dimword (:256) /\
 (!aid. st.cs_next_id <= aid ==> FLOOKUP initial.vs_allocas aid = NONE) /\
 ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
 initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
 ?actual.
 local_ptrs_rel func ce [scope] actual /\
 abi_encoder_registered_effect (frag_ids st st') [] initial actual /\
 alloca_inv actual /\ alloca_frontier_inv_from k ctx func site actual /\
 fresh_vars_wrt st' actual /\
 (!aid. st'.cs_next_id <= aid ==> FLOOKUP actual.vs_allocas aid = NONE) /\
 actual.vs_data_section = initial.vs_data_section /\
 actual.vs_call_ctx = initial.vs_call_ctx /\ actual.vs_labels = initial.vs_labels /\
 (!x w. not_fresh_at st x /\ lookup_var x initial = SOME w ==>
   lookup_var x actual = SOME w) /\
 ~actual.vs_halted /\ actual.vs_current_bb = st'.cs_current_bb /\
 actual.vs_inst_idx = LENGTH st'.cs_current_insts /\
 abi_decode_sim ctx func initial actual /\
 actual.vs_gas_readings = initial.vs_gas_readings /\ actual.vs_code = initial.vs_code /\
 actual.vs_outcomes = initial.vs_outcomes /\ actual.vs_tx_ctx = initial.vs_tx_ctx /\
 actual.vs_block_ctx = initial.vs_block_ctx /\
 initial.vs_alloca_next <= actual.vs_alloca_next /\
 (!p. p < initial.vs_alloca_next ==>
   mem_bytes_at p 1 actual.vs_memory = mem_bytes_at p 1 initial.vs_memory)
Proof
 rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
 irule deploy_ctor_register_suffix_actual_complete >> asm_rewrite_tac[] >>
 qexistsl [`atys`, `avs`, `ce0`, `data_size`, `encoded`, `env`, `fargs`, `0`, `fargs`,
   `ce0.ce_vars`] >> simp[]
QED
