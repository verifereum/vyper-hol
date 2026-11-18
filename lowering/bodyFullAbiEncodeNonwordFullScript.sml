Theory bodyFullAbiEncodeNonwordFull
Ancestors exprSimAbiEncodeStateTransport[qualified,ignore_grammar] abiBuiltinEncodeSource[qualified,ignore_grammar]
  bodyFullIntCallReturnFrame[qualified,ignore_grammar]
  bodyFullPreds bodySimFull bodyInvNoDalloca bodyFullAbiEncodeArgStep
  bodyFullAbiEncodeSetupTail bodyFullAbiEncodeFinish bodyFullAbiEncodeAllocOrigin
  bodyFullAbiEncodeSuffix bodyFullAbiEncodeUniformTranslation
  exprSimAbiEncodeNonwordCase exprSimAbiEncodeRuntimeInputs
  exprSimAbiEncodeNonwordResources exprSimAbiEncodeCapacity
  exprSimAbiEncodeNonwordResult bodyFullAbiEncodeReadResources
  exprSimIfExpWidenedPhysicalType bodyFullAbiEncodeNonwordWindow
  abiEncodeMaterialize valueCopyBytes bodyFullAbiEncodeSetupSourceFrame
  exprSimHyps exprSimSource gasOutcomeFullCompose gasShadowCompile
  gasShadowCompileStmtHelpers exprLowering compileEnv
  bodyFullAbiEncodeNonwordReady bodyFullAbiEncodeReadyFinish
  bodyFullAbiEncodeResultResources

Theorem abi_encode_nonword_vv_full_from_packaging:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode F mid) ty [e]) es /\
  body_expr_full_ok cx e /\ ~is_word_type (expr_type e)
  ==> expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        ce cx cty (TypeBuiltin ann (AbiEncode F mid) ty [e]) es
Proof
  strip_tac >>
  `~ctx_has_dalloca ctx` by metis_tac[body_inv_no_dalloca] >>
  `expr_body_pre ce cx env e es` by
    (irule abi_encode_body_arg_pre >> goal_assum (drule_at Any) >> simp[]) >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr ce cty (TypeBuiltin ann _ _ _) sa = _` mp_tac >>
  simp[compile_abi_encode_nonword_shape] >>
  pairarg_tac >> rename1 `lower_value _ _ _ _ sa = (op,sm)` >>
  simp[] >> simp[as_ptr_val_def] >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) op
    (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
    (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) sm` >>
  rename1 `lower_abi_encode _ _ _ _ _ sm = (out,sn)` >>
  simp[as_ptr_val_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `lower_value _ _ _ e sa = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >> pairarg_tac >>
  rename1 `compile_expr ce (expr_type e) e sa = (vv,si)` >>
  strip_tac >> gvs[] >>
  mp_tac (Q.INST [`cenv` |-> `ce`, `ty` |-> `expr_type e`]
    gas_shadow_stmt_compile_expr) >>
  rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  gvs[] >> rename1 `gas_shadow_state si shadow_si` >>
  rename1 `compile_expr ce (expr_type e) e sa = (vv,si)` >>
  mp_tac (Q.INST [`cenv` |-> `ce`] gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value) >>
  rewrite_tac[gasShadowStateTheory.gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`si`,`shadow_si`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `unwrap_value ce vv shadow_si` >> gvs[] >>
  rename1 `gas_shadow_state sm shadow_sm` >>
  qpat_x_assum `compile_expr ce cty (gas_shadow_expr _) shadow_sa = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def, compile_abi_encode_nonword_shape,
    gasShadowTheory.gas_shadow_expr_type,
    lower_value_def, comp_bind_def, as_ptr_val_def] >>
  Cases_on `lower_abi_encode F (OPTION_MAP bytes_method_id_word mid) op
    (type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e))
    (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)) shadow_sm` >>
  simp[as_ptr_val_def, contextTheory.mk_ptr_def] >> strip_tac >> gvs[] >>
  rename1 `fn_has_code shadow_sa shadow_sb shadow_func` >>
  `cs_extends sa si /\ cs_extends shadow_sa shadow_si` by
    metis_tac[exprSimUnwrapTheory.compile_expr_extends] >>
  `cs_extends si sm /\ cs_extends shadow_si shadow_sm` by
    metis_tac[exprSimUnwrapTheory.unwrap_value_extends] >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[cs_extends_trans] >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    metis_tac[abiBuiltinEncodeWordTheory.lower_abi_encode_extends] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  mp_tac (Q.INST [`rest` |-> `[]`, `mid` |-> `si`, `sb` |-> `sm`,
    `shadow_mid` |-> `shadow_si`, `shadow_sb` |-> `shadow_sm`]
    abi_encode_arg_step_full) >>
  simp[expr_can_mutate_def] >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  simp[eval_expr_singleton_type_builtin_action,
    vyperContextTheory.type_builtin_args_length_ok_def] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
      cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
      vyperStorageTraceTheory.storage_trace_frame_read_result]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_def]
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_value >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
      first_assum ACCEPT_TAC) >>
  qexists `childQ` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >> first_assum (irule_at Any) >>
      simp[Abbr `childR`] >> rpt strip_tac >>
      Cases_on `res` >- gvs[exprSimDefsTheory.expr_exit_def] >>
      qexists `y` >> Cases_on `r` >> Cases_on `y` >>
      gvs[exprSimDefsTheory.expr_exit_def, exprSimDefsTheory.halt_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >>
      gvs[exprSimDefsTheory.expr_exit_def]) >>
  map_every qx_gen_tac [`marks`,`res`,`ee`,`G1`,`tn1`,`s`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> childQ _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp_tac bool_ss [Abbr `childQ`] >> strip_tac >> gvs[] >>
  `lower_value compile_expr ce (expr_type e) e sa = (op,sm)` by
    simp[lower_value_def, comp_bind_def] >>
  `fn_has_code sm sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0` by
    (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ _ es.storage_trace ==> _ /\ _`
       drule >> simp[]) >>
  drule_all (REWRITE_RULE [] (Q.INST [
    `midw` |-> `OPTION_MAP bytes_method_id_word mid`,
    `ei` |-> `type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e)`,
    `maxlen` |-> `abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)`,
    `k` |-> `(case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4)`,
    `mw` |-> `(case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 32)`,
    `N` |-> `32 + 32 * word_size (abi_size_bound ce.ce_struct_fields (lowered_value_type ce e) +
           (case OPTION_MAP bytes_method_id_word mid of NONE => 0 | SOME _ => 4))`,
    `cap` |-> `val_footprint tv v`] abi_encode_nonword_ready_origin)) >>
  disch_then (qspecl_then [`shadow_ctx`, `PG`] strip_assume_tac) >>
  rename1 `gas_origin_ptr_path _ (s,G1,tn1) [] (OK u,Gu,tnu)` >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee u` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel H _ _ _ _ ee u /\ _`
       drule >> simp[]) >>
  drule_then strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >>
  suspend "protect_ready"
QED

Resume abi_encode_nonword_vv_full_from_packaging[protect_ready]:
  qabbrev_tac `midw = OPTION_MAP bytes_method_id_word mid` >>
  qabbrev_tac `maxlen = abi_size_bound ce.ce_struct_fields (lowered_value_type ce e)` >>
  qabbrev_tac `ei = type_to_abi_enc_info ce.ce_struct_fields ce (lowered_value_type ce e)` >>
  qabbrev_tac `selector = abi_builtin_encode_prefix midw` >>
  `LENGTH selector = (case midw of NONE => 0 | SOME _ => 4)` by
    (Cases_on `midw` >> simp[Abbr `selector`, abiBuiltinEncodeRunTheory.abi_builtin_encode_prefix_def,
       abiBuiltinEncodeMethodTheory.abi_builtin_encode_method_bytes_length]) >>
  qpat_assum `LENGTH selector = _` (fn th => rule_assum_tac (PURE_REWRITE_RULE [SYM th])) >>
  qabbrev_tac `N = 32 + 32 * word_size (maxlen + LENGTH selector)` >>
  `32 <= N` by simp[Abbr `N`] >>
  `p + 32 + LENGTH selector + LENGTH (enc ct rv) <= u.vs_alloca_next /\
   LENGTH (enc ct rv) + LENGTH selector < dimword (:256)` by decide_tac >>
  `lo <= u.vs_alloca_next` by decide_tac >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     disch_then (mp_tac o MATCH_MP stmtSimDefsTheory.eval_read_preserves_scopes_dom) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[vyperStorageTraceTheory.storage_trace_frame_bind,
         cj 5 vyperStorageTraceTheory.evaluate_storage_trace_frame,
         vyperStorageTraceTheory.storage_trace_frame_read_result] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     drule_at (Pat `f st = (res,st')`) vyperStorageFootprintTheory.valid_horizon_frame >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx es s0` by simp[] >>
  `!n b sz. local_region ce es.scopes s0 n b sz <=> local_region ce ee.scopes u n b sz` by
    metis_tac[wordArgsPtrTheory.wb_frame_local_regions] >>
  qabbrev_tac `sites = window_alloca_sites func (frag_ids ready body_end)` >>
  `sm.cs_next_id < ready.cs_next_id` by
    (drule (cj 1 abiBuiltinEncodeCodeTheory.abi_builtin_encode_setup_shape) >>
     Cases_on `midw` >> simp_tac bool_ss [optionTheory.option_case_def] >> decide_tac) >>
  `!id. id IN sites ==> ready.cs_next_id <= id` by
    (rpt strip_tac >>
     `id IN frag_ids ready body_end` by
       (qpat_x_assum `id IN sites` mp_tac >> simp_tac bool_ss [Abbr `sites`] >>
        metis_tac[abiEncoderWindowContractTheory.window_alloca_sites_subset,
                  pred_setTheory.SUBSET_DEF]) >>
     pop_assum mp_tac >>
     simp_tac bool_ss [abiEncoderPropsTheory.frag_ids_def,
       pred_setTheory.GSPECIFICATION, pairTheory.PAIR_EQ]) >>
  `!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,sz) ==>
       !n q k. local_region ce ee.scopes u n q k ==> regions_disjoint b sz q k` by
    (map_every qx_gen_tac [`id`, `b`, `sz`] >> strip_tac >>
     `?inst. MEM inst (fn_insts func) /\ inst.inst_id = id /\ inst.inst_opcode = ALLOCA /\
        inst.inst_id IN frag_ids ready body_end` by
       (qpat_assum `id IN sites` mp_tac >>
        simp_tac bool_ss [Abbr `sites`, abiEncoderWindowContractTheory.window_alloca_sites_def,
                          pred_setTheory.GSPECIFICATION, pairTheory.PAIR_EQ] >>
        strip_tac >> goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
     drule_all_then strip_assume_tac externalReturnEncoderSitesTheory.encoder_function_alloca_shape >>
     `not_local_ptr ce ee.scopes q` by (irule exprSimOperandsTheory.fresh_not_local_ptr >>
       qexists `ready` >> asm_rewrite_tac[]) >>
     rpt strip_tac >> irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`ce`,`func`,`inst`,`n`,`q`,`ee.scopes`,`u`] >> asm_rewrite_tac[]) >>
  `ci_mono sa sm` by
    (qpat_assum `lower_value _ _ _ _ sa = _` (fn th =>
       mp_tac (Q.SPECL [`ce`,`expr_type e`,`e`,`sa`]
         (cj 2 stmtLoweringMonoTheory.ci_mono_compile_expr_sa)) >> simp[th])) >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (qpat_assum `ci_mono sa sm` mp_tac >> metis_tac[exprLoweringPropsTheory.ci_mono_def]) >>
  `!i b sz. i IN sites /\ FLOOKUP u.vs_allocas i = SOME (b,sz) ==>
    regions_disjoint p N b sz` by
    (rpt strip_tac >> `i <> sm.cs_next_id` by
       (qpat_assum `!id. id IN sites ==> _` drule >> decide_tac) >>
     rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
     irule (Q.INST [`s` |-> `u`, `live` |-> `sm.cs_next_id`, `site` |-> `i`]
       abiCallerAllocationTheory.abi_caller_allocation_separate) >>
     qexistsl_tac [`i`,`sm`,`u`] >> asm_rewrite_tac[] >> metis_tac[]) >>
  qabbrev_tac `P = {i | i < u.vs_alloca_next /\
      (i < p+32+LENGTH selector \/ p+32+LENGTH selector+LENGTH (enc ct rv) <= i) /\
      (!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,sz) ==>
          i < b \/ b+sz <= i)}` >>
  `!i. i IN P <=> i < u.vs_alloca_next /\
      (i < p+32+LENGTH selector \/ p+32+LENGTH selector+LENGTH (enc ct rv) <= i) /\
      (!id b sz. id IN sites /\ FLOOKUP u.vs_allocas id = SOME (b,sz) ==>
          i < b \/ b+sz <= i)` by
    simp_tac bool_ss [Abbr `P`, pred_setTheory.GSPECIFICATION, pairTheory.PAIR_EQ] >>
  `!name b sz i. local_region ce ee.scopes u name b sz /\ b <= i /\ i < b+sz ==> i IN P` by
    (rpt strip_tac >>
     `b+sz <= u.vs_alloca_next` by
       drule_all_then ACCEPT_TAC bodyMemoryDefsTheory.body_local_region_frontier >>
     qpat_assum `!n b sz. local_region ce ee.scopes u n b sz ==> regions_disjoint p N b sz`
       (drule_then (assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
     qpat_assum `!i. i IN P <=> _` (fn th => rewrite_tac[th]) >>
     conj_tac >- decide_tac >> conj_tac >- decide_tac >>
     map_every qx_gen_tac [`id`,`q`,`k`] >> strip_tac >>
     `regions_disjoint q k b sz` by metis_tac[] >>
     qpat_assum `regions_disjoint q k b sz`
       (assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >>
     decide_tac) >>
  `!name b sz i. local_region ce es.scopes s0 name b sz /\ b <= i /\ i < b+sz ==> i IN P` by
    metis_tac[] >>
  `!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row` by
    (qpat_assum `wb_frame ce es ee sa s0 u`
       (ACCEPT_TAC o cj 2 o REWRITE_RULE [loweringPostsTheory.wb_frame_def])) >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    off <= i /\ i < off+sz ==> i IN P /\ (i < p \/ p+32 <= i)` by
    (map_every qx_gen_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
     `off+sz <= u.vs_alloca_next` by
       (irule abiCallerAllocationTheory.abi_caller_allocation_end >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [`sz`,`aid`,`off`] >> rewrite_tac[arithmeticTheory.LESS_EQ_REFL] >>
        first_assum ACCEPT_TAC) >>
     `aid <> sm.cs_next_id` by decide_tac >>
     `off+sz <= p \/ p+N <= off` by
       metis_tac[abiCallerAllocationTheory.abi_caller_allocation_separate] >>
     qpat_assum `!i. i IN P <=> _` (fn th => rewrite_tac[th]) >>
     (conj_tac >-
        (conj_tac >- decide_tac >> conj_tac >- decide_tac >>
         map_every qx_gen_tac [`id`,`b`,`k`] >> strip_tac >>
         `aid <> id` by (qpat_assum `!id. id IN sites ==> _` drule >> decide_tac) >>
         `off+sz <= b \/ b+k <= off` by
           metis_tac[abiCallerAllocationTheory.abi_caller_allocation_separate] >>
         decide_tac) >> decide_tac)) >>
  `!i. i < lo ==> i IN P` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i IN P <=> _` (fn th => rewrite_tac[th]) >>
     conj_tac >- decide_tac >> conj_tac >- decide_tac >>
     rpt strip_tac >>
     `lo <= b` by metis_tac[ptrDisciplineTheory.allocas_from_def] >> decide_tac) >>
  `!i. p+32 <= i /\ i < p+32+LENGTH selector ==> i IN P` by
    (gen_tac >> strip_tac >>
     qpat_assum `!i. i IN P <=> _` (fn th => rewrite_tac[th]) >>
     conj_tac >- decide_tac >> conj_tac >- decide_tac >>
     map_every qx_gen_tac [`id`,`b`,`k`] >> strip_tac >>
     `regions_disjoint p N b k` by metis_tac[] >>
     qpat_assum `regions_disjoint p N b k`
       (assume_tac o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]) >>
     decide_tac) >>
  suspend "finish_ready"
QED

Resume abi_encode_nonword_vv_full_from_packaging[finish_ready]:
  `abi_encoder_admissible ei` by
    simp[Abbr `ei`, abiEncoderAdmissibleTheory.abi_encoder_translation_admissible] >>
  `op_taint tnu (Var dp) = {} /\
   (0 < LENGTH (enc ct rv) ==> ptr_covers Gu tnu dp u (LENGTH (enc ct rv)))` by
    (qpat_assum `ptr_covers Gu tnu dp u maxlen` (fn th =>
       conj_tac >- ACCEPT_TAC (cj 1 (REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def] th)) >>
       strip_tac >> irule (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
         reasonCopySourcePtrTheory.ptr_covers_mono) th) >> first_assum ACCEPT_TAC)) >>
  `lookup_var root u = SOME (n2w p) /\ p < dimword(:256)` by
    (conj_tac >- (rewrite_tac[GSYM (cj 2 venomStateTheory.eval_operand_def)] >>
                  first_assum ACCEPT_TAC) >> decide_tac) >>
  `!name b sz. local_region ce ee.scopes u name b sz ==> regions_disjoint p 32 b sz` by
    (rpt strip_tac >>
     qpat_assum `!name b sz. local_region ce ee.scopes u name b sz ==> _`
       (drule_then (assume_tac o REWRITE_RULE[loweringStateRelDefsTheory.regions_disjoint_def])) >>
     rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at ready x` by metis_tac[] >>
  `!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at ready x` by metis_tac[] >>
  `!mem. mem_agree_outside tnu.t_mem u.vs_memory mem ==>
      mem_bytes_at (p+32) (LENGTH selector) mem = selector` by
    (gen_tac >> strip_tac >>
     qpat_assum `Abbrev (selector = _)`
       (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     Cases_on `midw`
     >- simp_tac (srw_ss()) [abiBuiltinEncodeRunTheory.abi_builtin_encode_prefix_def,
          valueEncodingDefsTheory.mem_bytes_at_def] >>
     qpat_assum `case SOME _ of NONE => T | SOME _ => _`
       (drule_then (fn th =>
          simp_tac (srw_ss()) [abiBuiltinEncodeRunTheory.abi_builtin_encode_prefix_def,
            exprSimConvertBytesTheory.convert_mem_word_prefix,
            abiBuiltinEncodeMethodTheory.abi_builtin_encode_method_bytes_length,
            abiBuiltinEncodeMethodTheory.abi_builtin_encode_method_bytes_def,
            byteTheory.word_to_bytes_be_def, th]) o
        SIMP_RULE std_ss [optionTheory.option_case_def])) >>
  `!i. i IN P ==> i < u.vs_alloca_next /\
      (i < p+32+LENGTH selector \/ p+32+LENGTH selector+LENGTH (enc ct rv) <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids ready body_end) /\
        FLOOKUP u.vs_allocas id = SOME (b,sz) ==> i < b \/ b+sz <= i)` by
    (qpat_assum `Abbrev (sites = _)` (fn th =>
       qpat_assum `!i. i IN P <=> _`
         (fn h => rewrite_tac[REWRITE_RULE[REWRITE_RULE[markerTheory.Abbrev_def] th] h])) >>
     simp_tac bool_ss []) >>
  `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b sz'. local_region ce es.scopes s0 n b sz' ==> off+sz <= b \/ b+sz' <= off) /\
      off <= i /\ i < off+sz ==> i IN P` by metis_tac[] >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id IN frag_ids ready body_end /\ FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz)
      ==> sz = 32 /\ (0 < val_footprint tv v ==> venomMemDefs$regions_disjoint (src,val_footprint tv v) (b,sz)) /\
          venomMemDefs$regions_disjoint (p+32+LENGTH selector,LENGTH (enc ct rv)) (b,sz)` by metis_tac[] >>
  drule abi_encode_ready_finish_origin_split >>
  disch_then (fn th =>
    qpat_assum `abi_builtin_encode_finish _ len _ body_end = _`
      (mp_tac o MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] th))) >>
  disch_then (qspecl_then [`tn0`,`tnu`,`sm.cs_next_id`,`src`,`sa`,`s0`,`u`,
    `d`,`p`,`lo`,`func`,`gas_explicit_sites ctx shadow_ctx`,`es`,`ee`,`maxlen`,
    `cx`,`ctx`,`ce`,`val_footprint tv v`,`rv`,`ct`,`PG`,`P`,`N`,`G0`,`Gu`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tnf`
    (qx_choose_then `cut` (qx_choose_then `Gcut` (qx_choose_then `tncut`
      strip_assume_tac)))))) >>
  `!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (s,G1,tn1) [] (OK t,Gf,tnf)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`u`,`tnu`] >> metis_tac[]) >>
  drule_all_then assume_tac abi_encode_nonword_source_result >>
  drule_all_then strip_assume_tac abi_encode_nonword_result_bound >>
  qmatch_asmsub_abbrev_tac `evaluate_type_builtin _ _ _ _ _ = INL (BytesV payload)` >>
  rename1 `expr_type (TypeBuiltin ann (AbiEncode F mid) ty [e]) = BaseT (BytesT (Dynamic limit))` >>
  `well_typed_type_builtin_args (AbiEncode F mid) ty [expr_type e]` by
    (qpat_assum `expr_body_pre ce cx env (TypeBuiltin ann _ _ _) es` mp_tac >>
     simp[NoAsms, exprSimHypsDefsTheory.expr_body_pre_def,
       Once vyperTypeSystemTheory.well_typed_expr_def]) >>
  `selector = abi_encode_method_id_bytes mid` by
    (simp[Abbr `selector`, Abbr `midw`, abiBuiltinEncodeSourceTheory.abi_builtin_encode_checked_prefix] >> (metis_tac[Abbr `selector`, Abbr `midw`, abiBuiltinEncodeSourceTheory.abi_builtin_encode_checked_prefix])) >>
  `payload = selector ++ enc ct rv` by simp[Abbr `payload`] >>
  `LENGTH payload <= limit` by simp[Abbr `payload`] >>
  `LENGTH payload <= maxlen + LENGTH selector /\ 32 + LENGTH payload <= N` by
    (qpat_assum `payload = selector ++ _` (fn th => rewrite_tac[th, listTheory.LENGTH_APPEND]) >>
     decide_tac) >>
  `!mem. mem_agree_outside tnf.t_mem t.vs_memory mem ==>
        val_in_memory (BaseTV (BytesT (Dynamic limit))) (BytesV payload) p mem` by
    (qx_gen_tac `mem` >> strip_tac >>
     qpat_assum `!mem. _ ==> mem_word_at p mem = _ /\ _`
       (qspec_then `mem` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     strip_tac >>
     qpat_assum `payload = selector ++ _` (fn th =>
       simp_tac (srw_ss()) [th, valueEncodingDefsTheory.val_in_memory_def,
         listTheory.LENGTH_APPEND]) >>
     conj_tac
     >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_assum ACCEPT_TAC) >>
     once_rewrite_tac[valueEncodingProofsTheory.mem_bytes_at_split_padded] >>
     qpat_assum `mem_bytes_at (p+32) (LENGTH selector) mem = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `mem_bytes_at (p+32+LENGTH selector) _ mem = _` (fn th => rewrite_tac[th])) >>
  `p + N <= t.vs_alloca_next` by
    (irule abiEncoderWindowContractTheory.window_alloca_growth_frontier >>
     qexists_tac `u` >> asm_rewrite_tac[]) >>
  `s0.vs_alloca_next <= t.vs_alloca_next` by
    (drule_then (assume_tac o cj 1) (iffLR abiEncoderWindowContractTheory.window_alloca_growth_def) >>
     decide_tac) >>
  `type_memory_bytes ce (lowered_value_type ce (TypeBuiltin ann (AbiEncode F mid) ty [e])) = N` by
    (`LENGTH selector = if IS_SOME mid then 4 else 0` by
       (qpat_assum `Abbrev (selector = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        qpat_assum `Abbrev (midw = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        Cases_on `mid` >> simp_tac (srw_ss()) [abiBuiltinEncodeRunTheory.abi_builtin_encode_prefix_def,
          abiBuiltinEncodeMethodTheory.abi_builtin_encode_method_bytes_length]) >>
     qpat_assum `Abbrev (N = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `Abbrev (maxlen = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `LENGTH selector = if _ then _ else _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [Once exprLoweringTheory.lowered_value_type_def, LET_THM,
       compileEnvTheory.type_memory_bytes_def, vfmConstantsTheory.word_size_def,
       arithmeticTheory.MULT_COMM]) >>
  `val_store_size (BaseTV (BytesT (Dynamic limit))) (BytesV payload) <= N` by
    (`word_size (LENGTH payload) <= word_size (maxlen + LENGTH selector)` by
       simp[exprSimPropsTheory.word_size_monotone] >>
     simp_tac (srw_ss()) [exprSimPropsTheory.val_store_size_def, Abbr `N`] >> decide_tac) >>
  `eval_operand (Var root) t = SOME (n2w p)` by
    (rewrite_tac[venomStateTheory.eval_operand_def] >> first_assum ACCEPT_TAC) >>
  `w2n (n2w p : 256 word) = p` by
    (qpat_assum `p < dimword(:256)` (fn th => simp_tac std_ss [wordsTheory.w2n_n2w, th])) >>
  mp_tac (Q.INST [`s` |-> `t`, `q` |-> `root`, `capacity` |-> `N`,
    `w` |-> `(n2w p : 256 word)`, `G` |-> `Gf`, `tn` |-> `tnf`,
    `N` |-> `limit`, `ann` |-> `ann`, `ensure` |-> `F`, `target` |-> `ty`,
    `args` |-> `[e]`, `mid` |-> `mid`, `ce` |-> `ce`, `cx` |-> `cx`,
    `ee` |-> `ee`, `payload` |-> `payload`] abi_encode_bytes_full_resources) >>
  (impl_tac >-
     (qpat_assum `w2n (n2w p : 256 word) = p` (fn th => rewrite_tac[th]) >>
      qpat_assum `type_memory_bytes ce (lowered_value_type ce (TypeBuiltin ann _ _ _)) = N`
        (fn th => rewrite_tac[th, arithmeticTheory.LESS_EQ_REFL]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  irule gas_outcome_full_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gf`,`ee`,`INL (Value (BytesV payload))`,`t`,`tnf`] >>
  conj_tac >- (qpat_assum `evaluate_type_builtin _ _ _ _ _ = INL (BytesV payload)`
    (fn th => simp_tac (srw_ss()) [th])) >>
  qx_gen_tac `H` >> strip_tac >>
  conj_tac >- (qpat_assum `!D. gas_origin_ptr_path _ (s,G1,tn1) [] (OK t,Gf,tnf)`
    (qspec_then `DF H` ACCEPT_TAC)) >>
  `ghost_inv_at (DF H) lo d ce cx (ee with gas_obs := []) Gf tnf t` by
    (qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel H _ _ _ _ ee u /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!D. ghost_inv_at D _ _ _ _ ee Gu tnu u ==> _`
       (qspec_then `DF H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     simp_tac (srw_ss()) [bodyPtrDefsTheory.ghost_inv_at_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  BETA_TAC >> qexists_tac `Value (BytesV payload)` >>
  qpat_assum `out = Var root` SUBST1_TAC >>
  conj_tac >- REFL_TAC >>
  reverse conj_tac >-
    (rewrite_tac[GSYM contextTheory.mk_ptr_def] >>
     conj_tac >-
       (qpat_assum `vv_store_bound _ _ _ ee _ _ t` mp_tac >>
        simp_tac (srw_ss()) [exprSimMemDefsTheory.vv_store_bound_def,
          loweringPostsTheory.post_value_type_def, vyperStateTheory.read_result_def,
          vyperStateTheory.return_def]) >>
     ntac 5 (conj_tac >- simp[]) >>
     conj_tac >-
       (qpat_assum `ptr_vv_ok _ _ _ _ ee Gf tnf t` mp_tac >>
        simp_tac (srw_ss()) [bodyPtrDefsTheory.ptr_vv_ok_def,
          loweringPostsTheory.post_value_type_def, vyperStateTheory.read_result_def,
          vyperStateTheory.return_def]) >>
     conj_tac >-
       (qpat_assum `expr_type (TypeBuiltin ann _ _ _) = _` (fn th =>
          simp_tac (srw_ss()) [th, compileEnvTheory.is_bytestring_type_def])) >>
     conj_tac >-
       simp_tac (srw_ss()) [contextTheory.vv_location_def, contextTheory.mk_ptr_def] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "value_post"
QED

Resume abi_encode_nonword_vv_full_from_packaging[value_post]:
  irule exprSimHashTheory.vv_post_pointer_cong >>
  qexists_tac `<|ptr_operand := Var root; ptr_location := LocMemory|>` >>
  simp_tac (srw_ss()) [] >>
  irule (REWRITE_RULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `TypeBuiltin ann (AbiEncode F mid) ty [e]`,
             `result` |-> `Value (BytesV payload)`] abi_encode_bytes_vv_post)) >>
  conj_tac >- rewrite_tac[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  `storage_well_formed_on cx (ee with gas_obs := []) (FST H)` by
    (qpat_assum `!h. valid_horizon _ _ h ee.storage_trace ==> expr_post h ctx func ce cx e es sa sm s0 ee v op s /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o cj 2 o REWRITE_RULE [loweringPostsTheory.expr_post_def] o CONJUNCT1) >>
     simp_tac (srw_ss()) [vyperStorageFootprintTheory.storage_well_formed_on_def,
       vyperStorageBackendTheory.get_storage_def, boolTheory.FORALL_BOOL]) >>
  suspend "caller_and_result"
QED

Resume abi_encode_nonword_vv_full_from_packaging[caller_and_result]:
  `!name b sz. local_region ce ee.scopes t name b sz <=> local_region ce ee.scopes u name b sz` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) ctx func ce cx ee u` mp_tac >>
     qpat_assum `local_ptrs_reserved ce ready` mp_tac >>
     qpat_assum `!x w. not_fresh_at ready x /\ lookup_var x u = SOME w ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[tuplePlaceStepTheory.tuple_place_endpoint_local_regions_some]) >>
  `sm.cs_next_id < sb.cs_next_id` by
    (drule_then (assume_tac o cj 2) abiEncoderCountersTheory.abi_encoder_counters >>
     drule_then (assume_tac o cj 1) abiBuiltinEncodeCodeTheory.abi_builtin_encode_finish_shape >>
     decide_tac) >>
  `!b sz. (!i. b <= i /\ i < b+sz ==> i IN P /\ (i < p \/ p+32 <= i)) ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz u.vs_memory` by
    (rpt gen_tac >> disch_tac >> irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
     qx_gen_tac `i` >> disch_tac >>
     qpat_assum `!i. i IN P /\ _ ==> mem_bytes_at i 1 t.vs_memory = _ /\ _`
       (qspec_then `i` (irule o cj 1)) >>
     first_x_assum (irule o SPEC_ALL) >> (simp[])) >>
  `!name b sz. local_region ce ee.scopes u name b sz ==>
      mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz u.vs_memory` by
    (map_every qx_gen_tac [`name`,`b`,`sz`] >> disch_tac >>
     qpat_assum `!b sz. (!i. _ ==> i IN P /\ _) ==> _`
       (qspecl_then [`b`,`sz`] irule) >>
     qx_gen_tac `i` >> strip_tac >> conj_tac
     >- ((qpat_assum `!name b sz i. local_region ce ee.scopes u name b sz /\ _ ==> i IN P`
           (qspecl_then [`name`,`b`,`sz`,`i`] irule) >> asm_rewrite_tac[] >> (metis_tac[]))) >>
     qpat_assum `!name b sz. local_region ce ee.scopes u name b sz ==> regions_disjoint p 32 b sz`
       (qspecl_then [`name`,`b`,`sz`] (mp_tac o REWRITE_RULE[loweringStateRelDefsTheory.regions_disjoint_def])) >>
     asm_rewrite_tac[] >> decide_tac) >>
  (conj_tac >- suspend "pure_frame") >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (qexistsl_tac [`limit`,`sm.cs_next_id`,`p`,`N`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (simp_tac (srw_ss()) [] >> rpt strip_tac >>
        qpat_assum `!name b sz. local_region ce ee.scopes t name b sz <=> _`
          (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
        qpat_assum `!name b sz. local_region ce ee.scopes u name b sz ==> regions_disjoint p N b sz`
          (drule_then (ACCEPT_TAC o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def]))) >>
     ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qpat_assum `expr_type (TypeBuiltin ann _ _ _) = _`
         (ACCEPT_TAC o REWRITE_RULE [vyperASTTheory.expr_type_def])) >>
     qpat_assum `!mem. mem_agree_outside tnf.t_mem _ mem ==> val_in_memory _ _ _ mem`
       (qspec_then `t.vs_memory` mp_tac) >>
     rewrite_tac[bodyPtrDefsTheory.mem_agree_outside_def])) >>
  (conj_tac >- suspend "wb_frame") >>
  suspend "state_rel"
QED

Resume abi_encode_nonword_vv_full_from_packaging[wb_frame]:
  rewrite_tac[exprSimWordArgsTheory.wb_frame_gas_obs] >>
  qpat_assum `wb_frame ce es ee sa s0 u`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  rewrite_tac[loweringPostsTheory.wb_frame_def] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!x w. not_fresh_at ready x /\ lookup_var x u = SOME w ==> _` irule >>
      simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      irule abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated >>
      qpat_assum `abi_encoder_registered_effect _ _ u t` (irule_at Any) >>
      first_assum (irule o SPEC_ALL) >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (map_every qx_gen_tac [`aid`,`off`,`sz`] >> strip_tac >>
      qpat_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==>
                    mem_bytes_at off sz u.vs_memory = _`
        (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
      (impl_tac >- asm_rewrite_tac[]) >> disch_then (rewrite_tac o single o GSYM) >>
      qpat_assum `!b sz. (!i. _ ==> i IN P /\ _) ==> _`
        (qspecl_then [`off`,`sz`] irule) >>
      qx_gen_tac `i` >> strip_tac >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==>
                              i IN P /\ (i < p \/ p+32 <= i)`
        (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
  irule exprSimPropsTheory.locals_kept_regions_tail >>
  qpat_assum `locals_kept ce es ee s0 u` (irule_at Any) >>
  qpat_assum `!n b sz. local_region ce es.scopes s0 n b sz <=> _`
    (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC
QED

Resume abi_encode_nonword_vv_full_from_packaging[pure_frame]:
  rewrite_tac[loweringPostsTheory.expr_has_effect_thm, listTheory.EXISTS_DEF] >>
  strip_tac >>
  `pure_frame ce func es sa s0 s` by
    (qpat_assum `!h. valid_horizon _ _ h ee.storage_trace ==> expr_post h ctx func ce cx e es sa sm s0 ee v op s /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
       exprSimWordArgsTheory.expr_post_pure_frame) o CONJUNCT1) >>
     disch_then irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `pure_frame ce func es sa s0 s`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.pure_frame_def]) >>
  rewrite_tac[loweringPostsTheory.pure_frame_def] >>
  conj_tac
  >- (map_every qx_gen_tac [`name`,`b`,`sz`] >> strip_tac >>
      `local_region ce ee.scopes u name b sz` by metis_tac[] >>
      `regions_disjoint p N b sz` by
        (qpat_assum `!n b sz. local_region ce ee.scopes u n b sz ==> regions_disjoint p N b sz`
           (drule_then ACCEPT_TAC)) >>
      `regions_disjoint (p+32) (case midw of NONE => 0 | SOME mw => 32) b sz` by
        (qpat_assum `regions_disjoint p N b sz` mp_tac >>
         rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (qpat_assum `!b sz. regions_disjoint (p+32) _ b sz ==> _` (drule_then ACCEPT_TAC)) >>
      qpat_assum `!n b sz. local_region ce ee.scopes u n b sz ==> mem_bytes_at b sz t.vs_memory = _`
        (drule_then (fn th => rewrite_tac[th])) >>
      qpat_assum `!n b sz. local_region ce es.scopes s0 n b sz ==> mem_bytes_at b sz s.vs_memory = _`
        (drule_then (fn th => asm_rewrite_tac[th]))) >>
  suspend "pure_exterior"
QED

Resume abi_encode_nonword_vv_full_from_packaging[pure_exterior]:
  map_every qx_gen_tac [`off`,`n`] >> disch_tac >>
  `cs_extends sm ready` by
    (drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_setup_shape >> strip_tac >>
     rewrite_tac[compileEnvTheory.cs_extends_def] >> qexists `[]` >>
     asm_rewrite_tac[listTheory.APPEND]) >>
  `cs_extends ready body_end` by metis_tac[abiEncoderAppendTheory.cs_extends_abi_encode] >>
  `cs_extends body_end sb` by
    (drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_finish_shape >> strip_tac >>
     rewrite_tac[compileEnvTheory.cs_extends_def] >> qexists `[]` >>
     asm_rewrite_tac[listTheory.APPEND]) >>
  `fn_has_code sm ready func` by metis_tac[fragExecTheory.fn_has_code_split,cs_extends_trans] >>
  drule_all exprSimAbiEncodePrefixWindowTheory.abi_encode_setup_alloca_code >>
  qmatch_goalsub_abbrev_tac `MEM allocation (fn_insts func)` >> strip_tac >>
  `allocation.inst_id = sm.cs_next_id /\ allocation.inst_opcode = ALLOCA` by
    simp_tac (srw_ss()) [Abbr `allocation`, venomInstTheory.mk_inst_def] >>
  `regions_disjoint off n p N` by
    ((qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> regions_disjoint off n b sz`
       (qspecl_then [`allocation`,`p`,`N`] irule) >>
     qexists `allocation` >> asm_rewrite_tac[] >> (metis_tac[]))) >>
  `!id b k. id IN sites /\ FLOOKUP t.vs_allocas id = SOME (b,k) ==>
    off+n <= b \/ b+k <= off` by
    (map_every qx_gen_tac [`id`,`b`,`k`] >> strip_tac >>
     `?j. MEM j (fn_insts func) /\ j.inst_id = id /\ j.inst_opcode = ALLOCA` by
       (qpat_assum `id IN sites` mp_tac >>
        simp_tac bool_ss [Abbr `sites`, abiEncoderWindowContractTheory.window_alloca_sites_def,
                          pred_setTheory.GSPECIFICATION, pairTheory.PAIR_EQ] >>
        strip_tac >> goal_assum (drule_at Any) >> asm_rewrite_tac[]) >>
     `sa.cs_next_id <= j.inst_id` by
       (qpat_assum `!id. id IN sites ==> _` (qspec_then `id` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        qpat_assum `j.inst_id = id` (fn th => rewrite_tac[th]) >> decide_tac) >>
     qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> regions_disjoint off n b sz`
       (qspecl_then [`j`,`b`,`k`] mp_tac) >>
     (impl_tac >- (ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
        qpat_assum `j.inst_id = id` (fn th => rewrite_tac[th]) >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o REWRITE_RULE [loweringStateRelDefsTheory.regions_disjoint_def])) >>
  `mem_bytes_at off n s.vs_memory = mem_bytes_at off n s0.vs_memory` by
    (qpat_assum `!off len. _ ==> mem_bytes_at off len s.vs_memory = _`
       (qspecl_then [`off`,`n`] mp_tac) >>
     (impl_tac >-
       (map_every qx_gen_tac [`j`,`b`,`k`] >> strip_tac >>
        `FLOOKUP u.vs_allocas j.inst_id = SOME (b,k)` by
          (qpat_assum `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> _`
             (drule_then ACCEPT_TAC)) >>
        `FLOOKUP t.vs_allocas j.inst_id = SOME (b,k)` by
          (irule abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated >>
           qpat_assum `abi_encoder_registered_effect _ _ u t` (irule_at Any) >> first_assum ACCEPT_TAC) >>
        qpat_assum `!inst b sz. MEM inst (fn_insts func) /\ _ ==> regions_disjoint off n b sz`
          (qspecl_then [`j`,`b`,`k`] mp_tac) >>
        (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        disch_then ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `mem_bytes_at off n u.vs_memory = mem_bytes_at off n s.vs_memory` by
    (qpat_assum `!b sz. regions_disjoint (p+32) _ b sz ==> _` irule >>
     qpat_assum `regions_disjoint off n p N` mp_tac >>
     rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qpat_assum `mem_bytes_at off n s.vs_memory = mem_bytes_at off n s0.vs_memory`
    (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `mem_bytes_at off n u.vs_memory = mem_bytes_at off n s.vs_memory`
    (fn th => rewrite_tac[GSYM th]) >>
  irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >>
  qx_gen_tac `a` >> strip_tac >>
  mp_tac (Q.INST [`lo` |-> `off`, `n` |-> `n`, `a` |-> `a`,
    `s` |-> `u`, `t` |-> `t`,
    `ids` |-> `window_alloca_sites func (frag_ids ready body_end)`,
    `outs` |-> `[(p+32+LENGTH (selector : word8 list),LENGTH (enc ct rv));(p,32)]`]
    exprSimAbiEncodeFrameTransferTheory.abi_encode_registered_protected_byte) >>
  (impl_tac >-
    (ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac
     >- (simp_tac (srw_ss()) [listTheory.EVERY_DEF] >>
         qpat_assum `regions_disjoint off n p N` mp_tac >>
         rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     qpat_assum `Abbrev (sites = _)`
       (fn th => rewrite_tac[GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
     first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
QED

Resume abi_encode_nonword_vv_full_from_packaging[state_rel]:
  rewrite_tac[exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
  `stmt_state_rel H ctx func ce cx ee u` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ ee u /\ _`
       (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  drule_then assume_tac stateRelProjTheory.stmt_state_rel_state_rel >>
  drule_then strip_assume_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac stateRelProjTheory.stmt_state_rel_alloca_room >>
  drule_then assume_tac stateRelProjTheory.stmt_state_rel_fmp_room >>
  drule_then assume_tac bodyFullIntCallReturnFrameTheory.return_stmt_immutable_sep >>
  drule_then assume_tac stateRelProjTheory.stmt_state_rel_immutable_base_zero >>
  qpat_assum `window_alloca_growth u t`
    (CONJUNCTS_THEN2 assume_tac (assume_tac o ONCE_REWRITE_RULE [boolTheory.CONJ_COMM]) o
     REWRITE_RULE [abiEncoderWindowContractTheory.window_alloca_growth_def]) >>
  qpat_assum `abi_encoder_registered_effect _ _ u t`
    (strip_assume_tac o cj 2 o REWRITE_RULE [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def]) >>
  `!i r. FLOOKUP u.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r` by
    (rpt strip_tac >> irule abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated >>
     qpat_assum `abi_encoder_registered_effect _ _ u t` (irule_at Any) >> first_assum ACCEPT_TAC) >>
  (`!name entry ptr sz. lookup_scopes name ee.scopes = SOME entry /\
      FLOOKUP ce.ce_vars name = SOME (PtrVar (Var ptr) sz) ==>
      lookup_var ptr t = lookup_var ptr u` by suspend "reserved_ptrs") >>
  `immutable_alloca_sep func ce cx ee t` by
    (match_mp_tac (Q.INST [`initial` |-> `u`]
       exprSimAbiEncodeStateTransportTheory.abi_encode_caller_immutable_separation) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (`ce.ce_is_ctor ==> !name itv iv off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
      mem_bytes_at off (type_memory_size itv) t.vs_memory =
      mem_bytes_at off (type_memory_size itv) u.vs_memory` by suspend "immutable_bytes") >>
  `state_rel H func ce cx ee t` by
    (match_mp_tac (Q.INST [`initial` |-> `u`, `prepared` |-> `u`,
       `observer` |-> `func`, `ids` |-> `window_alloca_sites func (frag_ids ready body_end)`,
       `outs` |-> `[(p+32+LENGTH (selector : word8 list),LENGTH (enc ct rv));(p,32)]`]
       exprSimAbiEncodeStateTransportTheory.abi_encode_caller_state_rel) >>
     rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, REFL_TAC]) >>
  `immutable_base_zero ce t` by
    (match_mp_tac (Q.INST [`initial` |-> `u`]
       exprSimAbiEncodeStateTransportTheory.abi_encode_caller_immutable_base) >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >> rpt strip_tac >>
     drule_all_then assume_tac exprLoweringPropsTheory.local_ptrs_reserved_imm_base >>
     qpat_assum `!x w. not_fresh_at ready x /\ lookup_var x u = SOME w ==> _` irule >>
     asm_rewrite_tac[]) >>
  `alloca_room ctx func t /\ fmp_room ctx func t` by
    (match_mp_tac (Q.INST [`initial` |-> `u`, `observer` |-> `func`]
       exprSimAbiEncodeStateTransportTheory.abi_encode_caller_resource_room) >>
     ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (rpt strip_tac >> first_assum ACCEPT_TAC) >>
     rpt strip_tac) >>
  match_mp_tac stateRelProjTheory.stmt_state_rel_intro >>
  ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "literal_rows"
QED

Resume abi_encode_nonword_vv_full_from_packaging[reserved_ptrs]:
  map_every qx_gen_tac [`local_name`,`local_entry`,`local_ptr`,`local_size`] >> strip_tac >>
  `not_fresh_at ready local_ptr` by
    (qpat_assum `local_ptrs_reserved ce ready` mp_tac >>
     qpat_assum `FLOOKUP ce.ce_vars local_name = SOME _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  `?w. lookup_var local_ptr u = SOME w` by
    (qpat_assum `local_ptrs_rel func ce ee.scopes u` mp_tac >>
     qpat_assum `lookup_scopes local_name ee.scopes = SOME local_entry` mp_tac >>
     qpat_assum `FLOOKUP ce.ce_vars local_name = SOME _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [loweringStateRelDefsTheory.local_ptrs_rel_def] >> metis_tac[]) >>
  qpat_assum `lookup_var local_ptr u = SOME _` (fn th => rewrite_tac[th]) >>
  qpat_assum `!x w. not_fresh_at ready x /\ lookup_var x u = SOME w ==> _` irule >>
  asm_rewrite_tac[]
QED

Resume abi_encode_nonword_vv_full_from_packaging[literal_rows]:
  map_every qx_gen_tac [`j`,`lit_word`,`row_base`,`row_size`] >> strip_tac >>
  Cases_on `j.inst_id IN window_alloca_sites func (frag_ids ready body_end)`
  >- (`j.inst_id IN frag_ids ready body_end` by
        (pop_assum mp_tac >> simp_tac (srw_ss()) [abiEncoderWindowContractTheory.window_alloca_sites_def]) >>
      `j.inst_operands = [Lit 32w]` by
        (drule_all_then (ACCEPT_TAC o CONJUNCT1) externalReturnEncoderSitesTheory.encoder_function_alloca_shape) >>
      `FLOOKUP cut.vs_allocas j.inst_id = SOME (row_base,row_size)` by
        (qpat_assum `t.vs_allocas = cut.vs_allocas` (fn th => rewrite_tac[GSYM th]) >>
         first_assum ACCEPT_TAC) >>
      `row_size = 32` by
        drule_all_then ACCEPT_TAC abiEncoderWindowContractTheory.window_strong_result_sizes >>
      qpat_assum `j.inst_operands = [Lit lit_word]` mp_tac >>
      qpat_assum `j.inst_operands = [Lit 32w]` (fn th => rewrite_tac[th]) >>
      simp_tac (srw_ss()) [wordsTheory.dimword_def] >> asm_rewrite_tac[]) >>
  `FLOOKUP u.vs_allocas j.inst_id = SOME (row_base,row_size)` by
    (qpat_assum `!i. i NOTIN window_alloca_sites func (frag_ids ready body_end) ==> _`
       (qspec_then `j.inst_id` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (fn th => rewrite_tac[GSYM th]) >> first_assum ACCEPT_TAC) >>
  qpat_assum `stmt_state_rel H ctx func ce cx ee u`
    (mp_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_size) >>
  disch_then (qspecl_then [`j`,`lit_word`,`row_base`,`row_size`] match_mp_tac) >>
  asm_rewrite_tac[]
QED

Resume abi_encode_nonword_vv_full_from_packaging[immutable_bytes]:
  `cs_extends sm ready` by
    (drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_setup_shape >> strip_tac >>
     rewrite_tac[compileEnvTheory.cs_extends_def] >> qexists `[]` >>
     asm_rewrite_tac[listTheory.APPEND]) >>
  `cs_extends ready body_end` by metis_tac[abiEncoderAppendTheory.cs_extends_abi_encode] >>
  `cs_extends body_end sb` by
    (drule abiBuiltinEncodeCodeTheory.abi_builtin_encode_finish_shape >> strip_tac >>
     rewrite_tac[compileEnvTheory.cs_extends_def] >> qexists `[]` >>
     asm_rewrite_tac[listTheory.APPEND]) >>
  `fn_has_code sm ready func` by metis_tac[fragExecTheory.fn_has_code_split,cs_extends_trans] >>
  drule_all exprSimAbiEncodePrefixWindowTheory.abi_encode_setup_alloca_code >>
  qmatch_goalsub_abbrev_tac `MEM allocation (fn_insts func)` >> strip_tac >>
  `allocation.inst_id = sm.cs_next_id /\ allocation.inst_opcode = ALLOCA` by
    simp_tac (srw_ss()) [Abbr `allocation`, venomInstTheory.mk_inst_def] >>
  `!i. i IN (sm.cs_next_id INSERT window_alloca_sites func (frag_ids ready body_end)) ==>
     ?j. MEM j (fn_insts func) /\ j.inst_opcode = ALLOCA /\ j.inst_id = i` by
    (simp_tac (srw_ss()) [abiEncoderWindowContractTheory.window_alloca_sites_def] >>
     rpt strip_tac >> metis_tac[]) >>
  strip_tac >> map_every qx_gen_tac [`name`,`itv`,`iv`,`off`] >> strip_tac >>
  `!i b k. i IN (sm.cs_next_id INSERT window_alloca_sites func (frag_ids ready body_end)) /\
      FLOOKUP t.vs_allocas i = SOME (b,k) ==> off+type_memory_size itv <= b \/ b+k <= off` by
    (match_mp_tac (Q.INST [`initial` |-> `t`, `actual` |-> `t`, `vs` |-> `ee`,
       `func` |-> `func`, `cenv` |-> `ce`, `cx` |-> `cx`, `name` |-> `name`, `v` |-> `iv`]
       exprSimAbiEncodeCallerFrameTheory.abi_encode_immutable_region_separation) >>
     ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (rpt strip_tac >> first_assum ACCEPT_TAC) >>
     conj_tac >-
       (map_every qx_gen_tac [`row_id`,`row_base`,`row_size`] >> strip_tac >>
        qpat_assum `FLOOKUP t.vs_allocas row_id = SOME _` mp_tac >>
        qpat_assum `FLOOKUP t.vs_allocas row_id = NONE`
          (fn th => simp_tac (srw_ss()) [th])) >>
     first_assum ACCEPT_TAC) >>
  `off+type_memory_size itv <= p \/ p+N <= off` by
    (qpat_assum `!i b k. i IN (sm.cs_next_id INSERT _) /\ _ ==> _`
       (qspecl_then [`sm.cs_next_id`,`p`,`N`] match_mp_tac) >>
     conj_tac >- simp_tac (srw_ss()) [] >> first_assum ACCEPT_TAC) >>
  irule abiDecodeStaticPropsTheory.mem_bytes_at_bytewise >> qx_gen_tac `a` >> strip_tac >>
  mp_tac (Q.INST [`lo` |-> `off`, `n` |-> `type_memory_size itv`, `a` |-> `a`,
    `s` |-> `u`, `t` |-> `t`, `ids` |-> `window_alloca_sites func (frag_ids ready body_end)`,
    `outs` |-> `[(p+32+LENGTH (selector : word8 list),LENGTH (enc ct rv));(p,32)]`]
    exprSimAbiEncodeFrameTransferTheory.abi_encode_registered_protected_byte) >>
  (impl_tac >-
    (ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (simp_tac (srw_ss()) [listTheory.EVERY_DEF] >> decide_tac) >>
     map_every qx_gen_tac [`i`,`b`,`k`] >> strip_tac >>
     qpat_assum `!i b k. i IN (sm.cs_next_id INSERT _) /\ _ ==> _`
       (qspecl_then [`i`,`b`,`k`] match_mp_tac) >>
     conj_tac >- (simp_tac (srw_ss()) [] >> disj2_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
QED

Finalise abi_encode_nonword_vv_full_from_packaging
