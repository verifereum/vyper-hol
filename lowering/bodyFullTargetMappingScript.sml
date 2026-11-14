(* The element suffix of a subscript into a mapping target on the joint
   line: the key's hash (for a bytestring key) and the slot computation
   after the index (subscript_tail_full, bodyFullTargetSubscript).

   TOP-LEVEL:
     target_mapping_tail_full -- subscript_tail_full when the base is a
       mapping *)
Theory bodyFullTargetMapping
Ancestors
  bodyFullTargetSubscript bodyFullTargetDefs bodySimFull targetPlaceSim
  bodyFullTargetMappingFacts bodyFullTargetMappingKey bodyFullTargetMappingScratch
  bodyFullTargetMappingRep bodyFullTargetMappingRun bodyFullTargetMappingOutcome
  targetSubscriptMapping targetSubscriptSplit vyperStorageTrace
  gasOutcomeFull fragGasOriginPtr vyperStorageFootprint loweringPosts
  vyperTypeSystem vyperInterpreter vyperState
  bodyPtrDefs exprOperandVar exprLoweringProps compileEnv ptrDiscipline loweringStateRelDefs
  stmtLoweringMono vyperEvalExprPreservesScopesDom exprSimWordArgs

Theorem target_mapping_tail_full:
  body_inv tops ctx cenv cx /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (HashMapT kt vt) ==>
  subscript_tail_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx env bt e es
Proof
  strip_tac >> simp[subscript_tail_full_def] >> rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace)
     mid2.storage_trace` by gvs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid2.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all target_mapping_source_cut >> strip_tac >> gvs[] >>
  drule_all target_mapping_compile_cut >> strip_tac >>
  Cases_on `extend_place cx (HashMapRef tr base_slot (expr_type e) vt)
    (ValueSubscript v) mid2` >> rename1 `extend_place _ _ _ _ = (res,ee)` >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     storage_well_formed_on cx mid2 (FST H)` by
    (rpt strip_tac >>
     `valid_horizon cx st0 H mid2.storage_trace` by
       metis_tac[valid_horizon_frame, storage_trace_frame_extend_place] >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> gvs[expr_post_def]) >>
  suspend "join"
QED

Resume target_mapping_tail_full[join]:
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid2.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`kt` |-> `expr_type e`] mapping_index_key_input)) >> strip_tac >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!x. iop = Var x \/ bop = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac
     >- metis_tac[compile_lower_value_var] >>
     `not_fresh_at sm x` by gvs[target_post_def] >>
     gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `op_taint tn2 bop = {}` by
    (`!x. bop = Var x ==> not_fresh_at sm x` by gvs[target_post_def] >>
     Cases_on `bop` >> gvs[op_taint_def, target_ptr_ok_def, ghost_kept_at_def] >>
     metis_tac[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `allocas_from lo t2 /\ lo <= t2.vs_alloca_next` by gvs[ghost_inv_at_def] >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid2 t2 /\
    ghost_inv_at (DF H) lo d cenv cx mid2 G2 tn2 t2` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> gvs[expr_post_def]) >>
  `?t HG tm.
    eval_operand slot t = SOME (hashmap_slot base_slot (encode_hashmap_key (expr_type e) v)) /\
    op_taint tm slot = {} /\ op_prov HG slot = NONE /\
    (!x. slot = Var x ==> not_fresh_at sb x) /\
    (!x. not_fresh_at sn x ==> lookup_var x t = lookup_var x t2 /\
      FLOOKUP HG x = FLOOKUP G2 x /\ op_taint tm (Var x) = op_taint tn2 (Var x)) /\
    wb_frame cenv mid2 mid2 sn t2 t /\ pure_frame cenv func mid2 sn t2 t /\
    ghost_kept_at lo cenv mid2 sn G2 tn2 t2 HG tm /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ allocas_from lo t /\
    t2.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H mid2.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t2,G2,tn2) [] (OK t,HG,tm) /\
      stmt_state_rel H ctx func cenv cx mid2 t /\
      ghost_inv_at (DF H) lo d cenv cx mid2 HG tm t)` by
    (qspecl_then [`iop`, `storage_trace_horizon mid2.storage_trace`]
       ho_match_mp_tac (Q.GENL [`key`, `H0`] mapping_suffix_full_run) >>
     simp[] >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sn.cs_next_id` by
    (mp_tac (Q.SPECL [`bt`, `cenv`, `sa`] ci_mono_compile_get_target_ptr) >>
     mp_tac (Q.SPECL [`cenv`, `expr_type e`, `e`, `sm`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  `MAP FDOM es.scopes = MAP FDOM mid1.scopes /\
   MAP FDOM mid1.scopes = MAP FDOM mid2.scopes` by
    (conj_tac
     >- (drule eval_base_place_preserves_scopes_dom >> simp[]) >>
     metis_tac[exprSimIfExpTheory.ifexp_root_condition_scopes]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid1.storage_trace` by
    (qsuff_tac `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace)
       (mid1 with gas_obs := index_gas).storage_trace` >- simp[] >>
     irule (INST_TYPE [Type.alpha |-> ``:value``] valid_horizon_frame) >>
     qexistsl_tac [`vyperState$bind (eval_expr cx e) (read_result cx)`, `INL v`, `mid2`] >>
     simp[] >> irule storage_trace_frame_bind >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) es.storage_trace` by
    (qsuff_tac `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace)
       (es with gas_obs := base_gas).storage_trace` >- simp[] >>
     irule (INST_TYPE [Type.alpha |-> ``:eval_result``] valid_horizon_frame) >>
     qexistsl_tac [`eval_base_place cx bt`, `INL (HashMapRef tr base_slot (expr_type e) vt)`, `mid1`] >>
     simp[evaluate_storage_trace_frame]) >>
  `wb_frame cenv es mid1 sa s0 t1 /\
   wb_frame cenv mid1 mid2 sm t1 t2 /\
   stmt_state_rel (storage_trace_horizon mid2.storage_trace) ctx func cenv cx es s0` by
    (gvs[target_post_def, expr_post_def, wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv es mid2 sa s0 t2 /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (irule (INST_TYPE [Type.beta |-> ``:256``] mapping_suffix_frames_join) >> simp[] >>
     conj_tac >- (qexistsl_tac [`storage_trace_horizon mid2.storage_trace`, `ctx`, `cx`, `func`] >> simp[]) >>
     qexistsl_tac [`G1`, `mid1`, `t1`, `sm`, `tn1`] >> simp[]) >>
  `wb_frame cenv es mid2 sa s0 t /\
   ghost_kept_at lo cenv es sa G0 tn0 s0 HG tm` by
    (irule (INST_TYPE [Type.beta |-> ``:256``] mapping_suffix_frames_join) >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qpat_x_assum `r = _` SUBST_ALL_TAC >>
  irule mapping_extension_full_outcome >>
  simp[] >> qexistsl_tac [`HG`, `t`, `tm`] >>
  simp[] >> rpt strip_tac >>
  `valid_horizon cx st0 H mid2.storage_trace` by
    metis_tac[valid_horizon_frame, storage_trace_frame_extend_place] >>
  metis_tac[]
QED

Finalise target_mapping_tail_full
