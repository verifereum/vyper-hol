(* Request-prefix companion to bodyFullStructLit. *)
Theory s1PrefixStructLit
Ancestors
  s1PrefixPreds bodyFullStructLit s1PrefixStructLitFields
  s1PrefixDefs s1PrefixOfVV s1PrefixCompose s1PrefixInvalidTraceDomain
  exprSimAggregateLayout exprSimAggregateSource exprBodyPreProps
  exprSimFullBundleProps bodyInvCodeProps exprSimDefs
  bodyFullIfExpReach bodyFullExprGeneric bodyMemoryDefs bodyPtrDefs
  compileEnv gasShadowCompile gasShadowState gasShadow gasContext
  loweringHalt allocLimits exprLoweringProps exprOperandVar loweringStateRelDefs
  vyperInterpreter vyperStorageTrace vyperStorageFootprint vyperAST
  vyperTypeSystem vyperState vyperTyping fragExec list pair

Theorem structlit_vv_sim_prefix:
  !cx v7 src_id_opt id kes DF lo d PG tops ctx shadow_ctx func shadow_func
     cenv env ty es.
    body_exprs_full_ok cx (MAP SND kes) /\
    body_exprs_prefix_ok cx (MAP SND kes) /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es ==>
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (StructLit v7 (src_id_opt,id) kes) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >> rpt gen_tac >> strip_tac >>
  `!qe. SND (eval_expr cx (StructLit v7 (src_id_opt,id) kes) qe) =
         SND (eval_exprs cx (MAP SND kes) qe)` by
    (gen_tac >> Cases_on `eval_exprs cx (MAP SND kes) qe` >>
     drule aggregate_eval_struct >>
     disch_then (qspecl_then [`(src_id_opt,id)`, `v7`] mp_tac) >> simp[]) >>
  drule_then (fn th => once_rewrite_tac[th]) gas_prefix_full_state_cong >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_prefix_full_invalid_trace_domain >> simp[evaluate_storage_trace_frame]) >>
  drule compile_struct_literal_inv >> strip_tac >> gvs[] >>
  drule struct_literal_lookup_types >> strip_tac >>
  drule struct_literal_evaluated_layout >> strip_tac >>
  drule_then strip_assume_tac expr_body_pre_static_facts >>
  `!e st. MEM e (MAP SND kes) /\ expr_sim_inv cenv cx env st ==>
    expr_body_pre cenv cx env e st` by metis_tac[expr_body_pre_struct_field] >>
  `v7 = StructT (src_id_opt,id)` by fs[well_typed_expr_def] >>
  `type_memory_size_list tvs < dimword(:256)` by
    (fs[alloc_limits_expr_def, type_memory_bytes_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `compile_alloc_buffer (type_memory_size_list tvs) sa = (ba,sm)` by metis_tac[] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (drule compile_alloc_buffer_extends >> strip_tac >>
     mp_tac (Q.SPECL [`compile_expr`, `cenv`, `StructT (src_id_opt,id)`,
       `kes`, `ba.buf_operand`, `0`, `sm`] ci_mono_compile_struct_lit_cfn) >>
     simp[ci_mono_def] >>
     (impl_tac >- (rpt gen_tac >> Cases_on `compile_expr cenv' ty' e' sa'` >>
       drule (cj 1 compile_expr_grows) >> simp[])) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (drule_all fn_has_code_split >> simp[]) >>
  `?Hbase:((bool # bytes32 # type_value) list # num list).
       stmt_state_rel Hbase ctx func cenv cx es s0` by
    (qexists_tac `storage_trace_horizon es.storage_trace` >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     gvs[storage_trace_domain_def]) >>
  drule_all structlit_alloc_init_full >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`] strip_assume_tac) >>
  suspend "code_cut"
QED

Resume structlit_vv_sim_prefix[code_cut]:
  `?shadow_sm. compile_alloc_buffer (type_memory_size_list tvs) shadow_sa = (ba,shadow_sm) /\
      gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.SPEC `type_memory_size_list tvs`
       bodyFullExprGenericTheory.gas_shadow_compiles_alloc_buffer) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `compile_alloc_buffer (type_memory_size_list tvs) shadow_sa` >> gvs[]) >>
  `compile_struct_lit compile_expr (gas_shadow_env T cenv) (StructT (src_id_opt,id))
     (MAP (I ## gas_shadow_expr) kes) (Var q) 0 shadow_sm = (u,shadow_sb)` by
    (qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
       (strip_assume_tac o MATCH_MP compile_struct_literal_inv o
        REWRITE_RULE [gasShadowTheory.gas_shadow_expr_def]) >>
     gvs[] >> imp_res_tac exprOperandVarTheory.compiler_struct_lit_result >> gvs[]) >>
  `fn_has_code shadow_sm shadow_sb shadow_func` by
    (drule compile_alloc_buffer_extends >> strip_tac >>
     `cs_extends shadow_sm shadow_sb` by
       (mp_tac (Q.SPECL [`compile_expr`, `gas_shadow_env T cenv`, `StructT (src_id_opt,id)`,
          `MAP (I ## gas_shadow_expr) kes`, `Var q`, `0`, `shadow_sm`]
          ci_mono_compile_struct_lit_cfn) >> simp[ci_mono_def] >>
        (impl_tac >- (rpt gen_tac >> Cases_on `compile_expr cenv' ty' e' sa'` >>
          drule (cj 1 compile_expr_grows) >> simp[])) >> simp[]) >>
     drule_all fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME(PtrVar(Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME(PtrVar(Var x) sz) ==> not_fresh_at sm x)` by
    (fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all bodyFullIfExpReachTheory.body_inv_no_phi >> simp[]) >>
  `!fn inst s. frag_reachable ctx func t fn inst s ==> dalloca_fmp_headroom inst s` by
    (rpt strip_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK t,G,tn)`
       (qspec_then `DF (storage_trace_horizon es.storage_trace)` assume_tac) >>
     drule_all bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  `cx_tops cx = tops` by metis_tac[body_inv_main_code] >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[evaluate_storage_trace_frame] >>
  qexistsl [`G`,`t`,`tn`] >> simp[] >>
  `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sm,sb,shadow_sm,shadow_sb)` by
    simp[expr_sim_full_code_def] >>
  `compile_struct_lit compile_expr cenv (StructT (src_id_opt,id)) kes (Var q) 0 sm = (u,sb)` by
    fs[] >>
  suspend "initial_fields"
QED

Resume structlit_vv_sim_prefix[initial_fields]:
  (* The allocation has executed; no field has been evaluated or stored. *)
  qabbrev_tac `inv' = (\H ee cs G tn z cells off.
    stmt_state_rel H ctx func cenv cx ee z /\
    storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn z /\
    wb_frame cenv es ee sa s0 z /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
    MAP FDOM es.scopes = MAP FDOM ee.scopes /\
    ~z.vs_halted /\ expr_sim_full_endpoint func cs s0 z /\
    not_fresh_at cs q /\ lookup_var q z = SOME (n2w (w2n w)) /\
    ptr_covers G tn q z (type_memory_size_list tvs) /\
    FLOOKUP z.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size_list tvs) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size_list tvs))] [q])
      (fn_insts func) /\
    lo <= w2n w /\ w2n w + type_memory_size_list tvs < dimword(:256) /\
    sa.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id < cs.cs_next_id /\
    sa.cs_next_var <= cs.cs_next_var /\ off <= type_memory_size_list tvs /\
    (!name p k. local_region cenv ee.scopes z name p k ==>
      w2n w + type_memory_size_list tvs <= p \/ p+k <= w2n w) /\
    (!name p k. local_region cenv es.scopes s0 name p k ==>
      w2n w + type_memory_size_list tvs <= p \/ p+k <= w2n w) /\
    (!old p k. FLOOKUP s0.vs_allocas old = SOME (p,k) /\ old < sa.cs_next_id ==>
      w2n w + type_memory_size_list tvs <= p \/ p+k <= w2n w) /\
    EVERY (\(tv,v,p,k). w2n w <= p /\ p+k <= w2n w+off) cells /\
    literal_prefix_ok cells tn z /\ (F ==> pure_frame cenv func es sa s0 z))` >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> inv' H es sm G tn t [] 0` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H _ _ _ _ _ t /\ _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `type_memory_size_list tvs = _` kall_tac >>
     simp[Abbr `inv'`, expr_sim_full_endpoint_def,
          bodyPtrMakeArrayMemoryFrameTheory.literal_prefix_ok_def] >>
     rpt conj_tac >> rpt strip_tac >>
     first_assum (drule_then (mp_tac o GEN_ALL)) >> decide_tac) >>
  qpat_assum `Abbrev (inv' = _)`
    (mp_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  disch_then (irule o MATCH_MP
    (INST_TYPE [alpha |-> ``:256``] structlit_fields_bundled_prefix)) >>
  qpat_assum `expr_sim_full_code _ (sm,sb,shadow_sm,shadow_sb)` (irule_at Any) >>
  qpat_assum `compile_struct_lit compile_expr cenv _ kes (Var q) 0 sm = _` (irule_at Any) >>
  qpat_assum `OPT_MMAP _ _ = SOME tvs` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv sa s0` (irule_at Any) >>
  qexistsl [`env`,`[]`,`Hbase`] >> simp[] >> first_assum ACCEPT_TAC
QED

Finalise structlit_vv_sim_prefix[local]

Theorem structlit_expr_prefix_ok:
  !cx v7 src_id_opt id kes.
  (!ks. ks = MAP FST kes ==> body_exprs_full_ok cx (MAP SND kes)) /\
  (!ks. ks = MAP FST kes ==> body_exprs_prefix_ok cx (MAP SND kes)) ==>
  body_expr_prefix_ok cx (StructLit v7 (src_id_opt,id) kes)
Proof
  simp[] >> rpt strip_tac >>
  simp[Once body_expr_prefix_ok_def] >> rpt gen_tac >> strip_tac >>
  drule_all structlit_vv_sim_prefix >> metis_tac[expr_sim_prefix_of_vv]
QED
