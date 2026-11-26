(* The owned, nonword default-return keyword of a linked external call. *)
Theory bodyExtKeywordDefaultMods
Ancestors
  exprLowering exprLoweringProps stmtLoweringMono fragExec compileEnv
  gasShadowState gasShadowCompilePure gasShadowCompileStmtHelpers
  bodyFullPostsMods loweringPosts bodyMemSnapshotSourceLocation abiEncodeMaterialize
  context valueCopyBytes
  bodyFullPredsMods bodyExtKeywordDefaultReadMods bodyExtKeywordDefaultAllocMods
  bodyExtKeywordDefaultAllocResourcesMods bodyExtKeywordDefaultUnwrapMods
  bodyExtKeywordDefaultStoreMods bodyExtKeywordDefaultLandingMods
  bodyCopyReadPhysicalTypeMods abiEncodeArgsCase
  exprSimMemorySource bodyPtrAttributeSource exprOperandVar
  gasOutcomeFullPostMods gasExemptCertMods haltExitProj exprSimDefs stmtSimProps
  vyperEvalExprPreservesScopesDom vyperStorageTrace vyperStorageFootprint
  loweringHalt fragGasOriginPtr fragGasPathPtr freshWrites gasOutcomeFullPostPathMods
  valueTypingMemoryProps allocLimits words exprSimMemDefs logValueFramePtr
  bodyPtrBopRepresentationFrame robustCopyTransportPtr
  exprSimHypsDefs exprSimHyps aggregateEvaluatedLayout bodyFullShadowBodyInv
  fragGasOriginPtrLoop

Theorem ext_kw_default_retag[local]:
  compile_expr ce ty e sa = (vv,sm) /\
  vv_holds_mods ce cx (post_value_type ce e) pv vv ee s /\
  ~is_word_type (expr_type e) /\
  arg_type_fits (lowered_value_type ce e) (expr_type e) ==>
  compile_materialize_vv ce (lowered_value_type ce e)
    (ext_call_arg_value (lowered_value_type ce e) vv) =
  compile_materialize_vv ce (lowered_value_type ce e) vv
Proof
  strip_tac >>
  `post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\
   is_bytestring_type (lowered_value_type ce e)` by
    simp[materialize_post_lowered_classify] >>
  `post_value_type ce e <> lowered_value_type ce e ==>
   vv_location vv = NONE \/ vv_location vv = SOME LocMemory` by
    metis_tac[snapshot_changed_type_location] >>
  `unwrap_value ce (ext_call_arg_value (lowered_value_type ce e) vv) =
   unwrap_value ce vv` suffices_by simp[compile_materialize_vv_def] >>
  Cases_on `vv` >> simp[ext_call_arg_value_def] >>
  gvs[vv_holds_mods_def, vv_holds_def, vv_location_def] >>
  Cases_on `p.ptr_location = LocCode` >> gvs[] >>
  Cases_on `p.ptr_location = LocMemory` >>
  gvs[unwrap_value_def, is_bytestring_word_type]
QED
Theorem ext_kw_default_code_split[local]:
  compile_expr ce ty e sa = (vv,sm) /\
  compile_materialize_vv ce' dt vv sm = (op,sb) /\
  fn_has_code sa sb func ==>
  fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >> irule fn_has_code_split >> simp[] >>
  conj_tac
  >- (qspecl_then [`ce`,`ty`,`e`,`sa`] mp_tac (cj 1 ci_mono_compile_expr_sa) >>
      simp[ci_mono_def]) >>
  qspecl_then [`ce'`,`dt`,`vv`,`sm`] mp_tac ci_mono_compile_materialize_vv >>
  simp[ci_mono_def]
QED

Theorem ext_kw_default_compile_cut[local]:
  ~is_word_type rt /\
  compile_ext_call_kwarg compile_expr cenv rt EKDefault e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt EKDefault
    (gas_shadow_expr e) shadow_sa = ((op,dt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?vv sm shadow_sm.
    dt = lowered_value_type cenv e /\
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e)
      shadow_sa = (vv,shadow_sm) /\
    compile_materialize_vv cenv dt vv sm = (op,sb) /\
    compile_materialize_vv cenv dt vv shadow_sm = (op,shadow_sb) /\
    gas_shadow_state sm shadow_sm /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\
    fn_has_code shadow_sm shadow_sb shadow_func
Proof
  strip_tac >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,sm)` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) shadow_sa = (sv,shadow_sm)` >>
  `sv = vv /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
        (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule gas_shadow_stmt_compile_expr_env >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[]) >>
  gvs[] >>
  rename1 `compile_expr cenv (expr_type e) e sa = (child,sm)` >>
  Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) child sm` >>
  Cases_on `compile_materialize_vv cenv (lowered_value_type cenv e) child shadow_sm` >>
  gvs[compile_ext_call_kwarg_def,comp_bind_def,comp_return_def] >>
  metis_tac[ext_kw_default_code_split]
QED

Theorem ext_kw_default_head_mods:
  body_expr_full_ok_mods mods exps cx e /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  ~is_word_type rt /\ expr_type e = rt /\
  compile_ext_call_kwarg compile_expr cenv rt EKDefault e sa = ((op,dt),sb) /\
  compile_ext_call_kwarg compile_expr (gas_shadow_env T cenv) rt EKDefault (gas_shadow_expr e)
    shadow_sa = ((op,dt),shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)
    (\H res ee G tn t. ?v. res = INL v /\
      stmt_state_rel H ctx func cenv cx ee t /\ immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ~t.vs_halted /\ alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      return_buf_frame d cenv sb t /\ wb_frame cenv es ee sa s0 t /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      t.vs_labels = s0.vs_labels /\ (!x. op = Var x ==> not_fresh_at sb x) /\
      dt = lowered_value_type cenv e /\ ptr_val_ok cx dt v op G tn t /\
      ptr_mem_ok cx dt v op G tn t /\ ptr_buf_ok cenv e op G t /\
      (!w. eval_operand op t = SOME w /\ type_memory_bytes cenv dt <> 0 ==>
           w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next) /\
      (?w aid tv. eval_operand op t = SOME w /\
        evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
        val_wf tv v /\ FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
        aid < sb.cs_next_id /\
        (!n b sz. local_region cenv ee.scopes t n b sz ==>
          regions_disjoint (w2n w) (type_memory_size tv) b sz)))
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`vv`,`sm`,`shadow_sm`]
    (map_every assume_tac o CONJUNCTS)) ext_kw_default_compile_cut >>
  Cases_on `compile_alloc_buffer (type_memory_bytes cenv dt) sm` >>
  rename1 `compile_alloc_buffer _ sm = (buf,sn)` >>
  Cases_on `unwrap_value cenv vv sn` >>
  rename1 `unwrap_value cenv vv sn = (srcop,sc)` >>
  Cases_on `compile_store_memory cenv srcop buf.buf_operand dt dt sc` >>
  qpat_x_assum `compile_materialize_vv _ _ _ sm = _` mp_tac >>
  simp[compile_materialize_vv_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
  disch_then strip_assume_tac >> gvs[] >>
  rename1 `compile_store_memory _ srcop _ _ _ sc = ((),sb)` >>
  `ci_mono sa sm` by
    (qspecl_then [`cenv`,`expr_type e`,`e`,`sa`] mp_tac (cj 1 ci_mono_compile_expr_sa) >> simp[]) >>
  `ci_mono sm sn` by
    (qspecl_then [`type_memory_bytes cenv (lowered_value_type cenv e)`,`sm`]
      mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono sn sc` by (qspecl_then [`cenv`,`vv`,`sn`] mp_tac ci_mono_unwrap_value >> simp[]) >>
  `ci_mono sc sb` by
    (qpat_assum `compile_store_memory _ _ _ _ _ sc = _`
       (SUBST1_TAC o SYM o SRULE [] o AP_TERM ``SND : unit # compile_state -> compile_state``) >>
     simp[ci_mono_compile_store_memory]) >>
  `cs_extends sn sb` by (irule cs_extends_trans >> qexists `sc` >> fs[ci_mono_def]) >>
  `fn_has_code sm sn func /\ fn_has_code sn sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `fn_has_code sn sc func /\ fn_has_code sc sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  suspend "child"
QED

Resume ext_kw_default_head_mods[child]:
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_assum `body_expr_full_ok_mods mods exps cx e`
       (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
     qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                   _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _`
       (FIRST o map irule o CONJUNCTS o REWRITE_RULE [IMP_CONJ_THM] o SPEC_ALL) >>
     asm_rewrite_tac[] >> conj_tac >- (qexistsl [`src`,`tops`] >> simp[]) >>
     qexists `env` >> simp[]) >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ Q R` >>
  irule ext_kw_default_read_cut_mods >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result _ v)`]
  >- simp[storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G tn s. childQ H res ee G tn s /\ s.vs_labels = s0.vs_labels /\
    ee.gas_obs = [] /\ ~s.vs_halted` >>
  (reverse conj_tac >- (irule gas_outcome_full_mods_post_source >>
    qexists_tac `\H res ee G tn s. childQ H res ee G tn s /\ s.vs_labels = s0.vs_labels` >>
    qexists_tac `childR` >>
    simp[] >> conj_tac
    >- (rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`,Abbr `R`,expr_exit_def] >>
        ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
          INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
    irule gas_outcome_full_mods_post_path >>
    qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
    rpt strip_tac >> drule_then strip_assume_tac gas_origin_ptr_path_projections >>
    drule_then (mp_tac o MATCH_MP fragGasPathFrameMemTheory.gas_path_code_labels) gas_path_ptr_erase >> simp[])) >>
  suspend "read"
QED

Resume ext_kw_default_head_mods[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (assume_tac o BETA_RULE) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >> asm_rewrite_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv s /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> (?r. _ = INL r /\ _) /\ _`
       (qspec_then `H` (drule_then (strip_assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11]))) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     Cases_on `vv` >- fs[vv_holds_mods_def,vv_holds_def] >>
     rename1 `LocatedValue tag p` >> Cases_on `p.ptr_location = LocCode`
     >- fs[vv_holds_mods_def,immutable_holds_mods_def,immutable_holds_def] >>
     fs[vv_holds_mods_def] >> drule_then strip_assume_tac attribute_vv_holds_read_operand >> simp[]) >>
  disj1_tac >> qexists `tv` >> simp[] >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)` by
    simp[vyperStateTheory.bind_def] >>
  drule_all_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choosel_then [`ptv`,`ltv`] (map_every assume_tac o CONJUNCTS))))
    copy_read_physical_type_gas_obs_mods >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    (qhdtm_assum `expr_body_pre_mods` (strip_assume_tac o REWRITE_RULE [expr_body_pre_mods_def]) >>
     irule copy_lowered_fits_mods >> qexistsl [`cx`,`env`,`es`,`mods`] >> simp[]) >>
  `~is_word_type (lowered_value_type cenv e)` by metis_tac[arg_type_fits_word_type] >>
  `type_memory_size ltv < 2 ** 64` by
    (`alloc_limits_expr cenv e` by fs[expr_body_pre_mods_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def] >> strip_tac >>
     `type_memory_bytes cenv (lowered_value_type cenv e) <= type_memory_bytes cenv (expr_type e)` by
       (irule (cj 1 abi_args_fits_memory_bytes) >> simp[]) >>
     fs[] >> decide_tac) >>
  `type_memory_size ltv + 64 < dimword (:256) /\ type_memory_size ltv < dimword (:256)` by
    (qpat_assum `type_memory_size ltv < 2 ** 64` mp_tac >>
     simp[NoAsms,dimword_def] >> decide_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
   sa.cs_next_var <= sc.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    (conj_tac >> irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[] >> decide_tac) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (qpat_assum `compile_expr cenv (expr_type e) e sa = (vv,sm)`
       (mp_then Any mp_tac (cj 1 compiler_compile_var)) >> simp[]) >>
  `compile_alloc_buffer (type_memory_size ltv) sm = (buf,sn)` by
    (qpat_assum `type_memory_bytes _ _ = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `sm.cs_next_id < sn.cs_next_id` by
    (qpat_assum `compile_alloc_buffer (type_memory_size ltv) sm = (buf,sn)`
       (mp_then Any mp_tac compile_alloc_buffer_parts) >> simp[]) >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    (drule_then mp_tac eval_expr_preserves_scopes_dom >> simp[]) >>
  `?obs. ee.storage_trace = es.storage_trace ++ obs` by
    (qpat_assum `eval_expr _ _ _ = (INL tv,ee)` (mp_then Any mp_tac storage_trace_frame_prefix) >>
     simp[evaluate_storage_trace_frame]) >>
  `storage_trace_domain cx st0 es.storage_trace` by
    metis_tac[storage_trace_domain_prefix] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s0` by
    (qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ es s0 /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >> fs[storage_trace_domain_def]) >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
    ext_kw_default_alloc_mods) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`q`,`dw`,`u`,`Ga`,`ta`] (map_every assume_tac o CONJUNCTS))) >>
  `!tag x. vv = StackValue tag x ==> ptr_buf_ok cenv e x G s` by simp[] >>
  drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ s`)
    ext_kw_default_alloc_unwrap_resources_mods >>
  disch_then drule_all >> disch_then strip_assume_tac >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `src` |-> `srcop`, `ty` |-> `expr_type e`,
                  `gs` |-> `gas_explicit marks s0.vs_gas_readings`,
                  `Gi` |-> `G0`, `ti` |-> `tn0`, `n` |-> `type_memory_size ltv`,
                  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    ext_kw_default_unwrap_entry_mods) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`,`sw`] (map_every assume_tac o CONJUNCTS)) >>
  `compile_store_memory cenv srcop (Var q) (lowered_value_type cenv e)
     (lowered_value_type cenv e) sc = ((),sb)` by
    (qpat_assum `buf.buf_operand = Var q` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  drule_at (Pat `compile_store_memory _ _ (Var _) _ _ _ = _`)
    ext_kw_default_store_path_mods >>
  disch_then drule_all >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
    (qx_choosel_then [`t`,`Gfin`,`tt`] (map_every assume_tac o CONJUNCTS))) >>
  `z.vs_labels = s0.vs_labels` by
    (`u.vs_labels = s.vs_labels` by
      (qpat_assum `u with <| vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _ |> = s` (SUBST1_TAC o SYM) >> simp[]) >>
     simp[]) >>
  `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==> FLOOKUP s.vs_allocas aid = SOME ent` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ s`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >> first_assum ACCEPT_TAC) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[] >> metis_tac[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists `sa` >> simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `src` |-> `srcop`, `dt` |-> `lowered_value_type cenv e`,
                  `Gi` |-> `G0`, `ti` |-> `tn0`,
                  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    ext_kw_default_owned_landing_mods) >>
  (impl_tac >- (asm_rewrite_tac[] >>
    qpat_assum `t.vs_current_bb = sb.cs_current_bb` mp_tac >> asm_rewrite_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "land"
QED

Resume ext_kw_default_head_mods[land]:
  irule gas_outcome_full_mods_pure >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`Gfin`,`ee`,`INL v`,`t`,`tt`] >> conj_tac
  >- (drule_then ACCEPT_TAC read_result_gas_obs) >>
  qx_gen_tac `H` >> disch_tac >> conj_tac
  >- (irule gas_origin_ptr_path_trans >> qexistsl_tac [`Ga`,`u`,`ta`] >>
      conj_tac >- first_assum (qspec_then `DF H` ACCEPT_TAC) >>
      irule gas_origin_ptr_path_trans >> qexistsl_tac [`Gz`,`z`,`tz`] >>
      conj_tac >> first_assum (qspec_then `DF H` ACCEPT_TAC)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ ee t /\ _`
    (drule_then strip_assume_tac) >>
  simp[Abbr `Q`] >> conj_tac
  >- (`t.vs_alloca_next = z.vs_alloca_next` by
        (qhdtm_assum `typed_copy_state_frame`
          (mp_tac o REWRITE_RULE [typedMemoryCopyTheory.typed_copy_state_frame_def]) >>
         simp[NoAsms,venomStateTheory.venom_state_component_equality]) >>
      qpat_assum `w2n dw + type_memory_size ltv <= z.vs_alloca_next` mp_tac >>
      qpat_assum `t.vs_alloca_next = z.vs_alloca_next` SUBST1_TAC >>
      ntac 2 disch_tac >> once_rewrite_tac [arithmeticTheory.ADD_COMM] >>
      first_assum ACCEPT_TAC) >>
  qexists_tac `sm.cs_next_id` >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise ext_kw_default_head_mods
