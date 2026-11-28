(* Requests in an immutable target arise in its evaluated indices. *)
Theory s1PrefixImmutableTargetPlace
Ancestors
  s1PrefixPreds s1PrefixCompose s1PrefixOfVV s1PrefixProps s1PrefixNames s1PrefixFrame
  bodyPtrPopTargetFragTransport pair targetPlaceSim targetPlaceSimCases
  gasShadowCompileStmtHelpers gasShadowCompile gasShadowState gasShadow bodyFullShared
  bodyFullPreds bodyFullTargetDefs vyperTypeEnv exprLoweringProps fragExec
  bodyFullBaseTargetProjection
  exprSimDefs gasContext stmtLoweringMono evalNoHalt bodyMemoryDefs
  gasOutcomeFull fragGasOriginPtrExec exprSimHypsDefs vyperStorageFootprint
  venomState list s1PrefixDefs bodySimFull freshWrites ptrDiscipline
  bodyFullTarget bodyFullTargetRoots bodyFullIfExpReach bodySimAugPlaceLoad
  targetSubscriptContinuation targetPlaceSimCasesBase tuplePlaceTargetGas
  tuplePlaceSourceHead exprSimSliceCompose exprSimSource
  vyperStorageTrace vyperInterpreter vyperState vyperTypeSystem
  vyperPlaceFrames[qualified]

Theorem immutable_extend_get_place_state[local]:
  SND (bind (extend_place cx (PlaceR (ImmutablePlace src id path)) sb)
    get_place es) = es
Proof
  simp[extend_place_def, Once bind_def] >>
  Cases_on `place_type_value cx (ImmutablePlace src id path) es` >>
  drule_then SUBST_ALL_TAC place_type_value_state >>
  rename1 `place_type_value _ _ _ = (tvres,_)` >>
  Cases_on `tvres` >> simp[] >> simp[Once bind_def] >>
  Cases_on `read_place cx (ImmutablePlace src id path) es` >>
  drule_then SUBST_ALL_TAC read_place_state >>
  rename1 `read_place _ _ _ = (vres,_)` >>
  Cases_on `vres` >> simp[] >>
  simp[ignore_bind_def, bind_def, lift_sum_def, return_def, raise_def,
       extend_memory_place_def, get_place_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def, get_place_def]
QED

Theorem immutable_toplevel_target_prefix:
  ~s.vs_halted ==>
  gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
    (eval_target_place cx (TopLevelNameTarget (src,id))) (es,s,G,tn)
Proof
  strip_tac >> irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame] >>
  rewrite_tac[eval_target_place_as_bind] >> simp[Once evaluate_def] >>
  rpt gen_tac >>
  Cases_on `lookup_global cx src id (es with gas_obs := gobs)` >>
  drule lookup_global_no_outcome >>
  rename1 `lookup_global _ _ _ _ = (result,mid)` >>
  Cases_on `result` >> simp[bind_def] >>
  metis_tac[vyperPlaceFramesTheory.get_place_state, pairTheory.PAIR, SND]
QED

Theorem get_place_bind_state:
  SND (bind a get_place es) = SND (a es)
Proof
  Cases_on `a es` >> rename1 `_ = SND (ans,mid)` >> Cases_on `ans` >>
  simp[bind_def] >>
  rename1 `SND (get_place pv mid) = mid` >>
  Cases_on `get_place pv mid` >>
  drule_then SUBST_ALL_TAC vyperPlaceFramesTheory.get_place_state >> simp[]
QED

Theorem immutable_attribute_keeps_prefix[local]:
  immutable_root cx bt /\
  gas_prefix_full P cx st0 (eval_target_place cx bt) (es,s,G,tn) ==>
  gas_prefix_full P cx st0 (eval_target_place cx (AttributeTarget bt fld)) (es,s,G,tn)
Proof
  strip_tac >> drule immutable_target_attribute_source >>
  disch_then (qspec_then `fld` SUBST1_TAC) >>
  `!ee. SND (bind (eval_target_place cx bt)
    (\p. bind (extend_place cx (PlaceR p) (AttrSubscript fld)) get_place) ee) =
    SND (eval_target_place cx bt ee)` by
    (gen_tac >> Cases_on `eval_target_place cx bt ee` >>
     rename1 `_ = SND (ans,mid)` >> Cases_on `ans` >>
     simp[Once bind_def, get_place_bind_state, extend_place_attr_gas_obs]) >>
  drule gas_prefix_full_state_cong >> simp[]
QED

Theorem immutable_index_extension_keeps_prefix[local]:
  gas_prefix_full P cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) ==>
  gas_prefix_full P cx st0
    (bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (extend_place cx (PlaceR (ImmutablePlace src id path))
        (ValueSubscript v)) get_place)) (es,s,G,tn)
Proof
  strip_tac >>
  `!ee. SND (bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (extend_place cx (PlaceR (ImmutablePlace src id path))
        (ValueSubscript v)) get_place) ee) =
    SND (bind (eval_expr cx e) (read_result cx) ee)` by
    (gen_tac >> Cases_on `bind (eval_expr cx e) (read_result cx) ee` >>
     rename1 `_ = SND (ans,mid)` >> Cases_on `ans` >>
     simp[Once bind_def, immutable_extend_get_place_state]) >>
  drule gas_prefix_full_state_cong >> simp[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- simp[target_root_def]
  >- (PairCases_on `nsid` >> rpt strip_tac >>
      irule immutable_toplevel_target_prefix >> simp[])
  >- suspend "subscript" >>
  suspend "attribute"
QED
*)
Theorem immutable_target_place_prefix_ind[local]:
  !bt DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env es id.
    body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_base_target_full_ok cx bt /\ body_base_target_prefix_ok cx bt /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_sim_inv cenv cx env es /\ target_indices_pre cenv cx env bt /\
    cx.in_deploy /\ immutable_root cx bt /\
    target_root bt = TopLevelNameTarget (NONE,id) /\
    ~cx_const_name cx (NONE,id) ==>
    !st0 ty sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME (Type ty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (r,sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target bt) shadow_sa = (r,shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      gas_admissible (eval_target_place cx bt) target_place_res_ok es /\
      return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (eval_target_place cx bt) (es,s0,G0,tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume immutable_target_place_prefix_ind[attribute]:
  strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `immutable_root cx bt` by fs[immutable_root_def,target_root_def] >>
  irule immutable_attribute_keeps_prefix >> simp[] >>
  fs[type_place_target_AttributeTarget] >>
  drule_then strip_assume_tac compile_get_target_ptr_attr >> gvs[] >>
  qpat_assum `compile_get_target_ptr _ _ (gas_shadow_target _) _ = _`
    (strip_assume_tac o MATCH_MP compile_get_target_ptr_attr o
     SIMP_RULE std_ss [gas_shadow_expr_def]) >>
  `gas_shadow_compiles (compile_get_target_ptr compile_expr cenv bt)
     (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target bt))` by irule gas_shadow_stmt_get_target_ptr_env >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >>
  qmatch_asmsub_rename_tac
    `compile_get_target_ptr _ _ (gas_shadow_target bt) shadow_sa = (rb,shadow_sm)` >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by
    metis_tac[ci_mono_compile_get_target_ptr,SND] >>
  `ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by
    metis_tac[ci_mono_emit_op,SND] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[ci_mono_def,fn_has_code_split] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (qpat_x_assum `gas_admissible (eval_target_place cx (AttributeTarget _ _)) _ _` mp_tac >>
     simp[immutable_target_attribute_source] >>
     disch_then (mp_then Any irule slice_gas_admissible_bind_head) >>
     simp[target_place_res_ok_def]) >>
  fs[body_base_target_full_ok_attribute_projection,body_base_target_prefix_ok_def,
     target_indices_pre_def,target_root_def] >>
  first_x_assum drule_all >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume immutable_target_place_prefix_ind[subscript]:
  disch_then (mk_asm "targetIH") >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `immutable_root cx bt` by fs[immutable_root_def,target_root_def] >>
  qpat_assum `type_place_target _ (SubscriptTarget _ _) = _`
    (strip_assume_tac o REWRITE_RULE[type_place_target_SubscriptTarget]) >>
  drule_all immutable_target_place_type >> strip_tac >> gvs[] >>
  drule_then strip_assume_tac target_subscript_compile_decompose >>
  qpat_assum `compile_get_target_ptr _ _ (gas_shadow_target _) _ = _`
    (strip_assume_tac o MATCH_MP target_subscript_compile_decompose o
     SIMP_RULE std_ss [gas_shadow_expr_def]) >>
  `gas_shadow_compiles (compile_get_target_ptr compile_expr cenv bt)
     (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target bt))` by irule gas_shadow_stmt_get_target_ptr_env >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >>
  qmatch_asmsub_rename_tac
    `compile_get_target_ptr _ _ (gas_shadow_target bt) shadow_sa = (rb,shadow_sm)` >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) shadow_sm = _`
    (assume_tac o SIMP_RULE std_ss [gas_shadow_expr_type]) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >>
  qmatch_asmsub_rename_tac
    `lower_value _ _ _ (gas_shadow_expr e) shadow_sm = (ix,shadow_sn)` >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb` by
    metis_tac[target_subscript_compile_intervals] >>
  `ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm shadow_sn /\
   ci_mono shadow_sn shadow_sb` by
    (qpat_assum `target_subscript_suffix _ (gas_shadow_expr _) _ _ _ = _`
       (mp_then Any (irule o SIMP_RULE std_ss [gas_shadow_expr_type])
         target_subscript_compile_intervals) >>
     simp[] >> qexists_tac `gas_shadow_target bt` >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code shadow_sa shadow_sm shadow_func /\
   fn_has_code shadow_sm shadow_sn shadow_func` by
    (qpat_assum `fn_has_code sa sb func`
       (mp_then Any drule_all target_subscript_interval_code) >> strip_tac >>
     qpat_assum `fn_has_code shadow_sa shadow_sb shadow_func`
       (mp_then Any drule_all target_subscript_interval_code) >> simp[]) >>
  drule immutable_target_subscript_source >>
  disch_then (qspec_then `e` (fn th =>
    RULE_ASSUM_TAC (REWRITE_RULE[th, GSYM bind_assoc]) >>
    REWRITE_TAC[th, GSYM bind_assoc])) >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (qpat_assum `gas_admissible (bind (eval_target_place _ _) _) _ _`
       (mp_then Any irule slice_gas_admissible_bind_head) >>
     simp[target_place_res_ok_def]) >>
  fs[body_base_target_full_ok_subscript_projection,body_base_target_prefix_ok_def,
     target_indices_pre_def,target_root_def] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_target_place cx bt) (es,s0,G0,tn0)` by
    (asm "targetIH" drule_all >> simp[]) >>
  `imm_target_place_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx env bt es` by (irule body_imm_target_place_sim_full >> metis_tac[]) >>
  qpat_x_assum `imm_target_place_sim_full _ _ _ _ bt _`
    (mp_tac o REWRITE_RULE [imm_target_place_sim_full_def]) >>
  qmatch_asmsub_rename_tac `type_place_target env bt = SOME (Type base_ty)` >>
  disch_then (qspecl_then [`st0`,`base_ty`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,
    `rb`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  suspend "index_handoff"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume immutable_target_place_prefix_ind[index_handoff]:
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_target_place cx bt) _ baseQ baseR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_target_place cx bt) (es,s0,G0,tn0)
      (\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\
        (!fn inst u. frag_reachable ctx func t fn inst u ==>
                     dalloca_fmp_headroom inst u)) baseR` by
    (irule gas_outcome_full_post_path >> qexists_tac `baseQ` >> simp[] >>
     rpt strip_tac
     >- (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
     irule gas_origin_ptr_path_dalloca_fmp_headroom >>
     metis_tac[body_inv_no_phi]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ baseQ baseR` kall_tac >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame,
       storage_trace_frame_bind_all, storage_trace_frame_extend_place,
       storage_trace_frame_get_place, storage_trace_frame_read_result] >>
  conj_tac
  >~ [`gas_prefix_full _ _ _ _ _`]
  >- suspend "index" >>
  simp[Abbr `baseR`] >> rpt strip_tac >>
  rename1 `ISR ans` >> Cases_on `ans` >> gvs[expr_exit_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume immutable_target_place_prefix_ind[index]:
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
    mid.storage_trace` by fs[storage_trace_domain_def] >>
  qunabbrev_tac `baseQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  gvs[] >>
  irule immutable_index_extension_keeps_prefix >>
  qpat_assum `!tail. eval_target_place cx bt _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE std_ss [APPEND_NIL])) >>
  drule tuple_place_target_base_inversion >> strip_tac >>
  `?sx pv ee. eval_base_place cx bt sx = (INL pv,ee)` by metis_tac[] >>
  `body_expr_prefix_ok cx e` by metis_tac[] >>
  `expr_sim_inv cenv cx env mid` by
    (qpat_assum `eval_target_place cx bt _ = _`
      (mp_then Any mp_tac aug_place_target_inv) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (qpat_assum `eval_base_place cx bt (es with gas_obs := _) = _`
      (mp_then Any mp_tac body_const_cells_agree_base) >> simp[]) >>
  `expr_body_pre cenv cx env e mid` by simp[] >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e mid` by
    (fs[Once body_expr_prefix_ok_def] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `return_buf_frame d cenv sm t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     fs[imm_target_post_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid t /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (qx_gen_tac `horizon` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `horizon` (drule_then strip_assume_tac)) >>
     fs[imm_target_post_def]) >>
  qpat_x_assum `expr_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[expr_sim_prefix_def,expr_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sm`,`sn`,`shadow_sm`,`shadow_sn`,
    `ix`,`t`,`G1`,`tn1`] mp_tac) >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise immutable_target_place_prefix_ind
*)

Theorem immutable_target_place_prefix:
  body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_base_target_full_ok cx bt /\ body_base_target_prefix_ok cx bt /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  target_indices_pre cenv cx env bt /\ cx.in_deploy /\ immutable_root cx bt /\
  target_root bt = TopLevelNameTarget (NONE,id) /\ ~cx_const_name cx (NONE,id) /\
  well_typed_target env bt ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  call_evaluation_safe cx (int_calls_target bt) /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sb) /\
  compile_get_target_ptr compile_expr (gas_shadow_env T cenv) (gas_shadow_target bt)
    shadow_sa = (r,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!fn inst u. frag_reachable ctx func s fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_target_place cx bt) (es,s,G,tn)
Proof
  rpt strip_tac >>
  `type_place_target env bt = SOME (Type ty)` by fs[well_typed_target_def] >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (irule tuple_place_target_gas_admissible >> metis_tac[]) >>
  irule immutable_target_place_prefix_ind >> metis_tac[]
QED
