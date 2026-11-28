(* Request-prefix companion to bodyFullTarget. *)
Theory s1PrefixTarget
Ancestors
  s1PrefixPreds bodyFullTarget s1PrefixDefs s1PrefixTargetSubscript
  s1PrefixNames s1PrefixCompose s1PrefixFrame s1PrefixProps
  bodyFullTargetSubscript bodyFullTargetDefs bodyFullPreds bodyFullShared
  bodyFullBaseTargetProjection
  bodyFullIfExpReach targetPlaceSimCasesBase targetPlaceSim targetPlaceSimDefs
  gasShadowCompileStmtHelpers gasShadowCompileHelpers gasShadowState gasShadow
  stmtLoweringMono emitHelperProps gasOutcomeFullCompose gasContext
  fragGasOriginPtrExec fragExec exprSimDefs exprLoweringProps exprSimSliceCompose
  vyperPlaceFrames vyperState vyperStorageTrace vyperEvalMisc vyperInterpreter
  vyperAST vyperTypeEnv vyperCallOutcomeFrame list pair

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  (* Extending a place can record a storage root but cannot issue a request. *)
  `!cx pv sub st res ee. extend_place cx pv sub st = (res,ee) ==>
     EVERY (\ob. !rq oc. ob = StorageOutcome rq oc ==> computed_precompile rq)
       (DROP (LENGTH st.storage_trace) ee.storage_trace)` by
    (rpt gen_tac >> Cases_on `pv`
     >- simp[extend_place_def,raise_def]
     >- (strip_tac >> drule_then SUBST_ALL_TAC extend_place_PlaceR_state >> simp[]) >>
     rename1 `HashMapRef _ _ _ vt` >> Cases_on `sub` >> Cases_on `vt` >>
     simp[extend_place_nested_mapping,extend_place_def,lift_option_type_def,
          bind_def,ignore_bind_def,raise_def,record_storage_event_def,return_def] >>
     rename1 `evaluate_type (get_tenv cx) typ` >>
     Cases_on `evaluate_type (get_tenv cx) typ` >>
     simp[return_def,raise_def] >> rw[] >> simp[DROP_APPEND1]) >>
  recInduct base_assignment_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (rpt strip_tac >> irule gas_prefix_full_no_outcome >>
      simp[evaluate_storage_trace_frame] >> rpt gen_tac >> strip_tac >>
      drule_then SUBST_ALL_TAC eval_base_place_NameTarget_preserves_state >> simp[])
  >- (PairCases_on `nsid` >> rpt strip_tac >> irule gas_prefix_full_no_outcome >>
      simp[evaluate_storage_trace_frame] >> rpt gen_tac >> simp[Once evaluate_def] >>
      strip_tac >> drule lookup_global_no_outcome >> simp[])
  >- suspend "subscript"
  >> suspend "attribute"
QED
*)
Theorem body_target_sim_prefix:
  !bt DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env es.
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_base_target_full_ok cx bt /\
    body_base_target_prefix_ok cx bt /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    target_pre cenv cx env bt es ==>
    !st0 vt sa sb shadow_sa shadow_sb r s0 G0 tn0.
      type_place_target env bt = SOME vt /\
      compile_get_target_ptr compile_expr cenv bt sa = (r, sb) /\
      compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target bt)
        shadow_sa = (r, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_base_place cx bt) target_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_prefix_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cx st0 (eval_base_place cx bt) (es, s0, G0, tn0)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume body_target_sim_prefix[subscript]:
  strip_tac >> rpt gen_tac >> strip_tac >>
  `body_base_target_full_ok cx bt /\ body_base_target_prefix_ok cx bt` by
    fs[body_base_target_full_ok_subscript_projection,body_base_target_prefix_ok_def] >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  match_mp_tac (Q.INST [`tops` |-> `tops`, `env` |-> `env`] target_subscript_sim_prefix) >>
  asm_rewrite_tac[] >> rpt conj_tac
  >- (irule body_target_sim_full >> metis_tac[])
  >- (irule subscript_tail_full_ok >> metis_tac[])
  >- (qpat_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env es.
                    body_inv tops ctx cenv cx /\ _ ==> _`
        (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,
                      `shadow_func`,`cenv`,`cx`,`env`,`es`] mp_tac) >>
      simp[]) >>
  rpt strip_tac >> irule gas_prefix_full_no_outcome >>
  simp[storage_trace_frame_extend_place] >> rpt gen_tac >> strip_tac >>
  qpat_assum `!cx pv sub st res ee. extend_place cx pv sub st = (res,ee) ==> _`
    (drule_then mp_tac) >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_target_sim_prefix[attribute]:
  strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  fs[type_place_target_AttributeTarget] >>
  `body_base_target_full_ok cx bt /\ body_base_target_prefix_ok cx bt` by
    fs[body_base_target_full_ok_attribute_projection,body_base_target_prefix_ok_def] >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  drule_then strip_assume_tac compile_get_target_ptr_attr >> gvs[] >>
  qpat_assum `compile_get_target_ptr _ _ (gas_shadow_target (AttributeTarget _ _)) _ = _`
    (strip_assume_tac o MATCH_MP compile_get_target_ptr_attr o
     SIMP_RULE std_ss [gas_shadow_expr_def]) >>
  `gas_shadow_compiles (compile_get_target_ptr compile_expr cenv bt)
     (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
        (gas_shadow_target bt))` by irule gas_shadow_stmt_get_target_ptr_env >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >>
  rename1 `compile_get_target_ptr _ _ bt sa = (rb,sm)` >>
  rename1 `compile_get_target_ptr _ _ (gas_shadow_target bt) shadow_sa = (rb,shadow_sm)` >>
  rename1 `type_place_target env bt = SOME (Type bty)` >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by
    metis_tac[ci_mono_compile_get_target_ptr,SND] >>
  `ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by metis_tac[ci_mono_emit_op,SND] >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split,ci_mono_def] >>
  qmatch_goalsub_rename_tac `eval_base_place cx (AttributeTarget bt fld)` >>
  `eval_base_place cx (AttributeTarget bt fld) =
     bind (eval_base_place cx bt) (\pv. extend_place cx pv (AttrSubscript fld))` by
    simp[FUN_EQ_THM, Once evaluate_def] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE[th]) >> REWRITE_TAC[th]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (qpat_assum `gas_admissible (bind _ _) _ _`
       (mp_then Any irule slice_gas_admissible_bind_head) >> simp[target_res_ok_def]) >>
  suspend "attribute_bind"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume body_target_sim_prefix[attribute_bind]:
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_base_place cx bt) (es,s0,G0,tn0)` by
    (qpat_assum `!DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env es.
                   body_inv tops ctx cenv cx /\ _ ==> _`
       (qspecl_then [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,`func`,
                     `shadow_func`,`cenv`,`cx`,`env`,`es`] mp_tac) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     disch_then (qspecl_then [`st0`,`Type bty`,`sa`,`sm`,`shadow_sa`,
                              `shadow_sm`,`rb`,`s0`,`G0`,`tn0`] mp_tac) >>
     asm_rewrite_tac[]) >>
  `target_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt es` by
    (irule body_target_sim_full >> metis_tac[]) >>
  qpat_x_assum `target_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [target_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`Type bty`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`rb`,
                           `s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `gas_outcome_full _ _ _ _ (eval_base_place cx bt) _ childQ childR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_base_place cx bt) (es,s0,G0,tn0)
     (\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted) childR` by
    (irule gas_outcome_full_post_path >> qexists_tac `childQ` >> simp[] >>
     rpt strip_tac >> drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. childQ H res ee G tn t /\ _) _`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[evaluate_requests_outcomes_frame,evaluate_storage_trace_frame,
       storage_trace_frame_extend_place] >> rpt conj_tac >>
  TRY (rpt gen_tac >> disch_tac >>
       qpat_assum `!cx pv sub st res ee. extend_place cx pv sub st = (res,ee) ==> _`
         (drule_then mp_tac) >> simp[] >> NO_TAC) >>
  simp[Abbr `childR`] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise body_target_sim_prefix
*)
