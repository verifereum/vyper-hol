(* The neutral selected-endpoint preparation used by the runtime full
   simulation and the request-prefix simulation. The theories check local
   instances, so the full simulation does not publish another interface. *)
structure runtimeBodyEndpointPrepareLib =
struct
open HolKernel boolLib bossLib
open bodyFullShadowBodyInvLoweringTheory
     sourceUnitExecutionTheory e2eDefsTheory compileVyperTheory vyperInterpreterTheory vyperStateTheory
     vyperStorageFootprintTheory gasShadowUnitTheory vyperTypeSelectedEntrySoundnessTheory
     externalEntryValueRevertTheory unitExecutionComposeTheory externalEntryJointTheory entryDispatchPropsTheory
     gasShadowRunLoweringTheory gasShadowUnitGuardsTheory fragGasOriginPtrExecTheory
     runtimeEntryEndpointTheory runtimeBodyStartDefsTheory externalEntryBoundTheory
     externalBodyFrameTheory externalFrameRetOkTheory runtimeBodyShadowTheory externalBodySupportTheory
     externalReturnPackageTheory compileEnvTheory
     exprSimHypsDefsTheory vyperTypeInvariantsTheory
     stmtSimPropsTheory stmtsEnvRetTyTheory gasSummaryTheory
     constSubstTheory constSubstStmtsPreserveTheory
     externalCallSelectedTheory externalBodySourceOkTheory bodySimFullMainTheory bodySimFullTheory bodyFullPredsTheory
     entryStateRelTheory entryReachBodyFmpTheory entryReachBodyRuntimeResourcesTheory
     bodyAbiDecodeTargetTheory rawReturnHeaderTheory loweringHaltTheory gasContextTheory bodyPtrDefsTheory
     gasOutcomeFullTheory fragGasOriginPtrTheory loweringPostsTheory stmtSimDefsTheory exprSimDefsTheory
     exprLoweringPropsTheory vyperStorageTraceTheory vyperStorageBackendTheory vyperCallTheory
     fragExecTheory moduleLoweringTheory fragGasOriginTheory fragFuelUnitTheory passSimulationDefsTheory
     acceptedContextPhiTheory vyperLoweringCorrectTheory typedCopyProducerTheory
     deployBodyReachabilityTheory contextRawReachableTheory contextCodegenRelTheory unitTransformDefsTheory
     venomInstTheory venomStateTheory ptrDisciplineTheory listTheory
     supportedProgramTheory

fun headroom_tm () = ``
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
  fn_entry_label func = SOME "__entry" /\
  gas_path unit.cu_context func
    (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0|>) n (OK s0) /\
  (ctx_has_dalloca unit.cu_context ==>
    !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
      dalloca_fmp_headroom inst s) ==>
  !fn inst s. frag_reachable unit.cu_context func s0 fn inst s ==>
    dalloca_fmp_headroom inst s``;

fun headroom_cases_tac () = strip_tac >> Cases_on `ctx_has_dalloca unit.cu_context`;
fun headroom_present_tac () =
  `!bb label. lookup_block label func.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> drule_all lower_vyper_runtime_unit_block_phi >> simp[]) >>
  `?bb. lookup_block "__entry" func.fn_blocks = SOME bb` by
    (Cases_on `func.fn_blocks` >>
     fs[fn_entry_label_def, entry_block_def, lookup_block_def, FIND_thm]) >>
  qabbrev_tac `entry = vs with <|vs_prev_bb := NONE;
    vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `phi_prefix_length bb.bb_instructions = 0` by metis_tac[] >>
  `enters_block func entry entry` by
    simp[enters_block_def, Abbr `entry`, eval_phis_no_phi, venom_state_fupdfupds] >>
  `!i. active_inst func i entry ==> raw_reachable vs unit.cu_context func i entry` by
    (rpt strip_tac >> irule raw_reachable_entry >> fs[Abbr `entry`]) >>
  `!i. active_inst func i s0 ==> raw_reachable vs unit.cu_context func i s0` by
    (rpt strip_tac >>
     qpat_assum `gas_path _ _ entry n (OK s0)` (fn path =>
       irule raw_reachable_gas_path >> irule_at Any path >> simp[] >>
       first_assum ACCEPT_TAC)) >>
  rpt strip_tac >>
  `raw_reachable vs unit.cu_context fn inst s` by
    (drule raw_reachable_through_fragment >>
     disch_then (qspec_then `vs` irule) >> first_assum ACCEPT_TAC) >>
  metis_tac[];
fun headroom_absent_tac () =
  rpt strip_tac >>
  `MEM func unit.cu_context.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  drule_then drule frag_reachable_members >> strip_tac >>
  `inst.inst_opcode <> DALLOCA` by
    (fs[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]) >>
  simp[dalloca_fmp_headroom_def];

fun package_source_tm () = ``
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,ret,subst_consts_stmts E source_body)) =
    (lbl,ce,pos_args,min_cds,pay,nr',key,tr,view,
     subst_consts_stmts E source_body,rt) ==>
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut,nr,rr,name,args,defaults,ret,source_body)) =
    (lbl,ce,pos_args,min_cds,pay,nr',key,tr,view,source_body,rt)``;
fun package_source_tac () =
  simp[package_external_fn_def, set_external_package_target_def,
       build_compile_env_subst_consts_stmts] >>
  strip_tac >> gvs[];

fun lock_inv_tm () = ``
  lock_if_nr cx nr iv es = (INL (),es_lock) /\ expr_sim_inv cenv cx env es ==>
  expr_sim_inv cenv cx env es_lock``;
fun lock_inv_tac () =
  strip_tac >> drule external_body_lock_frame >> strip_tac >>
  qpat_x_assum `expr_sim_inv _ _ _ _` mp_tac >>
  asm_simp_tac pure_ss [expr_sim_inv_def, state_well_typed_def, env_consistent_def,
    env_scopes_consistent_def, env_immutables_consistent_def] >> disch_then ACCEPT_TAC;

fun prepare_tm () = ``
  !tops rpolicy unit am tx ret vs mut nr args dflts fbody es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
    initial_venom_state_rel tops am tx vs /\
    outcomes_accounts_typed (SOME vs.vs_outcomes) /\
    (ctx_has_dalloca unit.cu_context ==>
      !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
        dalloca_fmp_headroom inst s) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut,nr,args,dflts,ret,fbody) /\
    runtime_body_endpoint tops rpolicy unit am tx vs es0 mut nr args dflts ret
      (subst_consts_stmts (module_consts_env tops []) fbody) ==>
    ?compiled_body cx entry shadow_unit explicit marks0 prefix func shadow_func
       cenv sa st' s0 G0 tn0.
      (compiled_body = subst_consts_stmts (module_consts_env tops []) fbody /\
       cx = initial_evaluation_context am.sources am.layouts tx NONE /\
       entry = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0|> /\
       explicit = gas_explicit_sites unit.cu_context shadow_unit.cu_context /\
       prefix = gas_explicit marks0 vs.vs_gas_readings /\
       runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
       gas_shadow_context unit.cu_context shadow_unit.cu_context /\
       gas_shadow_function func shadow_func /\
       MEM func unit.cu_context.ctx_functions /\
       MEM shadow_func shadow_unit.cu_context.ctx_functions /\
       unit.cu_context.ctx_entry = SOME "__entry" /\
       venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
       fn_entry_label func = SOME "__entry" /\
       (!gx. external_entry_bound tops am tx vs.vs_outcomes (prefix ++ gx)
                      mut args dflts (es0 with gas_obs := gx)) /\
       compile_guarded_body cenv nr global_nonreentrant_slot T (mut = View)
         compiled_body (if ret = NoneT then NONE else SOME ret) sa = ((),st') /\
       fn_has_code sa st' func /\
       ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
       s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
       s0.vs_gas_readings = DROP (LENGTH marks0) vs.vs_gas_readings /\
       (nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
               is_view_mut mut = (mut = View)) /\
       (nr ==> (!H : (bool # bytes32 # type_value) list # num list.
                 stmt_state_rel H unit.cu_context func cenv cx es0 s0 /\
                 ghost_inv H NONE cenv cx es0 G0 tn0 s0) /\
               (!D. gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
                 (entry,FEMPTY,entry_taint) marks0 (OK s0,G0,tn0))) /\
       storage_trace_domain cx (initial_state am []) es0.storage_trace /\
       (!H. valid_horizon cx (initial_state am []) H es0.storage_trace ==>
            gas_origin_ptr_path (cx_dead H cx,0,explicit,unit.cu_context,func,[])
              (entry,FEMPTY,entry_taint) marks0 (OK s0,G0,tn0))) /\
      !es_lock. lock_if_nr cx nr (is_view_mut mut) es0 = (INL (),es_lock) /\
               storage_trace_domain cx (initial_state am []) es_lock.storage_trace ==>
        ?bindings env_t env' sl sb shadow_sl shadow_sb s_b G_b tn_b cenv' RetQ.
          (RetQ = (\H v ee gt r. ?tv v' us.
            evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v = SOME v' /\
            unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),us) /\
            external_call_result_rel H tops ret tx
              (INL v', finalize_pending_deletions
                (abstract_machine_from_state am.sources am.exports am.layouts us),
               us.requests) r)) /\
          frame_ret_ok_full ((\H. cx_dead H cx),0,NONE,unit.cu_context,
            shadow_unit.cu_context,[],func,shadow_func) cx RetQ cenv ret /\
          external_entry_bound tops am tx vs.vs_outcomes (prefix ++ es0.gas_obs)
            mut args dflts es0 /\
          (!g. eval_stmts cx compiled_body (es_lock with gas_obs := g) =
               eval_stmts cx fbody (es_lock with gas_obs := g)) /\
          (nr /\ mut <> View ==> ~tx.is_static) /\
          cx_tops cx = tops /\ ~cenv.ce_is_ctor /\
          body_inv tops unit.cu_context cenv cx /\
          shadow_body_inv tops unit.cu_context shadow_unit.cu_context /\
          struct_args_unique tops /\ supported_stmts tops bindings compiled_body /\
          (!target. supported_stmts_expr_exists (expr_abi_decode_target_root target)
                 compiled_body ==> occurs_abi_decode_target target tops) /\
          body_const_cells_agree [(NONE,tops)] cx env_t es_lock /\
          expr_sim_inv cenv cx env_t es_lock /\ ce_locals_declared cenv env_t /\
          locals_alloc_ok cenv env_t /\ type_stmts env_t ret compiled_body = SOME env' /\
          stmts_exprs_ok cenv compiled_body /\
          call_evaluation_safe cx (int_calls_stmts compiled_body) /\
          (if nr then compile_nonreentrant_lock global_nonreentrant_slot T (mut = View)
           else comp_return ()) sa = ((),sl) /\
          compile_stmts cenv NoLoop (if ret = NoneT then BaseT BoolT else ret)
            compiled_body sl = ((),sb) /\
          stmts_env cenv NoLoop ret compiled_body sl = (cenv',sb) /\
          stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt compiled_body)
            shadow_sl = (gas_shadow_env T cenv',shadow_sb) /\
          gas_shadow_state sl shadow_sl /\ gas_shadow_state sb shadow_sb /\
          ctx_inst_ids_distinct unit.cu_context /\
          fn_has_code sl sb func /\ fn_has_code sb st' func /\
          fn_has_code shadow_sl shadow_sb shadow_func /\
          fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sl /\
          cenv.ce_return_pc = NONE /\ cenv.ce_return_buf = NONE /\
          ~block_is_terminated sl /\
          gas_admissible (eval_stmts cx compiled_body) (stmt_res_ok NoLoop) es_lock /\
          return_buf_frame NONE cenv sl s_b /\ alloca_history func s_b /\
          (ctx_has_dalloca unit.cu_context ==> allocas_below_fmp s_b) /\
          (!fn inst s. frag_reachable unit.cu_context func s_b fn inst s ==>
                      dalloca_fmp_headroom inst s) /\
          ~s_b.vs_halted /\ s_b.vs_current_bb = sl.cs_current_bb /\
          s_b.vs_inst_idx = LENGTH sl.cs_current_insts /\
          s_b.vs_gas_readings = DROP (LENGTH marks0) vs.vs_gas_readings /\
          s_b.vs_code = vs.vs_code /\ s_b.vs_labels = vs.vs_labels /\
          !H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
            stmt_state_rel H unit.cu_context func cenv cx es_lock s_b /\
            storage_well_formed_on cx es_lock (FST H) /\
            ghost_inv_at (cx_dead H cx) 0 NONE cenv cx es_lock G_b tn_b s_b /\
            gas_origin_ptr_path (cx_dead H cx,0,explicit,unit.cu_context,func,[])
              (entry,FEMPTY,entry_taint) marks0 (OK s_b,G_b,tn_b) /\
            ((!fuel. ptr_safe_run (cx_dead H cx) 0 fuel
                      unit.cu_context func [] G_b tn_b s_b) ==>
             !fuel. ptr_safe_blocks (cx_dead H cx) 0 fuel
                      unit.cu_context func [] FEMPTY entry_taint entry)``;

fun prepare_entry_tac () =
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `compiled_body = subst_consts_stmts (module_consts_env tops []) fbody` >>
  qpat_x_assum `runtime_body_endpoint _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [runtime_body_endpoint_def]) >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  qabbrev_tac `entry = vs with <|vs_prev_bb := NONE;
    vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  qabbrev_tac `explicit = gas_explicit_sites unit.cu_context shadow_unit.cu_context` >>
  qabbrev_tac `prefix = gas_explicit marks0 vs.vs_gas_readings` >>
  `nr ==> cx.nonreentrant_slot = SOME global_nonreentrant_slot /\
           is_view_mut mut = (mut = View)` by
    (strip_tac >> gvs[] >>
     drule_all externalEntryJointTheory.selected_nonreentrant_lock_metadata >>
     simp[Abbr `cx`]) >>
  `global_nonreentrant_slot < dimword (:256)` by
    simp[contextTheory.global_nonreentrant_slot_def, wordsTheory.dimword_def] >>
  qexistsl_tac [`compiled_body`,`cx`,`entry`,`shadow_unit`,`explicit`,`marks0`,
    `prefix`,`func`,`shadow_func`,`cenv`,`sa`,`st'`,`s0`,`G0`,`tn0`] >>
  conj_tac
  >- (asm_simp_tac std_ss [markerTheory.Abbrev_def] >>
      rpt strip_tac >>
      qpat_assum `!st0 H. valid_horizon cx st0 H es0.storage_trace ==> _`
        (qspecl_then [`initial_state am []`,`H`] mp_tac) >> simp[]) >>
  rpt strip_tac;

fun prepare_bound_tac package_source =
  `external_entry_bound tops am tx vs.vs_outcomes (prefix ++ es0.gas_obs)
     mut args dflts es0` by
    (`es0 with gas_obs := es0.gas_obs = es0` by (Cases_on `es0` >> simp[]) >>
     pop_assum (fn same =>
       qpat_assum `!gx. external_entry_bound _ _ _ _ _ _ _ _ _`
         (qspec_then `es0.gas_obs` (ACCEPT_TAC o PURE_REWRITE_RULE [same])))) >>
  `!tgt. supported_stmts_expr_exists (expr_abi_decode_target_root tgt)
       (subst_consts_stmts (module_consts_env tops []) fbody) ==>
       occurs_abi_decode_target tgt tops` by
    (rpt strip_tac >>
     fs[source_typing_ok_def] >>
     `ALOOKUP [(NONE,tops)] (NONE:num option) = SOME tops` by simp[] >>
     drule_all checked_const_substitution_abi_decode_target >>
     disch_tac >>
     drule lookup_function_abi_decode_target_occurs >>
     disch_then (qspec_then `tgt` match_mp_tac) >>
     first_assum ACCEPT_TAC) >>
  rename1 `set_external_package_target _ _ =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut',iv,compiled_body,rt)` >>
  `nkey = global_nonreentrant_slot /\ ut' = T /\ iv = (mut = View) /\
   rt = (if ret = NoneT then NONE else SOME ret)` by
    (drule return_package_target_inversion >> strip_tac >>
     drule return_package_metadata >> simp[]) >>
  qpat_assum `Abbrev (compiled_body = _)` (fn eq =>
    qpat_assum `set_external_package_target _ _ = _`
      (assume_tac o MATCH_MP package_source o
       PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] eq]));

fun prepare_registration_tac () =
  qpat_assum `compile_guarded_body cenv nr _ T _ compiled_body _ sa = _`
    (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
      nonreentrantEntryPathTheory.guarded_body_code_from_registration)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`sl`,`sb`] strip_assume_tac) >>
  qpat_assum
    `compile_guarded_body _ nr _ T _ (MAP gas_shadow_stmt compiled_body) _ shadow_sa = _`
    (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
      (Q.INST [`func` |-> `shadow_func`]
        nonreentrantEntryPathTheory.guarded_body_code_from_registration))) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`shadow_sl`,`shadow_sb`] strip_assume_tac) >>
  `gas_shadow_compiles
     (if nr then compile_nonreentrant_lock global_nonreentrant_slot T (mut = View)
      else comp_return ())
     (if nr then compile_nonreentrant_lock global_nonreentrant_slot T (mut = View)
      else comp_return ())` by
    (Cases_on `nr` >> simp[gasShadowModuleOpsTheory.gas_shadow_compiles_nonreentrant_lock,
      gasShadowStateTheory.gas_shadow_compiles_return]) >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (mp_tac o REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
  asm_simp_tac std_ss [] >> strip_tac;

fun prepare_env_tac () =
  qspecl_then [`tops`,`bindings`,`unit.cu_context`,`cx`,`cenv`,`compiled_body`,
    `ret`,`if ret = NoneT then NONE else SOME ret`,`env_t`,`env'`,`sl`,`sb`]
    mp_tac guarded_body_stmts_env >>
  impl_tac >- (asm_simp_tac std_ss [] >> simp[]) >>
  disch_then (qx_choose_then `cenv'` assume_tac) >>
  `SND (stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt compiled_body)
          shadow_sl) = shadow_sb` by
    (qpat_assum `compile_stmts _ NoLoop _ (MAP gas_shadow_stmt compiled_body) _ = _`
       (mp_tac o REWRITE_RULE [compile_stmts_env]) >>
     reverse (Cases_on `ret = NoneT`) >- simp[] >>
     gvs[] >> drule type_stmts_none_valued_return >> strip_tac >>
     qspecl_then [`MAP gas_shadow_stmt compiled_body`,`tops`,`bindings`,
       `gas_shadow_env T cenv`,`NoLoop`,`NoneT`,`BaseT BoolT`]
       mp_tac stmts_env_ret_ty_no_valued_return >>
     (impl_tac >- simp[gasShadowStmtEnvTheory.gas_shadow_supported_stmts,
       gasShadowStmtEnvTheory.gas_shadow_valued_return]) >>
     disch_then (fn th => PURE_REWRITE_TAC [th]) >> simp[]) >>
  qspecl_then [`compiled_body`,`cenv`,`NoLoop`,`ret`] mp_tac
    (Q.INST [`sd` |-> `T`] gasShadowStmtEnvTheory.gas_shadow_stmts_env_env) >>
  rewrite_tac[gasShadowCompileStmtBaseTheory.gas_shadow_compiles_env_def] >>
  disch_then (qspecl_then [`sl`,`shadow_sl`] mp_tac) >>
  asm_simp_tac std_ss [pairTheory.FST,pairTheory.SND] >> strip_tac >>
  `stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt compiled_body)
     shadow_sl = (gas_shadow_env T cenv',shadow_sb)` by
    metis_tac[pairTheory.PAIR] >>
  qpat_x_assum `SND (stmts_env _ _ _ (MAP gas_shadow_stmt _) _) = _` kall_tac >>
  qpat_x_assum `_ = FST (stmts_env _ _ _ (MAP gas_shadow_stmt _) _)` kall_tac;

fun prepare_reach_tac () =
  `?s_b G_b tn_b.
     gas_path_mem unit.cu_context func entry (LENGTH marks0) (OK s_b) /\
     alloca_history func s_b /\ return_buf_frame NONE cenv sl s_b /\
     local_ptrs_reserved cenv sl /\ ~block_is_terminated sl /\
     ~s_b.vs_halted /\ s_b.vs_current_bb = sl.cs_current_bb /\
     s_b.vs_inst_idx = LENGTH sl.cs_current_insts /\
     s_b.vs_gas_readings = s0.vs_gas_readings /\
     s_b.vs_code = vs.vs_code /\ s_b.vs_labels = vs.vs_labels /\
     (nr /\ mut <> View ==> ~tx.is_static) /\
     !H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
       stmt_state_rel H unit.cu_context func cenv cx es_lock s_b /\
       ghost_inv_at (cx_dead H cx) 0 NONE cenv cx es_lock G_b tn_b s_b /\
       gas_origin_ptr_path (cx_dead H cx,0,explicit,unit.cu_context,func,[])
         (entry,FEMPTY,entry_taint) marks0 (OK s_b,G_b,tn_b) /\
       ((!fuel. ptr_safe_run (cx_dead H cx) 0 fuel
                 unit.cu_context func [] G_b tn_b s_b) ==>
        !fuel. ptr_safe_blocks (cx_dead H cx) 0 fuel
          unit.cu_context func [] FEMPTY entry_taint entry)` by
    (reverse (Cases_on `nr`) >-
       (qpat_x_assum `lock_if_nr cx F _ es0 = _` mp_tac >>
        qpat_x_assum `(if F then _ else _) sa = _` mp_tac >>
        simp_tac (srw_ss()) [lock_if_nr_def, return_def, comp_return_def] >>
        ntac 2 (disch_then (SUBST_ALL_TAC o SYM)) >>
        qexistsl [`s0`,`G0`,`tn0`] >>
        asm_rewrite_tac[] >> qx_gen_tac `H` >> strip_tac >>
        qpat_assum `!st0 H. valid_horizon _ _ H _ ==> _`
          (qspecl_then [`initial_state am []`,`H`] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> simp[]) >>
     qpat_assum `T ==> cx.nonreentrant_slot = _ /\ _`
       (strip_assume_tac o REWRITE_RULE []) >>
     qpat_assum `T ==> fresh_vars_wrt sa s0 /\ _`
       (strip_assume_tac o REWRITE_RULE []) >>
     qpat_assum `(if T then _ else _) sa = _`
       (assume_tac o REWRITE_RULE []) >>
     mp_tac (Q.INST [`cx` |-> `cx`, `ss` |-> `entry`,
       `explicit` |-> `explicit`, `marks0` |-> `marks0`,
       `ctx` |-> `unit.cu_context`, `nkey` |-> `global_nonreentrant_slot`]
       (SPEC_ALL selected_entry_after_lock)) >>
     impl_tac >- (asm_simp_tac std_ss [] >> simp[]) >>
     disch_then (qx_choosel_then [`s_b`,`G_b`,`tn_b`] strip_assume_tac) >>
     `mut <> View ==> ~tx.is_static` by
       fs[Abbr `cx`, initial_evaluation_context_def] >>
     qexistsl [`s_b`,`G_b`,`tn_b`] >>
     simp[] >> qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!st0 H. valid_horizon cx st0 H es_lock.storage_trace ==> _`
       (qspecl_then [`initial_state am []`,`H`] mp_tac) >>
     simp[ghost_inv_cx_dead]);

fun prepare_source_tac headroom lock_inv =
  `gas_path unit.cu_context func entry (LENGTH marks0) (OK s_b)` by
    (drule_then (ACCEPT_TAC o CONJUNCT1) fragGasPathMemTheory.gas_path_mem_exec) >>
  `!fn inst s. frag_reachable unit.cu_context func s_b fn inst s ==>
       dalloca_fmp_headroom inst s` by
    (mp_tac (Q.INST [`s0` |-> `s_b`, `n` |-> `LENGTH (marks0:bool list)`]
      (SPEC_ALL headroom)) >>
     impl_tac >- (fs[Abbr `entry`] >> metis_tac[]) >>
     disch_then ACCEPT_TAC) >>
  `expr_sim_inv cenv cx env_t es_lock` by
    (irule lock_inv >> goal_assum (drule_at Any) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env_t es_lock` by
    (`es_lock.immutables = es0.immutables` by
       (drule_then strip_assume_tac external_body_lock_frame >> simp[]) >>
     irule (iffLR bodyFullPredsTheory.body_const_cells_agree_immutables) >>
     qexists_tac `es0` >> fs[Abbr `cx`]);

fun prepare_substitution_tac () =
  `!gas. eval_stmts cx compiled_body (es_lock with gas_obs := gas) =
          eval_stmts cx fbody (es_lock with gas_obs := gas)` by
    (mp_tac (Q.INST [`gs` |-> `prefix ++ es0.gas_obs`, `es0` |-> `es0`,
          `os` |-> `vs.vs_outcomes`, `unit` |-> `unit`, `rpolicy` |-> `rpolicy`,
          `es_lock` |-> `es_lock`, `nr` |-> `nr`, `mut` |-> `mut`,
          `ret` |-> `ret`, `fbody` |-> `fbody`, `tops` |-> `tops`,
          `args` |-> `args`, `dflts` |-> `dflts`, `am` |-> `am`, `tx` |-> `tx`]
       (SPEC_ALL external_source_body_substitution_nr)) >>
     disch_then (fn th =>
       qpat_assum `Abbrev (cx = _)` (fn eq =>
         qpat_assum `Abbrev (compiled_body = _)` (fn eq' =>
           mp_tac (PURE_REWRITE_RULE
             [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq),
              GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq')] th)))) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC);

fun prepare_storage_tac () =
  `!H. valid_horizon cx (initial_state am []) H es_lock.storage_trace ==>
     storage_well_formed_on cx es_lock (FST H)` by
    (gen_tac >> strip_tac >>
     `es_lock.storage_trace =
        es0.storage_trace ++ if nr then [StorageLock global_nonreentrant_slot] else []` by
       (reverse (Cases_on `nr`) >- fs[lock_if_nr_def, return_def] >>
        `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by fs[] >>
        irule lock_if_nr_success_trace >>
        qexistsl_tac [`cx`,`is_view_mut mut`] >> simp[]) >>
     `valid_horizon cx (initial_state am []) H es0.storage_trace` by
        fs[valid_horizon_def, storage_observations_ok_append] >>
     drule_all external_entry_bound_source_frame >> strip_tac >>
     mp_tac (Q.INST [`H` |-> `H`, `st` |-> `es0`, `u` |-> `es_lock`,
       `cx` |-> `cx`, `nr` |-> `nr`, `res` |-> `INL ()`, `view` |-> `is_view_mut mut`]
       vyperExternalEntryStorageFrameTheory.lock_if_nr_preserves_storage_well_formed_on) >>
     impl_tac
     >- (`storage_well_formed_on cx es0 (FST H)` by fs[Abbr `cx`] >>
         qpat_assum `valid_horizon cx _ H es_lock.storage_trace`
           (strip_assume_tac o REWRITE_RULE [valid_horizon_def]) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC);

fun prepare_return_tac () =
  mp_tac (Q.SPECL
    [`\H. cx_dead H cx`,`0`,`NONE`,`shadow_unit.cu_context`,`[]`,`func`,`shadow_func`,
     `tops`,`rpolicy`,`unit`,`am`,`tx`,`ret`,`mut`,`nr`,`args`,`dflts`,`fbody`,
     `lbl`,`cenv0`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut'`,`iv`,`rt`,`cenv`]
    external_source_frame_ret_ok_full_nr) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (fn th =>
    qpat_assum `Abbrev (cx = _)` (fn eq =>
      assume_tac (PURE_REWRITE_RULE
        [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] eq)] th))) >>
  `cx_tops cx = tops` by
    (irule cx_tops_module >> fs[Abbr `cx`, source_deployment_rel_def,
      vyperContextTheory.get_module_code_def, initial_evaluation_context_def]) >>
  `~cenv.ce_is_ctor` by fs[bodySimTheory.body_inv_def, Abbr `cx`, initial_evaluation_context_def] >>
  `ctx_inst_ids_distinct unit.cu_context` by
    (drule_all caller_runtime_entry_integrity >> simp[]) >>
  `struct_args_unique tops` by
    (fs[source_typing_ok_def] >> metis_tac[checked_contract_struct_args_unique]) >>
  qpat_assum `source_typing_ok tops am tx` (fn typing =>
    assume_tac (MATCH_MP source_typing_ok_vtype_keys_distinct typing)) >>
  drule_all runtime_shadow_body_inv >> strip_tac;

fun prepare_finish_tac () =
  `cenv.ce_return_buf = NONE` by fs[return_buf_frame_def] >>
  `gas_admissible (eval_stmts cx compiled_body) (stmt_res_ok NoLoop) es_lock` by
    (simp[gas_admissible_def] >> rpt strip_tac >>
     qunabbrev_tac `cx` >>
     drule_all_then (ACCEPT_TAC o CONJUNCT1) external_body_source_ok_nr) >>
  `(ctx_has_dalloca unit.cu_context ==> allocas_below_fmp s_b)` by
    (strip_tac >>
     qpat_assum `storage_trace_domain cx (initial_state am []) es_lock.storage_trace`
       (strip_assume_tac o REWRITE_RULE [storage_trace_domain_def]) >>
     qpat_assum `!H. valid_horizon cx _ H es_lock.storage_trace ==> _ /\ _`
       (qspec_then `storage_trace_horizon es_lock.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp
                        o CONJUNCT1) >> simp[]) >>
  qexistsl_tac [`bindings`,`env_t`,`env'`,`shadow_sl`,`shadow_sb`,`s_b`,`G_b`,`tn_b`] >>
  asm_simp_tac std_ss [] >>
  conj_tac >- (Cases_on `ret = NoneT` >> fs[]) >>
  rpt strip_tac >> asm_simp_tac std_ss [] >>
  first_x_assum irule >> qexists_tac `fn` >> first_assum ACCEPT_TAC;
end
