(* The reached address operand determines the linked SELFDESTRUCT outcome. *)
Theory bodySelfDestructCaseMods
Ancestors createSizeExit[qualified,ignore_grammar]
  bodyFullCases[qualified] bodyFullPredsMods bodyFullPostsMods
  bodyActionStackVVMods bodySelfDestructStaticMods bodySelfDestructOverflowMods
  bodySelfDestructHaltMods bodyForcedStorageFrameMods
  bodyFullShadowBodyInv exprBodyPreProps exprSimSliceCompose exprSimSend
  exprSimDefs stmtSimProps loweringStateRelDefs stateRelProj loweringPosts bodyPtrDefs
  exprLowering exprLoweringProps exprSimHypsDefs exprCallbackContracts
  gasShadowCompileStmtHelpers gasShadow gasOutcomeFullMods gasExemptCertMods
  fragGasOriginPtr fragGasOrigin fragGasSeqPtr fragGasEmitCtrl fragGasMode
  gasNormalPrefix gasSummaryCompose gasSummary gasStorage gasContext
  gasEvents gasCount memSafeRun instMemFrontier ptrDiscipline ptrSafeRun
  unitTransformDefs contextCodegenRel codegenRel
  selfdestructHalt builtinSystem compileEnv emitHelper fragExec
  vyperAST vyperInterpreter vyperState vyperStorageTrace vyperStorageFootprint
  vyperTypeSystem vyperValue vyperTyping vyperTypeCallGraph vyperContext
  supportedExprTraverse allocLimits venomState venomInst venomExecSemantics
  list rich_list pair
Libs pairLib

Theorem selfdestruct_source_cut[local]:
  !mods cenv cx env ann args dflt es.
    expr_body_pre_mods mods cenv cx env (Call ann SelfDestructTarget args dflt) es ==>
    ?e. args = [e] /\ ann = NoneT /\ dflt = NONE /\
        expr_type e = BaseT AddressT /\ expr_body_pre_mods mods cenv cx env e es
Proof
  rpt gen_tac >> strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  `?e. args = [e] /\ ann = NoneT /\ dflt = NONE /\
       expr_type e = BaseT AddressT` by
    gvs[Once well_typed_expr_def, LENGTH_EQ_NUM_compute] >>
  gvs[expr_body_pre_mods_def, well_typed_expr_def, byte_widths_expr_def,
      alloc_limits_expr_def, int_calls_expr_def, expr_has_evm_run_thm,
      supported_expr_exists_def, supported_exprs_exists_every]
QED

Theorem selfdestruct_stack_compile[local]:
  !ce ty child sa vv sb.
    compile_expr ce ty (Call NoneT SelfDestructTarget [child] NONE) sa = (vv,sb) ==>
    vv = StackValue NoneT (Lit 0w)
Proof
  rpt gen_tac >>
  simp[Once compile_expr_def, compile_call_def, expr_type_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[])
QED

(* The active singleton ghost has an unrelated dead-immutable conjunct.
   This no-memory terminal instruction needs storage taint and the allocation
   frontier, not the dead-immutable conjunct. *)
Theorem selfdestruct_suffix[local]:
  !op sm sb func t aw tn G ctx lo explicit PG.
    compile_selfdestruct op sm = ((),sb) /\ fn_has_code sm sb func /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\ ~t.vs_halted /\
    eval_operand op t = SOME aw /\ op_taint tn op = {} /\
    op_prov G op = NONE /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
    ?r. step_inst_base (mk_inst sm.cs_next_id SELFDESTRUCT [op] []) t = r /\
        exit_result r /\
        (!D. stor_taint_ok_at D tn t /\ allocas_from lo t /\
             lo <= t.vs_alloca_next ==>
          gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
            (t,G,tn) [] (r,G,tn))
Proof
  rpt gen_tac >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb /\
   sb.cs_current_insts = sm.cs_current_insts ++
     [mk_inst sm.cs_next_id SELFDESTRUCT [op] []]` by
    (qpat_x_assum `compile_selfdestruct _ _ = _` mp_tac >>
     simp[compile_selfdestruct_def, emit_void_def, fresh_id_def, emit_def,
          comp_bind_def] >> strip_tac >> gvs[]) >>
  `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
    !i. i < LENGTH [mk_inst sm.cs_next_id SELFDESTRUCT [op] []] ==>
      get_instruction bb (LENGTH sm.cs_current_insts + i) =
        SOME (EL i [mk_inst sm.cs_next_id SELFDESTRUCT [op] []])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> simp[]) >>
  first_x_assum (qspec_then `0` assume_tac) >> gvs[] >>
  conj_asm1_tac
  >- (simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operands_def] >>
      Cases_on `t.vs_call_ctx.cc_static` >> simp[exit_result_def]) >>
  rpt strip_tac >>
  irule exit_inst_origin_ptr >> simp[] >>
  simp[mk_inst_def, step_inst_non_invoke, gas_events_step_def,
    gas_count_step_def, mem_safe_step_non_invoke,
    inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def] >>
  fs[stor_taint_ok_at_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operands_def] >>
  Cases_on `t.vs_call_ctx.cc_static` >> simp[] >>
  rpt strip_tac >> gvs[halt_state_def, set_returndata_def] >>
  simp[step_taint_def, adopt_reset_def, store_taint_def,
       imm_taint_def, ret_taint_def] >>
  Cases_on `t.vs_call_ctx.cc_created_in_tx`
  >- gvs[vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
         combinTheory.APPLY_UPDATE_THM] >>
  gvs[GSYM vfmStateTheory.lookup_account_def,
      vfmSameFrameTheory.transfer_value_preserves_storage]
QED

Theorem selfdestruct_static_prefix[local]:
  !DF lo explicit ctx func PG mods cx st0 source es s0 G0 tn0
    marks v ee t G tn.
    (!tail. source (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v, ee with gas_obs := tail)) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (?a. dest_AddressV v = SOME a) /\ cx.txn.is_static /\
    create_size_exit_ok ctx
      (INR (Error (RuntimeError "write in static context")) : value + exception)
      (Abort ExHalt_abort (halt_state (set_returndata [] t))) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s0,G0,tn0) marks (OK t,G,tn) /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (t,G,tn) [] (Abort ExHalt_abort (halt_state (set_returndata [] t)),G,tn)) ==>
    gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) mods cx st0
      (bind (bind source (selfdestruct_tail cx)) (read_result cx))
      (es,s0,G0,tn0) Q
      (\H res ee' gt r. expr_exit res r /\ halt_exit H cx ee' res r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[gas_outcome_full_mods_def] >> qexists `marks` >>
  disj2_tac >> disj1_tac >>
  qexistsl [`INR (Error (RuntimeError "write in static context"))`, `ee`,
            `Abort ExHalt_abort (halt_state (set_returndata [] t))`, `G`, `tn`] >>
  conj_tac
  >- (gen_tac >> once_rewrite_tac[bind_assoc] >>
      pure_once_rewrite_tac[bind_def] >> asm_rewrite_tac[] >>
      simp[selfdestruct_tail_def, bind_def, ignore_bind_def, lift_option_type_def,
           check_not_static_def, check_def, assert_def, raise_def, return_def]) >>
  simp[exit_result_def, expr_exit_def, halt_exit_def] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _` drule >> strip_tac >>
  qpat_assum `gas_origin_ptr_path _ _ marks (OK t,G,tn)`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  disch_then (qspec_then `t` mp_tac) >> simp[] >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then irule >> first_assum ACCEPT_TAC
QED

Theorem selfdestruct_address_of_run[local]:
  gas_admissible
    (bind (bind (bind (eval_expr cx e) (read_result cx)) (selfdestruct_tail cx))
       (read_result cx)) expr_res_ok es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
  dest_AddressV v = SOME (w2w (typed_val_to_w256 (BaseTV AddressT) v))
Proof
  strip_tac >>
  `?a. dest_AddressV v = SOME a` by
    (Cases_on `dest_AddressV v` >> simp[] >>
     qpat_x_assum `gas_admissible _ _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspecl_then [`gs`, `INR (Error (TypeError "selfdestruct target"))`,
                             `ee`] mp_tac) >>
     once_rewrite_tac[bind_assoc] >> pure_once_rewrite_tac[bind_def] >>
     asm_rewrite_tac[] >>
     simp[selfdestruct_tail_def, lift_option_type_def, bind_def, raise_def,
          expr_res_ok_def]) >>
  irule exprSimSendTheory.address_typed_dest >>
  Cases_on `v` >> gvs[dest_AddressV_def, value_has_type_def]
QED

Theorem selfdestruct_run_mods[local]:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
    expr_type e = BaseT AddressT /\
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call NoneT SelfDestructTarget [e] NONE) es
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  `!ce ee st op st'.
     lower_value compile_expr ce ty (Call NoneT SelfDestructTarget [ee] NONE) st =
       (op,st') ==>
     compile_expr ce ty (Call NoneT SelfDestructTarget [ee] NONE) st =
       (StackValue NoneT (Lit 0w),st')` by
    (rpt gen_tac >> simp[lower_value_def, comp_bind_def] >>
     pairarg_tac >> simp[] >> strip_tac >>
     drule_then SUBST_ALL_TAC selfdestruct_stack_compile >>
     gvs[unwrap_value_def, comp_return_def]) >>
  `compile_expr cenv ty (Call NoneT SelfDestructTarget [e] NONE) sa =
       (StackValue NoneT (Lit 0w),sb) /\
   compile_expr (gas_shadow_env T cenv) ty
       (gas_shadow_expr (Call NoneT SelfDestructTarget [e] NONE)) shadow_sa =
       (StackValue NoneT (Lit 0w),shadow_sb)` by
    (conj_tac >- (first_x_assum irule >> qexists `op` >> simp[]) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
     pure_rewrite_tac[gas_shadow_expr_def, MAP, optionTheory.OPTION_MAP_DEF] >>
     first_assum MATCH_ACCEPT_TAC) >>
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
     (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
       (gas_shadow_expr e))` by
    MATCH_ACCEPT_TAC gas_shadow_stmt_lower_value_env >>
  drule_all_then strip_assume_tac bodyFullCasesTheory.selfdestruct_full_layout_shadow >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (qpat_assum `gas_admissible _ _ _` mp_tac >>
     rewrite_tac[eval_selfdestruct_action] >> once_rewrite_tac[bind_assoc] >>
     disch_then (MATCH_ACCEPT_TAC o MATCH_MP slice_gas_admissible_value_head)) >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ e _`
    (drule_all_then assume_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  suspend "compose"
QED

Resume selfdestruct_run_mods[compose]:
  qmatch_goalsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ fullQ fullR` >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ _` >>
  qpat_x_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ fullR`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_mods_def])
  >~ [`gas_bad_storage_at _ _ _ _ _ _`]
  >- suspend "storage"
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- suspend "exempt" >>
  Cases_on `exit_result r` >- suspend "early_exit" >> suspend "reached"
QED

Resume selfdestruct_run_mods[storage]:
  rewrite_tac[gas_outcome_full_mods_def] >> qexists `marks` >> disj1_tac >>
  reverse conj_tac >- metis_tac[] >>
  rewrite_tac[eval_selfdestruct_action] >> once_rewrite_tac[bind_assoc] >>
  irule gas_bad_storage_at_bind_left >> simp[] >>
  gen_tac >> irule storage_trace_frame_bind_all >>
  simp[storage_trace_frame_selfdestruct_tail, storage_trace_frame_read_result]
QED

Resume selfdestruct_run_mods[exempt]:
  rewrite_tac[gas_outcome_full_mods_def] >> qexists `marks` >>
  disj2_tac >> disj2_tac >>
  qexistsl [`err`,`ee`,`leaf`,`leaf_pg`,`leaf_g`,`leaf_tn`,`finish'`] >>
  reverse conj_tac >- metis_tac[] >>
  rewrite_tac[eval_selfdestruct_action, ignore_bind_def] >>
  ntac 2 (once_rewrite_tac[bind_assoc]) >>
  irule gas_exempt_cert_mods_error_value >> simp[ignore_bind_def]
QED

Resume selfdestruct_run_mods[early_exit]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
     ee.storage_trace` by fs[storage_trace_domain_def] >>
  `?ex. res = INR ex` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     strip_tac >> gvs[exit_result_def] >>
     Cases_on `res` >> simp[] >> Cases_on `r` >>
     gvs[Abbr `fullR`, exit_result_def, expr_exit_def]) >>
  gvs[] >> rewrite_tac[gas_outcome_full_mods_def] >> qexists `marks` >>
  disj2_tac >> disj1_tac >> qexistsl [`INR ex`,`ee`,`r`,`G'`,`tn'`] >>
  conj_tac
  >- (rewrite_tac[eval_selfdestruct_action] >>
      once_rewrite_tac[bind_assoc] >> irule gas_source_bind_exception >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  gvs[exit_result_def]
QED

Resume selfdestruct_run_mods[reached]:
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> gvs[exit_result_def] >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
    (drule_then strip_assume_tac) >> gvs[] >>
  rename1 `compile_selfdestruct data sm = ((),sb)` >>
  suspend "address"
QED

Resume selfdestruct_run_mods[address]:
  `dest_AddressV v = SOME (w2w (typed_val_to_w256 (BaseTV AddressT) v))` by
    (irule selfdestruct_address_of_run >>
     qpat_assum `gas_admissible (bind (eval_expr _ (Call _ _ _ _)) _) _ _`
        (irule_at Any o REWRITE_RULE [eval_selfdestruct_action]) >>
     qexistsl [`gas_explicit marks s0.vs_gas_readings`,`ee with gas_obs := []`] >>
     qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `post_value_type cenv e = BaseT AddressT` by simp[is_word_type_def] >>
  `eval_operand data t = SOME (typed_val_to_w256 (BaseTV AddressT) v)` by
    (qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_post_mods_def, expr_post_def, expr_val_rel_def]) >>
     simp[is_word_type_def, evaluate_type_def] >> strip_tac >> gvs[]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_origin_ptr_path _ _ marks (OK t,_,_)`
       (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule_all_then ACCEPT_TAC gas_path_ptr_ok_not_halted) >>
  `op_taint tn' data = {} /\ op_prov G' data = NONE` by
    fs[ptr_val_ok_def, is_word_type_def] >>
  drule_all selfdestruct_suffix >>
  disch_then (qspecl_then [`lo`,`gas_explicit_sites ctx shadow_ctx`,`PG`]
    strip_assume_tac) >>
  rename1 `step_inst_base _ t = r'` >>
  suspend "all_horizons"
QED

Resume selfdestruct_run_mods[all_horizons]:
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     state_rel H func cenv cx (ee with gas_obs := []) t /\
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s0,G0,tn0) marks (OK t,G',tn') /\
     gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (t,G',tn') [] (r',G',tn')` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac
     >- (qpat_assum `expr_post_mods H _ _ _ _ _ _ _ _ _ _ _ _ _`
           (strip_assume_tac o REWRITE_RULE [expr_post_mods_def, expr_post_def]) >>
         drule_then ACCEPT_TAC stmt_state_rel_state_rel) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!D. stor_taint_ok_at D _ _ /\ _ ==> _`
       (qspec_then `DF H` mp_tac) >>
     qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >> simp[]) >>
  `state_rel (storage_trace_horizon ee.storage_trace) func cenv cx
     (ee with gas_obs := []) t` by simp[] >>
  drule_then assume_tac state_rel_call_ctx_rel >>
  `t.vs_call_ctx.cc_address = cx.txn.target /\
   t.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
   t.vs_call_ctx.cc_static = cx.txn.is_static` by fs[call_ctx_rel_def] >>
  Cases_on `cx.txn.is_static`
  >- suspend "static" >>
  Cases_on `selfdestruct_overflows cx
      (w2w (typed_val_to_w256 (BaseTV AddressT) v)) ee.accounts`
  >- suspend "overflow" >> suspend "halt"
QED

Resume selfdestruct_run_mods[static]:
  `r' = Abort ExHalt_abort (halt_state (set_returndata [] t))` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operands_def]) >>
  qunabbrev_tac `fullR` >> pure_rewrite_tac[eval_selfdestruct_action] >>
  irule selfdestruct_static_prefix >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`G'`,`ee`,`marks`,`t`,`tn'`,`v`] >>
  `(halt_state (set_returndata [] t)).vs_call_ctx.cc_static` by
    simp[halt_state_def, set_returndata_def] >>
  simp[createSizeExitTheory.create_size_exit_ok_static,
       createSizeExitTheory.oversized_create_abort_static] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> state_rel _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `r' = Abort _ _` (SUBST_ALL_TAC o SYM) >>
  first_assum ACCEPT_TAC
QED

Resume selfdestruct_run_mods[overflow]:
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (assume_tac o REWRITE_RULE [APPEND_NIL])) >>
     `valid_horizon cx st0 H0
        ((es with gas_obs := gas_explicit marks s0.vs_gas_readings).storage_trace)`
       suffices_by simp[] >>
     irule (INST_TYPE [alpha |-> ``:value``] valid_horizon_frame) >>
     qexistsl [`bind (eval_expr cx e) (read_result cx)`, `INL v`, `ee with gas_obs := []`] >>
     simp[bodyForcedStorageFrameModsTheory.bop_forced_storage_frame]) >>
  `gas_value_prefix H0 T (ctx,func,cenv,cx) (expr_type e,e)
     (sa,sm,data) (es,s0) marks (v,ee,t)` by
    (qpat_assum `expr_post_mods H0 _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     qpat_assum `gas_origin_ptr_path _ _ marks (OK t,_,_)`
       (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     drule_then assume_tac gas_origin_path_erase >>
     simp[gas_value_prefix_def, gas_marked_exec_def]) >>
  irule selfdestruct_overflow_outcome_mods >>
  qpat_assum `gas_value_prefix _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> qexistsl [`StackValue NoneT (Lit 0w)`,`ty`,`tn'`,`sb`,`G'`] >>
  simp[] >>
  qpat_assum `!ce ee st op st'. lower_value _ _ _ _ _ = _ ==> _`
    (drule_then ACCEPT_TAC)
QED

Resume selfdestruct_run_mods[halt]:
  qunabbrev_tac `fullR` >> pure_rewrite_tac[eval_selfdestruct_action] >>
  irule selfdestruct_halt_outcome_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`G'`,`typed_val_to_w256 (BaseTV AddressT) v`,`ee`,
            `sm.cs_next_id`,`marks`,`data`,`r'`,`t`,`tn'`,`v`] >>
  simp[]
QED

Finalise selfdestruct_run_mods

Theorem body_selfdestruct_case_full_mods:
  !mods exps cx ann args dflt.
    body_exprs_full_ok_mods mods exps cx args ==>
    body_expr_full_ok_mods mods exps cx (Call ann SelfDestructTarget args dflt)
Proof
  rpt gen_tac >> disch_tac >> simp[Once body_expr_full_ok_mods_def] >>
  rpt gen_tac >> strip_tac >> drule_then strip_assume_tac selfdestruct_source_cut >>
  gvs[body_exprs_full_ok_mods_def] >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ e` mp_tac >>
  simp[Once body_expr_full_ok_mods_def] >> strip_tac >>
  qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
                 _ ==> expr_sim_full_mods _ _ _ _ e _ /\ _`
    (drule_all_then strip_assume_tac) >>
  `expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call NoneT SelfDestructTarget [e] NONE) es` by
    (irule selfdestruct_run_mods >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule action_stack_vv_full_mods >>
  qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (gen_tac >> Cases_on `compile_expr cenv ty
           (Call NoneT SelfDestructTarget [e] NONE) sa` >>
      drule selfdestruct_stack_compile >> simp[]) >>
  POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >>
  simp[eval_selfdestruct_action, bind_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  rename1 `selfdestruct_tail cx target st = (INL _,_)` >>
  qpat_x_assum `selfdestruct_tail _ _ _ = _` mp_tac >>
  qspecl_then [`cx`,`target`,`st`]
    (qx_choosel_then [`ex`,`out`] SUBST1_TAC) selfdestruct_tail_raises >> simp[]
QED
