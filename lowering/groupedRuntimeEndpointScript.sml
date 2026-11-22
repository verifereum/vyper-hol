(* The grouped dispatcher supplies the same post-binding endpoint as the
   plain dispatcher. All code and run witnesses are fixed before horizons. *)
Theory groupedRuntimeEndpoint
Ancestors
  groupedEntryPackage groupedEntryResources groupedDefaultHorizon
  externalBodyFrame externalEntryBound runtimeEntryEndpoint fragExec
  fragGasOriginPtr fragFuel gasShadowRunLowering loweringStateRelDefs bodyPtrDefs
  compileVyper e2eDefs moduleLowering compileEnv vyperInterpreter vyperState
  ptrDiscipline venomState venomInst list

val _ = Parse.hide "body";

Theorem grouped_registered_body_endpoint:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  initial_venom_state_rel tops am tx vs /\ outcomes_accounts_typed (SOME vs.vs_outcomes) /\
  cx = initial_evaluation_context am.sources am.layouts tx NONE /\
  vyperInterpreter$lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,body_ret,fbody) /\
  body = subst_consts_stmts (module_consts_env tops []) fbody /\
  (!gx. external_entry_bound tops am tx vs.vs_outcomes
    (gas_explicit marks vs.vs_gas_readings ++ gx) mut args dflts (es with gas_obs := gx)) /\
  es.gas_obs = [] /\
  set_external_package_target rpolicy.rpol_target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,lookup_raw_return_or_F (NONE:num option) tx.function_name External tops,
       tx.function_name,args,subst_consts_exprs (module_consts_env tops []) dflts,body_ret,body)) =
    (lbl,ce0,pos_args,min_cds,is_payable,nr,nkey,ut,iv,body,rt) /\
  ce with ce_vars := ce0.ce_vars = ce0 /\
  (!id ty. MEM (id,ty) args ==>
    (?p sz. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)) /\ ce.ce_var_type id = SOME ty) /\
  (!id loc. FLOOKUP ce.ce_vars id = SOME loc ==> MEM id (MAP FST args)) /\
  compile_guarded_body ce nr global_nonreentrant_slot T (mut = View)
    body (if body_ret = NoneT then NONE else SOME body_ret) sa = ((),final) /\
  fn_has_code sa final fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ ~block_is_terminated sa /\
  unit.cu_context.ctx_entry = SOME "__entry" /\
  lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  lookup_block "__entry" fn.fn_blocks = SOME bb /\
  (!l b. lookup_block l fn.fn_blocks = SOME b ==> phi_prefix_length b.bb_instructions = 0) /\
  runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
  gas_shadow_context unit.cu_context shadow_unit.cu_context /\
  gas_shadow_function fn shadow_fn /\
  MEM fn unit.cu_context.ctx_functions /\ MEM shadow_fn shadow_unit.cu_context.ctx_functions /\
  gas_shadow_state sa shadow_sa /\
  compile_guarded_body (gas_shadow_env T ce) nr global_nonreentrant_slot T (mut = View)
    (MAP gas_shadow_stmt body) (if body_ret = NoneT then NONE else SOME body_ret)
    shadow_sa = ((),shadow_final) /\ fn_has_code shadow_sa shadow_final shadow_fn /\
  s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
  s.vs_allocas = FEMPTY /\
  at_point sa t /\ (nr ==> fresh_vars_wrt sa t) /\
  return_buf_frame NONE ce sa t /\
  storage_trace_domain cx (initial_state am []) es.storage_trace /\
  (!H:(bool # bytes32 # type_value) list # num list.
    stmt_state_rel H unit.cu_context fn ce cx es t /\
    ghost_inv_at (cx_dead H cx) 0 NONE ce cx es G tn t) /\
  (!D. gas_origin_ptr_path
    (D,0,gas_explicit_sites unit.cu_context shadow_unit.cu_context,unit.cu_context,fn,[])
    (s,FEMPTY,entry_taint) marks (OK t,G,tn)) ==>
  runtime_body_endpoint tops rpolicy unit am tx vs es mut nr args dflts body_ret body
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  qpat_x_assum `body = _` SUBST_ALL_TAC >>
  `es with gas_obs := [] = es` by simp[evaluation_state_component_equality] >>
  qpat_assum `es with gas_obs := [] = es` (fn frame =>
    qpat_assum `!gx. external_entry_bound tops am tx vs.vs_outcomes _ mut args dflts (es with gas_obs := gx)`
      (qspec_then `[]:bytes32 list` (assume_tac o REWRITE_RULE [frame,APPEND_NIL]))) >>
  drule_all external_source_body_frame_nr >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [GSYM grouped_package_external_defaults]) >>
  qpat_assum `set_external_package_target _ _ = _`
    (assume_tac o REWRITE_RULE [grouped_package_external_defaults]) >>
  qpat_assum `at_point _ _` (strip_assume_tac o REWRITE_RULE [at_point_def]) >>
  `!D. ((!fuel. ptr_safe_run D 0 fuel unit.cu_context fn [] G tn t) ==>
    !fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn [] FEMPTY entry_taint s)` by
    (gen_tac >> qpat_assum `!D. gas_origin_ptr_path (D,0,_,_,fn,[]) _ marks _`
       (qspec_then `D` assume_tac) >>
     drule_all grouped_entry_origin_continuation >> simp[]) >>
  qpat_assum `!D. gas_origin_ptr_path (D,0,_,_,fn,[]) _ marks _`
    (qspec_then `cx_dead ([],[]) (initial_evaluation_context am.sources am.layouts tx NONE)`
      assume_tac) >>
  drule_all grouped_entry_origin_continuation >> strip_tac >>
  PURE_REWRITE_TAC [runtime_body_endpoint_def] >>
  qexistsl_tac [`marks`,`ce0`,`ce`,`sa`,`final`,`fn`,`t`,`G`,`tn`,
    `shadow_unit`,`shadow_fn`,`shadow_sa`,`shadow_final`] >>
  qpat_assum `s = _` (fn th => PURE_REWRITE_TAC [SYM th]) >>
  simp_tac bool_ss [] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qexistsl_tac [`lbl`,`pos_args`,`min_cds`,`is_payable`,`nkey`,`ut`,`iv`,`rt`] >>
      first_assum ACCEPT_TAC)
  >- (qexistsl_tac [`bindings`,`env_t`,`env'`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`run_from _ unit.cu_context fn t`]
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!k r. run_from k unit.cu_context fn t = r /\
          (!e. r <> Error e) ==> ?k'. run_context k' unit.cu_context vs = r`
        (qspecl_then [`fuel`,`run_from fuel unit.cu_context fn t`]
          (fn th => qpat_assum `!e. run_from _ _ _ _ <> Error e`
            (ACCEPT_TAC o MATCH_MP th o CONJ (REFL (Term `run_from fuel unit.cu_context fn t`))))))
  >~ [`fresh_vars_wrt sa t`]
  >- (strip_tac >> rpt conj_tac
      >~ [`fresh_vars_wrt sa t`] >- (qpat_assum `nr ==> fresh_vars_wrt sa t` mp_tac >> simp[])
      >~ [`ghost_inv _ NONE ce _ es G tn t`]
      >- (gen_tac >>
          qpat_assum `!H. stmt_state_rel H _ _ _ _ _ _ /\
            ghost_inv_at (cx_dead H _) 0 NONE _ _ _ _ _ _`
            (qspec_then `H` (ACCEPT_TAC o REWRITE_RULE [GSYM ghost_inv_cx_dead]))) >>
      first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >~ [`ptr_safe_blocks`]
  >- (qpat_assum `!D. (!fuel. ptr_safe_run D 0 fuel _ _ [] _ _ _) ==>
         !fuel. ptr_safe_blocks D 0 fuel _ _ [] _ _ _`
        (qspec_then `cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)` ACCEPT_TAC)) >>
  qpat_assum `!H. stmt_state_rel H _ _ _ _ _ _ /\
    ghost_inv_at (cx_dead H _) 0 NONE _ _ _ _ _ _`
    (qspec_then `H` strip_assume_tac) >>
  qpat_assum `!D. gas_origin_ptr_path (D,0,_,_,fn,[]) _ marks _`
    (qspec_then `cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE)` ACCEPT_TAC)
QED
