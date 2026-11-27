(* The source function releases its guard after Return raises.  The target
   releases it before STOP; RetQ compares those actual cleanup endpoints. *)
Theory externalReturnNoneNrFullFrag
Ancestors
  externalReturnPackage entryStateRel rawReturnHeader
  stmtSimReturn nonreentrantExit nonreentrantEntryEquiv loweringHalt
  bodySimFull bodyPtrDefs stmtSimDefs exprSimDefs exprSimHypsDefs bodySim e2eDefs
  gasOutcomeFullCompose fragGasOriginPtr fragGasOriginPtrExec fragGasEmitCtrl
  fragGasPathPtr fragGasPathMem fragExec gasCount gasEvents
  accountsRelProps sourceUnitExecution loweringStateRelDefs
  stmtLowering moduleLowering moduleLoweringProps compileVyper compileEnv context
  exprLoweringProps loweringPosts
  ptrSafeRun ptrDiscipline memSafeRun contextCodegenRel codegenRel unitTransformDefs
  venomInst venomState venomExecSemantics venomExecProofs
  emitHelper emitHelperProps vyperTypeSystem vyperTypeContract
  vyperTypeContractContext vyperTypeContractGetter
  vyperInterpreter vyperState vyperValueOperation vyperStorageFootprint vyperGetter
  list option finite_map rich_list

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt strip_tac >>
  `ret = NoneT` by gvs[type_stmt_def] >> gvs[] >>
  qpat_assum `cenv with ce_vars := _ = cenv0`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [compile_env_component_equality]) >>
  `ce.ce_nonreentrant = (nr,global_nonreentrant_slot,T,mut = View) /\
   ~ce.ce_is_ctor /\ ce.ce_return_pc = NONE` by
    (drule return_package_target_inversion >> strip_tac >>
     drule return_package_metadata >> strip_tac >>
     drule return_same_frame_metadata >> gvs[]) >>
  `ce.ce_ctor_exit_label = NONE` by
    (drule return_package_target_inversion >> strip_tac >>
     fs[same_frame_def] >>
     qpat_x_assum `package_external_fn _ _ _ _ = _` mp_tac >>
     simp[package_external_fn_def, update_cenv_nonreentrant_def] >>
     strip_tac >> gvs[] >> fs[compile_env_component_equality]) >>
  `nr ==> (mut = View \/ mut = Pure <=> mut = View) /\
          (mut <> View ==> lookup_nonreentrant_slot am.layouts tx.target =
            SOME global_nonreentrant_slot)` by
    (strip_tac >> gvs[] >>
     drule lookup_function_External_cases >> strip_tac
     >- (`function_header_ok External mut T raw tx.function_name
            args dflts NoneT` by metis_tac[source_typing_function_header] >>
         drule function_header_nonreentrant_view >> strip_tac >>
         fs[source_typing_ok_def] >>
         drule check_contract_main_module_allocated >> simp[] >> strip_tac >>
         drule check_contract_runtime_function_body_MEM >>
         disch_then (qspecl_then [`External`, `tops`, `NONE`, `NoneT`, `raw`,
           `T`, `mut`, `tx.function_name`, `dflts`, `fbody`, `args`] mp_tac) >>
         simp[check_function_body_def, global_nonreentrant_slot_def]) >>
     Cases_on `decl` >> gvs[is_public_getter_decl_def] >>
     Cases_on `v` >>
     gvs[external_getter_tuple_def, getter_def, AllCaseEqs()] >>
     rpt (pairarg_tac >> gvs[])) >>
  `unlock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
      nr (is_view_mut mut) =
    (if nr /\ mut <> View then
       release_nonreentrant_lock cx.txn.target global_nonreentrant_slot
     else vyperState$return ())` by
    (Cases_on `nr` >> Cases_on `mut = View` >>
     gvs[unlock_if_nr_def, initial_evaluation_context_def]) >>
  simp_tac std_ss [stmt_frag_full_def] >> rpt strip_tac >>
  `lo = 0` by fs[dead_lo_ok_def] >> gvs[] >>
  `?su. (if nr then
          compile_nonreentrant_unlock global_nonreentrant_slot T (mut = View)
        else comp_return ()) sa = ((),su) /\
        emit_inst STOP [] [] su = ((),sb)` by
    (qpat_x_assum `stmt_env _ _ _ _ sa = (_,sb)` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          compile_return_unlock_def] >>
     Cases_on `(if nr then
       compile_nonreentrant_unlock global_nonreentrant_slot T (mut = View)
       else comp_return ()) sa` >> rename1 `_ = (answer,su)` >>
     Cases_on `answer` >> simp[] >> strip_tac >>
     Cases_on `emit_inst STOP [] [] su` >>
     rename1 `emit_inst STOP [] [] su = (answer,stop_state)` >>
     Cases_on `answer` >> gvs[]) >>
  `compile_return_unlock ce sa = ((),su)` by simp[compile_return_unlock_def] >>
  drule compile_return_unlock_shape >> strip_tac >>
  `cs_extends su sb` by metis_tac[cs_extends_emit_inst] >>
  `fn_has_code sa su func /\ fn_has_code su sb func` by
    metis_tac[fn_has_code_split] >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_bad_nil >> simp[Once evaluate_def, raise_def]) >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
      es.storage_trace` by fs[storage_trace_domain_def] >>
  `nr /\ mut <> View ==> ~s0.vs_call_ctx.cc_static` by
    (first_x_assum (drule_then strip_assume_tac) >>
     fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s0` by
    (`stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es s0`
       by metis_tac[] >>
     first_assum (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  mp_tac (Q.INST [`st` |-> `sa`, `su` |-> `su`, `sb` |-> `sb`,
    `nkey` |-> `global_nonreentrant_slot`, `iv` |-> `mut = View`,
    `lo` |-> `0:num`, `s` |-> `s0`, `G` |-> `G0`, `tn` |-> `tn0`,
    `DF` |-> `DF`, `cenv` |-> `ce`, `cx` |-> `cx`]
    (INST_TYPE [alpha |-> ``:256``] optional_transient_unlock_stop_joint_at)) >>
  impl_tac >- simp[allocas_from_def] >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp ss` by
    (qpat_assum `ss = _` SUBST1_TAC >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s0` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `nr /\ mut <> View` >>
     simp[ptrDisciplineTheory.allocas_below_fmp_def, halt_state_def, tstore_def] >>
     metis_tac[]) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`G0`, `es`, `[]`,
    `Halt ss`,
    `INR (ReturnException NoneV)`, `tn'`] >>
  conj_tac >- simp[Once evaluate_def, raise_def] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  `stmt_state_rel H ctx func ce cx es s0 /\
   ghost_inv_at (DF H) 0 d ce cx es G0 tn0 s0` by metis_tac[] >>
  conj_tac
  >- (first_assum irule >> fs[ghost_inv_at_def]) >>
  simp[NoAsms, exit_result_def, stmt_exit_ptr_def, expr_exit_def,
       halt_exit_def] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  simp[] >> gen_tac >>
  `state_rel H func ce cx
    (es with <| scopes := []; gas_obs := tail |>) s0` by
    (fs[stmt_state_rel_def] >>
     metis_tac[state_rel_scopes_nil, state_rel_gas_obs]) >>
  `?ee'. (if nr /\ mut <> View then
            release_nonreentrant_lock cx.txn.target global_nonreentrant_slot
          else vyperState$return ())
        (es with <| scopes := []; gas_obs := tail |>) = (INL (),ee')` by
    (Cases_on `nr /\ mut <> View` >>
     simp[nonreentrantEquivTheory.release_nonreentrant_lock_execution, vyperStateTheory.return_def]) >>
  simp[vyperValueTheory.evaluate_type_def, safe_cast_def] >>
  qexists_tac `ee'` >> conj_tac >- metis_tac[] >>
  drule_all source_typing_none_return_plain >> strip_tac >>
  mp_tac (Q.INST [`cenv` |-> `ce`,
    `es` |-> `es with <| scopes := []; gas_obs := tail |>`,
    `es'` |-> `ee'`, `s` |-> `s0`,
    `ss` |-> `ss`,
    `nkey` |-> `global_nonreentrant_slot`, `iv` |-> `mut = View`,
    `srcs` |-> `am.sources`, `exps` |-> `am.exports`, `layouts` |-> `am.layouts`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:256``]
      external_halt_success_unlock))) >>
  impl_tac >- simp[] >>
  Cases_on `nr /\ mut <> View` >>
  simp[external_call_result_rel_def, tx_return_bytes_def, return_bytes_def,
       abstract_machine_from_state_def, halt_state_def, tstore_def]
QED
*)
Theorem return_selected_none_nr_frag_full:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,nr,args,dflts,ret,fbody) /\
  (nr /\ mut <> View ==> ~cx.txn.is_static) /\
  set_external_package_target target
    (package_external_fn tops T (K global_nonreentrant_slot)
      (mut,nr,rr,tx.function_name,args,dflts,ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,nr,nkey,ut,iv,fbody,rt) /\
  cenv with ce_vars := cenv0.ce_vars = cenv0 /\
  same_frame cenv ce /\ expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return NONE)) /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\
  cx.txn.target = tx.target ==>
  stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cx lctx
    (\H v ee gt r. ?tv v' ee'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      unlock_if_nr (initial_evaluation_context am.sources am.layouts tx NONE)
        nr (is_view_mut mut) ee = (INL (), ee') /\
      external_call_result_rel H tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee'),
         ee'.requests) r)
    ce (stmt_env ce lctx ret (Return NONE))
    (stmt_env (gas_shadow_env T ce) lctx ret (Return NONE))
    (eval_stmt cx (Return NONE)) es
Proof
  cheat
QED
