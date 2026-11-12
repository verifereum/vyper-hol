(* The selected nr=F, defaults=[] frame returns without a value through
   one STOP. Source tails and finite horizons share that terminal Halt. *)
Theory externalReturnNoneFullFrag
Ancestors
  externalReturnPackage rawReturnHeader e2eDefs bodySimFull
  fragExec gasOutcomeFullCompose fragGasOriginPtrExec fragGasOriginPtr
  fragGasOrigin fragGasPathPtr fragGasPathMem gasCount fragGasMode
  bodyPtrDefs stmtSimDefs exprSimHypsDefs bodySim
  accountsRelProps loweringStateRelDefs
  stmtLowering moduleLowering moduleLoweringProps compileVyper compileEnv
  exprLoweringProps loweringPosts
  ptrSafeRun ptrDiscipline memSafeRun
  venomInst venomState venomExecSemantics venomExecProofs
  emitHelper emitHelperProps
  vyperTypeSystem vyperInterpreter vyperState vyperValueOperation
  list option finite_map

Theorem return_selected_none_frag_full:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
  source_typing_ok tops am tx /\
  lookup_function NONE tx.function_name External tops =
    SOME (mut,F,args,[],ret,fbody) /\
  set_external_package_target target
    (package_external_fn tops ut nkey_map
      (mut,F,rr,tx.function_name,args,[],ret,fbody)) =
    (lbl,cenv0,pos_args,min_cds,is_payable,F,nkey,ut,iv,fbody,rt) /\
  compile_register_positional_args cenv0 pos_args off st = (cenv,sinit) /\
  same_frame cenv ce /\ expr_sim_inv ce cx env es /\
  IS_SOME (type_stmt env ret (Return NONE)) /\
  cx.sources = am.sources /\ cx.layouts = am.layouts /\
  cx.txn.target = tx.target ==>
  stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func) cx lctx
    (\H v ee gt r. ?tv v'. evaluate_type (type_env tops) ret = SOME tv /\
      safe_cast tv v = SOME v' /\
      external_call_result_rel H tops ret tx
        (INL v', finalize_pending_deletions
          (abstract_machine_from_state am.sources am.exports am.layouts ee),
         ee.requests) r)
    ce (stmt_env ce lctx ret (Return NONE))
    (stmt_env ce lctx ret (Return NONE))
    (eval_stmt cx (Return NONE)) es
Proof
  rpt strip_tac >>
  drule_all return_selected_same_frame_mode >> strip_tac >>
  `ret = NoneT` by gvs[type_stmt_def] >>
  gvs[] >>
  simp[stmt_frag_full_def] >> rpt strip_tac >>
  `ce.ce_ctor_exit_label = NONE` by
    (drule return_package_target_inversion >> strip_tac >>
     drule compile_register_positional_args_cenv >> strip_tac >>
     fs[same_frame_def] >>
     qpat_x_assum `package_external_fn _ _ _ _ = _` mp_tac >>
     simp[package_external_fn_def, update_cenv_nonreentrant_def] >>
     strip_tac >> gvs[] >>
     fs[compile_env_component_equality]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id STOP [] []]` by
    (qpat_x_assum `stmt_env _ _ _ _ sa = _` mp_tac >>
     simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
          comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emit_inst_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[]) >>
  irule gas_outcome_full_intro >>
  qexistsl_tac [`G0`, `es`, `[]`,
    `Halt (halt_state (s0 with vs_returndata := []))`,
    `INR (ReturnException NoneV)`, `tn0`] >>
  conj_tac
  >- simp[Once evaluate_def, raise_def] >>
  qx_gen_tac `H` >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s0.vs_inst_idx =
     SOME (mk_inst sa.cs_next_id STOP [] [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  conj_tac
  >- (irule gas_zero_paths_joint >>
      simp[exit_result_def] >>
      conj_tac
      >- (irule (cj 3 gas_path_mem_rules) >> simp[exit_result_def] >>
          simp[gas_path_mem_edge_def] >>
          qexistsl_tac [`0`, `mk_inst sa.cs_next_id STOP [] []`] >>
          simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
               gas_count_step_def, mk_inst_def, mem_safe_step_def,
               exit_result_def] >>
          fs[mk_inst_def, unitTransformDefsTheory.inst_mem_below_frontier_def,
             contextCodegenRelTheory.source_memory_read_ranges_def,
             codegenRelTheory.source_memory_write_ranges_def]) >>
      irule (cj 3 gas_path_ptr_rules) >> simp[exit_result_def] >>
      simp[gas_path_ptr_edge_def] >>
      qexistsl_tac [`0`, `mk_inst sa.cs_next_id STOP [] []`] >>
      simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
           gas_count_step_def, mk_inst_def, ptr_safe_step_def,
           exit_result_def] >>
      first_x_assum (qspec_then `H` mp_tac) >>
      simp[] >> strip_tac >>
      fs[mk_inst_def, ghost_inv_at_def, stor_taint_ok_at_def,
         ptr_inst_ok_def, access_ok_def, taint_ok_def,
         contextCodegenRelTheory.source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def,
         step_inst_non_invoke, step_inst_base_opcode_eqs] >>
      simp[step_taint_def, halt_state_def, adopt_reset_def, store_taint_def,
           imm_taint_def, ret_taint_def]) >>
  simp[exit_result_def, stmt_exit_ptr_def] >>
  first_x_assum (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  simp[safe_cast_def, external_call_result_rel_def, halt_state_def] >>
  simp[abstract_machine_from_state_def, finalize_pending_deletions_def] >>
  fs[stmt_state_rel_def, state_rel_def] >>
  drule_all source_typing_none_return_plain >> strip_tac >>
  `accounts_agree H cx
    (process_deletions s0.vs_pending_deletions es.accounts)
    (process_deletions s0.vs_pending_deletions s0.vs_accounts)` by
    (irule accounts_agree_process_deletions >> fs[accounts_rel_def]) >>
  fs[tx_return_bytes_def, return_bytes_def,
     logs_correspond_def, log_entry_corresponds_def,
     logs_rel_def, log_entry_equiv_def, accounts_rel_def,
     request_agree_def, accounts_agree_def, transient_agree_def,
     initial_evaluation_context_def] >>
  gvs[] >>
  `log_entry_corresponds (compiled_event_info tops) (type_env tops) tx.target =
   log_entry_equiv ce tx.target` by
    simp[FUN_EQ_THM, log_entry_corresponds_def, log_entry_equiv_def] >>
  `request_agree H
    (initial_evaluation_context am.sources am.layouts tx NONE) =
   request_agree H cx` by
    simp[FUN_EQ_THM, request_agree_def, accounts_agree_def,
         transient_agree_def, initial_evaluation_context_def] >>
  fs[initial_evaluation_context_def]
QED
