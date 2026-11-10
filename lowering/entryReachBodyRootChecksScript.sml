Theory entryReachBodyRootChecks
Ancestors
  loweringStateRelDefs externalEntryChecks entryReachBodyInitialResources externalEntryShape
  vyperLoweringCorrect moduleLoweringProps entryDispatchProps entryChecksProps
  compileVyper moduleLowering vyperCompiler venomInst venomState
  supportedProgram vyperState list pair fragExec

Theorem entry_reaches_checks_root:
  !tops rpolicy unit am tx ret vs mut args fbody.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) ==>
    ?rr lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st st' func s0.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops T (K global_nonreentrant_slot)
           (mut, F, rr, tx.function_name, args, ([] : expr list), ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody, rt) /\
      compile_entry_checks min_cds is_payable st = ((), st') /\
      fn_has_code st st' func /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      vars_pc_only vs s0 /\ fresh_vars_wrt st s0 /\ ~s0.vs_halted /\
      s0.vs_current_bb = st.cs_current_bb /\
      s0.vs_inst_idx = LENGTH st.cs_current_insts /\
      !fuel r. run_from fuel unit.cu_context func s0 = r /\
               (!e. r <> Error e) ==>
               ?fuel'. run_context fuel' unit.cu_context vs = r
Proof
  rpt gen_tac >> strip_tac >>
  drule_all selected_external_dispatch >> strip_tac >>
  qspecl_then [`tops`, `rpolicy.rpol_target`, `mut`, `rr`,
               `tx.function_name`, `args`, `ret`, `fbody`]
    strip_assume_tac selected_external_package >>
  drule_all source_runtime_entry_checks_code >> strip_tac >>
  `fn_entry_label func = SOME "__entry"` by
    simp[fn_entry_label_def, entry_block_def, NULL_EQ] >>
  `LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all initial_venom_state_calldata_length >> simp[]) >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    fs[initial_venom_state_rel_def] >>
  `EVERY (\(sel,lbl). sel < 2 ** 32)
     (MAP (\(sel,lbl,z). (sel,lbl))
       (build_selectors (type_env tops) (FST (classify_functions tops))))` by
    simp[linear_selectors_lt] >>
  `linear_dispatch_target vs.vs_call_ctx.cc_calldata
     (MAP (\(sel,lbl,z). (sel,lbl))
       (build_selectors (type_env tops) (FST (classify_functions tops)))) fb =
     st.cs_current_bb` by simp[] >>
  drule_all linear_dispatch_context_reaches >> strip_tac >>
  qexistsl_tac [`rr`, `"fn_" ++ tx.function_name`, `cenv`, `pos_args`,
                `min_cds`, `is_payable`, `nkey`, `ut`, `iv`, `rt`,
                `st`, `st'`, `func`, `s0`] >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  qexists_tac `fuel` >> simp[]
QED
