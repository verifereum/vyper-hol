(* Absent-default selector routing shares a single terminating certificate. *)
Theory calldataNoneFallbackJoint
Ancestors entryDispatchRevert defaultDispatchPlacement defaultDispatchRouting
  entryValueRevertPtr entryReachBodyFmp vyperLoweringCorrect vyperCompiler
  entryDispatchProps entryDispatchPtr compileVyper vyperCalldata
  loweringShapeProps loweringShapeDefs moduleLowering moduleLoweringProps
  compileEnv emitHelperProps fragExec contextCodegenRel venomInst venomState
  venomExecSemantics venomWf ptrSafeRun ptrDiscipline fragGasOriginPtr
  list pair finite_map

Theorem absent_default_fold[local]:
  !tops. ~EXISTS is_default_decl tops ==>
    FST (SND (SND (FOLDR classify_function ([],[],NONE,NONE) tops))) = NONE
Proof
  Induct >> simp[] >> gen_tac >>
  Cases_on `h` >> simp[is_default_decl_def, classify_function_def] >>
  Cases_on `f` >>
  qabbrev_tac `acc = FOLDR classify_function ([],[],NONE,NONE) tops` >>
  PairCases_on `acc` >> gvs[GSYM markerTheory.Abbrev_def] >>
  simp[is_default_decl_def, classify_function_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem none_fallback_entry_joint:
  !tops rpolicy unit am tx vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\ source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\ initial_venom_state_rel tops am tx vs /\
    ~EXISTS is_default_decl tops /\
    (LENGTH vs.vs_call_ctx.cc_calldata < 4 \/
     FIND (\(name,tys). abi_method_id (type_env tops) name tys =
       cd_selector vs.vs_call_ctx.cc_calldata) (abi_external_signatures tops) = NONE) ==>
    ?func s G' tn'.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\ s.vs_returndata = [] /\
      (!D explicit. gas_origin_ptr_path (D,0,explicit,unit.cu_context,func,[])
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0|>,FEMPTY,entry_taint) []
        (Abort Revert_abort s,G',tn')) /\
      (?bb. lookup_block "__entry" func.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\
      entry_prov func
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0|>) FEMPTY = FEMPTY /\
      entry_taint_vars func
        (vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                   vs_inst_idx := 0|>) entry_taint = entry_taint
Proof
  rpt gen_tac >> strip_tac >>
  drule lower_vyper_runtime_unit_context_entry >> strip_tac >>
  rename1 `venomInst$lookup_function "__entry" _ = SOME func` >>
  `?elbl. fn_entry_label func = SOME elbl` by
    (drule venomInstTheory.lookup_function_MEM >> strip_tac >>
     gvs[lowering_context_ok_def, EVERY_MEM] >>
     qpat_x_assum `!fn. MEM fn _ ==> ALL_DISTINCT _ /\ fn_has_entry fn` drule >>
     simp[fn_has_entry_def, fn_entry_label_def, entry_block_def] >>
     Cases_on `func.fn_blocks` >> simp[]) >>
  drule_all default_runtime_compile_layout >> strip_tac >>
  `FST (SND (SND (classify_functions tops))) = NONE` by
    (drule absent_default_fold >>
     simp[classify_functions_def] >> rpt (pairarg_tac >> gvs[])) >>
  `fbpkg = NONE` by simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  `emit_inst REVERT [Lit 0w; Lit 0w] [] checks = ((),entry_end)` by
    (qpat_x_assum `(case fbpkg of NONE => _ | SOME _ => _) checks = _` mp_tac >>
     simp[]) >>
  `checks.cs_current_bb = fallback /\ checks.cs_current_insts = []` by
    (qpat_x_assum `new_block _ _ = _` mp_tac >>
     simp[new_block_def] >> strip_tac >> gvs[]) >>
  `elbl = "__entry"` by
    (qpat_x_assum `fresh_label _ _ = _` mp_tac >>
     simp[fresh_label_def, initial_compile_state_def] >> strip_tac >> gvs[]) >>
  FAIL_TAC "installed"
QED
