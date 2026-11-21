(* Absent-default selector routing shares a single terminating certificate. *)
Theory calldataNoneFallbackJoint
Ancestors entryDispatchRevert entrySourcePackages entryRejectCode defaultDispatchRouting
  entryValueRevertPtr vyperLoweringCorrect vyperCompiler
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
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
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
  drule_all lower_runtime_default_free_packages >> strip_tac >>
  drule_all run_lowering_entry_label >> strip_tac >>
  `FST (SND (SND (classify_functions tops))) = NONE` by
    (drule absent_default_fold >>
     simp[classify_functions_def] >> rpt (pairarg_tac >> gvs[])) >>
  `fb = NONE` by simp[package_fallback_fn_def, set_fallback_package_target_def] >>
  qpat_x_assum `fb = NONE` SUBST_ALL_TAC >>
  drule_all run_lowering_fallback_revert_code >>
  disch_then (qx_choosel_then [`fallback`, `label_st`, `dispatch_st`,
       `checks`, `entry_end`] strip_assume_tac) >>
  qabbrev_tac `ss = vs with <|vs_prev_bb := NONE;
    vs_current_bb := "__entry"; vs_inst_idx := 0|>` >>
  `allocas_below_fmp ss` by
    (irule initial_entry_allocas_below_fmp >>
     goal_assum (drule_at Any) >> simp[Abbr `ss`, vars_pc_only_def]) >>
  `fresh_vars_wrt label_st ss /\ ~ss.vs_halted /\ allocas_from 0 ss /\
   LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256)` by
    (drule_all initial_entry_dispatch_scalars >>
     disch_then (qspecl_then [`0`, `"__entry"`, `label_st`] mp_tac) >>
     simp[Abbr `ss`]) >>
  `EVERY (\(sel,lbl). sel < 2 ** 32)
    (MAP (\(sel,lbl,z). (sel,lbl)) sels)` by
    (qspecl_then [`type_env tops`, `FST (classify_functions tops)`]
       mp_tac linear_selectors_lt >> simp[]) >>
  `linear_dispatch_target ss.vs_call_ctx.cc_calldata
     (MAP (\(sel,lbl,z). (sel,lbl)) sels) fallback = fallback` by
    (simp[Abbr `ss`] >> irule default_raw_fallback_target >> simp[]) >>
  drule linear_dispatch_fallback_revert_joint >>
  disch_then (qspecl_then [`entry_taint`, `ss`, `entry_end`, `checks`] mp_tac) >>
  disch_then (qspecl_then [`0`, `func`, `unit.cu_context`] mp_tac) >>
  disch_then (qspecl_then [`[]`, `FEMPTY`] mp_tac) >>
  (impl_tac >- simp[Abbr `ss`]) >> strip_tac >>
  drule_all compile_selector_dispatch_linear_layout >> strip_tac >>
  `phi_prefix_length b0.bb_instructions = 0 /\
   entry_prov func ss FEMPTY = FEMPTY /\
   entry_taint_vars func ss entry_taint = entry_taint` by
    (Cases_on `b0.bb_instructions` >>
     gvs[get_instruction_def, mk_inst_def, phi_prefix_length_def,
       entry_prov_def, entry_taint_vars_def, phis_prov_def, phis_taint_def,
       Abbr `ss`]) >>
  qexistsl_tac [`func`, `s`, `G'`, `tn'`] >> simp[] >> metis_tac[]
QED
