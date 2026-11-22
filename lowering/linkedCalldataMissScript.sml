(* Reuse the linear fallback revert certificate with linked ABI tables. *)
Theory linkedCalldataMiss
Ancestors
  defaultDispatchModsRun dispatchedClassifiedRouteMods
  e2eModsDefs sourceUnitExecutionMods vyperLoweringCorrect
  entryRejectCode entryJointRevertExit entryDispatchRevert entryDispatchPtr
  entryDispatchProps compileUnit compileVyper vyperCompiler loweringStateRelDefs
  vyperCalldata vyperContext fragGasOriginPtr fragGasPathMem fragGasPathPtr
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst finite_map

Theorem lower_vyper_runtime_unit_linear_miss_reverts_mods:
  !mods exps rpolicy unit am tx vs exts ints ctor imp_ctors.
    lower_vyper_runtime_unit_mods mods exps rpolicy = SOME unit /\
    source_typing_ok_mods mods exps am tx /\
    initial_venom_state_rel_mods mods am tx vs /\
    classify_functions_unit mods exps = (exts,ints,NONE,ctor,imp_ctors) /\
    ~EXISTS (external_has_defaults o SND) exts /\
    (LENGTH vs.vs_call_ctx.cc_calldata < 4 \/
     FIND (\(name,tys). abi_method_id (type_env_all_modules mods) name tys =
       cd_selector vs.vs_call_ctx.cc_calldata) (abi_deployed_signatures mods exps) = NONE) ==>
    ?func s G' tn'.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      s.vs_returndata = [] /\
      (?fuel. run_context fuel unit.cu_context vs = Abort Revert_abort s) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (Abort Revert_abort s) /\
      (!D. gas_path_ptr D 0 unit.cu_context func [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                         vs_inst_idx := 0 |>) 0 G' tn' (Abort Revert_abort s)) /\
      (!D fuel. ptr_safe_blocks D 0 fuel unit.cu_context func [] FEMPTY entry_taint
                  (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                              vs_inst_idx := 0 |>))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (SIMP_RULE bool_ss [LET_THM] default_unit_linear_run) >>
  simp[package_fallback_fn_unit_def, set_fallback_package_target_def] >>
  disch_then (qx_choose_then `ips` strip_assume_tac) >>
  drule_then strip_assume_tac run_lowering_entry >>
  rename1 `venomInst$lookup_function "__entry" _ = SOME func` >>
  drule_all_then assume_tac run_lowering_entry_label >>
  drule_all run_lowering_fallback_revert_code >>
  disch_then (qx_choosel_then [`fallback`,`label_st`,`dispatch_st`,`checks`,`entry_end`]
    strip_assume_tac) >>
  qabbrev_tac `ss = vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                               vs_inst_idx := 0 |>` >>
  qabbrev_tac `sels = MAP (\(sel,lbl,z). (sel,lbl))
    (build_selectors (type_env_all_modules mods) (MAP SND exts))` >>
  `LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256)` by
    (simp[Abbr `ss`] >>
     gvs[source_typing_ok_mods_def, initial_venom_state_rel_mods_def,
         venom_env_rel_def] >> drule_all_then ACCEPT_TAC call_ctx_rel_calldata_length) >>
  `fresh_vars_wrt label_st ss /\ ~ss.vs_halted /\ allocas_from 0 ss /\
   allocas_below_fmp ss` by
    gvs[Abbr `ss`, initial_venom_state_rel_mods_def, fresh_vars_wrt_def,
        allocas_from_def, allocas_below_fmp_def] >>
  `EVERY (\(sel,lbl). sel < 2 ** 32) sels` by
    simp[Abbr `sels`, linear_selectors_lt] >>
  `linear_dispatch_target ss.vs_call_ctx.cc_calldata sels fallback = fallback` by
    (drule_all linked_classified_linear_routes >>
     disch_then (qspec_then `vs.vs_call_ctx.cc_calldata` (mp_tac o CONJUNCT1)) >>
     simp[Abbr `ss`, Abbr `sels`]) >>
  qpat_assum `Abbrev (sels = _)` (fn th =>
    qpat_x_assum `compile_selector_dispatch_linear _ _ _ = _`
      (assume_tac o REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])) >>
  drule linear_dispatch_fallback_revert_joint >>
  disch_then (qspecl_then [`entry_taint`,`ss`,`entry_end`,`checks`] mp_tac) >>
  disch_then (qspecl_then [`0`,`func`,`unit.cu_context`] mp_tac) >>
  disch_then (qspecl_then [`[]`,`FEMPTY`] mp_tac) >>
  impl_tac >- simp[Abbr `ss`] >>
  disch_then (qx_choosel_then [`s`,`G'`,`tn'`] strip_assume_tac) >>
  drule_all compile_selector_dispatch_linear_layout >> strip_tac >>
  `entry_prov func ss FEMPTY = FEMPTY /\
   entry_taint_vars func ss entry_taint = entry_taint` by
    (Cases_on `b0.bb_instructions` >>
     gvs[get_instruction_def, mk_inst_def, entry_prov_def, entry_taint_vars_def,
         phis_prov_def, phis_taint_def, Abbr `ss`]) >>
  qexistsl [`func`,`s`,`G'`,`tn'`] >> simp[] >>
  qspecl_then [`unit.cu_context`,`func`,`vs`,`s`,`G'`,`tn'`,`[]`]
    mp_tac entry_joint_revert_exit >>
  simp[Abbr `ss`]
QED
