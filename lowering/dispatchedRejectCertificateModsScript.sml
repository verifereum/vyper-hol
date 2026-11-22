(* Package the installed nonpayable prefix as a linked execution certificate. *)
Theory dispatchedRejectCertificateMods
Ancestors
  dispatchedValuePrefix sourceUnitExecutionMods e2eModsDefs vyperLoweringCorrect
  loweringStateRelDefs vyperTypeContractSoundness compileEnv entryRejectCode
  moduleLoweringProps venomInst gasShadowUnit gasShadowState fragGasOrigin
  ptrSafeRun ptrDiscipline venomExecSemantics venomState fragExec
  vyperStorageFootprint vyperContext vyperInterpreter words finite_map list

Theorem linked_installed_reject_certificate:
  unit.cu_context.ctx_entry = SOME "__entry" /\
  venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME "__entry" /\
  EVERY (\(s,l). s < 2 ** 32) selectors /\
  compile_selector_dispatch_linear selectors fl ds = ((),de) /\
  fn_has_code ds de fn /\ ds.cs_current_bb = "__entry" /\
  ds.cs_current_insts = [] /\
  compile_entry_checks mc F opened = ((),checked) /\
  fn_has_code opened checked fn /\ opened.cs_current_insts = [] /\
  ~block_is_terminated opened /\
  opened.cs_current_bb = linear_dispatch_target vs.vs_call_ctx.cc_calldata selectors fl /\
  source_typing_ok_mods mods exps am tx /\
  initial_venom_state_rel_mods mods am tx vs /\
  gas_shadow_context unit.cu_context shadow_ctx /\
  tx.value <> 0 /\
  (!gobs. call_external_trace (SOME vs.vs_outcomes) gobs am tx =
    (INR (Error (RuntimeError "not Payable")),am,[],[])) ==>
  source_unit_execution_correct_with_mods shadow_ctx [] mods exps ret am tx unit vs
Proof
  strip_tac >>
  `MEM fn unit.cu_context.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `?shadow_fn. MEM shadow_fn shadow_ctx.ctx_functions /\
      gas_shadow_function fn shadow_fn` by
    (fs[gas_shadow_context_def] >> metis_tac[LIST_REL_MEM_IMP]) >>
  qabbrev_tac `ss = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry";
                            vs_inst_idx := 0|>` >>
  `LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256)` by
    (fs[Abbr `ss`, source_typing_ok_mods_def, initial_venom_state_rel_mods_def,
        venom_env_rel_def] >> drule_all call_ctx_rel_calldata_length >> simp[]) >>
  `ss.vs_call_ctx.cc_callvalue <> 0w` by
    gvs[Abbr `ss`, source_typing_ok_mods_def, initial_venom_state_rel_mods_def,
        venom_env_rel_def, call_ctx_rel_def, call_tx_well_typed_def, dimword_def, n2w_11] >>
  `ss.vs_call_ctx = vs.vs_call_ctx /\ ss.vs_current_bb = ds.cs_current_bb /\
   ss.vs_inst_idx = 0 /\ fresh_vars_wrt ds ss /\ ~ss.vs_halted /\
   allocas_from 0 ss /\ allocas_below_fmp ss` by
    fs[Abbr `ss`, initial_venom_state_rel_mods_def, fresh_vars_wrt_def,
       allocas_from_def, allocas_below_fmp_def] >>
  `?preabort. vars_pc_only ss preabort /\
    gas_origin_path T (gas_explicit_sites unit.cu_context shadow_ctx)
      unit.cu_context fn ss []
      (Abort Revert_abort (revert_state (set_returndata [] preabort)))` by
    (irule installed_dispatch_value_reject_origin >>
     simp[] >> conj_tac >- (qexists_tac `0` >> simp[]) >>
     qexistsl_tac [`checked`, `fl`, `mc`, `opened`, `selectors`, `ds`, `de`] >>
     fs[]) >>
  `!D PG G tn fuel. ptr_safe_blocks D 0 fuel unit.cu_context fn PG G tn ss` by
    (irule installed_dispatch_value_reject_ptr >>
     simp[] >> qexistsl_tac [`checked`, `fl`, `mc`, `opened`, `selectors`, `ds`, `de`] >>
     fs[]) >>
  suspend "certificate"
QED

Resume linked_installed_reject_certificate[certificate]:
  rewrite_tac[source_unit_execution_correct_with_mods_def] >>
  qexistsl_tac [`fn`, `shadow_fn`] >>
  asm_rewrite_tac[] >> disj2_tac >>
  qexistsl_tac [`INR (Error (RuntimeError "not Payable"))`, `am`, `[]`, `[]`] >>
  asm_rewrite_tac[] >> disj2_tac >>
  qexists_tac `Abort Revert_abort (revert_state (set_returndata [] preabort))` >>
  simp[GSYM markerTheory.Abbrev_def] >>
  simp[exit_result_def, storage_trace_domain_def, valid_horizon_def,
       storage_observations_ok_def, storage_trace_horizon_def,
       storage_trace_regions_def, storage_trace_locks_def, regions_consistent_def,
       storage_locks_separated_def, storage_well_formed_on_def, storage_roots_fit_def,
       storage_trace_backends_well_formed_def, external_call_result_rel_mods_def]
QED

Finalise linked_installed_reject_certificate
