(* Request-prefix certificates for the selected and rejected runtime entry routes. *)
Theory s1PrefixRuntimeUnit
Ancestors
  s1PrefixDefs s1PrefixUnitCompose s1PrefixDispatchedEndpoint s1PrefixBodyStart
  s1PrefixSelectedTrace s1PrefixOutOfDomain runtimePeakMemoryBound
  vyperStorageTrace exprSimHypsDefs

val _ = Parse.hide "tops";

Theorem unit_prefix_cert_holds:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
  supported_program tops /\
  source_typing_ok tops am tx /\
  source_deployment_rel tops am tx /\
  dispatched_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
  LENGTH vs.vs_call_ctx.cc_calldata < 2 ** 64 /\
  initial_venom_state_rel tops am tx vs /\
  code_layout_valid vs /\
  EVERY (\oc. LENGTH oc.co_returnData < dimword(:256) /\
               accounts_runtime_well_typed oc.co_accounts) vs.vs_outcomes /\
  LENGTH vs.vs_outcomes < 2 ** 64 /\
  vs.vs_fmp = vs.vs_initial_fmp /\
  w2n vs.vs_initial_fmp < 2 ** 254 /\
  unit_alloca_budget unit.cu_context +
    32 * ctx_dload_count unit.cu_context <= w2n vs.vs_initial_fmp ==>
  unit_prefix_cert shadow_unit.cu_context tops am tx unit vs
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dispatched_prefix_endpoint_cases >>
  disch_then (DISJ_CASES_THEN2 ACCEPT_TAC
    (qx_choosel_then [`mut`,`nr`,`args`,`dflts`,`fbody`,`es0`] strip_assume_tac)) >>
  `outcomes_accounts_typed (SOME vs.vs_outcomes)` by simp[outcomes_accounts_typed_def] >>
  `(ctx_has_dalloca unit.cu_context ==>
    !fn inst s. raw_reachable vs unit.cu_context fn inst s ==>
      dalloca_fmp_headroom inst s)` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC lower_vyper_runtime_unit_raw_headroom) >>
  drule_all runtime_prefix_body_start_cases >>
  disch_then
    (qx_choosel_then [`cx`,`entry`,`func`,`marks`,`G0`,`tn0`,`s0`] strip_assume_tac) >>
  Cases_on `storage_trace_domain cx (initial_state am []) es_lock.storage_trace`
  >- (qpat_assum `storage_trace_domain _ _ _ ==> _`
        (drule_then (qx_choosel_then
          [`compiled_body`,`shadow_func`,`cenv`,`RetQ`,`sl`,`sb`,
           `shadow_sl`,`shadow_sb`,`t`,`G`,`tn`,`cenv'`] strip_assume_tac)) >>
      `gas_prefix_full ((\H. cx_dead H cx),0,
         gas_explicit_sites unit.cu_context shadow_unit.cu_context,unit.cu_context,func,[])
         cx (initial_state am []) (eval_stmts cx compiled_body) (es_lock,t,G,tn)` by
        (qhdtm_x_assum `stmt_frag_prefix`
           (irule o PURE_ONCE_REWRITE_RULE[stmt_frag_prefix_def]) >>
         qexistsl_tac [`cenv'`,`sl`,`sb`,`shadow_sl`,`shadow_sb`] >>
         (* Unfold the precondition to erase its unused polymorphic parameters. *)
         qhdtm_x_assum `stmt_frag_full_pre` mp_tac >>
         pure_rewrite_tac[stmt_frag_full_pre_def] >> disch_then ACCEPT_TAC) >>
      drule_all selected_prefix_trace_alignment >> strip_tac >>
      irule (INST_TYPE [``:'a`` |-> ``:unit``] unit_prefix_cert_from_body) >>
      (conj_tac >- first_assum ACCEPT_TAC) >>
      qexistsl_tac [`G`,`cx`,`entry`,`marks`,`es_lock`,
                   `gas_explicit_sites unit.cu_context shadow_unit.cu_context`,
                   `func`,`eval_stmts cx compiled_body`,`t`,`tn`] >>
      asm_rewrite_tac[evaluate_storage_trace_frame]) >>
  (* Outside the trace domain, alignment uses the original source body. *)
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`compiled_body` |-> `fbody`] selected_prefix_trace_alignment)) >> strip_tac >>
  irule (INST_TYPE [``:'a`` |-> ``:unit``] out_of_domain_unit_prefix_cert) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`storage_trace_horizon es0.storage_trace`,`cx`,`entry`,`es_lock`,`s0`,
               `func`,`func`,`G0`,`[]`,`tn0`,`marks`,`eval_stmts cx fbody`] >>
  asm_rewrite_tac[evaluate_storage_trace_frame]
QED
