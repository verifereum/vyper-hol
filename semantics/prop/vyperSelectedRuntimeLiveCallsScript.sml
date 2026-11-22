(* External selection puts each outgoing runtime call in the checker live set. *)
Theory vyperSelectedRuntimeLiveCalls
Ancestors
  alist list
  vyperInterpreter vyperTypeContract vyperTypeContractContext
  vyperTypeSelectedEntry vyperTypeContractSoundness vyperReadOnlySyntax
  vyperDeployLiveClosure vyperTypeCallGraph vyperTypeCallGraphSoundness

Theorem selected_runtime_entry_live_calls:
  check_contract F am.layouts tx.target mods = SOME art /\
  exports_ok am.layouts tx.target mods exps /\
  (ALOOKUP am.exports tx.target = SOME exps \/
   exps = [] /\ ALOOKUP am.exports tx.target = NONE) /\
  selected_entry am tx mods (mut,nr,args,ds,ret,b) /\
  src = find_function_module am tx.target tx.function_name /\
  ALOOKUP mods src = SOME ts ==>
  module_allocated am.layouts tx.target src ts /\
  EVERY (\k. MEM k (live_functions am.layouts tx.target mods))
    (function_int_calls ds b)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_asm1_tac
  >- (Cases_on `ALOOKUP am.exports tx.target` >> gvs[find_function_module_def]
      >- metis_tac[check_contract_main_module_allocated] >>
      Cases_on `ALOOKUP exps tx.function_name` >> gvs[]
      >- metis_tac[check_contract_main_module_allocated] >>
      qpat_x_assum `exports_ok _ _ _ _`
        (assume_tac o CONJUNCT1 o REWRITE_RULE [exports_ok_def]) >>
      rename1 `ALOOKUP exps tx.function_name = SOME sid` >>
      `MEM (tx.function_name,sid) exps` by metis_tac[ALOOKUP_MEM] >>
      gvs[EVERY_MEM] >>
      qpat_x_assum `!e. MEM e exps ==> _`
        (qspec_then `(tx.function_name,sid)` mp_tac) >>
      gvs[]) >>
  qpat_x_assum `_ \/ _` kall_tac >>
  drule_all selected_entry_checked_cases >> strip_tac >> gvs[]
  >- (drule_then assume_tac ALOOKUP_MEM >>
      simp[EVERY_MEM] >> rpt strip_tac >>
      irule (CONJUNCT2 deploy_live_functions_closed) >>
      qexists `(find_function_module am tx.target tx.function_name,tx.function_name)` >>
      conj_tac
      >- (irule (CONJUNCT1 deploy_live_functions_closed) >> metis_tac[]) >>
      irule contract_call_edges_function >> metis_tac[]) >>
  `ds = []` by metis_tac[external_getter_defaults] >>
  `int_calls_stmts b = []` by metis_tac[selected_public_getter_body_int_calls_empty] >>
  simp[function_int_calls_def, int_calls_expr_def]
QED
