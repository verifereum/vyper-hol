(* Presentation layer for iterating on the call theorem without changing
 * the shared boundary definitions or rebuilding their consumers. *)
Theory e2eCorrectnessTop
Ancestors
  e2eCorrectness e2eDefs vyperTypeContract vyperTypeContractSoundness
  vyperTypeInitialState vyperContext vyperInterpreter vyperCall
  compileVyper supportedProgram vfmExecution callTrace

(* TOP-LEVEL: typing requirements not already supplied by deployment. *)
Definition source_typing_ok_top_def:
  source_typing_ok_top tops am tx <=>
    ?art. check_contract F am.layouts tx.target [(NONE, tops)] = SOME art /\
          immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
            (initial_evaluation_context am.sources am.layouts tx NONE)
            am.immutables /\
          machine_well_typed am /\ call_tx_well_typed tx
End

Theorem source_typing_ok_top_imp:
  source_typing_ok_top tops am tx /\ source_deployment_rel tops am tx ==>
  source_typing_ok tops am tx
Proof
  rw[source_typing_ok_top_def, source_deployment_rel_def,
     source_typing_ok_def] >>
  qexists_tac `art` >>
  simp[checked_contract_runtime_ready_def] >>
  metis_tac[check_contract_single_module_exports_ok]
QED

Theorem vyper_call_correct_top:
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ immutable_free_program tops /\
    source_typing_ok_top tops am tx /\
    source_storage_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx (buffer_to_list (FST (HD es.contexts)).msgParams.data) ret /\
    call_outcomes_storage_ok am tx (MAP SND (call_trace es))
    ==>
    ?result es'.
      run_call es = SOME (result, es') /\
      (frame_resource_starved es result es' \/
       call_result_rel tops ret am tx es result es')
Proof
  rpt strip_tac >>
  `source_deployment_rel tops am tx` by fs[call_state_rel_def] >>
  `source_typing_ok tops am tx` by metis_tac[source_typing_ok_top_imp] >>
  metis_tac[vyper_call_correct]
QED
