(* What a successful load_contract leaves for the deploy dead-transport:
 * its sources and layouts.
 *)
Theory ctorDeployDeadLoad
Ancestors
  ctorDeployDefs vyperInterpreter vyperTypeContractSoundness
  vyperTypeDeploymentMachine typedCopyProducer

Theorem load_contract_sources_layouts:
  !orc gobs am tx mods exps am' rqs.
    load_contract orc gobs am tx mods exps = INL (am', rqs) ==>
    am'.sources = (tx.target, mods) :: am.sources /\
    am'.layouts = am.layouts
Proof
  rpt strip_tac >>
  `!srcs lay t. (initial_evaluation_context srcs lay t NONE).txn = t` by
    simp[initial_evaluation_context_def] >>
  drule load_contract_success_constructor_constants_context >> strip_tac >>
  `am_ctor.sources = am_c.sources` by
    (drule_at (Pos (el 2)) call_external_function_deploy_success_cases >>
     simp[] >> disch_then (qspec_then `am_c` mp_tac) >>
     impl_tac >- fs[] >> strip_tac >>
     simp[abstract_machine_from_state_def]) >>
  drule evaluate_all_constants_preserves_machine_static_components >>
  simp[]
QED

Theorem deploy_source_ok_struct_args_unique:
  !tops am tx. deploy_source_ok tops am tx ==> struct_args_unique tops
Proof
  rw[deploy_source_ok_def, e2eDeployDefsTheory.deploy_typing_ok_def] >>
  metis_tac[checked_contract_struct_args_unique]
QED
