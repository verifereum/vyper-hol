(* What a successful load_contract leaves for the deploy dead-transport:
 * its sources and layouts, and the declared types of the target's
 * immutables.
 *)
Theory ctorDeployDeadLoad
Ancestors
  ctorDeployDefs vyperInterpreter vyperTypeContractSoundness
  typedCopyProducer

Theorem load_contract_sources_layouts:
  !orc gobs am tx mods exps am' rqs.
    load_contract orc gobs am tx mods exps = INL (am', rqs) ==>
    am'.sources = (tx.target, mods) :: am.sources /\
    am'.layouts = am.layouts
Proof
  cheat
QED

Theorem load_contract_immutables_typed:
  !tops am tx gobs am' rqs pre vis name ty slot post tv v.
    deploy_source_ok tops am tx /\
    load_contract NONE gobs am tx [(NONE, tops)] [] = INL (am', rqs) /\
    tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
    FLOOKUP (get_source_immutables NONE (account_immutables am' tx.target))
      name = SOME (tv,v) ==>
    evaluate_type (type_env tops) ty = SOME tv
Proof
  cheat
QED

Theorem deploy_source_ok_struct_args_unique:
  !tops am tx. deploy_source_ok tops am tx ==> struct_args_unique tops
Proof
  rw[deploy_source_ok_def, e2eDeployDefsTheory.deploy_typing_ok_def] >>
  metis_tac[checked_contract_struct_args_unique]
QED
