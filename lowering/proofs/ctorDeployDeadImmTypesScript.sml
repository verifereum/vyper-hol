(* A successful load_contract records each immutable of the target at its
 * declared type.
 *)
Theory ctorDeployDeadImmTypes
Ancestors
  ctorDeployDeadLoad ctorDeployDefs e2eDeployDefs e2eDefs vyperInterpreter
  vyperTypeContractSoundness vyperTypeInitialState vyperTypeContract

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
