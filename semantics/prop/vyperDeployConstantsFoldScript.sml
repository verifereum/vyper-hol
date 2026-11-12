(*
 * After a checked single-module deployment, the constants fold over the
 * deployed contract's immutables succeeds, and its constants are the ones
 * stored there.
 *)
Theory vyperDeployConstantsFold
Ancestors
  vyperInterpreter vyperState vyperTypeContract vyperTypeConstantFold
  vyperTypeContractSoundness

(* Intuition: evaluate_all_constants stores the fold's cenv over the initial
   main-module slot (constants_fold_evaluate_module_constants, from
   contract_constants_ok); the constructor, type-checked by check_contract T,
   writes no Constant name (no constant is an assignable bare global); and
   constants_fold_module_imms_independent moves the fold to the deployed
   immutables. *)
Theorem load_contract_establishes_constants_fold:
  load_contract orc gobs am deploy_tx [(NONE, tops)] exps = INL (am_deployed,rqs) /\
  am_deployed.sources <> am.sources /\
  check_contract T layouts deploy_tx.target [(NONE, tops)] = SOME art ==>
  ?imms cenv.
    ALOOKUP am_deployed.immutables deploy_tx.target = SOME imms /\
    constants_fold_module [(NONE, tops)] imms NONE tops FEMPTY = SOME cenv /\
    cenv SUBMAP get_source_immutables NONE imms
Proof
  cheat
QED
