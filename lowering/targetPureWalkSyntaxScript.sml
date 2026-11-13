(* Task-private mutability boundaries for target walks. *)
Theory targetPureWalkSyntax
Ancestors
  compileVyper vyperReadOnlySyntax vyperTypeCallGraph

Theorem target_walk_deploy_checked_call_probe:
  let ts = [FunctionDecl Deploy Nonpayable F F "ctor" [] [] NoneT []] in
    function_mutability_ok [(NONE,ts)] Deploy Nonpayable F [] [] /\
    call_target_mutability_ok [(NONE,ts)] View (IntCall (NONE,"ctor")) /\
    lookup_callable_function T "ctor" ts =
      SOME (Nonpayable,F,[],[],NoneT,[])
Proof
  EVAL_TAC
QED
