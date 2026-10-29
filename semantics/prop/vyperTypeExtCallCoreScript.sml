(* Shared concrete/oracle typing boundaries, below evaluator integration.
   Original proof bodies moved unchanged from vyperTypeExtCallSoundness. *)
Theory vyperTypeExtCallCore
Ancestors
  list finite_map option pair sum
  vyperAST vyperValue vyperABI vyperInterpreter vyperState vyperContext
  vyperRuntimeAccounts vyperTyping vyperTypeSystem vyperTypeInvariants
  vyperTypeValues vyperTypeEnv vyperTypeABI vyperTypeExprResult vyperTypeExprSoundness
Libs monadsyntax

val () = monadsyntax.enable_monad "vyper_evaluation";

Theorem accounts_runtime_well_typed_accounts_well_typed:
  !acc. accounts_runtime_well_typed acc <=> accounts_well_typed acc
Proof
  simp[accounts_runtime_well_typed_def, accounts_well_typed_def,
       account_runtime_well_typed_def, account_well_typed_def]
QED

Theorem evaluate_abi_decode_return_well_typed:
  !tenv ret_type bs v tv.
    evaluate_abi_decode_return tenv ret_type bs = INL v /\
    evaluate_type tenv ret_type = SOME tv ==>
    value_has_type tv v
Proof
  rpt strip_tac >>
  gvs[evaluate_abi_decode_return_def, AllCaseEqs(), LET_THM] >>
  TRY (metis_tac[evaluate_abi_decode_returndata_well_typed]) >>
  `evaluate_type tenv (TupleT [ret_type]) = SOME (TupleTV [tv])` by (
    imp_res_tac (cj 1 evaluate_type_well_formed) >>
    imp_res_tac well_formed_type_value_slot_size >>
    gvs[evaluate_type_def, OPT_MMAP_def, type_slot_size_def,
        wordsTheory.dimword_def]) >>
  drule_all evaluate_abi_decode_returndata_well_typed >> strip_tac >>
  gvs[value_has_type_inv, value_has_type_def]
QED

Theorem runtime_consistent_get_tenv:
  runtime_consistent env cx st ==> get_tenv cx = env.type_defs
Proof
  rw[runtime_consistent_def, env_consistent_def, env_context_consistent_def]
QED
