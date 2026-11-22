Theory dispatchedDecodedBindMods
Ancestors
  dispatchedDecodeDomain dispatchedDecodeCast vyperTypeABI
  vyperTypeBindArguments vyperTyping list

Theorem decoded_parameters_bind:
  OPT_MMAP (evaluate_type tenv) (MAP SND args) = SOME tvs /\
  calldata_decode_args cd tvs 0 = SOME vals ==>
  ?env. bind_arguments tenv args vals = SOME env
Proof
  strip_tac >>
  drule_then assume_tac evaluate_types_cd_cast_domain >>
  drule_all calldata_decode_args_safe_cast >> strip_tac >>
  drule_then assume_tac OPT_MMAP_LIST_REL >>
  irule bind_arguments_succeeds_stmt >>
  gvs[LIST_REL_EL_EQN, EL_MAP] >>
  rpt strip_tac >>
  metis_tac[safe_cast_result_well_typed]
QED
