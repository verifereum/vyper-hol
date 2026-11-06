Theory extRetStaticFrameMetadataPtr
Ancestors
  returnMetadataPtr abiEncoderProps vyperABI contractABI

val _ = Parse.hide "body";

Theorem abi_enc_plan_copy_layout[local]:
  abi_enc_plan tenv ty (AbiCopy m) ==>
  ?tv. evaluate_type tenv ty = SOME tv /\
       ~is_dynamic (vyper_to_abi_type tenv ty) /\
       m = type_memory_size tv
Proof
  simp[Once abi_enc_plan_cases] >> metis_tac[]
QED

Theorem external_frame_abicopy_layout:
  set_external_package_target target
    (package_external_fn tops use_trans keys
      (mut, nr, rr, name, args, defaults, ret, body)) =
    (lbl, cenv0, pos, cds, payable, nr', key, ut, view, body', rt) /\
  compile_register_positional_args cenv0 pos off st = (cenv, sa) /\
  same_frame cenv next /\ source_typing_ok tops am tx /\
  assignable_type (type_env tops) ret /\ ret <> NoneT /\
  next.ce_ret_enc_info = AbiCopy m ==>
  ?tv. evaluate_type (type_env tops) ret = SOME tv /\
       ~is_dynamic (vyper_to_abi_type (type_env tops) ret) /\
       m = type_memory_size tv
Proof
  strip_tac >> drule source_typing_distinct_type_keys >> strip_tac >>
  drule_all external_frame_ret_abi_plan >>
  strip_tac >> gvs[] >> drule abi_enc_plan_copy_layout >>
  IF_CASES_TAC >> simp[]
QED
