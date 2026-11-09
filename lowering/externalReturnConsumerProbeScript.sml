Theory externalReturnConsumerProbe
Ancestors
  externalReturnChosenWindow externalReturnPlan vyperLoweringCorrect
  loweringHalt vyperTypeABI vyperTyping vyperValue vyperABI contractABI
  e2eDefs loweringPosts bodySim compileEnv valueEncoding words list

Theorem return_bytes_functional:
  return_bytes tops ret v a /\ return_bytes tops ret v b ==> a = b
Proof
  simp[return_bytes_def] >> rpt IF_CASES_TAC >> rpt strip_tac >> gvs[]
QED

(* Checked conditional producer.  The memory premise names the cast result. *)
Theorem return_consumer_window_conditional:
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) cenv.ce_ret_enc_info /\
  evaluate_type (type_env tops) ret = SOME tv /\
  safe_cast tv v0 = SOME v /\ val_in_memory tv v sb mem /\
  return_bytes tops ret v bytes /\ LENGTH bytes <= cenv.ce_max_return_size ==>
  ?ct rv. abi_encoder_admissible cenv.ce_ret_enc_info /\
    abi_encoder_window_input cenv.ce_ret_enc_info ct rv sb (val_footprint tv v) mem /\
    return_bytes tops ret v (enc ct rv) /\
    LENGTH (enc ct rv) <= cenv.ce_max_return_size
Proof
  strip_tac >>
  `value_has_type tv v` by metis_tac[safe_cast_result_well_typed] >>
  `?av. vyper_to_abi (type_env tops) ret v = SOME av` by
    metis_tac[cj 1 vyper_to_abi_total] >>
  drule_all return_chosen_window >> strip_tac >>
  `enc ct rv = bytes` by metis_tac[return_bytes_functional] >>
  qexistsl_tac [`ct`, `rv`] >> simp[] >> metis_tac[return_plan_admissible]
QED

Theorem return_consumer_cast_memory:
  safe_cast tv v0 = SOME v /\ val_in_memory tv v0 sb mem ==>
  val_in_memory tv v sb mem
Proof
  metis_tac[cj 1 safe_cast_some_eq]
QED

Theorem return_consumer_expression_memory:
  expr_val_rel cx ret v op s /\ get_tenv cx = type_env tops /\
  evaluate_type (type_env tops) ret = SOME tv /\ ~is_word_type ret ==>
  ?w. eval_operand op s = SOME w /\ val_in_memory tv v (w2n w) s.vs_memory
Proof
  simp[expr_val_rel_def] >> metis_tac[]
QED

Theorem return_consumer_bytes_bound:
  evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) <= maxsize ==>
  ?bytes. return_bytes tops ret v bytes /\ LENGTH bytes <= maxsize
Proof
  strip_tac >> drule_all return_abi_value_package >>
  disch_then (qspec_then `needs_external_call_wrap ret /\
    is_dynamic (vyper_to_abi_type (type_env tops) ret)` strip_assume_tac) >>
  gvs[] >> drule chosen_return_abi_bytes >> strip_tac >>
  goal_assum (drule_at Any) >> decide_tac
QED

Theorem return_consumer_frame_metadata:
  same_frame cenv cenv' /\
  abi_enc_plan env ty cenv.ce_ret_enc_info /\
  vyper_abi_size_bound env ty <= cenv.ce_max_return_size ==>
  abi_enc_plan env ty cenv'.ce_ret_enc_info /\
  vyper_abi_size_bound env ty <= cenv'.ce_max_return_size
Proof
  metis_tac[return_same_frame_plan, return_same_frame_capacity]
QED

Theorem return_consumer_window:
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) cenv.ce_ret_enc_info /\
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) <= cenv.ce_max_return_size /\
  evaluate_type (type_env tops) ret = SOME tv /\
  safe_cast tv v0 = SOME v /\ val_in_memory tv v0 sb mem ==>
  ?ct rv. abi_encoder_admissible cenv.ce_ret_enc_info /\
    abi_encoder_window_input cenv.ce_ret_enc_info ct rv sb (val_footprint tv v) mem /\
    return_bytes tops ret v (enc ct rv) /\
    LENGTH (enc ct rv) <= cenv.ce_max_return_size
Proof
  strip_tac >> drule_all return_consumer_bytes_bound >> strip_tac >>
  drule_all return_consumer_cast_memory >> strip_tac >>
  drule_all return_consumer_window_conditional >> simp[]
QED
