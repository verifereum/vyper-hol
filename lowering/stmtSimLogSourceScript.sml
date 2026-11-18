Theory stmtSimLogSource
Ancestors
  eventTopicProps
  vyperEventSoundness vyperTypeABI compileEnv exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
   supportedTypes e2eDefs vyperTyping vyperValue vyperABI
  vyperEvent valueEncoding vyperInterpreter vyperState  vyperExprNoControl

Theorem log_event_word_topic:
  supported_event_leaf_type ty /\ ~is_bytestring_type ty /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  encode_event_topic ty v = SOME (typed_val_to_w256 tv v)
Proof
  strip_tac >>
  `is_word_type ty` by
    (Cases_on `ty` >>
     gvs[supported_event_leaf_type_def, supported_scalar_type_def,
         supported_word_type_def, supported_string_type_def,
         is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[supported_word_type_def, supported_string_type_def,
         is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[supported_word_type_def, supported_string_type_def,
         is_bytestring_type_def, is_word_type_def]) >>
  metis_tac[word_topic_encoding]
QED

Theorem log_scalar_abi_exists:
  supported_scalar_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v ==>
  ?av. vyper_to_abi tenv ty v = SOME av
Proof
  metis_tac[cj 1 vyper_to_abi_total]
QED

Theorem log_event_source_encoded:
  lookup_event_metadata tenv sources target id = SOME (h, tys, flags) /\
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\
                            value_has_type tv v) tys vals /\
  LENGTH flags = LENGTH tys ==>
  ?topics avs.
    encode_indexed_event_topics flags tys vals = SOME topics /\
    vyper_to_abi_list tenv (log_non_indexed_types flags tys)
      (log_non_indexed_values flags vals) = SOME avs /\
    encode_source_event tenv sources target id vals =
      SOME <| logger := target; topics := n2w h :: topics;
              data := enc (Tuple (vyper_to_abi_types tenv
                                  (log_non_indexed_types flags tys)))
                          (ListV avs) |>
Proof
  strip_tac >>
  drule_all typed_event_args_total >> strip_tac >>
  `LENGTH flags = LENGTH vals` by metis_tac[listTheory.LIST_REL_LENGTH] >>
  drule_all non_indexed_event_args_exists >> strip_tac >>
  gvs[encode_source_event_def, encode_vyper_event_metadata_def]
QED

Theorem log_source_event_encoded:
  lookup_event_metadata tenv sources target id = SOME (h, tys, flags) /\
  EVERY supported_scalar_type tys /\
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\
                            value_has_type tv v) tys vals /\
  LENGTH flags = LENGTH tys ==>
  ?topics avs.
    encode_indexed_event_topics flags tys vals = SOME topics /\
    vyper_to_abi_list tenv (log_non_indexed_types flags tys)
      (log_non_indexed_values flags vals) = SOME avs /\
    encode_source_event tenv sources target id vals =
      SOME <| logger := target; topics := n2w h :: topics;
              data := enc (Tuple (vyper_to_abi_types tenv
                                  (log_non_indexed_types flags tys)))
                          (ListV avs) |>
Proof
  metis_tac[log_event_source_encoded]
QED

Theorem log_eval_bind:
  eval_stmt cx (Log id args) =
    bind (eval_exprs cx args)
      (\vs. bind (lift_option (encode_source_event (get_tenv cx) cx.sources
                                 cx.txn.target id vs) "Log encode event")
        (\event. ignore_bind (check_not_static cx) (push_log event)))
Proof
  simp[Once evaluate_def]
QED

Theorem log_eval_static:
  cx.txn.is_static /\ eval_exprs cx args es = (INL vals, mid) /\
  encode_source_event (get_tenv cx) cx.sources cx.txn.target id vals = SOME ev ==>
  eval_stmt cx (Log id args) es =
    (INR (Error (RuntimeError "write in static context")), mid)
Proof
  simp[log_eval_bind, bind_def, ignore_bind_def, lift_option_def, return_def]
QED

(* Keep the encoding-error branch explicit: readiness only types successes.
   Outside a static frame; a static frame rejects the log write. *)
Theorem log_eval_outcome:
  ~cx.txn.is_static ==>
  (eval_stmt cx (Log id args) es = (res, es') <=>
  (?err. eval_exprs cx args es = (INR err, es') /\ res = INR err) \/
  (?vals mid. eval_exprs cx args es = (INL vals, mid) /\
    ((encode_source_event (get_tenv cx) cx.sources cx.txn.target id vals = NONE /\
      res = INR (Error (RuntimeError "Log encode event")) /\ es' = mid) \/
     (?event. encode_source_event (get_tenv cx) cx.sources cx.txn.target id vals =
                SOME event /\ res = INL () /\
              es' = mid with logs := mid.logs ++ [event]))))
Proof
  strip_tac >>
  Cases_on `eval_exprs cx args es` >>
  rename1 `eval_exprs cx args es = (result, mid)` >>
  Cases_on `result`
  >- (rename1 `eval_exprs cx args es = (INL vals, mid)` >>
      Cases_on `encode_source_event (get_tenv cx) cx.sources cx.txn.target id vals` >>
      gs[Once evaluate_def, bind_def, ignore_bind_def, lift_option_def,
         push_log_def, return_def, raise_def] >> metis_tac[]) >>
  gs[Once evaluate_def, bind_def, lift_option_def, push_log_def,
     return_def, raise_def] >> metis_tac[]
QED

Theorem log_argument_error_ok:
  eval_exprs cx args es = (INR err, es') /\
  stmt_res_ok lctx (INR err) ==>
  expr_res_ok (INR err)
Proof
  strip_tac >> drule (cj 2 eval_expr_no_control) >>
  Cases_on `err` >>
  gvs[no_control_exc_def, stmt_res_ok_def, expr_res_ok_def]
QED

Theorem log_non_indexed_lengths:
  !flags tys vals.
    LENGTH flags = LENGTH tys /\ LENGTH flags = LENGTH vals ==>
    LENGTH (log_non_indexed_types flags tys) = LENGTH (FILTER ($~) flags) /\
    LENGTH (log_non_indexed_values flags vals) = LENGTH (FILTER ($~) flags)
Proof
  Induct_on `flags`
  >- (Cases_on `tys` >> Cases_on `vals` >>
      simp[compileEnvTheory.log_non_indexed_types_def,
           loweringStateRelDefsTheory.log_non_indexed_values_def]) >>
  rpt gen_tac >> Cases_on `tys` >> Cases_on `vals` >> simp[] >>
  Cases_on `h` >>
  simp[compileEnvTheory.log_non_indexed_types_def,
       loweringStateRelDefsTheory.log_non_indexed_values_def] >>
  metis_tac[]
QED
