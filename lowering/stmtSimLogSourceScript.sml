Theory stmtSimLogSource
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
   supportedTypes e2eDefs vyperTyping vyperValue vyperABI
  vyperEventArgCompat vyperEvent valueEncoding vyperInterpreter vyperState vyperExprNoControl
  vyperTypeABI vyperEventCompatibility vyperTypeContract

(* Source-only scalar conversion boundary. No compiler execution is unfolded. *)
Theorem log_scalar_abi_exists:
  supported_scalar_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v ==>
  ?av. vyper_to_abi tenv ty v = SOME av
Proof
  Cases_on `ty` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def,
       evaluate_type_def] >>
  rpt strip_tac >> Cases_on `v` >>
  gvs[value_has_type_def, vyper_to_abi_base_def] >>
  Cases_on `b` >> gvs[value_has_type_def]
QED

Theorem log_word_topic:
  supported_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v ==>
  encode_event_topic ty v = SOME (typed_val_to_w256 tv v)
Proof
  Cases_on `ty` >> simp[supported_word_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, evaluate_type_def] >>
  rpt strip_tac >> Cases_on `v` >>
  gvs[value_has_type_def, encode_event_topic_def, event_value_to_word_def,
      is_event_bytestring_type_def, event_topic_word_def,
      typed_val_to_w256_def, val_to_w256_def] >>
  Cases_on `b` >> gvs[value_has_type_def, typed_val_to_w256_def,
                         val_to_w256_def, supported_word_type_def] >>
  simp[is_event_bytestring_type_def, event_topic_word_def]
QED

Theorem log_scalar_topic_exists:
  supported_scalar_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v ==>
  ?topic. encode_event_topic ty v = SOME topic
Proof
  Cases_on `ty` >>
  simp[supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def,
       evaluate_type_def] >>
  rpt strip_tac >> Cases_on `v` >>
  gvs[value_has_type_def, is_event_bytestring_type_def,
      encode_event_topic_def] >>
  Cases_on `b` >> gvs[value_has_type_def, is_event_bytestring_type_def,
                          encode_event_topic_def]
QED

Theorem log_scalar_topics_exist:
  !tys flags vals.
    EVERY supported_scalar_type tys /\
    LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\
                              value_has_type tv v) tys vals /\
    LENGTH flags = LENGTH tys ==>
    ?topics. encode_indexed_event_topics flags tys vals = SOME topics
Proof
  Induct_on `tys`
  >- (Cases_on `flags` >> Cases_on `vals` >>
      simp[encode_indexed_event_topics_def]) >>
  rpt gen_tac >> Cases_on `flags` >> Cases_on `vals` >>
  simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `encode_indexed_event_topics fs tys vs = SOME topics` >>
  rename1 `encode_indexed_event_topics (flg::fs) (ty::tys) (v::vs)` >>
  Cases_on `flg` >> simp[encode_indexed_event_topics_def] >>
  drule_all log_scalar_topic_exists >> strip_tac >> simp[]
QED

Theorem log_scalar_abi_list_exists:
  !tys vals.
    EVERY supported_scalar_type tys /\
    LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\
                              value_has_type tv v) tys vals ==>
    ?avs. vyper_to_abi_list tenv tys vals = SOME avs
Proof
  Induct_on `tys`
  >- (Cases_on `vals` >> simp[Once vyper_to_abi_def]) >>
  gen_tac >> Cases_on `vals` >> simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all log_scalar_abi_exists >> strip_tac >>
  simp[Once vyper_to_abi_def]
QED

Theorem log_non_indexed_scalars_typed:
  !flags tys vals.
    EVERY supported_scalar_type tys /\
    LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\
                              value_has_type tv v) tys vals /\
    LENGTH flags = LENGTH tys ==>
    EVERY supported_scalar_type (log_non_indexed_types flags tys) /\
    LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\
                              value_has_type tv v)
      (log_non_indexed_types flags tys) (log_non_indexed_values flags vals)
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
  strip_tac >>
  drule_all log_scalar_topics_exist >> strip_tac >>
  drule_all log_non_indexed_scalars_typed >> strip_tac >>
  drule_all log_scalar_abi_list_exists >> strip_tac >>
  `LENGTH flags = LENGTH vals` by metis_tac[listTheory.LIST_REL_LENGTH] >>
  drule_all non_indexed_event_args_exists >> strip_tac >>
  simp[encode_source_event_def, encode_vyper_event_metadata_def] >>
  metis_tac[]
QED

(* Aggregate data is typed; only indexed fields require scalar support. *)
Theorem log_typed_source_event_encoded:
  lookup_event_metadata tenv sources target id = SOME (h,tys,flags) /\
  LENGTH flags = LENGTH tys /\
  EVERY (\(ty,indexed). indexed ==> supported_scalar_type ty) (ZIP (tys,flags)) /\
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) tys vals ==>
  ?topics avs.
    encode_indexed_event_topics flags tys vals = SOME topics /\
    vyper_to_abi_list tenv (log_non_indexed_types flags tys)
      (log_non_indexed_values flags vals) = SOME avs /\
    encode_source_event tenv sources target id vals =
      SOME <|logger := target; topics := n2w h::topics;
        data := enc (Tuple (vyper_to_abi_types tenv (log_non_indexed_types flags tys))) (ListV avs)|>
Proof
  strip_tac >>
  `!flags tys vals.
    LENGTH flags = LENGTH tys /\
    EVERY (\(ty,indexed). indexed ==> supported_scalar_type ty) (ZIP (tys,flags)) /\
    LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) tys vals ==>
    ?topics avs.
      encode_indexed_event_topics flags tys vals = SOME topics /\
      vyper_to_abi_list tenv (log_non_indexed_types flags tys)
        (log_non_indexed_values flags vals) = SOME avs` by
    (rpt (pop_assum kall_tac) >> Induct
     >- (Cases_on `tys` >> Cases_on `vals` >>
         simp[encode_indexed_event_topics_def, compileEnvTheory.log_non_indexed_types_def,
           loweringStateRelDefsTheory.log_non_indexed_values_def, Once vyper_to_abi_def]) >>
     rpt gen_tac >> Cases_on `tys` >> Cases_on `vals` >> simp[] >>
     rename1 `encode_indexed_event_topics (flag::flags) (ty::tys) (v::vals)` >>
     Cases_on `flag` >> simp[] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     simp[encode_indexed_event_topics_def, compileEnvTheory.log_non_indexed_types_def,
       loweringStateRelDefsTheory.log_non_indexed_values_def, Once vyper_to_abi_def]
     >- (drule_all log_scalar_topic_exists >> strip_tac >> simp[]) >>
     drule_all (cj 1 vyper_to_abi_total) >> strip_tac >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  `LENGTH flags = LENGTH vals` by metis_tac[listTheory.LIST_REL_LENGTH] >>
  drule_all non_indexed_event_args_exists >> strip_tac >>
  simp[encode_source_event_def, encode_vyper_event_metadata_def] >> metis_tac[]
QED

(* Indexed hashing does not evaluate the declared capacity. *)
Theorem log_compatible_source_event_encoded:
  lookup_event_metadata tenv sources target id = SOME (h,dtys,flags) /\
  LENGTH flags = LENGTH dtys /\
  LIST_REL event_arg_compatible dtys ltys /\
  EVERY (\(ty,indexed). indexed ==> supported_scalar_type ty) (ZIP (dtys,flags)) /\
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) ltys vals /\
  LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
    (log_non_indexed_types flags dtys) (log_non_indexed_values flags vals) ==>
  ?topics avs.
    encode_indexed_event_topics flags ltys vals = SOME topics /\
    vyper_to_abi_list tenv (log_non_indexed_types flags dtys)
      (log_non_indexed_values flags vals) = SOME avs /\
    encode_source_event tenv sources target id vals =
      SOME <|logger := target; topics := n2w h::topics;
        data := enc (Tuple (vyper_to_abi_types tenv (log_non_indexed_types flags dtys))) (ListV avs)|>
Proof
  strip_tac >>
  `!flags dtys ltys vals.
    LENGTH flags = LENGTH dtys /\ LIST_REL event_arg_compatible dtys ltys /\
    EVERY (\(ty,indexed). indexed ==> supported_scalar_type ty) (ZIP (dtys,flags)) /\
    LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v) ltys vals /\
    LIST_REL (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
      (log_non_indexed_types flags dtys) (log_non_indexed_values flags vals) ==>
    ?topics avs.
      encode_indexed_event_topics flags ltys vals = SOME topics /\
      encode_indexed_event_topics flags dtys vals = SOME topics /\
      vyper_to_abi_list tenv (log_non_indexed_types flags dtys)
        (log_non_indexed_values flags vals) = SOME avs` by
    (rpt (pop_assum kall_tac) >> Induct
     >- (Cases_on `dtys` >> Cases_on `ltys` >> Cases_on `vals` >>
         simp[encode_indexed_event_topics_def, compileEnvTheory.log_non_indexed_types_def,
           loweringStateRelDefsTheory.log_non_indexed_values_def, Once vyper_to_abi_def]) >>
     rpt gen_tac >> Cases_on `dtys` >> Cases_on `ltys` >> Cases_on `vals` >> simp[] >>
     rename1 `encode_indexed_event_topics (flag::flags) (lty::ltys) (v::vals)` >>
     rename1 `event_arg_compatible dty lty` >>
     Cases_on `flag` >>
     simp[compileEnvTheory.log_non_indexed_types_def,
       loweringStateRelDefsTheory.log_non_indexed_values_def] >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     simp[encode_indexed_event_topics_def, compileEnvTheory.log_non_indexed_types_def,
       loweringStateRelDefsTheory.log_non_indexed_values_def, Once vyper_to_abi_def]
     >- (`supported_scalar_type lty` by
           (Cases_on `dty` >> Cases_on `lty` >>
            gvs[supported_scalar_type_def, supported_word_type_def,
              supported_string_type_def, event_arg_compatible_def] >>
            rename1 `event_arg_compatible (BaseT db) (BaseT ab)` >>
            Cases_on `db` >> Cases_on `ab` >>
            gvs[supported_scalar_type_def, supported_word_type_def,
              supported_string_type_def, event_arg_compatible_def] >>
            rename1 `event_arg_compatible (BaseT (BytesT fb)) (BaseT (BytesT ab))` >>
            Cases_on `fb` >> Cases_on `ab` >>
            gvs[supported_scalar_type_def, supported_word_type_def,
              supported_string_type_def, event_arg_compatible_def]) >>
         `event_indexable_type dty` by
           (Cases_on `dty` >> gvs[supported_scalar_type_def,
             supported_word_type_def, supported_string_type_def, event_indexable_type_def]) >>
         drule_all event_arg_compatible_topic >> strip_tac >>
         drule_all log_scalar_topic_exists >> strip_tac >> simp[]) >>
     `?av. vyper_to_abi tenv dty v = SOME av` by
       metis_tac[cj 1 vyper_to_abi_total] >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  `LENGTH flags = LENGTH vals` by metis_tac[listTheory.LIST_REL_LENGTH] >>
  drule_all non_indexed_event_args_exists >> strip_tac >>
  simp[encode_source_event_def, encode_vyper_event_metadata_def] >> metis_tac[]
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

(* Event compatibility may narrow bounds, but ABI descriptors erase them. *)
Theorem event_arg_compatible_abi_types:
  (!fty aty. event_arg_compatible fty aty ==>
     vyper_to_abi_type tenv aty = vyper_to_abi_type tenv fty) /\
  (!fts ats. event_arg_compatible_list fts ats ==>
     vyper_to_abi_types tenv ats = vyper_to_abi_types tenv fts)
Proof
  ho_match_mp_tac vyperEventArgCompatTheory.event_arg_compatible_ind >>
  simp[vyperEventArgCompatTheory.event_arg_compatible_def,
       vyper_base_to_abi_type_def]
QED
