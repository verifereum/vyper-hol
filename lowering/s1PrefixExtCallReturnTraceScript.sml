(* Decoding the returned bytes adds no source request. *)
Theory s1PrefixExtCallReturnTrace
Ancestors
  s1PrefixOfVV bodyFullExtCallReturnSource exprSimExtCallCase vyperState list

Theorem snd_bind_neutral[local]:
  (!v st. SND (next v st) = st) ==>
  !st. SND (bind source next st) = SND (source st)
Proof
  strip_tac >> gen_tac >> Cases_on `source st` >>
  rename1 `source st = (res,mid)` >> Cases_on `res` >>
  simpLib.ASM_SIMP_TAC bool_ss [bind_def, pairTheory.SND, pairTheory.pair_case_def,
                              sumTheory.sum_case_def]
QED

Theorem extcall_return_trace_prefix:
  LENGTH rest = LENGTH arg_types + LENGTH opts /\
  ext_call_opts_ok stat opts /\
  dest_AddressV target_v = SOME target /\
  value_opt = (if stat then NONE else
    case ext_call_kwarg EKValue opts (DROP (LENGTH arg_types) rest) of
      NONE => SOME 0 | SOME v => dest_NumV v) /\
  (stat <=> value_opt = NONE) /\
  build_ext_calldata (get_tenv cx) fname arg_types (TAKE (LENGTH arg_types) rest) =
    SOME calldata /\
  gas_prefix_full P cx st0
    (do accounts <- get_accounts;
        check (ext_call_precheck_ok skip ret_type target accounts)
          "ExtCall target has no code";
        framed <- frame_call_value cx value_opt;
        eval_ext_call_effects cx target calldata framed
          (ext_call_kwarg EKGas opts (DROP (LENGTH arg_types) rest)) accounts
     od) (ee,s,G,tn) ==>
  gas_prefix_full P cx st0
    (eval_ext_call cx stat skip (fname,arg_types,ret_type) opts (target_v::rest))
    (ee,s,G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (pure_rewrite_tac o single) eval_ext_call_request >>
  qmatch_goalsub_abbrev_tac `gas_prefix_full P cx st0 src` >>
  qmatch_asmsub_abbrev_tac `gas_prefix_full P cx st0 prefix` >>
  `!qe. SND (src qe) = SND (prefix qe)` suffices_by
    (disch_then (fn th => simp[MATCH_MP gas_prefix_full_state_cong th])) >>
  `src = bind prefix (\data.
     case (if data = [] then ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest)
           else NONE) of
       SOME v => do accounts' <- get_accounts;
                    check (skip \/ ext_call_has_code target accounts')
                      "ExtCall target has no code";
                    return (Value v) od
     | NONE => do val <- lift_sum_runtime
                    (evaluate_abi_decode_return (get_tenv cx) ret_type data);
                  return (Value val) od)` by
    simp[NoAsms, Abbr `src`, Abbr `prefix`, ignore_bind_def, bind_assoc] >>
  pop_assum (pure_rewrite_tac o single) >>
  irule snd_bind_neutral >> rpt gen_tac >>
  qspecl_then [`cx`,`ret_type`,`v`,
               `ext_call_kwarg EKDefault opts (DROP (LENGTH arg_types) rest)`,
               `skip`,`target`,`st`] strip_assume_tac extcall_return_source_tail >>
  first_x_assum (qspec_then `st.gas_obs` mp_tac) >>
  simp[NoAsms] >> disch_then (mp_tac o AP_TERM ``SND``) >> simp[NoAsms]
QED
