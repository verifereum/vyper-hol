Theory bodyECArithHeadSourceMods
Ancestors
  bodyFullBuiltinECArithSourceMatch
  exprSimECArith exprSimWordArgs vyperInterpreter vyperContext

(* Classify the source tail after the staged request has been matched.  The
   option distinguishes an invalid point from a valid point whose oracle head
   may fail. *)
Theorem ec_arith_head_source_mods:
  (bt = ECAdd \/ bt = ECMul) /\
  (if bt = ECAdd then evaluate_ecadd [v1;v2] else evaluate_ecmul [v1;v2]) =
    (case point_result of NONE => INR (RuntimeError
       (if bt = ECAdd then "ECAdd invalid point" else "ECMul invalid point"))
     | SOME xy => INL (mk_ec_result xy)) /\
  precompile_result (precompile_address bt) (precompile_input bt [v1;v2]) =
    SOME (OPTION_MAP (\(rx,ry). word_to_bytes (n2w rx:bytes32) T ++
      word_to_bytes (n2w ry:bytes32) T) point_result) /\
  es.outcomes = SOME u.vs_outcomes /\
  u.vs_outcomes <> [] ==>
  case point_result of NONE =>
    ec_source_tail cx a bt tys [v1;v2] es =
      (INR (Error (RuntimeError
         (if bt = ECAdd then "ECAdd invalid point" else "ECMul invalid point"))),es)
  | SOME xy =>
    ec_source_tail cx a bt tys [v1;v2] es =
      (if (HD u.vs_outcomes).co_success then INL (Value (mk_ec_result xy))
       else INR (Error (RuntimeError "precompile failed")),
       SND (take_call_outcome NONE (precompile_address bt) (precompile_input bt [v1;v2]) NONE es))
Proof
  strip_tac >> Cases_on `point_result` >> Cases_on `u.vs_outcomes` >>
  gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def]
QED
