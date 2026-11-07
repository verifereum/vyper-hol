(* Source typing at the reason-to-encoder boundary. *)
Theory reasonTypingProps
Ancestors
  exprSimSource exprSimHyps exprSimHypsDefs loweringPosts
  valueEncodingTyping vyperTypeExprResult vyperTypeExprSoundness
  vyperTypeInvariants vyperTyping vyperValue vyperState allocLimits
  reasonEndpointResourcesPtr reasonRepresentationPtr vyperInterpreter
  vyperValueOperation valueEncoding exprLoweringProps stringUnwrapLayout
  words vfmConstants exprLowering compileEnv
Libs
  monadsyntax

Theorem evaluate_type_string_result:
  evaluate_type tenv ty = SOME (BaseTV (StringT max)) ==>
  ty = BaseT (StringT max)
Proof
  Cases_on `ty` >> simp[Once evaluate_type_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem reason_string_source_typing:
  expr_body_pre cenv cx env r es /\
  eval_expr cx r es = (INL tv,ee) /\
  read_result cx tv ee = (INL (StringV str),ee) ==>
  ?max. expr_type r = BaseT (StringT max) /\
    evaluate_type (get_tenv cx) (BaseT (StringT max)) = SOME (BaseTV (StringT max)) /\
    type_alloc_ok cenv (BaseT (StringT max)) /\
    val_wf (BaseTV (StringT max)) (StringV str) /\ LENGTH str <= max
Proof
  strip_tac >>
  `vyperState$bind (eval_expr cx r) (read_result cx) es = (INL (StringV str),ee)` by
    simp[bind_def] >>
  drule exprSimSourceTheory.expr_body_pre_eval >>
  simp[bind_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `?max. evaluate_type (get_tenv cx) (expr_type r) = SOME (BaseTV (StringT max)) /\
     value_has_type (BaseTV (StringT max)) (StringV str)` by
    (fs[expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def,
        value_has_type_inv] >> metis_tac[value_has_type_def]) >>
  drule evaluate_type_string_result >> strip_tac >>
  `type_alloc_ok cenv (expr_type r)` by
    (irule alloc_limits_expr_type_alloc_ok >> fs[expr_body_pre_def]) >>
  drule (cj 1 value_has_type_val_wf) >> strip_tac >>
  qexists `max` >> gvs[value_has_type_def]
QED

Theorem literal_reason_source_resources:
  expr_body_pre cenv cx env (Literal (BaseT (StringT max)) (StringL str)) es ==>
  LENGTH str <= max /\
  type_alloc_ok cenv (BaseT (StringT max)) /\
  32+32*word_size max < dimword(:256) /\
  32+contractABI$ceil32 (LENGTH str) <= type_memory_bytes cenv (BaseT (StringT max)) /\
  LENGTH str+63 < dimword(:256) /\
  64+type_memory_bytes cenv (BaseT (StringT max)) < dimword(:256)
Proof
  strip_tac >>
  `eval_expr cx (Literal (BaseT (StringT max)) (StringL str)) es =
      (INL (Value (StringV str)),es)` by
    simp[Once evaluate_def, evaluate_literal_def, return_def] >>
  `read_result cx (Value (StringV str)) es = (INL (StringV str),es)` by
    simp[read_result_def, return_def] >>
  drule_all reason_string_source_typing >> strip_tac >>
  fs[vyperASTTheory.expr_type_def] >> gvs[] >>
  drule_all reasonEndpointResourcesPtrTheory.string_encoder_size_bounds >> strip_tac >>
  fs[val_wf_def, type_alloc_ok_def, is_word_type_def,
     string_memory_bytes_slots,
     type_slot_size_def, word_size_def, dimword_def] >> decide_tac
QED
