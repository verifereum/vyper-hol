(* The source and encoded result of rounding a reached decimal operand. *)
Theory bodyWordRoundReadResultMods
Ancestors
  bodyFullPostsMods bodyBranchCellFrameMods bodyWriteSubscriptSourceMods
  loweringPosts exprBopSimProps exprSimWordBuiltins exprSimUnopProps
  exprSimDefs compileEnv vyperTypeExprSoundness vyperInterpreter vyperContext
  vyperValue vyperValueOperation vyperTypeSystem vyperTyping valueEncoding
  venomState venomExecSemantics words integer_word

Theorem rounding_decimal_source[local]:
  (bt = Ceil \/ bt = Floor) /\ value_has_type (BaseTV DecimalT) v ==>
  ?v'. unop_result cx (BaseT (IntT 256)) bt tys v es = INL v' /\
    typed_val_to_w256 (BaseTV (IntT 256)) v' =
    safe_sdiv
      (if bt = Ceil then
         (if word_lt (typed_val_to_w256 (BaseTV DecimalT) v) 0w then
            typed_val_to_w256 (BaseTV DecimalT) v
          else typed_val_to_w256 (BaseTV DecimalT) v + n2w (10000000000 - 1))
       else (if word_lt (typed_val_to_w256 (BaseTV DecimalT) v) 0w then
            typed_val_to_w256 (BaseTV DecimalT) v - n2w (10000000000 - 1)
          else typed_val_to_w256 (BaseTV DecimalT) v))
      (n2w 10000000000)
Proof
  disch_then (CONJUNCTS_THEN2 DISJ_CASES_TAC assume_tac) >>
  Cases_on `v` >> gvs[value_has_type_def]
  >- (drule decimal_ceil_word >>
      simp[unop_result_def, evaluate_builtin_def, typed_val_to_w256_def,
           val_to_w256_def, decimal_scale_def, WORD_LTi, word_0_w2i])
  >> drule decimal_floor_word >>
  simp[unop_result_def, evaluate_builtin_def, typed_val_to_w256_def,
       val_to_w256_def, decimal_scale_def, WORD_LTi, word_0_w2i]
QED

Theorem word_rounding_read_result_mods:
  (bt = Ceil \/ bt = Floor) /\ expr_type e = BaseT DecimalT /\
  expr_body_pre_mods mods cenv cx env e es /\
  body_const_cells_agree_mods mods cx env es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := readings) = (INL v,mid) /\
  expr_post_mods H ctx func cenv cx e es sa s1 s0 mid v x t ==>
  eval_operand x t = SOME (typed_val_to_w256 (BaseTV DecimalT) v) /\
  ?v'. unop_result cx (BaseT (IntT 256)) bt [expr_type e] v mid = INL v' /\
    typed_val_to_w256 (BaseTV (IntT 256)) v' =
    safe_sdiv
      (if bt = Ceil then
         (if word_lt (typed_val_to_w256 (BaseTV DecimalT) v) 0w then
            typed_val_to_w256 (BaseTV DecimalT) v
          else typed_val_to_w256 (BaseTV DecimalT) v + n2w (10000000000 - 1))
       else (if word_lt (typed_val_to_w256 (BaseTV DecimalT) v) 0w then
            typed_val_to_w256 (BaseTV DecimalT) v - n2w (10000000000 - 1)
          else typed_val_to_w256 (BaseTV DecimalT) v))
      (n2w 10000000000)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_tac
  >- (`is_word_type (expr_type e)` by simp[is_word_type_def] >>
      `expr_val_rel cx (expr_type e) v x t` by
        fs[expr_post_mods_def, expr_post_def] >>
      drule expr_val_rel_typed >> disch_then irule >> simp[evaluate_type_def])
  >> `expr_body_pre_mods mods cenv cx env e (es with gas_obs := readings) /\
      body_const_cells_agree_mods mods cx env (es with gas_obs := readings)` by
    simp[body_const_cells_agree_mods_branch_updates]
  >> drule_all_then strip_assume_tac write_index_read_source_mods
  >> `value_has_type (BaseTV DecimalT) v` by
       gvs[value_runtime_typed_def, evaluate_type_def]
  >> irule rounding_decimal_source >> simp[]
QED
