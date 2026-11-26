(* Identify the word produced by the reached, forced Extract32 offset. *)
Theory bodyExtractOffsetWordMods
Ancestors
  bodyFullPostsMods bodyWriteSubscriptSourceMods bodyPtrDefs exprBodyPreProps
  exprWordOperand exprSimWordArgs loweringPosts loweringShapeDefs compileEnv
  valueEncoding vyperTypeExprSoundness vyperTypeEvalCaseProofs
  vyperTypeInvariants vyperTypeSystem vyperValue finite_map words integer_word
  arithmetic vyperTyping exprSimSource loweringSlice vyperState vyperInterpreter

Theorem extract32_offset_word_mods:
  expr_body_pre_mods mods cenv cx env off (mid with gas_obs := obs) /\
  body_const_cells_agree_mods mods cx env (mid with gas_obs := obs) /\
  bind (eval_expr cx off) (read_result cx) (mid with gas_obs := obs) = (INL w,ee) /\
  expr_type off = BaseT (UintT k) /\
  expr_post_mods H ctx func cenv cx off mid sn sq u ee w offop t /\
  ptr_val_ok cx (post_value_type cenv off) w offop G3 tn3 t /\
  lower_value compile_expr cenv ty off sn = (offop,sq) ==>
  ?i. w = IntV i /\ 0 <= i /\ Num i < dimword (:256) /\
      eval_operand offop t = SOME (n2w (Num i)) /\
      op_prov G3 offop = NONE /\ op_taint tn3 offop = {} /\
      (!z. offop = Var z ==> not_fresh_at sq z) /\ (!l. offop <> Label l)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  `?i. w = IntV i /\ 0 <= i /\ Num i < 2 ** k /\
       0 < k /\ k <= 256 /\ k MOD 8 = 0` by
    (qpat_x_assum `value_runtime_typed _ _ _` mp_tac >>
     Cases_on `w` >> simp[value_runtime_typed_def, evaluate_type_def, value_has_type_def]) >>
  `is_word_type (expr_type off)` by simp[is_word_type_def] >>
  `op_prov G3 offop = NONE /\ op_taint tn3 offop = {}` by
    fs[ptr_val_ok_def] >>
  `(!z. offop = Var z ==> not_fresh_at sq z) /\ (!l. offop <> Label l)` by
    (drule_then assume_tac expr_body_pre_mods_well_typed >>
     drule_then assume_tac expr_body_pre_mods_inv >>
     drule_then assume_tac expr_sim_inv_mods_env >>
     drule_then assume_tac env_consistent_type_defs_get_tenv >>
     `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
       (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
        simp[well_formed_type_def]) >>
     drule_all lower_value_word_shape >> simp[]) >>
  qexists_tac `i` >> simp[] >> conj_tac
  >- (rewrite_tac[dimword_def] >>
      irule LESS_LESS_EQ_TRANS >> qexists_tac `2 ** k` >> simp[EXP_BASE_LE_MONO]) >>
  `~(i < 0)` by intLib.ARITH_TAC >>
  qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule expr_post_word_operand >>
  simp[evaluate_type_def, word_value_def, val_to_w256_def, i2w_def]
QED
