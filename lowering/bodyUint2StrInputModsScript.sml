(* Linked typing and allocation facts for the Uint2Str operand and result. *)
Theory bodyUint2StrInputMods
Ancestors
  exprBodyPreProps exprSimHypsDefs exprSimUint2Str exprLowering loweringPosts
  compileEnv allocLimits supportedExprTraverse constSubstCorrect valueEncoding words
  vyperAST vyperTypeSystem vyperTypeCallGraph vyperValue vfmConstants

Theorem uint2str_input_mods:
  expr_body_pre_mods mods ce cx env (Builtin ann (Uint2Str n) args) es ==>
  ?e k. args = [e] /\ ann = BaseT (StringT n) /\ expr_type e = BaseT (UintT k) /\
        expr_body_pre_mods mods ce cx env e es /\
        LENGTH (num_to_dec_string (2 ** k - 1)) <= n
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >>
  disch_then (strip_assume_tac o MATCH_MP uint2str_expr_types) >> gvs[] >>
  qpat_x_assum `expr_body_pre_mods _ _ _ _ (Builtin _ (Uint2Str _) [_]) _` mp_tac >>
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       byte_widths_expr_def, alloc_limits_expr_def, int_calls_expr_def,
       expr_has_evm_run_thm, supported_expr_exists_def, DISJ_IMP_THM,
       FORALL_AND_THM, frame_well_typed_exprs_cons]
QED

Theorem uint2str_capacity_mods:
  expr_body_pre_mods mods ce cx env (Builtin (BaseT (StringT n)) (Uint2Str n) [e]) es /\
  X < dimword (:256) /\ LENGTH (num_to_dec_string X) <= n ==>
  ~is_word_type (expr_type (Builtin (BaseT (StringT n)) (Uint2Str n) [e])) /\
  evaluate_type (get_tenv cx)
    (expr_type (Builtin (BaseT (StringT n)) (Uint2Str n) [e])) = SOME (BaseTV (StringT n)) /\
  type_memory_bytes ce (lowered_value_type ce (Builtin (BaseT (StringT n)) (Uint2Str n) [e])) =
    type_memory_size (BaseTV (StringT n)) /\
  type_memory_size (BaseTV (StringT n)) = type_memory_bytes ce (BaseT (StringT n)) /\
  32 <= type_memory_bytes ce (BaseT (StringT n)) /\
  type_memory_bytes ce (BaseT (StringT n)) + n < dimword (:256) /\
  val_wf (BaseTV (StringT n)) (StringV (num_to_dec_string X)) /\
  LENGTH (num_to_dec_string X) + 32 <= type_memory_size (BaseTV (StringT n)) /\
  val_footprint (BaseTV (StringT n)) (StringV (num_to_dec_string X)) <=
    type_memory_bytes ce (BaseT (StringT n))
Proof
  strip_tac >> drule_all_then strip_assume_tac uint2str_result_memory_bounds >>
  `type_memory_bytes ce (BaseT (StringT n)) < 2 ** 64` by
    (qpat_x_assum `expr_body_pre_mods _ _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_mods_def, alloc_limits_expr_def, type_alloc_ok_def,
          is_word_type_def]) >>
  simp[expr_type_def, is_word_type_def, evaluate_type_def, type_slot_size_def,
       lowered_value_type_def, type_memory_size_def, type_memory_bytes_def] >>
  gvs[type_memory_bytes_def, word_size_def, dimword_def]
QED
