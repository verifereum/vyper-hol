(* Linked entry inputs for the ABI type builtins. *)
Theory bodyTypeBuiltinAbiMods
Ancestors
  bodyFullPredsMods exprBodyPreProps exprSimHypsDefs exprSimSource exprSimAbiDecodeEntryTyping
  supportedExprTraverse supportedProgram allocLimits vyperTypeBuiltins
  vyperTypeSystem vyperTypeCallGraph vyperContext vyperState vyperAST list

Theorem type_builtin_body_arg_pre_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann tb ty args) es /\
  MEM e args /\ expr_sim_inv_mods mods ce cx env es' ==>
  expr_body_pre_mods mods ce cx env e es'
Proof
  rw[expr_body_pre_mods_def, Once well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def, supported_expr_exists_def,
     supported_exprs_exists_every, EXISTS_MEM] >>
  gvs[expr_has_evm_run_thm, EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem,
            int_calls_exprs_every_mem]
QED

Theorem type_builtin_args_full_ok_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann tb ty args) es /\
  (!st x t. type_check (type_builtin_args_length_ok tb (LENGTH args))
      "TypeBuiltin args" st = (INL x,t) ==>
    body_exprs_full_ok_mods mods exps cx args) ==>
  body_exprs_full_ok_mods mods exps cx args
Proof
  strip_tac >>
  drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def] >>
  strip_tac >> drule well_typed_type_builtin_args_length >> simp[] >>
  strip_tac >> first_x_assum irule >> simp[type_check_def, assert_def, return_def]
QED

Theorem abi_decode_entry_inputs_mods:
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann (AbiDecode unwrap) ty args) es ==>
  ann = ty /\ EXISTS (occurs_abi_decode_target ty o SND) mods /\
  ?e n. args = [e] /\ expr_type e = BaseT (BytesT (Dynamic n)) /\
        expr_body_pre_mods mods ce cx env e es
Proof
  strip_tac >>
  drule_then (mp_tac o MATCH_MP abi_decode_parent_type) expr_body_pre_mods_well_typed >>
  strip_tac >> gvs[] >>
  conj_tac
  >- (qpat_assum `expr_body_pre_mods _ _ _ _ (TypeBuiltin _ _ _ _) _`
        (mp_tac o REWRITE_RULE [expr_body_pre_mods_def]) >>
      simp[supported_expr_exists_def, expr_abi_decode_target_root_def]) >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule type_builtin_body_arg_pre_mods >> simp[]
QED
