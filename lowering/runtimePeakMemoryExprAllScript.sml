(* The bounded expression callbacks either recurse at a smaller measure
   or emit INVALID. The window includes all three allocation chunk forms. *)
Theory runtimePeakMemoryExprAll
Ancestors
  runtimePeakMemoryExprDispatch runtimePeakMemoryExpr
  runtimePeakMemoryBuiltins runtimePeakMemoryAbi runtimePeakMemoryCode
  exprValueWrapperStateProps exprLowering exprCallBounds exprCallbackContracts
  builtinSimple compileEnv context emitHelper venomInst list pair arithmetic

Theorem dalloca_windows_builtin_dispatch_body_all[local]:
  (!ce ty e. preserves_dalloca_windows window (cfn ce ty e)) ==>
  preserves_dalloca_windows window (compile_builtin_dispatch_body cfn ce rt ty bi args)
Proof
  strip_tac >>
  `!env et e. preserves_dalloca_windows window (lower_value cfn env et e)` by
    (rpt gen_tac >> irule dalloca_windows_lower_value >> simp[]) >>
  `!env es. preserves_dalloca_windows window (compile_multi_exprs cfn env es)` by
    (rpt gen_tac >> irule dalloca_windows_multi_exprs >> simp[]) >>
  `(!es dst infos off.
      preserves_dalloca_windows window (compile_concat cfn ce es dst infos off)) /\
   (!es tys dst off.
      preserves_dalloca_windows window (compile_make_tuple cfn ce es tys dst off)) /\
   (!es et sz lw dst.
      preserves_dalloca_windows window (compile_make_array cfn ce es et sz lw dst))` by
    (conj_tac >- (rpt gen_tac >> irule dalloca_windows_concat >> simp[]) >>
     conj_tac >- (rpt gen_tac >> irule dalloca_windows_make_tuple >> simp[]) >>
     rpt gen_tac >> irule dalloca_windows_make_array >> simp[]) >>
  RULE_ASSUM_TAC (REWRITE_RULE [dalloca_windows_result_state]) >>
  Cases_on `bi` >>
  simp[compile_builtin_dispatch_body_def, dalloca_windows_result_state,
       LET_THM, pairTheory.UNCURRY, dalloca_windows_state_wrappers] >>
  rpt strip_tac >>
  (* Resolve the dispatch branches before chaining the state rules. *)
  simp (map (SIMP_RULE (srw_ss()) [dalloca_windows_result_state])
    [dalloca_windows_base_operations, dalloca_windows_emit_helpers,
     dalloca_windows_alloc_buffer, dalloca_windows_unwrap_value,
     dalloca_windows_acc, dalloca_windows_ptr_access] @ [compile_builtin_len_def]) >>
  (let
     val reduce = simp[dalloca_windows_state_wrappers, pairTheory.UNCURRY, LET_THM]
     val split_if =
       rename1 `compiler_dalloca_windows _ (SND (if guard then _ else _))` >>
       Cases_on `guard`
   in
     rpt ((split_if ORELSE BasicProvers.TOP_CASE_TAC) >> reduce)
   end) >>
  (let
     val state_rule = SIMP_RULE (srw_ss()) [dalloca_windows_result_state]
     val operations =
       [dalloca_windows_base_operations, dalloca_windows_hash_ops,
        dalloca_windows_bytes_ops, dalloca_windows_simple_values,
        dalloca_windows_alloc_buffer, dalloca_windows_unwrap_value,
        dalloca_windows_ptr_access, dalloca_windows_array_membership,
        dalloca_windows_list_membership, dalloca_windows_binop]
     val emit_rules = map DISCH_ALL (CONJUNCTS (UNDISCH dalloca_windows_emit_helpers))
     val state_step = FIRST (first_assum irule ::
       map (irule o state_rule)
         (dalloca_windows_acc :: emit_rules @ List.concat (map CONJUNCTS operations)))
   in
     rpt (state_step >> simp[])
   end)
QED

Theorem dalloca_windows_type_builtin_dispatch_body_all[local]:
  (!ce ty e. preserves_dalloca_windows window (cfn ce ty e)) ==>
  preserves_dalloca_windows window (compile_type_builtin_dispatch_body cfn ce vt ty tb rt args)
Proof
  strip_tac >>
  `preserves_dalloca_windows window (compile_abi_encode_args cfn ce args)` by
    (irule dalloca_windows_abi_encode_args >> simp[]) >>
  Cases_on `tb` >>
  simp[dalloca_windows_result_state, compile_type_builtin_dispatch_body_def,
       dalloca_windows_state_wrappers, LET_THM, pairTheory.UNCURRY] >>
  RULE_ASSUM_TAC (REWRITE_RULE [dalloca_windows_result_state]) >>
  rpt strip_tac >>
  rpt (COND_CASES_TAC >> simp[dalloca_windows_state_wrappers]) >>
  TRY (BasicProvers.TOP_CASE_TAC >> simp[dalloca_windows_state_wrappers]) >>
  rpt (FIRST (map (irule o REWRITE_RULE [dalloca_windows_result_state])
    ([dalloca_windows_convert, dalloca_windows_bytestring_widen_copy,
      dalloca_windows_lower_abi_encode, dalloca_windows_abi_encode_payload,
      dalloca_windows_lower_abi_decode, dalloca_windows_clamp_basetype,
      dalloca_windows_lower_value, dalloca_windows_unwrap_value] @
     CONJUNCTS dalloca_windows_base_operations @
     CONJUNCTS dalloca_windows_bytes_ops)) ORELSE
    gen_tac ORELSE disch_tac ORELSE conj_tac ORELSE
    first_assum ACCEPT_TAC ORELSE first_assum irule)
QED

Theorem dalloca_windows_expr_body_all[local]:
  (!ce ty e. preserves_dalloca_windows window (cfn ce ty e)) /\
  (!ann bi args. e = Builtin ann bi args ==>
    preserves_dalloca_windows window (bfn ce ann ty bi args)) /\
  (!ann tb rt args. e = TypeBuiltin ann tb rt args ==>
    preserves_dalloca_windows window (tfn ce ann ty tb rt args)) /\
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
  preserves_dalloca_windows window (compile_expr_body cfn bfn tfn ce ty e)
Proof
  Cases_on `e` >> simp[] >> strip_tac >>
  all_tac >~ [`compile_expr_body _ _ _ _ _ (Call ann target args d)`] >-
    (`compile_expr_body cfn bfn tfn ce ty (Call ann target args d) =
       compile_call cfn ce ann ty target args d` by
       simp[FUN_EQ_THM, compile_expr_body_def, vyperASTTheory.expr_type_def] >>
     pop_assum SUBST1_TAC >> irule dalloca_windows_compile_call >> simp[]) >>
  all_tac >~ [`compile_expr_body _ _ _ _ _ (Builtin ann bi args)`] >-
    (Cases_on `names_builtin bi args` >-
       (qpat_x_assum `preserves_dalloca_windows window (bfn _ _ _ _ _)` kall_tac >>
        qpat_x_assum `names_builtin bi args` mp_tac >>
        map_every qid_spec_tac [`args`, `bi`] >>
        recInduct exprSimHypsDefsTheory.names_builtin_ind >>
        simp[exprSimHypsDefsTheory.names_builtin_def, compile_expr_body_def,
             vyperASTTheory.expr_type_def,
             SIMP_RULE (srw_ss()) [dalloca_windows_result_state]
               dalloca_windows_modular_names, dalloca_windows_result_state]) >>
     RULE_ASSUM_TAC (REWRITE_RULE [dalloca_windows_result_state]) >>
     simp[exprSimHypsDefsTheory.compile_expr_body_builtin_dispatch,
          dalloca_windows_result_state]) >>
  RULE_ASSUM_TAC (REWRITE_RULE [dalloca_windows_result_state]) >>
  simp[dalloca_windows_result_state, compile_expr_body_def, vyperASTTheory.expr_type_def,
       LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >>
  all_tac >~ [`compile_dynarray_pop _ _ _ _ _ _ _`] >-
    (FIRST (map (irule o SIMP_RULE (srw_ss()) [dalloca_windows_result_state])
       (CONJUNCTS dalloca_windows_indexing)) >>
     irule (SIMP_RULE (srw_ss()) [dalloca_windows_result_state]
              dalloca_windows_get_target_ptr) >> simp[]) >>
  all_tac >~ [`compile_struct_lit _ _ _ _ _ _ _`] >-
    (irule (SIMP_RULE (srw_ss()) [dalloca_windows_result_state]
       dalloca_windows_compile_struct_lit) >>
     simp[SIMP_RULE (srw_ss()) [dalloca_windows_result_state]
            dalloca_windows_alloc_buffer]) >>
  all_tac >~ [`compile_subscript _ _ _ _ _ _ _`] >-
    (irule (SIMP_RULE (srw_ss()) [dalloca_windows_result_state]
       dalloca_windows_compile_subscript) >> simp[]) >>
  all_tac >~ [`compile_attribute _ _ _ _ _ _ _`] >-
    (irule (SIMP_RULE (srw_ss()) [dalloca_windows_result_state]
       dalloca_windows_compile_attribute) >> simp[]) >>
  all_tac >~ [`FLOOKUP ce.ce_module_vars nsid`] >-
    (Cases_on `FLOOKUP ce.ce_module_vars nsid` >> simp[] >>
     TRY (Cases_on `x` >> simp[]) >>
     simp[SIMP_RULE (srw_ss()) [dalloca_windows_result_state]
            dalloca_windows_emit_helpers]) >>
  simp[SIMP_RULE (srw_ss()) [dalloca_windows_result_state]
         dalloca_windows_simple_values] >>
  COND_CASES_TAC >> simp[] >>
  rpt (FIRST (first_assum irule ::
    map (irule o SIMP_RULE (srw_ss()) [dalloca_windows_result_state])
      (map DISCH_ALL (CONJUNCTS (UNDISCH dalloca_windows_emit_helpers)) @
       CONJUNCTS dalloca_windows_fresh @ CONJUNCTS dalloca_windows_simple_values @
       [dalloca_windows_lower_value, dalloca_windows_new_block]) @
    [conj_tac, CHANGED_TAC (simp[])]))
QED

Theorem dalloca_windows_compile_expr_all_mutual:
  (!chunk. raw_call_dalloca_chunk chunk 1 ==> window chunk 1) /\
  (!chunk. create_copy_dalloca_chunk chunk 5 ==> window chunk 5) /\
  (!chunk. create_blueprint_dalloca_chunk chunk 1 ==> window chunk 1) ==>
  ((!ce ty e st. compiler_dalloca_windows window st ==>
     compiler_dalloca_windows window (SND (compile_expr ce ty e st))) /\
   (!ce rt ty bi args st. compiler_dalloca_windows window st ==>
     compiler_dalloca_windows window (SND (compile_builtin_dispatch ce rt ty bi args st))) /\
   (!ce vt ty tb rt args st. compiler_dalloca_windows window st ==>
     compiler_dalloca_windows window
       (SND (compile_type_builtin_dispatch ce vt ty tb rt args st))))
Proof
  strip_tac >> ho_match_mp_tac compile_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC [compile_expr_raw_def] >>
  PURE_REWRITE_TAC [COND_CLAUSES] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  FIRST (map (irule o REWRITE_RULE [dalloca_windows_result_state])
    [dalloca_windows_expr_body_all, dalloca_windows_builtin_dispatch_body_all,
     dalloca_windows_type_builtin_dispatch_body_all]) >>
  asm_simp_tac bool_ss [] >>
  rpt conj_tac >> rpt strip_tac >>
  PURE_REWRITE_TAC [expr_child_callback_def, builtin_child_callback_def,
                    type_child_callback_def] >>
  COND_CASES_TAC >>
  (irule (REWRITE_RULE [dalloca_windows_result_state]
     dalloca_windows_invalid_expr_call) ORELSE first_assum irule) >>
  asm_simp_tac bool_ss []
QED
