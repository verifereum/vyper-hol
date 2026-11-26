(* Dispatch the selected local assignment prefix companion. *)
Theory s1PrefixBoolChainSelectedLocalAssign
Ancestors
  s1PrefixAssign exprSimAggregateLayout

Theorem bool_chain_selected_local_assign_prefix:
  !cx id ty e DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env env' ret_ty lctx RetQ es.
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_full_ok cx (NameTarget id)) /\
  (!s'' pv t' s'3' v t''.
       eval_expr cx e s'' = (INL pv,t') /\ read_result cx pv s'3' = (INL v,t'') ==>
       body_base_target_prefix_ok cx (NameTarget id)) /\
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (BaseTarget (NameTarget id)) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget (NameTarget id)) e) ==>
       occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (Assign (BaseTarget (NameTarget id)) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (NameTarget id)) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (NameTarget id)) e)) /\
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty /\
  FLOOKUP env.var_types id = SOME ty /\
  (is_word_type ty \/ expr_type e = ty \/ lowered_value_type cenv e = ty \/
   is_bytestring_type ty \/
   has_length_word (expr_type e) /\ is_empty_value_expr e) ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty
        (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `is_word_type ty`
  >- (irule body_assign_local_word_prefix >> metis_tac[]) >>
  `0 < type_memory_bytes cenv ty` by
    (drule_all assign_local_memory_bytes_pos >> simp[]) >>
  Cases_on `lowered_value_type cenv e = expr_type e \/
            is_bytestring_type (expr_type e) /\
            is_bytestring_type (lowered_value_type cenv e) /\
            arg_type_fits (lowered_value_type cenv e) (expr_type e)`
  >- (irule body_assign_local_memory_prefix >> metis_tac[]) >>
  irule body_assign_local_widened_prefix >> metis_tac[]
QED
