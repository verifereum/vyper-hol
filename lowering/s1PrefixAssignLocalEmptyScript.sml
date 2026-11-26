(* Request-prefix companion to bodyFullAssignLocalEmpty. *)
Theory s1PrefixAssignLocalEmpty
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixFrame assignBasePtrLocalBodyFacts
  exprBodyPreProps memoryLocalRhsProps stmtSimAssignMem targetPlaceSim
  vyperStorageTrace

Theorem body_assign_local_memory_empty_prefix:
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
  ~is_word_type ty /\
  0 < type_memory_bytes cenv ty /\
  has_length_word (expr_type e) /\
  is_empty_value_expr e ==>
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty
        (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all assign_base_local_rhs_pre >> strip_tac >>
  drule_all expr_sim_inv_local >> strip_tac >>
  drule expr_body_pre_env_type_defs >> strip_tac >>
  rename1 `lookup_scopes id es.scopes = SOME ent` >>
  `evaluate_type (get_tenv cx) ty = SOME ent.type` by metis_tac[] >>
  `!gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
        (INL (default_value ent.type), es with gas_obs := gs)` by
    metis_tac[memory_rhs_empty_read_destination] >>
  rw[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  drule_all assign_local_identity_rhs_all_tails >> strip_tac >>
  irule gas_prefix_full_no_outcome >>
  simp[evaluate_storage_trace_frame]
QED
