(* Forcing a homogeneous MakeArray keeps its materialized memory operand. *)
Theory bodyMakeArrayMaterializedMods
Ancestors
  bodyMakeArraySourceMods bodyAggregateReadMods bodyAggregateReadPostMods
  bodyFullShared exprSimAggregateLayout exprLoweringProps exprLowering compileEnv
  gasShadowCompileStmtHelpers gasShadowState context vyperAST

Theorem make_array_force_cuts[local]:
  lower_value compile_expr ce ty (Builtin (ArrayT et n) (MakeArray (SOME et) n) args) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Builtin (ArrayT et n) (MakeArray (SOME et) n) args)) sha = (op,shb) /\
  gas_shadow_state sa sha ==>
  compile_expr ce ty (Builtin (ArrayT et n) (MakeArray (SOME et) n) args) sa =
    (LocatedValue (ArrayT et n) (mk_ptr op LocMemory),sb) /\
  compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Builtin (ArrayT et n) (MakeArray (SOME et) n) args)) sha =
    (LocatedValue (ArrayT et n) (mk_ptr op LocMemory),shb)
Proof
  strip_tac >>
  Cases_on `compile_expr ce ty (Builtin (ArrayT et n) (MakeArray (SOME et) n) args) sa` >>
  drule_then strip_assume_tac compile_array_literal_inv >>
  `gas_shadow_compiles
     (compile_expr ce ty (Builtin (ArrayT et n) (MakeArray (SOME et) n) args))
     (compile_expr (gas_shadow_env T ce) ty
        (gas_shadow_expr (Builtin (ArrayT et n) (MakeArray (SOME et) n) args)))` by
    MATCH_ACCEPT_TAC gas_shadow_stmt_compile_expr_env >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (Builtin (ArrayT et n) (MakeArray (SOME et) n) args)) sha` >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  gvs[lower_value_def,comp_bind_def,unwrap_value_def,comp_return_def,mk_ptr_def,is_word_type_def]
QED

Theorem make_array_materialized_value_from_vv_mods:
  expr_body_pre_mods mods ce cx env (Builtin ann (MakeArray (SOME et) n) args) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Builtin ann (MakeArray (SOME et) n) args) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (Builtin ann (MakeArray (SOME et) n) args) es
Proof
  strip_tac >> drule_then strip_assume_tac make_array_source_layout_mods >>
  qpat_x_assum `ann = ArrayT et n` SUBST_ALL_TAC >>
  irule materialized_value_from_vv_mods >> asm_rewrite_tac[] >> reverse conj_tac
  >- (rpt gen_tac >>
      qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` kall_tac >>
      drule_all make_array_source_action_mods >> disch_then (fn th => simp[th]) >>
      Cases_on `FST (eval_exprs cx args (es with gas_obs := gs))` >> simp[] >> rw[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac make_array_force_cuts >>
  qexists_tac `LocatedValue (ArrayT et n) (mk_ptr op LocMemory)` >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `raw = Value v` SUBST_ALL_TAC >>
  `(mk_ptr op LocMemory).ptr_location = LocMemory` by simp[mk_ptr_def] >>
  `~is_word_type (ArrayT et n)` by simp[is_word_type_def] >>
  `ptr_buf_ok ce (Builtin (ArrayT et n) (MakeArray (SOME et) n) args)
     (mk_ptr op LocMemory).ptr_operand G t` by
    (qpat_assum `!t' p. LocatedValue _ _ = LocatedValue t' p /\ _ ==> ptr_buf_ok _ _ _ _ _`
       (qspecl_then [`ArrayT et n`,`mk_ptr op LocMemory`] mp_tac) >> simp[]) >>
  drule_all_then strip_assume_tac memory_buffer_read_post_mods >> fs[mk_ptr_def]
QED
