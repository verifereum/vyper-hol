(* The forced hash result uses the stack operand of the checked VV run. *)
Theory bodyHashSimPairMods
Ancestors
  bodyHashOperandMods bodyAggregateReadMods bodyAggregateReadPostMods
  bodyFullPredsMods bodyFullShared exprBodyPreProps exprSimHash exprBopLowering
  exprLowering exprLoweringProps gasShadowCompileStmtHelpers
  vyperAST vyperTyping vyperTypeSystem vyperInterpreter compileEnv

Theorem hash_compile_stack[local]:
  b = Keccak256 \/ b = Sha256 ==>
  ?op sb. compile_expr cenv ty (Builtin ann b [e]) sa = (StackValue ann op,sb)
Proof
  disch_then (fn th => simp[MATCH_MP compile_hash_singleton th]) >>
  pairarg_tac >> simp[as_stack_val_pair]
QED

Theorem hash_sim_pair_mods:
  (b = Keccak256 \/ b = Sha256) /\
  (builtin_args_length_ok b (LENGTH args) ==> body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann b args) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann b args) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann b args) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  reverse conj_asm2_tac
  >- (irule hash_route_from_suffixes_mods >> asm_rewrite_tac[] >>
      qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> asm_rewrite_tac[]) >>
  `well_typed_builtin_app ann b (MAP expr_type args)` by
    (drule expr_body_pre_mods_well_typed >> simp[Once well_typed_expr_def]) >>
  `?e. args = [e]` by
    (drule_at Any hash_builtin_types >>
     Cases_on `b = Keccak256` >> gvs[] >>
     strip_tac >> rename1 `args = [arg]` >>
     qexists_tac `arg` >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `args = [_]` SUBST_ALL_TAC >>
  irule materialized_value_from_vv_mods >> asm_rewrite_tac[] >>
  reverse conj_tac
  >- (rpt strip_tac >> drule_then ACCEPT_TAC eval_expr_builtin_value) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?x sm. compile_expr cenv ty (Builtin ann b [e]) sa = (StackValue ann x,sm)` by
    (irule hash_compile_stack >> first_assum ACCEPT_TAC) >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty
              (gas_shadow_expr (Builtin ann b [e])) shadow_sa` >>
  `gas_shadow_compiles (compile_expr cenv ty (Builtin ann b [e]))
     (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (Builtin ann b [e])))` by
    MATCH_ACCEPT_TAC gas_shadow_stmt_compile_expr_env >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  gvs[lower_value_def,comp_bind_def,unwrap_value_def,comp_return_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule stack_value_read_post_mods >> simp[] >>
  disch_then (qspecl_then [`tn`,`G`] mp_tac) >> simp[]
QED
