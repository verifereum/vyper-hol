(* Joint environment builtin family dispatcher. *)
Theory bodyFullBuiltinEnv
Ancestors
  bodyFullBuiltinEnvLength bodyFullBuiltinEnvEnv bodyFullBuiltinEnvAccount
  bodyFullBuiltinEnvHash bodyFullBuiltinEnvMethodIdLiteral
  bodyFullBuiltinEnvMethodIdRuntime bodyFullBuiltinEnvMethodIdSuffix
  bodyFullBuiltinEnvMethodIdCompose bodyFullBuiltinEnvMethodIdPost
  bodyFullPreds bodySimFull exprSimHypsDefs exprSimHash exprLowering
  vyperTypeBuiltins vyperTypeSystem vyperContext vyperAST list

Theorem env_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i /\ i <> MsgGas) \/
     (?i. bt = Acc i) \/ bt = BlockHash \/ bt = BlobHash \/ bt = MethodId) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt <> Len ==>
     body_exprs_full_ok cx args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt = Len ==>
     body_expr_full_ok cx (HD args)) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> disch_tac >>
  reverse (Cases_on `builtin_args_length_ok bt (LENGTH args)`)
  >- (irule env_family_bad_arity_sim_full >> metis_tac[]) >>
  qpat_x_assum `_ /\ _` strip_assume_tac
  >- (irule length_builtin_sim_full >> metis_tac[])
  >- (irule length_builtin_sim_full >> metis_tac[])
  >- (irule env_item_sim_full >> metis_tac[])
  >- (irule account_builtin_sim_full >> metis_tac[])
  >- (irule hash_builtin_sim_full >> metis_tac[])
  >- (irule hash_builtin_sim_full >> metis_tac[]) >>
  gvs[] >>
  `?e. args = [e]` by
    (Cases_on `args` >> gvs[builtin_args_length_ok_def] >>
     Cases_on `t` >> gvs[]) >> gvs[] >>
  `body_expr_full_ok cx e` by gvs[body_exprs_full_ok_def] >>
  Cases_on `method_id_literal e = NONE`
  >- (mp_tac method_id_runtime_sim_full_from_suffix >>
      (impl_tac >- MATCH_ACCEPT_TAC method_id_runtime_full_suffix) >>
      disch_then irule >> metis_tac[]) >>
  `?la l. e = Literal la l` by
    (Cases_on `e` >> gvs[method_id_literal_def] >> metis_tac[]) >> gvs[] >>
  `a = BaseT (BytesT (Dynamic 4)) \/ a = BaseT (BytesT (Fixed 4))` by
    (gvs[expr_body_pre_def, well_typed_expr_def] >>
     drule (SRULE [] (Q.INST [`b` |-> `MethodId`] hash_builtin_types)) >>
     simp[]) >>
  Cases_on `method_id_literal (Literal la l)` >> gvs[]
  >- (mp_tac method_id_literal_dynamic_sim_full_from_endpoint >>
      (impl_tac >- MATCH_ACCEPT_TAC method_id_literal_dynamic_endpoint_post) >>
      disch_then irule >> metis_tac[]) >>
  irule method_id_literal_fixed_sim_full >> metis_tac[]
QED
