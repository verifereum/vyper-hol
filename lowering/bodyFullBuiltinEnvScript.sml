(*
 * The joint (full) judgments of len, calldata length, the environment
 * items but msg.gas, the account accessors, blockhash, blobhash and
 * method_id, at every horizon (DF H, lo): source GAS origins, memory
 * posts and pointer ghosts share one witness.  bodyFullCases'
 * env_builtin_expr_full_ok is this, with body_expr_full_ok unfolded.
 *
 * TOP-LEVEL:
 *   env_builtin_sim_full
 *)
Theory bodyFullBuiltinEnv
Ancestors
  bodyFullBuiltinEnvEnv bodyFullBuiltinEnvLength bodyFullBuiltinEnvLen
  bodyFullBuiltinEnvAccount bodyFullBuiltinEnvHash
  bodyFullBuiltinEnvMethodIdSuffix bodyFullBuiltinEnvMethodIdRuntime
  bodyFullBuiltinEnvMethodIdLiteral bodyFullBuiltinEnvMethodIdCompose
  bodyFullBuiltinEnvMethodIdPost exprSimHash exprLoweringProps
  bodyFullExprGeneric bodyFullPreds bodySimFull exprSimHypsDefs exprLowering
  vyperTypeSystem vyperAST list

val _ = Parse.hide "body";

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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `builtin_args_length_ok bt (LENGTH args)`
  >- (Cases_on `bt = Len`
      >- (irule len_builtin_sim_full >> metis_tac[]) >>
      Cases_on `bt = CalldataLen`
      >- (irule calldatalen_builtin_sim_full >> metis_tac[]) >>
      Cases_on `?i. bt = Env i /\ i <> MsgGas`
      >- (irule env_item_sim_full >> metis_tac[]) >>
      Cases_on `?i. bt = Acc i`
      >- (irule account_builtin_sim_full >> metis_tac[]) >>
      Cases_on `bt = BlockHash \/ bt = BlobHash`
      >- (irule hash_builtin_sim_full >> metis_tac[]) >>
      `bt = MethodId` by metis_tac[] >> gvs[] >>
      `?e. args = [e]` by
        (Cases_on `args` >> gvs[vyperContextTheory.builtin_args_length_ok_def] >>
         rename1 `h::t` >> Cases_on `t` >> gvs[]) >> gvs[] >>
      `body_expr_full_ok cx e` by fs[body_exprs_full_ok_def] >>
      Cases_on `method_id_literal e`
      >- (irule (MATCH_MP method_id_runtime_sim_full_from_suffix
             method_id_runtime_full_suffix) >> simp[] >> metis_tac[]) >>
      rename1 `method_id_literal e = SOME bs` >>
      `?la l. e = Literal la l` by
        (Cases_on `e` >> gvs[method_id_literal_def] >>
         rename1 `method_id_literal (Literal la l)` >>
         Cases_on `l` >> gvs[method_id_literal_def]) >> gvs[] >>
      `a = BaseT (BytesT (Fixed 4)) \/ a = BaseT (BytesT (Dynamic 4))` by
        (mp_tac (Q.INST [`b` |-> `MethodId`, `ty` |-> `a`,
          `ts` |-> `[expr_type (Literal la l)]`] hash_builtin_types) >>
         gvs[expr_body_pre_def, well_typed_expr_def] >> metis_tac[]) >>
      Cases_on `a = BaseT (BytesT (Fixed 4))`
      >- (gvs[] >> irule method_id_literal_fixed_sim_full >> simp[]) >>
      `a = BaseT (BytesT (Dynamic 4))` by metis_tac[] >> gvs[] >>
      irule (MATCH_MP method_id_literal_dynamic_sim_full_from_endpoint
        method_id_literal_dynamic_endpoint_post) >> simp[]) >>
  irule env_family_bad_arity_sim_full >> metis_tac[]
QED
