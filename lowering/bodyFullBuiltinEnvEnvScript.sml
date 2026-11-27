(* Joint environment builtin cases, including the family's impossible arities. *)
Theory bodyFullBuiltinEnvEnv
Ancestors
  bodyFullBuiltinEnvReads bodyFullBuiltinEnvPrevHash
  bodyFullExprGeneric bodyFullPreds bodySimFull exprSimHypsDefs exprLowering
  vyperTypeBuiltins vyperTypeSystem vyperAST list
  bodyFullPredsMods[qualified] bodyInvSplit[qualified]

val _ = Parse.hide "body";

Theorem env_family_bad_arity_sim_full:
  !mods exps DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i /\ i <> MsgGas) \/
     (?i. bt = Acc i) \/ bt = BlockHash \/ bt = BlobHash \/ bt = MethodId) /\
    ~builtin_args_length_ok bt (LENGTH args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt <> Len ==>
     body_exprs_full_ok_mods mods exps cx args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt = Len ==>
     body_expr_full_ok_mods mods exps cx (HD args)) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >>
  gvs[expr_body_pre_def, cj 9 well_typed_expr_def] >>
  drule well_typed_builtin_app_length >> simp[]
QED

Theorem env_item_sim_full:
  !mods exps DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (?i. bt = Env i /\ i <> MsgGas) /\
    builtin_args_length_ok bt (LENGTH args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt <> Len ==>
     body_exprs_full_ok_mods mods exps cx args) /\
    (builtin_args_length_ok bt (LENGTH args) /\ bt = Len ==>
     body_expr_full_ok_mods mods exps cx (HD args)) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `i = PrevHash`
  >- (gvs[] >> irule env_prevhash_sim_full >> simp[] >> metis_tac[]) >>
  irule env_reads_sim_full >> simp[] >> metis_tac[]
QED
