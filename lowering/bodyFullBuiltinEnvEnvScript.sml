(* Joint environment builtin cases, including the family's impossible arities. *)
Theory bodyFullBuiltinEnvEnv
Ancestors
  bodyFullExprGeneric bodyFullPreds bodySimFull exprSimHypsDefs exprLowering
  vyperTypeBuiltins vyperTypeSystem vyperAST list

val _ = Parse.hide "body";

Theorem env_family_bad_arity_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (bt = Len \/ bt = CalldataLen \/ (?i. bt = Env i /\ i <> MsgGas) \/
     (?i. bt = Acc i) \/ bt = BlockHash \/ bt = BlobHash \/ bt = MethodId) /\
    ~builtin_args_length_ok bt (LENGTH args) /\
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
  rpt gen_tac >> strip_tac >>
  gvs[expr_body_pre_def, well_typed_expr_def] >>
  drule well_typed_builtin_app_length >> simp[]
QED
