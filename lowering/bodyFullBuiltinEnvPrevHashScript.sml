(* Joint full simulation of the previous-block hash environment builtin. *)
Theory bodyFullBuiltinEnvPrevHash
Ancestors
  bodyFullBuiltinEnvPrevHashSeq
  bodyFullExprGeneric bodyFullGhostFrame bodyFullPreds bodySimFull
  gasOutcomeFullCompose fragGasSeqPtr builtinProps exprSimProps exprSimSource
  exprSimHypsDefs exprLowering exprLoweringProps emitHelperProps emitHelper
  vyperTypeBuiltins vyperTypeSystem vyperAST vyperInterpreter vyperContext
  venomExecSemantics venomInst venomState compileEnv list rich_list
  vyperStorageTrace vyperStorageFootprint loweringStateRelDefs

val _ = Parse.hide "body";

Theorem env_prevhash_value_full[local]:
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin (env_item_type PrevHash) (Env PrevHash) []) es
Proof
  rw[expr_sim_full_def] >>
  irule gas_outcome_full_initial_domain >>
  simp[storage_trace_frame_bind, evaluate_storage_trace_frame,
       storage_trace_frame_read_result] >>
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by gvs[storage_trace_domain_def] >>
  `tx_env_ok cx.txn` by
    (first_x_assum drule >> gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def]) >>
  drule lower_value_env >> strip_tac >>
  cheat
QED

Theorem env_prevhash_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    bt = Env PrevHash /\ builtin_args_length_ok bt (LENGTH args) /\
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
  rpt gen_tac >> strip_tac >> gvs[] >>
  `args = [] /\ a = env_item_type PrevHash` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def] >>
  gvs[] >> conj_tac >- simp[env_prevhash_value_full] >>
  irule expr_vv_sim_stack_full >>
  simp[expr_type_def, env_item_type_def, is_word_type_def,
       env_prevhash_value_full] >>
  conj_tac
  >- (gen_tac >> simp[compile_expr_def] >>
      Cases_on `compile_env_var PrevHash sa` >> simp[as_stack_val_def]) >>
  metis_tac[eval_expr_builtin_value]
QED
