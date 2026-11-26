Theory bodyRawRevertValueRunMods
Ancestors
  bodyRawRevertValueBindMods bodyRawRevertCompiledTailMods

Theorem raw_revert_value_run_mods:
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx e es ty cap.
    expr_type e = BaseT (BytesT (Dynamic cap)) /\
    evaluate_type (get_tenv cx) (expr_type e) =
      SOME (BaseTV (BytesT (Dynamic cap))) /\
    eval_expr cx (Call NoneT RawRevert [e] NONE) =
      bind (bind (eval_expr cx e) (read_result cx))
        (\v. bind (lift_option_type (dest_BytesV v) "raw_revert data")
                  (\data. raise (Error (RevertData data)))) /\
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Call NoneT RawRevert [e] NONE) es
Proof
  mp_tac raw_revert_value_from_tail_mods >>
  (impl_tac >- MATCH_ACCEPT_TAC raw_revert_compiled_tail_joint_mods) >>
  disch_then ACCEPT_TAC
QED
