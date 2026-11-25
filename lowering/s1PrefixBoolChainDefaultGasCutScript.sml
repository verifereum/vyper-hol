(* Raw expression boundary before marshalling the first omitted default. *)
Theory s1PrefixBoolChainDefaultGasCut
Ancestors
  s1PrefixIntCallStageSingleton gasShadow gasShadowCompileLiteral
  exprLowering bodyFullShared vyperAST list pair

Theorem bool_chain_default_gas_raw_cut:
  compile_stage_intcall_args compile_expr ce
    (Builtin (env_item_type MsgGas) (Env MsgGas) []::rs)
    (flag::fs) (dt::ts) si = (ops,sf) /\
  compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
    (MAP gas_shadow_expr (Builtin (env_item_type MsgGas) (Env MsgGas) []::rs))
    (flag::fs) (dt::ts) sh_si = (ops,sh_sf) /\
  gas_shadow_state si sh_si /\
  fn_has_code si sf func /\ fn_has_code sh_si sh_sf sh_func ==>
  ?op cg sh_cg h cm sh_cm hs.
    compile_env_var MsgGas si = (op,cg) /\
    compile_env_var GasPrice sh_si = (op,sh_cg) /\
    gas_shadow_state cg sh_cg /\
    fn_has_code si cg func /\ fn_has_code sh_si sh_cg sh_func /\
    compile_stage_intcall_args compile_expr ce
      [Builtin (env_item_type MsgGas) (Env MsgGas) []] [flag] [dt] si = ([h],cm) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      [gas_shadow_expr (Builtin (env_item_type MsgGas) (Env MsgGas) [])]
      [flag] [dt] sh_si = ([h],sh_cm) /\
    compile_stage_intcall_args (\_ _ _. comp_return (StackValue (env_item_type MsgGas) op)) ce
      [Builtin (env_item_type MsgGas) (Env MsgGas) []] [flag] [dt] cg = ([h],cm) /\
    compile_stage_intcall_args (\_ _ _. comp_return (StackValue (env_item_type MsgGas) op)) (gas_shadow_env T ce)
      [gas_shadow_expr (Builtin (env_item_type MsgGas) (Env MsgGas) [])]
      [flag] [dt] sh_cg = ([h],sh_cm) /\
    compile_stage_intcall_args compile_expr ce rs fs ts cm = (hs,sf) /\
    compile_stage_intcall_args compile_expr (gas_shadow_env T ce)
      (MAP gas_shadow_expr rs) fs ts sh_cm = (hs,sh_sf) /\
    ops = h::hs /\ gas_shadow_state cm sh_cm /\
    fn_has_code si cm func /\ fn_has_code cm sf func /\
    fn_has_code sh_si sh_cm sh_func /\ fn_has_code sh_cm sh_sf sh_func
Proof
  strip_tac >>
  drule_all intcall_stage_cons_singleton_cut >> strip_tac >>
  Cases_on `compile_env_var MsgGas si` >>
  rename1 `compile_env_var MsgGas si = (op,cg)` >>
  Cases_on `compile_env_var GasPrice sh_si` >>
  rename1 `compile_env_var GasPrice sh_si = (sh_op,sh_cg)` >>
  assume_tac gas_shadow_compiles_env_msggas >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >>
  `compile_expr ce (expr_type (Builtin (env_item_type MsgGas) (Env MsgGas) []))
      (Builtin (env_item_type MsgGas) (Env MsgGas) []) si = (StackValue (env_item_type MsgGas) op,cg)` by
    simp[Once compile_expr_def, compile_expr_def, compile_builtin_dispatch_body_def,
         as_stack_val_def, expr_type_def] >>
  `compile_expr (gas_shadow_env T ce)
      (expr_type (gas_shadow_expr (Builtin (env_item_type MsgGas) (Env MsgGas) [])))
      (gas_shadow_expr (Builtin (env_item_type MsgGas) (Env MsgGas) [])) sh_si =
      (StackValue (env_item_type MsgGas) op,sh_cg)` by
    (simp[gas_shadow_expr_def, gas_shadow_builtin_def, expr_type_def] >>
     simp[Once compile_expr_def, compile_expr_def,
          compile_builtin_dispatch_body_def, as_stack_val_def, expr_type_def]) >>
  `fn_has_code si cg func` by
    (irule fn_has_code_intcall_singleton_head >>
     qpat_assum `compile_stage_intcall_args _ _ [_] _ _ si = _` (irule_at Any) >> simp[]) >>
  `fn_has_code sh_si sh_cg sh_func` by
    (irule fn_has_code_intcall_singleton_head >>
     qpat_assum `compile_stage_intcall_args _ _ [_] _ _ sh_si = _` (irule_at Any) >> simp[]) >>
  simp[] >>
  qpat_assum `compile_expr ce _ _ si = _`
    (simp o single o GSYM o MATCH_MP compile_stage_intcall_args_singleton_from_vv) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) sh_si = _`
    (simp o single o GSYM o MATCH_MP compile_stage_intcall_args_singleton_from_vv)
QED
