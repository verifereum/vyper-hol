(* The paired value entry of a nested singleton BoolChain is also a VV entry:
   unwrapping its StackValue emits no instructions. *)
Theory s1PrefixBoolChainProperHeadSourceAlignment
Ancestors
  s1PrefixBoolChainEqDemand boolChainCodeLayout gasShadowBoolChainOperands
  gasShadowState gasShadow[qualified] bodyFullShared[qualified]
  s1PrefixDefs exprSimHyps compileEnv exprLowering pair

Theorem bool_chain_proper_head_source_alignment:
  value_read_demand (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    tops cenv cx env (Builtin (BaseT BoolT) (BoolChain p n) [e]) ty es
    (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) ==>
  ?rv sr shadow_sr xl sg shadow_sg sf shadow_sf.
    op = Var rv /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin (BaseT BoolT) (BoolChain p n) [e]) es
      (st0,sa,sb,shadow_sa,shadow_sb,StackValue (BaseT BoolT) (Var rv),s0,G0,tn0) /\
    fresh_var sa = (rv,sr) /\ fresh_var shadow_sa = (rv,shadow_sr) /\
    fresh_label "bool_exit" sr = (xl,sg) /\
    fresh_label "bool_exit" shadow_sr = (xl,shadow_sg) /\
    compile_bool_chain_ops compile_expr cenv p rv xl
      (bool_chain_operands p (n - 1) e) sg = ((),sf) /\
    compile_bool_chain_ops compile_expr (gas_shadow_env T cenv) p rv xl
      (MAP gas_shadow_expr (bool_chain_operands p (n - 1) e)) shadow_sg = ((),shadow_sf) /\
    gas_shadow_state sg shadow_sg /\
    fn_has_code sg sf func /\ fn_has_code shadow_sg shadow_sf shadow_func /\
    sg.cs_current_bb = sa.cs_current_bb /\ sg.cs_current_insts = sa.cs_current_insts /\
    sg.cs_next_var = sa.cs_next_var + 1
Proof
  simp[value_read_demand_def,expr_sim_full_pre_def] >> strip_tac >>
  Cases_on `compile_expr cenv ty (Builtin (BaseT BoolT) (BoolChain p n) [e]) sa` >>
  drule_then strip_assume_tac bool_chain_root_layout >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr _) shadow_sa = (op,shadow_sb)`
    (mp_tac o REWRITE_RULE [gasShadowTheory.gas_shadow_expr_def,
                            gasShadowTheory.gas_shadow_builtin_def,listTheory.MAP]) >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty
    (Builtin (BaseT BoolT) (BoolChain p n) [gas_shadow_expr e]) shadow_sa` >>
  drule_then strip_assume_tac bool_chain_root_layout >>
  simp[lower_value_def,unwrap_value_def,comp_bind_def,comp_return_def] >> strip_tac >>
  gvs[lower_value_def,unwrap_value_def,comp_bind_def,comp_return_def,
      gas_shadow_bool_chain_operands] >>
  rename1 `fresh_var sa = (rv,sr)` >>
  rename1 `fresh_var shadow_sa = (rv,shadow_sr)` >>
  rename1 `fresh_label "bool_exit" sr = (xl,sg)` >>
  rename1 `fresh_label "bool_exit" shadow_sr = (shadow_xl,shadow_sg)` >>
  `gas_shadow_state sr shadow_sr` by
    (mp_then (Pos hd) (drule_all o GEN_ALL) bodyFullSharedTheory.gas_shadow_step
       gas_shadow_compiles_fresh_var >> simp[]) >>
  `shadow_xl = xl /\ gas_shadow_state sg shadow_sg` by
    (mp_then (Pos hd) (drule_all o GEN_ALL) bodyFullSharedTheory.gas_shadow_step
       gas_shadow_compiles_fresh_label >> simp[]) >>
  gvs[expr_vv_sim_full_pre_def,gasShadowTheory.gas_shadow_expr_def,
      gasShadowTheory.gas_shadow_builtin_def] >>
  metis_tac[expr_body_pre_vv_gas_admissible]
QED
