(*
 * Expression simulation: abi_encode's argument list, counted.
 *
 * compile_abi_encode_args compiles the operands of a tuple abi_encode,
 * materializing a composite operand when a later one may mutate.  From
 * the operands' case hypotheses, running the compiled list follows
 * eval_exprs as an actual counted path: on success every operand is
 * related to its value at the end, and every exception ends in its exit.
 *)

Theory exprSimAbiEncodeArgs
Ancestors
  abiEncodeArgsSim abiEncodeArgsCase exprSimAbiEncodeArgsUncaptured
  exprSimAbiEncodeArgsCaptured exprSimHypsDefs exprSimWordArgs
  abiDecoderReentry exprSimAbiGasBridge

Theorem compile_abi_encode_args_sim_live:
  !args ctx func ce cx Inv env es sa ops sb s0.
    abi_args_ready ctx func ce cx Inv args /\ Inv es /\
    (!s. Inv s ==> expr_sim_inv ce cx env s) /\
    (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
    EVERY (\e. !s. Inv s ==> expr_body_pre ce cx env e s) args /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\
    stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
      (\rr ee t. ?vs. rr = INL vs /\
         abi_args_post ctx func ce cx es sa sb s0 ee args ops vs t /\
         EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\rr ee r. wb_args_exit rr r)
Proof
  Induct_on `args`
  >- (rpt strip_tac >>
      gvs[exprLoweringTheory.compile_abi_encode_args_def,
          compileEnvTheory.comp_return_def] >>
      irule exprSimMemDefsTheory.gas_outcome_post_mono >>
      qexists_tac `\rr ee t. ?vs. rr = INL vs /\
        wb_args_post ctx func ce cx es sa s0 ee [] vs t /\
        t.vs_current_bb = sa.cs_current_bb /\
        t.vs_inst_idx = LENGTH sa.cs_current_insts` >>
      conj_tac
      >- (simp[wb_args_post_def, abi_args_post_nil] >> metis_tac[]) >>
      irule lower_word_args_nil_sim >> simp[])
  >> rpt strip_tac
  >> rename1 `abi_args_ready ctx func ce cx Inv (e::args)`
  >> gvs[abi_args_compile_cons, listTheory.EVERY_DEF]
  >> Cases_on `~is_word_type (expr_type e) /\ exprs_can_mutate ce args`
  >- (gvs[] >>
      `ci_mono sa mid` by
        metis_tac[exprLoweringPropsTheory.compile_expr_ci_mono, pairTheory.SND] >>
      `ci_mono mid sm` by
        metis_tac[exprLoweringPropsTheory.ci_mono_compile_materialize_vv, pairTheory.SND] >>
      `ci_mono sm sb` by metis_tac[abi_args_compile_mono, pairTheory.SND] >>
      `cs_extends sa mid /\ cs_extends mid sm /\ cs_extends sm sb` by
        gvs[exprLoweringPropsTheory.ci_mono_def] >>
      `fn_has_code sa mid func /\ fn_has_code mid sm func /\ fn_has_code sm sb func` by
        metis_tac[fragExecTheory.fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
      `local_ptrs_reserved ce mid /\ local_ptrs_reserved ce sm` by
        metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
                  exprLoweringPropsTheory.ci_mono_def] >>
      drule_all abi_args_ready_head >> strip_tac >>
      `expr_body_pre ce cx env e es` by metis_tac[] >>
      `!l. op <> Label l` by metis_tac[abi_args_materialize_not_label] >>
      `!x. op = Var x ==> not_fresh_at sm x` by
        metis_tac[exprOperandVarTheory.compiler_materialize_vv_var] >>
      `!x. vv_operand vv = Var x ==> not_fresh_at mid x` by
        metis_tac[exprOperandVarTheory.compiler_compile_var] >>
      `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
        metis_tac[exprSimHypsTheory.expr_body_pre_vv_gas_admissible] >>
      irule (SRULE [listTheory.EVERY_DEF] abi_args_captured_cons_sim_live) >>
      simp[] >>
      conj_tac
      >- (rpt strip_tac >>
          drule vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom >>
          simp[])
      >> conj_tac
      >- (rpt strip_tac >>
          `Inv (es with gas_obs := gs)` by metis_tac[] >>
          drule_all abi_args_ready_head >>
          simp[] >> metis_tac[])
      >> simp[abi_args_materialize_not_label,
              exprOperandVarTheory.compiler_materialize_vv_var,
              exprOperandVarTheory.compiler_compile_var,
              exprSimHypsTheory.expr_body_pre_vv_gas_admissible] >>
      reverse conj_tac >- metis_tac[] >>
      rpt strip_tac >>
      `Inv (es with gas_obs := gs)` by metis_tac[] >>
      drule_all abi_args_ready_head >> strip_tac >>
      `Inv es1` by metis_tac[] >>
      `abi_args_ready ctx func ce cx Inv args` by
        metis_tac[abi_args_ready_tail] >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >> gnvs[]
  >> `lower_value compile_expr ce (expr_type e) e sa = (op,sm)` by
    simp[exprLoweringTheory.lower_value_def, compileEnvTheory.comp_bind_def]
  >> `ci_mono sa mid` by
    metis_tac[exprLoweringPropsTheory.compile_expr_ci_mono, pairTheory.SND]
  >> `ci_mono mid sm` by
    metis_tac[exprLoweringPropsTheory.ci_mono_unwrap_value, pairTheory.SND]
  >> `ci_mono sm sb` by metis_tac[abi_args_compile_mono, pairTheory.SND]
  >> `cs_extends sa mid /\ cs_extends mid sm /\ cs_extends sm sb` by
    gvs[exprLoweringPropsTheory.ci_mono_def]
  >> `cs_extends sa sm` by metis_tac[compileEnvTheory.cs_extends_trans]
  >> `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fragExecTheory.fn_has_code_split]
  >> `local_ptrs_reserved ce sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var,
              exprLoweringPropsTheory.ci_mono_def]
  >> drule_all abi_args_ready_head >> strip_tac
  >> `expr_body_pre ce cx env e es` by metis_tac[]
  >> `!x. op = Var x ==> not_fresh_at sm x` by
    metis_tac[exprOperandVarTheory.compile_lower_value_var]
  >> `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[exprSimSourceTheory.expr_body_pre_gas_admissible]
  >> `ci_mono sa sm` by
    (gvs[exprLoweringPropsTheory.ci_mono_def] >>
     metis_tac[compileEnvTheory.cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS])
  >> irule (SRULE [listTheory.EVERY_DEF] abi_args_uncaptured_cons_sim_live)
  >> simp[]
  >> conj_tac
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (drule vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom >> simp[]) >>
      Cases_on `is_word_type (expr_type e)`
      >- (drule exprSimHypsTheory.expr_body_pre_physical_type >>
          metis_tac[exprSimLayoutTransportTheory.compatible_word_type]) >>
      `~exprs_can_mutate ce args` by metis_tac[] >>
      drule_all abiEncodeArgsScopesTheory.eval_exprs_no_mutation_scopes >> simp[])
  >> reverse conj_tac
  >- (qexists_tac `env` >> simp[] >> rpt strip_tac >>
      `Inv (es with gas_obs := gs)` by metis_tac[] >>
      drule_all abi_args_ready_head >> simp[] >> metis_tac[])
  >> rpt strip_tac
  >> `Inv (es with gas_obs := gs)` by metis_tac[]
  >> drule_all abi_args_ready_head >> strip_tac
  >> `Inv es1` by metis_tac[]
  >> `abi_args_ready ctx func ce cx Inv args` by
    metis_tac[abi_args_ready_tail]
  >> first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem compile_abi_encode_args_sim:
  !args ctx func ce cx Inv env es sa ops sb s0.
    abi_args_ready ctx func ce cx Inv args /\ Inv es /\
    (!s. Inv s ==> expr_sim_inv ce cx env s) /\
    (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
    EVERY (\e. !s. Inv s ==> expr_body_pre ce cx env e s) args /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\
    stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
      (\rr ee t. ?vs. rr = INL vs /\
         abi_args_post ctx func ce cx es sa sb s0 ee args ops vs t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\rr ee r. wb_args_exit rr r)
Proof
  rpt strip_tac >>
  drule_all compile_abi_encode_args_sim_live >>
  strip_tac >> irule exprSimMemDefsTheory.gas_outcome_post_mono >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem compile_abi_encode_args_case_gas_sim:
  !nocalls ctx func ce cx env ann ensure mid ty args es sa ops sb s0.
    exprs_case nocalls ctx func ce cx args /\
    expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) ty args) es /\
    (nocalls ==>
     int_calls_expr (TypeBuiltin ann (AbiEncode ensure mid) ty args) = []) /\
    compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\
    stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
      (\rr ee t. ?vs. rr = INL vs /\
         abi_args_post ctx func ce cx es sa sb s0 ee args ops vs t /\
         EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\rr ee r. wb_args_exit rr r)
Proof
  rpt strip_tac >>
  irule compile_abi_encode_args_sim_live >> simp[] >>
  qexistsl_tac [`expr_sim_inv ce cx env`, `env`] >>
  simp[expr_sim_inv_gas_obs] >>
  conj_tac
  >- gvs[expr_body_pre_def] >>
  reverse conj_tac
  >- (irule abi_args_ready_case >> metis_tac[]) >>
  simp[listTheory.EVERY_MEM] >>
  metis_tac[abi_args_body_pre_arg]
QED
