Theory bodyFullBopRestWordLayout
Ancestors
  exprLowering compileEnv context exprSimHypsDefs
  exprSimBopRestWordFacts exprSimSource exprBopLowering exprLoweringProps
  gasShadowState gasShadow gasShadowCompile gasShadowCompileHelpers gasShadowCompileMembership
  exprOperandVar externalEntryShape localPtrsProps freshWrites fragExec

Theorem rest_word_full_compile_layout:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  expr_type e2 = ArrayT (expr_type e1) bd /\
  (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) /\
  lower_value compile_expr cenv ty (gas_shadow_expr (Builtin ann (Bop bop) [e1;e2])) sha = (op,shb) /\
  gas_shadow_state sa sha /\
  fn_has_code sa sb func /\ fn_has_code sha shb shfunc /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?needle vv s1 sm sh1 shm.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (needle,s1) /\
    compile_expr cenv (expr_type e2) e2 s1 = (vv,sm) /\
    compile_var_array_membership cenv needle vv (ArrayT (expr_type e1) bd) (bop = In) sm = (op,sb) /\
    lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) sha = (needle,sh1) /\
    compile_expr cenv (expr_type e2) (gas_shadow_expr e2) sh1 = (vv,shm) /\
    compile_var_array_membership cenv needle vv (ArrayT (expr_type e1) bd) (bop = In) shm = (op,shb) /\
    gas_shadow_state s1 sh1 /\ gas_shadow_state sm shm /\
    cs_extends sa s1 /\ cs_extends s1 sm /\ cs_extends sm sb /\
    cs_extends sha sh1 /\ cs_extends sh1 shm /\ cs_extends shm shb /\
    fn_has_code sa s1 func /\ fn_has_code s1 sm func /\ fn_has_code sm sb func /\
    fn_has_code sha sh1 shfunc /\ fn_has_code sh1 shm shfunc /\ fn_has_code shm shb shfunc /\
    sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
    s1.cs_next_var <= sm.cs_next_var /\ s1.cs_next_id <= sm.cs_next_id /\
    local_ptrs_reserved cenv s1 /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
    (!x. needle = Var x \/ vv_operand vv = Var x ==> not_fresh_at sm x)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all rest_word_nonliteral_dispatch >> disch_tac >>
  qpat_x_assum `lower_value _ _ _ (Builtin _ _ _) sa = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_bop] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       Q.INST [`et` |-> `expr_type e1`, `bd` |-> `bd`] rest_word_nonliteral_dispatch,
       lower_value_child_call] >>
  rpt (pairarg_tac >> gnvs[]) >>
  simp[as_stack_val_pair, unwrap_value_def, comp_return_def] >> strip_tac >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val _ tailcomp` >>
  PairCases_on `tailcomp` >> simp[as_stack_val_pair] >> strip_tac >>
  gnvs[unwrap_value_def, comp_return_def, comp_bind_def, ETA_AX] >>
  rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  suspend "frontiers"
QED

Resume rest_word_full_compile_layout[frontiers]:
  `gas_shadow_compiles (lower_value compile_expr cenv (expr_type e1) e1)
     (lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1))` by
    (irule (SRULE [] (Q.SPEC `T` (Q.GEN `sh` (SPEC_ALL gas_shadow_compiles_lower_value)))) >>
     simp[cj 1 gas_shadow_compile_expr]) >>
  Cases_on `lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) sha` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e1) sha = (shneedle,sh1)` >>
  `shneedle = needle /\ gas_shadow_state st1 sh1` by
    (qpat_x_assum `gas_shadow_compiles _ _` mp_tac >>
     simp[gas_shadow_compiles_def] >> disch_then drule >> simp[]) >>
  gnvs[] >>
  Cases_on `compile_expr cenv (expr_type e2) (gas_shadow_expr e2) sh1` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e2) sh1 = (shvv,shm)` >>
  `shvv = arr_vv /\ gas_shadow_state st2 shm` by
    (qspecl_then [`cenv`, `expr_type e2`, `e2`, `T`] mp_tac (cj 1 gas_shadow_compile_expr) >>
     simp[gas_shadow_compiles_def] >> disch_then drule >> gvs[]) >>
  gnvs[] >>
  `!a t n elems. gas_shadow_expr e2 <> Builtin a (MakeArray t n) elems` by
    (Cases_on `e2` >> simp[gas_shadow_expr_def] >>
     rename1 `Builtin a bi args` >> Cases_on `bi` >>
     gvs[gas_shadow_builtin_def] >> Cases_on `e = MsgGas` >> simp[]) >>
  `expr_type (gas_shadow_expr e2) = ArrayT (expr_type e1) bd` by
    simp[gas_shadow_expr_type] >>
  `compile_var_array_membership cenv needle arr_vv (ArrayT (expr_type e1) bd)
      (bop = In) shm = (op,shb)` by
    (drule_all (Q.INST [`e2` |-> `gas_shadow_expr e2`] rest_word_nonliteral_dispatch) >>
     disch_tac >>
     qpat_x_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, gas_shadow_builtin_def] >>
     simp[Once lower_value_def, comp_bind_def, compile_expr_bop] >>
     simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)), lower_value_child_call] >>
     simp[gas_shadow_expr_type, ETA_AX, as_stack_val_pair, unwrap_value_def, comp_return_def] >>
     simp[SF ETA_ss] >>
     gnvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
     simp[as_stack_val_pair, unwrap_value_def, comp_return_def]) >>
  imp_res_tac (cj 2 compile_expr_grows) >>
  imp_res_tac (cj 1 compile_expr_grows) >>
  `cs_extends st2 sb /\ cs_extends shm shb` by
    (conj_tac
     >- (qspecl_then [`cenv`, `needle`, `arr_vv`, `ArrayT (expr_type e1) bd`, `bop = In`, `st2`]
           mp_tac compile_var_array_membership_labels >> simp[]) >>
     qspecl_then [`cenv`, `needle`, `arr_vv`, `ArrayT (expr_type e1) bd`, `bop = In`, `shm`]
       mp_tac compile_var_array_membership_labels >> simp[]) >>
  `local_ptrs_reserved cenv st1` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. needle = Var x ==> not_fresh_at st1 x` by
    metis_tac[compile_lower_value_var] >>
  `!x. vv_operand arr_vv = Var x ==> not_fresh_at st2 x` by
    metis_tac[cj 1 compiler_compile_var] >>
  simp[] >>
  rpt conj_tac
  >- metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans]
  >- metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans]
  >- metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans]
  >- metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans]
  >- metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans]
  >- metis_tac[fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
Finalise rest_word_full_compile_layout
