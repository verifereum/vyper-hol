Theory bodyFullRawLogLayout
Ancestors
  bodyFullRawLogFixedBoundary bodyFullExprGeneric exprLoweringProps
  gasShadow gasShadowState fragExec exprLowering compileEnv exprCallbackContracts vyperAST
Libs pairLib

Theorem raw_log_full_layout_shadow:
  (!ce ty e. gas_shadow_compiles (lower_value compile_expr ce ty e)
    (lower_value compile_expr ce ty (gas_shadow_expr e))) /\
  (!ce xs. gas_shadow_compiles (compile_multi_exprs compile_expr ce xs)
    (compile_multi_exprs compile_expr ce (MAP gas_shadow_expr xs))) /\
  gas_shadow_state sa shadow_sa /\
  lower_value compile_expr cenv ty
    (Call ann RawLog [Builtin a (MakeArray elem bd) topics; data] dflt) sa = (op,sb) /\
  lower_value compile_expr cenv ty
    (gas_shadow_expr (Call ann RawLog [Builtin a (MakeArray elem bd) topics; data] dflt))
    shadow_sa = (op,shadow_sb) /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
  op = Lit 0w /\
  compile_call compile_expr cenv ann ty RawLog
    [Builtin a (MakeArray elem bd) topics; data] dflt sa =
    (StackValue ann (Lit 0w),sb) /\
  ?ops sm shadow_sm sd shadow_sd value sn shadow_sn.
    compile_multi_exprs compile_expr cenv topics sa = (ops,sm) /\
    compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr topics)
      shadow_sa = (ops,shadow_sm) /\
    gas_shadow_state sm shadow_sm /\ gas_shadow_state sd shadow_sd /\
    gas_shadow_state sn shadow_sn /\
    lower_value compile_expr cenv (expr_type data) data sd = (value,sn) /\
    lower_value compile_expr cenv (expr_type data) (gas_shadow_expr data)
      shadow_sd = (value,shadow_sn) /\
    ci_mono sa sm /\ ci_mono sm sd /\ ci_mono sd sn /\ ci_mono sn sb /\
    fn_has_code sa sm func /\ fn_has_code sm sd func /\
    fn_has_code sd sn func /\ fn_has_code sn sb func /\
    fn_has_code shadow_sa shadow_sm shadow_func /\
    fn_has_code shadow_sm shadow_sd shadow_func /\
    fn_has_code shadow_sd shadow_sn shadow_func /\
    fn_has_code shadow_sn shadow_sb shadow_func /\
    ((expr_type data = BaseT (BytesT (Fixed 32)) /\
      ?buf s1 shadow_s1.
        compile_alloc_buffer 32 sm = (buf,sd) /\
        compile_alloc_buffer 32 shadow_sm = (buf,shadow_sd) /\
        emit_inst MSTORE [buf.buf_operand;value] [] sn = ((),s1) /\
        emit_inst MSTORE [buf.buf_operand;value] [] shadow_sn = ((),shadow_s1) /\
        emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++
          [Lit 32w;buf.buf_operand]) [] s1 = ((),sb) /\
        emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++
          [Lit 32w;buf.buf_operand]) [] shadow_s1 = ((),shadow_sb)) \/
     (expr_type data <> BaseT (BytesT (Fixed 32)) /\
      ?len ptr s1 s2 shadow_s1 shadow_s2.
       sd = sm /\ shadow_sd = shadow_sm /\
       emit_op MLOAD [value] sn = (len,s1) /\
       emit_op MLOAD [value] shadow_sn = (len,shadow_s1) /\
       emit_op ADD [value;Lit 32w] s1 = (ptr,s2) /\
       emit_op ADD [value;Lit 32w] shadow_s1 = (ptr,shadow_s2) /\
       emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len;ptr]) [] s2 = ((),sb) /\
       emit_inst LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [len;ptr]) [] shadow_s2 = ((),shadow_sb)))
Proof
  strip_tac >>
  `!ce tt aa args df st.
     compile_expr ce tt (Call aa RawLog args df) st =
     compile_call compile_expr ce aa tt RawLog args df st` by
    (rpt gen_tac >>
     pure_once_rewrite_tac[CONJUNCT1 compile_expr_raw_def] >>
     pure_rewrite_tac[compile_expr_body_def, expr_type_def, LET_THM] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >>
     simp[compile_call_child_calls]) >>
  qpat_x_assum `lower_value _ _ _ (Call _ _ _ _) _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  Cases_on `expr_type data = BaseT (BytesT (Fixed 32))`
  >- suspend "fixed" >> suspend "dynamic"
QED

Resume raw_log_full_layout_shadow[fixed]:
  drule_all raw_log_fixed_layout >> strip_tac >>
  gvs[raw_log_topic_exprs_def, unwrap_value_def, comp_return_def] >>
  Cases_on `compile_multi_exprs compile_expr cenv (MAP gas_shadow_expr topics) shadow_sa` >>
  rename1 `compile_multi_exprs _ _ _ shadow_sa = (sops,ss1)` >>
  qpat_assum `!ce xs. gas_shadow_compiles _ _`
    (qspecl_then [`cenv`,`topics`] (mp_tac o REWRITE_RULE [gas_shadow_compiles_def])) >>
  disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  `gas_shadow_compiles
    (lower_value compile_expr cenv (expr_type data) data)
    (lower_value compile_expr cenv (expr_type data) (gas_shadow_expr data))` by metis_tac[] >>
  assume_tac (Q.SPEC `32` gas_shadow_compiles_alloc_buffer) >>
  fs[] >> drule_all raw_log_fixed_continuation_shadow >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr (Call _ _ _ _)) _ = _` mp_tac >>
  simp[gas_shadow_expr_def, gas_shadow_builtin_def, Once lower_value_def,
    comp_bind_def, compile_call_def, raw_log_topic_exprs_def,
    unwrap_value_def, comp_return_def] >> strip_tac >> gvs[] >>
  FAIL_TAC "fixed mono"
QED
Resume raw_log_full_layout_shadow[dynamic]:
  cheat
QED
Finalise raw_log_full_layout_shadow
