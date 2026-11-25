(* The installed Send argument interval ends at the actual CALL cursor. *)
Theory entryCreateSendLayout
Ancestors
  s1PrefixDefs bodyFullWordArgs exprSimSend exprLoweringProps
  gasShadowState gasShadow compilerInstructionSuffix fragExec abiEncoderProps
  vyperInterpreter vyperState rich_list list pred_set arithmetic

Theorem send_word_source_bind:
  expr_body_pre ce cx env (Call ann (Send has_gas) args dflt) es ==>
  bind (eval_expr cx (Call ann (Send has_gas) args dflt)) (read_result cx) =
    bind (eval_exprs cx args) (\vs. bind (eval_send cx has_gas vs) (read_result cx)) /\
  (!e mid. MEM e args /\ expr_sim_inv ce cx env mid ==>
    expr_body_pre ce cx env e mid /\ is_word_type (expr_type e))
Proof
  strip_tac >> drule send_pre_types >> strip_tac >> conj_tac
  >- (pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
      Cases_on `bind (eval_expr cx (Call ann (Send has_gas) args dflt))
                     (read_result cx) x` >>
      drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_send_cases) >>
      strip_tac >> gvs[bind_def]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[expr_body_pre_send_arg] >>
  gvs[EVERY_MEM]
QED

Theorem send_word_shadow_mid[local]:
  lower_word_args ce expr_type args sa = (ops,sm) /\ gas_shadow_state sa sha ==>
  ?shm. lower_word_args (gas_shadow_env T ce) expr_type (MAP gas_shadow_expr args) sha =
          (ops,shm) /\ gas_shadow_state sm shm
Proof
  strip_tac >>
  `gas_shadow_compiles (lower_word_args ce expr_type args)
      (lower_word_args (gas_shadow_env T ce) expr_type (MAP gas_shadow_expr args))` by
    (irule gas_shadow_compiles_lower_word_args >> simp[gas_shadow_expr_type]) >>
  fs[gas_shadow_compiles_def] >>
  first_x_assum (qspecl_then [`sa`,`sha`] mp_tac) >> simp[] >>
  Cases_on `lower_word_args (gas_shadow_env T ce) expr_type
    (MAP gas_shadow_expr args) sha` >> simp[]
QED

Theorem send_word_intervals[local]:
  lower_word_args ce expr_type args sa = (ops,sm) /\
  emit_op CALL call_ops sm = (success,s3) /\ emit_void ASSERT [success] s3 = ((),sb) /\
  fn_has_code sa sb f ==>
  ci_mono sa sm /\ ci_mono sm sb /\
  fn_has_code sa sm f /\ fn_has_code sm sb f
Proof
  strip_tac >> drule ci_mono_lower_word_args >> strip_tac >>
  drule added_insts_emit_op >> strip_tac >>
  drule added_insts_emit_void >> strip_tac >>
  `ci_mono sm sb` by metis_tac[ci_mono_trans] >>
  fs[ci_mono_def] >> metis_tac[fn_has_code_split]
QED

Theorem send_word_site_layout:
  expr_body_pre ce cx env (Call ann (Send has_gas) args dflt) es /\
  (expr_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty (Call ann (Send has_gas) args dflt)
     es (st0,sa,sb,sha,shb,op,s0,G0,tn0) \/
   expr_vv_sim_full_pre (DF,lo,d,C,shC,PG,f,shf) ce cx ty (Call ann (Send has_gas) args dflt)
     es (st0,sa,sb,sha,shb,vv,s0,G0,tn0)) ==>
  ?addr amount gas sm shm success s3 shsuccess shs3.
    ann = NoneT /\
    MAP expr_type args =
      [BaseT AddressT; BaseT (UintT 256)] ++ (if has_gas then [BaseT (UintT 256)] else []) /\
    LENGTH args = (if has_gas then 3 else 2) /\
    lower_word_args ce expr_type args sa =
      ([addr;amount] ++ (if has_gas then [gas] else []),sm) /\
    lower_word_args (gas_shadow_env T ce) expr_type (MAP gas_shadow_expr args) sha =
      ([addr;amount] ++ (if has_gas then [gas] else []),shm) /\
    gas_shadow_state sm shm /\ (~has_gas ==> gas = Lit 0w) /\
    emit_op CALL [gas;addr;amount;Lit 0w;Lit 0w;Lit 0w;Lit 0w] sm = (success,s3) /\
    emit_void ASSERT [success] s3 = ((),sb) /\
    emit_op CALL [gas;addr;amount;Lit 0w;Lit 0w;Lit 0w;Lit 0w] shm = (shsuccess,shs3) /\
    emit_void ASSERT [shsuccess] shs3 = ((),shb) /\
    ci_mono sa sm /\ ci_mono sm sb /\ ci_mono sha shm /\ ci_mono shm shb /\
    fn_has_code sa sm f /\ fn_has_code sm sb f /\
    fn_has_code sha shm shf /\ fn_has_code shm shb shf /\
    frag_ids sa sm SUBSET frag_ids sa sb /\ frag_ids sm sb SUBSET frag_ids sa sb
Proof
  strip_tac >>
  gvs[expr_sim_full_pre_def, expr_vv_sim_full_pre_def, gas_shadow_expr_def] >>
  imp_res_tac lower_value_send >> gvs[] >>
  drule send_pre_types >> strip_tac >> gvs[] >>
  `MAP expr_type (MAP gas_shadow_expr args) = MAP expr_type args` by
    simp[MAP_MAP_o, combinTheory.o_DEF, gas_shadow_expr_type, ETA_AX] >>
  qpat_assum `compile_expr _ _ (Call _ _ args _) sa = _`
    (mp_then Any mp_tac compile_expr_send) >>
  simp[] >> strip_tac >>
  drule_all send_word_shadow_mid >> strip_tac >>
  qpat_assum `compile_expr _ _ (Call _ _ (MAP _ _) _) sha = _`
    (mp_then Any mp_tac compile_expr_send) >>
  simp[] >> strip_tac >>
  Cases_on `has_gas` >> gvs[] >>
  `ci_mono sa sm /\ ci_mono sm sb /\ fn_has_code sa sm f /\ fn_has_code sm sb f` by
    (irule send_word_intervals >> metis_tac[]) >>
  `ci_mono sha shm /\ ci_mono shm shb /\ fn_has_code sha shm shf /\ fn_has_code shm shb shf` by
    (irule send_word_intervals >> metis_tac[]) >>
  fs[ci_mono_def, frag_ids_def, SUBSET_DEF]
QED
