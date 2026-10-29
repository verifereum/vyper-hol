(*
 * Expression simulation: send (#636, Calls row 2)
 *
 * send(to, value[, gas=g]) lowers its word operands with lower_value, left
 * to right (lower_word_args at each operand's own type), then a CALL
 * [gas; to; value; 0; 0; 0; 0], gas being Lit 0w without gas=, and an
 * ASSERT of the success word; its value is StackValue NoneT (Lit 0w).  In
 * oracle mode the CALL takes the same outcome as the source's eval_send
 * (extCallOracleStep's send_call_oracle_step): on success both adopt it and
 * state_rel holds after, on failure the source raises "send failed" and
 * the ASSERT of the 0w success word aborts.  expr_sim_inv's
 * outcomes_accounts_typed rules out the third source result, the
 * "call outcome accounts" error, which Venom does not make.  The NoneV
 * result occupies no bytes, so expr_val_at holds of it wherever Lit 0w
 * points.
 *
 * TOP-LEVEL:
 *   compile_send_case_sim — expr_vv_ok of send
 *
 * Helpers:
 *   compile_expr_call, compile_expr_send, compile_expr_send_stack — the
 *     compile side
 *   eval_expr_send_cases, eval_send_value, eval_send_read,
 *     eval_expr_send_value,
 *     take_call_outcome_typed,
 *     eval_send_outcome_typed, address_typed_dest, uint256_typed_dest — the
 *     source side
 *   expr_sim_pre_send_arg, send_pre_types, typed_args_ready_inv — the
 *     operands
 *   send_tail_shape, send_tail_frag, expr_post_none_intro — the CALL and
 *     the ASSERT
 *)

Theory exprSimSend
Ancestors
  list pair vyperMisc fragExec loweringSlice exprSim exprSimHyps exprSimWordArgs
  exprSimPrecompiles exprSimOperators exprSimOperands exprSimAccounts
  extCallOracleStep exprCallbackContracts exprCallBounds exprLowering
  exprLoweringProps emitHelper compileEnv localPtrsProps valueEncoding
  vyperAST vyperInterpreter vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeCallGraph vyperCallOutcome extCallOracle
  vyperRuntimeAccounts vyperTypeInvariants vyperEvalExprPreservesScopesDom
  venomExecSemantics venomInst venomState
Libs
  pairLib

(* ===== The compile side ===== *)

Theorem compile_expr_call:
  !cenv ty ann target args dflt st.
    compile_expr cenv ty (Call ann target args dflt) st =
    compile_call compile_expr cenv ann ty target args dflt st
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       expr_type_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  irule compile_call_callback_contract >>
  irule expr_child_callback_agrees >>
  rpt strip_tac >> drule call_callback_child_bound >>
  simp[expr_size_def]
QED

Theorem compile_expr_send_stack:
  !cenv ty ann has_gas args dflt sa vv sb.
    compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa = (vv, sb) ==>
    vv = StackValue ann (Lit 0w)
Proof
  rpt gen_tac >> simp[compile_expr_call, compile_call_def] >>
  BasicProvers.every_case_tac >> rpt (pairarg_tac >> gvs[])
QED

(* With operands of send's types, the lowering is lower_word_args at the
   operands' own types, then the CALL and the ASSERT. *)
Theorem compile_expr_send:
  !cenv ty ann has_gas args dflt sa vv sb.
    MAP expr_type args =
      BaseT AddressT :: BaseT (UintT 256) ::
      (if has_gas then [BaseT (UintT 256)] else []) /\
    compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa = (vv, sb) ==>
    ?addr_op val_op gas_op sm success s3.
      lower_word_args cenv expr_type args sa =
        ([addr_op; val_op] ++ (if has_gas then [gas_op] else []), sm) /\
      (~has_gas ==> gas_op = Lit 0w) /\
      emit_op CALL [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
        sm = (success, s3) /\
      emit_void ASSERT [success] s3 = ((), sb)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_call, compile_call_def] >>
  `LENGTH args = if has_gas then 3 else 2` by
    (`LENGTH (MAP expr_type args) = if has_gas then 3 else 2` by
       (asm_rewrite_tac[] >> Cases_on `has_gas` >> simp[]) >>
     fs[]) >>
  `?a v gs. args = a::v::gs /\ LENGTH gs = (if has_gas then 1 else 0)` by
    (Cases_on `has_gas` >> gvs[LENGTH_EQ_NUM_compute]) >>
  gvs[] >>
  `gs = [] \/ ?g. gs = [g]` by
    (Cases_on `gs` >> gvs[] >> Cases_on `t` >> gvs[AllCaseEqs()]) >>
  gvs[lower_word_args_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  Cases_on `has_gas` >> gvs[]
QED

Theorem send_tail_shape:
  emit_op CALL ops sm = (success, s3) /\ emit_void ASSERT [success] s3 = (u, sb) ==>
  ?out. success = Var out /\ out = STRING #"%" (toString sm.cs_next_var) /\
    sb.cs_blocks = sm.cs_blocks /\ sb.cs_current_bb = sm.cs_current_bb /\
    sb.cs_next_var = sm.cs_next_var + 1 /\
    sb.cs_current_insts = sm.cs_current_insts ++
      [mk_inst sm.cs_next_id CALL ops [out];
       mk_inst (sm.cs_next_id + 1) ASSERT [Var out] []] /\
    cs_extends sm sb
Proof
  simp[emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

(* ===== The source side ===== *)

Theorem eval_expr_send_cases:
  !cx ann has_gas args dflt es res es'.
    LENGTH args = (if has_gas then 3 else 2) /\
    (do r <- eval_expr cx (Call ann (Send has_gas) args dflt);
        read_result cx r od) es = (res, es') ==>
    (?exc. eval_exprs cx args es = (INR exc, es') /\ res = INR exc) \/
    ?vs es1. eval_exprs cx args es = (INL vs, es1) /\
             (do tv <- eval_send cx has_gas vs; read_result cx tv od) es1 =
               (res, es')
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx args es` >>
  rename1 `eval_exprs cx args es = (rr, es1)` >>
  Cases_on `rr` >> simp[]
QED

Theorem eval_send_value:
  !cx has_gas vs st tv st'.
    eval_send cx has_gas vs st = (INL tv, st') ==> ?v. tv = Value v
Proof
  Cases_on `vs` >- simp[eval_send_def, raise_def] >>
  Cases_on `t` >- simp[eval_send_def, raise_def] >>
  simp[eval_send_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, lift_option_type_def, check_def,
       get_accounts_def, update_accounts_def, get_transient_storage_def,
       lift_option_def, update_transient_def, append_logs_def,
       vyperCallOutcomeTheory.take_call_outcome_def,
       vyperCallOutcomeTheory.adopt_call_outcome_def, LET_THM, UNCURRY,
       COND_RATOR, option_CASE_rator, prod_CASE_rator, sum_CASE_rator] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

(* Reading send's result: send returns a value, which reads as itself. *)
Theorem eval_send_read:
  !cx has_gas vs st res st'.
    (do tv <- eval_send cx has_gas vs; read_result cx tv od) st =
      (res, st') ==>
    ?r. eval_send cx has_gas vs st = (r, st') /\
        (!v. r = INL (Value v) ==> res = INL v) /\
        (!exc. r = INR exc ==> res = INR exc)
Proof
  rpt gen_tac >>
  Cases_on `eval_send cx has_gas vs st` >>
  rename1 `eval_send _ _ _ _ = (rr, st1)` >>
  Cases_on `rr` >> simp[bind_def] >> strip_tac >> gvs[] >>
  drule eval_send_value >> strip_tac >> gvs[read_result_def, return_def]
QED

Theorem eval_expr_send_value:
  !cx ann has_gas args dflt es tv es'.
    eval_expr cx (Call ann (Send has_gas) args dflt) es = (INL tv, es') ==>
    ?v. tv = Value v
Proof
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `eval_exprs cx args es` >>
  rename1 `eval_exprs cx args es = (rr, es1)` >>
  Cases_on `rr` >> rw[] >> drule eval_send_value >> simp[]
QED

(* take_call_outcome raises "call outcome accounts" only for a successful
   outcome whose accounts are not runtime well typed: not one of the
   remaining outcomes, by outcomes_accounts_typed, nor a computed
   precompile's, which keeps the current accounts. *)
Theorem take_call_outcome_typed:
  !target cd vo st.
    outcomes_accounts_typed st.outcomes /\
    accounts_runtime_well_typed st.accounts ==>
    FST (take_call_outcome target cd vo st) <>
      INR (Error (RuntimeError "call outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  simp[take_call_outcome_def] >> Cases_on `st.outcomes` >> simp[] >>
  pairarg_tac >> simp[] >> rw[] >>
  gvs[outcomes_accounts_typed_def, take_outcome_def] >>
  BasicProvers.every_case_tac >>
  gvs[failed_outcome_def, call_outcome_request_def]
QED

Theorem eval_send_outcome_typed:
  !cx has_gas to_v amount_v gas_vs es res es' os a n.
    es.outcomes = SOME os /\ outcomes_accounts_typed es.outcomes /\
    accounts_runtime_well_typed es.accounts /\
    dest_AddressV to_v = SOME a /\ dest_NumV amount_v = SOME n /\
    LENGTH gas_vs = (if has_gas then 1 else 0) /\
    eval_send cx has_gas (to_v :: amount_v :: gas_vs) es = (res, es') ==>
    res <> INR (Error (RuntimeError "call outcome accounts"))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_send _ _ _ _ = _` mp_tac >>
  simp[eval_send_def, bind_def, ignore_bind_def, type_check_def, assert_def,
       check_def, lift_option_type_def, vyperStateTheory.return_def] >>
  Cases_on `take_call_outcome a [] (SOME n) es` >>
  qmatch_asmsub_rename_tac `take_call_outcome _ _ _ _ = (tr, es1)` >>
  drule_all take_call_outcome_typed >>
  disch_then (qspecl_then [`a`, `[]`, `SOME n`] mp_tac) >>
  Cases_on `tr` >> simp[]
  >- (rename1 `INL x` >> PairCases_on `x` >> simp[] >> rpt strip_tac >>
      Cases_on `x1.co_success` >>
      gvs[bind_def, ignore_bind_def, assert_def, raise_def,
          adopt_call_outcome_equation, vyperStateTheory.return_def]) >>
  rw[] >> gvs[]
QED

Theorem address_typed_dest:
  !v. value_has_type (BaseTV AddressT) v ==>
      dest_AddressV v = SOME (w2w (typed_val_to_w256 (BaseTV AddressT) v))
Proof
  Cases >> simp[value_has_type_def, dest_AddressV_def] >>
  rw[address_word_w2w]
QED

Theorem uint256_typed_dest:
  !v. value_has_type (BaseTV (UintT 256)) v ==>
      dest_NumV v = SOME (w2n (typed_val_to_w256 (BaseTV (UintT 256)) v))
Proof
  Cases >> simp[value_has_type_def, dest_NumV_def, typed_val_to_w256_def,
                val_to_w256_def] >>
  strip_tac >> conj_tac >- intLib.COOPER_TAC >>
  `?m. i = &m` by (qexists_tac `Num i` >> intLib.COOPER_TAC) >>
  gvs[integer_wordTheory.i2w_pos, wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
      wordsTheory.dimword_def]
QED

(* ===== The operands ===== *)

Theorem expr_sim_pre_send_arg:
  !cenv cx env ann has_gas args dflt e es es'.
    expr_sim_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_sim_pre cenv cx env e es'
Proof
  rw[expr_sim_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def] >>
  drule_all well_typed_exprs_mem >> drule_all byte_widths_exprs_mem >>
  drule_all alloc_limits_exprs_mem >> gvs[]
QED

Theorem send_pre_types:
  expr_sim_pre cenv cx env (Call ann (Send has_gas) args dflt) es ==>
  ann = NoneT /\
  MAP expr_type args =
    [BaseT AddressT; BaseT (UintT 256)] ++
    (if has_gas then [BaseT (UintT 256)] else []) /\
  LENGTH args = (if has_gas then 3 else 2) /\
  EVERY (\e. is_word_type (expr_type e)) args
Proof
  simp[expr_sim_pre_def, well_typed_expr_def] >> strip_tac >>
  `LENGTH (MAP expr_type args) = (if has_gas then 3 else 2)` by
    (asm_rewrite_tac[] >> Cases_on `has_gas` >> simp[]) >>
  fs[] >> simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM (expr_type e) (MAP expr_type args)` by (simp[MEM_MAP] >> metis_tac[]) >>
  pop_assum mp_tac >> asm_rewrite_tac[] >>
  Cases_on `has_gas` >> rw[] >> simp[is_word_type_def]
QED

(* The invariant of typed_args_ready holds after all the operands. *)
Theorem typed_args_ready_inv:
  !args es vs es'.
    typed_args_ready ctx func cenv cx arg_ty Inv args /\ Inv es /\
    eval_exprs cx args es = (INL vs, es') ==>
    Inv es'
Proof
  Induct >- simp[eval_exprs_nil] >>
  rpt gen_tac >> strip_tac >>
  drule_all typed_args_cons_cases >> strip_tac >> gvs[] >>
  Cases_on `rr` >> gvs[] >>
  first_x_assum irule >>
  metis_tac[typed_args_ready_tail]
QED

(* ===== The CALL and the ASSERT ===== *)

Theorem expr_post_none_intro:
  expr_type e = NoneT /\ stmt_state_rel func cenv cx es' s /\
  wb_frame cenv es sa s0 s ==>
  expr_post func cenv cx e es sa sb s0 es' NoneV (Lit 0w) s
Proof
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def, wb_frame_def,
       eval_operand_def, vyperValueTheory.evaluate_type_def,
       is_word_type_def, val_in_memory_def, val_wf_def, val_footprint_def,
       type_memory_size_def] >>
  metis_tac[]
QED

(* The ASSERT of the success word the CALL just bound. *)
Theorem send_assert_ok[local]:
  !id x w s.
    w <> 0w ==>
    step_inst_base (mk_inst id ASSERT [Var x] []) (update_var x w s) =
      OK (update_var x w s)
Proof
  rpt strip_tac >> irule assert_true_correct >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem send_assert_fail[local]:
  !id x s.
    step_inst_base (mk_inst id ASSERT [Var x] []) (update_var x 0w s) =
      Abort Revert_abort (revert_state (set_returndata [] (update_var x 0w s)))
Proof
  rpt strip_tac >> irule assert_false_correct >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem send_tail_frag:
  emit_op CALL [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
    sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (u, sb) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  stmt_state_rel func cenv cx es1 t /\ wb_frame cenv es sa s0 t /\
  outcomes_accounts_typed es1.outcomes /\
  accounts_runtime_well_typed es1.accounts /\
  IS_SOME (eval_operand gas_op t) /\
  eval_operand addr_op t = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand val_op t = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs);
      read_result cx tv od) es1 = (res, es') /\
  expr_type e = NoneT ==>
  frag_exec ctx sm sb (\s. s = t)
    (\s. ?v. res = INL v /\
             expr_post func cenv cx e es sa sb s0 es' v (Lit 0w) s)
    (expr_exit res)
Proof
  strip_tac >> drule_all send_tail_shape >> strip_tac >>
  qpat_x_assum `bind _ _ _ = _` (strip_assume_tac o MATCH_MP eval_send_read) >>
  `~not_fresh_at sm out` by gvs[not_fresh_at_def] >>
  `emitted_insts sm sb =
     [mk_inst sm.cs_next_id CALL
        [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out];
      mk_inst (sm.cs_next_id + 1) ASSERT [Var out] []]` by
    fs[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  `state_rel func cenv cx es1 t` by fs[stmt_state_rel_def] >>
  qspecl_then [`func`, `cenv`, `cx`, `es1`, `t`,
               `mk_inst sm.cs_next_id CALL
                  [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out]`,
               `gas_op`, `addr_op`, `val_op`, `out`, `has_gas`, `to_v`,
               `amount_v`, `gas_vs`, `aw`, `vw`, `r`, `es'`]
    mp_tac send_call_oracle_step >>
  impl_tac >- simp[mk_inst_def] >>
  `es1.outcomes = SOME t.vs_outcomes` by fs[state_rel_def] >>
  `r <> INR (Error (RuntimeError "call outcome accounts"))` by
    (drule_all eval_send_outcome_typed >> simp[]) >>
  simp[] >> strip_tac >>
  `s'.vs_allocas = t.vs_allocas /\ s'.vs_alloca_next = t.vs_alloca_next /\
   s'.vs_memory = t.vs_memory /\ s'.vs_vars = t.vs_vars` by
    (qpat_x_assum `s' = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
  irule frag_exec_run_inst_seq >> rpt conj_tac >>
  TRY (fs[rich_listTheory.IS_PREFIX_APPEND, mk_inst_def, is_terminator_def] >>
       NO_TAC) >>
  rpt strip_tac >>
  TRY (gvs[run_inst_seq_def, send_assert_fail, expr_exit_def] >> NO_TAC) >>
  gvs[run_inst_seq_def, send_assert_ok] >>
  irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (irule stmt_state_rel_update_var >> conj_tac
      >- (irule fresh_not_local_ptr >> qexists_tac `sm` >> fs[]) >>
      `es'.scopes = es1.scopes /\ es'.immutables = es1.immutables` by
        (drule eval_send_preserves_non_accounts >> simp[]) >>
      `immutable_alloca_sep func cenv cx es' s'` by
        (irule immutable_alloca_sep_fields >> qexistsl_tac [`s`, `es1`] >>
         gvs[stmt_state_rel_def] >>
         rpt strip_tac >> qexists_tac `id` >>
         gvs[local_region_def, lookup_var_def]) >>
      irule stmt_state_rel_allocas_frame >> simp[] >>
      qexistsl_tac [`es1`, `s`] >> simp[]) >>
  irule wb_frame_readonly_tail >>
  qexists_tac `sm` >>
  qpat_assum `wb_frame _ _ _ _ _` (irule_at Any) >>
  simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[not_fresh_at_def] >> metis_tac[]
QED

(* ===== send ===== *)

Theorem lower_value_send:
  lower_value compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa =
    (op, sb) ==>
  op = Lit 0w /\
  compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa =
    (StackValue ann (Lit 0w), sb)
Proof
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa` >>
  drule compile_expr_send_stack >>
  simp[unwrap_value_def, comp_return_def] >> rw[] >> gvs[]
QED

Theorem send_expr_sim:
  expr_sim_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  EVERY (expr_sim_ok cenv) args ==>
  expr_sim ctx func cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  strip_tac >> drule send_pre_types >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_sim_pre_def] >>
  `EVERY (\e. is_word_type (expr_type e) /\ expr_sim_ok cenv e) args` by
    gvs[EVERY_MEM] >>
  `!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
         expr_sim_pre cenv cx env e s` by
    metis_tac[expr_sim_pre_send_arg] >>
  drule_all typed_stack_args_ready >>
  disch_then (qspecl_then [`func`, `ctx`, `expr_type`] strip_assume_tac) >>
  rewrite_tac[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  reverse (Cases_on `stmt_state_rel func cenv cx es s0`)
  >- (`(\s. s = s0 /\ stmt_state_rel func cenv cx es s) = (\s. F)` by
        (simp[FUN_EQ_THM] >> metis_tac[]) >>
      simp[] >> irule frag_exec_false_pre) >>
  drule lower_value_send >> strip_tac >> gvs[] >>
  drule_all compile_expr_send >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  drule_all send_tail_shape >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  drule_all eval_expr_send_cases >> strip_tac
  >- (gvs[] >> drule_all lower_typed_args_sim >>
      disch_then (qspec_then `s0` mp_tac) >> simp[wb_args_exit_def] >>
      strip_tac >> irule frag_exec_exit_prefix >>
      goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `expr_sim_inv cenv cx env es1` by metis_tac[typed_args_ready_inv] >>
  `LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) args vs` by
    (drule_at (Pat `eval_exprs _ _ _ = _`) stack_args_values_typed >>
     disch_then (qspecl_then [`cenv`, `env`] mp_tac) >>
     impl_tac >- (rpt strip_tac >> fs[EVERY_MEM] >> metis_tac[]) >>
     simp[]) >>
  drule_all lower_typed_args_sim >> disch_then (qspec_then `s0` mp_tac) >>
  simp[wb_args_exit_def] >> disch_then (mp_then Any irule wb_frag_then) >>
  simp[] >> qx_gen_tac `t` >> strip_tac >> gvs[typed_args_post_def] >>
  `LENGTH vs = LENGTH args` by metis_tac[LIST_REL_LENGTH] >>
  `?to_v amount_v gas_vs. vs = to_v :: amount_v :: gas_vs /\
     LENGTH gas_vs = (if has_gas then 1 else 0)` by
    (Cases_on `has_gas` >> gvs[LENGTH_EQ_NUM_compute]) >>
  `?a v gs. args = a::v::gs` by
    (Cases_on `has_gas` >> gvs[LENGTH_EQ_NUM_compute]) >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  `accounts_runtime_well_typed es1.accounts` by
    fs[expr_sim_inv_def,
       vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  `outcomes_accounts_typed es1.outcomes` by gvs[expr_sim_inv_def] >>
  irule send_tail_frag >> simp[expr_type_def] >>
  qpat_assum `bind (eval_send _ _ _) _ _ = _` (irule_at Any) >>
  qpat_assum `emit_op _ _ _ = _` (irule_at Any) >>
  qpat_assum `emit_void _ _ _ = _` (irule_at Any) >>
  qpat_assum `eval_operand addr_op _ = _` (irule_at Any) >>
  qpat_assum `eval_operand val_op _ = _` (irule_at Any) >>
  rpt conj_tac >>
  FIRST [first_assum ACCEPT_TAC,
         irule address_typed_dest >> first_assum ACCEPT_TAC,
         irule uint256_typed_dest >> first_assum ACCEPT_TAC,
         Cases_on `has_gas` >> gvs[eval_operand_def] >> NO_TAC,
         fs[] >> NO_TAC]
QED

(* TOP-LEVEL *)
Theorem compile_send_case_sim:
  !cenv ann has_gas args dflt.
    expr_sim_below cenv (expr_size (Call ann (Send has_gas) args dflt)) ==>
    expr_vv_ok cenv (Call ann (Send has_gas) args dflt)
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (expr_sim_ok cenv) args` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `expr_ok cenv e` suffices_by simp[expr_ok_def] >>
     irule expr_sim_below_mem >> qexists_tac `args` >> simp[] >>
     irule expr_sim_below_mono >> goal_assum (drule_at Any) >>
     simp[expr_size_def]) >>
  rewrite_tac[expr_vv_ok_def] >> rpt strip_tac >>
  irule expr_vv_sim_stack >> rpt conj_tac
  >- (gen_tac >>
      Cases_on `compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa` >>
      drule compile_expr_send_stack >> simp[])
  >- metis_tac[eval_expr_send_value] >>
  irule send_expr_sim >> simp[] >> metis_tac[]
QED
