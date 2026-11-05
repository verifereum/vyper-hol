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
 *   compile_send_case — send's expr_sim_case and expr_vv_case from its
 *     operands' exprs_case, for compile_expr_sim and the body simulation;
 *     compile_send_case_sim, expr_vv_ok of send, follows
 *
 * Helpers:
 *   compile_expr_call, compile_expr_send, compile_expr_send_stack — the
 *     compile side
 *   eval_expr_send_action, eval_send_value, eval_send_read,
 *     eval_expr_send_value,
 *     take_call_outcome_typed,
 *     eval_send_outcome_typed, address_typed_dest, uint256_typed_dest — the
 *     source side
 *   expr_body_pre_send_arg, send_pre_types, typed_args_ready_inv — the
 *     operands
 *   send_tail_shape, send_tail_path, expr_post_none_intro — the CALL and
 *     the ASSERT, a run that reads no GAS
 *   eval_send_gas_obs, eval_send_read_gas_obs — send reads no gas
 *     observation
 *   send_args_summary, send_exempt_cert — the operands' counted outcome
 *     followed by the tail
 *)

Theory exprSimSend
Ancestors
  exprSimSource
  exprSimHypsDefs
  exprSimDefs exprSimStack
  gasSummary gasSummaryCompose gasOutcome gasExemptCert
  fragGasMode fragGasPath fragGasSeq fragGasSeqAbort
  loweringPosts
  allocLimits
  list pair vyperMisc fragExec loweringSlice  exprSimHyps exprSimWordArgs
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
  Cases_on `x` >> gvs[failed_outcome_def] >>
  Cases_on `computed_precompile (call_outcome_request target cd vo st)` >>
  gvs[AllCaseEqs(), failed_outcome_def, call_outcome_request_def]
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

Theorem expr_body_pre_send_arg:
  !cenv cx env ann has_gas args dflt e es es'.
    expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rw[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def,
     supportedExprTraverseTheory.supported_expr_exists_def,
     supportedExprTraverseTheory.supported_exprs_exists_every,
     listTheory.EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED

Theorem send_pre_types:
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es ==>
  ann = NoneT /\
  MAP expr_type args =
    [BaseT AddressT; BaseT (UintT 256)] ++
    (if has_gas then [BaseT (UintT 256)] else []) /\
  LENGTH args = (if has_gas then 3 else 2) /\
  EVERY (\e. is_word_type (expr_type e)) args
Proof
  simp[expr_body_pre_def, well_typed_expr_def] >> strip_tac >>
  `LENGTH (MAP expr_type args) = (if has_gas then 3 else 2)` by
    (asm_rewrite_tac[] >> Cases_on `has_gas` >> simp[]) >>
  fs[] >> simp[EVERY_MEM] >> rpt strip_tac >>
  `MEM (expr_type e) (MAP expr_type args)` by (simp[MEM_MAP] >> metis_tac[]) >>
  pop_assum mp_tac >> asm_rewrite_tac[] >>
  Cases_on `has_gas` >> rw[] >> simp[is_word_type_def]
QED

(* The invariant of typed_args_ready holds after all the operands. *)
Theorem typed_args_ready_inv:
  !args es vs es' ctx.
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
  expr_type e = NoneT /\ stmt_state_rel ctx func cenv cx es' s /\
  wb_frame cenv es sa s0 s ==>
  expr_post ctx func cenv cx e es sa sb s0 es' NoneV (Lit 0w) s
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

Theorem send_call_read_step[local]:
  stmt_state_rel ctx func cenv cx es1 t /\
  outcomes_accounts_typed es1.outcomes /\
  accounts_runtime_well_typed es1.accounts /\
  IS_SOME (eval_operand gas_op t) /\
  eval_operand addr_op t = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand val_op t = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs);
      read_result cx tv od) es1 = (res, es') ==>
  ?t'. t' = t with <| vs_outcomes := t'.vs_outcomes;
                       vs_requests := t'.vs_requests;
                       vs_accounts := t'.vs_accounts;
                       vs_transient := t'.vs_transient;
                       vs_logs := t'.vs_logs;
                       vs_pending_deletions := t'.vs_pending_deletions;
                       vs_returndata := t'.vs_returndata |> /\
    ((res = INL NoneV /\
      step_inst_base (mk_inst id CALL
        [gas_op;addr_op;val_op;Lit 0w;Lit 0w;Lit 0w;Lit 0w] [out]) t =
        OK (update_var out 1w t') /\ state_rel func cenv cx es' t') \/
     (res = INR (Error (RuntimeError "send failed")) /\
      step_inst_base (mk_inst id CALL
        [gas_op;addr_op;val_op;Lit 0w;Lit 0w;Lit 0w;Lit 0w] [out]) t =
        OK (update_var out 0w t')))
Proof
  strip_tac >> drule eval_send_read >> strip_tac >>
  `state_rel func cenv cx es1 t` by fs[stmt_state_rel_def] >>
  `es1.outcomes = SOME t.vs_outcomes` by fs[state_rel_def] >>
  `r <> INR (Error (RuntimeError "call outcome accounts"))` by
    (drule_all eval_send_outcome_typed >> simp[]) >>
  drule_all (send_call_oracle_step |> SPEC_ALL |>
    Q.INST [`inst` |-> `mk_inst id CALL
      [gas_op;addr_op;val_op;Lit 0w;Lit 0w;Lit 0w;Lit 0w] [out]`] |>
    SRULE [mk_inst_def]) >>
  disch_then (qspecl_then [`out`, `id`] strip_assume_tac) >>
  gvs[mk_inst_def] >> metis_tac[]
QED

(* ===== The counted tail ===== *)

(* send reads no gas observation: its run is the same under any reading. *)
Theorem take_call_outcome_gas_obs[local]:
  !target cd vo st g.
    take_call_outcome target cd vo (st with gas_obs := g) =
      (FST (take_call_outcome target cd vo st),
       SND (take_call_outcome target cd vo st) with gas_obs := g) /\
    (SND (take_call_outcome target cd vo st)).gas_obs = st.gas_obs
Proof
  rpt gen_tac >> simp[take_call_outcome_def, call_outcome_request_def] >>
  Cases_on `st.outcomes` >> simp[LET_THM, UNCURRY] >> rw[]
QED

Theorem adopt_call_outcome_gas_obs[local]:
  !rq oc st g.
    adopt_call_outcome rq oc (st with gas_obs := g) =
      (FST (adopt_call_outcome rq oc st),
       SND (adopt_call_outcome rq oc st) with gas_obs := g) /\
    (SND (adopt_call_outcome rq oc st)).gas_obs = st.gas_obs
Proof
  simp[adopt_call_outcome_def, return_def, LET_THM, UNCURRY]
QED

Theorem eval_send_gas_obs:
  !cx has_gas vs st g.
    eval_send cx has_gas vs (st with gas_obs := g) =
      (FST (eval_send cx has_gas vs st),
       SND (eval_send cx has_gas vs st) with gas_obs := g) /\
    (SND (eval_send cx has_gas vs st)).gas_obs = st.gas_obs
Proof
  rpt gen_tac >>
  Cases_on `vs` >- simp[eval_send_def, raise_def] >>
  Cases_on `t` >- simp[eval_send_def, raise_def] >>
  rename1 `eval_send cx has_gas (to_v::amount_v::gas_vs)` >>
  simp[eval_send_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, lift_option_type_def] >>
  IF_CASES_TAC >> simp[raise_def, return_def] >>
  Cases_on `dest_AddressV to_v` >> simp[raise_def, return_def] >>
  Cases_on `dest_NumV amount_v` >> simp[raise_def, return_def] >>
  rename1 `dest_AddressV to_v = SOME addr` >>
  rename1 `dest_NumV amount_v = SOME amt` >>
  Cases_on `st.outcomes` >> simp[bind_def, ignore_bind_def]
  >- (simp[get_accounts_def, get_transient_storage_def, lift_option_def,
           check_def, assert_def, update_accounts_def, update_transient_def,
           append_logs_def, return_def, raise_def] >>
      Cases_on `run_ext_call cx.txn.target addr [] (SOME amt)
                  (forwarded_gas 0 (ext_call_kwarg EKGas [EKGas] gas_vs))
                  st.accounts st.tStorage (vyper_to_tx_params cx.txn)` >>
      simp[raise_def, return_def] >>
      rename1 `_ = SOME rr` >> PairCases_on `rr` >> simp[] >>
      IF_CASES_TAC >> simp[]) >>
  qspecl_then [`addr`, `[]`, `SOME amt`, `st`, `g`] mp_tac
    take_call_outcome_gas_obs >>
  Cases_on `take_call_outcome addr [] (SOME amt) st` >>
  rename1 `_ = (q, st1)` >> reverse (Cases_on `q`) >- simp[] >>
  rename1 `INL rqoc` >> PairCases_on `rqoc` >> simp[] >> strip_tac >>
  fs[check_def, assert_def, raise_def, return_def, bind_def, ignore_bind_def] >>
  IF_CASES_TAC >> fs[] >>
  qspecl_then [`rqoc0`, `rqoc1`, `st1`, `g`] mp_tac
    adopt_call_outcome_gas_obs >>
  Cases_on `adopt_call_outcome rqoc0 rqoc1 st1` >> rename1 `_ = (q2, _)` >>
  Cases_on `q2` >> simp[]
QED

Theorem eval_send_read_gas_obs:
  !cx has_gas vs st res st'.
    (do tv <- eval_send cx has_gas vs; read_result cx tv od) st =
      (res, st') ==>
    st'.gas_obs = st.gas_obs /\
    !g. (do tv <- eval_send cx has_gas vs; read_result cx tv od)
          (st with gas_obs := g) = (res, st' with gas_obs := g)
Proof
  rpt gen_tac >> strip_tac >> drule eval_send_read >> strip_tac >>
  qspecl_then [`cx`, `has_gas`, `vs`, `st`] assume_tac eval_send_gas_obs >>
  gvs[] >> Cases_on `r`
  >- (drule eval_send_value >> strip_tac >>
      gvs[bind_def, read_result_def, return_def]) >>
  gvs[bind_def]
QED

(* The CALL and the ASSERT read no GAS: their run is a zero-count path. *)
Theorem send_tail_path:
  emit_op CALL [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
    sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (u, sb) /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  stmt_state_rel ctx func cenv cx es1 t /\ wb_frame cenv es sa s0 t /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  outcomes_accounts_typed es1.outcomes /\
  accounts_runtime_well_typed es1.accounts /\
  IS_SOME (eval_operand gas_op t) /\
  eval_operand addr_op t = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand val_op t = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs);
      read_result cx tv od) es1 = (res, es') /\
  expr_type e = NoneT ==>
  ?r. gas_marked_path F ctx func t 0 r /\
      ((?t'. r = OK t' /\
             (?v. res = INL v /\
                  expr_post ctx func cenv cx e es sa sb s0 es' v (Lit 0w) t') /\
             t'.vs_current_bb = sb.cs_current_bb /\
             t'.vs_inst_idx = LENGTH sb.cs_current_insts) \/
       (exit_result r /\ expr_exit res r))
Proof
  strip_tac >> drule_all send_tail_shape >> strip_tac >>
  `~not_fresh_at sm out` by gvs[not_fresh_at_def] >>
  qabbrev_tac `code = [mk_inst sm.cs_next_id CALL
     [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out];
     mk_inst (sm.cs_next_id + 1) ASSERT [Var out] []]` >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) code /\
   FILTER (\i. i.inst_opcode = GAS) code = [] /\ LENGTH code = 2` by
    simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX code (DROP t.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `fn_has_code sm sb func` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >> qexists_tac `bb` >>
     qpat_x_assum `isPREFIX _ bb.bb_instructions` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     gvs[] >> qexists_tac `l` >>
     REWRITE_TAC[GSYM listTheory.APPEND_ASSOC,
                 rich_listTheory.DROP_LENGTH_APPEND]) >>
  drule_all send_call_read_step >>
  disch_then (qspecl_then [`out`, `sm.cs_next_id`] strip_assume_tac) >>
  rename1 `s' = t with <| vs_outcomes := _; vs_requests := _;
    vs_accounts := _; vs_transient := _; vs_logs := _;
    vs_pending_deletions := _; vs_returndata := _ |>` >>
  `s'.vs_allocas = t.vs_allocas /\ s'.vs_alloca_next = t.vs_alloca_next /\
   s'.vs_memory = t.vs_memory /\ s'.vs_vars = t.vs_vars /\
   s'.vs_labels = t.vs_labels` by
    (qpat_x_assum `s' = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[])
  >- (`run_inst_seq code t = OK (update_var out 1w s')` by
        asm_simp_tac (srw_ss()) [Abbr `code`, run_inst_seq_def,
                                 send_assert_ok] >>
      qspecl_then [`code`, `t`, `update_var out 1w s'`, `ctx`, `func`, `bb`]
        mp_tac tuple_run_inst_seq_gas_path >>
      (impl_tac >- fs[EVERY_MEM]) >>
      qpat_assum `FILTER _ code = []` (fn th => REWRITE_TAC[th, LENGTH]) >>
      strip_tac >>
      `LENGTH sb.cs_current_insts = t.vs_inst_idx + LENGTH code` by
        (qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
         qpat_x_assum `t.vs_inst_idx = _` SUBST1_TAC >> simp[]) >>
      qexists_tac `OK (update_var out 1w s' with
                       vs_inst_idx := LENGTH sb.cs_current_insts)` >>
      conj_tac
      >- (pop_assum SUBST1_TAC >> simp[gas_marked_path_def] >>
          first_assum ACCEPT_TAC) >>
      disj1_tac >> simp[] >>
      `(update_var out 1w s').vs_current_bb = sb.cs_current_bb` by
        (qpat_x_assum `s' = _` SUBST1_TAC >> fs[update_var_def]) >>
      pop_assum (fn th => simp[th]) >>
      qpat_assum `res = _` (fn th => simp[th]) >>
      reverse conj_tac
      >- (qpat_x_assum `s' = _` SUBST1_TAC >> fs[]) >>
      irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx] >>
      reverse conj_tac
      >- (irule stmt_state_rel_update_var >> conj_tac
          >- (irule fresh_not_local_ptr >> qexists_tac `sm` >> metis_tac[]) >>
          `es'.scopes = es1.scopes /\ es'.immutables = es1.immutables` by
            (drule eval_send_read >> strip_tac >>
             drule eval_send_preserves_non_accounts >> simp[]) >>
          `immutable_alloca_sep func cenv cx es' s'` by
            (irule immutable_alloca_sep_fields >> qexistsl_tac [`t`, `es1`] >>
             gvs[stmt_state_rel_def] >>
             rpt strip_tac >> qexists_tac `id` >>
             gvs[local_region_def, lookup_var_def]) >>
          `immutable_base_zero cenv s'` by
            (irule immutable_base_zero_frame >> qexists_tac `t` >>
             fs[stmt_state_rel_def, lookup_var_def]) >>
          irule stmt_state_rel_allocas_frame >> simp[] >>
          qexistsl_tac [`es1`, `t`] >> simp[] >>
          qpat_x_assum `s' = _`
            (fn th => once_rewrite_tac[th]) >> simp[]) >>
      irule wb_frame_readonly_tail >>
      qexists_tac `sm` >>
      qpat_assum `wb_frame _ _ _ _ _` (irule_at Any) >>
      simp[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rw[] >> gvs[not_fresh_at_def] >> metis_tac[]) >>
  `run_inst_seq code t =
     Abort Revert_abort (revert_state (set_returndata [] (update_var out 0w s')))` by
    asm_simp_tac (srw_ss()) [Abbr `code`, run_inst_seq_def, send_assert_fail] >>
  drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_abort_zero_path >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[exit_result_def, expr_exit_def]
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

Theorem eval_expr_send_action:
  !cx ann has_gas args dflt.
    LENGTH args = (if has_gas then 3 else 2) ==>
    bind (eval_expr cx (Call ann (Send has_gas) args dflt)) (read_result cx) =
    bind (eval_exprs cx args)
      (\vs. do tv <- eval_send cx has_gas vs; read_result cx tv od)
Proof
  rpt strip_tac >> simp[FUN_EQ_THM] >> qx_gen_tac `st` >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def] >>
  Cases_on `eval_exprs cx args st` >> rename1 `(rr, _)` >>
  Cases_on `rr` >> simp[]
QED

Theorem send_exempt_cert:
  LENGTH args = (if has_gas then 3 else 2) /\
  gas_exempt_cert memory tops p
    (ignore_bind (eval_exprs cx args) (return ())) start marks out endpoint ==>
  gas_exempt_cert memory tops p
    (ignore_bind
      (bind (eval_expr cx (Call ann (Send has_gas) args dflt)) (read_result cx))
      (return ())) start marks out endpoint
Proof
  strip_tac >> drule eval_expr_send_action >>
  disch_then (qspecl_then [`cx`, `ann`, `dflt`] SUBST1_TAC) >>
  PairCases_on `p` >> PairCases_on `start` >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  qmatch_goalsub_abbrev_tac `ignore_bind (bind _ k) _` >>
  `ignore_bind (bind (eval_exprs cx args) k) (return ()) =
   bind (eval_exprs cx args) (\vs. ignore_bind (k vs) (return ()))` by
    simp[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_values >> simp[]
QED

(* After the operands' counted run, the send tail reads no GAS and its
   source part reads no observation, so the whole action keeps the operands'
   marks. *)
Theorem send_args_summary:
  gas_summary_at F (ctx,func) marks (eval_exprs cx args) (es,s0)
    (\rr ee t. ?vs. rr = INL vs /\
       typed_args_post ctx func cenv cx es sa s0 ee args
         ([addr_op; val_op] ++ (if has_gas then [gas_op] else [])) vs t /\
       t.vs_current_bb = sm.cs_current_bb /\
       t.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\rr ee r. wb_args_exit rr r) /\
  (~has_gas ==> gas_op = Lit 0w) /\
  MAP expr_type args =
    [BaseT AddressT; BaseT (UintT 256)] ++
    (if has_gas then [BaseT (UintT 256)] else []) /\
  LENGTH args = (if has_gas then 3 else 2) /\
  typed_args_ready ctx func cenv cx expr_type (expr_sim_inv cenv cx env) args /\
  expr_sim_inv cenv cx env es /\
  (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
         expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)) /\
  emit_op CALL [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
    sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (u, sb) /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
  gas_summary_at F (ctx,func) marks
    (bind (eval_expr cx (Call NoneT (Send has_gas) args dflt)) (read_result cx))
    (es,s0)
    (\res ee t. ?v. res = INL v /\
       expr_post ctx func cenv cx (Call NoneT (Send has_gas) args dflt)
         es sa sb s0 ee v (Lit 0w) t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  qpat_x_assum `LENGTH args = _` (fn th => assume_tac th >>
    rewrite_tac[MATCH_MP eval_expr_send_action th]) >>
  gvs[]
  >- suspend "normal" >>
  Cases_on `res` >> gvs[wb_args_exit_def] >> rename1 `INR exc` >>
  qexistsl_tac [`INR exc`, `es_end`, `r`] >>
  conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  simp[]
QED

Resume send_args_summary[normal]:
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qabbrev_tac `es_in = es with gas_obs := gas_explicit marks s0.vs_gas_readings` >>
  `eval_exprs cx args es_in = (INL vs, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
     simp[Abbr `es_in`]) >>
  `expr_sim_inv cenv cx env es_in` by simp[Abbr `es_in`] >>
  `expr_sim_inv cenv cx env (es_end with gas_obs := [])` by
    metis_tac[typed_args_ready_inv] >>
  `LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) args vs` by
    (drule_all stack_args_values_typed_body >> simp[]) >>
  gvs[typed_args_post_def] >>
  `?to_v amount_v gas_vs. vs = to_v :: amount_v :: gas_vs /\
     LENGTH gas_vs = (if has_gas then 1 else 0)` by
    (Cases_on `has_gas` >> gvs[LENGTH_EQ_NUM_compute]) >>
  `?a v gs. args = a::v::gs` by
    (Cases_on `has_gas` >> gvs[LENGTH_EQ_NUM_compute]) >>
  gvs[vyperValueTheory.evaluate_type_def] >>
  `accounts_runtime_well_typed es_end.accounts /\
   outcomes_accounts_typed es_end.outcomes` by
    fs[expr_sim_inv_def,
       vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  Cases_on `(do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs);
                read_result cx tv od) (es_end with gas_obs := [])` >>
  rename1 `_ = (res, fin)` >>
  drule eval_send_read_gas_obs >> strip_tac >>
  `?r. gas_marked_path F ctx func t 0 r /\
       ((?t'. r = OK t' /\
              (?w. res = INL w /\
                   expr_post ctx func cenv cx
                     (Call NoneT (Send has_gas) (a::v::gs) dflt)
                     es sa sb s0 fin w (Lit 0w) t') /\
              t'.vs_current_bb = sb.cs_current_bb /\
              t'.vs_inst_idx = LENGTH sb.cs_current_insts) \/
        (exit_result r /\ expr_exit res r))` by
    (irule send_tail_path >> simp[expr_type_def] >>
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
            fs[] >> NO_TAC]) >>
  pop_assum strip_assume_tac >>
  `!tail. (do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs);
              read_result cx tv od) (es_end with gas_obs := tail) =
          (res, fin with gas_obs := tail)` by
    (gen_tac >> qpat_x_assum `!g. _ = (res, _)` (qspec_then `tail` mp_tac) >>
     simp[]) >>
  `fin with gas_obs := [] = fin` by
    gvs[evaluation_state_component_equality] >>
  qexistsl_tac [`res`, `fin`, `r`] >>
  (conj_tac
   >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
              |> REWRITE_RULE [APPEND_NIL]) >>
       qexistsl_tac [`es_end`, `t`, `to_v :: amount_v :: gas_vs`] >>
       simp[gas_marked_exec_def] >> gvs[])) >>
  gvs[]
QED

Finalise send_args_summary

Theorem send_expr_sim:
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  (!arg_ty. typed_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args) ==>
  expr_sim ctx func cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  strip_tac >> drule send_pre_types >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
         expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)` by
    (rpt strip_tac >- metis_tac[expr_body_pre_send_arg] >>
     gvs[EVERY_MEM]) >>
  `wb_args_shape cenv expr_type args` by metis_tac[typed_stack_args_shape] >>
  qpat_x_assum `!arg_ty. _` (qspec_then `expr_type` assume_tac) >>
  rewrite_tac[expr_sim_def] >> rpt gen_tac >> strip_tac >>
  drule lower_value_send >> strip_tac >> gvs[] >>
  drule_all compile_expr_send >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  drule_all send_tail_shape >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  qspecl_then [`args`, `ctx`, `func`, `cenv`, `cx`, `expr_type`,
    `expr_sim_inv cenv cx env`, `es`, `sa`,
    `[addr_op; val_op] ++ (if has_gas then [gas_op] else [])`, `sm`, `s0`]
    mp_tac lower_typed_args_sim >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      irule send_args_summary >> simp[expr_type_def] >>
      conj_tac
      >- (qexistsl_tac [`addr_op`, `gas_op`, `s3`, `sm`, `success`, `val_op`] >>
          fs[]) >>
      qexists_tac `env` >> fs[] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >>
  metis_tac[send_exempt_cert]
QED

(* TOP-LEVEL *)
Theorem compile_send_case:
  !nocalls ctx func cenv cx ann has_gas args dflt.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx (Call ann (Send has_gas) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx (Call ann (Send has_gas) args dflt)
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_case nocalls ctx func cenv cx (Call ann (Send has_gas) args dflt)`
    suffices_by simp[expr_sim_case_of_vv] >>
  rewrite_tac[expr_vv_case_def] >> rpt strip_tac >>
  drule send_pre_types >> strip_tac >>
  irule expr_vv_sim_stack >> rpt conj_tac
  >- (gen_tac >>
      Cases_on `compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa` >>
      drule compile_expr_send_stack >> simp[])
  >- metis_tac[eval_expr_send_value] >>
  irule send_expr_sim >> qexists_tac `env` >> simp[] >> gen_tac >>
  irule typed_args_ready_of_case >> qexists_tac `nocalls` >> simp[] >>
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- metis_tac[expr_body_pre_send_arg]
  >- (rw[] >> gvs[int_calls_expr_def] >> metis_tac[int_calls_exprs_mem]) >>
  gvs[EVERY_MEM]
QED

Theorem compile_send_case_sim:
  !cenv ann has_gas args dflt.
    expr_sim_below cenv (expr_size (Call ann (Send has_gas) args dflt)) ==>
    expr_vv_ok cenv (Call ann (Send has_gas) args dflt)
Proof
  rpt strip_tac >> simp[expr_vv_ok_case] >> rpt gen_tac >>
  `exprs_case T ctx func cenv cx args` by
    (irule exprs_case_below >> irule expr_sim_below_mono >>
     goal_assum (drule_at Any) >> simp[expr_size_def]) >>
  metis_tac[compile_send_case]
QED
