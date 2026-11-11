(* Memory case of the body induction (bodyMemory's body_mem_mutual): send.

   exprSimSend's simulation on the memory-counted contract: the operands
   run memory-checked (bodyArgsMemory), then the CALL, whose argument and
   return ranges are empty, and the ASSERT of its success word, neither of
   which touches memory, allocates or reads GAS. *)
Theory bodyMemSend
Ancestors
  bodyMemoryPreds bodyArgsMemory exprSimSend exprSimMemoryStack
  exprSimMemDefs exprSimPrecompiles exprSimWordArgs exprSimHypsDefs
  gasContext gasSummary gasOutcome gasSummaryCompose gasExemptCert
  fragGasMode fragGasPath fragGasPathMem fragGasSeqMem fragGasSeqAbort
  fragExecMem allocaHistory allocaHistoryFragment instMemFrontier memSafeRun
  venomExecProofs venomInstProofs instIdxIndep
  exprSimSource exprSimDefs exprSimStack loweringPosts allocLimits
  list pair vyperMisc fragExec loweringSlice exprSimHyps
  exprSimOperators exprSimOperands exprSimAccounts
  extCallOracleStep exprCallbackContracts exprCallBounds exprLowering
  exprLoweringProps emitHelper compileEnv loweringStateRelDefs localPtrsProps valueEncoding
  vyperAST vyperInterpreter vyperCallOutcomeFrame vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeCallGraph vyperCallOutcome extCallOracle
  vyperRuntimeAccounts vyperTypeInvariants vyperEvalExprPreservesScopesDom
  venomExecSemantics venomInst venomState rich_list bodyUnopFragMemory
Libs
  pairLib

(* ===== The source side reads no gas observation ===== *)

Theorem take_call_outcome_gas_obs[local]:
  !target cd vo st g.
    take_call_outcome target cd vo (st with gas_obs := g) =
      (FST (take_call_outcome target cd vo st),
       SND (take_call_outcome target cd vo st) with gas_obs := g) /\
    (SND (take_call_outcome target cd vo st)).gas_obs = st.gas_obs
Proof
  rpt gen_tac >> simp[take_call_outcome_def, take_request_outcome_def, call_outcome_request_def] >>
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

(* frame_call_value reads nothing from the state and changes nothing. *)
Theorem frame_call_value_pure[local]:
  !cx v. ?r. !st. frame_call_value cx v st = (r, st)
Proof
  rw[frame_call_value_def, check_def, assert_def, ignore_bind_def, bind_def,
     return_def, raise_def] >>
  Cases_on `v = NONE \/ v = SOME 0` >> simp[]
QED

Theorem eval_send_gas_obs[local]:
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
  qspecl_then [`cx`, `SOME amt`] strip_assume_tac frame_call_value_pure >>
  simp[] >> Cases_on `r` >> simp[] >>
  rename1 `INL vo` >>
  Cases_on `st.outcomes` >> simp[bind_def, ignore_bind_def, return_def]
  >- (simp[get_accounts_def, get_transient_storage_def, lift_option_def,
           check_def, assert_def, update_accounts_def, update_transient_def,
           append_logs_def, return_def, raise_def] >>
      Cases_on `run_ext_call cx.txn.target addr [] vo
                  (forwarded_gas 0 (ext_call_kwarg EKGas [EKGas] gas_vs))
                  st.accounts st.tStorage (vyper_to_tx_params cx.txn)` >>
      simp[raise_def, return_def] >>
      rename1 `_ = SOME rr` >> PairCases_on `rr` >> simp[] >>
      IF_CASES_TAC >> simp[]) >>
  qspecl_then [`addr`, `[]`, `vo`, `st`, `g`] mp_tac
    take_call_outcome_gas_obs >>
  Cases_on `take_call_outcome addr [] vo st` >>
  rename1 `_ = (q, st1)` >> reverse (Cases_on `q`) >- simp[] >>
  rename1 `INL rqoc` >> PairCases_on `rqoc` >> simp[] >> strip_tac >>
  fs[check_def, assert_def, raise_def, return_def, bind_def, ignore_bind_def] >>
  IF_CASES_TAC >> fs[] >>
  qspecl_then [`rqoc0`, `rqoc1`, `st1`, `g`] mp_tac
    adopt_call_outcome_gas_obs >>
  Cases_on `adopt_call_outcome rqoc0 rqoc1 st1` >> rename1 `_ = (q2, _)` >>
  Cases_on `q2` >> simp[]
QED

Theorem eval_send_read_gas_obs[local]:
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

Theorem eval_expr_send_action[local]:
  !cx ann has_gas args dflt.
    LENGTH args = (if has_gas then 3 else 2) ==>
    bind (eval_expr cx (Call ann (Send has_gas) args dflt)) (read_result cx) =
    bind (eval_exprs cx args)
      (\vs. do tv <- eval_send cx has_gas vs; read_result cx tv od)
Proof
  rpt strip_tac >> simp[FUN_EQ_THM] >> gen_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def] >>
  Cases_on `eval_exprs cx args x` >> rename1 `(rr, _)` >>
  Cases_on `rr` >> simp[]
QED

Theorem send_exempt_cert[local]:
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
    (simp[FUN_EQ_THM, ignore_bind_def, bind_def] >> gen_tac >>
     Cases_on `eval_exprs cx args x` >> rename1 `(rr, _)` >>
     Cases_on `rr` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_values >> simp[]
QED

(* ===== The CALL and the ASSERT ===== *)

(* fragGasSeqAbort's run_inst_seq_abort_zero_path on the memory-checked
   path. *)
(* The CALL's argument and return ranges are empty and ASSERT has none. *)
Theorem send_tail_mem_ok[local]:
  !id1 id2 gas_op addr_op val_op out s.
    run_inst_seq_mem_ok
      [mk_inst id1 CALL
         [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w] [out];
       mk_inst id2 ASSERT [Var out] []] s
Proof
  rpt gen_tac >> irule run_inst_seq_mem_ok_every >>
  simp[below_frontier_CALL, eval_operand_def] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem send_tail_path_mem:
  expr_has_effect e /\
  emit_op CALL [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
    sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (u, sb) /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  stmt_state_rel ctx func cenv cx es1 t /\ alloca_history func t /\
  wb_frame cenv es es1 sa s0 t /\
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
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT ==>
  ?r. gas_marked_path T ctx func t 0 r /\
      ((?t'. r = OK t' /\
             (?v. res = INL v /\
                  expr_post ctx func cenv cx e es sa sb s0 es' v (Lit 0w) t') /\
             t'.vs_current_bb = sb.cs_current_bb /\
             t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
             alloca_history func t' /\
             t.vs_alloca_next <= t'.vs_alloca_next) \/
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
  `run_inst_seq_mem_ok code t` by simp[Abbr `code`, send_tail_mem_ok] >>
  `?bb rest. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
             DROP t.vs_inst_idx bb.bb_instructions = code ++ rest` by
    (qpat_x_assum `fn_has_code sm sb func` mp_tac >>
     simp[fn_has_code_def] >> strip_tac >> qexists_tac `bb` >>
     qpat_x_assum `isPREFIX _ bb.bb_instructions` mp_tac >>
     simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     gvs[] >> qexists_tac `l` >>
     REWRITE_TAC[GSYM listTheory.APPEND_ASSOC,
                 rich_listTheory.DROP_LENGTH_APPEND]) >>
  `isPREFIX code (DROP t.vs_inst_idx bb.bb_instructions)` by
    simp[rich_listTheory.IS_PREFIX_APPEND] >>
  drule_all send_call_read_step >>
  disch_then (qspecl_then [`out`, `sm.cs_next_id`] strip_assume_tac) >>
  rename1 `s' = t with <| vs_outcomes := _; vs_requests := _;
    vs_accounts := _; vs_transient := _; vs_logs := _;
    vs_pending_deletions := _; vs_returndata := _ |>` >>
  `s'.vs_allocas = t.vs_allocas /\ s'.vs_alloca_next = t.vs_alloca_next /\
   s'.vs_memory = t.vs_memory /\ s'.vs_vars = t.vs_vars /\
   s'.vs_labels = t.vs_labels /\ s'.vs_current_bb = t.vs_current_bb` by
    (qpat_x_assum `s' = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[])
  >- (`run_inst_seq code t = OK (update_var out 1w s')` by
        asm_simp_tac (srw_ss()) [Abbr `code`, run_inst_seq_def,
                                 send_assert_ok] >>
      qspecl_then [`code`, `t`, `update_var out 1w s'`, `ctx`, `func`, `bb`]
        mp_tac run_inst_seq_gas_path_mem >>
      (impl_tac >- fs[EVERY_MEM]) >>
      qpat_assum `FILTER _ code = []` (fn th => REWRITE_TAC[th, LENGTH]) >>
      strip_tac >>
      `alloca_history func (update_var out 1w s' with
         vs_inst_idx := t.vs_inst_idx + LENGTH code)` by
        (irule alloca_history_run_inst_seq >>
         fs[stmt_state_rel_def, EVERY_MEM] >> metis_tac[]) >>
      `LENGTH sb.cs_current_insts = t.vs_inst_idx + LENGTH code` by
        (qpat_x_assum `sb.cs_current_insts = _` SUBST1_TAC >>
         qpat_x_assum `t.vs_inst_idx = _` SUBST1_TAC >> simp[]) >>
      qexists_tac `OK (update_var out 1w s' with
                       vs_inst_idx := LENGTH sb.cs_current_insts)` >>
      conj_tac
      >- (pop_assum SUBST1_TAC >> simp[gas_marked_path_def] >>
          first_assum ACCEPT_TAC) >>
      disj1_tac >> simp[] >>
      `(update_var out 1w s').vs_current_bb = sb.cs_current_bb /\
       (update_var out 1w s').vs_alloca_next = t.vs_alloca_next` by
        (qpat_x_assum `s' = _` SUBST1_TAC >> fs[update_var_def]) >>
      simp[] >>
      conj_tac
      >- (irule expr_post_none_intro >> simp[stmt_state_rel_inst_idx] >>
          conj_tac
          >- (irule stmt_state_rel_update_var >> conj_tac
              >- (irule fresh_not_local_ptr >> qexists_tac `sm` >>
                  metis_tac[]) >>
              `es'.scopes = es1.scopes /\ es'.immutables = es1.immutables` by
                (drule eval_send_read >> strip_tac >>
                 drule eval_send_preserves_non_accounts >> simp[]) >>
              `immutable_alloca_sep func cenv cx es' s'` by
                (irule immutable_alloca_sep_fields >>
                 qexistsl_tac [`t`, `es1`] >>
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
          `wb_frame cenv es es' sa s0 t` by
            (`es'.scopes = es1.scopes` by
               (drule eval_send_read >> strip_tac >>
                drule eval_send_preserves_non_accounts >> simp[]) >>
             qpat_x_assum `wb_frame cenv es es1 sa s0 t` mp_tac >>
             pure_rewrite_tac[wb_frame_def, locals_kept_def, popped_kept_def] >>
             qpat_x_assum `es'.scopes = es1.scopes`
               (fn th => pure_rewrite_tac[th]) >>
             disch_then ACCEPT_TAC) >>
          irule wb_frame_readonly_tail >>
          qexists_tac `sm` >>
          qpat_assum `wb_frame cenv es es' sa s0 t` (irule_at Any) >>
          simp[update_var_def, lookup_var_def,
               finite_mapTheory.FLOOKUP_UPDATE] >>
          rw[] >> gvs[not_fresh_at_def] >> metis_tac[]) >>
      qpat_x_assum `alloca_history func _` mp_tac >> simp[]) >>
  `run_inst_seq code t =
     Abort Revert_abort (revert_state (set_returndata [] (update_var out 0w s')))` by
    asm_simp_tac (srw_ss()) [Abbr `code`, run_inst_seq_def, send_assert_fail] >>
  drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_abort_zero_path_mem >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[exit_result_def, expr_exit_def]
QED

(* ===== send ===== *)

(* After the operands' memory-counted run, the send tail reads no GAS and
   its source part reads no observation, so the whole action keeps the
   operands' marks. *)
Theorem send_args_summary_mem:
  gas_summary_at T (ctx,func) marks (eval_exprs cx args) (es,s0)
    (\rr ee t. ?vs. rr = INL vs /\
       typed_args_post ctx func cenv cx es sa s0 ee args
         ([addr_op; val_op] ++ (if has_gas then [gas_op] else [])) vs t /\
       t.vs_current_bb = sm.cs_current_bb /\
       t.vs_inst_idx = LENGTH sm.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\rr ee r. wb_args_exit rr r) /\
  (~has_gas ==> gas_op = Lit 0w) /\
  MAP expr_type args =
    [BaseT AddressT; BaseT (UintT 256)] ++
    (if has_gas then [BaseT (UintT 256)] else []) /\
  LENGTH args = (if has_gas then 3 else 2) /\
  typed_args_ready_mem ctx func cenv cx expr_type
    (expr_sim_inv cenv cx env) args /\
  expr_sim_inv cenv cx env es /\
  (!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
         expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)) /\
  emit_op CALL [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
    sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (u, sb) /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var ==>
  gas_summary_at T (ctx,func) marks
    (bind (eval_expr cx (Call NoneT (Send has_gas) args dflt)) (read_result cx))
    (es,s0)
    (\res ee t. ?v. res = INL v /\
       expr_post ctx func cenv cx (Call NoneT (Send has_gas) args dflt)
         es sa sb s0 ee v (Lit 0w) t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  rewrite_tac[gas_summary_at_def] >> strip_tac >>
  qpat_x_assum `LENGTH args = _` (fn th => assume_tac th >>
    rewrite_tac[MATCH_MP eval_expr_send_action th]) >>
  gvs[]
  >- suspend "normal" >>
  Cases_on `res` >> gvs[wb_args_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >>
  conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  simp[]
QED

Resume send_args_summary_mem[normal]:
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
    metis_tac[typed_args_ready_mem_inv] >>
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
  `?r. gas_marked_path T ctx func t 0 r /\
       ((?t'. r = OK t' /\
              (?w. res = INL w /\
                   expr_post ctx func cenv cx
                     (Call NoneT (Send has_gas) (a::v::gs) dflt)
                     es sa sb s0 fin w (Lit 0w) t') /\
              t'.vs_current_bb = sb.cs_current_bb /\
              t'.vs_inst_idx = LENGTH sb.cs_current_insts /\
              alloca_history func t' /\
              t.vs_alloca_next <= t'.vs_alloca_next) \/
        (exit_result r /\ expr_exit res r))` by
    (irule send_tail_path_mem >> simp[expr_type_def, loweringPostsTheory.expr_has_effect_thm] >>
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

Finalise send_args_summary_mem

Theorem send_expr_sim_mem:
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  typed_args_ready_mem ctx func cenv cx expr_type
    (expr_sim_inv cenv cx env) args ==>
  expr_sim_mem ctx func cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  strip_tac >> drule send_pre_types >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
         expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)` by
    (rpt strip_tac >- metis_tac[expr_body_pre_send_arg] >>
     gvs[EVERY_MEM]) >>
  `wb_args_shape cenv expr_type args` by metis_tac[typed_stack_args_shape] >>
  rewrite_tac[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
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
    mp_tac lower_typed_args_sim_mem >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      PURE_REWRITE_TAC[vyperASTTheory.expr_type_def, expr_store_bound_none,
                       AND_CLAUSES] >>
      irule send_args_summary_mem >> simp[expr_type_def] >>
      conj_tac
      >- (qexistsl_tac [`addr_op`, `gas_op`, `s3`, `sm`, `success`, `val_op`] >>
          fs[]) >>
      qexists_tac `env` >> fs[] >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >>
  metis_tac[send_exempt_cert]
QED

Theorem body_send_mem_case:
  !cx v12 has_gas es v13.
    (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Call v12 (Send has_gas) es v13)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `Call ann (Send has_gas) args dflt` >>
  simp[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  drule send_pre_types >> strip_tac >>
  `body_exprs_mem_ok cx args` by
    (first_x_assum irule >> simp[type_check_def, assert_def]) >>
  `expr_sim_mem ctx func cenv cx ty (Call ann (Send has_gas) args dflt) es` by
    (irule send_expr_sim_mem >> qexists_tac `env` >> simp[] >>
     irule typed_args_ready_mem_of_body >> rpt conj_tac
     >- (rpt strip_tac >- metis_tac[expr_body_pre_send_arg] >>
         gvs[EVERY_MEM]) >>
     metis_tac[]) >>
  `~is_word_type (expr_type (Call NoneT (Send has_gas) args dflt)) ==>
   !tvt. evaluate_type (get_tenv cx)
           (lowered_value_type cenv (Call NoneT (Send has_gas) args dflt)) =
         SOME tvt ==> type_memory_size tvt = 0` by
    gvs[vyperASTTheory.expr_type_def, is_word_type_def,
        exprLoweringTheory.lowered_value_type_def,
        vyperValueTheory.evaluate_type_def,
        valueEncodingTheory.type_memory_size_def] >>
  simp[] >> drule_then irule body_expr_vv_sim_mem_stack >> simp[] >> conj_tac
  >- (gen_tac >>
      Cases_on `compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa` >>
      drule compile_expr_send_stack >> strip_tac >> gvs[]) >>
  metis_tac[eval_expr_send_value]
QED
