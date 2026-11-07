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
 *   eval_expr_send_cases, eval_send_value, eval_send_read,
 *     eval_expr_send_value,
 *     take_call_outcome_typed,
 *     eval_send_outcome_typed, address_typed_dest, uint256_typed_dest — the
 *     source side
 *   expr_body_pre_send_arg, send_pre_types, typed_args_ready_inv — the
 *     operands
 *   send_tail_shape, send_tail_frag, expr_post_none_intro — the CALL and
 *     the ASSERT
 *)

Theory exprSimSend
Ancestors
  exprSimSource
  exprSimHypsDefs
  exprSimDefs exprSimStack
  loweringPosts
  allocLimits
  list pair vyperMisc fragExec loweringSlice  exprSimHyps exprSimWordArgs
  gasOutcome gasSummary gasSummaryCompose gasExemptCert fragGasPath
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
  cheat
QED

Theorem compile_expr_send_stack:
  !cenv ty ann has_gas args dflt sa vv sb.
    compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa = (vv, sb) ==>
    vv = StackValue ann (Lit 0w)
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED

Theorem eval_send_value:
  !cx has_gas vs st tv st'.
    eval_send cx has_gas vs st = (INL tv, st') ==> ?v. tv = Value v
Proof
  cheat
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
  cheat
QED

Theorem eval_expr_send_value:
  !cx ann has_gas args dflt es tv es'.
    eval_expr cx (Call ann (Send has_gas) args dflt) es = (INL tv, es') ==>
    ?v. tv = Value v
Proof
  cheat
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
  cheat
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
  cheat
QED

Theorem address_typed_dest:
  !v. value_has_type (BaseTV AddressT) v ==>
      dest_AddressV v = SOME (w2w (typed_val_to_w256 (BaseTV AddressT) v))
Proof
  cheat
QED

Theorem uint256_typed_dest:
  !v. value_has_type (BaseTV (UintT 256)) v ==>
      dest_NumV v = SOME (w2n (typed_val_to_w256 (BaseTV (UintT 256)) v))
Proof
  cheat
QED

(* ===== The operands ===== *)

Theorem expr_body_pre_send_arg:
  !cenv cx env ann has_gas args dflt e es es'.
    expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  cheat
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
  cheat
QED

(* The invariant of typed_args_ready holds after all the operands. *)
Theorem typed_args_ready_inv:
  !args es vs es' ctx.
    typed_args_ready ctx func cenv cx arg_ty Inv args /\ Inv es /\
    eval_exprs cx args es = (INL vs, es') ==>
    Inv es'
Proof
  cheat
QED

(* ===== The CALL and the ASSERT ===== *)

Theorem expr_post_none_intro:
  post_value_type cenv e = expr_type e /\
  expr_type e = NoneT /\ stmt_state_rel ctx func cenv cx es' s /\
  wb_frame cenv es sa s0 s ==>
  expr_post ctx func cenv cx e es sa sb s0 es' NoneV (Lit 0w) s
Proof
  cheat
QED

(* The ASSERT of the success word the CALL just bound. *)
Theorem send_assert_ok[local]:
  !id x w s.
    w <> 0w ==>
    step_inst_base (mk_inst id ASSERT [Var x] []) (update_var x w s) =
      OK (update_var x w s)
Proof
  cheat
QED

Theorem send_assert_fail[local]:
  !id x s.
    step_inst_base (mk_inst id ASSERT [Var x] []) (update_var x 0w s) =
      Abort Revert_abort (revert_state (set_returndata [] (update_var x 0w s)))
Proof
  cheat
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
  cheat
QED

Theorem send_tail_frag:
  emit_op CALL [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
    sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (u, sb) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  stmt_state_rel ctx func cenv cx es1 t /\ wb_frame cenv es sa s0 t /\
  outcomes_accounts_typed es1.outcomes /\
  accounts_runtime_well_typed es1.accounts /\
  IS_SOME (eval_operand gas_op t) /\
  eval_operand addr_op t = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand val_op t = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  (do tv <- eval_send cx has_gas (to_v :: amount_v :: gas_vs);
      read_result cx tv od) es1 = (res, es') /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT ==>
  frag_exec ctx sm sb (\s. s = t)
    (\s. ?v. res = INL v /\
             expr_post ctx func cenv cx e es sa sb s0 es' v (Lit 0w) s)
    (expr_exit res)
Proof
  cheat
QED

(* ===== Counted gas: the CALL and the ASSERT as a gas path ===== *)

(* The oracle's take and adopt never read or write the gas observations. *)
Theorem take_call_outcome_gas_obs[local]:
  take_call_outcome target calldata value_opt (st with gas_obs := tail) =
  (FST (take_call_outcome target calldata value_opt st),
   SND (take_call_outcome target calldata value_opt st) with gas_obs := tail)
Proof
  cheat
QED

Theorem adopt_call_outcome_gas_obs[local]:
  adopt_call_outcome rq outcome (st with gas_obs := tail) =
  (FST (adopt_call_outcome rq outcome st),
   SND (adopt_call_outcome rq outcome st) with gas_obs := tail)
Proof
  cheat
QED

Theorem frame_call_value_gas_obs[local]:
  frame_call_value cx value_opt (st with gas_obs := tail) =
  (FST (frame_call_value cx value_opt st),
   SND (frame_call_value cx value_opt st) with gas_obs := tail)
Proof
  cheat
QED

(* send never reads or writes the gas observations. *)
Theorem eval_send_gas_obs[local]:
  !cx has_gas vs st r st'.
    eval_send cx has_gas vs st = (r, st') ==>
    !tail. eval_send cx has_gas vs (st with gas_obs := tail) =
             (r, st' with gas_obs := tail)
Proof
  cheat
QED

Theorem send_read_gas_obs[local]:
  bind (eval_send cx has_gas vs) (read_result cx) st = (res, st') ==>
  !tail. bind (eval_send cx has_gas vs) (read_result cx)
           (st with gas_obs := tail) = (res, st' with gas_obs := tail)
Proof
  cheat
QED

Theorem eval_expr_send_read_action[local]:
  LENGTH args = (if has_gas then 3 else 2) ==>
  bind (eval_expr cx (Call ann (Send has_gas) args dflt)) (read_result cx) =
  bind (eval_exprs cx args) (\vs. bind (eval_send cx has_gas vs) (read_result cx))
Proof
  cheat
QED

Theorem send_tail_path[local]:
  emit_op CALL [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
    sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (u, sb) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\
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
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT ==>
  ?n r. gas_marked_path F ctx func t n r /\
    ((?w. r = OK w /\
          (?v. res = INL v /\
               expr_post ctx func cenv cx e es sa sb s0 es' v (Lit 0w) w) /\
          w.vs_current_bb = sb.cs_current_bb /\
          w.vs_inst_idx = LENGTH sb.cs_current_insts) \/
     (exit_result r /\ expr_exit res r))
Proof
  cheat
QED

Theorem send_tail_summary[local]:
  emit_op CALL [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
    sm = (success, s3) /\
  emit_void ASSERT [success] s3 = (u, sb) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\
  stmt_state_rel ctx func cenv cx es1 t /\ wb_frame cenv es sa s0 t /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ es1.gas_obs = [] /\
  outcomes_accounts_typed es1.outcomes /\
  accounts_runtime_well_typed es1.accounts /\
  IS_SOME (eval_operand gas_op t) /\
  eval_operand addr_op t = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
  eval_operand val_op t = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
  LENGTH gas_vs = (if has_gas then 1 else 0) /\
  bind (eval_send cx has_gas (to_v :: amount_v :: gas_vs)) (read_result cx)
    es1 = (res, es') /\
  post_value_type cenv e = expr_type e /\ expr_type e = NoneT ==>
  ?marks. gas_summary_at F (ctx,func) marks
    (bind (eval_send cx has_gas (to_v :: amount_v :: gas_vs)) (read_result cx))
    (es1, t)
    (\res ee t. ?v. res = INL v /\
       expr_post ctx func cenv cx e es sa sb s0 ee v (Lit 0w) t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  cheat
QED

(* ===== send ===== *)

Theorem lower_value_send:
  lower_value compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa =
    (op, sb) ==>
  op = Lit 0w /\
  compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa =
    (StackValue ann (Lit 0w), sb)
Proof
  cheat
QED

Theorem send_expr_sim:
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  (!arg_ty. typed_args_ready ctx func cenv cx arg_ty (expr_sim_inv cenv cx env) args) ==>
  expr_sim ctx func cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  cheat
QED

(* TOP-LEVEL *)
Theorem compile_send_case:
  !nocalls ctx func cenv cx ann has_gas args dflt.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx (Call ann (Send has_gas) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx (Call ann (Send has_gas) args dflt)
Proof
  cheat
QED

Theorem compile_send_case_sim:
  !cenv ann has_gas args dflt.
    expr_sim_below cenv (expr_size (Call ann (Send has_gas) args dflt)) ==>
    expr_vv_ok cenv (Call ann (Send has_gas) args dflt)
Proof
  cheat
QED
