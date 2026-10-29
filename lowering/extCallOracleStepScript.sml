(*
 * The oracle external-call step (#636, Calls rows 1 and 2)
 *
 * In SOME oracle mode a source external call (eval_ext_call) or send
 * (eval_send) takes its outcome with take_call_outcome and, on success,
 * adopts it with adopt_call_outcome.  The lowering emits CALL (STATICCALL
 * for a static extcall), which Venom runs with exec_ext_call: it builds a
 * request from the evaluated operands (venom_call_request) and consumes
 * the outcome with consume_call_outcome.  Under state_rel the two requests
 * are the same, so both sides take the same outcome, record the same
 * request and, on success, adopt the same accounts, transient storage and
 * logs.  exec_ext_call_oracle_step is that step, for extcall and send
 * alike; send_call_oracle_step is send's CALL against eval_send.
 *
 * TOP-LEVEL:
 *   venom_call_request_source — Venom's request is the source's, given the
 *                            same target, value, calldata and static flag
 *   exec_ext_call_oracle_step — CALL/STATICCALL binds the success word and
 *                            keeps state_rel with the source after
 *                            adoption, given the locals survive the
 *                            return-buffer write
 *   send_call_oracle_step  — send's CALL against eval_send: success binds
 *                            1w with state_rel kept, failure binds 0w
 *
 * Helpers: logs_rel_eq, local_ptrs_rel_oracle_fields
 *
 * What compile_send_sim and compile_extcall_sim (exprSimCalls) still need
 * beyond these steps: take_call_outcome raises "call outcome accounts" on
 * a successful nonstatic outcome whose accounts are not runtime
 * well-typed, while Venom adopts the outcome and goes on, so the lowered
 * code does not abort there.  The step lemmas speak of a taken outcome
 * (INL); send_call_oracle_step lists that error as a case of its own.
 * Ruling it out takes an invariant that the outcomes still to consume are
 * well typed, as e2eDefs's call_outcomes_ok states for the initial ones;
 * state_rel carries no such invariant.
 *)

Theory extCallOracleStep
Ancestors
  list words
  compileEnv localPtrsProps exprLoweringProps accountsRelProps
  vyperInterpreter vyperState vyperValue vyperCallOutcome extCallOracle
  venomCallOracleDefs venomExecSemantics venomInst venomState venomMemProps

(* ===== Requests ===== *)

(* The request Venom builds from CALL's or STATICCALL's operands is the one
   the source builds: same target, value, calldata and static flag, and the
   accounts and transient storage accounts_rel makes equal. *)
Theorem venom_call_request_source:
  !es s aw vw ao az stat target value_opt.
    accounts_rel es s /\ w2w aw = target /\
    w2n vw = (case value_opt of NONE => 0 | SOME n => n) /\
    (stat \/ s.vs_call_ctx.cc_static) = IS_NONE value_opt ==>
    venom_call_request s aw vw ao az stat =
    call_outcome_request target (read_memory (w2n ao) (w2n az) s) value_opt es
Proof
  rpt strip_tac >>
  drule_then (qspecl_then [`target`, `read_memory (w2n ao) (w2n az) s`,
                           `value_opt`] strip_assume_tac)
    accounts_rel_call_request >>
  simp[venom_call_request_def, call_request_component_equality] >>
  simp[call_outcome_request_def]
QED

(* ===== Frames ===== *)

(* log_entry_equiv is equality, so logs_rel is. *)
Theorem logs_rel_eq:
  !cenv addr es s. logs_rel cenv addr es s <=> es.logs = s.vs_logs
Proof
  rw[logs_rel_def, log_entry_equiv_def, LIST_REL_EL_EQN, LIST_EQ_REWRITE] >>
  metis_tac[]
QED

(* local_ptrs_rel reads none of the fields an oracle call changes but
   memory. *)
Theorem local_ptrs_rel_oracle_fields:
  !func cenv sc s os rqs acc ts lg rd.
    local_ptrs_rel func cenv sc
      (s with <| vs_outcomes := os; vs_requests := rqs; vs_accounts := acc;
                 vs_transient := ts; vs_logs := lg; vs_returndata := rd |>) <=>
    local_ptrs_rel func cenv sc s
Proof
  simp[local_ptrs_rel_def, local_region_def, local_backed_def, lookup_var_def]
QED

(* ===== The shared step ===== *)

(* The adopted source state against Venom's state after consuming the
   outcome: everything but the locals follows from state_rel before the
   call, as both sides take, record and adopt the same outcome. *)
Theorem state_rel_adopt_consume[local]:
  !func cenv cx es s rq outcome rest ro rz.
    state_rel func cenv cx es s /\
    take_outcome rq s.vs_outcomes = (outcome, rest) /\
    local_ptrs_rel func cenv es.scopes
      (SND (consume_call_outcome rq ro rz s)) ==>
    state_rel func cenv cx
      (SND (adopt_call_outcome rq outcome
              (es with <| outcomes := SOME rest;
                          requests := record_request rq es.requests |>)))
      (SND (consume_call_outcome rq ro rz s))
Proof
  rpt strip_tac >>
  gvs[state_rel_def, adopt_call_outcome_equation, adopt_outcome_def,
      logs_rel_eq] >>
  Cases_on `outcome.co_success /\ ~rq.cr_static` >>
  gvs[storage_rel_def, transient_rel_def, accounts_rel_def,
      immutables_rel_def, call_ctx_rel_def, contract_storage_def,
      contract_transient_def]
QED

(* TOP-LEVEL: CALL or STATICCALL in oracle mode.  Given the source took
   outcome for the request the operands describe, Venom binds the success
   word, consumes the same outcome and writes the return buffer; once the
   locals survive that write, state_rel holds with the source after it
   adopts the outcome (on failure adoption changes nothing, so this is the
   source state as taken). *)
Theorem exec_ext_call_oracle_step:
  !func cenv cx es s inst gas aw vw ao az ro rz stat out target
   value_opt rq outcome es1.
    state_rel func cenv cx es s /\ inst.inst_outputs = [out] /\
    w2w aw = target /\
    w2n vw = (case value_opt of NONE => 0 | SOME n => n) /\
    stat = IS_NONE value_opt /\
    take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
      (INL (rq, outcome), es1) ==>
    ?s'. exec_ext_call inst s gas aw vw ao az ro rz stat =
           OK (update_var out (if outcome.co_success then 1w else 0w) s') /\
         s' = s with <| vs_outcomes := s'.vs_outcomes;
                        vs_requests := s'.vs_requests;
                        vs_accounts := s'.vs_accounts;
                        vs_transient := s'.vs_transient;
                        vs_logs := s'.vs_logs;
                        vs_returndata := s'.vs_returndata;
                        vs_memory := s'.vs_memory |> /\
         s'.vs_memory =
           (write_memory_with_expansion (w2n ro)
              (TAKE (w2n rz) outcome.co_returnData) s).vs_memory /\
         s'.vs_returndata = outcome.co_returnData /\
         (local_ptrs_rel func cenv es.scopes s' ==>
          state_rel func cenv cx (SND (adopt_call_outcome rq outcome es1)) s')
Proof
  rpt gen_tac >> strip_tac >>
  `accounts_rel es s /\ es.outcomes = SOME s.vs_outcomes /\
   ~s.vs_call_ctx.cc_static` by fs[state_rel_def] >>
  `?rest. rq = venom_call_request s aw vw ao az stat /\
          take_outcome rq s.vs_outcomes = (outcome, rest) /\
          es1 = es with <| outcomes := SOME rest;
                           requests := record_request rq es.requests |>` by
    (`venom_call_request s aw vw ao az stat =
      call_outcome_request target (read_memory (w2n ao) (w2n az) s)
        value_opt es` by (irule venom_call_request_source >> simp[]) >>
     pop_assum SUBST1_TAC >>
     qpat_x_assum `take_call_outcome _ _ _ _ = _` mp_tac >>
     simp[take_call_outcome_def] >> pairarg_tac >> simp[] >> rw[] >>
     qexists_tac `rest` >> simp[]) >>
  qexists_tac `SND (consume_call_outcome rq (w2n ro) (w2n rz) s)` >>
  rpt conj_tac
  >- gvs[exec_ext_call_def]
  >- simp[venom_state_component_equality]
  >- simp[]
  >- simp[] >>
  strip_tac >> qpat_x_assum `es1 = _` SUBST1_TAC >>
  irule state_rel_adopt_consume >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* ===== send ===== *)

(* send's CALL [gas; to; value; 0; 0; 0; 0] against eval_send, in oracle
   mode.  On success the source returns NoneV, Venom binds 1w, and
   state_rel holds after both adopt the outcome; on failure the source
   raises "send failed" and Venom binds 0w, which the ASSERT after the CALL
   turns into an Abort.  The return buffer is empty at 0, so memory is
   untouched.  The remaining source result is the accounts check of
   take_call_outcome, which Venom does not make. *)
Theorem send_call_oracle_step:
  !func cenv cx es s inst gas_op addr_op val_op out has_gas to_v amount_v
   gas_vs aw vw res es'.
    state_rel func cenv cx es s /\
    inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
    inst.inst_operands =
      [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
    IS_SOME (eval_operand gas_op s) /\
    eval_operand addr_op s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
    eval_operand val_op s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
    LENGTH gas_vs = (if has_gas then 1 else 0) /\
    eval_send cx has_gas (to_v :: amount_v :: gas_vs) es = (res, es') ==>
    res = INR (Error (RuntimeError "call outcome accounts")) \/
    ?s'. s' = s with <| vs_outcomes := s'.vs_outcomes;
                        vs_requests := s'.vs_requests;
                        vs_accounts := s'.vs_accounts;
                        vs_transient := s'.vs_transient;
                        vs_logs := s'.vs_logs;
                        vs_returndata := s'.vs_returndata |> /\
         ((res = INL (Value NoneV) /\
           step_inst_base inst s = OK (update_var out 1w s') /\
           state_rel func cenv cx es' s') \/
          (res = INR (Error (RuntimeError "send failed")) /\
           step_inst_base inst s = OK (update_var out 0w s')))
Proof
  rpt gen_tac >> strip_tac >>
  `es.outcomes = SOME s.vs_outcomes /\
   local_ptrs_rel func cenv es.scopes s /\ ~s.vs_call_ctx.cc_static` by
    fs[state_rel_def] >>
  `step_inst_base inst s =
     exec_ext_call inst s (THE (eval_operand gas_op s)) aw vw 0w 0w
       (0w:bytes32) (0w:bytes32) F` by
    (Cases_on `eval_operand gas_op s` >> fs[] >>
     simp[step_inst_base_def, eval_operand_def]) >>
  qpat_x_assum `eval_send _ _ _ _ = _` mp_tac >>
  simp[eval_send_def, bind_def, ignore_bind_def, type_check_def, assert_def,
       check_def, lift_option_type_def, vyperStateTheory.return_def] >>
  Cases_on `take_call_outcome (w2w aw) [] (SOME (w2n vw)) es` >>
  qmatch_asmsub_rename_tac `take_call_outcome _ _ _ _ = (tr, es1)` >>
  Cases_on `tr` >> simp[]
  >- (rename1 `INL x` >> PairCases_on `x` >> rename1 `INL (rq, outcome)` >>
      simp[] >> strip_tac >> disj2_tac >>
      qspecl_then [`func`, `cenv`, `cx`, `es`, `s`, `inst`,
                   `THE (eval_operand gas_op s)`, `aw`, `vw`, `0w`, `0w`,
                   `0w:bytes32`, `0w:bytes32`, `F`, `out`, `w2w aw`, `SOME (w2n vw)`, `rq`,
                   `outcome`, `es1`] mp_tac exec_ext_call_oracle_step >>
      simp[read_memory_def, write_memory_with_expansion_empty_0] >>
      strip_tac >>
      `s' = s with <| vs_outcomes := s'.vs_outcomes;
                      vs_requests := s'.vs_requests;
                      vs_accounts := s'.vs_accounts;
                      vs_transient := s'.vs_transient;
                      vs_logs := s'.vs_logs;
                      vs_returndata := s'.vs_returndata |>` by
        (qpat_x_assum `s'.vs_memory = _` mp_tac >>
         qpat_x_assum `s' = _` mp_tac >>
         simp[venom_state_component_equality]) >>
      `local_ptrs_rel func cenv es.scopes s'` by
        (qpat_x_assum `s' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
         simp[local_ptrs_rel_oracle_fields] >> first_assum ACCEPT_TAC) >>
      qexists_tac `s'` >> conj_tac
      >- (qpat_x_assum `s' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
          simp[venom_state_component_equality]) >>
      rpt (qpat_x_assum `s' = _` kall_tac) >>
      Cases_on `outcome.co_success` >>
      gvs[adopt_call_outcome_equation, bind_def, ignore_bind_def, assert_def,
          vyperStateTheory.return_def]) >>
  strip_tac >> disj1_tac >>
  qpat_x_assum `take_call_outcome _ _ _ _ = _` mp_tac >>
  simp[take_call_outcome_def] >> pairarg_tac >> rw[] >> gvs[]
QED
