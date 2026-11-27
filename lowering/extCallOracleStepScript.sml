(*
 * The oracle external-call step (#636, Calls rows 1 and 2)
 *
 * In SOME oracle mode a source external call (eval_ext_call) or send
 * (eval_send) takes its outcome with take_call_outcome and, on success,
 * adopts it with adopt_call_outcome.  The lowering emits CALL (STATICCALL
 * for a static extcall), which Venom runs with exec_ext_call: it builds a
 * request from the evaluated operands (venom_call_request) and consumes
 * the outcome with consume_call_outcome.  Under state_rel the two requests
 * agree (request_agree: equal but for accounts and transient storage that
 * agree up to dead bytes), so both sides take agreeing outcomes, record
 * agreeing requests and, on success, adopt agreeing accounts and transient
 * storage and the same logs.  exec_ext_call_oracle_step is that step, for extcall and send
 * alike; send_call_oracle_step is send's CALL against eval_send.
 *
 * TOP-LEVEL:
 *   venom_call_request_source — Venom's request agrees with the source's,
 *                            given the same target, value, calldata and
 *                            static flag
 *   exec_ext_call_oracle_step — CALL/STATICCALL binds the success word and
 *                            keeps state_rel with the source after
 *                            adoption, given locals and immutable bytes
 *                            survive the return-buffer write
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
 * state_rel carries no such invariant, and exprSimHyps's expr_sim_inv does
 * (outcomes_accounts_typed), which is how exprSimSend proves send.
 *)

Theory extCallOracleStep
Ancestors
  list words
  compileEnv loweringStateRelDefs localPtrsProps exprLoweringProps accountsRelProps
  vyperInterpreter vyperState vyperValue vyperCallOutcome vyperCallOutcomeProps extCallOracle
  venomCallOracleDefs venomExecSemantics venomInst venomState venomMemProps

(* ===== Requests ===== *)

(* The request Venom builds from CALL's or STATICCALL's operands agrees
   with the one the source builds: same target, value, calldata and static
   flag, and accounts and transient storage that agree as accounts_rel
   says. *)
Theorem venom_call_request_source:
  !cx es s aw vw ao az stat target value_opt gas_cap gas.
    accounts_rel H cx es s /\ w2w aw = target /\
    w2n vw = (case value_opt of NONE => 0 | SOME n => n) /\
    (stat \/ s.vs_call_ctx.cc_static) = IS_NONE value_opt /\
    (!g. gas_cap = SOME g ==> g = w2n gas) ==>
    request_agree H cx.txn.target
      (call_outcome_request target (read_memory (w2n ao) (w2n az) s)
         value_opt es with cr_gas := gas_cap)
      (venom_call_request s aw vw ao az stat with cr_gas := SOME (w2n gas))
Proof
  rpt strip_tac >>
  drule_then (qspecl_then [`target`, `read_memory (w2n ao) (w2n az) s`,
                           `value_opt`] strip_assume_tac)
    accounts_rel_call_request >>
  gvs[request_agree_def, venom_call_request_def, call_outcome_request_def,
      call_request_component_equality]
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
  !func cenv sc s os rqs acc ts lg pending rd.
    local_ptrs_rel func cenv sc
      (s with <| vs_outcomes := os; vs_requests := rqs; vs_accounts := acc;
                 vs_transient := ts; vs_logs := lg;
                 vs_pending_deletions := pending; vs_returndata := rd |>) <=>
    local_ptrs_rel func cenv sc s
Proof
  simp[local_ptrs_rel_def, local_region_def, local_backed_def, lookup_var_def]
QED

(* ===== The shared step ===== *)

(* The adopted source state against Venom's state after consuming the
   outcome: locals and immutable bytes need output preservation; other
   fields follow from state_rel before the call, as both sides take,
   record and adopt the same outcome. *)
Theorem state_rel_adopt_consume[local]:
  !func cenv cx es s rq rq' outcome rest ro rz tr.
    state_rel H func cenv cx es s /\ request_agree H cx.txn.target rq rq' /\
    take_outcome rq s.vs_outcomes = (outcome, rest) /\
    local_ptrs_rel func cenv es.scopes
      (SND (consume_call_outcome rq' ro rz s)) /\
    (!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
      immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es
        (SND (consume_call_outcome rq' ro rz s))) ==>

    state_rel H func cenv cx
      (SND (adopt_call_outcome rq outcome
              (es with <| outcomes := SOME rest;
                          requests := record_request rq es.requests;
                          storage_trace := tr |>)))
      (SND (consume_call_outcome rq' ro rz s))
Proof
  rpt strip_tac >>
  Cases_on `take_outcome rq' s.vs_outcomes` >>
  rename1 `take_outcome rq' _ = (outcome', rest')` >>
  drule_all take_outcome_agree >> strip_tac >>
  `outcome'.co_success = outcome.co_success /\
   outcome'.co_logs = outcome.co_logs /\
   outcome'.co_toDelete = outcome.co_toDelete` by
    (qpat_x_assum `_ = outcome'` (SUBST1_TAC o SYM) >> simp[]) >>
  `rq'.cr_static = rq.cr_static /\ rq'.cr_kind = rq.cr_kind /\
   (computed_precompile rq' <=> computed_precompile rq)` by
    (fs[request_agree_def] >> qpat_x_assum `_ = rq'` (SUBST1_TAC o SYM) >>
     simp[computed_precompile_def]) >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[state_rel_def, call_ctx_rel_def] >>
  `accounts_rel H cx
     (SND (adopt_call_outcome rq outcome
             (es with <| outcomes := SOME rest;
                         requests := record_request rq es.requests;
                         storage_trace := tr |>)))
     (SND (consume_call_outcome rq' ro rz s))` by
    (irule accounts_rel_adopt_call_outcome >>
     qexistsl [`es with <| outcomes := SOME rest;
                           requests := record_request rq es.requests;
                           storage_trace := tr |>`,
               `s.vs_logs`, `outcome`, `outcome'`, `rq`, `rq'`, `s`] >>
     gvs[state_rel_def, adopt_call_outcome_equation, accounts_rel_def]) >>
  drule accounts_rel_storage_transient >> simp[] >> strip_tac >>
  gvs[state_rel_def, adopt_call_outcome_equation, adopt_outcome_def,
      adopt_outcome_deletions_def, logs_rel_eq, record_request_def] >>
  Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >>
  Cases_on `rq.cr_kind = MessageCall` >>
  Cases_on `rq.cr_kind = DelegateMessageCall` >>
  gvs[storage_rel_def, transient_rel_def, accounts_rel_def,
      call_ctx_rel_def, contract_storage_def, contract_transient_def] >>
  gvs[immutables_rel_def] >>
  Cases_on `computed_precompile rq` >> simp[LIST_REL_APPEND] >>
  (conj_tac
   >- (qpat_assum `!src. src = _ \/ IS_SOME _ ==> _`
         (qspec_then `cenv.ce_module` mp_tac) >> simp[]) >>
   rpt gen_tac >> disch_tac >>
   qpat_assum `!src. src = _ \/ IS_SOME _ ==> _` (qspec_then `src` mp_tac) >>
   simp[])
QED

(* TOP-LEVEL: CALL or STATICCALL in oracle mode.  Given the source took
   outcome for the request the operands describe, Venom binds the success
   word, consumes the same outcome and writes the return buffer; once the
   locals and immutable bytes survive that write, state_rel holds with the
   source after it adopts the outcome (on failure adoption changes nothing, so this is the
   source state as taken). *)
Theorem exec_ext_call_oracle_step:
  !H func cenv cx es s inst gas aw vw ao az ro rz stat out target
   value_opt rq outcome es1 gas_cap.
    state_rel H func cenv cx es s /\ inst.inst_outputs = [out] /\
    w2w aw = target /\
    w2n vw = (case value_opt of NONE => 0 | SOME n => n) /\
    (stat \/ s.vs_call_ctx.cc_static) = IS_NONE value_opt /\
    (!g. gas_cap = SOME g ==> g = w2n gas) /\
    take_call_outcome gas_cap target
      (read_memory (w2n ao) (w2n az) s) value_opt es =
      (INL (rq, outcome), es1) ==>
    ?s'. exec_ext_call inst s gas aw vw ao az ro rz stat =
           OK (update_var out (if outcome.co_success then 1w else 0w) s') /\
         s' = s with <| vs_outcomes := s'.vs_outcomes;
                        vs_requests := s'.vs_requests;
                        vs_accounts := s'.vs_accounts;
                        vs_transient := s'.vs_transient;
                        vs_logs := s'.vs_logs;
                        vs_pending_deletions := s'.vs_pending_deletions;
                        vs_returndata := s'.vs_returndata;
                        vs_memory := s'.vs_memory |> /\
         s'.vs_memory =
           (write_memory_with_expansion (w2n ro)
              (TAKE (w2n rz) outcome.co_returnData) s).vs_memory /\
         s'.vs_returndata = outcome.co_returnData /\
         (local_ptrs_rel func cenv es.scopes s' /\
          (!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
            immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es s') ==>
          state_rel H func cenv cx (SND (adopt_call_outcome rq outcome es1)) s')
Proof
  rpt gen_tac >> strip_tac >>
  `accounts_rel H cx es s /\ es.outcomes = SOME s.vs_outcomes /\
   s.vs_call_ctx.cc_static = cx.txn.is_static` by
    fs[state_rel_def, call_ctx_rel_def] >>
  Cases_on `s.vs_outcomes = []`
  >- gvs[take_call_outcome_def, take_request_outcome_def] >>
  `?rest. rq = (call_outcome_request target (read_memory (w2n ao) (w2n az) s)
                 value_opt es with cr_gas := gas_cap) /\
          take_outcome rq s.vs_outcomes = (outcome, rest) /\
          es1 = es with <| outcomes := SOME rest;
                           requests := record_request rq es.requests;
                           storage_trace := es.storage_trace ++
                             [StorageOutcome rq outcome] |>` by
    (qpat_x_assum `take_call_outcome _ _ _ _ _ = _` mp_tac >>
     Cases_on `s.vs_outcomes` >> fs[] >>
     simp[take_call_outcome_def, take_request_outcome_def] >> pairarg_tac >> simp[] >> rw[] >>
     qexists_tac `rest` >> simp[]) >>
  `request_agree H cx.txn.target rq
    (venom_call_request s aw vw ao az stat with cr_gas := SOME (w2n gas))` by
    (qpat_x_assum `rq = _` SUBST1_TAC >>
     irule venom_call_request_source >> simp[]) >>
  qabbrev_tac `rq' = venom_call_request s aw vw ao az stat
    with cr_gas := SOME (w2n gas)` >>
  Cases_on `take_outcome rq' s.vs_outcomes` >>
  rename1 `take_outcome rq' _ = (outcome', rest')` >>
  drule_all take_outcome_agree >> strip_tac >>
  `outcome'.co_success = outcome.co_success /\
   outcome'.co_returnData = outcome.co_returnData` by
    (qpat_x_assum `_ = outcome'` (SUBST1_TAC o SYM) >> simp[]) >>
  qexists_tac `SND (consume_call_outcome rq' (w2n ro) (w2n rz) s)` >>
  rpt conj_tac
  >- gvs[exec_ext_call_def, Abbr `rq'`]
  >- simp[venom_state_component_equality]
  >- simp[]
  >- simp[] >>
  strip_tac >> qpat_x_assum `es1 = _` SUBST1_TAC >>
  irule state_rel_adopt_consume >> simp[] >>
  qpat_assum `!src. _ ==> immutables_rel _ _ _ _ _ _` mp_tac >>
  simp[consume_call_outcome_eq]
QED

Theorem exec_delegate_call_oracle_step:
  state_rel H func cenv cx es s /\ inst.inst_outputs = [out] /\
  w2w aw = target /\
  value_opt = (if s.vs_call_ctx.cc_static then NONE else SOME 0) /\
  (!g. gas_cap = SOME g ==> g = w2n gas) /\
  take_delegate_outcome gas_cap target
    (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) ==>
  ?s'. exec_delegatecall inst s gas aw ao az ro rz =
         OK (update_var out (if outcome.co_success then 1w else 0w) s') /\
       s' = s with <| vs_outcomes := s'.vs_outcomes;
                      vs_requests := s'.vs_requests;
                      vs_accounts := s'.vs_accounts;
                      vs_transient := s'.vs_transient;
                      vs_logs := s'.vs_logs;
                      vs_pending_deletions := s'.vs_pending_deletions;
                      vs_returndata := s'.vs_returndata;
                      vs_memory := s'.vs_memory |> /\
       s'.vs_memory = (write_memory_with_expansion (w2n ro)
         (TAKE (w2n rz) outcome.co_returnData) s).vs_memory /\
       s'.vs_returndata = outcome.co_returnData /\
       (local_ptrs_rel func cenv es.scopes s' /\
        (!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
          immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es s') ==>
        state_rel H func cenv cx (SND (adopt_call_outcome rq outcome es1)) s')
Proof
  strip_tac >>
  `accounts_rel H cx es s /\ es.outcomes = SOME s.vs_outcomes` by
    fs[state_rel_def] >>
  Cases_on `s.vs_outcomes = []`
  >- gvs[take_delegate_outcome_def, take_request_outcome_def] >>
  `?rest. rq = (delegate_outcome_request target
                  (read_memory (w2n ao) (w2n az) s) value_opt es
                with cr_gas := gas_cap) /\
          take_outcome rq s.vs_outcomes = (outcome,rest) /\
          es1 = es with <| outcomes := SOME rest;
                           requests := record_request rq es.requests;
                           storage_trace := es.storage_trace ++
                             [StorageOutcome rq outcome] |>` by
    (drule take_delegate_outcome_success >> strip_tac >>
     qexists_tac `rest` >> gvs[]) >>
  qabbrev_tac `rq' = venom_call_request s aw 0w ao az F with
    <| cr_kind := DelegateMessageCall; cr_gas := SOME (w2n gas) |>` >>
  `request_agree H cx.txn.target rq rq'` by
    (qpat_x_assum `rq = _` SUBST1_TAC >>
     drule_then (qspecl_then [`target`, `read_memory (w2n ao) (w2n az) s`,
                              `value_opt`] strip_assume_tac)
       accounts_rel_call_request >>
     Cases_on `s.vs_call_ctx.cc_static` >>
     gvs[Abbr `rq'`, delegate_outcome_request_def, request_agree_def,
         venom_call_request_def, call_outcome_request_def,
         call_request_component_equality]) >>
  Cases_on `take_outcome rq' s.vs_outcomes` >>
  rename1 `take_outcome rq' _ = (outcome',rest')` >>
  drule_all take_outcome_agree >> strip_tac >>
  `outcome'.co_success = outcome.co_success /\
   outcome'.co_returnData = outcome.co_returnData` by
    (qpat_x_assum `_ = outcome'` (SUBST1_TAC o SYM) >> simp[]) >>
  qexists_tac `SND (consume_call_outcome rq' (w2n ro) (w2n rz) s)` >>
  rpt conj_tac
  >- gvs[exec_delegatecall_def, Abbr `rq'`]
  >- simp[venom_state_component_equality]
  >- simp[]
  >- simp[] >>
  strip_tac >> qpat_x_assum `es1 = _` SUBST1_TAC >>
  irule state_rel_adopt_consume >> simp[] >>
  qpat_assum `!src. _ ==> immutables_rel _ _ _ _ _ _` mp_tac >>
  simp[consume_call_outcome_eq]
QED

Theorem frame_call_value_success:
  frame_call_value cx value_opt es = (INL framed_value, es') ==>
  es' = es /\
  (cx.txn.is_static ==> value_opt = NONE \/ value_opt = SOME 0) /\
  framed_value = (if cx.txn.is_static then NONE else value_opt)
Proof
  rw[frame_call_value_def, bind_def, ignore_bind_def, check_def, assert_def,
     vyperStateTheory.return_def] >> gvs[AllCaseEqs()]
QED

(* CALL evaluates all operands before the static-value fault. *)
Theorem call_static_value_abort:
  state_rel H func cenv cx es s /\ cx.txn.is_static /\
  inst.inst_opcode = CALL /\
  inst.inst_operands = [gop; aop; vop; iop; zop; rop; cop] /\
  eval_operand gop s = SOME gas /\ eval_operand aop s = SOME aw /\
  eval_operand vop s = SOME vw /\ vw <> 0w /\
  eval_operand iop s = SOME ip /\ eval_operand zop s = SOME iz /\
  eval_operand rop s = SOME rp /\ eval_operand cop s = SOME cap ==>
  frame_call_value cx (SOME (w2n vw)) es =
    (INR (Error (RuntimeError "write in static context")), es) /\
  step_inst_base inst s = Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  strip_tac >>
  `s.vs_call_ctx.cc_static` by fs[state_rel_def, call_ctx_rel_def] >>
  simp[frame_call_value_def, bind_def, ignore_bind_def, check_def, assert_def,
       vyperStateTheory.return_def, w2n_eq_0, step_inst_base_opcode_eqs]
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
   gas_vs aw vw res es' gw.
    state_rel H func cenv cx es s /\
    inst.inst_opcode = CALL /\ inst.inst_outputs = [out] /\
    inst.inst_operands =
      [gas_op; addr_op; val_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w] /\
    eval_operand gas_op s = SOME gw /\
    w2n gw = (case OPTION_BIND (ext_call_kwarg EKGas [EKGas] gas_vs) dest_NumV of
               NONE => 0 | SOME g => g) /\
    eval_operand addr_op s = SOME aw /\ dest_AddressV to_v = SOME (w2w aw) /\
    eval_operand val_op s = SOME vw /\ dest_NumV amount_v = SOME (w2n vw) /\
    LENGTH gas_vs = (if has_gas then 1 else 0) /\
    eval_send cx has_gas (to_v :: amount_v :: gas_vs) es = (res, es') ==>
    (res = INR (Error (RuntimeError "write in static context")) /\
     step_inst_base inst s = Abort ExHalt_abort (halt_state (set_returndata [] s))) \/
    (res = INR (Error (RuntimeError "take_call_outcome")) /\
     step_inst_base inst s = Abort ExHalt_abort (halt_state (set_returndata [] s))) \/
    res = INR (Error (RuntimeError "call outcome accounts")) \/
    ?s'. s' = s with <| vs_outcomes := s'.vs_outcomes;
                        vs_requests := s'.vs_requests;
                        vs_accounts := s'.vs_accounts;
                        vs_transient := s'.vs_transient;
                        vs_logs := s'.vs_logs;
                        vs_pending_deletions := s'.vs_pending_deletions;
                        vs_returndata := s'.vs_returndata |> /\
         ((res = INL (Value NoneV) /\
           step_inst_base inst s = OK (update_var out 1w s') /\
           state_rel H func cenv cx es' s') \/
          (res = INR (Error (RuntimeError "send failed")) /\
           step_inst_base inst s = OK (update_var out 0w s')))
Proof
  rpt gen_tac >> strip_tac >>
  `es.outcomes = SOME s.vs_outcomes /\
   local_ptrs_rel func cenv es.scopes s /\
   s.vs_call_ctx.cc_static = cx.txn.is_static` by
    fs[state_rel_def, call_ctx_rel_def] >>
  Cases_on `cx.txn.is_static /\ vw <> 0w`
  >- (disj1_tac >>
      qpat_x_assum `eval_send _ _ _ _ = _` mp_tac >>
      fs[eval_send_def, frame_call_value_def, bind_def, ignore_bind_def,
         type_check_def, assert_def, check_def, lift_option_type_def,
         vyperStateTheory.return_def, w2n_eq_0] >>
      Cases_on `eval_operand gas_op s` >>
      fs[step_inst_base_opcode_eqs, eval_operand_def]) >>
  disj2_tac >>
  `step_inst_base inst s =
     exec_ext_call inst s gw aw vw 0w 0w
       (0w:bytes32) (0w:bytes32) cx.txn.is_static` by
    (Cases_on `eval_operand gas_op s` >> fs[] >>
     simp[step_inst_base_opcode_eqs, eval_operand_def]) >>
  `frame_call_value cx (SOME (w2n vw)) es =
     (INL (if cx.txn.is_static then NONE else SOME (w2n vw)), es)` by
    (Cases_on `cx.txn.is_static` >> fs[frame_call_value_def, w2n_eq_0,
      bind_def, ignore_bind_def, check_def, assert_def, vyperStateTheory.return_def]) >>
  Cases_on `s.vs_outcomes = []`
  >- (disj1_tac >>
      qpat_x_assum `eval_send _ _ _ _ = _` mp_tac >>
      simp[eval_send_def, bind_def, ignore_bind_def, type_check_def,
           assert_def, check_def, lift_option_type_def, return_def,
           take_call_outcome_def, take_request_outcome_def,
           exec_ext_call_def] >> strip_tac >> gvs[]) >>
  disj2_tac >>
  qpat_x_assum `eval_send _ _ _ _ = _` mp_tac >>
  simp[eval_send_def, update_pending_deletions_def, bind_def, ignore_bind_def,
       type_check_def, assert_def, check_def, lift_option_type_def,
       vyperStateTheory.return_def] >>
  qpat_assum `w2n gw = _` (fn th => rewrite_tac[GSYM th]) >>
  Cases_on `take_call_outcome (SOME (w2n gw)) (w2w aw) []
    (if cx.txn.is_static then NONE else SOME (w2n vw)) es` >>
  qmatch_asmsub_rename_tac `take_call_outcome _ _ _ _ _ = (tr, es1)` >>
  Cases_on `tr` >> simp[]
  >- (rename1 `INL x` >> PairCases_on `x` >> rename1 `INL (rq, outcome)` >>
      simp[] >> strip_tac >> disj2_tac >>
      qspecl_then [`H`, `func`, `cenv`, `cx`, `es`, `s`, `inst`,
                   `gw`, `aw`, `vw`, `0w`, `0w`,
                   `0w:bytes32`, `0w:bytes32`, `cx.txn.is_static`, `out`, `w2w aw`,
                   `if cx.txn.is_static then NONE else SOME (w2n vw)`, `rq`,
                   `outcome`, `es1`, `SOME (w2n gw)`] mp_tac exec_ext_call_oracle_step >>
      (impl_tac >-
        (Cases_on `cx.txn.is_static` >>
         gvs[read_memory_def, write_memory_with_expansion_empty_0])) >>
      simp[write_memory_with_expansion_empty_0] >>
      strip_tac >>
      `s' = s with <| vs_outcomes := s'.vs_outcomes;
                      vs_requests := s'.vs_requests;
                      vs_accounts := s'.vs_accounts;
                      vs_transient := s'.vs_transient;
                      vs_logs := s'.vs_logs;
                      vs_pending_deletions := s'.vs_pending_deletions;
                      vs_returndata := s'.vs_returndata |>` by
        (qpat_x_assum `s'.vs_memory = _` mp_tac >>
         qpat_x_assum `s' = _` mp_tac >>
         simp[venom_state_component_equality]) >>
      `local_ptrs_rel func cenv es.scopes s'` by
        (qpat_x_assum `s' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
         simp[local_ptrs_rel_oracle_fields] >> first_assum ACCEPT_TAC) >>
      `!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
        immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es s'` by
        (gen_tac >> disch_tac >>
         `immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es s` by
           (fs[state_rel_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
         qpat_x_assum `immutables_rel _ _ _ _ es s` mp_tac >>
         qpat_x_assum `s' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
         simp[immutables_rel_def]) >>
      qexists_tac `s'` >> conj_tac
      >- (qpat_x_assum `s' = _` (fn th => ONCE_REWRITE_TAC [th]) >>
          simp[venom_state_component_equality]) >>
      rpt (qpat_x_assum `s' = _` kall_tac) >>
      Cases_on `outcome.co_success` >>
      gvs[adopt_call_outcome_equation, bind_def, ignore_bind_def, assert_def,
          vyperStateTheory.return_def] >> metis_tac[]) >>
  strip_tac >> disj1_tac >>
  qpat_x_assum `take_call_outcome _ _ _ _ _ = _` mp_tac >>
  Cases_on `s.vs_outcomes` >> gvs[] >>
  simp[take_call_outcome_def, take_request_outcome_def] >> pairarg_tac >> rw[] >> gvs[]
QED
