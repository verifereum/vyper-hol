Theory lowerDloadExternalBackward
Ancestors
  lowerDloadOracleSelection lowerDloadDelegateBoundary
  venomExecSemantics venomCallOracleDefs extCallOracle venomState list

(* Requests may have different account snapshots and histories. Only their
   scalar selector inputs and calldata determine the returned word/bytes. *)
Theorem ld_exec_ext_call_backward:
  read_memory (w2n offS) (w2n sz) s =
    read_memory (w2n offT) (w2n sz) t /\
  s.vs_outcomes = t.vs_outcomes /\
  exec_ext_call i t gas addr value offT sz roT rs static = OK t' ==>
  ?out w rS rT.
    i.inst_outputs = [out] /\ t' = update_var out w rT /\
    exec_ext_call i s gas addr value offS sz (roS:bytes32) rs static =
      OK (update_var out w rS) /\
    consume_call_outcome (venom_call_request s addr value offS sz static)
      (w2n roS) (w2n rs) s = (w,rS) /\
    consume_call_outcome (venom_call_request t addr value offT sz static)
      (w2n roT) (w2n rs) t = (w,rT) /\
    rS.vs_returndata = rT.vs_returndata /\
    rS.vs_memory = (write_memory_with_expansion (w2n roS)
      (TAKE (w2n rs) rT.vs_returndata) s).vs_memory /\
    rT.vs_memory = (write_memory_with_expansion (w2n roT)
      (TAKE (w2n rs) rT.vs_returndata) t).vs_memory
Proof
  strip_tac >>
  qabbrev_tac `rqS = venom_call_request s addr value offS sz static` >>
  qabbrev_tac `rqT = venom_call_request t addr value offT sz static` >>
  `rqS.cr_kind = rqT.cr_kind /\ rqS.cr_value = rqT.cr_value /\
   rqS.cr_target = rqT.cr_target /\ rqS.cr_data = rqT.cr_data` by
    simp[Abbr `rqS`, Abbr `rqT`, venom_call_request_def] >>
  drule ld_take_outcome_success_cong >>
  disch_then (qspec_then `t.vs_outcomes` assume_tac) >>
  drule ld_take_outcome_returndata_cong >>
  disch_then (qspec_then `t.vs_outcomes` assume_tac) >>
  Cases_on `consume_call_outcome rqS (w2n roS) (w2n rs) s` >>
  Cases_on `consume_call_outcome rqT (w2n roT) (w2n rs) t` >>
  gvs[exec_ext_call_def, Abbr `rqT`,
      Excl "consume_call_outcome_eq", AllCaseEqs()] >>
  gvs[consume_call_outcome_eq]
QED

(* Oversize initcode aborts, so a successful target execution also certifies
   the same size guard for the source. No static assumption is hidden here:
   it belongs to instruction dispatch, not exec_create. *)
Theorem ld_exec_create_backward:
  read_memory (w2n offS) (w2n sz) s =
    read_memory (w2n offT) (w2n sz) t /\
  s.vs_outcomes = t.vs_outcomes /\
  exec_create i t value offT sz salt = OK t' ==>
  ?out w rS rT.
    i.inst_outputs = [out] /\ t' = update_var out w rT /\
    exec_create i s value offS sz salt = OK (update_var out w rS) /\
    consume_create_outcome (venom_create_request s value offS sz salt) s = (w,rS) /\
    consume_create_outcome (venom_create_request t value offT sz salt) t = (w,rT) /\
    rS.vs_returndata = rT.vs_returndata /\
    rS.vs_memory = s.vs_memory /\ rT.vs_memory = t.vs_memory
Proof
  strip_tac >>
  qabbrev_tac `rqS = venom_create_request s value offS sz salt` >>
  qabbrev_tac `rqT = venom_create_request t value offT sz salt` >>
  `rqS.cr_kind = rqT.cr_kind /\ rqS.cr_value = rqT.cr_value /\
   rqS.cr_target = rqT.cr_target /\ rqS.cr_data = rqT.cr_data` by
    simp[Abbr `rqS`, Abbr `rqT`, venom_create_request_def] >>
  drule ld_take_outcome_success_cong >>
  disch_then (qspec_then `t.vs_outcomes` assume_tac) >>
  drule ld_take_outcome_returndata_cong >>
  disch_then (qspec_then `t.vs_outcomes` assume_tac) >>
  drule ld_take_outcome_created_cong >>
  disch_then (qspec_then `t.vs_outcomes` assume_tac) >>
  Cases_on `consume_create_outcome rqS s` >>
  Cases_on `consume_create_outcome rqT t` >>
  gvs[exec_create_def, Abbr `rqT`,
      Excl "consume_create_outcome_eq", AllCaseEqs()] >>
  gvs[consume_create_outcome_eq]
QED

(* Concrete EVM completion does not consult the caller's memory when
   selecting its word and returndata; it only writes the selected bytes. *)
Theorem ld_extract_result_backward:
  extract_venom_result t v roT rs result = SOME (w,rT) ==>
  ?rS.
    extract_venom_result s v roS rs result = SOME (w,rS) /\
    rS.vs_returndata = rT.vs_returndata /\
    rS.vs_memory = (write_memory_with_expansion roS
      (TAKE rs rT.vs_returndata) s).vs_memory /\
    rT.vs_memory = (write_memory_with_expansion roT
      (TAKE rs rT.vs_returndata) t).vs_memory
Proof
  Cases_on `result` >- simp[extract_venom_result_def] >>
  rename1 `SOME p` >> PairCases_on `p` >>
  Cases_on `p1.contexts` >- simp[extract_venom_result_def] >>
  rename1 `p1.contexts = h::rest` >>
  Cases_on `rest` >> simp[extract_venom_result_def] >>
  PairCases_on `h` >>
  Cases_on `p0`
  >- (simp[extract_venom_result_def] >> rpt strip_tac >> gvs[]) >>
  Cases_on `y` >> simp[extract_venom_result_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ld_exec_delegatecall_backward:
  ld_shared_state tn un s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n offS) (w2n sz) s =
    read_memory (w2n offT) (w2n sz) t /\
  exec_delegatecall i t gas addr offT sz roT rs = OK t' ==>
  ?out w rS rT.
    i.inst_outputs = [out] /\ t' = update_var out w rT /\
    exec_delegatecall i s gas addr offS sz (roS:bytes32) rs = OK (update_var out w rS) /\
    rS.vs_returndata = rT.vs_returndata /\
    rS.vs_memory = (write_memory_with_expansion (w2n roS)
      (TAKE (w2n rs) rT.vs_returndata) s).vs_memory /\
    rT.vs_memory = (write_memory_with_expansion (w2n roT)
      (TAKE (w2n rs) rT.vs_returndata) t).vs_memory
Proof
  strip_tac >> drule_all ld_delegatecall_run_shared >>
  disch_then (qspecl_then [`w2w addr`, `w2n gas`] assume_tac) >>
  gvs[exec_delegatecall_def, AllCaseEqs()] >>
  drule ld_extract_result_backward >>
  disch_then (qspecl_then [`s`, `w2n roS`] strip_assume_tac) >>
  qexistsl [`output`, `rS`, `s''`] >> simp[]
QED

(* Matching operand interfaces permit input/output offsets to move. CALL's
   value guard is read from the target OK step and replayed, not assumed. *)
Theorem ld_call_step_backward:
  ((i.inst_opcode = CALL /\
      i.inst_operands = [gop;adop;vop;offop;szop;rop;rsop] /\
      eval_operand vop s = SOME value /\ eval_operand vop t = SOME value /\
      static = t.vs_call_ctx.cc_static) \/
   (i.inst_opcode = STATICCALL /\
      i.inst_operands = [gop;adop;offop;szop;rop;rsop] /\
      value = 0w /\ static = T)) /\
  eval_operand gop s = SOME gas /\ eval_operand gop t = SOME gas /\
  eval_operand adop s = SOME addr /\ eval_operand adop t = SOME addr /\
  eval_operand offop s = SOME offS /\ eval_operand offop t = SOME offT /\
  eval_operand szop s = SOME sz /\ eval_operand szop t = SOME sz /\
  eval_operand rop s = SOME roS /\ eval_operand rop t = SOME roT /\
  eval_operand rsop s = SOME rs /\ eval_operand rsop t = SOME rs /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  read_memory (w2n offS) (w2n sz) s = read_memory (w2n offT) (w2n sz) t /\
  s.vs_outcomes = t.vs_outcomes /\ step_inst fuel CT i t = OK t' ==>
  ?out w rS rT.
    i.inst_outputs = [out] /\ t' = update_var out w rT /\
    step_inst fuel CS i s = OK (update_var out w rS) /\
    consume_call_outcome (venom_call_request s addr value offS sz static)
      (w2n roS) (w2n rs) s = (w,rS) /\
    consume_call_outcome (venom_call_request t addr value offT sz static)
      (w2n roT) (w2n rs) t = (w,rT) /\
    rS.vs_returndata = rT.vs_returndata /\
    rS.vs_memory = (write_memory_with_expansion (w2n roS)
      (TAKE (w2n rs) rT.vs_returndata) s).vs_memory /\
    rT.vs_memory = (write_memory_with_expansion (w2n roT)
      (TAKE (w2n rs) rT.vs_returndata) t).vs_memory
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
       Excl "consume_call_outcome_eq"] >>
  rpt IF_CASES_TAC >> simp[Excl "consume_call_outcome_eq"] >> strip_tac >>
  drule_all ld_exec_ext_call_backward >>
  disch_then (qspec_then `roS` strip_assume_tac) >>
  qexistsl [`out`, `w`, `rS`, `rT`] >>
  simp[Excl "consume_call_outcome_eq"]
QED

Theorem ld_create_step_backward:
  ((i.inst_opcode = CREATE /\ i.inst_operands = [vop;offop;szop] /\ salt = NONE) \/
   (i.inst_opcode = CREATE2 /\ i.inst_operands = [vop;offop;szop;saltop] /\
      salt = SOME saltword /\ eval_operand saltop s = SOME saltword /\
      eval_operand saltop t = SOME saltword)) /\
  eval_operand vop s = SOME value /\ eval_operand vop t = SOME value /\
  eval_operand offop s = SOME offS /\ eval_operand offop t = SOME offT /\
  eval_operand szop s = SOME sz /\ eval_operand szop t = SOME sz /\
  s.vs_call_ctx.cc_static = t.vs_call_ctx.cc_static /\
  read_memory (w2n offS) (w2n sz) s = read_memory (w2n offT) (w2n sz) t /\
  s.vs_outcomes = t.vs_outcomes /\ step_inst fuel CT i t = OK t' ==>
  ?out w rS rT.
    i.inst_outputs = [out] /\ t' = update_var out w rT /\
    step_inst fuel CS i s = OK (update_var out w rS) /\
    consume_create_outcome (venom_create_request s value offS sz salt) s = (w,rS) /\
    consume_create_outcome (venom_create_request t value offT sz salt) t = (w,rT) /\
    rS.vs_returndata = rT.vs_returndata /\
    rS.vs_memory = s.vs_memory /\ rT.vs_memory = t.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, eval_operands_def,
       Excl "consume_create_outcome_eq"] >>
  rpt IF_CASES_TAC >> simp[Excl "consume_create_outcome_eq"] >> strip_tac >>
  drule_all ld_exec_create_backward >> strip_tac >>
  qexistsl [`out`, `w`, `rS`, `rT`] >>
  simp[Excl "consume_create_outcome_eq"]
QED

Theorem ld_delegatecall_step_backward:
  i.inst_opcode = DELEGATECALL /\
  i.inst_operands = [gop;adop;offop;szop;rop;rsop] /\
  eval_operand gop s = SOME gas /\ eval_operand gop t = SOME gas /\
  eval_operand adop s = SOME addr /\ eval_operand adop t = SOME addr /\
  eval_operand offop s = SOME offS /\ eval_operand offop t = SOME offT /\
  eval_operand szop s = SOME sz /\ eval_operand szop t = SOME sz /\
  eval_operand rop s = SOME roS /\ eval_operand rop t = SOME roT /\
  eval_operand rsop s = SOME rs /\ eval_operand rsop t = SOME rs /\
  ld_shared_state tn un s t /\ tn.t_stor = {} /\ tn.t_trans = {} /\
  read_memory (w2n offS) (w2n sz) s = read_memory (w2n offT) (w2n sz) t /\
  step_inst fuel CT i t = OK t' ==>
  ?out w rS rT.
    i.inst_outputs = [out] /\ t' = update_var out w rT /\
    step_inst fuel CS i s = OK (update_var out w rS) /\
    rS.vs_returndata = rT.vs_returndata /\
    rS.vs_memory = (write_memory_with_expansion (w2n roS)
      (TAKE (w2n rs) rT.vs_returndata) s).vs_memory /\
    rT.vs_memory = (write_memory_with_expansion (w2n roT)
      (TAKE (w2n rs) rT.vs_returndata) t).vs_memory
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs] >> strip_tac >>
  drule_all ld_exec_delegatecall_backward >>
  disch_then (qspec_then `roS` strip_assume_tac) >>
  qexistsl [`out`, `w`, `rS`, `rT`] >> simp[]
QED
