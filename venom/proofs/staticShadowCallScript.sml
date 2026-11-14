Theory staticShadowCall
Ancestors
  staticShadowFrame staticShadowPrim staticShadowDefs venomExecSemantics
  venomCallOracleDefs extCallOracle venomState venomInst list
Libs
  stepInstBaseLib

Theorem static_shadow_take_outcome[local]:
  rq.cr_accounts = a /\ rq.cr_tStorage = ts ==>
  take_outcome (rq with cr_static := b)
    (MAP (\co. co with <| co_accounts := a;
       co_tStorage := ts; co_logs := []; co_toDelete := [] |>) os) =
  ((FST (take_outcome rq os)) with <| co_accounts := a;
       co_tStorage := ts; co_logs := []; co_toDelete := [] |>,
   MAP (\co. co with <| co_accounts := a;
       co_tStorage := ts; co_logs := []; co_toDelete := [] |>)
       (SND (take_outcome rq os)))
Proof
  strip_tac >> gvs[] >> Cases_on `os` >> simp[take_outcome_def, computed_precompile_def,
    failed_outcome_def] >>
  Cases_on `rq.cr_kind = MessageCall /\ rq.cr_value = 0` >> simp[] >>
  Cases_on `precompile_result rq.cr_target rq.cr_data` >> gvs[] >>
  Cases_on `x` >> gvs[] >>
  Cases_on `h.co_success` >> simp[] >> rpt IF_CASES_TAC >> simp[]
QED

Theorem static_shadow_consume_call[local]:
  static_shadow_rel s sh /\ s.vs_call_ctx.cc_static /\ rq.cr_static /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient ==>
  FST (consume_call_outcome (rq with cr_static := b) ro rz sh) =
    FST (consume_call_outcome rq ro rz s) /\
  static_shadow_rel (SND (consume_call_outcome rq ro rz s))
    (SND (consume_call_outcome (rq with cr_static := b) ro rz sh)) /\
  (SND (consume_call_outcome rq ro rz s)).vs_call_ctx.cc_static
Proof
  strip_tac >>
  drule (iffLR static_shadow_rel_normal_form) >> strip_tac >> gvs[] >>
  simp[static_shadow_def,
       consume_call_outcome_eq, static_shadow_take_outcome] >>
  simp[adopt_outcome_def, adopt_outcome_deletions_def,
       static_shadow_rel_def, static_shadow_def, record_request_def,
       computed_precompile_def, MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF,
       write_memory_with_expansion_def, venom_state_component_equality] >>
  IF_CASES_TAC >> simp[MAP_APPEND]
QED

Theorem static_shadow_call_output[local]:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh /\ rq.cr_static /\
  rq.cr_accounts = s.vs_accounts /\ rq.cr_tStorage = s.vs_transient ==>
  static_shadow_result_rel
    (let (w,t) = consume_call_outcome rq ro rz s in
      case outs of [out] => OK (update_var out w t) | _ => Error msg)
    (let (w,t) = consume_call_outcome (rq with cr_static := b) ro rz sh in
      case outs of [out] => OK (update_var out w t) | _ => Error msg)
Proof
  strip_tac >>
  `FST (consume_call_outcome (rq with cr_static := b) ro rz sh) =
     FST (consume_call_outcome rq ro rz s) /\
   static_shadow_rel (SND (consume_call_outcome rq ro rz s))
     (SND (consume_call_outcome (rq with cr_static := b) ro rz sh)) /\
   (SND (consume_call_outcome rq ro rz s)).vs_call_ctx.cc_static` by
    (irule static_shadow_consume_call >> simp[]) >>
  namedCases_on `outs` ["", "out rest"] >>
  simp[static_shadow_result_rel_def, Excl "consume_call_outcome_eq"] >>
  Cases_on `rest` >>
  simp[static_shadow_result_rel_def, Excl "consume_call_outcome_eq"] >>
  rpt (pairarg_tac >> gvs[Excl "consume_call_outcome_eq"]) >>
  simp[static_shadow_rel_update_var, update_var_def,
       Excl "consume_call_outcome_eq"]
QED

Theorem static_shadow_exec_ext_call[local]:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel
    (exec_ext_call inst s gas addr value ao az ro rz i)
    (exec_ext_call inst sh gas addr value ao az ro rz j)
Proof
  strip_tac >>
  `venom_call_request sh addr value ao az j =
     venom_call_request s addr value ao az i with cr_static := j` by
    (drule static_shadow_rel_fields >>
     gvs[venom_call_request_def, read_memory_def, static_shadow_rel_def,
         static_shadow_def, venom_state_component_equality]) >>
  simp[exec_ext_call_def, Excl "consume_call_outcome_eq"] >>
  irule (SRULE [LET_THM, Excl "consume_call_outcome_eq"]
    static_shadow_call_output) >> simp[venom_call_request_def]
QED

Theorem static_shadow_exec_delegatecall[local]:
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel
    (exec_delegatecall inst s gas addr ao az ro rz)
    (exec_delegatecall inst sh gas addr ao az ro rz)
Proof
  strip_tac >>
  qabbrev_tac `rq = venom_call_request s addr 0w ao az F with
    cr_kind := DelegateMessageCall` >>
  `venom_call_request sh addr 0w ao az F with cr_kind := DelegateMessageCall =
     rq with cr_static := F` by
    (drule static_shadow_rel_fields >>
     gvs[Abbr `rq`, venom_call_request_def, read_memory_def, static_shadow_rel_def,
         static_shadow_def, venom_state_component_equality]) >>
  simp[exec_delegatecall_def, Excl "consume_call_outcome_eq"] >>
  irule (SRULE [LET_THM, Excl "consume_call_outcome_eq"]
    static_shadow_call_output) >> simp[Abbr `rq`, venom_call_request_def]
QED

Theorem static_shadow_calls:
  MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL] /\
  s.vs_call_ctx.cc_static /\ static_shadow_rel s sh ==>
  static_shadow_result_rel (step_inst_base inst s) (step_inst_base inst sh)
Proof
  strip_tac >>
  `!op. eval_operand op sh = eval_operand op s` by
    metis_tac[static_shadow_rel_eval_operand] >>
  `~sh.vs_call_ctx.cc_static` by
    (drule static_shadow_rel_fields >> simp[]) >>
  fs[] >> with_opcode_clause simp >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[static_shadow_exec_ext_call, static_shadow_exec_delegatecall,
       Excl "consume_call_outcome_eq"] >>
  simp[static_shadow_result_rel_def]
QED
