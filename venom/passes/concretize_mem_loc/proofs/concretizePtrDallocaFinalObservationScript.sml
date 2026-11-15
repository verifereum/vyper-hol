Theory concretizePtrDallocaFinalObservation
Ancestors
  concretizePtrDallocaObservationTransport concretizePtrRequestHistory
  concretizePtrTaintContent lowerDloadTerminalObservation
  ptrDiscipline venomState finite_map pred_set

(* The outgoing content uses the actual source poststate and the target
   observation after its cursor update, which leaves requests unchanged. *)
Theorem ptr_dalloca_actual_request_observation:
  dead_wf D /\ taint_within D CS vs /\
  frame_reachable vs CS stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel CS inst s = OK post /\
  ptr_history_content tn s t /\ ptr_history_content nextn post nextt /\
  LENGTH t.vs_requests < LENGTH nextt.vs_requests /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans ==>
  un.t_stor SUBSET D.d_stor t.vs_call_ctx.cc_address
    (t.vs_accounts t.vs_call_ctx.cc_address).storage /\
  un.t_trans SUBSET D.d_trans t.vs_call_ctx.cc_address
    (t.vs_transient t.vs_call_ctx.cc_address)
Proof
  strip_tac >>
  `LENGTH s.vs_requests < LENGTH post.vs_requests` by
    (qpat_assum `ptr_history_content tn s t`
       (mp_tac o MATCH_MP ptr_history_content_request_lengths) >>
     qpat_assum `ptr_history_content nextn post nextt`
       (mp_tac o MATCH_MP ptr_history_content_request_lengths) >> simp[]) >>
  `tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
      (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
   tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
      (s.vs_transient s.vs_call_ctx.cc_address)` by
    (qpat_assum `taint_within D CS vs`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [taint_within_def]) >>
     disch_then (qspecl_then [`stk`,`PG`,`G`,`tn`,`fn`,`inst`,`s`,`fuel`,`post`]
       mp_tac) >> simp[]) >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (qpat_assum `ptr_history_content tn s t`
       (mp_tac o MATCH_MP ptr_history_content_call_ctx) >> simp[]) >>
  qpat_assum `ptr_history_content tn s t`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [ptr_history_content_def, ptr_taint_content_def,
       contract_storage_def, contract_transient_def,
       vfmStateTheory.lookup_account_def]) >>
  mp_tac (Q.INST [`tt` |-> `un`] ptr_dalloca_request_taint_transport) >>
  (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[])) >> simp[]
QED

(* Persistent masks at a terminal event are transported only after the
   actual source final_taint witness and both successful Halt steps exist. *)
Theorem ptr_dalloca_actual_final_observation:
  dead_wf D /\ taint_within D CS vs /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel CS inst s = Halt sh /\
  it.inst_opcode <> INVOKE /\ step_inst fuelt CT it t = Halt th /\
  final_taint vs CS sh (step_taint inst s sh tn) (ret_taint tn inst s) /\
  ptr_history_content tn s t /\
  un.t_stor SUBSET tn.t_stor /\ un.t_trans SUBSET tn.t_trans /\
  un.t_imm SUBSET tn.t_imm /\
  ret_taint un it t SUBSET ret_taint tn inst s /\
  LENGTH sh.vs_returndata = LENGTH th.vs_returndata /\
  (!i. i < LENGTH sh.vs_returndata /\ i NOTIN ret_taint tn inst s ==>
    EL i sh.vs_returndata = EL i th.vs_returndata) ==>
  (step_taint it t th un).t_stor SUBSET D.d_stor th.vs_call_ctx.cc_address
    (th.vs_accounts th.vs_call_ctx.cc_address).storage /\
  (step_taint it t th un).t_trans SUBSET D.d_trans th.vs_call_ctx.cc_address
    (th.vs_transient th.vs_call_ctx.cc_address) /\
  (step_taint it t th un).t_imm SUBSET D.d_imm th.vs_immutables /\
  ret_taint un it t SUBSET D.d_ret th.vs_returndata
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `taint_within D CS vs`
    (mp_tac o CONJUNCT2 o REWRITE_RULE [taint_within_def]) >>
  disch_then (qspecl_then [`sh`,`step_taint inst s sh tn`,`ret_taint tn inst s`]
    mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.INST [`i` |-> `inst`, `C` |-> `CS`, `s` |-> `s`,
    `sh` |-> `sh`, `tn` |-> `tn`, `fuel` |-> `fuel`]
    ld_noninvoke_halt_persistent) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  mp_tac (Q.INST [`i` |-> `it`, `C` |-> `CT`, `s` |-> `t`,
    `sh` |-> `th`, `tn` |-> `un`, `fuel` |-> `fuelt`]
    ld_noninvoke_halt_persistent) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `s.vs_call_ctx = t.vs_call_ctx` by
    (drule ptr_history_content_call_ctx >> simp[]) >>
  qpat_assum `ptr_history_content tn s t`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [ptr_history_content_def, ptr_taint_content_def,
       contract_storage_def, contract_transient_def,
       vfmStateTheory.lookup_account_def]) >>
  `!k. k IN FDOM s.vs_immutables ==>
    word_agree_except {b | (k,b) IN tn.t_imm}
      (s.vs_immutables ' k) (t.vs_immutables ' k)` by
    (rpt strip_tac >>
     `k IN FDOM t.vs_immutables` by
       (qpat_assum `FDOM s.vs_immutables = FDOM t.vs_immutables`
          (fn thm => once_rewrite_tac[GSYM thm]) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!k u v. FLOOKUP s.vs_immutables k = SOME u /\
       FLOOKUP t.vs_immutables k = SOME v ==> _`
       (qspecl_then [`k`,`s.vs_immutables ' k`,`t.vs_immutables ' k`] mp_tac) >>
     (impl_tac >- simp[FLOOKUP_DEF]) >> disch_then ACCEPT_TAC) >>
  qpat_assum `s.vs_call_ctx = t.vs_call_ctx`
    (fn eq => RULE_ASSUM_TAC (REWRITE_RULE [eq])) >>
  qpat_assum `FDOM s.vs_immutables = FDOM t.vs_immutables`
    (fn eq => RULE_ASSUM_TAC (REWRITE_RULE [eq]) >> assume_tac eq) >>
  mp_tac (Q.INST [`s` |-> `sh`, `t` |-> `th`,
    `tn` |-> `step_taint inst s sh tn`, `tt` |-> `step_taint it t th un`,
    `R` |-> `ret_taint tn inst s`, `Rt` |-> `ret_taint un it t`]
    ptr_dalloca_final_taint_transport) >>
  (impl_tac >- (rpt conj_tac >> asm_rewrite_tac[])) >>
  disch_then ACCEPT_TAC
QED
