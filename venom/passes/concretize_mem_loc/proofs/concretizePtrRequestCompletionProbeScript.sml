Theory concretizePtrRequestCompletionProbe
Ancestors concretizePtrRequestHistory venomCallOracleDefs concretizePtrSharedFields
  concretizePtrTaintContent concretizePtrOpaqueRetpc
  ptrDiscipline venomState extCallOracle finite_map list words pred_set

(* This is the source guard in step_taint, not outcome-store equality. *)
Definition ptr_call_adopted_def:
  ptr_call_adopted s u <=>
    ~s.vs_call_ctx.cc_static /\ u.vs_requests <> s.vs_requests /\
    u.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
End

Theorem ptr_history_call_shell:
  ptr_history_content tn s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n at) (w2n az) t ==>
  ptr_request_shell (venom_call_request s addr value ao az st)
    (venom_call_request t addr value at az st)
Proof
  simp[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
       ptr_core_shared_def, ptr_shared_fields_def, venom_call_request_def,
       ptr_request_shell_def]
QED

Theorem ptr_call_completion_adopted:
  consume_call_outcome (venom_call_request s addr value ao az st) ro rz s = (w,u) ==>
  (ptr_call_adopted s u <=>
    ~s.vs_call_ctx.cc_static /\
    ~computed_precompile (venom_call_request s addr value ao az st) /\
    s.vs_outcomes <> [] /\ (HD s.vs_outcomes).co_success)
Proof
  simp[consume_call_outcome_eq] >> strip_tac >> gvs[ptr_call_adopted_def] >>
  Cases_on `s.vs_outcomes` >> simp[take_outcome_def, record_request_def] >>
  Cases_on `computed_precompile (venom_call_request s addr value ao az st)` >>
  simp[] >>
  metis_tac[LENGTH, LENGTH_APPEND, DECIDE ``!n:num. n + 1 <> n``,
            DECIDE ``!n:num. n <> SUC n``]
QED

Theorem ptr_history_completion_guard:
  ptr_history_content tn s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n at) (w2n az) t /\
  consume_call_outcome (venom_call_request s addr value ao az st) ro rz s = (w,u) /\
  consume_call_outcome (venom_call_request t addr value at az st) rt rz t = (v,z) ==>
  (ptr_call_adopted s u <=> ptr_call_adopted t z)
Proof
  strip_tac >>
  `ptr_request_shell (venom_call_request s addr value ao az st)
     (venom_call_request t addr value at az st)` by
    (irule ptr_history_call_shell >> metis_tac[]) >>
  drule ptr_request_shell_classification >>
  drule ptr_call_completion_adopted >>
  rev_drule ptr_call_completion_adopted >>
  gvs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
      ptr_core_shared_def, ptr_shared_fields_def]
QED

Theorem ptr_history_call_completion:
  ptr_history_content tn s t /\
  read_memory (w2n ao) (w2n az) s = read_memory (w2n at) (w2n az) t /\
  consume_call_outcome (venom_call_request s addr value ao az st) ro rz s = (w,u) /\
  consume_call_outcome (venom_call_request t addr value at az st) rt rz t = (v,z) ==>
  w = v /\ u.vs_returndata = z.vs_returndata /\
  ptr_history_content
    (tn with <| t_stor := if ~st /\ ptr_call_adopted s u then {} else tn.t_stor;
                t_trans := if ~st /\ ptr_call_adopted s u then {} else tn.t_trans |>) u z
Proof
  strip_tac >>
  `ptr_request_shell (venom_call_request s addr value ao az st)
     (venom_call_request t addr value at az st)` by
    (irule ptr_history_call_shell >> metis_tac[]) >>
  `ptr_request_history
     (record_request (venom_call_request s addr value ao az st) s.vs_requests)
     (record_request (venom_call_request t addr value at az st) t.vs_requests)` by
    (irule ptr_request_record >> gvs[ptr_history_content_def]) >>
  `ptr_call_adopted s u <=>
    ~s.vs_call_ctx.cc_static /\
    ~computed_precompile (venom_call_request s addr value ao az st) /\
    s.vs_outcomes <> [] /\ (HD s.vs_outcomes).co_success` by
    (irule ptr_call_completion_adopted >> metis_tac[]) >>
  fs[ptr_history_content_def, ptr_taint_content_def, ptr_taint_control_def,
     ptr_core_shared_def, ptr_shared_fields_def] >>
  gvs[consume_call_outcome_eq] >>
  Cases_on `t.vs_outcomes` >>
  simp[take_outcome_def, failed_outcome_def] >>
  gvs[venom_call_request_def, adopt_outcome_def, adopt_outcome_deletions_def,
      contract_storage_def, contract_transient_def] >>
  Cases_on `precompile_result (w2w addr) (read_memory (w2n at) (w2n az) t)` >>
  gvs[computed_precompile_def, take_outcome_def, failed_outcome_def] >>
  Cases_on `st` >> Cases_on `t.vs_call_ctx.cc_static` >>
  Cases_on `h.co_success` >>
  gvs[storage_agree_except_def, word_agree_except_def] >>
  Cases_on `w2n value = 0` >> gvs[] >>
  rename1 `precompile_result _ _ = SOME pc` >> Cases_on `pc` >>
  gvs[failed_outcome_def, storage_agree_except_def, word_agree_except_def,
      venom_call_request_def]
QED

(* A masked storage write commutes with the historical-request quotient. *)
Theorem ptr_history_sstore:
  ptr_history_content tn s t /\ word_agree_except m u v ==>
  ptr_history_content (tn with t_stor := key_update tn.t_stor k m)
    (sstore k u s) (sstore k v t)
Proof
  simp[ptr_history_content_def] >> strip_tac >>
  drule_all ptr_taint_content_sstore >>
  disch_then (qspec_then `k` mp_tac) >> simp[sstore_def]
QED

(* Real completion after unequal, fully tainted writes; a later common
   overwrite clears the current mask, without editing either history. *)
Theorem ptr_request_store_call_overwrite_probe:
  s.vs_outcomes = [] /\
  ~computed_precompile (venom_call_request (sstore k 1w s) addr 0w 0w 0w F) /\
  consume_call_outcome
    (venom_call_request (sstore k 1w s) addr 0w 0w 0w F)
    0 0 (sstore k 1w s) = (w,u) /\
  consume_call_outcome
    (venom_call_request (sstore k 2w s) addr 0w 0w 0w F)
    0 0 (sstore k 2w s) = (v,z) ==>
  ptr_history_content (tn with t_stor := key_update tn.t_stor k {b | b < 32}) u z /\
  ptr_history_content
    (tn with t_stor := key_update (key_update tn.t_stor k {b | b < 32}) k {})
    (sstore k 0w u) (sstore k 0w z) /\
  (sstore k 0w u).vs_requests = u.vs_requests /\
  (sstore k 0w z).vs_requests = z.vs_requests /\
  key_taint (key_update (key_update tn.t_stor k {b | b < 32}) k {}) k = {} /\
  u.vs_requests = s.vs_requests ++
    [venom_call_request (sstore k 1w s) addr 0w 0w 0w F] /\
  z.vs_requests = s.vs_requests ++
    [venom_call_request (sstore k 2w s) addr 0w 0w 0w F]
Proof
  strip_tac >>
  `ptr_history_content
     (tn with t_stor := key_update tn.t_stor k {b | b < 32})
     (sstore k 1w s) (sstore k 2w s)` by
    (irule ptr_history_sstore >> simp[word_agree_except_def]) >>
  `read_memory (w2n (0w:bytes32)) (w2n (0w:bytes32)) (sstore k 1w s) =
   read_memory (w2n (0w:bytes32)) (w2n (0w:bytes32)) (sstore k 2w s)` by
    simp[read_memory_def] >>
  `~ptr_call_adopted (sstore k 1w s) u` by
    (qpat_assum `consume_call_outcome _ _ _ _ = (w,u)` mp_tac >>
     simp[consume_call_outcome_eq, sstore_def, take_outcome_def] >>
     strip_tac >> gvs[ptr_call_adopted_def, take_outcome_def]) >>
  drule_all ptr_history_call_completion >> simp[] >> strip_tac >>
  conj_tac >- (
    qpat_assum `ptr_history_content _ u z`
      (mp_then Any mp_tac ptr_history_sstore) >>
    disch_then (qspecl_then [`0w`, `0w`, `{}`, `k`] mp_tac) >>
    simp[word_agree_except_def]) >>
  simp[sstore_def, key_taint_def, key_update_def, EXTENSION] >>
  `~computed_precompile (venom_call_request (sstore k 2w s) addr 0w 0w 0w F)` by
    gvs[computed_precompile_def, venom_call_request_def, sstore_def, read_memory_def] >>
  qpat_x_assum `consume_call_outcome _ _ _ _ = (w,u)` mp_tac >>
  qpat_x_assum `consume_call_outcome _ _ _ _ = (v,z)` mp_tac >>
  simp[consume_call_outcome_eq, take_outcome_def, record_request_def, sstore_def] >>
  rpt strip_tac >> gvs[]
QED
