(* Shared adoption and return-buffer transport boundaries. *)
Theory o1LowerDloadExternalEffects
Ancestors o1LowerDloadExternalOracle o1LowerDloadShared
  o1LowerDloadRangeTransport venomCallOracleDefs extCallOracle
  ptrDiscipline venomState finite_map list pred_set

Theorem ld_consume_call_outcome_shared_effects:
  ld_shared_agree D A tn s t /\ request_agree_except D rq1 rq2 /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq1 ro1 rs1 s = (w1,s1) /\
  consume_call_outcome rq2 ro2 rs2 t = (w2,t1) ==>
  ld_shared_agree D A
    (tn with <|t_stor := if s1.vs_accounts <> s.vs_accounts then {} else tn.t_stor;
               t_trans := if s1.vs_transient <> s.vs_transient then {} else tn.t_trans|>)
    s1 t1 /\
  ld_shared_agree D A
    (tn with <|t_stor := if ~rq1.cr_static /\ s1.vs_requests <> s.vs_requests /\
                    s1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
                  then {} else tn.t_stor;
               t_trans := if ~rq1.cr_static /\ s1.vs_requests <> s.vs_requests /\
                    s1.vs_outcomes <> s.vs_outcomes /\ (HD s.vs_outcomes).co_success
                  then {} else tn.t_trans|>) s1 t1
Proof
  strip_tac >>
  `rq1.cr_target = rq2.cr_target /\ rq1.cr_value = rq2.cr_value /\
   rq1.cr_data = rq2.cr_data /\ rq1.cr_static = rq2.cr_static /\
   rq1.cr_kind = rq2.cr_kind` by
    fs[request_agree_except_def, call_request_component_equality] >>
  `computed_precompile rq1 = computed_precompile rq2` by
    simp[computed_precompile_def] >>
  `s.vs_outcomes = t.vs_outcomes` by fs[ld_shared_agree_def] >>
  Cases_on `computed_precompile rq2`
  >- (Cases_on `t.vs_outcomes` >>
      gvs[consume_call_outcome_eq, take_outcome_def, record_request_def,
          adopt_outcome_def, adopt_outcome_deletions_def, failed_outcome_def,
          ld_shared_agree_def] >>
      Cases_on `precompile_result rq2.cr_target rq2.cr_data`
      >- gvs[adopt_outcome_def, adopt_outcome_deletions_def, failed_outcome_def] >>
      rename1 `precompile_result _ _ = SOME x` >> Cases_on `x` >>
      gvs[adopt_outcome_def, adopt_outcome_deletions_def, failed_outcome_def] >>
      Cases_on `h.co_success` >>
      gvs[adopt_outcome_def, adopt_outcome_deletions_def, failed_outcome_def]) >>
  Cases_on `t.vs_outcomes` >>
  gvs[consume_call_outcome_eq, take_outcome_def, record_request_def,
      adopt_outcome_def, adopt_outcome_deletions_def, failed_outcome_def] >>
  gvs[ld_shared_agree_def, LIST_REL_APPEND] >>
  rename1 `h.co_success` >>
  Cases_on `h.co_success /\ ~rq2.cr_static` >>
  gvs[] >>
  simp[word_agree_except_def] >>
  rpt strip_tac >> rpt IF_CASES_TAC >> gvs[word_agree_except_def]
QED

Theorem ld_consume_call_outcome_shared:
  ld_shared_agree D A tn s t /\ request_agree_except D rq1 rq2 /\
  rq1.cr_accounts = s.vs_accounts /\ rq2.cr_accounts = t.vs_accounts /\
  rq1.cr_tStorage = s.vs_transient /\ rq2.cr_tStorage = t.vs_transient /\
  consume_call_outcome rq1 ro1 rs1 s = (w1,s1) /\
  consume_call_outcome rq2 ro2 rs2 t = (w2,t1) ==>
  ld_shared_agree D A
    (tn with <|t_stor := if s1.vs_accounts <> s.vs_accounts then {} else tn.t_stor;
               t_trans := if s1.vs_transient <> s.vs_transient then {} else tn.t_trans|>)
    s1 t1
Proof
  metis_tac[ld_consume_call_outcome_shared_effects]
QED

Theorem ld_memory_agree_return_buffer:
  k = MIN rs (LENGTH bs) /\
  ld_memory_agree sites lo mask s.vs_memory t.vs_memory /\
  ld_joint_geometry sites X lo owners /\
  (k=0 \/ (p=q /\ p+k<=lo) \/
   (?id b c z j. FLOOKUP sites id = SOME (b,c,z) /\ j+k<=z /\
                 p=b+j /\ q=c+j)) ==>
  ld_memory_agree sites lo (mask DIFF {i | p<=i /\ i<p+k})
    (write_memory_with_expansion p (TAKE rs bs) s).vs_memory
    (write_memory_with_expansion q (TAKE rs bs) t).vs_memory
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  `LENGTH (TAKE rs bs) = k` by
    (Cases_on `rs <= LENGTH bs` >> gvs[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF]) >>
  Cases_on `k=0`
  >- (`TAKE rs bs = []` by metis_tac[LENGTH_NIL] >>
      gvs[] >> irule ld_memory_agree_empty_write >> simp[]) >>
  qpat_assum `LENGTH (TAKE rs bs) = _` (fn th => once_rewrite_tac[GSYM th]) >>
  drule_at (Pat `ld_joint_geometry _ _ _ _`) ld_memory_agree_clean_write >>
  disch_then irule >> simp[] >> metis_tac[]
QED

(* Exact CREATE requests select the same created address and adopted fields.
   Each run retains its own locals and appends to its own request history. *)
Theorem ld_consume_create_outcome_transport:
  s.vs_outcomes = t.vs_outcomes /\ s.vs_accounts = t.vs_accounts /\
  s.vs_transient = t.vs_transient /\ s.vs_logs = t.vs_logs /\
  s.vs_pending_deletions = t.vs_pending_deletions /\
  consume_create_outcome rq s = (w,r) ==>
  r = s with <|vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
    vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
    vs_pending_deletions := r.vs_pending_deletions;
    vs_returndata := r.vs_returndata;
    vs_requests := record_request rq s.vs_requests|> /\
  consume_create_outcome rq t = (w,t with <|
    vs_accounts := r.vs_accounts; vs_transient := r.vs_transient;
    vs_logs := r.vs_logs; vs_outcomes := r.vs_outcomes;
    vs_pending_deletions := r.vs_pending_deletions;
    vs_returndata := r.vs_returndata;
    vs_requests := record_request rq t.vs_requests|>)
Proof
  simp[consume_create_outcome_eq] >> strip_tac >> gvs[] >>
  simp[venom_state_fupdcanon]
QED
