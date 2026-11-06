Theory concretizePtrActualWrites
Ancestors ptrDiscipline memLocDefs codegenRel concretizeMemLocDefs
  concretizePtrChronologicalHistory concretizePtrLifetime list rich_list

Theorem ptr_exact_size_step_writes:
  inst_write_size inst = SOME n ==>
  step_writes inst s post = source_memory_write_ranges inst s
Proof
  Cases_on `inst.inst_opcode = CALL` >-
    (simp[inst_write_size_def, mem_write_ops_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  Cases_on `inst.inst_opcode = STATICCALL` >-
    (simp[inst_write_size_def, mem_write_ops_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  Cases_on `inst.inst_opcode = DELEGATECALL` >-
    (simp[inst_write_size_def, mem_write_ops_def] >>
     rpt strip_tac >> gvs[AllCaseEqs()]) >>
  simp[step_writes_def]
QED

Theorem ptr_chrono_step_actual_mem:
  !ctx a b. ptr_chrono_step ctx a b ==>
    !x. x IN a.po_taint.t_mem /\ x NOTIN b.po_taint.t_mem ==>
      x IN range_bytes (step_writes a.po_inst a.po_state b.po_state)
Proof
  ho_match_mp_tac ptr_chrono_step_ind >> rpt conj_tac
  >- (simp[ptr_observe_def, step_taint_def, mem_taint_def,
           step_writes_def] >> SET_TAC[]) 
  >- (simp[ptr_observe_def, entry_taint_vars_def] >>
      rpt gen_tac >> CASE_TAC >> simp[]) >>
  simp[ptr_observe_def]
QED

(* Finite backward selection: the final actual write has a pure successor. *)
Theorem ptr_last_actual_index[local]:
  !j i. i <= j /\ tainted i /\ ~tainted j /\
    (!k. i <= k /\ k < j ==> tainted k /\ ~tainted (SUC k) ==> writes k) ==>
    ?w. i <= w /\ w < j /\ writes w /\ ~tainted (SUC w) /\
        (!k. w < k /\ k < j ==> ~writes k)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  Cases_on `i = SUC j` >- gvs[] >>
  `i <= j` by decide_tac >>
  Cases_on `writes j`
  >- (qexists `j` >> simp[] >> rpt strip_tac >> decide_tac) >>
  `~tainted j` by
    (qpat_x_assum `!k. _` (qspec_then `j` mp_tac) >> simp[]) >>
  `?w. i <= w /\ w < j /\ writes w /\ ~tainted (SUC w) /\
        (!k. w < k /\ k < j ==> ~writes k)` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> simp[]) >>
  qexists `w` >> simp[] >> rpt strip_tac >>
  Cases_on `k = j` >- gvs[] >>
  `k < j` by decide_tac >> metis_tac[]
QED

Theorem ptr_chrono_last_actual_interval:
  ptr_chrono_history vs0 ctx h endpoint /\ i <= j /\ j < LENGTH h /\
  x IN (EL i h).po_taint.t_mem /\ x NOTIN (EL j h).po_taint.t_mem ==>
  ?w. i <= w /\ w < j /\
    x IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
                                  (EL (SUC w) h).po_state) /\
    x NOTIN (EL (SUC w) h).po_taint.t_mem /\
    (!k. w < k /\ k < j ==>
      x NOTIN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state
                                       (EL (SUC k) h).po_state))
Proof
  strip_tac >> ho_match_mp_tac ptr_last_actual_index >> simp[] >>
  rpt strip_tac >> irule ptr_chrono_step_actual_mem >> simp[] >>
  qexists `ctx` >> simp[] >> irule ptr_chrono_history_adjacent >>
  conj_tac >- decide_tac >> qexistsl [`endpoint`,`vs0`] >> simp[]
QED

Theorem ptr_chrono_fresh_last_actual_index:
  ptr_chrono_history vs0 ctx h endpoint /\
  h = pre ++ [a] ++ tail /\ tail <> [] /\
  a.po_inst.inst_opcode = ALLOCA /\
  step_inst fuel ctx a.po_inst a.po_state = OK sa' /\
  x IN new_site_bytes a.po_state sa' /\ x NOTIN endpoint.po_taint.t_mem ==>
  ?k. LENGTH pre < k /\ SUC k < LENGTH h /\
    x IN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state
                                  (EL (SUC k) h).po_state) /\
    x NOTIN (EL (SUC k) h).po_taint.t_mem /\
    (!j. k < j /\ SUC j < LENGTH h ==>
      x NOTIN range_bytes (step_writes (EL j h).po_inst (EL j h).po_state
                                       (EL (SUC j) h).po_state))
Proof
  strip_tac >>
  `SUC (LENGTH pre) < LENGTH h /\ EL (LENGTH pre) h = a` by
    (simp[EL_APPEND_EQN] >> Cases_on `tail` >> gvs[]) >>
  `ptr_chrono_step ctx a (EL (SUC (LENGTH pre)) h)` by
    metis_tac[ptr_chrono_history_adjacent] >>
  `x IN (EL (SUC (LENGTH pre)) h).po_taint.t_mem` by
    metis_tac[ptr_chrono_step_alloca] >>
  drule ptr_chrono_history_end >> strip_tac >>
  `EL (PRE (LENGTH h)) h = endpoint` by metis_tac[LAST_EL] >>
  qpat_x_assum `h = pre ++ [a] ++ tail` kall_tac >>
  `?w. SUC (LENGTH pre) <= w /\ w < PRE (LENGTH h) /\
    x IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
                                  (EL (SUC w) h).po_state) /\
    x NOTIN (EL (SUC w) h).po_taint.t_mem /\
    (!k. w < k /\ k < PRE (LENGTH h) ==>
      x NOTIN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state
                                       (EL (SUC k) h).po_state))` by
    (irule ptr_chrono_last_actual_interval >> simp[] >>
     qexistsl [`ctx`,`endpoint`,`vs0`] >> simp[]) >>
  qexists `w` >> simp[]
QED
