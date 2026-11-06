Theory concretizePtrActualWrites
Ancestors ptrDiscipline memLocDefs codegenRel concretizeMemLocDefs
  concretizePtrChronologicalHistory concretizePtrLifetime concretizePtrOwnerDemand
  list rich_list

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

(* Backwards purity across a finite interval of actual nonwrites. *)
Theorem ptr_nonwrite_interval_pure[local]:
  !j i. i <= j /\ ~tainted j /\
    (!k. i <= k /\ k < j ==> ~writes k) /\
    (!k. i <= k /\ k < j ==> tainted k /\ ~tainted (SUC k) ==> writes k) ==>
    ~tainted i
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  Cases_on `i = SUC j` >- gvs[] >>
  `i <= j` by decide_tac >>
  `~tainted j` by
    (qpat_x_assum `!k. _ ==> tainted k /\ _ ==> _` (qspec_then `j` mp_tac) >>
     qpat_x_assum `!k. _ ==> ~writes k` (qspec_then `j` mp_tac) >> simp[]) >>
  first_x_assum irule >> simp[] >> conj_tac >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

(* One selection implementation, allowing initially pure fixed bytes. *)
Theorem ptr_last_actual_index[local]:
  !j i. i <= j /\ ~tainted j /\
    (!k. i <= k /\ k < j ==> tainted k /\ ~tainted (SUC k) ==> writes k) ==>
    ((!k. i <= k /\ k < j ==> ~writes k) \/
     ?w. i <= w /\ w < j /\ writes w /\ ~tainted (SUC w) /\
         (!k. w < k /\ k < j ==> ~writes k))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- simp[] >>
  Cases_on `i = SUC j` >- simp[] >>
  `i <= j` by decide_tac >>
  Cases_on `writes j`
  >- (disj2_tac >> qexists `j` >> simp[]) >>
  `~tainted j` by
    (qpat_x_assum `!k. _` (qspec_then `j` mp_tac) >> simp[]) >>
  `(!k. i <= k /\ k < j ==> ~writes k) \/
   ?w. i <= w /\ w < j /\ writes w /\ ~tainted (SUC w) /\
       (!k. w < k /\ k < j ==> ~writes k)` by
    (first_x_assum irule >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> simp[])
  >- (disj1_tac >> rpt strip_tac >>
      Cases_on `k = j` >- gvs[] >>
      `k < j` by decide_tac >> metis_tac[]) >>
  disj2_tac >> qexists `w` >> simp[] >> rpt strip_tac >>
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
  strip_tac >>
  `!k. i <= k /\ k < j ==>
    x IN (EL k h).po_taint.t_mem /\ x NOTIN (EL (SUC k) h).po_taint.t_mem ==>
    x IN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state
      (EL (SUC k) h).po_state)` by
    (rpt strip_tac >> irule ptr_chrono_step_actual_mem >> simp[] >>
     qexists `ctx` >> simp[] >> irule ptr_chrono_history_adjacent >>
     conj_tac >- decide_tac >> qexistsl [`endpoint`,`vs0`] >> simp[]) >>
  `(!k. i <= k /\ k < j ==> x NOTIN range_bytes
      (step_writes (EL k h).po_inst (EL k h).po_state (EL (SUC k) h).po_state)) \/
   ?w. i <= w /\ w < j /\
     x IN range_bytes (step_writes (EL w h).po_inst (EL w h).po_state
       (EL (SUC w) h).po_state) /\ x NOTIN (EL (SUC w) h).po_taint.t_mem /\
     (!k. w < k /\ k < j ==> x NOTIN range_bytes
       (step_writes (EL k h).po_inst (EL k h).po_state (EL (SUC k) h).po_state))` by
    (ho_match_mp_tac ptr_last_actual_index >> simp[])
  >- (`x NOTIN (EL i h).po_taint.t_mem` suffices_by simp[] >>
      mp_tac (Q.INST
        [`tainted` |-> `\k. x IN (EL k h).po_taint.t_mem`,
         `writes` |-> `\k. x IN range_bytes (step_writes (EL k h).po_inst
           (EL k h).po_state (EL (SUC k) h).po_state)`]
        ptr_nonwrite_interval_pure) >>
      disch_then (qspecl_then [`j`,`i`] mp_tac) >> simp[] >> metis_tac[]) >>
  qexists `w` >> simp[]
QED

Theorem ptr_chrono_last_actual_or_none:
  ptr_chrono_history vs C h endpoint /\ x NOTIN endpoint.po_taint.t_mem ==>
  ((!n. SUC n < LENGTH h ==>
      x NOTIN range_bytes (step_writes (EL n h).po_inst
        (EL n h).po_state (EL (SUC n) h).po_state)) \/
   (?w. SUC w < LENGTH h /\
     x IN range_bytes (step_writes (EL w h).po_inst
       (EL w h).po_state (EL (SUC w) h).po_state) /\
     x NOTIN (EL (SUC w) h).po_taint.t_mem /\
     (!n. w < n /\ SUC n < LENGTH h ==>
       x NOTIN range_bytes (step_writes (EL n h).po_inst
         (EL n h).po_state (EL (SUC n) h).po_state))))
Proof
  strip_tac >> drule ptr_chrono_history_end >> strip_tac >>
  `0 < LENGTH h /\ EL (LENGTH h-1) h = endpoint` by
    (Cases_on `h` >> gvs[LAST_EL]) >>
  `!k. k < LENGTH h-1 <=> SUC k < LENGTH h` by decide_tac >>
  `!k. k < LENGTH h-1 ==>
    x IN (EL k h).po_taint.t_mem /\ x NOTIN (EL (SUC k) h).po_taint.t_mem ==>
    x IN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state
      (EL (SUC k) h).po_state)` by
    (rpt strip_tac >> irule ptr_chrono_step_actual_mem >> simp[] >>
     qexists `C` >> simp[] >> irule ptr_chrono_history_adjacent >>
     conj_tac >- decide_tac >> qexistsl [`endpoint`,`vs`] >> simp[]) >>
  mp_tac (Q.INST
    [`tainted` |-> `\k. x IN (EL k h).po_taint.t_mem`,
     `writes` |-> `\k. x IN range_bytes (step_writes (EL k h).po_inst
       (EL k h).po_state (EL (SUC k) h).po_state)`]
    ptr_last_actual_index) >>
  disch_then (qspecl_then [`LENGTH h-1`,`0`] mp_tac) >> simp[]
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

Theorem ptr_stage_owner_actual_interval_no_kill:
  ctx_pass_stage rpolicy (CFP_Simple VP_ConcretizeMemLoc)
    (o1_walk_view rpolicy 2) C C' /\
  EVERY (\f. f.fn_eom = NONE) C.ctx_functions /\
  ctx_inst_ids_distinct C /\ callee_first names C.ctx_functions /\
  lookup_function fn.fn_name C.ctx_functions = SOME fn /\
  lookup_function fn.fn_name C'.ctx_functions = SOME out.fpo_function /\
  fn_pass_step rpolicy (CFP_Simple VP_ConcretizeMemLoc) observed s fn out /\
  ctx_fn_names observed.cu_context = ctx_fn_names C /\
  o1_walk_view rpolicy 2 C' fn observed /\
  ptr_chrono_history vs C h endpoint /\ i <= j /\ j < LENGTH h /\
  (!k. i <= k /\ k <= j ==> d <= LENGTH (EL k h).po_stack) /\
  (ptr_owner_view d (EL i h)).cf_fn = fn /\
  FLOOKUP (ptr_owner_view d (EL i h)).cf_state.vs_allocas aid = SOME (b,sz) /\
  b <= byte /\ byte < b + sz /\
  (!k. i <= k /\ k < j ==>
    ~in_revert_forward (EL k h).po_fn (EL k h).po_state /\
    byte NOTIN range_bytes (step_writes (EL k h).po_inst (EL k h).po_state
                                         (EL (SUC k) h).po_state)) /\
  o1_run_state_ok vs /\ o1_ctx_shape C /\ ~ctx_has_dalloca C /\
  EVERY (fn_ptr_ok P) C.ctx_functions /\ EVERY ssa_form C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  EVERY (\f. EVERY (\inst. inst.inst_opcode <> DALLOCA) (fn_insts f)) C.ctx_functions /\
  wf_function fn /\ all_reachable fn /\ ptr_discipline lo C vs /\
  ptr_bp_origins fn (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn) ==>
  !k. i <= k /\ k < j ==>
  ~ptr_ml_can_kill (Allocation aid)
    (bp_analyze_fuel (concretize_memloc_fuel fn) (cfg_analyze fn) fn)
    (\a. if context_alloca_size fn (imported_mems_used observed.cu_context fn) a = 0 then NONE
         else SOME (context_alloca_size fn (imported_mems_used observed.cu_context fn) a))
    (ptr_owner_view d (EL k h)).cf_inst
Proof
  strip_tac >>
  `!k. i <= k /\ k < j ==>
    ~in_revert_forward (EL k h).po_fn (EL k h).po_state /\
    (!n off len. inst_write_size (EL k h).po_inst = SOME n /\
      MEM (off,len) (source_memory_write_ranges (EL k h).po_inst (EL k h).po_state) ==>
      ~(off <= byte /\ byte < off + len))` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!k. _ /\ _ ==> ~in_revert_forward _ _ /\ _`
       (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
     rpt strip_tac >> drule ptr_exact_size_step_writes >>
     disch_then (qspecl_then [`(EL k h).po_state`,
                               `(EL (SUC k) h).po_state`] assume_tac) >>
     gvs[range_bytes_def] >> metis_tac[]) >>
  match_mp_tac ptr_stage_owner_interval_no_kill >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!k. _ /\ _ ==> ~in_revert_forward _ _ /\ !n off len. _`
    (qspec_then `k` mp_tac) >> simp[] >> metis_tac[]
QED

(* Integration boundary:
   ptr_chrono_fresh_last_actual_index supplies the byte-exclusion conjunct
   above for i = SUC k and j = PRE (LENGTH h).  The no-revert conjunct still
   comes from the source history's EVERY no-revert premise.  No requested
   CALL output byte is inferred to have been written.

   The remaining owner premises are independent: the selected owner's depth
   must be present at every index from i through j, its view at i must be fn,
   and that view must retain the allocation (b,sz) containing the byte.  A
   retained birth record alone does not supply these continuity facts.  This
   boundary neither identifies a retained birth with that owner nor supplies
   paired target-byte agreement or actual-aware protected livesets. *)
