(* Observation-free source reads and counted machine-load prefixes. *)
Theory augAssignPlaceLoadContinuation
Ancestors
  stmtReasonVvMemory gasSummaryCompose gasOutcome gasExemptCert
  fragGasMode fragGasPathMem vyperState stmtSimAugAssignPlaceMemory
  stmtForArrayMemorySupport

Theorem aug_place_source_prefix_mem[local]:
  (!gs. source (es with gas_obs := gs) =
    (INL (v:value), es with gas_obs := gs)) /\
  ~s.vs_halted /\
  gas_outcome T tops (ctx,func) cx st0 (next v)
    (es with gas_obs := [],s) Q R ==>
  gas_outcome T tops (ctx,func) cx st0 (bind source next) (es,s) Q R
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) source (es,s) [] (INL v) es (OK s)` by
    (simp[gasSummaryTheory.gas_marked_exec_def,
          gasSummaryTheory.gas_explicit_def, gas_marked_path_def] >>
     irule (cj 1 gas_path_mem_rules) >> simp[]) >>
  drule_all aug_place_completed_value_prefix >> simp[]
QED

Theorem aug_place_read_type_load_mem:
  ((?id path. p = MemoryPlace id path) \/ (?tr slot tv. p = StoragePlace tr slot tv)) /\
  (!gs. read_place cx p (es with gas_obs := gs) =
      (INL cur,es with gas_obs := gs)) /\
  (!gs. place_type_value cx p (es with gas_obs := gs) =
      (INL ptv,es with gas_obs := gs)) /\
  ~s.vs_halted /\
  gas_marked_path T ctx func s 0 (OK u) /\
  gas_outcome T tops (ctx,func) cx st0 (next cur ptv)
    (es with gas_obs := [],u) Q R ==>
  gas_outcome T tops (ctx,func) cx st0
    (bind (read_place cx p) (\cur. bind (place_type_value cx p) (next cur)))
    (es,s) Q R
Proof
  strip_tac >>
  `gas_outcome T tops (ctx,func) cx st0 (next cur ptv) (es,u) Q R` by
    (drule gas_outcome_start_gas_obs >>
     disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[]) >>
  `gas_outcome T tops (ctx,func) cx st0 (next cur ptv) (es,s) Q R` by
    (irule gas_outcome_zero_prefix_any >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[]
  >- (irule aug_place_memory_reads_outcome >> simp[] >>
      qexistsl_tac [`cur`, `ptv`] >>
      qpat_x_assum `!gs. read_place _ _ _ = _`
        (qspec_then `es.gas_obs` assume_tac) >>
      qpat_x_assum `!gs. place_type_value _ _ _ = _`
        (qspec_then `es.gas_obs` assume_tac) >> gvs[]) >>
  irule aug_place_source_prefix_mem >> simp[] >>
  qpat_x_assum `!gs. place_type_value _ _ _ = _`
    (qspec_then `[]` mp_tac) >>
  simp[place_type_value_def, return_def] >> strip_tac >> gvs[] >>
  simp[place_type_value_def, bind_return] >>
  drule gas_outcome_start_gas_obs >>
  disch_then (qspec_then `[]` mp_tac) >> simp[]
QED
