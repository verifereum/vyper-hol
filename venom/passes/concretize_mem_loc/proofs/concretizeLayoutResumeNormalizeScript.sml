Theory concretizeLayoutResumeNormalize
Ancestors concretizeLayoutCallerResume concretizeLayoutPairedEntry concretizeLayoutPhaseOrigin
  frameRelocationControl frameRelocationLocal frameRelocationValues
  frameRelocationEnvironment concretizeLayoutSupplement concretizeLayoutReaderContext
  ptrDiscipline venomState

(* State-only transport: neither execution cursors nor the lifetime bound
   constrain local values.  Activation identifiers and annotations are retained. *)
Theorem layout_ordinary_state_resume_indices:
  ~a.lop_pending /\
  a.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  layout_ordinary_state D lo C' q0 es qs a s t ==>
  layout_ordinary_state D lo C' q0 es qs
    (a with <| lop_config := JointConfig stk PG G tn fn inst
       (s with vs_inst_idx := i) oms om hs h; lop_bound := bound |>)
    (s with vs_inst_idx := i) (t with vs_inst_idx := j)
Proof
  simp[layout_ordinary_state_def, layout_phase_normalize_def] >> rpt strip_tac >>
  gvs[local_rel_def, variable_domains_def, variables_agree_on_def,
      local_values_def, lookup_var_def, concretize_supplement_def,
      relocation_env_def, relocation_reader_context_def,
      concretize_local_obs_def, dead_result_rel_def] >> metis_tac[]
QED

val _ = export_theory();
