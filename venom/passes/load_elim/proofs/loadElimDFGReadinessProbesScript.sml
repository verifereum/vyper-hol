Theory loadElimDFGReadinessProbes
Ancestors
  loadElimPhiProbes dfgCorrectnessProof finite_map venomWf venomInst
  loadElimDefs venomState loadElimOccurrenceInvariants
  loadElimSentinelHelpers memoryCopyElisionSound basePtrDefs venomMemDefs
  venomExecSemantics memLocDefs

Definition readiness_probe_fn_def:
  readiness_probe_fn = mk_raw_function "readiness"
    [<| bb_label := "e"; bb_instructions :=
      [probe_inst 0 MLOAD [Lit 0w] ["x"];
       probe_inst 1 MLOAD [Lit 0w] ["y"];
       probe_inst 2 STOP [] []] |>]
End

Definition readiness_probe_ctx_def:
  readiness_probe_ctx = mk_load_context
    (bp_analyze (cfg_analyze readiness_probe_fn) readiness_probe_fn)
    (memory_alias_analyze
      (bp_analyze (cfg_analyze readiness_probe_fn) readiness_probe_fn)
      readiness_probe_fn)
    (dfg_build_function readiness_probe_fn) memory_config
End

Definition readiness_probe_fn1_def:
  readiness_probe_fn1 = load_elim_one readiness_probe_ctx
    (cfg_analyze readiness_probe_fn) readiness_probe_fn
End

Theorem readiness_probe_wf:
  wf_function readiness_probe_fn /\ fn_inst_wf readiness_probe_fn /\
  wf_ssa readiness_probe_fn
Proof
  conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
  simp[wf_ssa_def, ssa_form_def, def_dominates_uses_def,
       readiness_probe_fn_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, probe_inst_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem readiness_probe_round:
  readiness_probe_fn1 = mk_raw_function "readiness"
    [<| bb_label := "e"; bb_instructions :=
      [probe_inst 0 MLOAD [Lit 0w] ["x"];
       probe_inst 1 ASSIGN [Var "x"] ["y"];
       probe_inst 2 STOP [] []] |>]
Proof
  EVAL_TAC >> simp[FUN_FMAP_EMPTY] >> EVAL_TAC
QED

Definition readiness_probe_state_def:
  readiness_probe_state = (ARB : venom_state) with
    vs_vars := FEMPTY |++ [("x",0w); ("y",1w)]
End

Theorem readiness_probe_source_sound:
  !s. dfg_assigns_sound (dfg_build_function readiness_probe_fn) s
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem readiness_probe_rebuilt_unsound:
  ~dfg_assigns_sound (dfg_build_function readiness_probe_fn1)
    readiness_probe_state
Proof
  rewrite_tac[readiness_probe_round, dfg_assigns_sound_def] >>
  disch_then (qspec_then `"y"` (qspec_then
    `probe_inst 1 ASSIGN [Var "x"] ["y"]` mp_tac)) >> EVAL_TAC >> simp[]
QED

Theorem readiness_probe_bp_empty:
  !v. bp_get_ptrs
    (bp_analyze (cfg_analyze readiness_probe_fn) readiness_probe_fn) v = []
Proof
  EVAL_TAC >> simp[]
QED

Theorem readiness_probe_step_preserves:
  le_step_preserves
    (bp_analyze (cfg_analyze readiness_probe_fn) readiness_probe_fn)
    (dfg_build_function readiness_probe_fn) readiness_probe_fn
Proof
  simp[le_step_preserves_def, le_step_invariants_inst_idx,
       le_step_invariants_def, readiness_probe_source_sound,
       bp_ptr_sound_def, readiness_probe_bp_empty] >>
  simp[readiness_probe_fn_def, mk_raw_function_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def, probe_inst_def, step_inst_base_opcode_eqs,
       exec_read1_def, eval_operand_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[allocas_non_overlapping_def, allocas_in_word_def,
      bp_ptrs_bounded_def, memloc_within_alloca_def, update_var_def] >>
  gvs[probe_inst_def]
QED

Theorem readiness_probe_rebuilt_lookup:
  FLOOKUP (dfg_build_function readiness_probe_fn1).dfg_defs "y" =
    SOME (probe_inst 1 ASSIGN [Var "x"] ["y"])
Proof
  rewrite_tac[readiness_probe_round] >> EVAL_TAC
QED

(* Auxiliary nonpreservation, not a counterexample to run_blocks correctness. *)
Theorem readiness_probe_no_initial_transport:
  wf_function readiness_probe_fn /\ fn_inst_wf readiness_probe_fn /\
  wf_ssa readiness_probe_fn /\
  dfg_assigns_sound (dfg_build_function readiness_probe_fn) readiness_probe_state /\
  le_step_preserves
    (bp_analyze (cfg_analyze readiness_probe_fn) readiness_probe_fn)
    (dfg_build_function readiness_probe_fn) readiness_probe_fn /\
  ~dfg_assigns_sound (dfg_build_function
    (load_elim_one readiness_probe_ctx (cfg_analyze readiness_probe_fn)
      readiness_probe_fn)) readiness_probe_state
Proof
  simp[GSYM readiness_probe_fn1_def, readiness_probe_wf,
       readiness_probe_source_sound, readiness_probe_step_preserves,
       readiness_probe_rebuilt_unsound]
QED
