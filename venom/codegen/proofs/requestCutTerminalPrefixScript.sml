Theory requestCutTerminalPrefix
Ancestors
  jointRequestCut requestCutFinalizerTerminal blockSimHelpers
  asmFrameRel codegenEntryRel asmOptimizer asmDataEnv asmSem
  contextCodegenRel o1PassContract venomState callTrace extCallOracle vfmExecution
  venomExecSemantics venomInst
  list rich_list

Theorem request_cut_entry_has_pending:
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    (entry_asm_state vs0 es with as_code := assemble prog' ++ vs0.vs_data_section) es /\
  raw_variant fmp vs vs0 /\ raw_reachable vs C fn inst s /\
  inst.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
  step_inst fuel C inst s = OK t /\ k < LENGTH t.vs_requests ==>
  k < LENGTH (call_requests es)
Proof
  strip_tac >>
  `!rq rqs. record_request rq rqs = rqs ++ [rq]` by simp[record_request_def] >>
  `vs0.vs_requests = [] /\ vs0.vs_outcomes = MAP SND (call_trace es)` by
    fs[asm_frame_rel_tail_nil, asm_frame_rel_def, entry_asm_state_def] >>
  `vs.vs_outcomes = vs0.vs_outcomes /\ vs.vs_requests = vs0.vs_requests` by
    (qpat_x_assum `raw_variant fmp vs vs0` mp_tac >>
     pure_rewrite_tac[raw_variant_def, gas_variant_def] >>
     disch_then (mp_tac o Q.AP_TERM `\v. (v.vs_outcomes,v.vs_requests)`) >> simp[]) >>
  `LENGTH s.vs_requests < LENGTH t.vs_requests` by simp[] >>
  `vs.vs_requests = []` by simp[] >>
  drule_all recorded_step_within_oracle_length >> simp[call_requests_def]
QED

(* A terminal on this same assembly prefix accounts for the entire frame
   request list. Only the length of the terminal's requests is needed. *)
Theorem request_cut_terminal_prefix_crossed:
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  asm_frame_prog_ok prog' /\ vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  (fin = asm_opt_finalizer ==>
    label_disciplined (asm_data_env prog (assemble prog ++ vs0.vs_data_section))
      prog (entry_asm_state vs0 es)) /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    ((entry_asm_state vs0 es) with as_code := assemble prog' ++ vs0.vs_data_section) es /\
  run_call es = SOME (result,final) /\ ~frame_resource_starved es result final /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog n (entry_asm_state vs0 es) = AsmOK ast /\
  (asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog m ast = AsmHalt out \/
   asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog m ast = AsmRevert out \/
   asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog m ast = AsmFault out) /\
  LENGTH out.as_requests <= LENGTH t.vs_requests /\
  raw_variant fmp vs vs0 /\ raw_reachable vs C fn inst s /\
  inst.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
  step_inst fuel C inst s = OK post /\ k < LENGTH post.vs_requests ==>
  k < LENGTH t.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all request_cut_entry_has_pending >> strip_tac >>
  `(entry_asm_state vs0 es).as_pc = 0 /\
   (entry_asm_state vs0 es).as_code = assemble prog ++ vs0.vs_data_section` by
    simp[entry_asm_state_def] >>
  `asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog (n + m) (entry_asm_state vs0 es) = AsmHalt out \/
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog (n + m) (entry_asm_state vs0 es) = AsmRevert out \/
    asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
     prog (n + m) (entry_asm_state vs0 es) = AsmFault out` by
    metis_tac[asm_steps_compose_halt, asm_steps_compose_revert, asm_steps_compose_fault] >>
  mp_tac (Q.INST [`rpolicy` |-> `rp`, `data` |-> `vs0.vs_data_section`,
    `s` |-> `entry_asm_state vs0 es`, `n` |-> `n + m`, `a` |-> `out`,
    `r` |-> `result`] asm_finalizer_terminal_oracle) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE asm_rewrite_tac[]))) >>
  strip_tac >>
  `LENGTH (call_requests es) <= LENGTH out.as_requests` by metis_tac[IS_PREFIX_LENGTH] >>
  decide_tac
QED
