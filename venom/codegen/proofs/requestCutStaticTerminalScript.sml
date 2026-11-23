Theory requestCutStaticTerminal
Ancestors
  requestCutAbortBound requestCutTerminalPrefix codegenStaticAbortEntrySim
  staticAbortAsmOptCorrect staticAbortFrameException contextStaticAbortRel
  asmFrameRel asmOptimizer codegenEntrySim codegenEntryRel codegenLabelDisciplined
  codegenSymRel contextCodegenRel o1PassContract
  asmSem fnPlanPlaceRevertPostamble venomExecSemantics venomInst venomState venomWf list rich_list

(* Once the capped invariants cover the terminal run, static-aware
   codegen accounts for requests even inside the relaxed memory window. *)
Theorem request_cut_static_terminal_crossed:
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  asm_frame_prog_ok prog' /\ vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    (entry_asm_state vs0 es with as_code := assemble prog' ++ vs0.vs_data_section) es /\
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rp unit = SOME prog /\ unit_shape_ok unit /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es) /\
  codegen_context_obligations_abort (raw_reachable vs0) unit.cu_context cpl /\
  codegen_reachability_package (raw_reachable vs0) unit.cu_context vs0 /\
  (!fn inst l.
    MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  (fin = asm_opt_finalizer ==> label_flow_ok unit.cu_context /\ sym_unit_static_ok unit /\
    code_end_offset_ok (\ctx fn i t. raw_reachable vs0 ctx fn i t /\
       ~in_static_abort_prefix fn t) unit.cu_context) /\
  EVERY wf_function unit.cu_context.ctx_functions /\
  raw_reachable vs0 unit.cu_context fn9 inst9 s9 /\ inst9.inst_opcode <> INVOKE /\
  step_inst fuel9 unit.cu_context inst9 s9 = Abort ab post9 /\
  raw_variant fmp vs vs0 /\ raw_reachable vs C fn inst s /\
  inst.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
  step_inst fuel C inst s = OK post /\ k < LENGTH post.vs_requests ==>
  k < LENGTH s9.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all request_cut_entry_has_pending >> strip_tac >>
  drule_all raw_reachable_primitive_abort >> strip_tac >>
  rename1 `run_context bound unit.cu_context vs0 = Abort ab post9` >>
  `call_requests es <<= post9.vs_requests` by
    (Cases_on `fin = asm_opt_finalizer`
     >- (gvs[asm_frame_rel_tail_nil] >>
         mp_tac (Q.SPECL [`bound`, `rp`, `unit`, `cpl`, `prog`, `prog'`,
           `raw_reachable vs0`, `vs0`, `es`, `ab`, `post9`]
           codegen_correct_static_abort_asm_opt) >>
         (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
         simp[]) >>
     `fin = K SOME` by fs[accepted_finalizers_def] >>
     `prog' = prog` by fs[] >>
     `entry_asm_state vs0 es with as_code := assemble prog ++ vs0.vs_data_section =
        entry_asm_state vs0 es` by simp[entry_asm_state_def] >>
     gvs[asm_frame_rel_tail_nil] >>
     mp_tac (Q.SPECL [`bound`, `rp`, `unit`, `cpl`, `prog`,
       `raw_reachable vs0`, `vs0`, `entry_asm_state vs0 es`, `ab`, `post9`]
       codegen_entry_asm_sim_abort_rel) >>
     (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
     disch_then (qx_choosel_then [`n`, `ast`] (CONJUNCTS_THEN assume_tac)) >>
     mp_tac (Q.SPECL [`prog`, `vs0.vs_data_section`, `es`,
       `entry_asm_state vs0 es`, `n`, `ast`, `post9.vs_requests`]
       asm_frame_exception_requests) >>
     simp[IS_PREFIX_REFL]) >>
  drule IS_PREFIX_LENGTH >> strip_tac >>
  metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem request_cut_static_terminal_crossed_own:
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  asm_frame_prog_ok prog' /\ vs0.vs_code = assemble prog' ++ vs0.vs_data_section /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    (entry_asm_state vs0 es) es /\
  generate_context_plan unit.cu_context = SOME cpl /\
  codegen_assembly rp unit = SOME prog /\ unit_shape_ok unit /\
  codegen_asm_entry_rel_reloc (lo_reloc prog prog') cpl prog vs0 (entry_asm_state vs0 es) /\
  codegen_context_obligations_abort (raw_reachable vs0) unit.cu_context cpl /\
  codegen_reachability_package (raw_reachable vs0) unit.cu_context vs0 /\
  (!fn inst l.
    MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  (fin = asm_opt_finalizer ==> label_flow_own_ok unit.cu_context /\ sym_unit_static_ok unit /\
    code_end_offset_ok (\ctx fn i t. raw_reachable vs0 ctx fn i t /\
       ~in_static_abort_prefix fn t) unit.cu_context) /\
  EVERY wf_function unit.cu_context.ctx_functions /\
  raw_reachable vs0 unit.cu_context fn9 inst9 s9 /\ inst9.inst_opcode <> INVOKE /\
  step_inst fuel9 unit.cu_context inst9 s9 = Abort ab post9 /\
  raw_variant fmp vs vs0 /\ raw_reachable vs C fn inst s /\
  inst.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
  step_inst fuel C inst s = OK post /\ k < LENGTH post.vs_requests ==>
  k < LENGTH s9.vs_requests
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `fin = asm_opt_finalizer`
  >- (`entry_asm_state vs0 es with as_code := assemble prog' ++ vs0.vs_data_section =
        entry_asm_state vs0 es` by simp[entry_asm_state_def] >>
      `k < LENGTH (call_requests es)` by
        (mp_tac (Q.INST [`t` |-> `post`] request_cut_entry_has_pending) >>
         (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
         simp[]) >>
      drule_all raw_reachable_primitive_abort >> strip_tac >>
      rename1 `run_context bound unit.cu_context vs0 = Abort ab post9` >>
      `call_requests es <<= post9.vs_requests` by
        (gvs[asm_frame_rel_tail_nil] >>
         mp_tac (Q.SPECL [`bound`, `rp`, `unit`, `cpl`, `prog`, `prog'`,
           `raw_reachable vs0`, `vs0`, `es`, `ab`, `post9`]
           codegen_correct_static_abort_asm_opt_own) >>
         (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
         simp[]) >>
      drule IS_PREFIX_LENGTH >> strip_tac >>
      metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `fin = K SOME` by fs[accepted_finalizers_def] >>
  `prog' = prog` by fs[combinTheory.K_THM] >>
  `entry_asm_state vs0 es with as_code := assemble prog ++ vs0.vs_data_section =
    entry_asm_state vs0 es` by simp[entry_asm_state_def] >>
  `codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es)` by
    fs[lo_reloc_refl, codegen_asm_entry_rel_reloc_def, codegen_asm_entry_rel_def] >>
  mp_tac (Q.INST [`fin` |-> `K SOME`, `prog'` |-> `prog`]
    request_cut_static_terminal_crossed) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    fs[combinTheory.K_THM, accepted_finalizers_def])) >>
  simp[]
QED
