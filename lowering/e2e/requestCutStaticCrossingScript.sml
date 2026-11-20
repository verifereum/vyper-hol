Theory requestCutStaticCrossing
Ancestors
  requestCutStaticObligations requestCutStaticTerminal requestCutStaticCfgAbort
  requestCutCoveredInvariants requestCutTerminalInvariants
  o1ContractCfgNormJointCursors o1PipelineCorrect o1PassContract
  contextCodegenRel codegenEntryRel codegenEntrySim asmFrameRel asmOptimizer asmSem
  fnPlanPlaceRevertPostamble codegenLabelDisciplined
  unitMemInv codegenSymRel unitShapeDefs staticAbortDefs dftGasOracleDefs
  venomPassSchedule venomExecSemantics venomWf venomState venomInst list

fun prove_request_cut_static_crossing terminal =
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `k < LENGTH s9.vs_requests` >> simp[] >>
  `LENGTH s9.vs_requests <= k` by decide_tac >>
  qpat_x_assum `C9 = _` SUBST_ALL_TAC >>
  mp_tac request_cut_cfg_static_abort >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`abort_inst`, `stop`, `ab`, `end9`] strip_assume_tac) >>
  mp_tac (Q.INST [`guarded` |-> `fin = asm_opt_finalizer`,
    `C9` |-> `unit.cu_context`] request_cut_covered_invariants) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])) >>
  strip_tac >>
  mp_tac (Q.INST [`C` |-> `unit.cu_context`, `fn` |-> `fn9`, `s` |-> `stop`,
    `inst` |-> `abort_inst`, `ab` |-> `ab`, `post` |-> `end9`, `fuel` |-> `0`,
    `v` |-> `vs0`, `guarded` |-> `fin = asm_opt_finalizer`] request_cut_abort_invariants) >>
  (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
  strip_tac >>
  `codegen_context_obligations_abort (raw_reachable vs0) unit.cu_context cpl /\
   codegen_reachability_package (raw_reachable vs0) unit.cu_context vs0` by
    (`vs0.vs_initial_fmp = n2w cpl.cp_initial_fmp` by
       fs[codegen_asm_entry_rel_def, codegen_asm_entry_rel_reloc_def] >>
     qpat_x_assum `unit = _` SUBST_ALL_TAC >>
     irule request_cut_static_obligations_at_fmp >> metis_tac[]) >>
  mp_tac (Q.INST [`fn9` |-> `fn9`, `s9` |-> `stop`, `inst9` |-> `abort_inst`,
    `ab` |-> `ab`, `post9` |-> `end9`, `fuel9` |-> `0`,
    `C` |-> `src_unit.cu_context`] terminal) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[])) >>
  simp[];

(* A static write still pending at the stopped observation can be run to
   its abort. All frame memory and code-end checks only need the cut. *)
Theorem request_cut_static_crossing_own:
  o1_pipeline rp src_unit = SOME out /\ unit = out.po_unit /\
  C9 = unit.cu_context /\
  ctx_pass_stage rp (CFP_Simple VP_DFT) dft_view C7 C8 /\ o1_pre 7 C7 C8 /\
  ctx_pass_stage rp (CFP_Simple VP_CFGNormalization) cfg_view C8 C9 /\
  o1_ctx_shape C7 /\ EVERY wf_ssa C7.ctx_functions /\ o1_ctx_shape C8 /\
  EVERY wf_function C9.ctx_functions /\ ctx_labels_bound C7 vs0.vs_labels /\
  o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\ code_layout_valid vs0 /\
  (!fn inst t. raw_reachable vs0 C8 fn inst t /\ ~in_static_abort_prefix fn t ==>
    ?p d. ev_reachable orc vs0 C8 p d fn inst (t with vs_gas_readings := vs0.vs_gas_readings)) /\
  (!p d fn inst s. ev_reachable orc vs0 C7 p d fn inst s /\ LENGTH s.vs_requests <= k ==>
    ?ws. raw_reachable source C7 fn inst (s with vs_gas_readings := ws)) /\
  mem_inv (\ctx fn inst s. LENGTH s.vs_requests <= k ==>
    lowered_mem_fact eom ctx fn inst s) C7 source /\
  (fin = asm_opt_finalizer ==> code_end_offset_ok
    (\ctx fn inst s. raw_reachable source ctx fn inst s /\ LENGTH s.vs_requests <= k) C7) /\
  max_live_eom C9 = SOME eom /\
  fin IN accepted_finalizers /\ fin rp prog = SOME prog' /\
  asm_frame_prog_ok prog' /\ vs0.vs_code = assemble prog' ++ vs0.vs_data_section /\
  asm_frame_rel_tail [] prog' vs0.vs_data_section es
    (entry_asm_state vs0 es) es /\
  generate_context_plan C9 = SOME cpl /\ codegen_assembly rp unit = SOME prog /\
  unit_shape_ok unit /\ codegen_ready C9 /\
  codegen_asm_entry_rel_reloc (lo_reloc prog prog') cpl prog vs0 (entry_asm_state vs0 es) /\
  (!fn inst l. MEM fn C9.ctx_functions /\ MEM inst (fn_insts fn) /\
    inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  (fin = asm_opt_finalizer ==> label_flow_own_ok C9 /\ sym_unit_static_ok unit) /\
  cfg_norm_joint_cursors C8 C9 (schedules,(rounds,cells),saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  in_static_abort_prefix fn8 s8 /\ inv_memory_observation inst9.inst_opcode /\
  raw_reachable vs0 C9 fn9 inst9 s9 /\
  (!i l. MEM i (fn_insts fn9) /\ i.inst_opcode <> PHI /\
    MEM (Label l) (compute_operands i) ==> IS_SOME (FLOOKUP s9.vs_labels l)) /\
  raw_variant fmp vs vs0 /\ raw_reachable vs src_unit.cu_context fn inst s /\
  inst.inst_opcode <> INVOKE /\ LENGTH s.vs_requests = k /\
  step_inst fuel src_unit.cu_context inst s = OK post /\ k < LENGTH post.vs_requests ==>
  k < LENGTH s9.vs_requests
Proof
  prove_request_cut_static_crossing request_cut_static_terminal_crossed_own
QED
