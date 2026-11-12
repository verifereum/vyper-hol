(* Finite selected-call handoffs at the actual physical control coordinates. *)
Theory functionInlinerLiveSelected
Ancestors
  functionInlinerEntryHandoff functionInlinerLiveInvariant functionInlinerLiveReturn
  functionInlinerSelectedReturn functionInlinerParameterExecution
  functionInlinerEvaluatorResidual functionInlinerFmp
  functionInlinerParameterLocations functionInlinerActivation functionInlinerReachableCuts
  functionInlinerRoutedProvenance functionInlinerOccurrences functionInlinerDefs
  venomExecSemantics venomExecProofs venomState venomInstProps callLayoutDefs
  functionInlinerSimulation functionInlinerFrame venomInstProofs venomInst list pred_set

Theorem inline_parameter_step_effects[local]:
  (is_param_opcode inst.inst_opcode \/ inst.inst_opcode = ASSIGN) /\
  step_inst fuel C inst s = OK t ==>
  inline_shared_frame (t with vs_inst_idx := i) = inline_shared_frame s /\
  inline_caller_residual (t with vs_inst_idx := i) = inline_caller_residual s /\
  (t with vs_inst_idx := i).vs_fmp = s.vs_fmp
Proof
  strip_tac >> gvs[is_param_opcode_iff] >>
  gvs[step_inst_def, step_inst_base_opcode_eqs, AllCaseEqs(),
      update_var_def, inline_shared_frame_def, stateFrameTheory.execution_frame_def,
      inline_caller_residual_def, merge_callee_state_def]
QED

Theorem inline_parameter_sequence_effects:
  !N ts.
    (!k. k < N ==> ?inst t.
      (is_param_opcode inst.inst_opcode \/ inst.inst_opcode = ASSIGN) /\
      step_inst fuel C inst (ts k) = OK t /\
      ts (SUC k) = t with vs_inst_idx := SUC (ts k).vs_inst_idx) ==>
    inline_shared_frame (ts N) = inline_shared_frame (ts 0) /\
    inline_caller_residual (ts N) = inline_caller_residual (ts 0) /\
    (ts N).vs_fmp = (ts 0).vs_fmp
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `inline_shared_frame (ts N) = inline_shared_frame (ts 0) /\
   inline_caller_residual (ts N) = inline_caller_residual (ts 0) /\
   (ts N).vs_fmp = (ts 0).vs_fmp` by
    (first_x_assum irule >> rpt strip_tac >> first_x_assum irule >> simp[]) >>
  first_x_assum (qspec_then `N` mp_tac) >> simp[] >> strip_tac >>
  metis_tac[inline_parameter_step_effects]
QED

Theorem inline_parameter_sequence_indices[local]:
  !N ts.
    (!k. k < N ==> ?t.
      ts (SUC k) = t with vs_inst_idx := SUC (ts k).vs_inst_idx) ==>
    !k. k <= N ==> (ts k).vs_inst_idx = (ts 0).vs_inst_idx + k
Proof
  rpt gen_tac >> strip_tac >> Induct >> simp[] >> strip_tac >>
  `k < N /\ k <= N` by decide_tac >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >> strip_tac >> simp[]
QED

Theorem inline_parameter_interval_effects:
  inline_parameter_interval root ml 0 N /\
  lookup_block ml root.fn_blocks = SOME bb /\ (ts 0).vs_inst_idx = 0 /\
  (!k. k < N ==> ?inst t.
    get_instruction bb (ts k).vs_inst_idx = SOME inst /\
    step_inst fuel C inst (ts k) = OK t /\
    ts (SUC k) = t with vs_inst_idx := SUC (ts k).vs_inst_idx) ==>
  inline_shared_frame (ts N) = inline_shared_frame (ts 0) /\
  inline_caller_residual (ts N) = inline_caller_residual (ts 0) /\
  (ts N).vs_fmp = (ts 0).vs_fmp
Proof
  strip_tac >>
  `!k. k <= N ==> (ts k).vs_inst_idx = k` by
    (mp_tac inline_parameter_sequence_indices >>
     disch_then (qspecl_then [`N`,`ts`] mp_tac) >> simp[] >> metis_tac[]) >>
  irule inline_parameter_sequence_effects >> qexistsl [`C`,`fuel`] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `k` mp_tac) >> simp[] >> strip_tac >>
  fs[inline_parameter_interval_def, get_instruction_def, AllCaseEqs()] >>
  metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]
QED
