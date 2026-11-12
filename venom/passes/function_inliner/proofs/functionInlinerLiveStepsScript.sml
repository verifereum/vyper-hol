(* Running cuts preserve live effects only at the active owner.  Terminal
   cuts deliberately expose observations rather than a continuing live stack. *)
Theory functionInlinerLiveSteps
Ancestors
  functionInlinerLiveInvariant functionInlinerEvaluatorResidual functionInlinerFmp
  functionInlinerOperationalCuts functionInlinerOperational functionInlinerSimulation
  functionInlinerParameterSavedReads functionInlinerParameterAncestry
  functionInlinerFrame functionInlinerReachableCuts
  venomExecProofs venomExecSemantics venomState list

Theorem inline_live_head_update[local]:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
  inline_owner_storage cert
    ((p,a,route,snap with <|ils_state := u; ils_defined := defined|>)::rest)
    (frame with ipf_state := v) /\
  inline_shared_frame u = inline_shared_frame v /\
  inline_caller_residual u = inline_caller_residual snap.ils_state /\
  u.vs_fmp = snap.ils_state.vs_fmp ==>
  inline_live_stack C cert root
    ((p,a,route,snap with <|ils_state := u; ils_defined := defined|>)::rest)
    (frame with ipf_state := v)
Proof
  strip_tac >>
  `inline_parameter_saved_reads
     ((p,a,route,snap with <|ils_state := u; ils_defined := defined|>)::rest)` by
    metis_tac[inline_live_stack_lifecycle, inline_parameter_saved_reads_head_replace] >>
  `inline_caller_residual v = inline_caller_residual u` by
    metis_tac[inline_caller_residual_shared] >>
  `v.vs_fmp = u.vs_fmp` by
    (qpat_x_assum `inline_shared_frame u = inline_shared_frame v`
      (mp_tac o Q.AP_TERM `\s. s.vs_fmp`) >>
     simp[inline_shared_frame_def, stateFrameTheory.execution_frame_def]) >>
  gvs[inline_live_stack_def] >>
  gvs[EVERY_MEM, pairTheory.FORALL_PROD]
QED

Theorem inline_live_ordinary_step:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inst_wf src /\ inline_ordinary_opcode src.inst_opcode /\
  step_inst fuel C src snap.ils_state = OK s' /\
  EVERY (\x. MEM x (cfgTransform$fn_all_vars a.ia_function) /\
    ~retpc_var a.ia_function x) src.inst_outputs /\
  INJ route.ir_rename (set src.inst_outputs UNION snap.ils_defined) UNIV /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function v)
    src.inst_operands /\
  dst.inst_opcode = src.inst_opcode /\
  dst.inst_operands = MAP (inline_rename_operand route.ir_rename lab) src.inst_operands /\
  dst.inst_outputs = MAP route.ir_rename src.inst_outputs ==>
  ?t. step_inst tfuel Tctx dst frame.ipf_state = OK t /\
      inline_live_stack C cert root
        ((p,a,route,snap with <|ils_state := s';
          ils_defined := set src.inst_outputs UNION snap.ils_defined|>)::rest)
        (frame with ipf_state := t) /\
      inline_shared_frame s' = inline_shared_frame t /\
      s'.vs_current_bb = snap.ils_state.vs_current_bb /\
      s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
      t.vs_current_bb = frame.ipf_state.vs_current_bb /\
      t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >>
  `inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
   inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state` by
    metis_tac[inline_live_stack_storage, inline_live_stack_head_shared] >>
  drule_all inline_owner_storage_ordinary_step >>
  disch_then (qspecl_then [`tfuel`, `Tctx`] strip_assume_tac) >>
  qexists `t` >> simp[] >> irule inline_live_head_update >>
  simp[] >>
  `~is_terminator src.inst_opcode` by metis_tac[inline_ordinary_OK_nonterminator] >>
  `step_inst_base src snap.ils_state = OK s'` by
    metis_tac[step_inst_non_invoke, inline_ordinary_opcode_def, MEM] >>
  metis_tac[inline_caller_residual_step_nonterminator, inline_base_ok_fmp,
            inline_ordinary_opcode_def, MEM]
QED

Theorem inline_live_assign_step:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  src.inst_opcode = ASSIGN /\ src.inst_operands = [op] /\ src.inst_outputs = [x] /\
  step_inst fuel C src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  (!v. op = Var v ==> MEM v (cfgTransform$fn_all_vars a.ia_function) /\
    (retpc_var a.ia_function v ==> retpc_var a.ia_function x)) /\
  dst.inst_opcode = ASSIGN /\
  dst.inst_operands = [inline_rename_operand route.ir_rename lab op] /\
  dst.inst_outputs = [route.ir_rename x] ==>
  ?t. step_inst tfuel Tctx dst frame.ipf_state = OK t /\
      inline_live_stack C cert root
        ((p,a,route,snap with <|ils_state := s';
          ils_defined := x INSERT snap.ils_defined|>)::rest)
        (frame with ipf_state := t) /\
      inline_shared_frame s' = inline_shared_frame t /\
      s'.vs_current_bb = snap.ils_state.vs_current_bb /\
      s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
      t.vs_current_bb = frame.ipf_state.vs_current_bb /\
      t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >>
  `inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
   inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state` by
    metis_tac[inline_live_stack_storage, inline_live_stack_head_shared] >>
  drule_all inline_owner_storage_assign_ok_step >>
  disch_then (qspecl_then [`tfuel`, `Tctx`] strip_assume_tac) >>
  qexists `t` >> simp[] >> irule inline_live_head_update >> simp[] >>
  qpat_x_assum `step_inst fuel C src _ = _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def] >> strip_tac >>
  gvs[AllCaseEqs(), update_var_def]
QED

Theorem inline_live_phi_body_cut:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inline_routed_leaf cert root p a.ia_function path /\
  route.ir_rename = inline_path_rename path /\
  lookup_block snap.ils_state.vs_current_bb a.ia_function.fn_blocks = SOME sb /\
  lookup_block frame.ipf_state.vs_current_bb root.fn_blocks = SOME tb /\
  (!q. snap.ils_state.vs_prev_bb = SOME q ==> MEM q (fn_labels a.ia_function)) /\
  inline_phi_entry_path path (snap.ils_state.vs_current_bb,snap.ils_state.vs_prev_bb) =
    (frame.ipf_state.vs_current_bb,frame.ipf_state.vs_prev_bb) /\
  eval_phis snap.ils_state sb.bb_instructions = OK u ==>
  ?v. eval_phis frame.ipf_state tb.bb_instructions = OK v /\
    let ks = phi_prefix_length sb.bb_instructions;
        kt = phi_prefix_length tb.bb_instructions;
        su = u with vs_inst_idx := ks;
        tv = v with vs_inst_idx := kt
    in ks = kt /\
      inline_live_stack C cert root
        ((p,a,route,snap with <|ils_state := su;
          ils_defined := inline_phi_outputs sb.bb_instructions UNION snap.ils_defined|>)::rest)
        (frame with ipf_state := tv) /\
      inline_shared_frame su = inline_shared_frame tv /\
      su.vs_current_bb = snap.ils_state.vs_current_bb /\
      su.vs_prev_bb = snap.ils_state.vs_prev_bb /\
      tv.vs_current_bb = frame.ipf_state.vs_current_bb /\
      tv.vs_prev_bb = frame.ipf_state.vs_prev_bb /\
      inline_phi_entry_path path (su.vs_current_bb,su.vs_prev_bb) =
        (tv.vs_current_bb,tv.vs_prev_bb) /\
      su.vs_inst_idx = ks /\ tv.vs_inst_idx = kt
Proof
  strip_tac >>
  `inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
   inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state` by
    metis_tac[inline_live_stack_storage, inline_live_stack_head_shared] >>
  drule_all inline_owner_phi_body_cut >> strip_tac >>
  qexists `v` >> gvs[] >> irule inline_live_head_update >> simp[] >>
  metis_tac[inline_caller_residual_phis, inline_caller_residual_updates,
            inline_eval_phis_fmp]
QED

Theorem inline_live_halt_cut:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inst_wf src /\ inline_ordinary_opcode src.inst_opcode /\
  step_inst fuel C src snap.ils_state = Halt u /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function v)
    src.inst_operands /\
  get_instruction sb snap.ils_state.vs_inst_idx = SOME src /\
  d.ic_index = frame.ipf_state.vs_inst_idx /\
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  c.ic_fields = inline_inst_fields src /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  inline_cell_var_action frames = route.ir_rename /\
  inline_cell_label_action frames = lab ==>
  ?tb dst v.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME tb /\
    get_instruction tb frame.ipf_state.vs_inst_idx = SOME dst /\
    step_inst tfuel Tctx dst frame.ipf_state = Halt v /\
    exec_block fuel C sb snap.ils_state = Halt u /\
    exec_block tfuel Tctx tb frame.ipf_state = Halt v /\
    inline_owner_storage cert
      ((p,a,route,snap with ils_state := u)::rest)
      (frame with ipf_state := v) /\
    inline_shared_frame u = inline_shared_frame v
Proof
  strip_tac >> irule inline_owner_halt_cut >>
  metis_tac[inline_live_stack_storage, inline_live_stack_head_shared]
QED

Theorem inline_live_abort_cut:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inst_wf src /\ inline_ordinary_opcode src.inst_opcode /\
  step_inst fuel C src snap.ils_state = Abort reason u /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function v)
    src.inst_operands /\
  get_instruction sb snap.ils_state.vs_inst_idx = SOME src /\
  d.ic_index = frame.ipf_state.vs_inst_idx /\
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  c.ic_fields = inline_inst_fields src /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  inline_cell_var_action frames = route.ir_rename /\
  inline_cell_label_action frames = lab ==>
  ?tb dst v.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME tb /\
    get_instruction tb frame.ipf_state.vs_inst_idx = SOME dst /\
    step_inst tfuel Tctx dst frame.ipf_state = Abort reason v /\
    exec_block fuel C sb snap.ils_state = Abort reason u /\
    exec_block tfuel Tctx tb frame.ipf_state = Abort reason v /\
    inline_owner_storage cert
      ((p,a,route,snap with ils_state := u)::rest)
      (frame with ipf_state := v) /\
    inline_shared_frame u = inline_shared_frame v
Proof
  strip_tac >> irule inline_owner_abort_cut >>
  metis_tac[inline_live_stack_storage, inline_live_stack_head_shared]
QED

Theorem inline_live_ordinary_fetch:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inst_wf src /\ inline_ordinary_opcode src.inst_opcode /\
  step_inst fuel C src snap.ils_state = OK s' /\
  EVERY (\x. MEM x (cfgTransform$fn_all_vars a.ia_function) /\
    ~retpc_var a.ia_function x) src.inst_outputs /\
  INJ route.ir_rename (set src.inst_outputs UNION snap.ils_defined) UNIV /\
  EVERY (\op. !v. op = Var v ==>
    MEM v (cfgTransform$fn_all_vars a.ia_function) /\ ~retpc_var a.ia_function v)
    src.inst_operands /\
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  c.ic_fields = inline_inst_fields src /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  inline_cell_var_action frames = route.ir_rename /\
  inline_cell_label_action frames = lab ==>
  ?bb dst t.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME bb /\
    get_instruction bb d.ic_index = SOME dst /\
    step_inst tfuel Tctx dst frame.ipf_state = OK t /\
    inline_live_stack C cert root
      ((p,a,route,snap with <|ils_state := s';
        ils_defined := set src.inst_outputs UNION snap.ils_defined|>)::rest)
      (frame with ipf_state := t) /\
    inline_shared_frame s' = inline_shared_frame t /\
    s'.vs_current_bb = snap.ils_state.vs_current_bb /\
    s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
    t.vs_current_bb = frame.ipf_state.vs_current_bb /\
    t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >>
  `~MEM src.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP]` by
    gvs[inline_ordinary_opcode_def] >>
  drule_all inline_cell_zipper_route_fetch >> strip_tac >>
  qexistsl [`bb`, `dst`] >> simp[] >>
  irule inline_live_ordinary_step >> metis_tac[]
QED

Theorem inline_live_assign_fetch:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  src.inst_opcode = ASSIGN /\ src.inst_operands = [op] /\ src.inst_outputs = [x] /\
  step_inst fuel C src snap.ils_state = OK s' /\
  MEM x (cfgTransform$fn_all_vars a.ia_function) /\
  INJ route.ir_rename (x INSERT snap.ils_defined) UNIV /\
  (!v. op = Var v ==> MEM v (cfgTransform$fn_all_vars a.ia_function) /\
    (retpc_var a.ia_function v ==> retpc_var a.ia_function x)) /\
  inline_cell_at c /\ inline_cell_zipper c frames d /\
  c.ic_fields = inline_inst_fields src /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  inline_cell_var_action frames = route.ir_rename /\
  inline_cell_label_action frames = lab ==>
  ?bb dst t.
    lookup_block d.ic_block d.ic_function.fn_blocks = SOME bb /\
    get_instruction bb d.ic_index = SOME dst /\
    step_inst tfuel Tctx dst frame.ipf_state = OK t /\
    inline_live_stack C cert root
      ((p,a,route,snap with <|ils_state := s';
        ils_defined := x INSERT snap.ils_defined|>)::rest)
      (frame with ipf_state := t) /\
    inline_shared_frame s' = inline_shared_frame t /\
    s'.vs_current_bb = snap.ils_state.vs_current_bb /\
    s'.vs_inst_idx = snap.ils_state.vs_inst_idx /\
    t.vs_current_bb = frame.ipf_state.vs_current_bb /\
    t.vs_inst_idx = frame.ipf_state.vs_inst_idx
Proof
  strip_tac >>
  `~MEM src.inst_opcode [PHI; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP]` by simp[] >>
  drule_all inline_cell_zipper_route_fetch >> strip_tac >>
  qexistsl [`bb`, `dst`] >> simp[] >>
  irule inline_live_assign_step >> gvs[] >> metis_tac[]
QED
