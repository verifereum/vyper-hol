(* Finite evaluator segments, indexed by actual entry and interior body cuts. *)
Theory functionInlinerRecursiveTransport
Ancestors
  functionInlinerSelectedSource functionInlinerSelectedContinuation functionInlinerFrontier
  functionInlinerResidualReturn functionInlinerEvaluatorResidual functionInlinerFmp
  functionInlinerReturnRouting functionInlinerEnvelopes functionInlinerSimulation functionInlinerCuts
  functionInlinerLiveInvariant functionInlinerParameterSequential functionInlinerParameterAncestry
  functionInlinerLiveSteps functionInlinerLiveEdges functionInlinerFuel
  functionInlinerLocation functionInlinerParameterLocations
  functionInlinerActivation functionInlinerSiteLayout cfgTransform
  venomExecSemantics venomExecProofs o1PassLift arithmetic
  functionInlinerOccurrences functionInlinerRoutedProvenance functionInlinerOrigin
  functionInlinerRouteKeys functionInlinerParameterLineage
  functionInlinerFrame venomState venomInst list

Datatype:
  inline_eval_cut = InlineEntry venom_state | InlineBody basic_block venom_state
End

Definition inline_resume_def:
  (inline_resume ctx root h (InlineEntry t) = run_blocks h ctx root t) /\
  (inline_resume ctx root h (InlineBody bb t) =
    case exec_block h ctx bb t of
      OK u => if u.vs_halted then Halt u else run_blocks h ctx root u
    | IntRet ir u => IntRet ir u
    | other => other)
End

Definition inline_segment_def:
  inline_segment ctx root b delta c d <=>
    !h. b <= h ==>
      inline_resume ctx root (h + delta) c = inline_resume ctx root h d
End

Definition inline_terminal_def:
  inline_terminal ctx root b c result <=>
    !h. b <= h ==> inline_resume ctx root h c = result
End

Theorem inline_segment_refl:
  inline_segment ctx root 0 0 c c
Proof simp[inline_segment_def]
QED

Theorem inline_segment_compose:
  inline_segment ctx root b1 d1 c1 c2 /\
  inline_segment ctx root b2 d2 c2 c3 ==>
  inline_segment ctx root (MAX b1 b2) (d2 + d1) c1 c3
Proof
  simp[inline_segment_def] >> rpt strip_tac >>
  `b1 <= h + d2 /\ b2 <= h` by decide_tac >>
  first_x_assum (qspec_then `h` assume_tac) >>
  first_x_assum (qspec_then `h + d2` assume_tac) >>
  gvs[ADD_ASSOC]
QED

Theorem inline_segment_terminal:
  inline_segment ctx root b1 delta c d /\
  inline_terminal ctx root b2 d result ==>
  !h. MAX b1 b2 <= h ==> inline_resume ctx root (h + delta) c = result
Proof
  simp[inline_segment_def, inline_terminal_def] >> rpt strip_tac >>
  `b1 <= h /\ b2 <= h` by decide_tac >> metis_tac[]
QED

Theorem inline_terminal_witness:
  inline_terminal ctx root b c result ==>
  ?h. inline_resume ctx root h c = result
Proof
  simp[inline_terminal_def] >> metis_tac[LESS_EQ_REFL]
QED

Theorem inline_segment_entry_body:
  lookup_block t.vs_current_bb root.fn_blocks = SOME bb /\
  eval_phis t bb.bb_instructions = OK post ==>
  inline_segment ctx root 0 1 (InlineEntry t)
    (InlineBody bb (post with vs_inst_idx := phi_prefix_length bb.bb_instructions))
Proof
  simp[inline_segment_def, inline_resume_def, GSYM ADD1, Once run_blocks_def]
QED

Theorem inline_segment_body_equal:
  (!h. b <= h ==> exec_block h ctx bb t = exec_block h ctx bb' t') ==>
  inline_segment ctx root b 0 (InlineBody bb t) (InlineBody bb' t')
Proof
  simp[inline_segment_def, inline_resume_def]
QED

Theorem inline_segment_body_step:
  get_instruction bb t.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\
  (!h. b <= h ==> step_inst h ctx inst t = OK u) ==>
  inline_segment ctx root b 0 (InlineBody bb t)
    (InlineBody bb (u with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  strip_tac >> irule inline_segment_body_equal >> rpt strip_tac >>
  simp[Once exec_block_def]
QED

Theorem inline_segment_body_jump:
  (!h. b <= h ==> exec_block h ctx bb t = OK u) /\ ~u.vs_halted ==>
  inline_segment ctx root b 0 (InlineBody bb t) (InlineEntry u)
Proof
  simp[inline_segment_def, inline_resume_def]
QED

Theorem inline_terminal_body:
  (!h. b <= h ==> exec_block h ctx bb t = result) /\
  (!u. result <> OK u) ==>
  inline_terminal ctx root b (InlineBody bb t) result
Proof
  strip_tac >> simp[inline_terminal_def, inline_resume_def] >>
  rpt strip_tac >> `exec_block h ctx bb t = result` by metis_tac[] >>
  simp[] >> Cases_on `result` >> gvs[]
QED

Theorem inline_terminal_body_halted:
  (!h. b <= h ==> exec_block h ctx bb t = OK u) /\ u.vs_halted ==>
  inline_terminal ctx root b (InlineBody bb t) (Halt u)
Proof
  simp[inline_terminal_def, inline_resume_def]
QED

Theorem inline_segment_terminal_transport:
  inline_segment ctx root b1 delta c d /\
  inline_terminal ctx root b2 d result ==>
  inline_terminal ctx root (MAX b1 b2 + delta) c result
Proof
  strip_tac >> simp[inline_terminal_def] >> rpt strip_tac >>
  `MAX b1 b2 <= h - delta /\ h = (h - delta) + delta` by decide_tac >>
  drule_all inline_segment_terminal >> simp[]
QED

(* The selected entry jump, empty PHI batch and emitted parameter prefix
   compose into a single actual body resumption. *)
Theorem inline_segment_entry_prefix:
  (!h. b <= h ==> exec_block h ctx tb t = OK v) /\
  ~v.vs_halted /\
  lookup_block v.vs_current_bb root.fn_blocks = SOME bb /\
  eval_phis v bb.bb_instructions = OK v /\
  phi_prefix_length bb.bb_instructions = v.vs_inst_idx /\
  (!h. b <= h ==> exec_block h ctx bb v = exec_block h ctx bb w) ==>
  inline_segment ctx root b 1 (InlineBody tb t) (InlineBody bb w)
Proof
  simp[inline_segment_def, inline_resume_def] >> rpt strip_tac >>
  `b <= h + 1` by decide_tac >>
  `exec_block (h + 1) ctx tb t = OK v` by metis_tac[] >>
  simp[GSYM ADD1, Once run_blocks_def] >>
  `v with vs_inst_idx := v.vs_inst_idx = v` by simp[] >> simp[]
QED

Theorem inline_segment_body_step_at:
  get_instruction bb t.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ step_inst b ctx inst t = OK u ==>
  inline_segment ctx root b 0 (InlineBody bb t)
    (InlineBody bb (u with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  strip_tac >> irule inline_segment_body_step >> simp[] >>
  rpt strip_tac >> irule (cj 1 venomExecPropsTheory.fuel_mono) >>
  simp[] >> qexists `b` >> simp[]
QED

Theorem inline_terminal_body_at:
  exec_block b ctx bb t = result /\ (!e. result <> Error e) /\
  (!u. result <> OK u) ==>
  inline_terminal ctx root b (InlineBody bb t) result
Proof
  strip_tac >> irule inline_terminal_body >> simp[] >> rpt strip_tac >>
  irule (cj 2 venomExecPropsTheory.fuel_mono) >> simp[] >> qexists `b` >> simp[]
QED

Theorem inline_terminal_entry_at:
  run_blocks b ctx root t = result /\ (!e. result <> Error e) ==>
  inline_terminal ctx root b (InlineEntry t) result
Proof
  simp[inline_terminal_def, inline_resume_def] >> rpt strip_tac >>
  irule (cj 3 venomExecPropsTheory.fuel_mono) >> simp[] >> qexists `b` >> simp[]
QED

(* A fixed finite successful trace remains the same trace at larger fuel.
   Unlike equality of residual evaluations, this also covers error residuals. *)
Theorem inline_finite_trace_residual:
  !N ts.
    (!i. i < N ==> ?inst u.
      get_instruction bb (ts i).vs_inst_idx = SOME inst /\
      ~is_terminator inst.inst_opcode /\
      step_inst b ctx inst (ts i) = OK u /\
      ts (SUC i) = u with vs_inst_idx := SUC (ts i).vs_inst_idx) ==>
    !h. b <= h ==>
      exec_block h ctx bb (ts 0) = exec_block h ctx bb (ts N)
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `exec_block h ctx bb (ts 0) = exec_block h ctx bb (ts N)` by
    (first_x_assum irule >> simp[] >>
     rpt strip_tac >> first_x_assum irule >> simp[]) >>
  `N < SUC N` by simp[] >>
  qpat_x_assum `!i. i < SUC N ==> _` (qspec_then `N` mp_tac) >>
  simp[] >> strip_tac >>
  `step_inst h ctx inst (ts N) = OK u` by
    (irule (cj 1 venomExecPropsTheory.fuel_mono) >> simp[] >>
     qexists `b` >> simp[]) >>
  asm_rewrite_tac[] >> simp[Once exec_block_def]
QED

Theorem inline_segment_entry_trace:
  exec_block b ctx tb t = OK v /\ ~v.vs_halted /\
  lookup_block v.vs_current_bb root.fn_blocks = SOME bb /\
  eval_phis v bb.bb_instructions = OK v /\
  phi_prefix_length bb.bb_instructions = v.vs_inst_idx /\ ts 0 = v /\
  (!i. i < N ==> ?inst u.
    get_instruction bb (ts i).vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode /\ step_inst b ctx inst (ts i) = OK u /\
    ts (SUC i) = u with vs_inst_idx := SUC (ts i).vs_inst_idx) ==>
  inline_segment ctx root b 1 (InlineBody tb t) (InlineBody bb (ts N))
Proof
  strip_tac >> irule inline_segment_entry_prefix >> qexists `v` >> simp[] >>
  conj_tac
  >- (drule inline_finite_trace_residual >> simp[]) >>
  rpt strip_tac >> irule (cj 2 venomExecPropsTheory.fuel_mono) >>
  simp[] >> qexists `b` >> simp[]
QED

Theorem inline_parameter_trace_control[local]:
  !N. (!i. i < N ==> ?inst u.
    is_param_opcode inst.inst_opcode /\
    step_inst fuel C inst (ss i) = OK u /\
    ss (SUC i) = u with vs_inst_idx := SUC (ss i).vs_inst_idx) ==>
    (ss N).vs_current_bb = (ss 0).vs_current_bb /\
    (ss N).vs_prev_bb = (ss 0).vs_prev_bb /\
    (ss N).vs_halted = (ss 0).vs_halted
Proof
  Induct >> simp[] >> strip_tac >>
  `((ss N).vs_current_bb = (ss 0).vs_current_bb) /\
   ((ss N).vs_prev_bb = (ss 0).vs_prev_bb) /\
   ((ss N).vs_halted = (ss 0).vs_halted)` by
    (first_x_assum irule >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  first_x_assum (qspec_then `N` strip_assume_tac) >> gvs[] >>
  `~is_terminator inst.inst_opcode /\ ~is_alloca_op inst.inst_opcode /\
   ~is_ext_call_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >>
     gvs[venomInstTheory.is_param_opcode_def, venomInstTheory.is_terminator_def,
         venomInstTheory.is_alloca_op_def, venomInstTheory.is_ext_call_op_def]) >>
  drule_all passSharedFieldTheory.step_inst_preserves_all >> simp[]
QED

Theorem inline_selected_source_segment:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_live_stack C cert root ((p,pa,proute,psnap)::entries) frame /\
  inline_original_child C cfuel pa.ia_id occurrence orig psnap.ils_state r ca res /\
  inline_call_incidence cert root p pa.ia_function l j orig
    (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename ca.ia_function /\
  ca.ia_function.fn_blocks = entry::rest /\
  entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  inline_cell_frame (SelectedJump e) c mid /\
  (clone_function e.ise_prefix e.ise_callee).fn_blocks = eb::blocks /\
  inline_cell_zipper mid frames d /\ d.ic_function = root /\
  MAP (\(tag,next). inline_cell_choice tag) frames = zipper /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  frame.ipf_state.vs_current_bb = d.ic_block /\
  frame.ipf_state.vs_inst_idx = d.ic_index /\ ~frame.ipf_state.vs_halted ==>
  ?k bres ss ml bb tb snap ts.
    cfuel = SUC k /\
    exec_block k C entry (ss (LENGTH params)) = bres /\
    (ss (LENGTH params)).vs_inst_idx = LENGTH params /\
    (ss (LENGTH params)).vs_current_bb = entry.bb_label /\
    (ss (LENGTH params)).vs_prev_bb = NONE /\
    ~(ss (LENGTH params)).vs_halted /\
    phi_prefix_length entry.bb_instructions <= (ss (LENGTH params)).vs_inst_idx /\
    (no_param_insts tail ==>
      no_param_insts (DROP (ss (LENGTH params)).vs_inst_idx entry.bb_instructions)) /\
    (!err. bres <> Error err) /\
    res = (case bres of
      OK z => if z.vs_halted then Halt z else run_blocks k C ca.ia_function z
    | IntRet ir z => IntRet ir z | other => other) /\
    lookup_block d.ic_block root.fn_blocks = SOME tb /\
    lookup_block ml root.fn_blocks = SOME bb /\
    inline_segment Tctx root 0 1 (InlineBody tb frame.ipf_state)
      (InlineBody bb (ts (LENGTH params))) /\
    inline_parameter_boundary_path (InlineEnter e::zipper)
      e.ise_callee entry.bb_label (LENGTH params) root ml (LENGTH params) /\
    (ts (LENGTH params)).vs_current_bb = ml /\
    (ts (LENGTH params)).vs_inst_idx = LENGTH params /\
    ~(ts (LENGTH params)).vs_halted /\
    inline_live_stack C cert root
      ((q,ca,route,snap with <|ils_state := ss (LENGTH params);
        ils_defined := set (FLAT (MAP (\i. i.inst_outputs) params))|>)::
       (p,pa,proute,psnap)::entries)
      (frame with ipf_state := ts (LENGTH params))
Proof
  strip_tac >> drule_all inline_live_selected_source_entry_trace >>
  disch_then (qspecl_then [`0`, `Tctx`] strip_assume_tac) >>
  `((ss (LENGTH params)).vs_current_bb = (ss 0).vs_current_bb) /\
   ((ss (LENGTH params)).vs_prev_bb = (ss 0).vs_prev_bb) /\
   ((ss (LENGTH params)).vs_halted = (ss 0).vs_halted)` by
    (irule inline_parameter_trace_control >>
     qexistsl [`C`,`k`] >> rpt strip_tac >>
     `is_param_opcode (EL i params).inst_opcode` by
       (drule_all callLayoutDefsTheory.param_insts_from_el >>
        simp[callLayoutDefsTheory.param_inst_at_def]) >> metis_tac[]) >>
  `ca.ia_entry.vs_current_bb = entry.bb_label /\
   ca.ia_entry.vs_prev_bb = NONE /\ ~ca.ia_entry.vs_halted` by
    (qpat_x_assum `inline_original_child _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[inline_original_child_def] >> strip_tac >>
     qpat_x_assum `setup_callee _ _ _ = SOME _` mp_tac >>
     simp[setup_callee_def] >> disch_then (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  `~(ts (LENGTH params)).vs_halted` by
    (drule functionInlinerLiveInvariantTheory.inline_live_stack_head_shared >>
     disch_then (mp_tac o Q.AP_TERM `\s. s.vs_halted`) >>
     simp[functionInlinerFrameTheory.inline_shared_frame_def,
          stateFrameTheory.execution_frame_def]) >>
  qexistsl [`k`, `bres`, `ss`, `ml`, `bb`, `tb`, `snap`, `ts`] >> simp[listTheory.DROP_APPEND2] >>
  irule inline_segment_entry_trace >> simp[] >>
  gvs[venomStateTheory.jump_to_def]
QED

(* An activation stops before its own return.  The invoking proof branch,
   not the physical root evaluator, owns the selected return continuation. *)
Definition inline_return_frontier_def:
  inline_return_frontier C Tctx cert root p a route rest frame cut ir u <=>
    ?b delta snap t rb ret path counter rf fuel.
      inline_segment Tctx root b delta cut (InlineBody rb t) /\
      inline_live_stack C cert root ((p,a,route,snap)::rest)
        (frame with ipf_state := t) /\ ~t.vs_halted /\
      lookup_block snap.ils_state.vs_current_bb a.ia_function.fn_blocks = SOME rf /\
      get_instruction rf snap.ils_state.vs_inst_idx = SOME ret /\
      step_inst fuel C ret snap.ils_state = IntRet ir u /\
      ret.inst_opcode <> INVOKE /\
      lookup_block t.vs_current_bb root.fn_blocks = SOME rb /\
      inline_live_location cert root p a path
        (InlineAtInstruction snap.ils_state.vs_inst_idx)
        (InlineAtInstruction t.vs_inst_idx) counter snap.ils_state t
End

Definition inline_activation_outcome_def:
  inline_activation_outcome C Tctx cert root p a route rest frame cut result <=>
    case result of
      IntRet ir u => inline_return_frontier C Tctx cert root p a route rest frame cut ir u
    | Halt u => ?b v. inline_terminal Tctx root b cut (Halt v) /\
        inline_shared_frame u = inline_shared_frame v
    | Abort reason u => ?b v. inline_terminal Tctx root b cut (Abort reason v) /\
        inline_shared_frame u = inline_shared_frame v
    | other => F
End

Theorem inline_activation_return_here:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
  ~frame.ipf_state.vs_halted /\
  lookup_block snap.ils_state.vs_current_bb a.ia_function.fn_blocks = SOME rf /\
  get_instruction rf snap.ils_state.vs_inst_idx = SOME ret /\
  step_inst fuel C ret snap.ils_state = IntRet ir u /\ ret.inst_opcode <> INVOKE /\
  lookup_block frame.ipf_state.vs_current_bb root.fn_blocks = SOME rb /\
  inline_live_location cert root p a path
    (InlineAtInstruction snap.ils_state.vs_inst_idx)
    (InlineAtInstruction frame.ipf_state.vs_inst_idx) counter snap.ils_state frame.ipf_state ==>
  inline_activation_outcome C Tctx cert root p a route rest frame
    (InlineBody rb frame.ipf_state) (IntRet ir u)
Proof
  simp[inline_activation_outcome_def, inline_return_frontier_def] >> strip_tac >>
  qexistsl [`0`, `0`, `snap`, `frame.ipf_state`, `rb`, `ret`, `path`, `counter`, `rf`, `fuel`] >>
  simp[inline_segment_refl]
QED

Theorem inline_activation_outcome_segment:
  inline_segment Tctx root b delta cut mid /\
  inline_activation_outcome C Tctx cert root p a route rest frame mid result ==>
  inline_activation_outcome C Tctx cert root p a route rest frame cut result
Proof
  Cases_on `result` >>
  simp[inline_activation_outcome_def, inline_return_frontier_def] >> strip_tac
  >- (drule_all inline_segment_terminal_transport >> metis_tac[])
  >- (drule_all inline_segment_terminal_transport >> metis_tac[]) >>
  drule_all inline_segment_compose >> metis_tac[]
QED

Theorem inline_activation_halt_here:
  exec_block b Tctx bb t = Halt v /\ inline_shared_frame u = inline_shared_frame v ==>
  inline_activation_outcome C Tctx cert root p a route rest frame
    (InlineBody bb t) (Halt u)
Proof
  simp[inline_activation_outcome_def] >> strip_tac >> qexistsl [`b`, `v`] >>
  simp[] >> irule inline_terminal_body_at >> simp[]
QED

Theorem inline_activation_abort_here:
  exec_block b Tctx bb t = Abort reason v /\
  inline_shared_frame u = inline_shared_frame v ==>
  inline_activation_outcome C Tctx cert root p a route rest frame
    (InlineBody bb t) (Abort reason u)
Proof
  simp[inline_activation_outcome_def] >> strip_tac >> qexistsl [`b`, `v`] >>
  simp[] >> irule inline_terminal_body_at >> simp[]
QED

Theorem inline_activation_entry_body:
  lookup_block t.vs_current_bb root.fn_blocks = SOME bb /\
  eval_phis t bb.bb_instructions = OK post /\
  inline_activation_outcome C Tctx cert root p a route rest frame
    (InlineBody bb (post with vs_inst_idx := phi_prefix_length bb.bb_instructions)) result ==>
  inline_activation_outcome C Tctx cert root p a route rest frame (InlineEntry t) result
Proof
  strip_tac >> irule inline_activation_outcome_segment >>
  goal_assum (drule_at Any) >> qexistsl [`0`, `1`] >>
  irule inline_segment_entry_body >> simp[]
QED

(* Source residual equations used by the fuel/remaining-instructions induction.
   In particular an OK block result is resumed, not identified with the
   completed activation result. *)
Theorem inline_resume_entry_unfold:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK post ==>
  inline_resume C fn (SUC fuel) (InlineEntry s) =
  inline_resume C fn fuel
    (InlineBody bb (post with vs_inst_idx := phi_prefix_length bb.bb_instructions))
Proof
  simp[inline_resume_def, Once run_blocks_def]
QED

Theorem inline_resume_body_next:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  ~is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK u ==>
  inline_resume C fn fuel (InlineBody bb s) =
  inline_resume C fn fuel (InlineBody bb (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  simp[inline_resume_def, Once exec_block_def]
QED

Theorem inline_resume_body_branch:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  is_terminator inst.inst_opcode /\ step_inst fuel C inst s = OK u /\
  ~u.vs_halted ==>
  inline_resume C fn fuel (InlineBody bb s) = inline_resume C fn fuel (InlineEntry u)
Proof
  simp[inline_resume_def, Once exec_block_def]
QED

Theorem inline_resume_body_return:
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel C inst s = IntRet ir u ==>
  inline_resume C fn fuel (InlineBody bb s) = IntRet ir u
Proof
  simp[inline_resume_def, Once exec_block_def]
QED

Theorem inline_boundary_repair_opcode[local]:
  (inline_edit_repair e bb l inst).inst_opcode = inst.inst_opcode
Proof
  simp[inline_edit_repair_def, subst_label_inst_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem inline_boundary_keep_fetch[local]:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  (EL e.ise_index source_bb.bb_instructions).inst_opcode = INVOKE /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block l e.ise_caller.fn_blocks = SOME bb /\
  get_instruction bb j = SOME inst /\ inst.inst_opcode <> INVOKE ==>
  ?ml mj tb ti.
    inline_keep_boundary e l j = (ml,mj) /\
    lookup_block ml e.ise_final.fn_blocks = SOME tb /\
    get_instruction tb mj = SOME ti /\ ti.inst_opcode = inst.inst_opcode /\
    inline_choice_location (InlineKeep e)
      <|il_block := l; il_phase := InlineAtInstruction j; il_counter := k|> =
      SOME <|il_block := ml; il_phase := InlineAtInstruction mj; il_counter := k|>
Proof
  strip_tac >> Cases_on `l = e.ise_block`
  >- (gvs[] >>
      `j < LENGTH bb.bb_instructions /\ inst = EL j bb.bb_instructions` by
        gvs[venomInstTheory.get_instruction_def] >>
      `j <> e.ise_index` by metis_tac[] >>
      `e.ise_index <= LENGTH bb.bb_instructions` by decide_tac >>
      Cases_on `j < e.ise_index`
      >- (drule_all inline_edit_prefix_fetch >>
          simp[inline_fetched_fields_def, inline_inst_fields_def,
               inline_keep_boundary_def, inline_choice_location_def] >>
          metis_tac[inline_boundary_repair_opcode]) >>
      `e.ise_index < j` by decide_tac >>
      drule_all inline_edit_suffix_fetch >>
      simp[inline_fetched_fields_def, inline_inst_fields_def,
           inline_keep_boundary_def, inline_choice_location_def] >>
      metis_tac[inline_boundary_repair_opcode]) >>
  drule_all inline_edit_other_fetch >>
  simp[inline_fetched_fields_def, inline_inst_fields_def,
       inline_keep_boundary_def, inline_choice_location_def] >>
  metis_tac[inline_boundary_repair_opcode]
QED

Theorem inline_boundary_enter_fetch[local]:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  e.ise_index < LENGTH bb.bb_instructions /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block l e.ise_callee.fn_blocks = SOME cb /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  get_instruction cb j = SOME inst /\ inst.inst_opcode <> INVOKE ==>
  ?counter tb ti.
    lookup_block (STRCAT e.ise_prefix l) e.ise_final.fn_blocks = SOME tb /\
    get_instruction tb (LENGTH (FST (inline_cell_prefix e bb cb j))) = SOME ti /\
    ti.inst_opcode <> INVOKE /\
    inline_choice_location (InlineEnter e)
      <|il_block := l; il_phase := InlineAtInstruction j; il_counter := k|> =
      SOME <|il_block := STRCAT e.ise_prefix l;
             il_phase := InlineAtInstruction (LENGTH (FST (inline_cell_prefix e bb cb j)));
             il_counter := counter|>
Proof
  strip_tac >>
  `j < LENGTH cb.bb_instructions /\ inst = EL j cb.bb_instructions` by
    gvs[venomInstTheory.get_instruction_def] >>
  drule_all inline_edit_enter_focus_fetch >>
  simp[LET_THM] >> disch_then (qspec_then `0` mp_tac) >>
  simp[functionInlinerOccurrencesTheory.inline_rewrite_expansion_nonempty] >>
  qmatch_goalsub_abbrev_tac `inline_edit_repair _ _ _ head` >>
  `(clone_instruction e.ise_prefix (fn_labels e.ise_callee)
      (EL j cb.bb_instructions)).inst_opcode <> INVOKE` by
    gvs[functionInlinerDefsTheory.clone_instruction_def] >>
  `head.inst_opcode <> INVOKE` by
    (simp[Abbr `head`] >>
     metis_tac[functionInlinerOccurrencesTheory.inline_rewrite_invoke_cell,
       functionInlinerOccurrencesTheory.inline_rewrite_expansion_nonempty,
       listTheory.EL_def]) >>
  simp[inline_fetched_fields_def, inline_inst_fields_def] >> strip_tac >>
  simp[inline_choice_location_def, functionInlinerReachableCutsTheory.inline_cell_prefix_def] >>
  metis_tac[inline_boundary_repair_opcode]
QED

Theorem inline_boundary_choice_fetch[local]:
  inline_annotated_origin C e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin C e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\
  ((choice = InlineKeep e /\ fn = e.ise_caller) \/
   (choice = InlineEnter e /\ fn = e.ise_callee)) /\
  lookup_block l fn.fn_blocks = SOME sb /\
  get_instruction sb j = SOME inst /\ inst.inst_opcode <> INVOKE /\
  inline_parameter_boundary choice fn l j root ml mj ==>
  ?counter tb ti.
    inline_choice_location choice
      <|il_block := l; il_phase := InlineAtInstruction j; il_counter := k|> =
      SOME <|il_block := ml; il_phase := InlineAtInstruction mj; il_counter := counter|> /\
    lookup_block ml root.fn_blocks = SOME tb /\
    get_instruction tb mj = SOME ti /\ ti.inst_opcode <> INVOKE
Proof
  strip_tac >>
  drule_all functionInlinerOccurrencesTheory.inline_annotated_edit_fetch_facts >>
  strip_tac
  >- (gvs[inline_parameter_boundary_def] >>
      `ALL_DISTINCT (fn_labels e.ise_caller)` by
        metis_tac[functionInlinerOccurrencesTheory.inline_annotated_origin_labels] >>
      `?bb. lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
        e.ise_index < LENGTH bb.bb_instructions /\
        (EL e.ise_index bb.bb_instructions).inst_opcode = INVOKE` by
        (irule functionInlinerWfTheory.find_invoke_site_lookup >>
         gvs[inline_site_edit_valid_def] >> metis_tac[]) >>
      gvs[] >> drule_all inline_boundary_keep_fetch >>
      disch_then (qspec_then `k` strip_assume_tac) >>
      gvs[] >> metis_tac[]) >>
  gvs[inline_parameter_boundary_def] >>
  `MEM l (fn_labels e.ise_callee)` by
    metis_tac[venomExecPropsTheory.lookup_block_label,
      venomExecPropsTheory.lookup_block_MEM, venomInstTheory.fn_labels_def, listTheory.MEM_MAP] >>
  `~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
   STRCAT e.ise_prefix l <> e.ise_return` by metis_tac[] >>
  drule_all inline_boundary_enter_fetch >>
  disch_then (qspec_then `k` strip_assume_tac) >> gvs[] >> metis_tac[]
QED

Theorem inline_boundary_path_fetch[local]:
  !path fn root l j sb inst ml mj k.
    inline_annotated_choice_path C path fn root /\
    lookup_block l fn.fn_blocks = SOME sb /\
    get_instruction sb j = SOME inst /\ inst.inst_opcode <> INVOKE /\
    inline_parameter_boundary_path path fn l j root ml mj ==>
    ?counter tb ti.
      inline_path_location path
        (SOME <|il_block := l; il_phase := InlineAtInstruction j; il_counter := k|>) =
        SOME <|il_block := ml; il_phase := InlineAtInstruction mj; il_counter := counter|> /\
      lookup_block ml root.fn_blocks = SOME tb /\
      get_instruction tb mj = SOME ti /\ ti.inst_opcode <> INVOKE
Proof
  Induct >>
  simp[functionInlinerParameterPropagationTheory.inline_annotated_choice_path_def,
       inline_parameter_boundary_path_def] >> rpt strip_tac >>
  rename1 `inline_parameter_boundary h fn l j mid il ij` >>
  `mid = e.ise_final` by gvs[inline_parameter_boundary_def] >>
  `?counter tb ti.
    inline_choice_location h
      <|il_block := l; il_phase := InlineAtInstruction j; il_counter := k|> =
      SOME <|il_block := il; il_phase := InlineAtInstruction ij; il_counter := counter|> /\
    lookup_block il mid.fn_blocks = SOME tb /\
    get_instruction tb ij = SOME ti /\ ti.inst_opcode <> INVOKE` by
    (irule inline_boundary_choice_fetch >> metis_tac[]) >>
  gvs[] >> first_x_assum drule_all >> strip_tac >>
  simp[inline_path_location_def, listTheory.FOLDL, inline_location_step_def] >>
  metis_tac[inline_path_location_def]
QED

Theorem inline_noninvoke_boundary_location:
  inline_annotated_origin C n root cert /\
  inline_routed_leaf cert root p fn path /\
  lookup_block l fn.fn_blocks = SOME sb /\
  get_instruction sb j = SOME inst /\ inst.inst_opcode <> INVOKE /\
  inline_parameter_boundary_path path fn l j root ml mj ==>
  ?counter.
    inline_path_location path
      (SOME <|il_block := l; il_phase := InlineAtInstruction j; il_counter := 0|>) =
      SOME <|il_block := ml; il_phase := InlineAtInstruction mj; il_counter := counter|>
Proof
  strip_tac >>
  `inline_annotated_choice_path C path fn root` by
    metis_tac[functionInlinerReturnRoutingTheory.inline_routed_leaf_annotated_path] >>
  drule_all inline_boundary_path_fetch >> metis_tac[]
QED

Theorem inline_activation_boundary_return:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inline_routed_leaf cert root p a.ia_function path /\
  ~frame.ipf_state.vs_halted /\
  lookup_block snap.ils_state.vs_current_bb a.ia_function.fn_blocks = SOME rf /\
  get_instruction rf snap.ils_state.vs_inst_idx = SOME ret /\
  step_inst fuel C ret snap.ils_state = IntRet ir u /\ ret.inst_opcode <> INVOKE /\
  lookup_block frame.ipf_state.vs_current_bb root.fn_blocks = SOME rb /\
  inline_parameter_boundary_path path a.ia_function
    snap.ils_state.vs_current_bb snap.ils_state.vs_inst_idx root
    frame.ipf_state.vs_current_bb frame.ipf_state.vs_inst_idx ==>
  inline_activation_outcome C Tctx cert root p a route rest frame
    (InlineBody rb frame.ipf_state) (IntRet ir u)
Proof
  strip_tac >> drule_all inline_noninvoke_boundary_location >> strip_tac >>
  irule inline_activation_return_here >>
  simp[functionInlinerLiveInvariantTheory.inline_live_location_def] >> metis_tac[]
QED

Theorem inline_keep_boundary_ordinary_suc[local]:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb /\
  e.ise_index < LENGTH source_bb.bb_instructions /\
  (EL e.ise_index source_bb.bb_instructions).inst_opcode = INVOKE /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block l e.ise_caller.fn_blocks = SOME sb /\
  get_instruction sb j = SOME inst /\ inst.inst_opcode <> INVOKE /\
  inline_parameter_boundary (InlineKeep e) e.ise_caller l j e.ise_final ml mj ==>
  inline_parameter_boundary (InlineKeep e) e.ise_caller l (SUC j)
    e.ise_final ml (SUC mj)
Proof
  strip_tac >>
  `j < LENGTH sb.bb_instructions` by gvs[venomInstTheory.get_instruction_def] >>
  `l = e.ise_block ==> j <> e.ise_index` by
    (strip_tac >> gvs[venomInstTheory.get_instruction_def] >> metis_tac[]) >>
  `inline_keep_boundary e l (SUC j) = (ml,SUC mj)` by
    (Cases_on `l = e.ise_block` >>
     Cases_on `e.ise_index < j` >>
     gvs[inline_parameter_boundary_def, inline_keep_boundary_def]) >>
  `SUC j <= LENGTH sb.bb_instructions` by decide_tac >>
  drule_all inline_keep_boundary_produce >> simp[]
QED

Theorem inline_enter_boundary_ordinary_suc[local]:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block l e.ise_callee.fn_blocks = SOME cb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  get_instruction cb j = SOME inst /\
  ~MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] /\
  inline_parameter_boundary (InlineEnter e) e.ise_callee l j e.ise_final ml mj ==>
  inline_parameter_boundary (InlineEnter e) e.ise_callee l (SUC j)
    e.ise_final ml (SUC mj)
Proof
  strip_tac >>
  `SUC j <= LENGTH cb.bb_instructions` by
    gvs[venomInstTheory.get_instruction_def] >>
  drule_all functionInlinerReachableCutsTheory.inline_cell_prefix_singleton_suc >>
  disch_then (qspecl_then [`e`,`bb`] strip_assume_tac) >>
  `inline_parameter_boundary (InlineEnter e) e.ise_callee l (SUC j) e.ise_final
    (STRCAT e.ise_prefix l) (LENGTH (FST (inline_cell_prefix e bb cb (SUC j))))` by
    (irule inline_enter_boundary_produce >> metis_tac[]) >>
  gvs[inline_parameter_boundary_def]
QED

Theorem inline_enter_boundary_ordinary_fetch[local]:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  lookup_block l e.ise_callee.fn_blocks = SOME cb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  get_instruction cb j = SOME inst /\
  ~MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP] ==>
  ?tb ti. lookup_block (STRCAT e.ise_prefix l) e.ise_final.fn_blocks = SOME tb /\
    get_instruction tb (LENGTH (FST (inline_cell_prefix e bb cb j))) = SOME ti /\
    ti.inst_opcode = inst.inst_opcode
Proof
  strip_tac >>
  `j < LENGTH cb.bb_instructions /\ inst = EL j cb.bb_instructions` by
    gvs[venomInstTheory.get_instruction_def] >>
  drule_all functionInlinerReachableCutsTheory.inline_cell_focus_singleton >>
  disch_then (qspecl_then [`e`,`bb`] assume_tac) >>
  drule_all inline_edit_enter_focus_fetch >>
  simp[LET_THM] >> disch_then (qspec_then `0` mp_tac) >>
  gvs[functionInlinerReachableCutsTheory.inline_cell_focus_def,
      functionInlinerReachableCutsTheory.inline_cell_prefix_def] >>
  simp[inline_fetched_fields_def, inline_inst_fields_def,
       inline_boundary_repair_opcode, functionInlinerDefsTheory.clone_instruction_def] >>
  metis_tac[]
QED

Theorem inline_boundary_choice_ordinary_suc[local]:
  inline_annotated_origin C e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin C e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\
  ((choice = InlineKeep e /\ fn = e.ise_caller) \/
   (choice = InlineEnter e /\ fn = e.ise_callee)) /\
  lookup_block l fn.fn_blocks = SOME sb /\ get_instruction sb j = SOME inst /\
  ~MEM inst.inst_opcode [INVOKE; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP; PHI] /\
  inline_parameter_boundary choice fn l j root ml mj ==>
  inline_parameter_boundary choice fn l (SUC j) root ml (SUC mj) /\
  ?tb ti. lookup_block ml root.fn_blocks = SOME tb /\
    get_instruction tb mj = SOME ti /\ ti.inst_opcode = inst.inst_opcode
Proof
  strip_tac >>
  drule_all functionInlinerOccurrencesTheory.inline_annotated_edit_fetch_facts >>
  strip_tac
  >- (gvs[] >>
      `root = e.ise_final` by gvs[inline_parameter_boundary_def] >>
      `ALL_DISTINCT (fn_labels e.ise_caller)` by
        metis_tac[functionInlinerOccurrencesTheory.inline_annotated_origin_labels] >>
      `?bb. lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
        e.ise_index < LENGTH bb.bb_instructions /\
        (EL e.ise_index bb.bb_instructions).inst_opcode = INVOKE` by
        (irule functionInlinerWfTheory.find_invoke_site_lookup >>
         gvs[inline_site_edit_valid_def] >> metis_tac[]) >>
      gvs[] >> conj_tac >- (irule inline_keep_boundary_ordinary_suc >> metis_tac[]) >>
      drule_all inline_boundary_keep_fetch >>
      disch_then (qspec_then `0` strip_assume_tac) >>
      gvs[inline_parameter_boundary_def] >> metis_tac[pairTheory.PAIR_EQ]) >>
  gvs[] >>
  `MEM l (fn_labels e.ise_callee)` by
    metis_tac[venomExecPropsTheory.lookup_block_label,
      venomExecPropsTheory.lookup_block_MEM, venomInstTheory.fn_labels_def, listTheory.MEM_MAP] >>
  `~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
   STRCAT e.ise_prefix l <> e.ise_return` by metis_tac[] >>
  `root = e.ise_final` by gvs[inline_parameter_boundary_def] >>
  gvs[] >> conj_tac >- (irule inline_enter_boundary_ordinary_suc >> simp[] >> metis_tac[]) >>
  `~MEM inst.inst_opcode [PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP]` by simp[] >>
  drule inline_enter_boundary_ordinary_fetch >>
  disch_then drule >> disch_then drule >>
  disch_then (qspec_then `j` mp_tac) >>
  simp[] >>
  gvs[inline_parameter_boundary_def] >> metis_tac[]
QED

Theorem inline_boundary_path_ordinary_suc:
  !path fn root l j sb inst ml mj.
    inline_annotated_choice_path C path fn root /\
    lookup_block l fn.fn_blocks = SOME sb /\ get_instruction sb j = SOME inst /\
    ~MEM inst.inst_opcode [INVOKE; PARAM; FMP_PARAM; RETPC_PARAM; RET; RETFMP; PHI] /\
    inline_parameter_boundary_path path fn l j root ml mj ==>
    inline_parameter_boundary_path path fn l (SUC j) root ml (SUC mj)
Proof
  Induct >>
  simp[functionInlinerParameterPropagationTheory.inline_annotated_choice_path_def,
       inline_parameter_boundary_path_def] >> rpt strip_tac >>
  rename1 `inline_parameter_boundary h fn l j mid il ij` >>
  `mid = e.ise_final` by gvs[inline_parameter_boundary_def] >>
  `inline_parameter_boundary h fn l (SUC j) mid il (SUC ij) /\
   ?tb ti. lookup_block il mid.fn_blocks = SOME tb /\
     get_instruction tb ij = SOME ti /\ ti.inst_opcode = inst.inst_opcode` by
    (irule inline_boundary_choice_ordinary_suc >> simp[] >> metis_tac[]) >>
  gvs[] >> first_x_assum drule >> simp[] >> metis_tac[]
QED

Theorem inline_canonical_body_prefix:
  canonical_param_prefix fn ==>
  ?entry rest params tail.
    fn.fn_blocks = entry::rest /\
    entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
    no_param_insts tail /\
    (!j. LENGTH params <= j ==>
      no_param_insts (DROP j entry.bb_instructions)) /\
    EVERY (\bb. no_param_insts bb.bb_instructions) rest
Proof
  simp[callLayoutDefsTheory.canonical_param_prefix_iff] >> rpt strip_tac >>
  rename1 `no_param_insts tailcode` >>
  qexistsl [`entry`,`rest`,`users ++ fmp ++ retpc`,`tailcode`] >>
  simp[listTheory.APPEND_ASSOC] >> rpt strip_tac >>
  simp[listTheory.DROP_APPEND2] >>
  gvs[callLayoutDefsTheory.no_param_insts_def] >>
  metis_tac[rich_listTheory.EVERY_DROP]
QED

Theorem inline_selected_source_body_cut:
  inliner_input_ok C /\ inline_annotated_origin C n root cert /\
  inline_live_stack C cert root ((p,pa,proute,psnap)::entries) frame /\
  inline_original_child C cfuel pa.ia_id occurrence orig psnap.ils_state r ca res /\
  inline_call_incidence cert root p pa.ia_function l j orig
    (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q route.ir_rename ca.ia_function /\
  canonical_param_prefix ca.ia_function /\
  inline_cell_frame (SelectedJump e) c mid /\
  (clone_function e.ise_prefix e.ise_callee).fn_blocks = eb::blocks /\
  inline_cell_zipper mid frames d /\ d.ic_function = root /\
  MAP (\(tag,next). inline_cell_choice tag) frames = zipper /\
  EVERY (\(tag,next). !e. tag <> SelectedJump e) frames /\
  frame.ipf_state.vs_current_bb = d.ic_block /\
  frame.ipf_state.vs_inst_idx = d.ic_index /\ ~frame.ipf_state.vs_halted ==>
  ?entry rest params tail k bres ss ml bb tb snap ts.
    ca.ia_function.fn_blocks = entry::rest /\
    entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
    no_param_insts tail /\ cfuel = SUC k /\
    exec_block k C entry (ss (LENGTH params)) = bres /\
    (ss (LENGTH params)).vs_inst_idx = LENGTH params /\
    (ss (LENGTH params)).vs_current_bb = entry.bb_label /\
    (ss (LENGTH params)).vs_prev_bb = NONE /\
    ~(ss (LENGTH params)).vs_halted /\
    phi_prefix_length entry.bb_instructions <= (ss (LENGTH params)).vs_inst_idx /\
    no_param_insts (DROP (ss (LENGTH params)).vs_inst_idx entry.bb_instructions) /\
    (!err. bres <> Error err) /\
    res = (case bres of
      OK z => if z.vs_halted then Halt z else run_blocks k C ca.ia_function z
    | IntRet ir z => IntRet ir z | other => other) /\
    lookup_block d.ic_block root.fn_blocks = SOME tb /\
    lookup_block ml root.fn_blocks = SOME bb /\
    inline_segment Tctx root 0 1 (InlineBody tb frame.ipf_state)
      (InlineBody bb (ts (LENGTH params))) /\
    inline_parameter_boundary_path (InlineEnter e::zipper)
      e.ise_callee entry.bb_label (LENGTH params) root ml (LENGTH params) /\
    (ts (LENGTH params)).vs_current_bb = ml /\
    (ts (LENGTH params)).vs_inst_idx = LENGTH params /\
    ~(ts (LENGTH params)).vs_halted /\
    inline_live_stack C cert root
      ((q,ca,route,snap with <|ils_state := ss (LENGTH params);
        ils_defined := set (FLAT (MAP (\i. i.inst_outputs) params))|>)::
       (p,pa,proute,psnap)::entries)
      (frame with ipf_state := ts (LENGTH params))
Proof
  strip_tac >> drule inline_canonical_body_prefix >> strip_tac >>
  drule_all inline_selected_source_segment >>
  disch_then (qspec_then `Tctx` strip_assume_tac) >>
  qexistsl [`entry`,`rest`,`params`,`tail`,`k`,`bres`,`ss`,`ml`,`bb`,`tb`,`snap`,`ts`] >>
  simp[]
QED


Theorem inline_parameter_prefix_boundary[local]:
  inline_annotated_choice_path C path fn root /\
  inline_path_rename path = I /\
  lookup_block l fn.fn_blocks = SOME bb /\
  bb.bb_instructions = params ++ tail /\ param_insts_from 0 params ==>
  inline_parameter_boundary_path path fn l (LENGTH params)
    root l (LENGTH params)
Proof
  strip_tac >>
  `inline_parameter_interval fn l 0 (LENGTH params)` by
    (simp[inline_parameter_interval_def] >>
     rpt strip_tac >> disj1_tac >>
     drule_all callLayoutDefsTheory.param_insts_from_el >>
     simp[callLayoutDefsTheory.param_inst_at_def, listTheory.EL_APPEND_EQN]) >>
  drule_all inline_parameter_interval_transport >> strip_tac >>
  drule functionInlinerEntryHandoffTheory.inline_parameter_boundary_path_zero >>
  simp[] >> strip_tac >> gvs[]
QED

Theorem inline_selected_body_routed_boundary:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_namespace_leaf_at cert q sigma child /\
  child.fn_blocks = entry::rest /\
  entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  inline_parameter_boundary_path (InlineEnter e::zipper)
    e.ise_callee entry.bb_label (LENGTH params) root ml mj ==>
  ?path. inline_routed_leaf cert root q child path /\
    inline_parameter_boundary_path path child entry.bb_label (LENGTH params)
      root ml mj
Proof
  strip_tac >>
  drule functionInlinerPairedSelectionTheory.inline_selected_paired_separation >>
  simp[] >> disch_then drule >> strip_tac >>
  drule functionInlinerOccurrencesTheory.inline_annotated_entry_route >> strip_tac >>
  qpat_x_assum `!prefix. inline_routed_leaf _ _ _ _ _ ==> _` drule >> strip_tac >>
  `child = inline_entry_function b` by
    (drule functionInlinerRoutedProvenanceTheory.inline_routed_leaf_namespace >>
     strip_tac >>
     gvs[functionInlinerEnvelopesTheory.inline_namespace_leaf_at_def] >>
     imp_res_tac functionInlinerSelectedParameterDescriptorsTheory.inline_namespace_node_same_address >>
     qpat_x_assum `InlineNamespaceLeaf child = InlineNamespaceLeaf (inline_entry_function b)` mp_tac >>
     simp[NoAsms]) >>
  qpat_assum `inline_routed_leaf b e.ise_callee _ _ _`
    (mp_then Any mp_tac functionInlinerReturnRoutingTheory.inline_routed_leaf_annotated_path) >>
  disch_then drule >> strip_tac >>
  `lookup_block entry.bb_label child.fn_blocks = SOME entry` by
    (gvs[venomInstTheory.lookup_block_def, listTheory.FIND_thm]) >>
  qpat_x_assum `child = inline_entry_function b` (fn th => fs[GSYM th]) >>
  drule_all inline_parameter_prefix_boundary >> strip_tac >>
  qexists `path' ++ [InlineEnter e] ++ zipper` >>
  conj_tac >- metis_tac[] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  irule inline_parameter_boundary_path_append >>
  qexistsl [`e.ise_callee`, `LENGTH params`, `entry.bb_label`] >> simp[]
QED

Theorem inline_phi_prefix_at[local]:
  j < phi_prefix_length xs ==>
  j < LENGTH xs /\ (EL j xs).inst_opcode = PHI
Proof
  strip_tac >>
  qspec_then `xs` mp_tac analysisSimProofsBaseTheory.phi_prefix_all_phi >>
  simp[listTheory.EVERY_EL, listTheory.LENGTH_TAKE, venomExecProofsTheory.phi_prefix_length_le] >>
  metis_tac[listTheory.EL_TAKE, venomExecProofsTheory.phi_prefix_length_le,
    arithmeticTheory.LESS_LESS_EQ_TRANS]
QED

Theorem inline_phi_cell_prefix_length[local]:
  !j. j <= phi_prefix_length cb.bb_instructions ==>
    LENGTH (FST (inline_cell_prefix e bb cb j)) = j
Proof
  Induct >- simp[] >> strip_tac >>
  `j < LENGTH cb.bb_instructions /\
   (EL j cb.bb_instructions).inst_opcode = PHI` by
    (irule inline_phi_prefix_at >> decide_tac) >>
  `get_instruction cb j = SOME (EL j cb.bb_instructions)` by
    simp[venomInstTheory.get_instruction_def] >>
  drule functionInlinerReachableCutsTheory.inline_cell_prefix_singleton_suc >> simp[]
QED

Theorem inline_routed_phi_prefix_boundary:
  !cert root p fn path. inline_routed_leaf cert root p fn path ==>
  !C n l sb.
    inline_annotated_origin C n root cert /\
    lookup_block l fn.fn_blocks = SOME sb ==>
    ?tb. lookup_block (inline_path_rename path l) root.fn_blocks = SOME tb /\
      phi_prefix_length tb.bb_instructions = phi_prefix_length sb.bb_instructions /\
      inline_parameter_boundary_path path fn l (phi_prefix_length sb.bb_instructions)
        root (inline_path_rename path l) (phi_prefix_length tb.bb_instructions)
Proof
  ho_match_mp_tac functionInlinerRoutedProvenanceTheory.inline_routed_leaf_strongind >> rpt conj_tac
  >- simp[inline_parameter_boundary_path_def, functionInlinerRoutedProvenanceTheory.inline_path_rename_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule functionInlinerOccurrencesTheory.inline_annotated_origin_edit_elim >>
  simp[] >> strip_tac >>
  first_x_assum (drule_then (drule_then assume_tac)) >>
  gvs[] >>
  drule_all functionInlinerOccurrencesTheory.inline_annotated_edit_fetch_facts >>
  strip_tac >>
  `wf_function e.ise_caller /\ inliner_phi_labels_closed e.ise_callee` by
    metis_tac[functionInlinerEnvelopesTheory.inline_annotated_origin_erasure,
      functionInlinerOriginTheory.qualified_origin_erasure,
      functionInlinerOriginTheory.inliner_fn_origin_structure,
      functionInlinerOriginTheory.qualified_origin_phi_labels_closed] >>
  `ALL_DISTINCT (fn_labels e.ise_caller) /\ fn_succs_closed e.ise_caller` by
    gvs[venomWfTheory.wf_function_def] >>
  rename1 `lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source_bb` >>
  `!z. MEM z (bb_succs <|bb_label := e.ise_return;
       bb_instructions := DROP (e.ise_index+1) source_bb.bb_instructions|>) ==>
      MEM z (fn_labels e.ise_caller)` by
    (Cases_on `e.ise_index+1 < LENGTH source_bb.bb_instructions`
     >- metis_tac[functionInlinerSimulationTheory.inline_saved_suffix_succs_closed] >>
     simp[listTheory.DROP_LENGTH_TOO_LONG, venomInstTheory.bb_succs_def])
  >- (qpat_assum `lookup_block _ e.ise_caller.fn_blocks = SOME tb`
     (mp_then (Pat `lookup_block l e.ise_caller.fn_blocks = SOME bb`)
       mp_tac functionInlinerReachableCutsTheory.inline_edit_keep_phi_prefix_fields) >>
   disch_then (qspec_then `source_bb` mp_tac) >> simp[] >> strip_tac >>
   `phi_prefix_length sb.bb_instructions <= LENGTH tb.bb_instructions` by
     metis_tac[venomExecProofsTheory.phi_prefix_length_le] >>
   `phi_prefix_length tb'.bb_instructions = phi_prefix_length sb.bb_instructions` by
     (qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `LENGTH`) >>
      simp[listTheory.LENGTH_TAKE, venomExecProofsTheory.phi_prefix_length_le]) >>
   `inline_path_rename path l = e.ise_block ==>
      phi_prefix_length sb.bb_instructions <= e.ise_index` by
     (strip_tac >> gvs[] >>
      `(EL e.ise_index source_bb.bb_instructions).inst_opcode = INVOKE` by
        (gvs[inline_site_edit_valid_def] >>
         drule_all functionInlinerWfTheory.find_invoke_site_lookup >> simp[]) >>
      spose_not_then assume_tac >>
      `e.ise_index < phi_prefix_length source_bb.bb_instructions` by decide_tac >>
      drule inline_phi_prefix_at >> simp[]) >>
   simp[functionInlinerRoutedProvenanceTheory.inline_path_rename_append,
     functionInlinerRoutedProvenanceTheory.inline_path_rename_def,
     functionInlinerActivationTheory.inline_choice_rename_def, combinTheory.o_DEF] >>
   irule functionInlinerSelectedContinuationTheory.inline_parameter_boundary_path_append >>
   qexistsl [`e.ise_caller`, `phi_prefix_length sb.bb_instructions`,
     `inline_path_rename path l`] >>
   simp[inline_parameter_boundary_path_def, inline_parameter_boundary_def,
     inline_keep_boundary_def] >>
   conj_tac
   >- (IF_CASES_TAC >> gvs[] >> decide_tac) >>
   metis_tac[venomExecProofsTheory.phi_prefix_length_le]) >>
  `MEM (inline_path_rename path l) (fn_labels e.ise_callee)` by
    metis_tac[venomExecPropsTheory.lookup_block_label,
      venomExecPropsTheory.lookup_block_MEM, venomInstTheory.fn_labels_def,
      listTheory.MEM_MAP] >>
  qpat_assum `lookup_block _ e.ise_callee.fn_blocks = SOME tb`
    (mp_then (Pat `lookup_block l e.ise_callee.fn_blocks = SOME bb`)
      mp_tac functionInlinerReachableCutsTheory.inline_edit_enter_phi_prefix_fields) >>
  disch_then (qspec_then `source_bb` mp_tac) >> simp[] >> strip_tac >>
  `phi_prefix_length sb.bb_instructions <= LENGTH tb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le] >>
  `phi_prefix_length tb'.bb_instructions = phi_prefix_length sb.bb_instructions` by
    (qpat_x_assum `MAP _ _ = MAP _ _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[listTheory.LENGTH_TAKE, venomExecProofsTheory.phi_prefix_length_le]) >>
  `LENGTH (FST (inline_cell_prefix e source_bb tb
       (phi_prefix_length sb.bb_instructions))) = phi_prefix_length sb.bb_instructions` by
    (irule inline_phi_cell_prefix_length >> simp[]) >>
  simp[functionInlinerRoutedProvenanceTheory.inline_path_rename_append,
    functionInlinerRoutedProvenanceTheory.inline_path_rename_def,
    functionInlinerActivationTheory.inline_choice_rename_def, combinTheory.o_DEF] >>
  irule functionInlinerSelectedContinuationTheory.inline_parameter_boundary_path_append >>
  qexistsl [`e.ise_callee`, `phi_prefix_length sb.bb_instructions`,
    `inline_path_rename path l`] >>
  simp[inline_parameter_boundary_path_def, inline_parameter_boundary_def] >>
  metis_tac[venomExecProofsTheory.phi_prefix_length_le]
QED

Theorem inline_live_phi_body_boundary:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
  inline_annotated_origin C n root cert /\
  inline_routed_leaf cert root p a.ia_function path /\
  route.ir_rename = inline_path_rename path /\
  lookup_block snap.ils_state.vs_current_bb a.ia_function.fn_blocks = SOME sb /\
  lookup_block frame.ipf_state.vs_current_bb root.fn_blocks = SOME tb /\
  (!q. snap.ils_state.vs_prev_bb = SOME q ==> MEM q (fn_labels a.ia_function)) /\
  inline_phi_entry_path path (snap.ils_state.vs_current_bb,snap.ils_state.vs_prev_bb) =
    (frame.ipf_state.vs_current_bb,frame.ipf_state.vs_prev_bb) /\
  ~snap.ils_state.vs_halted /\ ~frame.ipf_state.vs_halted /\
  eval_phis snap.ils_state sb.bb_instructions = OK u ==>
  ?v. eval_phis frame.ipf_state tb.bb_instructions = OK v /\
    let su = u with vs_inst_idx := phi_prefix_length sb.bb_instructions;
        tv = v with vs_inst_idx := phi_prefix_length tb.bb_instructions
    in inline_live_stack C cert root
      ((p,a,route,snap with <|ils_state := su;
        ils_defined := inline_phi_outputs sb.bb_instructions UNION snap.ils_defined|>)::rest)
      (frame with ipf_state := tv) /\
      inline_parameter_boundary_path path a.ia_function su.vs_current_bb su.vs_inst_idx
        root tv.vs_current_bb tv.vs_inst_idx /\
      ~su.vs_halted /\ ~tv.vs_halted
Proof
  strip_tac >>
  drule_all functionInlinerLiveStepsTheory.inline_live_phi_body_cut >> strip_tac >>
  drule_all inline_routed_phi_prefix_boundary >> strip_tac >>
  `inline_path_rename path snap.ils_state.vs_current_bb = frame.ipf_state.vs_current_bb` by
    metis_tac[functionInlinerReachableCutsTheory.inline_phi_entry_path_label, pairTheory.FST] >>
  gvs[] >>
  metis_tac[venomExecProofsTheory.eval_phis_preserves_halted]
QED

(* Root prefixes evolve the current locals without changing the activation's
   immutable entry, saved state, or physical anchor. *)
Theorem inline_root_same_state_storage[local]:
  inline_annotated_origin C n root cert /\
  a.ia_function = inline_entry_function cert /\
  a.ia_entry.vs_labels = FEMPTY /\
  inline_caller_bookkeeping a.ia_entry s /\
  s.vs_fmp = a.ia_entry.vs_fmp ==>
  inline_live_stack C cert root
    [(inline_entry_address cert,a,inline_route_identity a.ia_id,
      <|ils_state := s; ils_saved := a.ia_entry; ils_entry := a.ia_entry;
        ils_defined := {x | MEM x (cfgTransform$fn_all_vars a.ia_function) /\
                           IS_SOME (lookup_var x s)};
        ils_opaque := retpc_var a.ia_function; ils_protected := {};
        ils_parent_rename := I|>)]
    <|ipf_state := s; ipf_anchor := a.ia_entry|>
Proof
  strip_tac >>
  `inline_namespace_leaf_at cert (inline_entry_address cert) I a.ia_function` by
    metis_tac[functionInlinerOccurrencesTheory.inline_entry_leaf] >>
  simp[functionInlinerLiveInvariantTheory.inline_live_stack_def,
       functionInlinerOperationalCutsTheory.inline_owner_storage_def,
       functionInlinerStackSupportsTheory.inline_address_stack_def,
       functionInlinerStackSupportsTheory.inline_address_entry_def,
       functionInlinerStackSupportsTheory.inline_address_links_def,
       functionInlinerStackSupportsTheory.inline_erase_addresses_def,
       functionInlinerCutsTheory.inline_suspended_observations_def,
       functionInlinerCutsTheory.inline_tracked_snapshot_def,
       inline_snapshot_data_def, inline_route_identity_def,
       functionInlinerParameterSavedReadsTheory.inline_parameter_saved_reads_def,
       pred_setTheory.SUBSET_DEF] >>
  gvs[functionInlinerSimulationTheory.inline_caller_bookkeeping_def] >>
  metis_tac[functionInlinerParameterAncestryTheory.inline_parameter_ancestry_rules]
QED

Theorem inline_root_parameter_step[local]:
  is_param_opcode inst.inst_opcode /\ step_inst fuel C inst s = OK t ==>
  step_inst tfuel Tctx inst s = OK t /\
  inline_caller_bookkeeping s (t with vs_inst_idx := i) /\
  (t with vs_inst_idx := i).vs_fmp = s.vs_fmp /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_prev_bb = s.vs_prev_bb /\
  t.vs_halted = s.vs_halted /\ t.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >> gvs[venomInstTheory.is_param_opcode_iff] >>
  gvs[step_inst_def, step_inst_base_opcode_eqs, AllCaseEqs(),
      venomStateTheory.update_var_def,
      functionInlinerSimulationTheory.inline_caller_bookkeeping_def]
QED

Theorem inline_root_parameter_trace[local]:
  (!k. k < N ==> ?inst t.
    is_param_opcode inst.inst_opcode /\
    step_inst fuel C inst (ss k) = OK t /\
    ss (SUC k) = t with vs_inst_idx := SUC (ss k).vs_inst_idx) ==>
  !k. k <= N ==>
    inline_caller_bookkeeping (ss 0) (ss k) /\
    (ss k).vs_fmp = (ss 0).vs_fmp /\
    (ss k).vs_current_bb = (ss 0).vs_current_bb /\
    (ss k).vs_prev_bb = (ss 0).vs_prev_bb /\
    (ss k).vs_halted = (ss 0).vs_halted /\
    (ss k).vs_inst_idx = (ss 0).vs_inst_idx + k
Proof
  strip_tac >> Induct >- simp[] >> strip_tac >>
  `k < N /\ k <= N` by decide_tac >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `!k. k < N ==> _` (qspec_then `k` mp_tac) >>
  simp[] >> strip_tac >>
  drule_all inline_root_parameter_step >> strip_tac >>
  gvs[functionInlinerSimulationTheory.inline_caller_bookkeeping_def]
QED

Theorem inline_root_parameter_fetched_trace[local]:
  inline_annotated_origin C n root cert /\
  (inline_entry_function cert).fn_blocks = entry::rest /\
  entry.bb_instructions = params ++ tail /\ param_insts_from 0 params /\
  (ss 0).vs_inst_idx = 0 /\
  (!k. k < LENGTH params ==> ?t.
    step_inst fuel C (EL k params) (ss k) = OK t /\
    ss (SUC k) = t with vs_inst_idx := SUC (ss k).vs_inst_idx) ==>
  ?eb. lookup_block entry.bb_label root.fn_blocks = SOME eb /\
    (!k. k < LENGTH params ==> ?dst t.
      get_instruction eb (ss k).vs_inst_idx = SOME dst /\
      step_inst tfuel Tctx dst (ss k) = OK t /\
      ss (SUC k) = t with vs_inst_idx := SUC (ss k).vs_inst_idx /\
      ~is_terminator dst.inst_opcode)
Proof
  strip_tac >>
  drule functionInlinerEntryParametersTheory.inline_annotated_entry_parameter_prefix >>
  disch_then (qspecl_then [`entry`,`rest`,`params`,`tail`] mp_tac) >>
  simp[] >> strip_tac >> qexists `eb` >> simp[] >>
  `!k. k < LENGTH params ==> is_param_opcode (EL k params).inst_opcode` by
    (rpt strip_tac >> drule_all callLayoutDefsTheory.param_insts_from_el >>
     simp[callLayoutDefsTheory.param_inst_at_def]) >>
  `!k. k <= LENGTH params ==> (ss k).vs_inst_idx = k` by
    (rpt strip_tac >>
     mp_tac (inline_root_parameter_trace |> Q.INST [`N` |-> `LENGTH (params:instruction list)`]) >>
     (impl_tac >- metis_tac[]) >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `inline_inst_fields (EL k ps) = inline_inst_fields (EL k params)` by
    metis_tac[listTheory.EL_MAP] >>
  qexists `EL k ps` >>
  simp[venomInstTheory.get_instruction_def, listTheory.EL_APPEND_EQN] >>
  `is_param_opcode (EL k params).inst_opcode` by simp[] >>
  qpat_x_assum `!k. k < LENGTH params ==> ?t. _` (qspec_then `k` mp_tac) >>
  simp[] >> strip_tac >>
  qexists `t` >> simp[] >>
  qpat_x_assum `!k. k < LENGTH params ==> is_param_opcode _` kall_tac >>
  gvs[venomInstTheory.is_param_opcode_iff, inline_inst_fields_def] >>
  gvs[step_inst_def, step_inst_base_opcode_eqs, venomInstTheory.is_terminator_def]
QED

Theorem inline_keep_current_boundary[local]:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  e.ise_index < LENGTH bb.bb_instructions /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  lookup_block l e.ise_caller.fn_blocks = SOME cb /\
  get_instruction cb j = SOME inst /\
  inline_choice_location (InlineKeep e)
    <|il_block := l; il_phase := InlineAtInstruction j; il_counter := k|> =
    SOME <|il_block := ml; il_phase := InlineAtInstruction mj; il_counter := next|> ==>
  inline_parameter_boundary (InlineKeep e) e.ise_caller l j e.ise_final ml mj
Proof
  strip_tac >>
  `j <= LENGTH cb.bb_instructions` by gvs[venomInstTheory.get_instruction_def] >>
  drule_all inline_keep_boundary_produce >>
  gvs[inline_choice_location_def, inline_keep_boundary_def] >>
  Cases_on `l = e.ise_block` >> gvs[] >>
  Cases_on `e.ise_index < j` >> gvs[]
QED

Theorem inline_enter_current_boundary[local]:
  inline_site_edit_valid e /\
  lookup_block e.ise_block e.ise_caller.fn_blocks = SOME bb /\
  ~MEM e.ise_return (fn_labels e.ise_caller) /\
  ~MEM (STRCAT e.ise_prefix l) (fn_labels e.ise_caller) /\
  STRCAT e.ise_prefix l <> e.ise_return /\
  lookup_block l e.ise_callee.fn_blocks = SOME cb /\
  get_instruction cb j = SOME inst /\
  inline_choice_location (InlineEnter e)
    <|il_block := l; il_phase := InlineAtInstruction j; il_counter := k|> =
    SOME <|il_block := ml; il_phase := InlineAtInstruction mj; il_counter := next|> ==>
  inline_parameter_boundary (InlineEnter e) e.ise_callee l j e.ise_final ml mj
Proof
  strip_tac >>
  `j <= LENGTH cb.bb_instructions` by gvs[venomInstTheory.get_instruction_def] >>
  drule_all inline_enter_boundary_produce >>
  gvs[inline_choice_location_def, functionInlinerReachableCutsTheory.inline_cell_prefix_def]
QED

Theorem inline_residual_current_path[local]:
  !cert root p fn l j orig outcome.
    inline_call_incidence cert root p fn l j orig outcome ==>
    !C n loc inst k.
      inline_annotated_origin C n root cert /\
      outcome = InlineResidual loc inst /\ loc.il_phase = InlineAtInstruction k ==>
      ?path. inline_routed_leaf cert root p fn path /\
        inline_parameter_boundary_path path fn l j root loc.il_block k
Proof
  ho_match_mp_tac inline_call_incidence_strongind >> rpt conj_tac >> simp[]
  >- (rpt strip_tac >> qexists `[]` >>
      simp[inline_parameter_boundary_path_def, inline_routed_leaf_rules]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  drule inline_annotated_origin_edit_elim >> simp[] >> strip_tac >>
  `?i. loc.il_phase = InlineAtInstruction i` by
    metis_tac[inline_call_incidence_residual_phase] >>
  qpat_x_assum `!C n k. _`
    (qspecl_then [`C`, `e.ise_state.is_inline_count`, `i`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all inline_annotated_edit_fetch_facts >> strip_tac
  >- (qexists `path ++ [InlineKeep e]` >>
      conj_tac >- metis_tac[inline_routed_leaf_rules] >>
      irule inline_parameter_boundary_path_append >> goal_assum (drule_at Any) >>
      simp[inline_parameter_boundary_path_def] >>
      `?cb current. lookup_block loc.il_block e.ise_caller.fn_blocks = SOME cb /\
        get_instruction cb i = SOME current` by
        (drule inline_call_incidence_residual_fetch >>
         disch_then (qspecl_then [`C`, `e.ise_state.is_inline_count`, `loc`, `inst`] mp_tac) >>
         simp[inline_fetched_fields_def] >> metis_tac[]) >>
      `loc = <|il_block := loc.il_block; il_phase := InlineAtInstruction i;
        il_counter := loc.il_counter|>` by simp[inline_location_component_equality] >>
      `loc' = <|il_block := loc'.il_block; il_phase := InlineAtInstruction k;
        il_counter := loc'.il_counter|>` by simp[inline_location_component_equality] >>
      irule inline_keep_current_boundary >> metis_tac[]) >>
  qexists `path ++ [InlineEnter e]` >>
  conj_tac >- metis_tac[inline_routed_leaf_rules] >>
  irule inline_parameter_boundary_path_append >> goal_assum (drule_at Any) >>
  simp[inline_parameter_boundary_path_def] >>
  `?cb current. lookup_block loc.il_block e.ise_callee.fn_blocks = SOME cb /\
    get_instruction cb i = SOME current` by
    (drule inline_call_incidence_residual_fetch >>
     disch_then (qspecl_then [`C`, `e.ise_state.is_inline_count`, `loc`, `inst`] mp_tac) >>
     simp[inline_fetched_fields_def] >> metis_tac[]) >>
  `MEM loc.il_block (fn_labels e.ise_callee)` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,
      venomExecPropsTheory.lookup_block_label, fn_labels_def, MEM_MAP] >>
  `loc = <|il_block := loc.il_block; il_phase := InlineAtInstruction i;
    il_counter := loc.il_counter|>` by simp[inline_location_component_equality] >>
  `loc' = <|il_block := loc'.il_block; il_phase := InlineAtInstruction k;
    il_counter := loc'.il_counter|>` by simp[inline_location_component_equality] >>
  irule inline_enter_current_boundary >> metis_tac[]
QED

(* The three clauses share a fuel, but not a phase.  INITIAL and ENTRY
   consume a run_blocks layer before BODY; residual INVOKE uses INITIAL
   at BODY's fuel, not a fictitious smaller child fuel. *)
Theorem inline_residual_arguments[local]:
  inline_call_incidence cert root p fn l j orig (InlineResidual loc dst) /\
  inline_annotated_origin C n root cert /\
  inline_routed_leaf cert root p fn path /\
  decode_invoke orig = SOME (nm,ops) /\
  s.vs_labels = FEMPTY /\ eval_operands ops s = SOME args ==>
  decode_invoke dst = SOME (nm,MAP (inline_rename_operand (inline_path_rename path) I) ops) /\
  dst.inst_outputs = MAP (inline_path_rename path) orig.inst_outputs
Proof
  strip_tac >>
  `EVERY (\op. !name. op <> Label name) ops` by
    (`EVERY (\op. IS_SOME (eval_operand op s)) ops` by
       simp[GSYM eval_operands_IS_SOME_EVERY] >>
     fs[EVERY_MEM] >> rpt strip_tac >> gvs[] >>
     qpat_x_assum `!op. MEM op ops ==> IS_SOME _`
       (qspec_then `Label name` mp_tac) >> simp[eval_operand_def]) >>
  `?actual. orig.inst_operands = Label nm::ops /\
     dst.inst_operands = Label nm::actual` by
    (drule inline_call_incidence_residual_target >>
     disch_then (qspecl_then [`C`,`n`,`loc`,`dst`] mp_tac) >>
     simp[] >> strip_tac >> gvs[decode_invoke_def]) >>
  drule inline_call_incidence_residual_routing >>
  disch_then (qspecl_then [`loc`,`dst`] mp_tac) >> simp[] >> strip_tac >>
  `inline_path_rename path' = inline_path_rename path` by
    metis_tac[inline_routed_leaf_key_unique, inline_path_key_rename] >>
  `actual = MAP (inline_rename_operand (inline_path_rename path') I) ops` by
    (irule LIST_EQ >>
     `LENGTH actual = LENGTH ops` by
       (qspec_then `path'` (qspec_then `orig.inst_operands` mp_tac)
          inline_call_operand_fold_length >> metis_tac[LENGTH, prim_recTheory.INV_SUC_EQ]) >>
     simp[] >> rpt strip_tac >>
     qspec_then `path'` (qspecl_then [`Label nm::ops`,`SUC x`,`I`] mp_tac)
       inline_call_operand_fold_value >>
     fs[EVERY_EL] >> simp[] >>
     qpat_x_assum `Label nm::actual = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[EL_MAP, EL]) >>
  gvs[decode_invoke_def] >>
  qpat_x_assum `Label nm::_ = _` (fn th => rewrite_tac[GSYM th]) >> simp[]
QED

Definition inline_transport_family_def:
  inline_transport_family C Tctx R <=>
    (!root cert. R root cert ==> ?n. inline_annotated_origin C n root cert) /\
    (!root cert p fn l j orig loc inst name args child.
      R root cert /\
      inline_call_incidence cert root p fn l j orig (InlineResidual loc inst) /\
      decode_invoke orig = SOME (name,args) /\
      lookup_function name C.ctx_functions = SOME child ==>
      ?target cert'. lookup_function name Tctx.ctx_functions = SOME target /\
        inline_entry_function cert' = child /\ R target cert')
End

Definition inline_physical_outcome_def:
  inline_physical_outcome Tctx root cut result <=>
    case result of
      IntRet ir u => ?b v. inline_terminal Tctx root b cut (IntRet ir v) /\
        inline_shared_frame u = inline_shared_frame v
    | Halt u => ?b v. inline_terminal Tctx root b cut (Halt v) /\
        inline_shared_frame u = inline_shared_frame v
    | Abort reason u => ?b v. inline_terminal Tctx root b cut (Abort reason v) /\
        inline_shared_frame u = inline_shared_frame v
    | other => F
End

Definition inline_transport_initial_def:
  inline_transport_initial C Tctx R fuel <=>
    !root cert fn s result.
      R root cert /\ fn = inline_entry_function cert /\
      fn.fn_blocks <> [] /\ s.vs_labels = FEMPTY /\ ~s.vs_halted /\
      s.vs_current_bb = (HD fn.fn_blocks).bb_label /\ s.vs_inst_idx = 0 /\
      run_blocks fuel C fn s = result /\
      (!err. result <> Error err) /\ (!u. result <> OK u) ==>
      inline_physical_outcome Tctx root (InlineEntry s) result
End

Definition inline_transport_entry_def:
  inline_transport_entry C Tctx R fuel <=>
    !root cert p a route snap rest frame path sb tb completed_fuel result.
      R root cert /\
      inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
      inline_frontier_stack ((p,a,route,snap)::rest) frame /\
      inline_namespace_leaf_at cert p route.ir_rename a.ia_function /\
      inline_routed_leaf cert root p a.ia_function path /\
      route.ir_rename = inline_path_rename path /\
      ~snap.ils_state.vs_halted /\ ~frame.ipf_state.vs_halted /\
      lookup_block snap.ils_state.vs_current_bb a.ia_function.fn_blocks = SOME sb /\
      lookup_block frame.ipf_state.vs_current_bb root.fn_blocks = SOME tb /\
      a.ia_function.fn_blocks <> [] /\
      snap.ils_state.vs_current_bb <> (HD a.ia_function.fn_blocks).bb_label /\
      (!q. snap.ils_state.vs_prev_bb = SOME q ==> MEM q (fn_labels a.ia_function)) /\
      inline_phi_entry_path path
        (snap.ils_state.vs_current_bb,snap.ils_state.vs_prev_bb) =
        (frame.ipf_state.vs_current_bb,frame.ipf_state.vs_prev_bb) /\
      run_blocks completed_fuel C a.ia_function a.ia_entry = result /\
      inline_resume C a.ia_function fuel (InlineEntry snap.ils_state) = result /\
      (!err. result <> Error err) /\ (!u. result <> OK u) ==>
      inline_activation_outcome C Tctx cert root p a route rest frame
        (InlineEntry frame.ipf_state) result
End

Definition inline_transport_body_def:
  inline_transport_body C Tctx R fuel <=>
    !root cert p a route snap rest frame path sb tb completed_fuel result.
      R root cert /\
      inline_live_stack C cert root ((p,a,route,snap)::rest) frame /\
      inline_frontier_stack ((p,a,route,snap)::rest) frame /\
      inline_namespace_leaf_at cert p route.ir_rename a.ia_function /\
      inline_routed_leaf cert root p a.ia_function path /\
      route.ir_rename = inline_path_rename path /\
      ~snap.ils_state.vs_halted /\ ~frame.ipf_state.vs_halted /\
      lookup_block snap.ils_state.vs_current_bb a.ia_function.fn_blocks = SOME sb /\
      lookup_block frame.ipf_state.vs_current_bb root.fn_blocks = SOME tb /\
      inline_parameter_boundary_path path a.ia_function
        snap.ils_state.vs_current_bb snap.ils_state.vs_inst_idx root
        frame.ipf_state.vs_current_bb frame.ipf_state.vs_inst_idx /\
      phi_prefix_length sb.bb_instructions <= snap.ils_state.vs_inst_idx /\
      no_param_insts (DROP snap.ils_state.vs_inst_idx sb.bb_instructions) /\
      run_blocks completed_fuel C a.ia_function a.ia_entry = result /\
      inline_resume C a.ia_function fuel (InlineBody sb snap.ils_state) = result /\
      (!err. result <> Error err) /\ (!u. result <> OK u) ==>
      inline_activation_outcome C Tctx cert root p a route rest frame
        (InlineBody tb frame.ipf_state) result
End

Theorem inline_zero_frame_boundary[local]:
  inline_cell_frame tag c d /\
  (!e k. tag = EnterCell e k ==> k = 0) ==>
  inline_parameter_boundary (inline_cell_choice tag)
    c.ic_function c.ic_block c.ic_index d.ic_function d.ic_block d.ic_index
Proof
  strip_tac >>
  `inline_cell_at d` by metis_tac[functionInlinerReachableCutsTheory.inline_cell_frame_sound] >>
  Cases_on `tag` >>
  gvs[functionInlinerReachableCutsTheory.inline_cell_frame_def,
      functionInlinerReachableCutsTheory.inline_cell_choice_def,
      inline_parameter_boundary_def,
      functionInlinerReachableCutsTheory.inline_cell_at_def,
      inline_fetched_fields_def,
      functionInlinerReachableCutsTheory.inline_make_cell_def,
      inline_keep_boundary_def, venomInstTheory.get_instruction_def] >>
  metis_tac[LESS_IMP_LESS_OR_EQ]
QED

Theorem inline_jump_keep_produce[local]:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\ c.ic_function = e.ise_caller /\
  inline_cell_at c /\ FST c.ic_fields = JMP ==>
  ?d. inline_cell_frame (KeepCell e) c d /\
    d.ic_function = e.ise_final /\ inline_cell_at d /\ FST d.ic_fields = JMP
Proof
  strip_tac >> drule_all functionInlinerOccurrencesTheory.inline_annotated_edit_fetch_facts >> strip_tac >>
  `ALL_DISTINCT (fn_labels e.ise_caller)` by
    metis_tac[functionInlinerOccurrencesTheory.inline_annotated_origin_labels] >>
  `?source. lookup_block e.ise_block e.ise_caller.fn_blocks = SOME source /\
    e.ise_index < LENGTH source.bb_instructions /\
    (EL e.ise_index source.bb_instructions).inst_opcode = INVOKE` by
    metis_tac[inline_site_edit_valid_def,
      functionInlinerWfTheory.find_invoke_site_lookup] >>
  `c.ic_block <> e.ise_block \/ c.ic_index <> e.ise_index` by
    (gvs[functionInlinerReachableCutsTheory.inline_cell_at_def,
      inline_fetched_fields_def,
      venomInstTheory.get_instruction_def, inline_inst_fields_def] >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `(_,_,_) = c.ic_fields` (assume_tac o SYM) >> fs[]) >>
  `?d. inline_cell_frame (KeepCell e) c d` by
    metis_tac[functionInlinerReachableCutsTheory.inline_keep_cell_produce] >>
  qexists `d` >> simp[] >>
  `inline_cell_at d` by metis_tac[functionInlinerReachableCutsTheory.inline_cell_frame_sound] >> simp[] >>
  qpat_x_assum `inline_cell_frame _ _ _` mp_tac >>
  simp[functionInlinerReachableCutsTheory.inline_cell_frame_def] >> rpt strip_tac >>
  gvs[functionInlinerReachableCutsTheory.inline_make_cell_def,
    inline_inst_fields_def,
    inline_edit_repair_def]
QED

Theorem inline_jump_enter_produce[local]:
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_caller a /\
  inline_annotated_origin ctx e.ise_state.is_inline_count e.ise_callee b /\
  inline_site_edit_valid e /\ c.ic_function = e.ise_callee /\
  inline_cell_at c /\ FST c.ic_fields = JMP ==>
  ?d. inline_cell_frame (EnterCell e 0) c d /\
    d.ic_function = e.ise_final /\ inline_cell_at d /\ FST d.ic_fields = JMP
Proof
  strip_tac >> drule_all functionInlinerOccurrencesTheory.inline_annotated_edit_fetch_facts >> strip_tac >>
  `?cb inst. lookup_block c.ic_block e.ise_callee.fn_blocks = SOME cb /\
    get_instruction cb c.ic_index = SOME inst /\
    c.ic_fields = inline_inst_fields inst` by
    metis_tac[functionInlinerReachableCutsTheory.inline_cell_at_def, inline_fetched_fields_def] >>
  `inst.inst_opcode = JMP` by gvs[inline_inst_fields_def] >>
  `MEM c.ic_block (fn_labels e.ise_callee)` by
    (simp[venomInstTheory.fn_labels_def, MEM_MAP] >>
     metis_tac[venomExecPropsTheory.lookup_block_MEM,
               venomExecPropsTheory.lookup_block_label]) >>
  `inline_cell_focus e bb cb c.ic_index =
    ([clone_instruction e.ise_prefix (fn_labels e.ise_callee) inst],
     SND (inline_cell_prefix e bb cb c.ic_index))` by
    gvs[functionInlinerReachableCutsTheory.inline_cell_focus_def,
        venomInstTheory.get_instruction_def, functionInlinerDefsTheory.clone_instruction_def,
        functionInlinerDefsTheory.rewrite_inline_inst_def, is_param_opcode_def] >>
  `?d. inline_cell_frame (EnterCell e 0) c d` by
    (irule functionInlinerReachableCutsTheory.inline_enter_cell_produce >> simp[] >> metis_tac[]) >>
  qexists `d` >> simp[] >>
  `inline_cell_at d` by metis_tac[functionInlinerReachableCutsTheory.inline_cell_frame_sound] >> simp[] >>
  qpat_x_assum `inline_cell_frame _ _ _` mp_tac >>
  simp[functionInlinerReachableCutsTheory.inline_cell_frame_def] >> rpt strip_tac >>
  gvs[functionInlinerReachableCutsTheory.inline_make_cell_def,
      inline_inst_fields_def, inline_edit_repair_def, functionInlinerDefsTheory.clone_instruction_def] >> metis_tac[]
QED

Theorem inline_jump_path_produce[local]:
  !path c root.
  inline_annotated_choice_path ctx path c.ic_function root /\
  inline_cell_at c /\ FST c.ic_fields = JMP ==>
  ?frames d. inline_cell_zipper c frames d /\
    MAP (\(tag,next). inline_cell_choice tag) frames = path /\
    EVERY (\(tag,next). !edit. tag <> SelectedJump edit) frames /\
    d.ic_function = root /\ inline_cell_at d /\ FST d.ic_fields = JMP /\
    inline_parameter_boundary_path path c.ic_function c.ic_block c.ic_index
      root d.ic_block d.ic_index
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (qexistsl_tac [`[]`,`c`] >>
      gvs[functionInlinerParameterPropagationTheory.inline_annotated_choice_path_def,
          functionInlinerReachableCutsTheory.inline_cell_zipper_def,
          inline_parameter_boundary_path_def]) >>
  qpat_x_assum `inline_annotated_choice_path _ _ _ _` mp_tac >>
  simp[functionInlinerParameterPropagationTheory.inline_annotated_choice_path_def] >> strip_tac >> gvs[]
  >- (drule_all inline_jump_keep_produce >> strip_tac >>
      `inline_parameter_boundary (InlineKeep e) c.ic_function c.ic_block c.ic_index
         d.ic_function d.ic_block d.ic_index` by
        (drule inline_zero_frame_boundary >>
         simp[functionInlinerReachableCutsTheory.inline_cell_choice_def]) >>
      first_x_assum (qspec_then `d` mp_tac) >> simp[] >>
      disch_then (qspec_then `root` mp_tac) >> simp[] >> strip_tac >>
      qexistsl_tac [`(KeepCell e,d)::frames`,`d'`] >>
      simp[functionInlinerReachableCutsTheory.inline_cell_zipper_def,
           functionInlinerReachableCutsTheory.inline_cell_choice_def,
           inline_parameter_boundary_path_def] >>
      metis_tac[inline_zero_frame_boundary,
        functionInlinerReachableCutsTheory.inline_cell_choice_def]) >>
  drule_all inline_jump_enter_produce >> strip_tac >>
  `inline_parameter_boundary (InlineEnter e) c.ic_function c.ic_block c.ic_index
     d.ic_function d.ic_block d.ic_index` by
    (drule inline_zero_frame_boundary >>
     simp[functionInlinerReachableCutsTheory.inline_cell_choice_def]) >>
  first_x_assum (qspec_then `d` mp_tac) >> simp[] >>
  disch_then (qspec_then `root` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`(EnterCell e 0,d)::frames`,`d'`] >>
  simp[functionInlinerReachableCutsTheory.inline_cell_zipper_def,
       functionInlinerReachableCutsTheory.inline_cell_choice_def,
       inline_parameter_boundary_path_def] >>
  metis_tac[inline_zero_frame_boundary,
    functionInlinerReachableCutsTheory.inline_cell_choice_def]
QED

Theorem inline_selected_jump_boundary:
  inline_annotated_origin C n root cert /\
  inline_call_incidence cert root p fn l j orig (InlineSelected u q e zipper) /\
  inline_routed_leaf cert root p fn path /\
  inline_parameter_boundary_path path fn l j root tl tj ==>
  ?c mid frames d. inline_cell_frame (SelectedJump e) c mid /\
    inline_cell_zipper mid frames d /\
    MAP (\(tag,next). inline_cell_choice tag) frames = zipper /\
    EVERY (\(tag,next). !edit. tag <> SelectedJump edit) frames /\
    d.ic_function = root /\ d.ic_block = tl /\ d.ic_index = tj
Proof
  strip_tac >>
  drule functionInlinerPairedSelectionTheory.inline_selected_paired_separation >> simp[] >>
  disch_then drule >> strip_tac >>
  `inline_fetched_fields e.ise_caller e.ise_block e.ise_index
     (inline_inst_fields current)` by
    (drule inline_call_incidence_residual_fetch >>
     disch_then (qspecl_then [`C`,`e.ise_state.is_inline_count`,`src`,`current`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  qmatch_asmsub_abbrev_tac `inline_fetched_fields _ _ _ fields` >>
  qabbrev_tac `c = inline_make_cell e.ise_caller e.ise_block e.ise_index fields` >>
  `inline_cell_at c /\ c.ic_function = e.ise_caller /\
   c.ic_block = e.ise_block /\ c.ic_index = e.ise_index` by
    simp[Abbr `c`, functionInlinerReachableCutsTheory.inline_cell_at_def,
      functionInlinerReachableCutsTheory.inline_make_cell_def] >>
  `~MEM e.ise_return (fn_labels e.ise_caller)` by
    metis_tac[functionInlinerOccurrencesTheory.inline_annotated_edit_fetch_facts] >>
  `?mid. inline_cell_frame (SelectedJump e) c mid` by
    metis_tac[functionInlinerReachableCutsTheory.inline_selected_cell_produce] >>
  `mid.ic_function = e.ise_final /\ inline_cell_at mid /\ FST mid.ic_fields = JMP` by
    (conj_tac
     >- gvs[functionInlinerReachableCutsTheory.inline_cell_frame_def,
            functionInlinerReachableCutsTheory.inline_make_cell_def] >>
     conj_tac >- metis_tac[functionInlinerReachableCutsTheory.inline_cell_frame_sound] >>
     gvs[functionInlinerReachableCutsTheory.inline_cell_frame_def,
         functionInlinerReachableCutsTheory.inline_make_cell_def]) >>
  `inline_annotated_choice_path C zipper e.ise_final root` by
    metis_tac[functionInlinerSelectedParameterDescriptorsTheory.inline_selected_annotated_choice_path] >>
  mp_tac (Q.SPECL [`zipper`,`mid`,`root`] (Q.INST [`ctx` |-> `C`] inline_jump_path_produce)) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`c`,`mid`,`frames`,`d`] >> simp[] >>
  drule inline_residual_current_path >>
  disch_then (qspecl_then [`C`,`e.ise_state.is_inline_count`,`src`,`current`,
    `e.ise_index`] mp_tac) >> simp[] >> strip_tac >>
  `MAP inline_choice_key path' = MAP inline_choice_key path''` by
    metis_tac[functionInlinerRouteKeysTheory.inline_routed_leaf_key_unique] >>
  `inline_parameter_boundary_path path' fn l j e.ise_caller e.ise_block e.ise_index` by
    metis_tac[functionInlinerSelectedContinuationTheory.inline_parameter_boundary_path_keys] >>
  `inline_parameter_boundary (InlineKeep e) e.ise_caller e.ise_block e.ise_index
     e.ise_final mid.ic_block mid.ic_index` by
    (drule inline_zero_frame_boundary >>
     simp[functionInlinerReachableCutsTheory.inline_cell_choice_def]) >>
  `inline_parameter_boundary_path (path' ++ [InlineKeep e] ++ zipper)
     fn l j root d.ic_block d.ic_index` by
    (irule inline_parameter_boundary_path_append >> goal_assum (drule_at Any) >>
     irule inline_parameter_boundary_path_append >> goal_assum (drule_at Any) >>
     simp[inline_parameter_boundary_path_def] >> metis_tac[]) >>
  `MAP inline_choice_key path =
     MAP inline_choice_key (path' ++ [InlineKeep e] ++ zipper)` by
    metis_tac[functionInlinerRouteKeysTheory.inline_routed_leaf_key_unique] >>
  `inline_parameter_boundary_path path fn l j root d.ic_block d.ic_index` by
    metis_tac[functionInlinerSelectedContinuationTheory.inline_parameter_boundary_path_keys] >>
  metis_tac[inline_parameter_boundary_path_functional]
QED

Theorem inline_live_stack_index:
  inline_live_stack C cert root ((p,a,route,snap)::rest) frame ==>
  inline_live_stack C cert root
    ((p,a,route,snap with ils_state := snap.ils_state with vs_inst_idx := si)::rest)
    (frame with ipf_state := frame.ipf_state with vs_inst_idx := ti)
Proof
  strip_tac >>
  `inline_owner_storage cert ((p,a,route,snap)::rest) frame /\
   inline_parameter_saved_reads ((p,a,route,snap)::rest)` by
    metis_tac[inline_live_stack_def] >>
  drule_all inline_parameter_sequential_control >>
  disch_then (qspecl_then [`ti`,`si`] strip_assume_tac) >>
  fs[inline_live_stack_def, inline_parameter_owners_cons,
     inline_shared_frame_def, stateFrameTheory.execution_frame_def,
     inline_caller_residual_updates]
QED

Theorem inline_recursive_transport:
  inliner_input_ok C /\ inline_transport_family C Tctx R ==>
  !fuel. inline_transport_initial C Tctx R fuel /\
         inline_transport_entry C Tctx R fuel /\
         inline_transport_body C Tctx R fuel
Proof
  strip_tac >> completeInduct_on `fuel` >>
  conj_asm1_tac >- suspend "initial" >>
  conj_asm1_tac >- suspend "entry" >>
  suspend "body"
QED

Resume inline_recursive_transport[entry]:
  rewrite_tac[inline_transport_entry_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel`
  >- (qpat_x_assum `inline_resume _ _ _ _ = _` mp_tac >>
      simp[inline_resume_def, Once run_blocks_def] >> metis_tac[]) >>
  `inline_transport_body C Tctx R n` by simp[] >>
  `?k. inline_annotated_origin C k root cert` by
    metis_tac[inline_transport_family_def] >>
  mp_tac (Q.SPECL [`snap.ils_state`,`sb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  strip_tac
  >- (rename1 `eval_phis snap.ils_state sb.bb_instructions = OK post` >>
      drule_all inline_live_phi_body_boundary >> strip_tac >>
      `MEM a.ia_function C.ctx_functions` by
        metis_tac[functionInlinerReachableCutsTheory.inline_routed_leaf_source_member] >>
      `canonical_param_prefix a.ia_function` by
        (gvs[functionInlinerContractTheory.inliner_input_ok_def, listTheory.EVERY_MEM] >>
         metis_tac[]) >>
      `no_param_insts sb.bb_instructions` by
        (qpat_x_assum `canonical_param_prefix _` mp_tac >>
         Cases_on `a.ia_function.fn_blocks` >>
         simp[callLayoutDefsTheory.canonical_param_prefix_def] >> strip_tac >>
         `MEM sb t` by
           (qpat_assum `lookup_block snap.ils_state.vs_current_bb _ = _`
              (mp_tac o MATCH_MP venomExecPropsTheory.lookup_block_MEM) >>
            strip_tac >> gvs[] >>
            metis_tac[venomExecPropsTheory.lookup_block_label]) >>
         gvs[listTheory.EVERY_MEM]) >>
      `inline_resume C a.ia_function n
         (InlineBody sb (post with vs_inst_idx := phi_prefix_length sb.bb_instructions)) = result` by
        (qpat_x_assum `inline_resume C a.ia_function (SUC n) _ = _` mp_tac >>
         simp[inline_resume_def, Once run_blocks_def]) >>
      fs[LET_THM] >>
      `post.vs_current_bb = snap.ils_state.vs_current_bb /\
       v.vs_current_bb = frame.ipf_state.vs_current_bb` by
        metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
      `post.vs_alloca_next = snap.ils_state.vs_alloca_next /\
       v.vs_alloca_next = frame.ipf_state.vs_alloca_next` by
        metis_tac[inline_frontier_phis] >>
      `inline_frontier_stack
         ((p,a,route,snap with
           <|ils_state := post with vs_inst_idx := phi_prefix_length sb.bb_instructions;
             ils_defined := inline_phi_outputs sb.bb_instructions UNION snap.ils_defined|>)::rest)
         (frame with ipf_state := v with vs_inst_idx := phi_prefix_length tb.bb_instructions)` by
        gvs[inline_frontier_stack_def] >>
      `inline_activation_outcome C Tctx cert root p a route rest
         (frame with ipf_state := v with vs_inst_idx := phi_prefix_length tb.bb_instructions)
         (InlineBody tb (v with vs_inst_idx := phi_prefix_length tb.bb_instructions)) result` by
        (qpat_assum `inline_transport_body C Tctx R n`
           (assume_tac o REWRITE_RULE[inline_transport_body_def]) >>
         qpat_assum `inline_live_stack _ _ _ _ (frame with ipf_state := _)`
           (fn live => first_x_assum (fn ih => mp_then (Pat `inline_live_stack _ _ _ _ _`) mp_tac ih live)) >>
         simp[] >> disch_then (qspecl_then [`path`,`completed_fuel`] mp_tac) >>
         fs[callLayoutDefsTheory.no_param_insts_def] >>
         metis_tac[rich_listTheory.EVERY_DROP]) >>
      irule inline_activation_entry_body >> goal_assum (drule_at Any) >>
      simp[] >>
      Cases_on `result` >>
      gvs[inline_activation_outcome_def, inline_return_frontier_def] >> metis_tac[]) >>
  qpat_x_assum `inline_resume _ _ _ _ = _` mp_tac >>
  simp[inline_resume_def, Once run_blocks_def] >> metis_tac[]
QED

Resume inline_recursive_transport[body]:
  rewrite_tac[inline_transport_body_def] >> rpt gen_tac >>
  map_every qid_spec_tac [`frame`,`tb`] >>
  completeInduct_on `LENGTH sb.bb_instructions - snap.ils_state.vs_inst_idx` >>
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction sb snap.ils_state.vs_inst_idx`
  >- (qpat_x_assum `inline_resume _ _ _ _ = _` mp_tac >>
      simp[inline_resume_def, Once exec_block_def] >> metis_tac[]) >>
  rename1 `get_instruction sb snap.ils_state.vs_inst_idx = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (`terminates (step_inst fuel C inst snap.ils_state)` by
        (Cases_on `step_inst fuel C inst snap.ils_state` >> simp[passSimulationDefsTheory.terminates_def] >>
         qpat_x_assum `inline_resume _ _ _ _ = _` mp_tac >>
         simp[inline_resume_def, Once exec_block_def] >> metis_tac[]) >>
      `?child cr. inline_original_child C fuel a.ia_id 0 inst snap.ils_state
         (step_inst fuel C inst snap.ils_state) child cr` by
        (irule functionInlinerActivationTheory.inline_original_child_exists >> simp[]) >>
      `?n. inline_annotated_origin C n root cert` by
        metis_tac[inline_transport_family_def] >>
      `?outcome. inline_call_incidence cert root p a.ia_function
        snap.ils_state.vs_current_bb snap.ils_state.vs_inst_idx inst outcome` by
        (drule functionInlinerOccurrencesTheory.inline_call_incidence_total >>
         metis_tac[]) >>
      Cases_on `outcome`
      >- (rename1 `inline_call_incidence _ _ _ _ _ _ _ (InlineResidual loc dst)` >>
          qpat_assum `inline_original_child _ _ _ _ _ _ _ _ _` mp_tac >>
          rewrite_tac[functionInlinerActivationTheory.inline_original_child_def] >>
          strip_tac >>
          `?target cert'. lookup_function nm Tctx.ctx_functions = SOME target /\
             inline_entry_function cert' = child.ia_function /\ R target cert'` by
            (qpat_assum `inline_transport_family _ _ _`
               (strip_assume_tac o REWRITE_RULE[inline_transport_family_def]) >>
             first_x_assum drule_all >> simp[]) >>
          `snap.ils_state.vs_labels = FEMPTY` by
            (drule functionInlinerLiveInvariantTheory.inline_live_stack_storage >>
             strip_tac >>
             drule functionInlinerOperationalCutsTheory.inline_owner_storage_head >>
             simp[functionInlinerCutsTheory.inline_tracked_snapshot_def]) >>
          `child.ia_function.fn_blocks <> [] /\ child.ia_entry.vs_labels = FEMPTY /\
             ~child.ia_entry.vs_halted /\ child.ia_entry.vs_inst_idx = 0 /\
             child.ia_entry.vs_current_bb = (HD child.ia_function.fn_blocks).bb_label` by
            (qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
             Cases_on `child.ia_function.fn_blocks` >>
             simp[setup_callee_def] >>
             disch_then (fn th => simp[GSYM th])) >>
          `inline_physical_outcome Tctx target (InlineEntry child.ia_entry) cr` by
            (qpat_assum `inline_transport_initial _ _ _ fuel`
               (mp_tac o REWRITE_RULE[inline_transport_initial_def]) >>
             disch_then irule >>
             simp[] >> conj_tac
             >- (Cases_on `cr` >> gvs[passSimulationDefsTheory.terminates_def]) >>
             conj_tac >- metis_tac[o1PassLiftTheory.run_blocks_not_OK] >>
             qexists `cert'` >> simp[]) >>
          `?k. loc.il_phase = InlineAtInstruction k /\
             inline_fetched_fields root loc.il_block k (inline_inst_fields dst)` by
            (drule inline_call_incidence_residual_fetch >>
             disch_then (qspecl_then [`C`,`n`,`loc`,`dst`] mp_tac) >> simp[]) >>
          `?rpath. inline_routed_leaf cert root p a.ia_function rpath /\
             inline_parameter_boundary_path rpath a.ia_function
               snap.ils_state.vs_current_bb snap.ils_state.vs_inst_idx root loc.il_block k` by
            (drule inline_residual_current_path >>
             disch_then (qspecl_then [`C`,`n`,`loc`,`dst`,`k`] mp_tac) >> simp[]) >>
          `MAP inline_choice_key path = MAP inline_choice_key rpath` by
            metis_tac[inline_routed_leaf_key_unique] >>
          `inline_parameter_boundary_path path a.ia_function
             snap.ils_state.vs_current_bb snap.ils_state.vs_inst_idx root loc.il_block k` by
            metis_tac[inline_parameter_boundary_path_keys] >>
          `loc.il_block = frame.ipf_state.vs_current_bb /\
             k = frame.ipf_state.vs_inst_idx` by
            metis_tac[inline_parameter_boundary_path_functional] >>
          `?tinst. get_instruction tb frame.ipf_state.vs_inst_idx = SOME tinst /\
             inline_inst_fields tinst = inline_inst_fields dst` by
            (gvs[inline_fetched_fields_def] >> metis_tac[]) >>
          `decode_invoke dst = SOME
             (nm,MAP (inline_rename_operand route.ir_rename I) ops) /\
             dst.inst_outputs = MAP route.ir_rename inst.inst_outputs` by
            (metis_tac[inline_residual_arguments]) >>
          `decode_invoke tinst = SOME
             (nm,MAP (inline_rename_operand route.ir_rename I) ops) /\
             tinst.inst_outputs = MAP route.ir_rename inst.inst_outputs /\
             tinst.inst_opcode = INVOKE` by
            (drule inline_call_incidence_residual_phase >> simp[] >>
             gvs[inline_inst_fields_def, decode_invoke_def]) >>
          `MEM a.ia_function C.ctx_functions` by
            metis_tac[functionInlinerReachableCutsTheory.inline_routed_leaf_source_member] >>
          `MEM inst (fn_insts a.ia_function)` by
            (imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
             gvs[venomInstTheory.get_instruction_def] >>
             metis_tac[venomInstTheory.fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff, listTheory.EL_MEM]) >>
          `inline_opacity_ok a.ia_function {v | retpc_var a.ia_function v}` by
            metis_tac[functionInlinerOpacityTheory.inliner_input_opacity] >>
          `EVERY (\op. !v. op = Var v ==>
             MEM v (cfgTransform$fn_all_vars a.ia_function) /\
             ~retpc_var a.ia_function v) ops` by
            (rewrite_tac[listTheory.EVERY_MEM] >> qx_gen_tac `op` >> disch_tac >>
             BETA_TAC >> qx_gen_tac `x` >> disch_then SUBST_ALL_TAC >>
             `MEM (Var x) inst.inst_operands` by
               (gvs[decode_invoke_def, AllCaseEqs()]) >>
             conj_tac
             >- (mp_tac (Q.INST [`fn` |-> `a.ia_function`,
                   `P` |-> `\v. MEM v (cfgTransform$fn_all_vars a.ia_function)`]
                   functionInlinerNamespaceTheory.inline_fn_vars_in) >>
                 simp[functionInlinerNamespaceTheory.inline_inst_vars_in_def, listTheory.EVERY_MEM] >>
                 disch_then (qspec_then `inst` mp_tac) >> simp[] >>
                 strip_tac >> first_x_assum (qspec_then `Var x` mp_tac) >> simp[]) >>
             drule_all functionInlinerOpacityTheory.inline_opacity_invoke_operand >> simp[]) >>
          `inline_tracked_snapshot a.ia_function a route snap frame` by
            (drule functionInlinerLiveInvariantTheory.inline_live_stack_storage >>
             strip_tac >> drule functionInlinerOperationalCutsTheory.inline_owner_storage_head >> simp[]) >>
          `eval_operands (MAP (inline_rename_operand route.ir_rename I) ops)
             frame.ipf_state = SOME edge.ipe_args` by
            (irule functionInlinerOperationalCutsTheory.inline_tracked_operands_success >>
             goal_assum (drule_at Any) >> simp[]) >>
          `target.fn_blocks <> [] /\
             (HD target.fn_blocks).bb_label = (HD child.ia_function.fn_blocks).bb_label` by
            (`?m. inline_annotated_origin C m target cert'` by
               metis_tac[inline_transport_family_def] >>
             drule inline_annotated_entry_first_label >> simp[]) >>
          `inline_shared_frame snap.ils_state = inline_shared_frame frame.ipf_state` by
            metis_tac[functionInlinerLiveInvariantTheory.inline_live_stack_head_shared] >>
          `snap.ils_state.vs_alloca_next = frame.ipf_state.vs_alloca_next` by
            metis_tac[inline_frontier_stack_head] >>
          `setup_callee child.ia_function edge.ipe_args snap.ils_state =
             setup_callee target edge.ipe_args frame.ipf_state` by
            (irule inline_frontier_setup_compare >> simp[]) >>
          `setup_callee target edge.ipe_args frame.ipf_state = SOME child.ia_entry` by
            metis_tac[] >>
          Cases_on `cr` >> gvs[passSimulationDefsTheory.terminates_def, inline_physical_outcome_def]
          >- (rename1 `inline_terminal Tctx target b (InlineEntry child.ia_entry) (Halt tv)` >>
              rename1 `inline_original_call_result _ _ (Halt sv) _` >>
              gvs[inline_terminal_def, inline_resume_def] >>
              `step_inst b Tctx tinst frame.ipf_state = Halt tv` by
                simp[Once step_inst_def] >>
              `exec_block b Tctx tb frame.ipf_state = Halt tv` by
                simp[Once exec_block_def] >>
              `run_blocks completed_fuel C a.ia_function a.ia_entry = Halt sv` by
                (gvs[functionInlinerActivationTheory.inline_original_call_result_def] >>
                 qpat_x_assum `_ = run_blocks completed_fuel C a.ia_function a.ia_entry` mp_tac >>
                 simp[Once exec_block_def]) >>
              gvs[] >> irule inline_activation_halt_here >> metis_tac[])
          >- (rename1 `inline_terminal Tctx target b (InlineEntry child.ia_entry) (Abort reason tv)` >>
              rename1 `inline_original_call_result _ _ (Abort reason sv) _` >>
              gvs[inline_terminal_def, inline_resume_def] >>
              `step_inst b Tctx tinst frame.ipf_state = Abort reason tv` by
                simp[Once step_inst_def] >>
              `exec_block b Tctx tb frame.ipf_state = Abort reason tv` by
                simp[Once exec_block_def] >>
              `run_blocks completed_fuel C a.ia_function a.ia_entry = Abort reason sv` by
                (gvs[functionInlinerActivationTheory.inline_original_call_result_def] >>
                 qpat_x_assum `_ = run_blocks completed_fuel C a.ia_function a.ia_entry` mp_tac >>
                 simp[Once exec_block_def]) >>
              gvs[] >> irule inline_activation_abort_here >> metis_tac[]) >>
          rename1 `inline_terminal Tctx target b (InlineEntry child.ia_entry) (IntRet ir tv)` >>
          rename1 `inline_original_call_result _ _ (IntRet ir sv) _` >>
          gvs[functionInlinerActivationTheory.inline_original_call_result_def] >>
          rename1 `bind_outputs edge.ipe_call.inst_outputs ir.iret_values
            (adopt_return_fmp ir (merge_callee_state snap.ils_state sv)) = SOME su` >>
          gvs[inline_terminal_def, inline_resume_def] >>
          `inline_fmp_ctx_ok C` by metis_tac[inline_input_fmp_ctx] >>
          `inline_fmp_result snap.ils_state.vs_fmp (IntRet ir sv)` by
            (drule_all inline_callee_fmp_result >>
             disch_then (qspec_then `fuel` mp_tac) >> simp[]) >>
          `inline_caller_residual sv = inline_caller_residual child.ia_entry` by
            metis_tac[inline_caller_residual_run_blocks_return] >>
          `inline_caller_residual child.ia_entry = inline_caller_residual snap.ils_state` by
            (qpat_x_assum `setup_callee child.ia_function _ _ = _` mp_tac >>
             simp[setup_callee_def, AllCaseEqs()] >> strip_tac >>
             gvs[inline_caller_residual_def, inline_shared_frame_def,
               stateFrameTheory.execution_frame_def, merge_callee_state_def,
               venom_state_component_equality]) >>
          `EVERY (\x. MEM x (cfgTransform$fn_all_vars a.ia_function) /\
             ~retpc_var a.ia_function x) edge.ipe_call.inst_outputs` by
            metis_tac[inline_call_output_namespace] >>
          `INJ route.ir_rename (set edge.ipe_call.inst_outputs UNION snap.ils_defined) UNIV` by
            (irule pred_setTheory.INJ_SUBSET >> qexists `UNIV` >> simp[] >>
             metis_tac[inline_namespace_leaf_at_def, inline_namespace_node_injective]) >>
          `inline_caller_residual sv = inline_caller_residual snap.ils_state` by metis_tac[] >>
          drule_all inline_live_residual_return >> strip_tac >>
          `!h. b <= h ==> step_inst h Tctx tinst frame.ipf_state = OK tu` by
            (rpt strip_tac >> simp[Once step_inst_def] >> gvs[]) >>
          `inline_segment Tctx root b 0 (InlineBody tb frame.ipf_state)
             (InlineBody tb (tu with vs_inst_idx := SUC frame.ipf_state.vs_inst_idx))` by
            (irule inline_segment_body_step >> simp[venomInstTheory.is_terminator_def]) >>
          `?spath. inline_routed_leaf cert root p a.ia_function spath /\
             inline_parameter_boundary_path spath a.ia_function
               snap.ils_state.vs_current_bb (SUC snap.ils_state.vs_inst_idx)
               root frame.ipf_state.vs_current_bb (SUC frame.ipf_state.vs_inst_idx)` by
            (drule inline_residual_invoke_successor_path >>
             disch_then (qspecl_then [`C`,`n`,`loc`,`dst`,`frame.ipf_state.vs_inst_idx`] mp_tac) >>
             simp[]) >>
          `inline_parameter_boundary_path path a.ia_function
             snap.ils_state.vs_current_bb (SUC snap.ils_state.vs_inst_idx)
             root frame.ipf_state.vs_current_bb (SUC frame.ipf_state.vs_inst_idx)` by
            metis_tac[inline_routed_leaf_key_unique, inline_parameter_boundary_path_keys] >>
          qabbrev_tac `nextsnap = snap with <|ils_state := su with vs_inst_idx := SUC snap.ils_state.vs_inst_idx;
             ils_defined := set edge.ipe_call.inst_outputs UNION snap.ils_defined|>` >>
          qabbrev_tac `nextframe = frame with ipf_state := tu with vs_inst_idx := SUC frame.ipf_state.vs_inst_idx` >>
          `inline_live_stack C cert root ((p,a,route,nextsnap)::rest) nextframe` by
            (simp[Abbr `nextsnap`, Abbr `nextframe`] >>
             qpat_assum `inline_live_stack _ _ _ _ (frame with ipf_state := tu)`
               (mp_tac o MATCH_MP (Q.INST
                 [`si` |-> `SUC snap.ils_state.vs_inst_idx`,
                  `ti` |-> `SUC frame.ipf_state.vs_inst_idx`] inline_live_stack_index)) >> simp[]) >>
          `inline_frontier_stack ((p,a,route,nextsnap)::rest) nextframe` by
            (fs[inline_frontier_stack_def, Abbr `nextsnap`, Abbr `nextframe`]) >>
          `snap.ils_state.vs_inst_idx < LENGTH sb.bb_instructions` by
            (gvs[get_instruction_def, AllCaseEqs()] >> decide_tac) >>
          qpat_x_assum `!m. m < LENGTH sb.bb_instructions - snap.ils_state.vs_inst_idx ==> _`
            (qspec_then `LENGTH sb.bb_instructions - SUC snap.ils_state.vs_inst_idx` mp_tac) >>
          simp[] >> disch_then (qspecl_then [`sb`,`nextsnap`] mp_tac) >>
          simp[Abbr `nextsnap`] >>
          disch_then (qspecl_then [`tb`,`nextframe`] mp_tac) >>
          impl_tac
          >- (fs[Abbr `nextframe`] >>
              conj_tac
              >- (fs[callLayoutDefsTheory.no_param_insts_def] >>
                  qpat_assum `EVERY _ (DROP snap.ils_state.vs_inst_idx _)`
                    (mp_tac o MATCH_MP rich_listTheory.EVERY_DROP) >>
                  disch_then (qspec_then `1` mp_tac) >>
                  simp[rich_listTheory.DROP_DROP_T, arithmeticTheory.ADD1]) >>
              qpat_x_assum `_ = run_blocks completed_fuel C a.ia_function a.ia_entry` mp_tac >>
              simp[Once exec_block_def, venomInstTheory.is_terminator_def]) >>
          disch_tac >>
          `inline_activation_outcome C Tctx cert root p a route rest frame
             (InlineBody tb (tu with vs_inst_idx := SUC frame.ipf_state.vs_inst_idx))
             (run_blocks completed_fuel C a.ia_function a.ia_entry)` by
            (qpat_x_assum `inline_activation_outcome _ _ _ _ _ _ _ _ nextframe _ _` mp_tac >>
             simp[Abbr `nextframe`, inline_activation_outcome_def, inline_return_frontier_def]) >>
          drule_all inline_activation_outcome_segment >> simp[]) >>
      rename1 `inline_call_incidence _ _ _ _ _ _ _ (InlineSelected u q e zipper)` >>
      drule functionInlinerParameterNestingTheory.inline_selected_entry_route_pair >>
      disch_then (qspecl_then [`C`,`n`,`u`,`q`,`e`,`zipper`] mp_tac) >>
      simp[] >> strip_tac >>
      `child' = child.ia_function` by
        (drule_all functionInlinerReturnRoutingTheory.inline_selected_return_call_target >>
         strip_tac >>
         qpat_assum `inline_original_child _ _ _ _ _ _ _ _ _` mp_tac >>
         pure_rewrite_tac[functionInlinerActivationTheory.inline_original_child_def] >>
         strip_tac >>
         gvs[venomExecSemanticsTheory.decode_invoke_def] >>
         `MEM child' C.ctx_functions` by
           metis_tac[functionInlinerReachableCutsTheory.inline_routed_leaf_source_member] >>
         `ALL_DISTINCT (MAP (\f. f.fn_name) C.ctx_functions)` by
           fs[functionInlinerContractTheory.inliner_input_ok_def,
             venomWfTheory.ctx_wf_def, venomWfTheory.ctx_distinct_fn_names_def,
             venomInstTheory.ctx_fn_names_def] >>
         `lookup_function child'.fn_name C.ctx_functions = SOME child'` by
           (irule intCallLookupTheory.lookup_function_distinct_mem >> simp[]) >>
         gvs[]) >>
      drule_all inline_selected_jump_boundary >> strip_tac >>
      `canonical_param_prefix child.ia_function` by
        (`MEM child.ia_function C.ctx_functions` by
           metis_tac[functionInlinerReachableCutsTheory.inline_routed_leaf_source_member] >>
         gvs[functionInlinerContractTheory.inliner_input_ok_def, EVERY_MEM] >> metis_tac[]) >>
      `?eb blocks. (clone_function e.ise_prefix e.ise_callee).fn_blocks = eb::blocks` by
        (drule functionInlinerPairedSelectionTheory.inline_selected_paired_separation >> simp[] >>
         disch_then drule >> strip_tac >>
         drule functionInlinerOccurrencesTheory.inline_annotated_entry_route >> strip_tac >>
         qpat_x_assum `!prefix. inline_routed_leaf _ _ _ _ _ ==> _` drule >> strip_tac >>
         `child.ia_function = inline_entry_function b` by
           (drule functionInlinerRoutedProvenanceTheory.inline_routed_leaf_namespace >>
            strip_tac >>
            gvs[functionInlinerEnvelopesTheory.inline_namespace_leaf_at_def] >>
            imp_res_tac functionInlinerSelectedParameterDescriptorsTheory.inline_namespace_node_same_address >>
            qpat_x_assum `InlineNamespaceLeaf child.ia_function = InlineNamespaceLeaf (inline_entry_function b)` mp_tac >>
            simp[NoAsms]) >>
         `(inline_entry_function b).fn_blocks <> []` by
           (Cases_on `child.ia_function.fn_blocks` >>
            gvs[callLayoutDefsTheory.canonical_param_prefix_def]) >>
         `e.ise_callee.fn_blocks <> []` by
           metis_tac[functionInlinerOccurrencesTheory.inline_annotated_entry_first_label] >>
         Cases_on `e.ise_callee.fn_blocks` >>
         gvs[functionInlinerDefsTheory.clone_function_def]) >>
      qabbrev_tac `croute = route with ir_rename :=
        inline_path_rename (prefix ++ [InlineEnter e] ++ zipper)` >>
      `inline_namespace_leaf_at cert q croute.ir_rename child.ia_function` by
        (simp[Abbr `croute`] >> metis_tac[]) >>
      `frame.ipf_state.vs_current_bb = d.ic_block /\
       frame.ipf_state.vs_inst_idx = d.ic_index` by simp[] >>
      drule_all (Q.INST [`Tctx` |-> `Tctx`, `route` |-> `croute`]
        (SPEC_ALL inline_selected_source_body_cut)) >>
      disch_then (qspec_then `Tctx` strip_assume_tac) >>
      drule_all inline_selected_body_routed_boundary >> strip_tac >>
      FAIL_TAC "BODY selected: child fuel induction") >>
  FAIL_TAC "BODY non-INVOKE: direct return, terminal, ordinary successor or branch ENTRY"
QED

Resume inline_recursive_transport[initial]:
  rewrite_tac[inline_transport_initial_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `fuel` >- gvs[Once run_blocks_def] >>
  `inline_transport_body C Tctx R n` by simp[] >>
  Cases_on `fn.fn_blocks` >- gvs[] >> rename1 `fn.fn_blocks = entry::blocks` >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME entry` by
    simp[venomInstTheory.lookup_block_def, listTheory.FIND_thm] >>
  mp_tac (Q.SPECL [`s`,`entry.bb_instructions`] eval_phis_ok_or_error_defs) >>
  strip_tac
  >- (rename1 `eval_phis s entry.bb_instructions = OK post` >>
      `inline_resume C fn n
         (InlineBody entry (post with vs_inst_idx := phi_prefix_length entry.bb_instructions)) = result` by
        (drule_all inline_resume_entry_unfold >>
         disch_then (qspecl_then [`n`,`C`] mp_tac) >> simp[inline_resume_def]) >>
      FAIL_TAC "INITIAL: source entry unfolding and same-state parameter endpoint") >>
  qpat_x_assum `run_blocks (SUC n) C fn s = result` mp_tac >>
  simp[Once run_blocks_def] >> metis_tac[]
QED

Finalise inline_recursive_transport
