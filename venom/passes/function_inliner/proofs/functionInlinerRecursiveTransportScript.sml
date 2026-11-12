(* Finite evaluator segments, indexed by actual entry and interior body cuts. *)
Theory functionInlinerRecursiveTransport
Ancestors
  functionInlinerSelectedSource functionInlinerSelectedContinuation
  functionInlinerLiveSteps functionInlinerLiveEdges functionInlinerFuel
  venomExecSemantics venomExecProofs arithmetic

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
    inline_live_stack C cert root
      ((q,ca,route,snap with <|ils_state := ss (LENGTH params);
        ils_defined := set (FLAT (MAP (\i. i.inst_outputs) params))|>)::
       (p,pa,proute,psnap)::entries)
      (frame with ipf_state := ts (LENGTH params))
Proof
  strip_tac >> drule_all inline_live_selected_source_entry_trace >>
  disch_then (qspecl_then [`0`, `Tctx`] strip_assume_tac) >>
  qexistsl [`k`, `bres`, `ss`, `ml`, `bb`, `tb`, `snap`, `ts`] >> simp[] >>
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
