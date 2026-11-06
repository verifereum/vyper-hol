Theory concretizeLayoutPhaseAllocation
Ancestors concretizeLayoutPhaseOrigin concretizeLayoutPhaseSuccess
  concretizeLayoutLocalAllocation concretizeStepStructure
  concretizeMemLocDefs passSharedDefs venomExecSemantics venomState venomInst ptrDiscipline list

Theorem layout_alloca_trace_step:
  vs0.vs_allocas = FEMPTY /\
  ~g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  g.lop_config = JointConfig stk PG G tn fn inst s oms om hs h /\
  g.lop_ids = birth::ids /\ g.lop_anns = (rp,rv)::anns /\
  g.lop_cursor < LENGTH es /\
  EL g.lop_cursor es = SOME (OriginOrdinary fuel post) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit sz] /\
  inst.inst_outputs = [v] /\
  FLOOKUP positions (Allocation inst.inst_id) =
    SOME (concretize_positions C' fn inst.inst_id) /\
  get_instruction g.lop_origin.lbo_source s.vs_inst_idx = SOME inst /\
  step_inst_base inst s = OK post ==>
  ?k tpost.
    step_inst_base (concretize_inst_with_positions positions inst) t = OK tpost /\
    k.lop_pending /\ k.lop_cursor = SUC g.lop_cursor /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q
      (INL g) (INL k) (OK post) (OK tpost)
Proof
  strip_tac >>
  `layout_ordinary_trace vs0 C q0 es qs q g s /\
   layout_ordinary_state D lo C' q0 es qs g s t` by
    fs[layout_ordinary_entry_def] >>
  `joint_trace vs0 C q0 es qs q /\
   EL g.lop_cursor (q0::qs) = g.lop_config` by
    fs[layout_ordinary_trace_def] >>
  qpat_x_assum `layout_ordinary_state _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[layout_ordinary_state_def] >> strip_tac >> gvs[] >> fs[ETA_AX] >>
  ` (concretize_inst_with_positions positions inst).inst_opcode = ASSIGN /\
    (concretize_inst_with_positions positions inst).inst_operands =
      [Lit (n2w (concretize_positions C' fn inst.inst_id))] /\
    (concretize_inst_with_positions positions inst).inst_outputs = [v]` by
    simp[concretize_inst_with_positions_def, mk_assign_inst_def] >>
  drule_at (Pat `local_rel _ _ _ _ _ _ _`) concretize_alloca_local_complete >>
  disch_then (drule_at (Pat `joint_trace _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  disch_then (drule_at (Pat `concretize_supplement _ _ _ _`)) >>
  simp[] >>
  disch_then (qspecl_then [`concretize_inst_with_positions positions inst`, `rp`] mp_tac) >>
  simp[] >> strip_tac >>
  `step_inst fuel C inst s = OK post` by simp[step_inst_non_invoke] >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_ordinary_success_phase >>
  disch_then (drule_at (Pat `step_inst _ _ _ _ = OK _`)) >>
  disch_then (drule_at (Pat `relocation_taint_le _ _ _`)) >>
  simp[is_terminator_def, ETA_AX] >>
  disch_then (qspec_then `tpost` mp_tac) >> simp[] >> metis_tac[]
QED
