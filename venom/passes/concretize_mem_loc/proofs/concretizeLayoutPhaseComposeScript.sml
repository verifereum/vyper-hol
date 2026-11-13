Theory concretizeLayoutPhaseCompose
Ancestors concretizeLayoutPhaseExceptional concretizeLayoutPhaseOrigin
  ptrDiscipline frameRelocationEnvironment
  frameRelocationValues frameRelocationLocal concretizeLayoutSupplement
  concretizeLayoutReaderContext venomState

Theorem layout_ordinary_state_cursor:
  layout_ordinary_state D lo C' q0 es qs g s t ==>
  layout_ordinary_state D lo C' q0 es qs (g with lop_pending := F)
    (layout_phase_normalize g.lop_pending s)
    (layout_phase_normalize g.lop_pending t)
Proof
  Cases_on `g.lop_config` >>
  simp[layout_ordinary_state_def] >> rpt strip_tac >>
  Cases_on `g.lop_pending` >>
  gvs[local_rel_def, variable_domains_def, variables_agree_on_def,
    local_values_def, lookup_var_def, concretize_supplement_def,
    relocation_env_def, relocation_reader_context_def,
    concretize_local_obs_def, dead_result_rel_def] >> metis_tac[]
QED

Theorem layout_ordinary_administrative:
  layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t ==>
  layout_ordinary_entry D lo vs0 C C' q0 es qs q
    (g with lop_pending := F)
    (layout_phase_normalize g.lop_pending s)
    (layout_phase_normalize g.lop_pending t)
Proof
  simp[layout_ordinary_entry_def] >> strip_tac >>
  conj_tac >- gvs[layout_ordinary_trace_def] >>
  irule layout_ordinary_state_cursor >> simp[]
QED

Definition layout_phase_ready_def:
  (layout_phase_ready (INL g) = INL (g with lop_pending := F)) /\
  (layout_phase_ready (INR g) = INR (g with ltp_pending := F))
End

Definition layout_phase_pending_def:
  (layout_phase_pending (INL g) = g.lop_pending) /\
  (layout_phase_pending (INR g) = g.ltp_pending)
End

Theorem layout_phase_ready_entry:
  layout_phase_entry D lo vs0 C C' q0 es qs q g s t ==>
  layout_phase_entry D lo vs0 C C' q0 es qs q (layout_phase_ready g)
    (layout_phase_normalize (layout_phase_pending g) s)
    (layout_phase_normalize (layout_phase_pending g) t)
Proof
  Cases_on `g` >>
  simp[layout_phase_entry_def, layout_phase_ready_def, layout_phase_pending_def]
  >- metis_tac[layout_ordinary_administrative] >>
  rename1 `layout_terminal_entry C h s t` >>
  Cases_on `h.ltp_pending` >> simp[]
  >- (strip_tac >>
      drule_all layout_terminal_administrative >> simp[]) >>
  simp[layout_terminal_entry_def]
QED

Theorem layout_phase_ready_begins[simp]:
  layout_phase_begins (layout_phase_ready g) bb p <=>
  layout_phase_begins g bb p
Proof
  Cases_on `g` >>
  simp[layout_phase_begins_def, layout_phase_ready_def, layout_phase_origin_def]
QED

Theorem layout_phase_ok_abort_splice:
  layout_phase_ok_abort D lo vs0 C C' q0 es qs q g h (OK s) (OK t) /\
  layout_phase_ok_abort D lo vs0 C C' q0 es qs q h k r r' ==>
  layout_phase_ok_abort D lo vs0 C C' q0 es qs q g k r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[layout_phase_ok_abort_def] >> metis_tac[]
QED

Theorem layout_pending_returncopy_block_abort:
  ptr_discipline lo C vs0 /\ EVERY (fn_ptr_ok P) C.ctx_functions /\
  EVERY (\f. EVERY inst_wf (fn_insts f)) C.ctx_functions /\
  g.lop_pending /\ layout_ordinary_entry D lo vs0 C C' q0 es qs q g s t /\
  sn = layout_phase_normalize T s /\ tnxt = layout_phase_normalize T t /\
  g.lop_config = JointConfig stk PG G tn fn inst sn oms om hs h /\
  o1_fn_shape C fn /\ fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RETURNDATACOPY /\ inst.inst_operands = [opd;ops;opn] /\
  eval_operand opd sn = SOME dst /\ eval_operand ops sn = SOME src /\
  eval_operand opn sn = SOME sz /\
  get_instruction g.lop_origin.lbo_source sn.vs_inst_idx = SOME inst /\
  layout_block_pair positions g.lop_origin.lbo_source g.lop_origin.lbo_target
    sn.vs_inst_idx tnxt.vs_inst_idx /\
  revert_forward_pair g.lop_origin.lbo_source sn.vs_inst_idx j /\
  step_inst_base inst sn = OK post /\
  exec_block (SUC fuel) C g.lop_origin.lbo_source sn = Abort a final ==>
  ?final'. exec_block (SUC fuel) C' g.lop_origin.lbo_target tnxt = Abort a final' /\
    layout_phase_ok_abort D lo vs0 C C' q0 es qs q (INL g) (INL g)
      (Abort a final) (Abort a final')
Proof
  strip_tac >>
  `layout_ordinary_entry D lo vs0 C C' q0 es qs q
    (g with lop_pending := F) sn tnxt` by
    (drule layout_ordinary_administrative >> simp[]) >>
  drule_at (Pat `layout_ordinary_entry _ _ _ _ _ _ _ _ _ _ _ _`)
    layout_returncopy_phase_block_abort >>
  simp[layout_phase_ok_abort_def] >>
  disch_then irule >> gvs[] >> metis_tac[]
QED

val _ = export_theory();
