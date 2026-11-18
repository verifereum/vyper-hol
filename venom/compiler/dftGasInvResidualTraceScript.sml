Theory dftGasInvResidualTrace
Ancestors
  dftGasInvPseudoPrefix dftGasInvSSAProbe dftGasInvCrossingProbe
  dftGasInvOracleFrame dftGasOracleDefs dftScheduleOrder
  venomInstProofs venomExecSemantics venomInst venomState
  dftAvailability dftCorrectness dftRunRel list finite_map pred_set option

Definition inv_ev_trace_def:
  (inv_ev_trace orc p d fuel ctx [] s t <=> s = t) /\
  (inv_ev_trace orc p d fuel ctx (x::xs) s t <=>
    ?u. ~is_terminator x.inst_opcode /\
      ev_step orc p d fuel ctx x s = OK u /\
      inv_ev_trace orc p d fuel ctx xs
        (u with vs_inst_idx := SUC s.vs_inst_idx) t)
End

Theorem inv_ev_noninvoke_nonoutput:
  ev_step orc p d fuel ctx x s = OK t /\
  x.inst_opcode <> INVOKE /\ ~is_terminator x.inst_opcode /\
  ~MEM v x.inst_outputs ==>
  lookup_var v t = lookup_var v s
Proof
  strip_tac >> Cases_on `x.inst_opcode = GAS`
  >- (gvs[Once ev_step_def, ev_gas_def, AllCaseEqs()] >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `step_inst fuel ctx x s = OK t` by
    gvs[Once ev_step_def, Once step_inst_def] >>
  metis_tac[step_preserves_non_output_vars]
QED

Theorem inv_crossing_operand_frame:
  ev_step orc p d fuel ctx x s = OK t /\ inst_wf x /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> INVOKE /\ ~dft_must_order x y ==>
  !op. MEM op y.inst_operands ==>
    eval_operand op (t with vs_inst_idx := SUC s.vs_inst_idx) = eval_operand op s
Proof
  strip_tac >>
  `x.inst_opcode <> PHI` by (Cases_on `x.inst_opcode` >> fs[is_pseudo_def]) >>
  drule_all inv_ev_step_availability >> strip_tac >>
  Cases >> simp[eval_operand_def] >> strip_tac
  >- (rename1 `MEM (Var name) y.inst_operands` >>
      `~MEM name x.inst_outputs` by
        (fs[dft_must_order_def, inst_defs_def, inst_uses_def, DISJOINT_DEF,
            EXTENSION, MEM_operand_vars_iff] >> metis_tac[]) >>
      `lookup_var name t = lookup_var name s` by
        metis_tac[inv_ev_noninvoke_nonoutput] >>
      fs[lookup_var_def]) >>
  simp[]
QED

Theorem inv_codecopy_cannot_cross_memory:
  inv_memory_observation obs ==>
  ~inv_crossing_candidate CODECOPY obs outputs_empty
Proof
  simp[inv_memory_observation_def] >> rpt strip_tac >>
  gvs[inv_crossing_candidate_def, venomEffectsTheory.read_effects_def,
      venomEffectsTheory.write_effects_def, venomEffectsTheory.all_effects_def,
      venomEffectsTheory.empty_effects_def, is_terminator_def]
QED

Theorem inv_remaining_trace_extension:
  !pre s.
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  EVERY inst_wf bb.bb_instructions /\
  dft_remaining_inv fn bb (pre ++ y::post) s /\
  ~s.vs_call_ctx.cc_static /\ inv_memory_observation y.inst_opcode /\
  EVERY (\x. inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
    ~dft_must_order x y) pre ==>
  ?t. inv_ev_trace orc p d fuel ctx pre s t /\
    dft_remaining_inv fn bb (y::post) t /\
    (!op. MEM op y.inst_operands ==> eval_operand op t = eval_operand op s)
Proof
  Induct >> simp[inv_ev_trace_def] >>
  rpt strip_tac >>
  `h.inst_opcode <> INVOKE /\ h.inst_opcode <> CODECOPY` by
    metis_tac[inv_invoke_cannot_cross_memory, inv_codecopy_cannot_cross_memory,
              inv_crossing_candidate_necessary] >>
  `MEM h bb.bb_instructions /\ ~is_pseudo h.inst_opcode` by
    fs[dft_remaining_inv_def] >>
  `inst_wf h` by (fs[EVERY_MEM] >> metis_tac[]) >>
  `!op. MEM op h.inst_operands ==> ?v. eval_operand op s = SOME v` by
    metis_tac[inv_remaining_head_operands, IS_SOME_EXISTS] >>
  `?u. ev_step orc p d fuel ctx h s = OK u` by
    metis_tac[inv_crossed_predecessor_total] >>
  `dft_remaining_inv fn bb (pre ++ y::post)
      (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule (SRULE [] (Q.INST [`pre` |-> `[]`] inv_remaining_ev_step)) >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `u.vs_call_ctx = s.vs_call_ctx` by metis_tac[inv_ev_step_call_ctx] >>
  first_x_assum (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `t` >> simp[] >>
  metis_tac[inv_crossing_operand_frame]
QED

Theorem inv_entry_trace_extension:
  wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  EVERY inst_wf bb.bb_instructions /\
  bb.bb_instructions = pseudos ++ (pre ++ y::post) /\
  EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
  EVERY (\i. ~is_pseudo i.inst_opcode) (pre ++ y::post) /\
  fn_entry_label fn = SOME s.vs_current_bb /\ bb.bb_label = s.vs_current_bb /\
  ~s.vs_call_ctx.cc_static /\
  (!i l. MEM i bb.bb_instructions /\ ~is_pseudo i.inst_opcode /\
     ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
     i.inst_opcode <> CODECOPY /\ MEM (Label l) i.inst_operands ==>
     l IN FDOM s.vs_labels) /\
  eval_phis s bb.bb_instructions = OK u /\
  inv_ev_prefix orc p d ctx bb (LENGTH pseudos - phi_prefix_length pseudos)
    (u with vs_inst_idx := phi_prefix_length pseudos) t /\
  inv_memory_observation y.inst_opcode /\
  EVERY (\x. inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
    ~dft_must_order x y) pre ==>
  ?v. inv_ev_trace orc p d fuel ctx pre t v /\
    dft_remaining_inv fn bb (y::post) v /\
    (!op. MEM op y.inst_operands ==> eval_operand op v = eval_operand op t)
Proof
  strip_tac >>
  `FOLDR (dft_exec_cons fuel ctx) OK (DROP (phi_prefix_length pseudos) pseudos)
    (u with vs_inst_idx := phi_prefix_length pseudos) = OK t` by
    (irule inv_pseudo_prefix_drop >>
     simp[venomExecProofsTheory.phi_prefix_length_le] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `dft_remaining_inv fn bb (pre ++ y::post) t` by
    (drule_all inv_entry_pseudo_initialized >> simp[]) >>
  `t.vs_call_ctx = s.vs_call_ctx` by
    (drule inv_ev_prefix_call_ctx >> simp[] >>
     drule dftRunRelTheory.dft_eval_phis_call_ctx >> simp[]) >>
  irule inv_remaining_trace_extension >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
