Theory algebraicOptMainStepProofs
Ancestors
  algebraicOptMainProducerProofs algebraicOptMainScalarProofs
  algebraicOptMainResidualStepProofs algebraicOptMainLayoutProofs
  algebraicOptIszeroPreservationProofs algebraicOptDefs opcodeClass
  algebraicOptCmpChunkProofs
  algebraicOptTraceProofs algebraicOptShapeProofs instIdxIndep venomExecSemantics venomInst venomWf
Libs
  listTheory

Theorem ao_main_terminator_step:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  trace <> [] /\ ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM inst (fn_insts fn) /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ is_terminator inst.inst_opcode /\
  ao_main_observations fn V s r /\
  s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|> = r /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) ==>
  ao_transform_inst dfg ra lbl idx (ao_compute_fn_iszero_targets fn) fr inst =
    [ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst] /\
  ((?e. step_inst fuel ctx inst s = Error e) \/
   lift_result
     (\t u. ao_main_observations fn V t u /\
       t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> = u /\
       t.vs_inst_idx = 0 /\ u.vs_inst_idx = 0)
     (execution_equiv UNIV) (execution_equiv UNIV)
     (step_inst fuel ctx inst s)
     (step_inst fuel ctx (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst) r))
Proof
  strip_tac >>
  `ao_transform_inst dfg ra lbl idx (ao_compute_fn_iszero_targets fn) fr inst =
    [ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst]` by
    (irule ao_transform_inst_control_owner >> simp[]) >> simp[] >>
  `~MEM inst.inst_opcode
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT; ISZERO; BALANCE; EXTCODESIZE] /\
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  mp_tac ao_main_residual_transform_step >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (qspec_then `ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst` mp_tac) >>
  simp[] >>
  Cases_on `step_inst fuel ctx inst s` >>
  Cases_on `step_inst fuel ctx
    (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst) r` >>
  simp[stateEquivTheory.lift_result_def] >> strip_tac >> gvs[] >>
  `v.vs_inst_idx = 0` by
    (irule terminator_OK_inst_idx_0 >> qexistsl [`inst`,`s`] >>
     gvs[step_inst_non_invoke]) >>
  `v'.vs_inst_idx = 0` by
    (irule terminator_OK_inst_idx_0 >>
     qexistsl [`ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst`,`r`] >>
     gvs[step_inst_non_invoke, ao_resolve_iszero_inst_fields]) >> simp[]
QED

Theorem ao_main_special_chunk:
  !ctx fn s0 n k s inst bb V r t mid fr next fuel.
  ao_source_prefix ctx fn s0 n k F s /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  s0.vs_inst_idx = 0 /\ s0.vs_prev_bb = NONE /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==> lookup_var x s0 = NONE) /\
  MEM inst (fn_insts fn) /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT; ISZERO; BALANCE; EXTCODESIZE] /\
  step_inst_base inst s = OK t /\
  ao_main_observations fn V s r /\
  s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|> = r /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  ir_supply_inst_ok mid /\ V SUBSET set mid.irs_used_vars /\
  ao_alloc_fresh mid = (fr,next) ==>
  ?u. ao_cmp_exec_chunk fuel ctx
        (ao_transform_inst (dfg_build_function fn) (range_analyze fn)
          s.vs_current_bb s.vs_inst_idx (ao_compute_fn_iszero_targets fn) fr inst) r = OK u /\
      ao_main_observations fn V t u /\
      (u with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
      u.vs_inst_idx = r.vs_inst_idx + LENGTH
        (ao_transform_inst (dfg_build_function fn) (range_analyze fn)
          s.vs_current_bb s.vs_inst_idx (ao_compute_fn_iszero_targets fn) fr inst)
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_labels = r.vs_labels /\ s.vs_accounts = r.vs_accounts /\
   s.vs_call_ctx = r.vs_call_ctx` by
    gvs[venomStateTheory.venom_state_component_equality] >>
  Cases_on `MEM inst.inst_opcode [ISZERO; BALANCE; EXTCODESIZE]`
  >- (drule ao_source_prefix_has_trace >> strip_tac >>
      `!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
         lookup_var x (SND (SND (HD trace))) = NONE` by (simp[] >> metis_tac[]) >>
      Cases_on `inst.inst_opcode = ISZERO`
      >- suspend "iszero" >>
      `MEM inst.inst_opcode [BALANCE; EXTCODESIZE]` by fs[MEM] >>
      irule ao_main_environment_producer_chunk >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule ao_main_allocated_scalar_chunk >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[MEM]
QED
Resume ao_main_special_chunk[iszero]:
  `?op. inst.inst_operands = [op]` by
    (qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
     simp[step_inst_base_opcode_eqs, exec_pure1_def,
          AllCaseEqs()] >> metis_tac[]) >>
  `LENGTH (ao_transform_inst (dfg_build_function fn) (range_analyze fn)
    s.vs_current_bb s.vs_inst_idx (ao_compute_fn_iszero_targets fn) fr inst) = 1` by
    simp[ao_transform_iszero] >>
  simp[] >> irule ao_main_iszero_transform_chunk >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
Finalise ao_main_special_chunk

Theorem ao_main_ordinary_chunk:
  !ctx fn s0 n k s inst bb V r mid fr next.
  ao_source_prefix ctx fn s0 n k F s /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  s0.vs_inst_idx = 0 /\ s0.vs_prev_bb = NONE /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==> lookup_var x s0 = NONE) /\
  MEM inst (fn_insts fn) /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode /\
  ao_main_observations fn V s r /\
  s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|> = r /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  ir_supply_inst_ok mid /\ V SUBSET set mid.irs_used_vars /\
  ao_alloc_fresh mid = (fr,next) ==>
  (?e. step_inst k ctx inst s = Error e) \/
  lift_result
    (\t u. ao_main_observations fn V (t with vs_inst_idx := SUC s.vs_inst_idx) u /\
      t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> = u /\
      u.vs_inst_idx = r.vs_inst_idx + LENGTH
        (ao_transform_inst (dfg_build_function fn) (range_analyze fn)
          s.vs_current_bb s.vs_inst_idx (ao_compute_fn_iszero_targets fn) fr inst))
    (execution_equiv UNIV) (execution_equiv UNIV)
    (step_inst k ctx inst s)
    (ao_cmp_exec_chunk k ctx
      (ao_transform_inst (dfg_build_function fn) (range_analyze fn)
        s.vs_current_bb s.vs_inst_idx (ao_compute_fn_iszero_targets fn) fr inst) r)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `MEM inst.inst_opcode
    [SHL; SHR; SAR; SIGNEXTEND; Exp; ADD; SUB; XOR; AND; MUL;
     Div; SDIV; Mod; SMOD; OR; EQ; GT; LT; SGT; SLT; ISZERO; BALANCE; EXTCODESIZE]`
  >- suspend "special" >>
  drule ao_source_prefix_has_trace >> strip_tac >>
  `!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE` by (simp[] >> metis_tac[]) >>
  mp_tac (Q.INST [`h` |-> `k`, `fuel` |-> `k`] ao_main_residual_transform_step) >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  disch_then (qspec_then `ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst` mp_tac) >>
  simp[ao_transform_inst_residual_singleton] >>
  suspend "residual"
QED
Resume ao_main_ordinary_chunk[special]:
  `inst.inst_opcode <> INVOKE` by fs[MEM] >>
  simp[step_inst_non_invoke] >>
  Cases_on `step_inst_base inst s` >> simp[]
  >- suspend "special_ok"
  >- (drule step_inst_base_halt_opcodes >> fs[MEM])
  >- (drule step_inst_base_abort_opcodes >> fs[MEM]) >>
  drule step_inst_base_intret_opcodes >> fs[MEM]
QED
Resume ao_main_ordinary_chunk[special_ok]:
  `?u. ao_cmp_exec_chunk k ctx
        (ao_transform_inst (dfg_build_function fn) (range_analyze fn)
          s.vs_current_bb s.vs_inst_idx (ao_compute_fn_iszero_targets fn) fr inst) r = OK u /\
      ao_main_observations fn V v u /\
      (u with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r /\
      u.vs_inst_idx = r.vs_inst_idx + LENGTH
        (ao_transform_inst (dfg_build_function fn) (range_analyze fn)
          s.vs_current_bb s.vs_inst_idx (ao_compute_fn_iszero_targets fn) fr inst)` by
    (irule ao_main_special_chunk >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  simp[stateEquivTheory.lift_result_def] >>
  conj_tac
  >- (irule algebraicOptMainResidualProofsTheory.ao_main_observations_vars >>
      goal_assum (drule_at Any) >> simp[]) >>
  `v with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s` by
    (qpat_x_assum `step_inst_base inst s = OK v` mp_tac >>
     gvs[MEM] >> simp[step_inst_base_opcode_eqs, exec_pure1_def, exec_pure2_def,
       exec_read1_def, AllCaseEqs(), venomStateTheory.update_var_def] >>
     rpt strip_tac >> gvs[]) >>
  gvs[venomStateTheory.venom_state_component_equality]
QED
Resume ao_main_ordinary_chunk[residual]:
  `~MEM inst.inst_opcode [JMP; DJMP; JNZ]` by
    (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
  simp[MEM, ao_cmp_exec_chunk_single] >>
  Cases_on `step_inst k ctx inst s` >>
  Cases_on `step_inst k ctx
    (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) inst) r` >>
  simp[stateEquivTheory.lift_result_def] >> strip_tac >> gvs[] >>
  conj_tac
  >- (irule algebraicOptMainResidualProofsTheory.ao_main_observations_vars >>
      goal_assum (drule_at Any) >> simp[]) >>
  gvs[venomStateTheory.venom_state_component_equality]
QED
Finalise ao_main_ordinary_chunk
