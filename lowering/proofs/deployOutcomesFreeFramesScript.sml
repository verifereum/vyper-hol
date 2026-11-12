Theory deployOutcomesFreeFrames
Ancestors
  ptrDiscipline venomState venomExecSemantics codegenRel contextCodegenRel ctxLookupAgreeHelpers

Theorem outcomes_operand[simp]:
  eval_operand op (s with vs_outcomes := os) = eval_operand op s /\
  lookup_var v (s with vs_outcomes := os) = lookup_var v s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem outcomes_provenance[simp]:
  step_prov PG G inst (s with vs_outcomes := os) = step_prov PG G inst s /\
  entry_prov fn (s with vs_outcomes := os) G = entry_prov fn s G /\
  entry_taint_vars fn (s with vs_outcomes := os) tn = entry_taint_vars fn s tn
Proof
  simp[step_prov_def, out_prov_def, entry_prov_def, entry_taint_vars_def]
QED

Theorem outcomes_taint_parts[simp]:
  written_taint tn inst (s with vs_outcomes := os) = written_taint tn inst s /\
  out_taint tn inst (s with vs_outcomes := os) = out_taint tn inst s /\
  store_taint opc tn inst (s with vs_outcomes := os) X = store_taint opc tn inst s X /\
  imm_taint tn inst (s with vs_outcomes := os) = imm_taint tn inst s /\
  ret_taint tn inst (s with vs_outcomes := os) = ret_taint tn inst s
Proof
  simp[written_taint_def, out_taint_def, store_taint_def, imm_taint_def,
       ret_taint_def]
QED

Theorem outcomes_operands[simp]:
  !ops s os. eval_operands ops (s with vs_outcomes := os) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def]
QED

Theorem outcomes_memory_ranges[simp]:
  source_memory_write_ranges inst (s with vs_outcomes := os) = source_memory_write_ranges inst s /\
  source_memory_read_ranges inst (s with vs_outcomes := os) = source_memory_read_ranges inst s
Proof
  simp[source_memory_write_ranges_def, source_memory_read_ranges_def,
       fixed_source_write_range_def, sized_source_write_range_def,
       dret_memory_read_ranges_def, memory_range_of_operands_def]
QED

Theorem outcomes_step_taint[simp]:
  inst.inst_opcode <> CALL ==>
  step_taint inst (s with vs_outcomes := os) (t with vs_outcomes := ot) tn =
  step_taint inst s t tn
Proof
  simp[step_taint_def, adopt_reset_def, mem_taint_def, new_site_bytes_def,
       step_writes_def]
QED

Theorem outcomes_state_predicates[simp]:
  access_ok lo G fn inst (s with vs_outcomes := os) = access_ok lo G fn inst s /\
  taint_ok fn tn inst (s with vs_outcomes := os) = taint_ok fn tn inst s /\
  allocas_from lo (s with vs_outcomes := os) = allocas_from lo s /\
  allocas_below_fmp (s with vs_outcomes := os) = allocas_below_fmp s
Proof
  simp[access_ok_def, taint_ok_def, about_to_revert_def, in_revert_forward_def,
       active_inst_def, allocas_from_def, allocas_below_fmp_def]
QED

Theorem outcomes_active_inst[simp]:
  active_inst fn inst (s with vs_outcomes := os) = active_inst fn inst s
Proof
  simp[active_inst_def]
QED

Theorem outcomes_frames_entry_only:
  !vs ctx stk PG G tn fn inst s.
    frame_reachable vs ctx stk PG G tn fn inst s ==>
    !name entry.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME entry /\
      EVERY (\i. i.inst_opcode <> INVOKE) (fn_insts entry) ==>
      stk = [] /\ fn = entry
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >> strip_tac
  >- gvs[]
  >- (first_x_assum drule_all >> strip_tac >> gvs[] >>
      drule_all EVERY_active_inst >> simp[])
  >- (first_x_assum drule_all >> simp[])
QED

Theorem outcomes_frames_transport:
  !vs ctx stk PG G tn fn inst t.
    frame_reachable vs ctx stk PG G tn fn inst t ==>
    !s os name entry.
      vs = (s with vs_outcomes := os) /\
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME entry /\
      EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) /\
      (!i u v fuel os. active_inst entry i u /\
        step_inst fuel ctx i (u with vs_outcomes := os) = OK v ==>
        ?v0. step_inst fuel ctx i u = OK v0 /\ v = (v0 with vs_outcomes := os)) /\
      (!u v os. enters_block entry (u with vs_outcomes := os) v ==>
        ?v0. enters_block entry u v0 /\ v = (v0 with vs_outcomes := os)) ==>
      stk = [] /\ fn = entry /\
      ?t0. frame_reachable s ctx stk PG G tn fn inst t0 /\
           t = (t0 with vs_outcomes := os)
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> rpt gen_tac >> strip_tac
  >- (gvs[] >>
      qpat_x_assum `!u v os. _` (qspec_then
        `s with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>` mp_tac) >>
      disch_then (qspecl_then [`t`, `os`] mp_tac) >> simp[] >> strip_tac >>
      gvs[] >> qexists_tac `v0` >> simp[] >> irule frame_reachable_entry >>
      goal_assum (drule_at Any) >> simp[])
  >- (first_x_assum drule_all >> strip_tac >> gvs[] >>
      `inst.inst_opcode <> CALL` by
        (drule EVERY_active_inst >> disch_then (qspecl_then [`t0`, `inst`] mp_tac) >> simp[]) >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      qexists_tac `v0 with vs_inst_idx := SUC t0.vs_inst_idx` >> simp[] >>
      irule frame_reachable_next >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> gvs[active_inst_def] >> metis_tac[])
  >- (first_x_assum drule_all >> strip_tac >> gvs[] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      first_x_assum drule_all >> strip_tac >> gvs[] >>
      qexists_tac `v0'` >> simp[] >> irule frame_reachable_block >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[])
  >- (first_x_assum drule_all >> strip_tac >> gvs[] >>
      drule_all EVERY_active_inst >> simp[])
  >- (first_x_assum drule_all >> simp[])
QED

Theorem outcomes_final_taint_transport:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME entry /\
  EVERY (\i. ~MEM i.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE]) (fn_insts entry) /\
  (!i u v fuel os. active_inst entry i u /\
    step_inst fuel ctx i (u with vs_outcomes := os) = OK v ==>
    ?v0. step_inst fuel ctx i u = OK v0 /\ v = (v0 with vs_outcomes := os)) /\
  (!u v os. enters_block entry (u with vs_outcomes := os) v ==>
    ?v0. enters_block entry u v0 /\ v = (v0 with vs_outcomes := os)) /\
  (!i u v fuel os. active_inst entry i u /\
    step_inst fuel ctx i (u with vs_outcomes := os) = Halt v ==>
    ?v0. step_inst fuel ctx i u = Halt v0 /\ v = (v0 with vs_outcomes := os)) /\
  final_taint (s with vs_outcomes := os) ctx t tn R ==>
  ?t0. final_taint s ctx t0 tn R /\ t = (t0 with vs_outcomes := os)
Proof
  simp[final_taint_def] >> strip_tac >>
  drule outcomes_frames_transport >>
  disch_then (qspecl_then [`s`, `os`, `name`, `entry`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[] >>
  `inst.inst_opcode <> CALL` by
    (drule EVERY_active_inst >> disch_then (qspecl_then [`t0`, `inst`] mp_tac) >> simp[]) >>
  qexists_tac `v0` >> simp[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED
