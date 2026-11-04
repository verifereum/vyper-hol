Theory lowerDloadPtrOrdinary
Ancestors
  lowerDloadPtrBlockEntry lowerDloadPtrAggregate lowerDloadPtrPhi
  lowerDloadPtrRel venomExecSemantics venomState venomInst ptrDiscipline
  unitShapeDefs codegenRel memLocDefs finite_map list pred_set

Theorem retpc_assign_input_tracked[local]:
  MEM i (fn_insts f) /\ i.inst_opcode = ASSIGN /\
  MEM v i.inst_outputs /\ ~retpc_var f v /\
  i.inst_operands = [Var w] ==> ~retpc_var f w
Proof
  simp[retpc_var_def] >> metis_tac[copy_phi_var_assign]
QED

Theorem assign_step_success[local]:
  i.inst_opcode = ASSIGN ==>
  (step_inst fuel C i s = OK s' <=>
   ?op out a. i.inst_operands = [op] /\ i.inst_outputs = [out] /\
     eval_operand op s = SOME a /\ s' = update_var out a s)
Proof
  strip_tac >> simp[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem assign_ghost_updates[local]:
  i.inst_opcode = ASSIGN /\ i.inst_operands = [op] /\ i.inst_outputs = [out] /\
  eval_operand op s = SOME a ==>
  step_prov PG G i (update_var out a s) = set_prov G [out] (op_prov G op) /\
  step_taint i s (update_var out a s) tn =
    tn with t_var := set_var_taint tn.t_var [out] (op_taint tn op)
Proof
  simp[step_prov_def, out_prov_def, first_prov_def, step_taint_def,
    mem_taint_def, out_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, update_var_def, new_site_bytes_def, step_writes_def,
    written_taint_def, range_bytes_def, source_memory_write_ranges_def,
    FLOOKUP_DEF, taint_component_equality] >>
  Cases_on `op_prov G op` >> simp[EXTENSION] >> metis_tac[]
QED

Theorem dload_boundary_core_assign:
  MEM i (fn_insts f) /\ i.inst_opcode = ASSIGN /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t' cs ds /\
    s' = s with vs_vars := s'.vs_vars /\
    t' = t with vs_vars := t'.vs_vars
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[assign_step_success] >> strip_tac >> gvs[] >>
  `eval_operand op s <> NONE` by
    (drule eval_operand_definedness >>
     disch_then (qspec_then `op` mp_tac) >>
     (impl_tac >- metis_tac[MEM]) >> simp[]) >>
  Cases_on `eval_operand op s` >- gvs[] >>
  rename1 `eval_operand op t = SOME b` >>
  rename1 `eval_operand op s = SOME a` >>
  `dload_vars_match fs {v | ~retpc_var f v} G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `~retpc_var f out ==> op_taint tn op = op_taint un op /\
    dload_value_word fs (op_taint tn op) (op_prov G op) (op_prov H op) a b` by
    (strip_tac >>
     `!w. op = Var w ==> ~retpc_var f w` by
       metis_tac[retpc_assign_input_tracked, MEM] >>
     conj_tac >- (Cases_on `op` >> gvs[op_taint_def, dload_vars_match_def]) >>
     irule dload_matched_operand >>
     qexistsl [`{v | ~retpc_var f v}`,`s`,`t`,`un`] >> simp[]) >>
  drule_all assign_ghost_updates >> strip_tac >>
  qpat_x_assum `eval_operand op s = SOME a` mp_tac >>
  drule_all assign_ghost_updates >> strip_tac >> disch_tac >>
  qexists `update_var out a s` >>
  simp[assign_step_success, assign_ghost_updates] >>
  conj_tac >- (rpt strip_tac >>
    irule update_var_definedness >> qexists `U` >> simp[]) >>
  simp[update_var_def] >>
  `dload_vars_match fs {v | ~retpc_var f v}
    (set_prov G [out] (op_prov G op)) (set_prov H [out] (op_prov H op))
    (tn with t_var := set_var_taint tn.t_var [out] (op_taint tn op))
    (un with t_var := set_var_taint un.t_var [out] (op_taint un op))
    (s with <|vs_vars := (update_var out a s).vs_vars; vs_inst_idx := s.vs_inst_idx|>)
    (t with <|vs_vars := (update_var out b t).vs_vars; vs_inst_idx := t.vs_inst_idx|>)` by
    (simp[update_var_def] >> pure_rewrite_tac[GSYM update_var_def] >>
     irule dload_vars_match_write >> simp[]) >>
  drule_all dload_boundary_core_var_index_update >> simp[update_var_def]
QED

Theorem dload_boundary_core_assign_index:
  MEM i (fn_insts f) /\ i.inst_opcode = ASSIGN /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==>
      (lookup_var v (s' with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (t' with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un)
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
      (t' with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    s' = s with vs_vars := s'.vs_vars /\
    t' = t with vs_vars := t'.vs_vars
Proof
  strip_tac >> drule_all dload_boundary_core_assign >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  qexists `s'` >> simp[lookup_var_def] >>
  conj_tac >- gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
