Theory lowerDloadPtrParameters
Ancestors
  lowerDloadPtrOrdinary lowerDloadPtrJointNext lowerDloadPtrCall
  lowerDloadPtrAggregate lowerDloadPtrBlockEntry lowerDloadPtrPhi
  lowerDloadPtrRel venomInst contextCodegenRel
  venomExecSemantics venomState ptrDiscipline unitShapeDefs codegenRel memLocDefs pred_set list finite_map words

Theorem parameter_step_success[local]:
  (i.inst_opcode = PARAM \/ i.inst_opcode = RETPC_PARAM) ==>
  (step_inst fuel C i s = OK s1 <=>
   ?idx out. i.inst_operands = [Lit idx] /\ i.inst_outputs = [out] /\
     (i.inst_opcode = PARAM ==> w2n idx < LENGTH s.vs_params) /\
     s1 = update_var out
       (if i.inst_opcode = PARAM then EL (w2n idx) s.vs_params
        else s.vs_return_pc_token) s)
Proof
  strip_tac >> gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem parameter_ghost_updates[local]:
  (i.inst_opcode = PARAM \/ i.inst_opcode = RETPC_PARAM) /\
  i.inst_operands = [Lit idx] /\ i.inst_outputs = [out] ==>
  step_prov PG G i (update_var out a s) = set_prov G [out]
    (if i.inst_opcode = PARAM /\ w2n idx < LENGTH PG then EL (w2n idx) PG else NONE) /\
  step_taint i s (update_var out a s) tn =
    tn with t_var := set_var_taint tn.t_var [out] {}
Proof
  strip_tac >> gvs[step_prov_def, out_prov_def, step_taint_def,
    mem_taint_def, out_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, update_var_def, new_site_bytes_def, step_writes_def,
    written_taint_def, range_bytes_def, source_memory_write_ranges_def,
    FLOOKUP_DEF, taint_component_equality] >>
  simp[EXTENSION, eval_operand_def, SF CONJ_ss]
QED

Theorem dload_boundary_core_parameter_tracked:
  MEM i (fn_insts f) /\ (i.inst_opcode = PARAM \/ i.inst_opcode = RETPC_PARAM) /\
  (i.inst_opcode = RETPC_PARAM ==> !out. MEM out i.inst_outputs ==> out NOTIN V) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t1 ==>
  ?s1. step_inst fuel Cs i s = OK s1 /\
    (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 cs ds /\
    s1 = s with vs_vars := s1.vs_vars /\ t1 = t with vs_vars := t1.vs_vars
Proof
  strip_tac >>
  `dload_param_values fs PG PH s.vs_params t.vs_params` by
    metis_tac[dload_boundary_params] >>
  `LENGTH s.vs_params = LENGTH t.vs_params` by
    metis_tac[dload_param_values_length] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[parameter_step_success] >> strip_tac >> gvs[] >>
  simp[parameter_step_success, parameter_ghost_updates, step_prov_def, out_prov_def] >>
  (conj_tac >- (rpt strip_tac >> irule update_var_definedness >> qexists `U` >> simp[])) >>
  simp[update_var_def] >>
  qmatch_goalsub_abbrev_tac `set_prov G [out] p` >>
  qmatch_goalsub_abbrev_tac `set_prov H [out] q` >>
  qmatch_goalsub_abbrev_tac `s with vs_vars := sv` >>
  qmatch_goalsub_abbrev_tac `t with vs_vars := tv` >>
  `dload_vars_match fs V
    (set_prov G [out] p) (set_prov H [out] q)
    (tn with t_var := set_var_taint tn.t_var [out] {})
    (un with t_var := set_var_taint un.t_var [out] {})
    (s with <|vs_vars := sv; vs_inst_idx := s.vs_inst_idx|>)
    (t with <|vs_vars := tv; vs_inst_idx := t.vs_inst_idx|>)` by
    (simp[Abbr `sv`, Abbr `tv`] >> pure_rewrite_tac[GSYM update_var_def] >>
     `out IN V ==> dload_value_word fs {} p q
       (if i.inst_opcode = PARAM then EL (w2n idx) s.vs_params else s.vs_return_pc_token)
       (if i.inst_opcode = PARAM then EL (w2n idx) t.vs_params else t.vs_return_pc_token)` by
       (strip_tac >> unabbrev_all_tac >> gvs[] >>
        `w2n idx < LENGTH s.vs_params` by simp[] >>
        drule_all dload_param_values_lookup >> simp[]) >>
     irule dload_vars_match_write >> simp[] >>
     metis_tac[dload_boundary_vars]) >>
  drule_all dload_boundary_core_var_index_update >> simp[]
QED

Theorem dload_boundary_core_parameter_tracked_index:
  MEM i (fn_insts f) /\ (i.inst_opcode = PARAM \/ i.inst_opcode = RETPC_PARAM) /\
  (i.inst_opcode = RETPC_PARAM ==> !out. MEM out i.inst_outputs ==> out NOTIN V) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t1 ==>
  ?s1. step_inst fuel Cs i s = OK s1 /\
    (!v. v IN U ==>
      (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (t1 with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un)
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    s1 = s with vs_vars := s1.vs_vars /\ t1 = t with vs_vars := t1.vs_vars
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_at (Pat `dload_boundary_core`) dload_boundary_core_parameter_tracked >>
  disch_then (drule_at (Pat `step_inst`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  disch_then (qspec_then `U` mp_tac) >> simp[] >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  qexists `s1` >> simp[lookup_var_def] >>
  conj_tac >- gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED

Theorem dload_parameter_retpc_output:
  MEM i (fn_insts f) /\ i.inst_opcode = RETPC_PARAM ==>
  !out. MEM out i.inst_outputs ==> retpc_var f out
Proof
  rpt strip_tac >> simp[retpc_var_def] >>
  irule copy_phi_var_seed >> qexists `i` >> simp[]
QED

Theorem dload_boundary_core_parameter:
  MEM i (fn_insts f) /\ (i.inst_opcode = PARAM \/ i.inst_opcode = RETPC_PARAM) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t1 ==>
  ?s1. step_inst fuel Cs i s = OK s1 /\
    (!v. v IN U ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1 cs ds /\
    s1 = s with vs_vars := s1.vs_vars /\ t1 = t with vs_vars := t1.vs_vars
Proof
  strip_tac >> irule dload_boundary_core_parameter_tracked >>
  simp[] >> metis_tac[dload_parameter_retpc_output]
QED

Theorem dload_actual_parameter_next:
  frame_reachable vs C cs PG G tn f i s /\
  dload_control_match q f g s t i [i] 0 /\
  (i.inst_opcode = PARAM \/ i.inst_opcode = RETPC_PARAM) /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) g.fn_blocks) /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  step_inst fuel C' i t = OK t1 /\
  active_inst g j (t1 with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?s1 i' emitted'.
    step_inst fuel C i s = OK s1 /\
    frame_reachable vs C cs PG (step_prov PG G i s1) (step_taint i s s1 tn)
      f i' (s1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    dload_control_match q f g
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) i' emitted' 0 /\
    j = HD emitted' /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (step_prov PG G i s1) (step_prov PH H i t1)
      (step_taint i s s1 tn) (step_taint i t t1 un)
      (s1 with vs_inst_idx := SUC s.vs_inst_idx)
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    (!v. v IN U ==>
      (lookup_var v (s1 with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (t1 with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    s1 = s with vs_vars := s1.vs_vars /\ t1 = t with vs_vars := t1.vs_vars
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM i (fn_insts f)` by
    (qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
     simp[dload_control_match_def, active_inst_def, fn_insts_def,
          o1PassContractTheory.fn_insts_blocks_MEM] >> metis_tac[EL_MEM]) >>
  drule_all dload_boundary_core_parameter >>
  disch_then (qspec_then `C` strip_assume_tac) >>
  `~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    (gvs[is_terminator_def]) >>
  drule_all dload_singleton_reachable_next >> strip_tac >>
  qexistsl [`s1`,`i'`,`emitted'`] >> simp[lookup_var_def] >>
  conj_tac >- (irule dload_boundary_core_index_update >> simp[]) >>
  gvs[lookup_var_def]
QED
