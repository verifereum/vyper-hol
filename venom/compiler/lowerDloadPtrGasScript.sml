Theory lowerDloadPtrGas
Ancestors lowerDloadPtrEnvironmentRead lowerDloadPtrScalar lowerDloadPtrOrdinary
  lowerDloadPtrPhi lowerDloadPtrRel lowerDloadPtrAggregate
  lowerDloadPtrBlockEntry lowerDloadPtrCall ptrDiscipline venomExecSemantics
  venomState venomInst unitShapeDefs codegenRel memLocDefs pointerConfinedDefs
  finite_map list pred_set

Theorem dload_boundary_core_gas_stream_update:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  dload_boundary_core lo fs V Ws PG PH G H tn un
    (s with vs_gas_readings := readings)
    (t with vs_gas_readings := readings) cs ds
Proof
  simp[dload_boundary_core_def] >> strip_tac >>
  rpt conj_tac
  >- (qpat_x_assum `dload_table_stack _ _ _` mp_tac >>
      simp[dload_table_stack_def] >> strip_tac >>
      gen_tac >> Cases_on `k`
      >- (qpat_x_assum `!k. _ ==> _` (qspec_then `0` mp_tac) >> simp[])
      >> qpat_x_assum `!k. _ ==> _` (qspec_then `SUC n` mp_tac) >> simp[])
  >- gvs[dload_vars_match_def, lookup_var_def]
  >- (gvs[dload_memory_match_def] >> first_assum ACCEPT_TAC)
  >- (gvs[dload_shared_store_def] >> first_assum ACCEPT_TAC)
  >- gvs[dload_equal_environment_def, venom_state_component_equality]
  >> simp[]
QED

Theorem gas_step_transport[local]:
  i.inst_opcode = GAS /\ dload_equal_environment s t /\
  step_inst fuel Ct i t = OK t' ==>
  ?out z readings. i.inst_outputs = [out] /\
    t' = update_var out z (t with vs_gas_readings := readings) /\
    step_inst fuel Cs i s =
      OK (update_var out z (s with vs_gas_readings := readings))
Proof
  strip_tac >>
  `s.vs_gas_readings = t.vs_gas_readings` by
    (qpat_x_assum `dload_equal_environment _ _` mp_tac >>
     simp[dload_equal_environment_def, venom_state_component_equality]) >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
    exec_gas_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  Cases_on `t.vs_gas_readings` >> gvs[]
  >- (qexistsl [`0w`, `[]`] >> simp[update_var_def, venom_state_component_equality])
  >> rename1 `t.vs_gas_readings = head::tail` >>
  qexistsl [`head`, `tail`] >> simp[]
QED

Theorem gas_ghost_updates[local]:
  i.inst_opcode = GAS /\ i.inst_outputs = [out] /\
  s'.vs_allocas = s.vs_allocas /\ s'.vs_fmp = s.vs_fmp ==>
  step_prov PG G i s' = set_prov G [out] NONE /\
  step_taint i s s' tn = tn with t_var := set_var_taint tn.t_var [out] {}
Proof
  strip_tac >>
  `out_taint tn i s = {} /\ written_taint tn i s = {}` by
    (conj_tac
     >- (irule out_taint_opcode_exclusion >> simp[])
     >> irule written_taint_opcode_exclusion >> simp[]) >>
  simp[step_prov_def, out_prov_def, step_taint_def,
    mem_taint_def, adopt_reset_def, store_taint_def, imm_taint_def,
    new_site_bytes_def, step_writes_def, range_bytes_def,
    source_memory_write_ranges_def, FLOOKUP_DEF,
    taint_component_equality, EXTENSION] >> simp[SF CONJ_ss]
QED

Theorem dload_boundary_core_gas:
  i.inst_opcode = GAS /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un) s' t' cs ds /\
    s' = s with <|vs_vars := s'.vs_vars; vs_gas_readings := s'.vs_gas_readings|> /\
    t' = t with <|vs_vars := t'.vs_vars; vs_gas_readings := t'.vs_gas_readings|>
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `dload_equal_environment s t` by metis_tac[dload_boundary_environment] >>
  drule_all gas_step_transport >>
  disch_then (qspec_then `Cs` strip_assume_tac) >> gnvs[] >>
  conj_tac >- (simp[lookup_var_def, update_var_def] >>
    rpt strip_tac >> Cases_on `v = out` >> gvs[lookup_var_def, FLOOKUP_UPDATE]) >>
  `dload_boundary_core lo fs V Ws PG PH G H tn un
    (s with vs_gas_readings := readings)
    (t with vs_gas_readings := readings) cs ds` by
    (irule dload_boundary_core_gas_stream_update >> simp[]) >>
  `step_prov PG G i (update_var out z (s with vs_gas_readings := readings)) =
     set_prov G [out] NONE /\
   step_taint i s (update_var out z (s with vs_gas_readings := readings)) tn =
     tn with t_var := set_var_taint tn.t_var [out] {}` by
    (irule gas_ghost_updates >> simp[update_var_def]) >>
  `step_prov PH H i (update_var out z (t with vs_gas_readings := readings)) =
     set_prov H [out] NONE /\
   step_taint i t (update_var out z (t with vs_gas_readings := readings)) un =
     un with t_var := set_var_taint un.t_var [out] {}` by
    (irule gas_ghost_updates >> simp[update_var_def]) >>
  simp[update_var_def] >>
  `dload_vars_match fs V (set_prov G [out] NONE) (set_prov H [out] NONE)
    (tn with t_var := set_var_taint tn.t_var [out] {})
    (un with t_var := set_var_taint un.t_var [out] {})
    ((s with vs_gas_readings := readings) with
      <|vs_vars := (update_var out z s).vs_vars; vs_inst_idx := s.vs_inst_idx|>)
    ((t with vs_gas_readings := readings) with
      <|vs_vars := (update_var out z t).vs_vars; vs_inst_idx := t.vs_inst_idx|>)` by
    (`dload_vars_match fs V (set_prov G [out] NONE) (set_prov H [out] NONE)
       (tn with t_var := set_var_taint tn.t_var [out] {})
       (un with t_var := set_var_taint un.t_var [out] {})
       (update_var out z (s with vs_gas_readings := readings))
       (update_var out z (t with vs_gas_readings := readings))` by
       (irule dload_vars_match_write >>
        simp[dload_value_word_def, word_agree_except_def] >>
        metis_tac[dload_boundary_vars]) >>
     gvs[dload_vars_match_def, lookup_var_def, update_var_def]) >>
  drule_all dload_boundary_core_var_index_update >>
  `s with <|vs_vars := s.vs_vars |+ (out,z); vs_inst_idx := s.vs_inst_idx;
     vs_gas_readings := readings|> =
   s with <|vs_vars := s.vs_vars |+ (out,z); vs_gas_readings := readings|>` by
    simp[venom_state_component_equality] >>
  `t with <|vs_vars := t.vs_vars |+ (out,z); vs_inst_idx := t.vs_inst_idx;
     vs_gas_readings := readings|> =
   t with <|vs_vars := t.vs_vars |+ (out,z); vs_gas_readings := readings|>` by
    simp[venom_state_component_equality] >>
  simp[update_var_def]
QED

Theorem dload_boundary_core_gas_index:
  i.inst_opcode = GAS /\
  MEM i (fn_insts f) /\ fn_ptr_ok P f /\ FDOM G SUBSET fn_pv P f /\
  access_ok lo G f i s /\ taint_ok f tn i s /\
  s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) i.inst_operands ==> v IN V /\ v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  step_inst fuel Ct i t = OK t' ==>
  ?s'. step_inst fuel Cs i s = OK s' /\
    (!v. v IN U ==>
      (lookup_var v (s' with vs_inst_idx := SUC s.vs_inst_idx) = NONE <=>
       lookup_var v (t' with vs_inst_idx := SUC t.vs_inst_idx) = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (step_prov PG G i s') (step_prov PH H i t')
      (step_taint i s s' tn) (step_taint i t t' un)
      (s' with vs_inst_idx := SUC s.vs_inst_idx)
      (t' with vs_inst_idx := SUC t.vs_inst_idx) cs ds /\
    s' = s with <|vs_vars := s'.vs_vars; vs_gas_readings := s'.vs_gas_readings|> /\
    t' = t with <|vs_vars := t'.vs_vars; vs_gas_readings := t'.vs_gas_readings|>
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dload_boundary_core_gas >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  qexists `s'` >> simp[lookup_var_def] >>
  conj_tac >- gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
