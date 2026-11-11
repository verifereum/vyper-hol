Theory lowerDloadPtrBump
Ancestors
  lowerDloadPtrScalar lowerDloadPtrPhi lowerDloadPtrRel lowerDloadPtrAggregate
  lowerDloadPtrOrdinary lowerDloadPtrBlockEntry ptrDiscipline unitShapeDefs codegenRel memLocDefs
  venomExecSemantics venomState venomInst pointerConfinedDefs finite_map pred_set list

Theorem bump_operand_clean[local]:
  i.inst_opcode = BUMP /\ MEM i (fn_insts f) /\ fn_ptr_ok P f /\
  FDOM G SUBSET fn_pv P f /\ taint_ok f tn i s /\
  MEM op i.inst_operands ==>
  op_prov G op = NONE /\ op_taint tn op = {}
Proof
  strip_tac >>
  `ptr_use_ok P (fn_pv P f) i` by metis_tac[fn_ptr_ok_def] >>
  gvs[ptr_use_ok_def, is_pointer_preserving_op_def,
    mem_read_ops_def, mem_write_ops_def, taint_ok_def] >>
  Cases_on `op` >> gvs[op_prov_def, FLOOKUP_DEF, SUBSET_DEF] >> metis_tac[]
QED

Theorem bump_step_transport[local]:
  i.inst_opcode = BUMP /\
  (!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t) /\
  step_inst fuel Ct i t = OK t' ==>
  ?p n b z. i.inst_outputs = [p;n] /\
    t' = update_var n (word_add b z) (update_var p b t) /\
    step_inst fuel Cs i s =
      OK (update_var n (word_add b z) (update_var p b s))
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  strip_tac >> gvs[MEM] >> metis_tac[]
QED

Theorem bump_ghost_updates[local]:
  i.inst_opcode = BUMP /\ i.inst_outputs = [p;n] ==>
  step_prov PG G i (update_var n z (update_var p b s)) =
    DRESTRICT G (COMPL {p;n}) /\
  step_taint i s (update_var n z (update_var p b s)) tn =
    tn with t_var := DRESTRICT tn.t_var (COMPL {p;n})
Proof
  strip_tac >>
  `out_taint tn i s = {} /\ written_taint tn i s = {}` by
    (conj_tac >- (irule out_taint_opcode_exclusion >> simp[]) >>
     irule written_taint_opcode_exclusion >> simp[]) >>
  simp[step_prov_def, out_prov_def, step_taint_def, set_prov_def,
    set_var_taint_def, mem_taint_def, adopt_reset_def, store_taint_def,
    imm_taint_def, update_var_def] >>
  simp[new_site_bytes_def, step_writes_def, range_bytes_def,
    source_memory_write_ranges_def, FLOOKUP_DEF,
    taint_component_equality, EXTENSION] >> simp[SF CONJ_ss]
QED

Theorem dload_vars_match_bump[local]:
  dload_vars_match fs V G H tn un s t ==>
  dload_vars_match fs V (DRESTRICT G (COMPL {p;n}))
    (DRESTRICT H (COMPL {p;n}))
    (tn with t_var := DRESTRICT tn.t_var (COMPL {p;n}))
    (un with t_var := DRESTRICT un.t_var (COMPL {p;n}))
    (update_var n z (update_var p b s))
    (update_var n z (update_var p b t))
Proof
  strip_tac >> simp[dload_vars_match_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `v = n`
  >- gvs[lookup_var_def, update_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       dload_value_word_def, op_taint_def, word_agree_except_def] >>
  Cases_on `v = p`
  >- gvs[lookup_var_def, update_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       dload_value_word_def, op_taint_def, word_agree_except_def] >>
  qpat_x_assum `dload_vars_match _ _ _ _ _ _ _ _` mp_tac >>
  simp[dload_vars_match_def] >> disch_then (qspec_then `v` mp_tac) >>
  simp[lookup_var_def, update_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE, op_taint_def] >>
  strip_tac >> gvs[]
QED

Theorem dload_boundary_core_bump:
  i.inst_opcode = BUMP /\
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
    s' = s with vs_vars := s'.vs_vars /\
    t' = t with vs_vars := t'.vs_vars
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `dload_vars_match fs V G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `!op. MEM op i.inst_operands ==> eval_operand op s = eval_operand op t` by
    (rpt strip_tac >>
     `op_prov G op = NONE /\ op_taint tn op = {}` by
       (drule_all bump_operand_clean >> simp[]) >>
     `!v. op = Var v ==> v IN V` by metis_tac[] >>
     `eval_operand op s = NONE <=> eval_operand op t = NONE` by
       (drule eval_operand_definedness >>
        disch_then (qspec_then `op` mp_tac) >>
        (impl_tac >- metis_tac[]) >> simp[]) >>
     drule_all scalar_operand_equal >> simp[]) >>
  drule_all bump_step_transport >>
  disch_then (qspec_then `Cs` strip_assume_tac) >> gnvs[] >>
  conj_tac >- (rpt strip_tac >>
    irule update_var_definedness >> qexists `U` >> simp[] >>
    rpt strip_tac >> irule update_var_definedness >> qexists `U` >> simp[]) >>
  drule_all bump_ghost_updates >> strip_tac >>
  `step_prov PH H i (update_var n (word_add b z) (update_var p b t)) =
      DRESTRICT H (COMPL {p;n}) /\
   step_taint i t (update_var n (word_add b z) (update_var p b t)) un =
      un with t_var := DRESTRICT un.t_var (COMPL {p;n})` by
    (irule bump_ghost_updates >> simp[]) >>
  simp[] >>
  `dload_vars_match fs V (DRESTRICT G (COMPL {p;n}))
    (DRESTRICT H (COMPL {p;n}))
    (tn with t_var := DRESTRICT tn.t_var (COMPL {p;n}))
    (un with t_var := DRESTRICT un.t_var (COMPL {p;n}))
    (s with <|vs_vars := (update_var n (word_add b z) (update_var p b s)).vs_vars;
               vs_inst_idx := s.vs_inst_idx|>)
    (t with <|vs_vars := (update_var n (word_add b z) (update_var p b t)).vs_vars;
               vs_inst_idx := t.vs_inst_idx|>)` by
      (simp[update_var_def] >>
       irule (SRULE[update_var_def] dload_vars_match_bump) >> simp[]) >>
  simp[update_var_def] >>
  drule_all dload_boundary_core_var_index_update >> simp[update_var_def]
QED

Theorem dload_boundary_core_bump_index:
  i.inst_opcode = BUMP /\
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
    s' = s with vs_vars := s'.vs_vars /\
    t' = t with vs_vars := t'.vs_vars
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all dload_boundary_core_bump >>
  disch_then (qspec_then `Cs` strip_assume_tac) >>
  qexists `s'` >> simp[lookup_var_def] >>
  conj_tac >- gvs[lookup_var_def] >>
  irule dload_boundary_core_index_update >> simp[]
QED
