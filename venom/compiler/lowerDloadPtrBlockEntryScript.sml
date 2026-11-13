Theory lowerDloadPtrBlockEntry
Ancestors
  lowerDloadPtrAggregate lowerDloadPtrPhi lowerDloadPtrRel lowerDloadPtrCall venomExecProofs
  venomState venomInst venomExecSemantics lowerDloadDefs contextCodegenRel
  ptrDiscipline unitShapeDefs list finite_map execEquivParamBase lowerDloadPtrStatic

Theorem dload_table_stack_var_index_update[local]:
  dload_table_stack fs (s::ss) (t::ts) ==>
  dload_table_stack fs
    ((s with <|vs_vars := sv; vs_inst_idx := si|>)::ss)
    ((t with <|vs_vars := tv; vs_inst_idx := ti|>)::ts)
Proof
  simp[dload_table_stack_def] >> strip_tac >> gen_tac >>
  Cases_on `k`
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  first_x_assum (qspec_then `SUC n` mp_tac) >> simp[]
QED

Theorem dload_environment_var_index_update[local]:
  dload_equal_environment s t ==>
  dload_equal_environment
    (s with <|vs_vars := sv; vs_inst_idx := si|>)
    (t with <|vs_vars := tv; vs_inst_idx := ti|>)
Proof
  simp[dload_equal_environment_def, venom_state_component_equality]
QED

Theorem dload_boundary_core_var_index_update:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  dload_vars_match fs V G' H'
    (tn with t_var := tv) (un with t_var := uv)
    (s with <|vs_vars := sv; vs_inst_idx := si|>)
    (t with <|vs_vars := tvs; vs_inst_idx := ti|>) ==>
  dload_boundary_core lo fs V Ws PG PH G' H'
    (tn with t_var := tv) (un with t_var := uv)
    (s with <|vs_vars := sv; vs_inst_idx := si|>)
    (t with <|vs_vars := tvs; vs_inst_idx := ti|>) cs ds
Proof
  simp[dload_boundary_core_def, dload_memory_match_def,
    dload_shared_store_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[dload_table_stack_var_index_update, dload_environment_var_index_update]
QED

Theorem dload_boundary_core_phis_tracked:
  (!i v lbl op w. MEM i xs /\ i.inst_opcode = PHI /\
    i.inst_outputs = [v] /\ v IN V /\ s.vs_prev_bb = SOME lbl /\
    resolve_phi lbl i.inst_operands = SOME op /\ op = Var w ==> w IN V) /\
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  eval_phis s xs = OK sp /\ eval_phis t xs = OK tp ==>
  dload_boundary_core lo fs V Ws PG PH
    (phis_prov s.vs_prev_bb G xs) (phis_prov t.vs_prev_bb H xs)
    (tn with t_var := phis_taint s.vs_prev_bb tn xs)
    (un with t_var := phis_taint t.vs_prev_bb un xs)
    (sp with vs_inst_idx := si) (tp with vs_inst_idx := ti) cs ds
Proof
  strip_tac >>
  `dload_vars_match fs V G H tn un s t` by
    metis_tac[dload_boundary_vars] >>
  `!i v lbl op w. MEM i (TAKE (phi_prefix_length xs) xs) /\
    i.inst_outputs = [v] /\ v IN V /\ s.vs_prev_bb = SOME lbl /\
    resolve_phi lbl i.inst_operands = SOME op /\ op = Var w ==> w IN V` by
    metis_tac[phi_prefix_member] >>
  `eval_phis s (TAKE (phi_prefix_length xs) xs) = OK sp /\
   eval_phis t (TAKE (phi_prefix_length xs) xs) = OK tp` by
    simp[phi_prefix_computations] >>
  drule_all dload_vars_match_phis >> simp[phi_prefix_computations] >> strip_tac >>
  `sp = s with vs_vars := sp.vs_vars` by
    metis_tac[eval_phis_only_updates_vs_vars] >>
  `tp = t with vs_vars := tp.vs_vars` by
    metis_tac[eval_phis_only_updates_vs_vars] >>
  qpat_x_assum `dload_vars_match _ _ _ _ _ _ sp tp` mp_tac >>
  simp[dload_vars_match_def, lookup_var_def] >> strip_tac >>
  qpat_assum `sp = _` (fn th => once_rewrite_tac[th]) >>
  qpat_assum `tp = _` (fn th => once_rewrite_tac[th]) >> simp[] >>
  irule dload_boundary_core_var_index_update >>
  conj_tac >- simp[dload_vars_match_def, lookup_var_def] >>
  qexistsl [`G`,`H`] >> simp[]
QED

Theorem dload_boundary_core_phis:
  (!i. MEM i xs ==> MEM i (fn_insts f)) /\
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  eval_phis s xs = OK sp /\ eval_phis t xs = OK tp ==>
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
    (phis_prov s.vs_prev_bb G xs) (phis_prov t.vs_prev_bb H xs)
    (tn with t_var := phis_taint s.vs_prev_bb tn xs)
    (un with t_var := phis_taint t.vs_prev_bb un xs)
    (sp with vs_inst_idx := si) (tp with vs_inst_idx := ti) cs ds
Proof
  strip_tac >> irule dload_boundary_core_phis_tracked >>
  simp[] >> metis_tac[retpc_phi_input_tracked, resolve_phi_MEM, MEM]
QED

Theorem dload_original_phi_input_tracked:
  MEM i (fn_insts f) /\ i.inst_opcode = PHI /\ i.inst_outputs = [v] /\
  v IN (set (fn_ir_vars f) DIFF {a | retpc_var f a}) /\
  resolve_phi lbl i.inst_operands = SOME (Var w) ==>
  w IN (set (fn_ir_vars f) DIFF {a | retpc_var f a})
Proof
  simp[] >> metis_tac[fn_ir_vars_operand, retpc_phi_input_tracked, resolve_phi_MEM, MEM]
QED

Theorem lower_dload_function_supply_enters_boundary_tracked:
  lower_dload_function_supply q f = (g,q') /\
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds /\
  s.vs_current_bb = t.vs_current_bb /\
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  (!i v lbl op w. MEM i (fn_insts f) /\ i.inst_opcode = PHI /\
    i.inst_outputs = [v] /\ v IN V /\
    resolve_phi lbl i.inst_operands = SOME op /\ op = Var w ==> w IN V) /\
  (!i v. MEM i (fn_insts f) /\ MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  enters_block g t t' ==>
  ?b s'. lookup_block s.vs_current_bb f.fn_blocks = SOME b /\
    enters_block f s s' /\ s'.vs_inst_idx = t'.vs_inst_idx /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core lo fs V Ws PG PH
      (phis_prov s.vs_prev_bb G b.bb_instructions)
      (phis_prov t.vs_prev_bb H b.bb_instructions)
      (tn with t_var := phis_taint s.vs_prev_bb tn b.bb_instructions)
      (un with t_var := phis_taint t.vs_prev_bb un b.bb_instructions)
      s' t' cs ds
Proof
  simp[lower_dload_function_supply_def, enters_block_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule_all lower_dload_blocks_supply_lookup >> strip_tac >>
  `MEM b f.fn_blocks` by metis_tac[lookup_block_def, FIND_MEM] >>
  `!i. MEM i b.bb_instructions ==> MEM i (fn_insts f)` by
    (simp[fn_insts_def] >> metis_tac[MEM_fn_insts_blocks]) >>
  `?sp. eval_phis s b.bb_instructions = OK sp /\
    (!v. v IN U ==> (lookup_var v sp = NONE <=> lookup_var v s_phi = NONE))` by
    (irule lower_dload_block_supply_phi_definedness >>
     conj_tac >- metis_tac[] >>
     qexistsl [`bb`,`u`,`u'`,`t`] >> simp[]) >>
  drule lower_dload_block_supply_phi_exact >> strip_tac >>
  `eval_phis t b.bb_instructions = OK s_phi` by metis_tac[] >>
  `!i v lbl op w. MEM i b.bb_instructions /\ i.inst_opcode = PHI /\
    i.inst_outputs = [v] /\ v IN V /\ s.vs_prev_bb = SOME lbl /\
    resolve_phi lbl i.inst_operands = SOME op /\ op = Var w ==> w IN V` by
    metis_tac[] >>
  drule_all dload_boundary_core_phis_tracked >>
  disch_then (qspecl_then [`phi_prefix_length b.bb_instructions`,
    `phi_prefix_length b.bb_instructions`] assume_tac) >>
  qexistsl [`b`,`sp with vs_inst_idx := phi_prefix_length b.bb_instructions`] >>
  gvs[lookup_var_def]
QED

Theorem lower_dload_function_supply_enters_boundary:
  lower_dload_function_supply q f = (g,q') /\
  dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH G H tn un s t cs ds /\
  s.vs_current_bb = t.vs_current_bb /\
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_labels = t.vs_labels /\
  (!i v. MEM i (fn_insts f) /\ MEM (Var v) i.inst_operands ==> v IN U) /\
  (!v. v IN U ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  enters_block g t t' ==>
  ?b s'. lookup_block s.vs_current_bb f.fn_blocks = SOME b /\
    enters_block f s s' /\ s'.vs_inst_idx = t'.vs_inst_idx /\
    (!v. v IN U ==> (lookup_var v s' = NONE <=> lookup_var v t' = NONE)) /\
    dload_boundary_core lo fs {v | ~retpc_var f v} Ws PG PH
      (phis_prov s.vs_prev_bb G b.bb_instructions)
      (phis_prov t.vs_prev_bb H b.bb_instructions)
      (tn with t_var := phis_taint s.vs_prev_bb tn b.bb_instructions)
      (un with t_var := phis_taint t.vs_prev_bb un b.bb_instructions)
      s' t' cs ds
Proof
  strip_tac >> irule lower_dload_function_supply_enters_boundary_tracked >>
  simp[] >> metis_tac[retpc_phi_input_tracked, resolve_phi_MEM, MEM]
QED

Theorem dload_boundary_core_index_update:
  dload_boundary_core lo fs V Ws PG PH G H tn un s t cs ds ==>
  dload_boundary_core lo fs V Ws PG PH G H tn un
    (s with vs_inst_idx := si) (t with vs_inst_idx := ti) cs ds
Proof
  strip_tac >>
  `dload_vars_match fs V G H
    (tn with t_var := tn.t_var) (un with t_var := un.t_var)
    (s with <|vs_vars := s.vs_vars; vs_inst_idx := si|>)
    (t with <|vs_vars := t.vs_vars; vs_inst_idx := ti|>)` by
    (drule dload_boundary_vars >> simp[dload_vars_match_def, lookup_var_def]) >>
  `s with <|vs_vars := s.vs_vars; vs_inst_idx := si|> = s with vs_inst_idx := si` by
    simp[venom_state_component_equality] >>
  `t with <|vs_vars := t.vs_vars; vs_inst_idx := ti|> = t with vs_inst_idx := ti` by
    simp[venom_state_component_equality] >>
  drule_all dload_boundary_core_var_index_update >> simp[]
QED

