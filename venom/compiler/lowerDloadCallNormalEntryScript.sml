Theory lowerDloadCallNormalEntry
Ancestors
  lowerDloadCallNormalSetup lowerDloadNormalEntry lowerDloadOwnership
  ptrDiscipline contextCodegenRel venomExecSemantics venomState list
  o1ContractLowerDload lowerDloadSourceInterface venomInst venomInstProps unitShapeDefs

Theorem ld_entry_prov_no_previous:
  s.vs_prev_bb = NONE /\ enters_block fn s s1 ==>
  ld_entry_prov fn s AG = AG
Proof
  simp[enters_block_def, ld_entry_prov_def] >> rpt strip_tac >>
  Cases_on `bb.bb_instructions` >>
  gvs[eval_phis_def, ld_phis_prov_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  gvs[eval_one_phi_def, AllCaseEqs()]
QED

Theorem ld_entry_taint_no_previous:
  s.vs_prev_bb = NONE /\ enters_block fn s s1 ==>
  entry_taint_vars fn s tn = tn
Proof
  simp[enters_block_def, entry_taint_vars_def] >> rpt strip_tac >>
  Cases_on `bb.bb_instructions` >>
  gvs[eval_phis_def, phis_taint_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  gvs[eval_one_phi_def, AllCaseEqs()]
QED

Theorem ld_call_setup_controls[local]:
  lower_dload_function_supply a child = (callee,b) /\
  setup_callee child xs s = SOME ss /\ setup_callee callee ys t = SOME cs ==>
  ss.vs_current_bb = cs.vs_current_bb /\
  ss.vs_prev_bb = NONE /\ cs.vs_prev_bb = NONE
Proof
  strip_tac >> drule lower_dload_function_supply_labels >>
  qpat_x_assum `setup_callee child xs s = _` mp_tac >>
  qpat_x_assum `setup_callee callee ys t = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[setup_callee_def, fn_entry_label_def, entry_block_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem ld_call_normal_entry_backward:
  lower_dload_function_supply a child = (callee,b) /\
  opaque_use_ok caller /\ MEM ci (fn_insts caller) /\
  ci.inst_opcode = INVOKE /\ decode_invoke ci = SOME (nm,ops) /\
  taint_ok caller tn ci s /\
  V = set (fn_ir_vars caller) /\ U = {v | v IN V /\ ~retpc_var caller v} /\
  ld_normal_data CS caller V U lo E L H AP BP AG BH tn un s t
    astk live keys d A suspended gstk f /\
  sf = <|lf_fn := caller; lf_inst := ci; lf_state := s;
          lf_params := AP; lf_prov := AG; lf_tvar := tn.t_var; lf_local := L|> /\
  tf = <|lf_fn := target_caller; lf_inst := ci; lf_state := t;
          lf_params := BP; lf_prov := BH; lf_tvar := un.t_var; lf_local := H|> /\
  FINITE child_keys /\
  eval_operands ops t = SOME args /\ setup_callee callee args t = SOME cs /\
  enters_block callee cs ct ==>
  ?sargs ss ss1.
    eval_operands ops s = SOME sargs /\ setup_callee child sargs s = SOME ss /\
    enters_block child ss ss1 /\
    ld_normal_data CS child (set (fn_ir_vars child))
      {v | v IN set (fn_ir_vars child) /\ ~retpc_var child v}
      lo E FEMPTY FEMPTY (MAP (ld_op_prov AG) ops) (MAP (ld_op_prov BH) ops)
      FEMPTY FEMPTY (tn with t_var := FEMPTY) (un with t_var := FEMPTY)
      ss1 ct (sf::astk) live child_keys (32 * SUM (MAP CARD (A::suspended)))
      {} (A::suspended) (tf::gstk) t.vs_alloca_next /\
    ss1.vs_inst_idx = ct.vs_inst_idx /\
    ss1.vs_current_bb = ct.vs_current_bb /\ ss1.vs_prev_bb = ct.vs_prev_bb /\
    ss1 = ss with <|vs_vars := ss1.vs_vars; vs_inst_idx := ss1.vs_inst_idx|> /\
    ct = cs with <|vs_vars := ct.vs_vars; vs_inst_idx := ct.vs_inst_idx|>
Proof
  strip_tac >> drule_all ld_call_normal_setup_backward >>
  disch_then (qspec_then `set (fn_ir_vars child)` strip_assume_tac) >>
  drule_all ld_call_setup_controls >> strip_tac >>
  `!bb i v. MEM bb child.fn_blocks /\ MEM i bb.bb_instructions /\
    MEM (Var v) i.inst_operands ==> v IN set (fn_ir_vars child)` by
    (rpt strip_tac >> irule ld_original_operand_support >>
     qexists_tac `i` >> simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
     qexists_tac `bb` >> simp[]) >>
  `ss.vs_prev_bb = cs.vs_prev_bb` by simp[] >>
  qpat_assum `ld_normal_data CS child _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac ld_normal_data_entry_backward) >>
  disch_then (qspecl_then [`ct`,`callee`,`b`,`a`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `ld_entry_prov child ss FEMPTY = FEMPTY /\
   ld_entry_prov callee cs FEMPTY = FEMPTY /\
   entry_taint_vars child ss (tn with t_var := FEMPTY) = (tn with t_var := FEMPTY) /\
   entry_taint_vars callee cs (un with t_var := FEMPTY) = (un with t_var := FEMPTY)` by
    metis_tac[ld_entry_prov_no_previous, ld_entry_taint_no_previous] >>
  qexistsl_tac [`sargs`,`ss`,`s1`] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qpat_x_assum `s1 = ss with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
     qpat_x_assum `ct = cs with <|vs_vars := _; vs_inst_idx := _|>` kall_tac >>
     qpat_x_assum `ld_normal_data CS child _ _ _ _ _ _ _ _ _ _ _ _ s1 _ _ _ _ _ _ _ _ _`
       mp_tac >> simp[])]
QED
