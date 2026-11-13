Theory loadElimAssignSemantics
Ancestors
  loadElimOccurrence overflowElimHelpers2 venomExecSemantics venomExecProps
  venomState finite_map list

Theorem le_step_assign_result:
  di.inst_opcode = ASSIGN /\ di.inst_operands = [src] /\
  di.inst_outputs = [v] /\ step_inst fuel C di u = OK t ==>
  ?w. eval_operand src u = SOME w /\ t = update_var v w u
Proof
  strip_tac >>
  `step_inst_base di u = OK t` by
    gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base di u = OK t` mp_tac >>
  simp[Once step_inst_base_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem le_step_assign_lookup:
  inst_wf di /\ di.inst_opcode = ASSIGN /\ di.inst_operands = [src] /\
  di.inst_outputs = [v] /\ step_inst fuel C di u = OK t ==>
  lookup_var v t = eval_operand src u
Proof
  strip_tac >> drule_all le_step_assign_result >> strip_tac >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem le_step_assign_lookup_post:
  inst_wf di /\ di.inst_opcode = ASSIGN /\ di.inst_operands = [src] /\
  di.inst_outputs = [v] /\ step_inst fuel C di u = OK t /\
  (!w. src = Var w ==> w <> v) ==>
  lookup_var v t = eval_operand src t
Proof
  strip_tac >> drule_all le_step_assign_result >> strip_tac >>
  Cases_on `src` >> gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem le_occ_valid_labels:
  le_occ_valid C fn e ==>
  (le_occ_after e).vs_labels = (le_occ_pre e).vs_labels
Proof
  Cases_on `e` >>
  simp[le_occ_valid_def, le_occ_after_def, le_occ_pre_def] >> strip_tac
  >- (drule step_inst_preserves_labels_always >> simp[COND_RAND]) >>
  metis_tac[eval_phis_preserves_labels]
QED

Theorem le_occ_chain_labels:
  !es s t. le_occ_chain s es t /\ EVERY (le_occ_valid C fn) es ==>
  t.vs_labels = s.vs_labels
Proof
  Induct >> simp[le_occ_chain_def] >> rpt strip_tac >>
  first_x_assum drule_all >>
  drule le_occ_valid_labels >> simp[]
QED

Theorem le_occ_prefix_suffix_label:
  le_occ_prefix C fn s0 (pre ++ e::suffix) i s ==>
  eval_operand (Label l) (le_occ_post e) = eval_operand (Label l) s
Proof
  strip_tac >> drule le_occ_prefix_chain >>
  simp[le_occ_chain_append, le_occ_chain_def] >> strip_tac >>
  drule le_occ_prefix_valid >> simp[] >> strip_tac >>
  drule_all le_occ_chain_labels >>
  Cases_on `e` >>
  simp[le_occ_after_def, le_occ_post_def, eval_operand_def, COND_RAND]
QED
