Theory makeSsaCurrentRetainedValue
Ancestors makeSsaCurrentRetainedRead makeSsaCurrentSingletonSelectors
  makeSsaCurrentPhiOrigins venomWf venomInst venomExecSemantics venomState venomExecProps list

Theorem current_resolve_phi_pair_member:
  !ops p v. phi_well_formed ops /\ resolve_phi p ops = SOME (Var v) ==>
    MEM (p,v) (phi_pairs ops)
Proof
  recInduct phi_well_formed_ind >>
  simp[phi_well_formed_def, resolve_phi_def, phi_pairs_def] >>
  rpt strip_tac >> Cases_on `lbl = p` >> gvs[] >> metis_tac[]
QED

Theorem current_eval_one_phi_selected:
  phi.inst_opcode = PHI /\ inst_wf phi /\ st.vs_prev_bb = SOME p /\
  eval_one_phi st phi = SOME (dst,value) ==>
  ?v. phi.inst_outputs = [dst] /\
    resolve_phi p phi.inst_operands = SOME (Var v) /\
    MEM (p,v) (phi_pairs phi.inst_operands) /\ lookup_var v st = SOME value
Proof
  strip_tac >>
  `LENGTH phi.inst_outputs = 1 /\ phi_well_formed phi.inst_operands`
    by gvs[inst_wf_def] >>
  Cases_on `phi.inst_outputs` >> fs[] >>
  Cases_on `t` >> fs[] >>
  gvs[eval_one_phi_def, AllCaseEqs()] >>
  drule_all current_phi_resolve_var >> strip_tac >>
  gvs[eval_operand_def] >>
  metis_tac[current_resolve_phi_pair_member]
QED

Theorem current_certificate_retained_eval:
  current_structural_certificate s fn fn' s' A H events /\
  wf_function fn /\ fn_inst_wf fn /\ all_reachable fn /\ entry_block fn = SOME eb /\
  first_block_no_preds fn /\ blocks_have_leading_phi fn.fn_blocks /\
  fn_defs_reach_uses fn /\ fn_phi_operands_single_def fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\ fn_phis_non_degenerate fn /\
  lookup_block h fn.fn_blocks = SOME old /\ old.bb_instructions = phis ++ tail /\
  EVERY (\j. j.inst_opcode = PHI) phis /\
  (tail = [] \/ (HD tail).inst_opcode <> PHI) /\ i < LENGTH phis /\
  (EL i old.bb_instructions).inst_opcode = PHI /\
  MEM ev events /\ current_event_label ev = p /\ fn_cfg_edge fn p h /\
  lookup_block p fn.fn_blocks = SOME pred /\
  st.vs_prev_bb = SOME p /\ st'.vs_prev_bb = SOME p /\
  current_singleton_agree (current_instruction_singleton_table fn H) st st' /\
  eval_one_phi st (EL i old.bb_instructions) = SOME (dst,value) ==>
  ?out r batch name. lookup_block h fn'.fn_blocks = SOME out /\
    r < batch /\ batch <= LENGTH out.bb_instructions /\
    EVERY (\j. j.inst_opcode = PHI) (TAKE batch out.bb_instructions) /\
    (EL r out.bb_instructions).inst_opcode = PHI /\
    (EL r out.bb_instructions).inst_outputs = [name] /\
    current_token_name H (CurrentOriginal h i 0) = SOME name /\
    eval_one_phi st' (EL r out.bb_instructions) = SOME (name,value)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM old fn.fn_blocks /\ old.bb_label = h` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `i < LENGTH old.bb_instructions` by simp[] >>
  `MEM (EL i old.bb_instructions) old.bb_instructions` by metis_tac[EL_MEM] >>
  `inst_wf (EL i old.bb_instructions)` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  drule_all current_eval_one_phi_selected >> strip_tac >>
  `lookup_var v st = lookup_var (latest_current_name (current_event_exit_rs ev) v) st'` by
    (irule current_certificate_phi_operand_agree >> metis_tac[]) >>
  drule_all current_certificate_retained_leading_read >> strip_tac >>
  qexistsl_tac [`out`, `r`, `batch`, `name`] >>
  asm_rewrite_tac[] >> simp[eval_one_phi_def, eval_operand_def] >> gvs[]
QED
