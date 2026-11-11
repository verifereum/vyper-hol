Theory makeSsaCurrentCarrierOwner
Ancestors
  makeSsaCurrentHistoryOwner makeSsaCurrentCleanupBoundary makeSsaCurrentDefs
  makeSsaCurrentWfSsa makeSsaCurrentCertificate makeSsaCurrentTreeTrace
  makeSsaCurrentAllocation
  makeSsaHelper venomInst list rich_list makeSsaRfAllocation
Theorem current_carrier_copy_source_slot:
  inst.inst_opcode = PHI /\ inst.inst_outputs = [out] /\
  inst.inst_operands = current_phi_slots slots /\
  simplify_current_phi inst =
    inst with <|inst_opcode := ASSIGN; inst_operands := [Var src]|> ==>
  ?p. MEM (p,src) slots /\ src <> out
Proof
  strip_tac >>
  ` (simplify_current_phi inst).inst_opcode = ASSIGN /\
    (simplify_current_phi inst).inst_operands = [Var src]` by simp[] >>
  qpat_x_assum `simplify_current_phi inst = _` kall_tac >>
  gvs[simplify_current_phi_def, simplify_current_phi_raw_def,
    current_phi_output_def, current_phi_slots_remove_self, current_phi_slots_values] >>
  qabbrev_tac `vals = MAP SND (FILTER (\slot. SND slot <> out) slots)` >>
  Cases_on `vals`
  >- (gvs[keep_current_phi_vars_def] >>
      BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  Cases_on `EVERY (\w. w = h) t`
  >- (gvs[keep_current_phi_vars_def] >>
      Cases_on `EVERY (\v. MEM v (inst_ir_vars inst))
        (inst_ir_vars (inst with <|inst_opcode := ASSIGN; inst_operands := [Var h]|>))` >>
      gvs[] >>
      rename1 `?p. MEM (p,carrier) slots /\ carrier <> out` >>
      `MEM carrier (MAP SND (FILTER (\slot. SND slot <> out) slots))` by simp[] >>
      fs[MEM_MAP, MEM_FILTER] >> metis_tac[pairTheory.PAIR, pairTheory.SND]) >>
  gvs[keep_current_phi_vars_def]
QED

Theorem current_carrier_copy_owned_name:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  (!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==>
        ~MEM v di.inst_outputs) /\
  current_wf_inserted_phi_at A renamed h q v /\
  (EL q new.bb_instructions).inst_outputs = [out] /\
  simplify_current_phi (EL q new.bb_instructions) =
    (EL q new.bb_instructions) with
      <|inst_opcode := ASSIGN; inst_operands := [Var src]|> ==>
  ?t. MEM (t,v,src) H
Proof
  strip_tac >>
  drule_all current_wf_inserted_phi_slots >> strip_tac >>
  `(EL q new.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_inserted_phi_at_def] >> metis_tac[optionTheory.SOME_11]) >>
  drule_all current_carrier_copy_source_slot >> strip_tac >>
  `?i. i < LENGTH pairs /\ EL i pairs = (p,src)` by
    metis_tac[MEM_EL] >>
  drule_all current_wf_inserted_phi_pair >> strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
   fn_phi_operands_single_def fn /\ all_reachable fn /\
   first_block_no_preds fn /\ first_block_no_phi fn` by
    fs[current_wf_phi_context_def] >>
  `?pred. lookup_block p fn.fn_blocks = SOME pred` by
    (fs[venomWfTheory.fn_cfg_edge_def] >>
     metis_tac[venomExecPropsTheory.MEM_lookup_block, venomWfTheory.wf_function_def,
       venomInstTheory.fn_labels_def]) >>
  `current_actual_inserted fn v h` by
    metis_tac[current_wf_inserted_phi_prefix] >>
  `current_demand fn v p (LENGTH pred.bb_instructions)` by
    metis_tac[current_wf_inserted_pred_demand] >>
  `current_wf_token_owner fn (current_event_exit_env ev v) v` by
    metis_tac[current_wf_precleanup_exit_owner] >>
  `!w. current_event_exit_env ev v <> CurrentDefault w` by
    metis_tac[current_wf_precleanup_exit_nondefault] >>
  qexists `current_event_exit_env ev v` >>
  irule current_history_owned_name_member >> metis_tac[]
QED

Theorem current_carrier_cut_token_owned_name:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\ MEM ev events /\
  lookup_block (current_event_label ev) fn.fn_blocks = SOME old /\
  A (current_event_label ev) = current_block_annotations old pre /\
  LENGTH (collect_phis old.bb_instructions) <= i /\
  i <= LENGTH old.bb_instructions /\
  current_source_cut A ev (LENGTH pre + i) rs E /\
  current_demand fn v (current_event_label ev) i /\
  current_token_name H (E v) = SOME n ==>
  MEM (E v,v,n) H
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events /\
   wf_function fn /\ fn_inst_wf fn /\ fn_defs_reach_uses fn /\
   fn_phi_operands_single_def fn /\ all_reachable fn /\
   first_block_no_preds fn /\ first_block_no_phi fn` by
    fs[current_wf_phi_context_def] >>
  drule current_wf_precleanup_structural >> strip_tac >>
  drule_all current_wf_certificate_static_entry >> strip_tac >>
  `current_wf_token_owner fn (current_event_entry_env ev v) v` by
    metis_tac[current_wf_inherited_token_owner] >>
  `current_wf_token_owner fn (E v) v` by
    metis_tac[current_wf_source_cut_owner] >>
  drule_all current_wf_certificate_actual_prefix >> strip_tac >>
  `LENGTH pre = LENGTH pre'` by
    ( `LENGTH (current_block_annotations old pre) =
       LENGTH (current_block_annotations old pre')` by metis_tac[] >>
      qpat_x_assum `LENGTH (current_block_annotations _ _) = _` mp_tac >>
      simp[current_block_annotations_def, current_inserted_annotations_def]) >>
  `E v <> CurrentDefault v` by
    (irule current_wf_demanded_source_cut_nondefault >> metis_tac[]) >>
  `!w. E v <> CurrentDefault w` by
    (Cases_on `E v` >> gvs[current_wf_token_owner_def]) >>
  irule current_history_owned_name_member >> metis_tac[]
QED

