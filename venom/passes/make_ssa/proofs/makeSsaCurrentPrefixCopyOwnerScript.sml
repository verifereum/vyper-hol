Theory makeSsaCurrentPrefixCopyOwner
Ancestors
  makeSsaCurrentCarrierOwner makeSsaCurrentHistoryOwner makeSsaCurrentWfSsa
  makeSsaDefs venomWf venomInst venomExecProps list rich_list

Theorem current_prefix_inserted_copy_owner:
  current_wf_phi_context s fn renamed s' A H events /\
  entry_block fn = SOME eb /\
  lookup_block h fn.fn_blocks = SOME old /\
  lookup_block h renamed = SOME new /\
  current_wf_inserted_phi_at A renamed h q v /\
  (EL q new.bb_instructions).inst_outputs = [dst] /\
  simplify_current_phi (EL q new.bb_instructions) =
    (EL q new.bb_instructions) with
      <|inst_opcode := ASSIGN; inst_operands := [Var src]|> ==>
  (?td. MEM (td,v,dst) H) /\ (?ts. MEM (ts,v,src) H)
Proof
  strip_tac >>
  `current_wf_precleanup_certificate s fn renamed s' A H events` by
    fs[current_wf_phi_context_def] >>
  conj_tac
  >- (drule_all current_wf_inserted_phi_output >> strip_tac >> gvs[] >>
      qexists `CurrentInserted v h` >>
      irule current_history_owned_name_member >>
      simp[current_wf_token_owner_def] >> metis_tac[]) >>
  Cases_on `!di. MEM di old.bb_instructions /\ di.inst_opcode = PHI ==>
    ~MEM v di.inst_outputs`
  >- metis_tac[current_carrier_copy_owned_name] >>
  gvs[NOT_FORALL_THM] >>
  `?k. k < LENGTH old.bb_instructions /\ EL k old.bb_instructions = di` by
    metis_tac[MEM_EL] >>
  `fn_inst_wf fn` by fs[current_wf_phi_context_def] >>
  `inst_wf di` by metis_tac[fn_inst_wf_def, lookup_block_MEM] >>
  `di.inst_outputs = [v]` by
    (qpat_x_assum `inst_wf di` mp_tac >>
     simp[inst_wf_def, LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[]) >>
  qpat_x_assum `EL k old.bb_instructions = di` (SUBST_ALL_TAC o SYM) >>
  drule_all current_wf_exceptional_original_source >> strip_tac >>
  drule_all current_wf_inserted_phi_slots >> strip_tac >>
  drule_all current_wf_exceptional_inserted_pair_values >> strip_tac >>
  `(EL q new.bb_instructions).inst_opcode = PHI` by
    (fs[current_wf_inserted_phi_at_def] >> metis_tac[optionTheory.SOME_11]) >>
  drule_all current_carrier_copy_source_slot >> strip_tac >>
  `src = n` by metis_tac[] >>
  `current_wf_token_owner fn (CurrentOriginal h k 0) v` by
    (simp[current_wf_token_owner_def] >> qexists `old` >> simp[]) >>
  qexists `CurrentOriginal h k 0` >>
  irule current_history_owned_name_member >> simp[] >> metis_tac[]
QED
