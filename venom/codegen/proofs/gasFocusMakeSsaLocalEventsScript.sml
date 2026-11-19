(* Semantic observations at MakeSSA's concrete paired instruction positions. *)
Theory gasFocusMakeSsaLocalEvents
Ancestors
  o1ContractMakeSsaSrc makeSsaCurrentLockstep makeSsaCurrentLockstepShape
  makeSsaCurrentCopyPrefixRuntime gasEvents gasEventsFuel
  venomExecSemantics venomState venomInst list rich_list arithmetic

Theorem make_ssa_paired_gas_site:
  make_ssa_input_ok fn /\ fn_inst_wf fn /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\
  ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  make_ssa_current_fn s fn = (fn',s') /\
  lookup_block l fn.fn_blocks = SOME bb /\
  lookup_block l fn'.fn_blocks = SOME bb' /\
  phi_prefix_length bb.bb_instructions <= k /\
  k < LENGTH bb.bb_instructions /\
  i = EL k bb.bb_instructions /\
  i' = EL (make_ssa_pos fn fn' l k) bb'.bb_instructions /\
  i.inst_opcode = GAS ==>
  gas_events_step fuel' C' fn'.fn_name i' st' =
  gas_events_step fuel C fn.fn_name i st
Proof
  strip_tac >>
  drule_all make_ssa_current_fn_block_shape >> strip_tac >>
  `fn'.fn_name = fn.fn_name` by
    (drule makeSsaCurrentPropsTheory.make_ssa_current_fn_metadata >>
     simp[fn_identity_metadata_eq_def]) >>
  gvs[make_ssa_pos_def, gas_events_step_def]
QED

Theorem make_ssa_copy_prefix_gas_events:
  !xs st post rest.
    current_prefix_steps fuel C xs st post /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE) xs /\
    DROP st.vs_inst_idx bb.bb_instructions = xs ++ rest ==>
    gas_events_block fuel C owner bb st = gas_events_block fuel C owner bb post
Proof
  Induct >> simp[current_prefix_steps_def] >> rpt strip_tac >>
  `st.vs_inst_idx < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _`
       (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  `get_instruction bb st.vs_inst_idx = SOME h` by
    (simp[get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _`
       (mp_tac o AP_TERM ``HD : instruction list -> instruction``) >>
     simp[HD_DROP]) >>
  drule_all gas_events_block_nonterminator >>
  disch_then (qspec_then `owner` mp_tac) >>
  simp[gas_events_step_def] >> disch_then SUBST1_TAC >>
  first_x_assum irule >> simp[] >> qexists `rest` >>
  qpat_x_assum `DROP _ _ = _`
    (mp_tac o AP_TERM ``DROP 1 : instruction list -> instruction list``) >>
  simp[DROP_DROP_T, ADD1, ADD_COMM]
QED
