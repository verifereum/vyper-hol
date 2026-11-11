Theory makeSsaCurrentEntryPrefix
Ancestors
  makeSsaCurrentLockstep o1MakeSsaCfg o1MakeSsaFormats
  venomWfProps analysisSimProofsBase
  o1PassLift o1PassContract venomWf cfgWf venomInst venomExecProofs venomExecSemantics list relation

Theorem current_target_entry_prefix_initial:
  make_ssa_current_fn s fn = (fn',s') /\ wf_function fn /\
  first_block_no_preds fn /\ first_block_no_phi fn /\ fn_entry_state fn st ==>
  ?bb. lookup_block st.vs_current_bb fn'.fn_blocks = SOME bb /\
    fn_entry_state fn' st /\ enters_block fn' st st /\
    eval_phis st bb.bb_instructions = OK st /\
    phi_prefix_length bb.bb_instructions = 0 /\
    strict_dom_vars_defined fn' st /\ fn_reachable fn' st.vs_current_bb /\
    st.vs_inst_idx <= LENGTH bb.bb_instructions /\
    (!j x. j < st.vs_inst_idx /\ j < LENGTH bb.bb_instructions /\
      MEM x (EL j bb.bb_instructions).inst_outputs ==> IS_SOME (lookup_var x st))
Proof
  strip_tac >>
  drule_all make_ssa_current_fn_first_block_no_phi >> strip_tac >>
  drule make_ssa_current_fn_entry_label >> strip_tac >>
  `fn_entry_state fn' st` by gvs[fn_entry_state_def] >>
  `?bb. lookup_block st.vs_current_bb fn'.fn_blocks = SOME bb /\
    EVERY (\i. i.inst_opcode <> PHI) bb.bb_instructions` by
    (gvs[fn_entry_state_def, fn_entry_label_def, entry_block_def,
         first_block_no_phi_def, AllCaseEqs()] >>
     Cases_on `fn'.fn_blocks` >> gvs[lookup_block_def, FIND_thm]) >>
  `st.vs_inst_idx = 0 /\ fn_entry_label fn' = SOME st.vs_current_bb` by
    fs[fn_entry_state_def] >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (Cases_on `bb.bb_instructions` >> gvs[phi_prefix_length_def]) >>
  `eval_phis st bb.bb_instructions = OK st` by
    metis_tac[phi_prefix_length_zero_eval_phis_ok] >>
  `enters_block fn' st st` by metis_tac[enters_block_no_phi] >>
  `strict_dom_vars_defined fn' st` by metis_tac[strict_dom_vars_defined_entry] >>
  `fn_reachable fn' st.vs_current_bb` by simp[fn_reachable_def] >>
  qexists `bb` >> asm_rewrite_tac[] >> simp[]
QED
