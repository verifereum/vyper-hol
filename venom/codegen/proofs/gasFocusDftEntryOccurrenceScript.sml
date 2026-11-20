Theory gasFocusDftEntryOccurrence
Ancestors
  gasFocusInitialNativeRoot o1DftStageSsa dftContractGas dftRunRel
  dftDefs o1PassContract venomPassSchedule venomWf venomExecProofs
  contextCodegenRel venomInst venomState list option

(* The selected target block determines the native head, before any joint step. *)
Theorem focus_dft_entry_occurrence:
  !tf. tf = dft_fn sf ==>
  !E. E = root_base with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|> ==>
  !u. u = sp with vs_inst_idx := phi_prefix_length bt.bb_instructions ==>
    ctx_pass_stage rp (CFP_Simple VP_DFT) view C7 C8 /\
    o1_pre 7 C7 C8 /\ o1_ctx_shape C7 /\ o1_ctx_shape C8 /\
    EVERY wf_ssa C7.ctx_functions /\ C7.ctx_entry = SOME nm /\
    lookup_function nm C7.ctx_functions = SOME sf /\ fn_entry_label sf = SOME lbl /\
    lookup_block lbl tf.fn_blocks = SOME bt /\ bt.bb_label = lbl /\
    eval_phis E bt.bb_instructions = OK sp /\
    get_instruction bt u.vs_inst_idx = SOME inst /\ 0 < N ==>
    !q. q = JointConfig [] [] FEMPTY entry_taint tf inst u [] FEMPTY []
              [OriginInitial E; OriginObserve (OriginSnapshot tf [] FEMPTY FEMPTY inst u)] ==>
    !T. T = dftGasFromListTraceDefs$trace_blocks [] 0 N C8 tf E ==>
      C8.ctx_entry = SOME nm /\ lookup_function nm C8.ctx_functions = SOME tf /\
      fn_entry_label tf = SOME lbl /\ dft_fn_rel sf tf /\
      enters_block tf E u /\ active_inst tf inst u /\
      joint_initial root_base C8 q /\ joint_trace root_base C8 q [] [] q /\
      dftGasFromListTraceDefs$trace_context N C8 root_base = T /\
      (?tail. T = (([],1,inst.inst_id),tf,inst,u)::tail) /\
      0 < LENGTH T /\ EL 0 T = (([],1,inst.inst_id),tf,inst,u) /\
      TAKE 0 T = [] /\ LENGTH (TAKE 0 T) = 0 /\
      dftGasFromListTraceDefs$trace_gas (TAKE 0 T) = []
Proof
  CONV_TAC (TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV)) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  drule_all dft_stage_fn_rel >> strip_tac >>
  `C8.ctx_entry = SOME nm` by simp[] >>
  `lookup_function nm C8.ctx_functions = SOME (dft_fn sf)` by
    (drule dft_ctx_functions_map >> simp[lookup_function_map]) >>
  `dft_fn_rel sf (dft_fn sf)` by
    (drule dft_fn_rel_lookup_function >>
     disch_then (qspec_then `nm` mp_tac) >> simp[OPTREL_def]) >>
  `fn_entry_label (dft_fn sf) = SOME lbl` by
    (drule dft_fn_rel_entry_label >> simp[]) >>
  `wf_function (dft_fn sf)` by
    (drule o1_ctx_shape_wf_functions >>
     simp[EVERY_MEM] >> metis_tac[lookup_function_MEM]) >>
  qmatch_asmsub_abbrev_tac `eval_phis E _ = OK sp` >>
  qmatch_asmsub_abbrev_tac `get_instruction bt u.vs_inst_idx = SOME inst` >>
  `E.vs_prev_bb = NONE /\ E.vs_current_bb = lbl` by simp[Abbr `E`] >>
  `enters_block (dft_fn sf) E u` by
    (simp[enters_block_def] >> qexistsl [`bt`, `sp`] >> simp[Abbr `u`]) >>
  `active_inst (dft_fn sf) inst u` by
    (`sp = E` by metis_tac[eval_phis_no_prev] >>
     `u.vs_current_bb = lbl` by simp[Abbr `u`] >>
     simp[active_inst_def] >> qexists `bt` >>
     gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[lookup_block_MEM]) >>
  `E = (root_base with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)` by
    simp[Abbr `E`] >>
  asm_rewrite_tac[] >>
  drule_all (CONV_RULE (TOP_DEPTH_CONV Unwind.UNWIND_FORALL_CONV) focus_initial_native_root) >>
  pop_assum (fn th => pure_rewrite_tac[LET_THM, th]) >>
  BETA_TAC >> disch_then ACCEPT_TAC
QED
