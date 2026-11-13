Theory fmpStageCoverBackLaterArity
Ancestors
  o1PassContract o1ContractMakeSsaSrcOpcodes singleUseExpansionDefs
  dftLifting dftDefs dftStructural callLayoutDefs venomInst list rich_list
  arithmetic finite_map cfgHelpers venomExecProps

Theorem make_ssa_current_fn_user_count:
  ALL_DISTINCT (fn_labels fn) /\ make_ssa_current_fn s fn = (fn',s') ==>
  LENGTH (fn_user_param_insts fn') = LENGTH (fn_user_param_insts fn)
Proof
  strip_tac >> drule_all make_ssa_current_fn_key >>
  Cases_on `fn.fn_blocks` >> Cases_on `fn'.fn_blocks` >>
  simp[block_key_def, fn_user_param_insts_def, fn_entry_insts_def,
       entry_block_def] >> strip_tac >>
  gvs[] >>
  `kept_opcode PARAM` by simp[kept_opcode_def] >>
  simp[kept_opcode_count]
QED

Theorem fmp_make_ssa_user_count:
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA) observed s fn out /\
  ALL_DISTINCT (fn_labels fn) ==>
  LENGTH (fn_user_param_insts fn) <=
  LENGTH (fn_user_param_insts out.fpo_function)
Proof
  rw[fn_pass_step_def] >>
  gvs[AllCaseEqs()] >>
  drule_all make_ssa_current_fn_user_count >> simp[]
QED

Theorem sue_insts_user_count[local]:
  !insts s outs s'. sue_expand_insts_supply dfg s insts = (outs,s') ==>
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) insts) <=
  LENGTH (FILTER (\i. i.inst_opcode = PARAM) outs)
Proof
  Induct >> simp[sue_expand_insts_supply_def] >> rpt gen_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  Cases_on `h.inst_opcode = PARAM` >> gvs[FILTER_APPEND_DISTRIB] >>
  gvs[sue_expand_inst_supply_def, sue_should_skip_def, is_param_opcode_def]
QED

Theorem sue_blocks_user_count[local]:
  !bbs s outs s'. sue_expand_blocks_supply dfg s bbs = (outs,s') ==>
  LENGTH (fn_user_param_insts (fn with fn_blocks := bbs)) <=
  LENGTH (fn_user_param_insts (fn with fn_blocks := outs))
Proof
  Cases >> simp[sue_expand_blocks_supply_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[sue_expand_block_supply_def, AllCaseEqs(), fn_user_param_insts_def,
      fn_entry_insts_def, entry_block_def] >>
  drule sue_insts_user_count >> simp[]
QED

Theorem sue_function_user_count:
  sue_expand_function_supply s fn = (fn',s') ==>
  LENGTH (fn_user_param_insts fn) <= LENGTH (fn_user_param_insts fn')
Proof
  simp[sue_expand_function_supply_def] >> strip_tac >>
  gvs[AllCaseEqs()] >> drule sue_blocks_user_count >>
  disch_then (qspec_then `fn` mp_tac) >> simp[]
QED

Theorem fmp_sue_user_count:
  fn_pass_step rpolicy (CFP_Simple VP_SingleUseExpansion) observed s fn out ==>
  LENGTH (fn_user_param_insts fn) <=
  LENGTH (fn_user_param_insts out.fpo_function)
Proof
  rw[fn_pass_step_def] >> gvs[AllCaseEqs()] >>
  drule sue_function_user_count >> simp[]
QED

Theorem dft_process_param_keys[local]:
  ALL_DISTINCT (MAP (\b. b.bb_label) st.dls_blocks) ==>
  MAP (\b. (b.bb_label, FILTER (\i. i.inst_opcode = PARAM) b.bb_instructions))
    (FST (dft_process_one cfg lr fn st lbl)).dls_blocks =
  MAP (\b. (b.bb_label, FILTER (\i. i.inst_opcode = PARAM) b.bb_instructions))
    st.dls_blocks
Proof
  strip_tac >> simp[dft_process_one_def] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  simp[MAP_MAP_o, MAP_EQ_f] >> rpt strip_tac >>
  Cases_on `b.bb_label = lbl` >> simp[] >>
  `lookup_block lbl st.dls_blocks = SOME b` by
    (irule venomExecPropsTheory.MEM_lookup_block >> simp[]) >>
  gvs[] >>
  `FILTER (\i. i.inst_opcode = PARAM)
    (FILTER (\i. is_pseudo i.inst_opcode) (dft_block (REVERSE order) b).bb_instructions) =
   FILTER (\i. i.inst_opcode = PARAM)
    (FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions)` by
    simp[dft_block_phis] >>
  gvs[FILTER_FILTER, SF CONJ_ss, is_pseudo_def, is_param_opcode_def,
      dft_block_def]
QED

Theorem dft_loop_param_keys[local]:
  ALL_DISTINCT (MAP (\b. b.bb_label) (FST trip).dls_blocks) ==>
  MAP (\b. (b.bb_label, FILTER (\i. i.inst_opcode = PARAM) b.bb_instructions))
    (FST (dft_loop_step cfg lr fn trip)).dls_blocks =
  MAP (\b. (b.bb_label, FILTER (\i. i.inst_opcode = PARAM) b.bb_instructions))
    (FST trip).dls_blocks
Proof
  PairCases_on `trip` >> simp[dft_loop_step_def] >> strip_tac >>
  Cases_on `trip2` >> simp[] >> Cases_on `trip1` >> simp[] >>
  pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[] >>
  drule dft_process_param_keys >>
  disch_then (qspecl_then [`lr`, `h`, `fn`, `cfg`] mp_tac) >> simp[]
QED

Theorem dft_funpow_param_keys[local]:
  !n trip. ALL_DISTINCT (MAP (\b. b.bb_label) (FST trip).dls_blocks) ==>
  MAP (\b. (b.bb_label, FILTER (\i. i.inst_opcode = PARAM) b.bb_instructions))
    (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks =
  MAP (\b. (b.bb_label, FILTER (\i. i.inst_opcode = PARAM) b.bb_instructions))
    (FST trip).dls_blocks
Proof
  Induct >> simp[arithmeticTheory.FUNPOW] >> rpt strip_tac >>
  drule dft_loop_param_keys >>
  disch_then (qspecl_then [`lr`, `fn`, `cfg`] assume_tac) >>
  `MAP (\b. b.bb_label) (FST (dft_loop_step cfg lr fn trip)).dls_blocks =
   MAP (\b. b.bb_label) (FST trip).dls_blocks` by
    (first_x_assum (mp_tac o Q.AP_TERM `MAP FST`) >> simp[MAP_MAP_o, combinTheory.o_DEF]) >>
  first_x_assum (qspec_then `dft_loop_step cfg lr fn trip` mp_tac) >> simp[]
QED

Theorem fmp_dft_user_count:
  fn_pass_step rpolicy (CFP_Simple VP_DFT) observed s fn out /\
  ALL_DISTINCT (fn_labels fn) ==>
  LENGTH (fn_user_param_insts fn) <=
  LENGTH (fn_user_param_insts out.fpo_function)
Proof
  strip_tac >> gvs[fn_pass_step_def] >>
  mp_tac (Q.SPECL [`LENGTH fn.fn_blocks * LENGTH fn.fn_blocks`,
    `(<|dls_blocks := fn.fn_blocks; dls_from_to := FEMPTY;
         dls_last_order := FEMPTY|>, (cfg_analyze fn).cfg_dfs_post, F)`]
    (Q.INST [`cfg` |-> `cfg_analyze fn`, `lr` |-> `liveness_analyze fn`]
      dft_funpow_param_keys)) >>
  simp[fn_labels_def] >>
  simp[dft_fn_def] >> pairarg_tac >> simp[] >>
  Cases_on `fn.fn_blocks` >> Cases_on `final_st.dls_blocks` >>
  simp[fn_user_param_insts_def, fn_entry_insts_def, entry_block_def] >>
  strip_tac >> gvs[fn_labels_def]
QED

Theorem sue_blocks_labels[local]:
  !bbs s outs s'. sue_expand_blocks_supply dfg s bbs = (outs,s') ==>
  MAP (\b. b.bb_label) outs = MAP (\b. b.bb_label) bbs
Proof
  Induct >> simp[sue_expand_blocks_supply_def] >> rpt gen_tac >>
  strip_tac >> gvs[AllCaseEqs(), sue_expand_block_supply_def] >>
  gvs[AllCaseEqs()] >> first_x_assum drule >> simp[]
QED

Theorem fmp_sue_labels:
  fn_pass_step rpolicy (CFP_Simple VP_SingleUseExpansion) observed s fn out ==>
  fn_labels out.fpo_function = fn_labels fn
Proof
  rw[fn_pass_step_def] >>
  gvs[AllCaseEqs(), sue_expand_function_supply_def] >>
  gvs[AllCaseEqs(), fn_labels_def] >>
  drule sue_blocks_labels >> simp[]
QED

(* Suffix premise inventory (DROP 4 o1_fn_passes):
   MakeSSA; SimplifyCFG; SingleUseExpansion; DFT; CFGNormalization.

   All bounds here use fn_user_param_insts (entry block), never a total
   function count. Only MakeSSA and DFT have residual premises: distinct
   block labels. In particular DFT no longer needs wf_function, fn_inst_wf
   or EVERY inst_shape_ok, nor correctness of its scheduled body.

   Suppliers for the joining theory:
   - Initial labels: source o1_ctx_shape -> o1_fn_shape -> wf_function ->
     ALL_DISTINCT (fn_labels source). fmp_lower_function_preserves_labels
     (fmpStepLayout) transfers these to the input of MakeSSA.
   - MakeSSA output: make_ssa_current_fn_key followed by block_key_labels
     preserves the label list, using the same distinctness premise as
     fmp_make_ssa_user_count. No additional shape premise is needed.
   - SimplifyCFG output: simplify_cfg_fn_with_labels_transition followed by
     label_map_transition_def gives ALL_DISTINCT output labels from
     ALL_DISTINCT input labels. This is structural, not an application of
     o1_step_contract to an unshaped observed unit.
   - SUE: fmp_sue_user_count has no residual premise; fmp_sue_labels above
     transfers distinctness to DFT.
   - DFT: fmp_dft_user_count needs only that distinctness. For its output,
     dft_fn_labels_map (dftCorrectness) preserves the label list.
   - CFGNormalization: its separate child's proposed user-count interface
     takes distinct input labels, supplied by the preceding DFT equation.
     This inventory does not assume that child's count proof.

   Thus no intermediate observed-unit shape or ir_supply_inst_ok premise
   needs to be inferred from fn_steps/walk_view for these four bounds.
   The joining theory still owes SimplifyCFG's independent count bound
   and the initial source-to-FMP count bound; neither is asserted here.
*)
