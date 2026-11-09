(* Exact memory-check boundaries of the sealed sparse-store observer. *)
Theory storeSlotsObserverMemory
Ancestors
  exprSimAbiGasBridge fragGasPathMem fragExec memSafeRun contextCodegenRel
  o1ContractSimplifyCfgSrcFrame venomInst venomExecSemantics venomState
  compileEnv list rich_list arithmetic simplifyCfgMergeRuns abiEncoderObserver

Theorem observer_revert_pair_before_stop[local]:
  revert_forward_pair
    <|bb_label := lbl; bb_instructions := xs ++ [mk_inst id STOP [] []]|> i j ==>
  j < LENGTH xs
Proof
  simp[revert_forward_pair_def, get_instruction_def] >> strip_tac >>
  Cases_on `j < LENGTH xs` >> simp[] >>
  gvs[EL_APPEND_EQN, mk_inst_def] >>
  `j - LENGTH xs = 0` by decide_tac >> gvs[]
QED

Theorem observer_revert_pair_prefix[local]:
  isPREFIX xs bb.bb_instructions /\
  revert_forward_pair
    <|bb_label := lbl; bb_instructions := xs ++ [mk_inst id STOP [] []]|> i j ==>
  revert_forward_pair bb i j
Proof
  strip_tac >> drule observer_revert_pair_before_stop >> strip_tac >>
  drule scfg_revert_forward_pair_take >>
  disch_then (qspec_then `LENGTH xs` mp_tac) >>
  simp[TAKE_APPEND] >> strip_tac >>
  fs[IS_PREFIX_APPEND] >>
  drule scfg_revert_forward_pair_suffix >>
  disch_then (qspec_then `l` mp_tac) >>
  simp[revert_forward_pair_def, get_instruction_def] >> metis_tac[]
QED

Theorem observer_memory_check_transfer:
  fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb /\
  (revert_forward_at bb idx \/ mem_safe_step fuel ctx inst s) ==>
  ?original. lookup_block lbl fn.fn_blocks = SOME original /\
    (revert_forward_at original idx \/ mem_safe_step fuel ctx inst s)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule frag_observer_lookup_cases >> strip_tac
  >- (gvs[] >> fs[fn_has_code_def] >>
      fs[revert_forward_at_def] >>
      metis_tac[observer_revert_pair_prefix]) >>
  fs[fn_has_code_def] >> metis_tac[]
QED

Theorem observer_nonstart_phi_zero:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  lbl <> sa.cs_current_bb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >> Cases_on `bb.bb_instructions`
  >- simp[venomExecSemanticsTheory.phi_prefix_length_def] >>
  rename1 `bb.bb_instructions = inst::rest` >>
  Cases_on `(lbl,0) = frag_observer_cut sb`
  >- (gvs[frag_observer_cut_def] >>
      drule frag_observer_lookup_cases >> strip_tac >>
      gvs[venomInstTheory.mk_inst_def,
          venomExecSemanticsTheory.phi_prefix_length_def]) >>
  `get_instruction bb 0 = SOME inst` by simp[venomInstTheory.get_instruction_def] >>
  `(lbl,0) IN frag_observer_region sa sb` by
    (drule frag_observer_lookup_cases >> strip_tac >>
     simp[frag_observer_region_def, MEM_MAP] >> metis_tac[]) >>
  drule_all frag_observer_off_cut_opcodes >> strip_tac >>
  simp[venomExecSemanticsTheory.phi_prefix_length_def]
QED

Theorem observer_entered_is_jump[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) <> frag_observer_cut sb /\
  lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK middle /\ is_terminator inst.inst_opcode /\
  lookup_block middle.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME target /\
  eval_phis middle target.bb_instructions = OK entered ==>
  inst.inst_opcode <> INVOKE /\ middle = jump_to middle.vs_current_bb s /\
  (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) = middle
Proof
  strip_tac >> drule_all frag_observer_off_cut_opcodes >> strip_tac >>
  drule_all scfg_terminator_jump >> strip_tac >>
  `middle.vs_current_bb <> sa.cs_current_bb` by
    (irule frag_observer_jump_no_reentry >>
     qexistsl_tac [`inst`, `s`] >> metis_tac[step_inst_non_invoke]) >>
  `phi_prefix_length target.bb_instructions = 0` by
    (irule observer_nonstart_phi_zero >> metis_tac[]) >>
  `entered = middle` by gvs[eval_phis_no_phi] >>
  simp[] >>
  qpat_assum `middle = jump_to _ _`
    (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  fs[jump_to_def]
QED

Theorem observer_memory_edge_transfer:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) <> frag_observer_cut sb /\
  gas_path_mem_edge ctx (frag_observer sa sb fn id) s n (OK t) ==>
  gas_path_mem_edge ctx fn s n (OK t)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qpat_x_assum `gas_path_mem_edge _ _ _ _ _` mp_tac >>
  simp[gas_path_mem_edge_def] >> strip_tac >>
  `?original. lookup_block s.vs_current_bb fn.fn_blocks = SOME original /\
      get_instruction original s.vs_inst_idx = SOME inst` by
    (irule frag_observer_instruction_agrees >> metis_tac[]) >>
  `revert_forward_at original s.vs_inst_idx \/ mem_safe_step fuel ctx inst s` by
    metis_tac[observer_memory_check_transfer, optionTheory.SOME_11] >>
  simp[gas_path_mem_edge_def] >> qexists_tac `fuel` >> simp[] >>
  gvs[fragExecTheory.exit_result_def] >>
  metis_tac[observer_entered_is_jump]
QED

Theorem observer_lookup_nonentry_region[local]:
  lbl <> sa.cs_current_bb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb ==>
  (lbl,idx) IN frag_observer_region sa sb
Proof
  strip_tac >> drule frag_observer_lookup_cases >> strip_tac >>
  simp[frag_observer_region_def, MEM_MAP] >> metis_tac[]
QED

Theorem observer_jump_region[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) <> frag_observer_cut sb /\
  lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst fuel ctx inst s = OK middle /\ is_terminator inst.inst_opcode /\
  lookup_block middle.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME target ==>
  (middle.vs_current_bb,idx) IN frag_observer_region sa sb
Proof
  strip_tac >> drule_all frag_observer_off_cut_opcodes >> strip_tac >>
  drule_all scfg_terminator_jump >> strip_tac >>
  `middle.vs_current_bb <> sa.cs_current_bb` by
    (irule frag_observer_jump_no_reentry >>
     qexistsl_tac [`inst`, `s`] >> metis_tac[step_inst_non_invoke]) >>
  metis_tac[observer_lookup_nonentry_region]
QED

Theorem observer_memory_edge_region:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) <> frag_observer_cut sb /\
  gas_path_mem_edge ctx (frag_observer sa sb fn id) s n (OK t) /\
  ((t.vs_current_bb,t.vs_inst_idx) = frag_observer_cut sb \/
   ?bb. lookup_block t.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME bb) ==>
  (t.vs_current_bb,t.vs_inst_idx) IN frag_observer_region sa sb
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?target. lookup_block t.vs_current_bb
      (frag_observer sa sb fn id).fn_blocks = SOME target` by
    metis_tac[frag_observer_cut_def, pairTheory.PAIR_EQ, frag_observer_cut_lookup] >>
  qpat_x_assum `gas_path_mem_edge _ _ _ _ _` mp_tac >>
  simp[gas_path_mem_edge_def] >> strip_tac >>
  gvs[exit_result_def]
  >>~- ([`~is_terminator inst.inst_opcode`],
    drule_all venomInstProofsTheory.step_preserves_control_flow >> strip_tac >>
    gvs[frag_observer_region_def] >>
    metis_tac[LESS_EQ_SUC_REFL, LESS_EQ_TRANS])
  >>~- ([`eval_phis _ _ = OK _`],
    drule venomExecProofsTheory.eval_phis_preserves_current_bb >> strip_tac >>
    gvs[] >> metis_tac[observer_jump_region]) >>
  all_tac
  >>~- ([`exit_result (step_inst _ _ _ _)`],
    qpat_x_assum `OK _ = step_inst _ _ _ _` (assume_tac o SYM) >>
    fs[exit_result_def]) >>
  metis_tac[observer_jump_region]
QED
