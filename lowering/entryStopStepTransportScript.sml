(* Concrete single-step transport across suffix-retaining STOP insertion. *)
Theory entryStopStepTransport
Ancestors
  entryStopObserverConstruction abiEncoderObserver venomExecSemantics
  venomExecProofs venomExecProps venomInst list rich_list arithmetic

Theorem entry_stop_phi_prefix:
  !xs k iid. phi_prefix_length xs <= k /\ k <= LENGTH xs ==>
    phi_prefix_length (TAKE k xs ++ [mk_inst iid STOP [] []] ++ DROP k xs) =
      phi_prefix_length xs /\
    TAKE (phi_prefix_length xs)
      (TAKE k xs ++ [mk_inst iid STOP [] []] ++ DROP k xs) =
      TAKE (phi_prefix_length xs) xs
Proof
  Induct_on `xs`
  >- simp[phi_prefix_length_def, mk_inst_def] >>
  rpt gen_tac >> Cases_on `k`
  >- (simp[phi_prefix_length_def] >>
      Cases_on `h.inst_opcode = PHI` >> simp[phi_prefix_length_def, mk_inst_def]) >>
  Cases_on `h.inst_opcode = PHI` >>
  simp[phi_prefix_length_def] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem entry_stop_block_phis[local]:
  phi_prefix_length bb.bb_instructions <= k /\ k <= LENGTH bb.bb_instructions ==>
  phi_prefix_length (entry_stop_block k iid bb).bb_instructions =
    phi_prefix_length bb.bb_instructions /\
  eval_phis s (entry_stop_block k iid bb).bb_instructions =
    eval_phis s bb.bb_instructions
Proof
  strip_tac >> drule_all entry_stop_phi_prefix >> strip_tac >>
  simp[entry_stop_block_def] >>
  once_rewrite_tac[GSYM eval_phis_prefix] >> asm_rewrite_tac[]
QED

Theorem entry_stop_source_instruction[local]:
  lookup_block lbl fn.fn_blocks = SOME original /\
  k <= LENGTH original.bb_instructions /\
  (s.vs_current_bb = lbl ==> s.vs_inst_idx < k) /\
  lookup_block s.vs_current_bb (entry_stop_function lbl k iid fn).fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst ==>
  ?bb'. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb' /\
        get_instruction bb' s.vs_inst_idx = SOME inst
Proof
  simp[entry_stop_function_def, entry_stop_lookup_block] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  strip_tac >> Cases_on `s.vs_current_bb = lbl`
  >- (gvs[] >>
      `original.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
      gvs[entry_stop_block_before_cut]) >>
  `x.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >> gvs[]
QED

Theorem entry_stop_target_phis[local]:
  lookup_block lbl fn.fn_blocks = SOME original /\
  phi_prefix_length original.bb_instructions <= k /\ k <= LENGTH original.bb_instructions /\
  lookup_block dest (entry_stop_function lbl k iid fn).fn_blocks = SOME bb ==>
  ?bb'. lookup_block dest fn.fn_blocks = SOME bb' /\
    phi_prefix_length bb.bb_instructions = phi_prefix_length bb'.bb_instructions /\
    eval_phis s bb.bb_instructions = eval_phis s bb'.bb_instructions
Proof
  simp[entry_stop_function_def, entry_stop_lookup_block] >>
  Cases_on `lookup_block dest fn.fn_blocks` >> simp[] >>
  strip_tac >> Cases_on `dest = lbl`
  >- (gvs[] >> `original.bb_label = dest` by metis_tac[lookup_block_label] >>
      gvs[entry_stop_block_phis]) >>
  `x.bb_label = dest` by metis_tac[lookup_block_label] >> gvs[]
QED

Theorem entry_stop_observer_step_transport:
  !lbl fn bb k s observer_ctx iid t ctx.
  lookup_block lbl fn.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions <= k /\ k <= LENGTH bb.bb_instructions /\
  (s.vs_current_bb = lbl ==> s.vs_inst_idx < k) /\
  abi_observer_step observer_ctx (entry_stop_function lbl k iid fn) (lbl,k) s t ==>
  abi_observer_step ctx fn (lbl,k) s t
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `abi_observer_step _ _ _ _ _` mp_tac >>
  simp[abi_observer_step_def] >> strip_tac >>
  drule_all entry_stop_source_instruction >> strip_tac >>
  `step_inst 0 ctx inst s = OK middle` by
    gvs[step_inst_non_invoke] >>
  simp[] >>
  drule_all entry_stop_target_phis >>
  disch_then (qspec_then `middle` strip_assume_tac) >>
  goal_assum (drule_at Any) >> gvs[]
QED
