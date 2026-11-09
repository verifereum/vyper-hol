(* Concrete relabeled return-decoder execution and caller payload transport. *)
Theory extcallReturnRelabelSuccess
Ancestors
  extcallReturnDecoderRelabel extcallReturnCountedPayload
  extcallReturnRelabelPrefix extcallReturnCompletedCut
  extcallReturnObserverResources extcallReturnObserverIds extcallReturnObserver
  extcallReturnDecodeSummary extcallReturnDecoderCode
  abiValidAllocatedContract abiMalformedRecursiveInterface
  exprSimAbiGasBridge abiEncoderObserver bodyMemAssignTopCopySem
  compileEnv venomState venomInst venomExecSemantics list pred_set finite_map

Theorem return_relabel_stmt_control[local]:
  stmt_state_rel ctx func ce cx es (s with vs_current_bb := b) =
  stmt_state_rel ctx func ce cx es s
Proof
  irule EQ_TRANS >>
  qexists_tac `stmt_state_rel ctx func ce cx es
    (s with <|vs_vars := s.vs_vars; vs_current_bb := b;
              vs_inst_idx := s.vs_inst_idx; vs_prev_bb := s.vs_prev_bb|>)` >>
  conj_tac >- (AP_TERM_TAC >> simp[venom_state_component_equality]) >>
  rewrite_tac[topcopy_control_frame] >> simp[]
QED

Theorem return_relabel_operand[local]:
  eval_operand op (s with vs_current_bb := L) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem return_relabel_entry[local]:
  abi_malformed_entry ctx func ce cx es st sites dstid live
    base_op hi src dst B len xs p d n s ==>
  abi_malformed_entry ctx func ce cx es (start_relabel L ids st)
    sites dstid live base_op hi src dst B len xs p d n
    (s with vs_current_bb := L)
Proof
  strip_tac >>
  `local_ptrs_reserved ce (start_relabel L ids st) =
   local_ptrs_reserved ce st` by
    simp[local_ptrs_reserved_def, start_relabel_def, not_fresh_at_def] >>
  fs[abi_malformed_entry_def, start_relabel_def,
     abi_malformed_allocated_window_def, abi_malformed_destination_def,
     return_relabel_stmt_control, return_relabel_operand] >>
  metis_tac[]
QED

Theorem return_relabel_observer_bare[local]:
  cs_extends st en /\ st.cs_blocks <> en.cs_blocks /\
  L <> en.cs_current_bb /\
  ~MEM en.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks st en))) ==>
  frag_relabel_observer st en L ids func id =
    frag_observer (start_relabel L ids st) (start_swap st L ids en)
      (frag_relabel_observer st en L ids func id) id
Proof
  strip_tac >> drule_all start_swap_fields >> strip_tac >>
  `~MEM en.cs_current_bb
    (MAP (\bb. bb.bb_label)
      (emitted_blocks (start_relabel L ids st) (start_swap st L ids en)))` by
    simp[start_swap_emitted_blocks] >>
  `~MEM <|bb_label := en.cs_current_bb;
           bb_instructions := en.cs_current_insts ++ [mk_inst id STOP [] []]|>
    (emitted_blocks (start_relabel L ids st) (start_swap st L ids en))` by
    (fs[MEM_MAP] >> metis_tac[]) >>
  `FILTER (\bb. MEM bb
      (emitted_blocks (start_relabel L ids st) (start_swap st L ids en)))
      (emitted_blocks (start_relabel L ids st) (start_swap st L ids en)) =
      emitted_blocks (start_relabel L ids st) (start_swap st L ids en)` by
    simp[FILTER_EQ_ID, EVERY_MEM] >>
  simp[frag_observer_def, frag_relabel_observer_def]
QED

Theorem return_relabel_sites[local]:
  abi_malformed_scratch_sites (start_relabel L ids st)
    (start_swap st L ids en) func = abi_malformed_scratch_sites st en func
Proof
  simp[abi_malformed_scratch_sites_def, start_relabel_def, start_swap_def] >>
  IF_CASES_TAC >> simp[]
QED
