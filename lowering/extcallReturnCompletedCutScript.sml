(* Separate the bare execution observer from completed resource metadata. *)
Theory extcallReturnCompletedCut
Ancestors
  extcallReturnCutPrefix extcallReturnDecoderCode abiValidAllocatedContract
  extcallReturnCountedTransport extcallReturnObserverResources
  abiEncoderObserver abiDecoderLoop exprSimAbiGasBridge
  abiMalformedRecursiveInterface abiMalformedSiteFrame exprSimHash
  venomExecSemantics venomInstProps venomInst venomState compileEnv
  extcallReturnObserver extcallReturnObserverIds callLayoutDefs rich_list
  list pred_set finite_map

Theorem return_complete_lookup_present[local]:
  lookup_block lbl obs.fn_blocks = SOME bb ==>
  lookup_block lbl (return_observer_complete func obs keep).fn_blocks = SOME bb
Proof
  simp[return_observer_complete_def, lookup_block_def, FIND_APPEND_CASE] >>
  strip_tac >> simp[]
QED

Theorem return_complete_step_forward[local]:
  abi_observer_step ctx obs cut s t ==>
  abi_observer_step ctx (return_observer_complete func obs keep) cut s t
Proof
  rw[abi_observer_step_def] >>
  imp_res_tac return_complete_lookup_present >> metis_tac[]
QED

Theorem return_complete_prefix_forward[local]:
  local_prefix ctx obs cut s t ==>
  local_prefix ctx (return_observer_complete func obs keep) cut s t
Proof
  Induct_on `local_prefix` >> rpt strip_tac
  >- (irule (cj 1 local_prefix_rules) >> simp[]) >>
  irule (cj 2 local_prefix_rules) >> metis_tac[return_complete_step_forward]
QED

Theorem return_ids_step_forward[local]:
  EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
    MEM i (fn_insts func)) (fn_insts obs) /\
  abi_observer_step ctx obs cut s t ==>
  abi_observer_step ctx (return_observer_ids func bound obs) cut s t
Proof
  rw[abi_observer_step_def] >>
  `inst.inst_opcode <> STOP /\ inst.inst_opcode <> NOP ==>
     MEM inst (fn_insts func)` by
    (drule_all return_observer_instruction_member >>
     fs[EVERY_MEM]) >>
  simp[return_observer_ids_lookup, return_observer_ids_get_instruction,
       return_observer_ids_phis, return_observer_inst_ids_step] >>
  qexists_tac `middle` >> simp[]
QED

Theorem return_ids_prefix_forward[local]:
  local_prefix ctx obs cut s t ==>
  EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
    MEM i (fn_insts func)) (fn_insts obs) ==>
  local_prefix ctx (return_observer_ids func bound obs) cut s t
Proof
  Induct_on `local_prefix` >> rpt strip_tac
  >- (irule (cj 1 local_prefix_rules) >> simp[]) >>
  irule (cj 2 local_prefix_rules) >> metis_tac[return_ids_step_forward]
QED

Theorem return_completed_cut_resources:
  bare = frag_observer st en host id /\
  full = return_observer_complete func (return_observer_ids func bound bare) keep /\
  EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
    MEM i (fn_insts func)) (fn_insts bare) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~MEM (Label keep) i.inst_operands)
    (fn_insts bare) /\
  s.vs_current_bb <> keep /\ en.cs_current_bb <> keep /\
  cs_extends st en /\ fn_has_code st en host /\ frag_gas_free st en /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (frag_code st en) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region st en /\ ~s.vs_halted /\
  abi_valid_allocated_post tv v (return_observer_context ctx full) full
    ce cx es st en ceiling dstid d n s t /\
  stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct full /\
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts full) <=> MEM i (fn_insts func))) ==>
  ?u. local_prefix (return_observer_context ctx full) bare (frag_observer_cut en) s u /\
    stop_view u = stop_view t /\ u.vs_fmp = s.vs_fmp /\
    abi_malformed_resource_post ctx func ce cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s u /\
    val_in_memory tv v d u.vs_memory /\
    abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) d n s u /\
    fresh_vars_wrt ceiling u /\
    (!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
       FLOOKUP s.vs_allocas aid = SOME (b,sz) \/ s.vs_alloca_next <= b) /\
    ~u.vs_halted /\ u.vs_current_bb = en.cs_current_bb /\
    u.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  fs[abi_valid_allocated_post_def] >>
  `abi_decode_sim (return_observer_context ctx full) bare s t` by
    (irule return_observer_ids_complete_sim >> metis_tac[]) >>
  `?fuel. run_from fuel (return_observer_context ctx full) bare s = Halt (stop_view t)` by
    (irule abi_decode_sim_stop_run >> simp[] >>
     qexistsl_tac [`<|bb_label := en.cs_current_bb;
       bb_instructions := en.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction]) >>
  `?u. local_prefix (return_observer_context ctx full) bare (frag_observer_cut en) s u /\
       stop_view u = stop_view t` by
    (qpat_assum `bare = _` (fn th => simp[Once th]) >>
     irule frag_observer_halt_cut_prefix >> simp[frag_observer_cut_def] >>
     conj_tac >- metis_tac[] >> simp[stop_view_def, halt_state_def]) >>
  `u.vs_fmp = s.vs_fmp` by (irule return_frag_prefix_fmp >> metis_tac[]) >>
  `local_prefix (return_observer_context ctx full) full (frag_observer_cut en) s u` by
    (simp[] >> irule return_complete_prefix_forward >>
     irule return_ids_prefix_forward >> metis_tac[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  drule stop_view_fields >> strip_tac >>
  `abi_malformed_resource_post (return_observer_context ctx full) full
     ce cx es st.cs_next_var (abi_malformed_scratch_sites st en full) dstid s u` by
    (fs[abi_malformed_resource_post_def] >>
     conj_tac >-
       (drule_all stop_view_recover >> disch_then SUBST1_TAC >>
        gvs[hash_returndata_state_rel]) >>
     metis_tac[stop_view_operand]) >>
  `abi_malformed_resource_post ctx func ce cx es st.cs_next_var
     (abi_malformed_scratch_sites st en full) dstid s u` by
    (irule return_observer_output_resources >> metis_tac[]) >>
  drule return_observer_alloca_structure >> strip_tac >>
  qexists_tac `u` >>
  fs[frag_observer_cut_def, abi_valid_allocated_frame_def,
     abi_malformed_site_range_def, fresh_vars_wrt_def] >> metis_tac[]
QED
