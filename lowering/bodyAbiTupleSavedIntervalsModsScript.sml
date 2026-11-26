(* Protection at the original saved-operand observation across a physical phase. *)
Theory bodyAbiTupleSavedIntervalsMods
Ancestors
  bodyAbiTupleBufferStateMods bodyFullExtCallDirectWindows
  bodyFullShadowBodyInv exprSimSubscriptArrayFrame stateRelProj
  abiEncoderWindowPhase loweringPosts loweringStateRelDefs
  compileEnv finite_map pred_set list words pair

Theorem abi_tuple_saved_intervals_phase_mods:
  abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
    shared pbase capacity root dst dst_offset prefix a u Gu tu /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func ce cx ee s) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  local_ptrs_reserved ce se /\ fn_inst_ids_distinct func /\
  window_phase ctx func a c ids outs u v /\
  (!aid. aid IN ids ==> se.cs_next_id <= aid) /\
  EVERY (\(p,n). pbase+dst_offset <= p /\ p+n <= pbase+capacity) outs /\
  (!aid. aid IN shared INSERT ids ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
    (!aid p n. aid IN ids /\ FLOOKUP v.vs_allocas aid = SOME (p,n) ==>
      i < p \/ p+n <= i) /\ i IN tv.t_mem ==> i IN tu.t_mem) ==>
  !b n. ((b = 0 /\ n = lo) \/
         (?name. local_region ce ee.scopes s name b n) \/
         (?aid. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n))) ==>
    mem_bytes_at b n v.vs_memory = mem_bytes_at b n s.vs_memory /\
    (!i. b <= i /\ i < b+n /\ i IN tv.t_mem ==> i IN tn.t_mem)
Proof
  rewrite_tac[abi_tuple_buffer_state_mods_def] >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ s`
    (drule_then assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ u /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _ s`
    (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `EVERY (\(p,n). pbase <= p /\ p+n <= pbase+capacity) outs` by
    (simp_tac bool_ss [EVERY_MEM, FORALL_PROD, UNCURRY_DEF] >>
     qx_genl_tac [`p`,`n`] >> disch_tac >>
     qpat_assum `EVERY _ outs`
       (qspecl_then [`p`,`n`] (drule_then strip_assume_tac) o
        SIMP_RULE bool_ss [EVERY_MEM, FORALL_PROD, UNCURRY_DEF]) >>
     simp[] >> decide_tac) >>
  drule_all_then (assume_tac o CONJUNCT1)
    (Q.INST [`cut` |-> `(se:compile_state).cs_next_id`]
       extcall_direct_encode_windows) >>
  `!name b n. local_region ce ee.scopes s name b n ==>
      local_region ce ee.scopes u name b n` by
    (rpt strip_tac >> drule_all_then (fn th => simp[th]) local_region_wb_frame) >>
  (* Writeback retains the lookup itself, independently of byte agreement. *)
  `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
      FLOOKUP u.vs_allocas aid = SOME row` by fs[wb_frame_def] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!p k. ((p = 0 /\ k = lo) \/ _) ==> mem_bytes_at p k v.vs_memory = _ /\ _`
    (qspecl_then [`b`,`n`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qpat_assum `!p k. ((p = 0 /\ k = lo) \/ _) ==> mem_bytes_at p k u.vs_memory = _ /\ _`
    (qspecl_then [`b`,`n`] (drule_then strip_assume_tac)) >>
  simp[] >> metis_tac[]
QED
