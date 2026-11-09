(* Equal-block sanitation for resource-restoring return decoding. *)
Theory extcallReturnStraightCounted
Ancestors
  extcallReturnStraightObserver extcallReturnDecoderRelabel
  extcallReturnCompletedCut extcallReturnCountedPayload extcallReturnDecodeSummary
  extcallReturnObserverResources extcallReturnObserverIds extcallReturnObserver
  fragExec venomExecSemantics venomExecProofs venomWf
  abiValidAllocatedContract abiMalformedRecursiveInterface
  exprSimAbiGasBridge abiEncoderObserver fragGasMode compileEnv venomState
  venomInst exprLoweringProps list rich_list pred_set finite_map

Theorem return_straight_sanitized_code[local]:
  cs_extends st en /\ st.cs_blocks = en.cs_blocks /\
  LENGTH ids = LENGTH st.cs_current_insts ==>
  frag_code (start_relabel st.cs_current_bb ids st)
    (start_swap st st.cs_current_bb ids en) = frag_code st en
Proof
  strip_tac >> drule_all return_straight_shape >> strip_tac >>
  drule_all return_straight_swap >> strip_tac >>
  `emitted_blocks (start_relabel st.cs_current_bb ids st)
    (start_swap st st.cs_current_bb ids en) = []` by
    (irule (cj 3 return_straight_shape) >> simp[start_relabel_def] >> metis_tac[]) >>
  simp[frag_code_def, emitted_insts_def, start_relabel_def, start_swap_def,
       DROP_APPEND, DROP_DROP]
QED

Theorem return_straight_sanitized_sites[local]:
  abi_malformed_scratch_sites (start_relabel st.cs_current_bb ids st)
    (start_swap st st.cs_current_bb ids en) func =
  abi_malformed_scratch_sites st en func
Proof
  simp[abi_malformed_scratch_sites_def, start_relabel_def, start_swap_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem return_straight_sanitized_entry[local]:
  abi_malformed_entry ctx func ce cx es st sites dstid live
    base_op hi src dst B len xs p d n s ==>
  abi_malformed_entry ctx func ce cx es (start_relabel st.cs_current_bb ids st)
    sites dstid live base_op hi src dst B len xs p d n s
Proof
  simp[abi_malformed_entry_def, start_relabel_def,
       local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]
QED

(* Zero adjustment leaves the already-distinct straight observer unchanged. *)
Theorem return_straight_ids_zero[local]:
  return_observer_ids func 0 obs = obs
Proof
  `!i. return_observer_inst_ids func 0 i = i` by
    (simp[return_observer_inst_ids_def] >> gen_tac >>
     IF_CASES_TAC >> simp[]) >>
  `return_observer_inst_ids func 0 = I` by simp[FUN_EQ_THM] >>
  simp[return_observer_ids_def, MAP_ID]
QED

Theorem return_straight_bare_self[local]:
  cs_extends st en /\ st.cs_blocks = en.cs_blocks /\
  LENGTH ids = LENGTH st.cs_current_insts ==>
  (let a = start_relabel st.cs_current_bb ids st in
   let b = start_swap st st.cs_current_bb ids en in
   let bare = frag_observer a b func id in
   bare = frag_observer a b bare id)
Proof
  strip_tac >> drule_all return_straight_swap >> strip_tac >>
  drule_all return_straight_shape >> strip_tac >>
  `emitted_blocks (start_relabel st.cs_current_bb ids st)
    (start_swap st st.cs_current_bb ids en) = []` by
    (irule (cj 3 return_straight_shape) >> simp[start_relabel_def] >> metis_tac[]) >>
  simp[frag_observer_def]
QED

Theorem return_straight_resource_observer[local]:
  cs_extends st en /\ st.cs_blocks = en.cs_blocks /\ frag_gas_free st en /\
  fn_has_code st en func /\ fn_inst_ids_distinct func ==>
  ?ids id keep bare full.
    LENGTH ids = LENGTH st.cs_current_insts /\
    bare = frag_observer (start_relabel st.cs_current_bb ids st)
      (start_swap st st.cs_current_bb ids en) func id /\
    full = return_observer_complete func bare keep /\
    fn_has_code (start_relabel st.cs_current_bb ids st)
      (start_swap st st.cs_current_bb ids en) full /\
    fn_inst_ids_distinct full /\
    (!i. i.inst_opcode = ALLOCA ==>
      (MEM i (fn_insts full) <=> MEM i (fn_insts func))) /\
    (!i. MEM i (fn_insts full) ==> i.inst_opcode <> INVOKE) /\
    (!i. MEM i (fn_insts full) /\ i.inst_opcode = DALLOCA ==>
      MEM i (fn_insts func)) /\
    EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
      MEM i (fn_insts func)) (fn_insts bare) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~MEM (Label keep) i.inst_operands)
      (fn_insts bare) /\
    st.cs_current_bb <> keep /\ en.cs_current_bb <> keep
Proof
  strip_tac >>
  qspecl_then [`fn_insts func`, `LENGTH st.cs_current_insts`]
    strip_assume_tac frag_relabel_fresh_ids >> rename1 `~MEM id ids` >>
  qabbrev_tac `bare = frag_observer (start_relabel st.cs_current_bb ids st)
    (start_swap st st.cs_current_bb ids en) func id` >>
  `fn_has_code (start_relabel st.cs_current_bb ids st)
     (start_swap st st.cs_current_bb ids en) bare /\
   fn_inst_ids_distinct bare /\
   (!i. MEM i (fn_insts bare) ==> i.inst_opcode <> INVOKE /\
     (i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==> MEM i (fn_insts func)))` by
    (drule_all return_straight_observer_provenance >>
     disch_then (qspec_then `id` strip_assume_tac) >>
     simp[Abbr `bare`, return_straight_observer_code,
          return_straight_observer_distinct]) >>
  qspec_then `bare` strip_assume_tac (Q.GEN `obs` return_observer_complete_fresh_label) >>
  `st.cs_current_bb <> keep /\ en.cs_current_bb <> keep` by
    (drule_all return_straight_swap >> strip_tac >>
     drule_all fn_has_code_start >> strip_tac >>
     fs[fn_has_code_def, start_relabel_def] >>
     imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
     fs[MEM_MAP] >> metis_tac[]) >>
  qexistsl_tac [`ids`, `id`, `keep`, `bare`, `return_observer_complete func bare keep`] >>
  simp[Abbr `bare`, return_observer_complete_has_code] >>
  conj_tac
  >- (irule return_observer_complete_ids >> simp[] >>
      metis_tac[return_straight_observer_id_agreement]) >>
  conj_tac >- simp[return_observer_complete_allocas] >>
  fs[return_observer_complete_members, EVERY_MEM] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

