(* Equal-block sanitation for resource-restoring return decoding. *)
Theory extcallReturnStraightCounted
Ancestors
  extcallReturnStraightObserver extcallReturnDecoderRelabel extcallReturnDecoderLabels
  extcallReturnCompletedCut extcallReturnCountedPayload extcallReturnDecodeSummary
  extcallReturnCountedCheck
  extcallReturnObserverResources extcallReturnObserverIds extcallReturnObserver
  fragExec venomExecSemantics venomExecProofs venomWf
  abiValidAllocatedContract abiMalformedRecursiveInterface
  exprSimAbiGasBridge abiEncoderObserver fragGasMode compileEnv loweringStateRelDefs venomState
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


Theorem return_capped_straight_counted_success:
  cs_extends st en /\ st.cs_blocks = en.cs_blocks /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  (!l. dst <> Label l /\ base_op <> Label l /\ hi <> Label l) /\
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  rv = (if needs_external_call_wrap ty then ArrayV (TupleV [v]) else v) /\
  cap = vyper_abi_size_bound env rt /\
  evaluate_abi_decode_return env ty bs = INL v /\
  abi_decoder_coherent ce env sf rt tv /\
  compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info sf ce rt) st = ((),en) /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live base_op hi
    (Lit 0w) dst B (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 d
    (type_memory_bytes ce rt) s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ceiling u. gas_marked_path F ctx func s 0 (OK u) /\
    u.vs_fmp = s.vs_fmp /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s u /\
    val_in_memory tv rv d u.vs_memory /\
    abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) d
      (type_memory_bytes ce rt) s u /\
    fresh_vars_wrt ceiling u /\
    (!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
       FLOOKUP s.vs_allocas aid = SOME (b,sz) \/ s.vs_alloca_next <= b) /\
    ~u.vs_halted /\ u.vs_current_bb = en.cs_current_bb /\
    u.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `frag_gas_free st en` by
    (drule return_decoder_straight_gas_free >> simp[]) >>
  drule_all return_straight_resource_observer >> strip_tac >>
  qabbrev_tac `a = start_relabel st.cs_current_bb ids st` >>
  qabbrev_tac `b = start_swap st st.cs_current_bb ids en` >>
  `cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
   b.cs_current_bb = en.cs_current_bb /\
   LENGTH b.cs_current_insts = LENGTH en.cs_current_insts /\
   a.cs_next_var = st.cs_next_var /\
   s.vs_current_bb = a.cs_current_bb /\
   s.vs_inst_idx = LENGTH a.cs_current_insts` by
    (drule_all return_straight_swap >> strip_tac >>
     simp[Abbr `a`, Abbr `b`, start_relabel_def] >> metis_tac[]) >>
  `frag_code a b = frag_code st en` by
    (simp[Abbr `a`, Abbr `b`] >> irule return_straight_sanitized_code >> simp[]) >>
  `frag_gas_free a b` by
    (`emitted_blocks a b = []` by metis_tac[cj 3 return_straight_shape] >>
     fs[frag_gas_free_def, Abbr `a`, start_relabel_def]) >>
  `abi_malformed_scratch_sites a b func = abi_malformed_scratch_sites st en func` by
    simp[Abbr `a`, Abbr `b`, return_straight_sanitized_sites] >>
  `compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi
     (type_to_abi_dec_info sf ce rt) a = ((),b)` by suspend "compile" >>
  `abi_malformed_entry ctx func cenv cx es a
     (abi_malformed_scratch_sites a b func) dstid live base_op hi
     (Lit 0w) dst B (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 d
     (type_memory_bytes ce rt) s` by
    (simp[Abbr `a`] >> irule return_straight_sanitized_entry >> gvs[]) >>
  `?ceiling t. abi_valid_allocated_post tv rv (return_observer_context ctx full)
     full cenv cx es a b ceiling dstid d (type_memory_bytes ce rt) s t` by
    suspend "allocated" >>
  `?u. local_prefix (return_observer_context ctx full) bare (frag_observer_cut b) s u /\
    u.vs_fmp = s.vs_fmp /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid s u /\
    val_in_memory tv rv d u.vs_memory /\
    abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) d
      (type_memory_bytes ce rt) s u /\
    fresh_vars_wrt ceiling u /\
    (!aid p sz. FLOOKUP u.vs_allocas aid = SOME (p,sz) ==>
       FLOOKUP s.vs_allocas aid = SOME (p,sz) \/ s.vs_alloca_next <= p) /\
    ~u.vs_halted /\ u.vs_current_bb = en.cs_current_bb /\
    u.vs_inst_idx = LENGTH en.cs_current_insts` by suspend "resources" >>
  suspend "counted"
QED

Resume return_capped_straight_counted_success[compile]:
  simp[Abbr `a`, Abbr `b`] >> irule return_decoder_start_relabel >> gvs[]
QED
Resume return_capped_straight_counted_success[allocated]:
  drule_all return_observer_input_entry >> strip_tac >>
  drule return_observer_alloca_structure >> strip_tac >>
  irule return_capped_allocated_success >> metis_tac[]
QED
Resume return_capped_straight_counted_success[resources]:
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (frag_code a b)` by
    (drule extcallReturnDecoderCodeTheory.return_decoder_frag_code >> simp[]) >>
  `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region a b` by
    metis_tac[frag_observer_start_region] >>
  `stmt_state_rel ctx func cenv cx es s` by fs[abi_malformed_entry_def] >>
  `full = return_observer_complete func (return_observer_ids func 0 bare) keep` by
    simp[return_straight_ids_zero] >>
  `bare = frag_observer a b bare id` by
    (simp[Abbr `a`, Abbr `b`] >> metis_tac[return_straight_bare_self]) >>
  `fn_has_code a b bare` by
    (simp[Abbr `a`, Abbr `b`] >> irule return_straight_observer_code >> simp[]) >>
  `s.vs_current_bb <> keep /\ b.cs_current_bb <> keep` by metis_tac[] >>
  drule_all return_completed_cut_resources >> strip_tac >>
  qexists_tac `u` >> gvs[]
QED
Resume return_capped_straight_counted_success[counted]:
  `local_prefix ctx bare (frag_observer_cut b) s u` by
    metis_tac[return_observer_prefix_context] >>
  `abi_decode_sim ctx bare s u` by metis_tac[local_prefix_sim] >>
  `abi_decode_sim ctx (frag_observer st en func id) s u` by
    (irule return_straight_observer_sim >> simp[Abbr `a`, Abbr `b`] >> metis_tac[]) >>
  `?fuel. run_from fuel ctx (frag_observer st en func id) s = Halt (stop_view u)` by
    (irule abi_decode_sim_stop_run >> simp[] >>
     qexistsl_tac [`<|bb_label := en.cs_current_bb;
       bb_instructions := en.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction]) >>
  `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region st en` by
    metis_tac[frag_observer_start_region] >>
  `?u'. local_prefix ctx (frag_observer st en func id) (frag_observer_cut en) s u' /\
     stop_view u' = stop_view u` by
    (irule frag_observer_halt_cut_prefix >> simp[frag_observer_cut_def] >>
     conj_tac >- metis_tac[] >> simp[stop_view_def, halt_state_def]) >>
  `gas_path ctx func s 0 (OK u')` by
    (drule frag_observer_prefix_zero_path >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  `?rd. u' = u with vs_returndata := rd` by
    metis_tac[stop_view_recover] >>
  qexistsl_tac [`ceiling`, `u'`] >>
  gvs[gas_marked_path_def, frag_observer_cut_def, fresh_vars_wrt_def] >>
  `u with vs_returndata := rd =
   u with <|vs_returndata := rd; vs_prev_bb := u.vs_prev_bb|>` by
    simp[venom_state_component_equality] >>
  pop_assum (fn th => once_rewrite_tac[th]) >>
  rewrite_tac[extcall_return_observer_resources, extcall_return_observer_frame] >>
  simp[]
QED
Finalise return_capped_straight_counted_success
