(* Concrete relabeled return-decoder execution and caller payload transport. *)
Theory extcallReturnRelabelSuccess
Ancestors
  extcallReturnDecoderRelabel extcallReturnCountedPayload
  extcallReturnRelabelPrefix extcallReturnCompletedCut
  extcallReturnObserverResources extcallReturnObserverIds extcallReturnObserver
  extcallReturnDecodeSummary extcallReturnDecoderCode
  abiValidAllocatedContract abiMalformedRecursiveInterface
  exprSimAbiGasBridge abiEncoderObserver exprLoweringProps
  compileEnv venomState venomInst venomExecSemantics venomExecProofs fragExec
  list pred_set finite_map

Theorem return_relabel_stmt_control[local]:
  stmt_state_rel ctx func ce cx es (s with vs_current_bb := b) =
  stmt_state_rel ctx func ce cx es s
Proof
  `fmp_room ctx func (s with vs_current_bb := b) =
   fmp_room ctx func s` by
    (irule fmp_room_fields_cong >> simp[]) >>
  simp[stmt_state_rel_def, state_rel_def, accounts_rel_def, local_ptrs_rel_def,
       local_region_def, local_backed_def, immutable_base_zero_alt,
       lookup_var_def, storage_rel_def,
       transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
       contract_storage_def, contract_transient_def, venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.allocas_non_overlapping_def,
       venomMemDefsTheory.alloca_next_valid_def, alloca_room_def,
       pending_alloca_size_def, immutable_alloca_sep_def]
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

(* Prefix identities affect compilation but not the allocated decoder post. *)
Theorem return_relabel_post_ids[local]:
  cs_extends st en /\ st.cs_blocks <> en.cs_blocks ==>
  (abi_valid_allocated_post tv v ctx func ce cx es
     (start_relabel L ids' st) (start_swap st L ids' en) ceiling dstid d n s t =
   abi_valid_allocated_post tv v ctx func ce cx es
     (start_relabel L ids st) (start_swap st L ids en) ceiling dstid d n s t)
Proof
  strip_tac >> drule_all start_swap_fields >> strip_tac >>
  simp[abi_valid_allocated_post_def, return_relabel_sites, start_relabel_def]
QED

Theorem return_relabel_start_fields[local,simp]:
  (start_relabel L ids st).cs_current_bb = L /\
  LENGTH (start_relabel L ids st).cs_current_insts = LENGTH ids
Proof
  simp[start_relabel_def]
QED

(* Post-driven interface: select the concrete runtime state before metadata. *)
Theorem return_relabel_cut[local]:
  abi_valid_allocated_post tv v (return_observer_context ctx full) full
    ce cx es (start_relabel L ids st) (start_swap st L ids en)
    ceiling dstid d n (s with vs_current_bb := L) t ==>
  cs_extends st en /\ st.cs_blocks <> en.cs_blocks /\
  bare = frag_observer (start_relabel L ids st) (start_swap st L ids en) bare id /\
  full = return_observer_complete func (return_observer_ids func bound bare) keep /\
  EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
    MEM i (fn_insts func)) (fn_insts bare) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~MEM (Label keep) i.inst_operands)
    (fn_insts bare) /\
  L <> keep /\ en.cs_current_bb <> keep /\
  fn_has_code (start_relabel L ids st) (start_swap st L ids en) bare /\
  frag_gas_free (start_relabel L ids st) (start_swap st L ids en) /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
    (frag_code (start_relabel L ids st) (start_swap st L ids en)) /\
  (L,s.vs_inst_idx) IN frag_observer_region (start_relabel L ids st) (start_swap st L ids en) /\
  ~s.vs_halted /\ stmt_state_rel ctx func ce cx es (s with vs_current_bb := L) /\
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct full /\
  (!i. i.inst_opcode = ALLOCA ==> (MEM i (fn_insts full) <=> MEM i (fn_insts func))) ==>
  ?u. local_prefix (return_observer_context ctx full) bare (frag_observer_cut en)
      (s with vs_current_bb := L) u /\
    u.vs_fmp = s.vs_fmp /\
    abi_malformed_resource_post ctx func ce cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid (s with vs_current_bb := L) u /\
    val_in_memory tv v d u.vs_memory /\
    abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) d n
      (s with vs_current_bb := L) u /\ fresh_vars_wrt ceiling u /\
    (!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
      FLOOKUP s.vs_allocas aid = SOME (b,sz) \/ s.vs_alloca_next <= b) /\
    ~u.vs_halted /\ u.vs_current_bb = en.cs_current_bb /\
    u.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  rpt strip_tac >>
  drule_all start_swap_fields >> strip_tac >>
  `cs_extends (start_relabel L ids st) (start_swap st L ids en)` by
    simp[start_relabel_extends] >>
  drule_at (Pat `abi_valid_allocated_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)
    return_completed_cut_resources >>
  disch_then drule >> disch_then drule >>
  simp[return_relabel_sites, frag_observer_cut_def] >>
  fs[start_relabel_def] >> metis_tac[]
QED

Theorem return_capped_relabel_prefix:
  cs_extends st en /\ st.cs_blocks <> en.cs_blocks /\ frag_ops_free st en /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  (en.cs_current_insts <> [] \/
   !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  ~MEM en.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks st en))) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code st en)) /\
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
  ?L ids id ceiling u.
    frag_relabel_context st en L ids func /\
    local_prefix ctx (frag_relabel_observer st en L ids func id)
      (frag_observer_cut en) (s with vs_current_bb := L) u /\
    u.vs_fmp = s.vs_fmp /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
      (abi_malformed_scratch_sites st en func) dstid (s with vs_current_bb := L) u /\
    val_in_memory tv rv d u.vs_memory /\
    abi_valid_allocated_frame (abi_malformed_scratch_sites st en func) d
      (type_memory_bytes ce rt) (s with vs_current_bb := L) u /\
    fresh_vars_wrt ceiling u /\
    (!aid b sz. FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
       FLOOKUP s.vs_allocas aid = SOME (b,sz) \/ s.vs_alloca_next <= b) /\
    ~u.vs_halted /\ u.vs_current_bb = en.cs_current_bb /\
    u.vs_inst_idx = LENGTH en.cs_current_insts
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all frag_relabel_observer_exists >> strip_tac >>
  qabbrev_tac `bare = frag_relabel_observer st en L ids func id` >>
  qspecl_then [`func`, `bare`] strip_assume_tac
    (Q.GENL [`func`, `obs`] return_observer_ids_bound) >>
  qspec_then `bare` strip_assume_tac
    (Q.GEN `obs` return_observer_complete_fresh_label) >>
  qabbrev_tac `full = return_observer_complete func
    (return_observer_ids func bound bare) keep` >>
  `fn_inst_ids_distinct full /\
   (!i. i.inst_opcode = ALLOCA ==>
      (MEM i (fn_insts full) <=> MEM i (fn_insts func)))` by
    (qspecl_then [`func`, `bare`, `bound`, `keep`] mp_tac
       (Q.GENL [`func`, `obs`, `bound`, `keep`] return_observer_ids_complete_metadata) >>
     simp[Abbr `full`]) >>
  `(!i. MEM i (fn_insts full) ==> i.inst_opcode <> INVOKE) /\
   (!i. MEM i (fn_insts full) /\ i.inst_opcode = DALLOCA ==>
      MEM i (fn_insts func))` by
    (fs[Abbr `full`, return_observer_complete_members, return_observer_ids_insts,
        MEM_MAP] >> rpt strip_tac >> gvs[] >>
     simp[return_observer_inst_ids_def]) >>
  `fn_has_code (start_relabel L (return_observer_prefix_ids func bound ids) st)
    (start_swap st L (return_observer_prefix_ids func bound ids) en) full` by
    (simp[Abbr `full`] >> irule return_observer_complete_has_code >>
     irule return_observer_ids_relabel_code >> simp[]) >>
  `abi_malformed_entry ctx func cenv cx es
    (start_relabel L (return_observer_prefix_ids func bound ids) st)
    (abi_malformed_scratch_sites st en func) dstid live base_op hi
    (Lit 0w) dst B (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 d
    (type_memory_bytes ce rt) (s with vs_current_bb := L)` by
    (irule return_relabel_entry >> simp[]) >>
  drule_all return_observer_input_entry >> strip_tac >>
  `compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info sf ce rt)
    (start_relabel L (return_observer_prefix_ids func bound ids) st) =
    ((), start_swap st L (return_observer_prefix_ids func bound ids) en)` by
    (irule return_decoder_start_relabel >> simp[]) >>
  `?ceiling t. abi_valid_allocated_post tv rv
    (return_observer_context ctx full) full cenv cx es
    (start_relabel L (return_observer_prefix_ids func bound ids) st)
    (start_swap st L (return_observer_prefix_ids func bound ids) en)
    ceiling dstid d (type_memory_bytes ce rt) (s with vs_current_bb := L) t` by
    (irule return_capped_allocated_success >> simp[] >>
     qexistsl_tac [`B`, `base_op`, `bs`, `dst`, `env`, `hi`, `live`, `sf`, `ty`, `v`] >>
     drule return_observer_alloca_structure >> strip_tac >>
     gvs[return_relabel_sites]) >>
  `abi_valid_allocated_post tv rv (return_observer_context ctx full) full
    cenv cx es (start_relabel L ids st) (start_swap st L ids en)
    ceiling dstid d (type_memory_bytes ce rt) (s with vs_current_bb := L) t` by
    metis_tac[return_relabel_post_ids] >>
  qpat_x_assum `abi_valid_allocated_post _ _ _ _ _ _ _
    (start_relabel _ (return_observer_prefix_ids _ _ _) _) _ _ _ _ _ _ _` kall_tac >>
  `bare = frag_observer (start_relabel L ids st) (start_swap st L ids en) bare id` by
    (simp[Abbr `bare`] >> irule return_relabel_observer_bare >> simp[]) >>
  `L <> keep /\ en.cs_current_bb <> keep` by
    (`cs_extends (start_relabel L ids st) (start_swap st L ids en)` by
       simp[start_relabel_extends] >>
     qspecl_then [`start_relabel L ids st`, `start_swap st L ids en`, `bare`]
       mp_tac fn_has_code_start >>
     simp[] >> strip_tac >>
     drule lookup_block_MEM >> drule lookup_block_label >>
     fs[fn_has_code_def] >>
     imp_res_tac lookup_block_MEM >> imp_res_tac lookup_block_label >>
     drule_all start_swap_fields >> strip_tac >>
     fs[MEM_MAP] >> metis_tac[]) >>
  `(L,s.vs_inst_idx) IN frag_observer_region
    (start_relabel L ids st) (start_swap st L ids en)` by
    (qspec_then `start_swap st L ids en` mp_tac
       (Q.SPEC `start_relabel L ids st` (Q.GENL [`sa`, `sb`] frag_observer_start_region)) >>
     simp[start_relabel_extends]) >>
  `stmt_state_rel ctx func cenv cx es (s with vs_current_bb := L)` by
    fs[abi_malformed_entry_def, return_relabel_stmt_control] >>
  `EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode)
    (frag_code (start_relabel L ids st) (start_swap st L ids en))` by
    (simp[start_relabel_frag_code] >> irule return_decoder_frag_code >>
     goal_assum (drule_at Any)) >>
  `cs_extends (start_relabel L ids st) (start_swap st L ids en)` by
    simp[start_relabel_extends] >>
  `EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) (fn_insts bare) /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~MEM (Label keep) i.inst_operands)
       (fn_insts bare)` by fs[EVERY_MEM] >>
  `full = return_observer_complete func (return_observer_ids func bound bare) keep` by
    simp[Abbr `full`] >>
  drule return_relabel_cut >>
  disch_then (qspecl_then [`keep`, `id`, `func`, `bound`, `bare`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `local_prefix ctx bare (frag_observer_cut en) (s with vs_current_bb := L) u` by
    metis_tac[return_observer_prefix_context] >>
  qexistsl_tac [`L`, `ids`, `id`, `ceiling`, `u`] >>
  conj_tac >- (pure_rewrite_tac [frag_relabel_context_def] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qpat_x_assum `local_prefix ctx bare _ _ _` mp_tac >>
    simp_tac bool_ss [Abbr `bare`]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
