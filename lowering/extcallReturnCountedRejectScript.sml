(* Counted rejection of the capped, singleton-wrapped return decoder. *)
Theory extcallReturnCountedReject
Ancestors
  extcallReturnCountedTransport extcallReturnStraightObserver
  extcallReturnObserverResources extcallReturnDecoderRelabel
  extcallReturnEntryBridge extcallReturnSyntax extcallReturnLabelSyntax
  extcallReturnDecoderLabels
  abiReturnReject abiMalformedRecursiveInterface abiReturnPrefixTransport
  exprLoweringProps exprSimAbiGasBridge abiEncoderObserver fragExec fragGasMode compileEnv loweringStateRelDefs venomState venomInst
  venomExecSemantics localPtrsProps list finite_map words

(* The corresponding success-side fact is local to its theory. *)
Theorem return_reject_stmt_control[local]:
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

Theorem return_reject_entry_control[local]:
  abi_malformed_entry ctx func ce cx es st sites dstid live
    base_op hi src dst B len xs p d n s ==>
  abi_malformed_entry ctx func ce cx es (start_relabel L ids st)
    sites dstid live base_op hi src dst B len xs p d n
    (s with vs_current_bb := L)
Proof
  strip_tac >>
  `!op. eval_operand op (s with vs_current_bb := L) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  fs[abi_malformed_entry_def, start_relabel_def,
     local_ptrs_reserved_def, not_fresh_at_def,
     abi_malformed_allocated_window_def, abi_malformed_destination_def,
     return_reject_stmt_control] >> metis_tac[]
QED

Theorem return_reject_sites[local]:
  abi_malformed_scratch_sites (start_relabel L ids st)
    (start_swap st L ids en) func = abi_malformed_scratch_sites st en func
Proof
  simp[abi_malformed_scratch_sites_def, start_relabel_def, start_swap_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem return_capped_observer_reject:
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  cap = vyper_abi_size_bound env rt /\
  (~is_dynamic (vyper_to_abi_type env rt) ==>
    cap = static_length (vyper_to_abi_type env rt)) /\
  abi_static_length (vyper_to_abi_type env rt) <= LENGTH (TAKE cap bs) /\
  evaluate_abi_decode_return env ty bs = INR err /\
  abi_decoder_coherent ce env sf rt tv /\ abi_decode_bytes_widths env rt /\
  assignable_type env rt /\ type_memory_size tv < dimword (:256) /\
  abi_size_bound sf rt < dimword (:256) /\
  compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info sf ce rt) st = ((),en) /\
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct obs /\
  LENGTH ids = LENGTH st.cs_current_insts /\
  fn_has_code (start_relabel L ids st) (start_swap st L ids en) obs /\
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts obs) <=> MEM i (fn_insts func))) /\
  (!i. MEM i (fn_insts obs) ==> i.inst_opcode <> INVOKE) /\
  (!i. MEM i (fn_insts obs) /\ i.inst_opcode = DALLOCA ==>
    MEM i (fn_insts func)) /\
  (case type_to_abi_dec_info sf ce rt of
     DecPrimWord clamp => 32 <= LENGTH (TAKE cap bs) | _ => T) /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live base_op hi
    (Lit 0w) dst B (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 d
    (type_memory_bytes ce rt) s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?fuel u. run_from fuel (return_observer_context ctx obs) obs
    (s with vs_current_bb := L) = Abort Revert_abort u
Proof
  strip_tac >>
  `abi_malformed_scratch_sites (start_relabel L ids st)
      (start_swap st L ids en) obs = abi_malformed_scratch_sites st en func` by
    (simp[return_reject_sites] >>
     drule return_observer_alloca_structure >> simp[]) >>
  drule_all return_observer_input_entry >> strip_tac >>
  drule return_reject_entry_control >>
  disch_then (qspecl_then [`ids`, `L`] assume_tac) >>
  `compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info sf ce rt) (start_relabel L ids st) =
      ((),start_swap st L ids en)` by
    (irule return_decoder_start_relabel >> simp[]) >>
  qspecl_then [`s with vs_current_bb := L`, `start_swap st L ids en`]
    (qx_choose_then `ceiling` strip_assume_tac) return_decoder_ceiling_exists >>
  irule abi_return_bounded_decode_reject >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  first_assum (irule_at (Pat `fn_has_code _ _ _`)) >>
  first_assum (irule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
  qexists_tac `ty` >>
  first_assum (irule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
  asm_rewrite_tac[] >>
  first_assum (irule_at (Pat `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`err`, `ceiling`] >>
  gvs[start_relabel_def]
QED

Theorem return_capped_counted_reject:
  cs_extends st en /\ fn_has_code st en func /\ fn_inst_ids_distinct func /\
  (!l. dst <> Label l /\ base_op <> Label l /\ hi <> Label l) /\
  (en.cs_current_insts <> [] \/
   !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  cap = vyper_abi_size_bound env rt /\
  (~is_dynamic (vyper_to_abi_type env rt) ==>
    cap = static_length (vyper_to_abi_type env rt)) /\
  abi_static_length (vyper_to_abi_type env rt) <= LENGTH (TAKE cap bs) /\
  evaluate_abi_decode_return env ty bs = INR err /\
  abi_decoder_coherent ce env sf rt tv /\ abi_decode_bytes_widths env rt /\
  assignable_type env rt /\ type_memory_size tv < dimword (:256) /\
  abi_size_bound sf rt < dimword (:256) /\
  compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info sf ce rt) st = ((),en) /\
  (case type_to_abi_dec_info sf ce rt of
     DecPrimWord clamp => 32 <= LENGTH (TAKE cap bs) | _ => T) /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live base_op hi
    (Lit 0w) dst B (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 d
    (type_memory_bytes ce rt) s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (Abort Revert_abort u)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `frag_ops_free st en` by metis_tac[return_decoder_ops_free] >>
  `?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\
       (?u. r = Abort Revert_abort u)` suffices_by metis_tac[] >>
  Cases_on `st.cs_blocks = en.cs_blocks`
  >- (`frag_gas_free st en` by
        (irule return_decoder_straight_gas_free >> simp[] >>
         first_assum (irule_at (Pat `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`)) >>
         simp[]) >>
      irule (SRULE [] (Q.INST [`sa` |-> `st`, `sb` |-> `en`,
        `R` |-> `\r. ?u. r = Abort Revert_abort u`]
        return_observer_counted_abort_straight)) >> simp[] >>
      qexistsl_tac [`en`, `st`] >> simp[] >> rpt strip_tac >>
      `?fuel u. run_from fuel (return_observer_context ctx fn') fn'
         (s with vs_current_bb := st.cs_current_bb) = Abort Revert_abort u` by
        (irule return_capped_observer_reject >>
         first_assum (irule_at (Pat `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
         first_assum (irule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
         first_assum (irule_at (Pat `fn_has_code _ _ _`)) >>
         simp[] >> metis_tac[]) >>
      `s with vs_current_bb := st.cs_current_bb = s` by simp[venom_state_component_equality] >>
      fs[] >> qexists_tac `fuel` >>
      simp[exit_result_def]) >>
  irule (SRULE [] (Q.INST [`sa` |-> `st`, `sb` |-> `en`,
        `R` |-> `\r. ?u. r = Abort Revert_abort u`]
    return_observer_counted_abort_relabel)) >> simp[] >>
  qexistsl_tac [`en`, `st`] >> simp[] >>
  reverse conj_tac
  >- metis_tac[return_decoder_endpoint_label, return_decoder_fragment_ids] >>
  rpt strip_tac >>
  `?fuel u. run_from fuel (return_observer_context ctx fn') fn'
     (s with vs_current_bb := L) = Abort Revert_abort u` by
    (irule return_capped_observer_reject >>
     first_assum (irule_at (Pat `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     first_assum (irule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
     first_assum (irule_at (Pat `fn_has_code _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  qexists_tac `fuel` >> simp[exit_result_def]
QED
