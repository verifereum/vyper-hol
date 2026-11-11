(* Counted execution is assembled only after caller resources are restored. *)
Theory extcallReturnCountedPayload
Ancestors
  extcallReturnCompletedCut extcallReturnObserver extcallReturnObserverIds
  extcallReturnCountedTransport abiValidAllocatedContract
  abiMalformedRecursiveInterface abiEncoderObserver exprSimAbiGasBridge
  extcallReturnDecodeSummary extcallReturnObserverResources
  fragGasMode compileEnv venomState venomInst venomExecSemantics list pred_set

Theorem return_completed_counted_success:
  bare = frag_observer st en host id /\
  full = return_observer_complete func (return_observer_ids func bound bare) keep /\
  EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
    MEM i (fn_insts func)) (fn_insts bare) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~MEM (Label keep) i.inst_operands)
    (fn_insts bare) /\
  s.vs_current_bb <> keep /\ en.cs_current_bb <> keep /\
  cs_extends st en /\ fn_has_code st en host /\ frag_gas_free st en /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (frag_code st en) /\
  (st.cs_blocks = en.cs_blocks \/ en.cs_current_insts <> [] \/
    !bb. lookup_block en.cs_current_bb host.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region st en /\ ~s.vs_halted /\
  abi_valid_allocated_post tv v (return_observer_context ctx full) full
    ce cx es st en ceiling dstid d n s t /\
  stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ fn_inst_ids_distinct full /\
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts full) <=> MEM i (fn_insts func))) ==>
  ?u. gas_marked_path F ctx host s 0 (OK u) /\
    u.vs_fmp = s.vs_fmp /\
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
  strip_tac >> drule_all return_completed_cut_resources >> strip_tac >>
  `local_prefix ctx bare (frag_observer_cut en) s u` by
    metis_tac[return_observer_prefix_context] >>
  `gas_path ctx host s 0 (OK u)` by
    (drule frag_observer_prefix_zero_path >>
     disch_then irule >> metis_tac[]) >>
  qexists_tac `u` >> simp[gas_marked_path_def]
QED

(* Invoke the source adapter in the completed observer, then recover the
   caller's resources before converting its finite prefix to a counted path. *)
Theorem return_capped_completed_counted_success:
  bare = frag_observer st en func id /\
  full = return_observer_complete func (return_observer_ids func bound bare) keep /\
  EVERY (\i. i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
    MEM i (fn_insts func)) (fn_insts bare) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~MEM (Label keep) i.inst_operands)
    (fn_insts bare) /\
  s.vs_current_bb <> keep /\ en.cs_current_bb <> keep /\
  cs_extends st en /\ fn_has_code st en func /\ frag_gas_free st en /\
  EVERY (\i. abi_decoder_reentry_opcode i.inst_opcode) (frag_code st en) /\
  (st.cs_blocks = en.cs_blocks \/ en.cs_current_insts <> [] \/
    !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code st en full /\ fn_inst_ids_distinct func /\ fn_inst_ids_distinct full /\
  (!i. i.inst_opcode = ALLOCA ==>
    (MEM i (fn_insts full) <=> MEM i (fn_insts func))) /\
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
  `(!i. MEM i (fn_insts full) ==> i.inst_opcode <> INVOKE) /\
   (!i. MEM i (fn_insts full) /\ i.inst_opcode = DALLOCA ==>
      MEM i (fn_insts func))` by
    (fs[return_observer_complete_members, return_observer_ids_insts,
        MEM_MAP, EVERY_MEM] >> rpt strip_tac >> gvs[] >>
     simp[return_observer_inst_ids_def]) >>
  drule_all return_observer_input_entry >> strip_tac >>
  drule return_observer_alloca_structure >> strip_tac >>
  `?ceiling t. abi_valid_allocated_post tv rv (return_observer_context ctx full)
     full cenv cx es st en ceiling dstid d (type_memory_bytes ce rt) s t` by
    (irule return_capped_allocated_success >> metis_tac[]) >>
  `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region st en` by
    metis_tac[frag_observer_start_region] >>
  `stmt_state_rel ctx func cenv cx es s` by
    fs[abi_malformed_entry_def] >>
  drule_all return_completed_counted_success >> strip_tac >>
  qexistsl_tac [`ceiling`, `u`] >> simp[]
QED
