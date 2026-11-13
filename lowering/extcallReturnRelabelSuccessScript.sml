(* Concrete relabeled return-decoder execution and caller payload transport. *)
Theory extcallReturnRelabelSuccess
Ancestors
  extcallReturnEdgePrefix extcallReturnDecoderRelabel extcallReturnCountedPayload
  extcallReturnRelabelPrefix extcallReturnCompletedCut
  extcallReturnObserverResources extcallReturnObserverIds extcallReturnObserver
  extcallReturnDecodeSummary extcallReturnDecoderCode
  abiValidAllocatedContract abiMalformedRecursiveInterface
  exprSimAbiGasBridge exprSimAbiGasBridgeEdge abiEncoderObserver exprLoweringProps
  compileEnv loweringStateRelDefs venomState venomInst venomExecSemantics venomExecProofs fragExec
  list pred_set finite_map


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
  strip_tac >>
  drule_all return_capped_relabel_edge_prefix >> strip_tac >>
  qexistsl_tac [`L`, `ids`, `id`, `ceiling`, `u`] >> simp[] >>
  fs[frag_relabel_edge_context_def, frag_relabel_context_def]
QED
