(* Caller-counted decoder success after the concrete relabeled prefix. *)
Theory extcallReturnRelabelCounted
Ancestors
  extcallReturnRelabelSuccess extcallReturnRelabelPrefix
  extcallReturnCountedCheck abiValidAllocatedContract
  abiMalformedRecursiveInterface abiMalformedSiteFrame exprSimAbiGasBridge
  abiEncoderObserver fragGasMode compileEnv venomState venomExecSemantics
  list pred_set finite_map

Theorem return_resource_initial_label[local]:
  abi_malformed_resource_post ctx func ce cx es next sites dstid
    (s with vs_current_bb := L) t =
  abi_malformed_resource_post ctx func ce cx es next sites dstid s t
Proof
  `!op. eval_operand op (s with vs_current_bb := L) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[abi_malformed_resource_post_def]
QED

Theorem return_frame_initial_label[local]:
  abi_valid_allocated_frame sites d n (s with vs_current_bb := L) t =
  abi_valid_allocated_frame sites d n s t
Proof
  simp[abi_valid_allocated_frame_def, abi_malformed_site_range_def]
QED

Theorem return_capped_relabel_counted_success:
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
  drule_all return_capped_relabel_prefix >> strip_tac >>
  `frag_relabel_state L st.cs_current_bb (s with vs_current_bb := L) s` by
    (irule frag_relabel_state_initial >> simp[]) >>
  `(L,s.vs_inst_idx) IN frag_observer_region
    (start_relabel L ids st) (start_swap st L ids en)` by
    (qspec_then `start_swap st L ids en` mp_tac
       (Q.SPEC `start_relabel L ids st`
         (Q.GENL [`sa`, `sb`] frag_observer_start_region)) >>
     fs[frag_relabel_context_def, start_relabel_extends, start_relabel_def]) >>
  `?u'. gas_path ctx func s 0 (OK u') /\
     frag_relabel_state L st.cs_current_bb u u'` by
    (drule return_relabel_prefix_path >> disch_then irule >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`id`, `ids`, `en`] >> simp[] >> gvs[]) >>
  `u.vs_current_bb <> L` by fs[frag_relabel_context_def] >>
  drule_all frag_relabel_state_cut >> strip_tac >>
  qexistsl_tac [`ceiling`, `u'`] >>
  conj_tac >- simp[gas_marked_path_def] >>
  qpat_x_assum `u' = u with vs_prev_bb := _`
    (fn th => once_rewrite_tac[th]) >>
  simp[SRULE [] (Q.INST [`rd` |-> `t.vs_returndata`]
      extcall_return_observer_resources),
    SRULE [] (Q.INST [`rd` |-> `t.vs_returndata`]
      extcall_return_observer_frame), fresh_vars_wrt_def] >>
  fs[return_resource_initial_label, return_frame_initial_label,
     fresh_vars_wrt_def] >> gvs[]
QED
