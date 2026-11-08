(* Successful allocation-backed dynamic-array initialization. *)
Theory abiValidAllocatedArrayInit
Ancestors
  abiValidAllocatedArrayPrefix abiValidAllocatedArraySource
  abiMalformedInitTotal abiMalformedInitResource abiMalformedBulkIntegration
  abiMalformedRecursiveInterface abiMalformedConstructorContract
  abiDecoderDynarrayPrefix abiDecoderArrayLoopInit abiDecoderArrayInitReentry
  abiDecoderIndexInit abiDecoderContract abiDecodeRanges abiMalformedNavigation
  abiDecoderAbortReentry abiDecoderReentry abiDecoderReentryPointer
  exprLoweringProps localPtrsProps emitHelperProps emitHelper
  compileEnv context venomState venomMemDefs venomInst
  finite_map pred_set words list arithmetic

Theorem abi_valid_allocated_array_init_fresh_run:
  abi_decode_array_loop_init dst src MLOAD base_op hi maxn stride st = (setup,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  fn_inst_ids_distinct func /\ fresh_vars_wrt st s /\
  maxn < dimword (:256) /\ 32 <= outsz /\
  n = abi_head_word (DROP p xs) /\ n <= maxn /\ p+32+n*stride <= L /\
  MEM (mk_inst (en.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (en.cs_next_var-1))]) (fn_insts func) /\
  en.cs_next_id-2 IN sites ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt en t
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decode_array_loop_init_trace >> strip_tac >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `eval_operand src s = SOME (n2w p) /\
   eval_operand base_op s = SOME (n2w B) /\
   eval_operand hi s = SOME (n2w L) /\ B+L < dimword (:256) /\
   mem_bytes_at B L (abi_decode_source MLOAD s) = xs` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
       abi_decode_source_def] >>
  `p+32 <= L /\ L < dimword (:256)` by decide_tac >>
  `abi_decode_load MLOAD (n2w (B+p):bytes32) s = n2w n` by
    (drule_all abi_checked_offset_load >> strip_tac >> fs[]) >>
  drule_at (Pat `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _`)
    abi_decode_dynarray_position_prefix_sequence >>
  disch_then (qspecl_then [`s`, `p`, `n`, `B`] mp_tac) >>
  (impl_tac >- (simp[] >> disj2_tac >> qexists_tac `L` >> simp[] >> gvs[MULT_COMM])) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st guard_st) s = OK guarded` >>
  `abi_malformed_entry ctx func cenv cx es guard_st sites dstid live
    base_op hi src dst B L xs p d outsz guarded` by
    (drule_all abi_malformed_dynarray_prefix_entry >> simp[]) >>
  drule_all abi_malformed_init_header_resource >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts guard_st header_st) guarded = OK prepared` >>
  `local_ptrs_reserved cenv header_st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `guard_st` >>
     fs[abi_malformed_entry_def]) >>
  `stmt_state_rel ctx func cenv cx es prepared` by
    fs[abi_malformed_resource_post_def] >>
  `MEM (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString header_st.cs_next_var)]) (fn_insts func) /\
   header_st.cs_next_id IN sites` by
    (qpat_x_assum `MEM _ (fn_insts func)` mp_tac >>
     qpat_x_assum `_ IN sites` mp_tac >> simp[]) >>
  `fresh_vars_wrt en prepared` by
    (irule fresh_vars_wrt_mono >> qexists_tac `header_st` >> simp[GREATER_EQ]) >>
  `en.cs_next_var <= en.cs_next_var` by simp[] >>
  drule_all (Q.INST [`ceiling` |-> `en`] abi_malformed_index_resource) >>
  disch_then (qspec_then `dstid` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts header_st en) prepared = OK indexed` >>
  `run_inst_seq (emitted_insts guard_st en) guarded = OK indexed` by
    (irule run_inst_seq_compose_ok >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `indexed` >> simp[] >>
  irule run_inst_seq_compose_ok >>
  qexistsl_tac [`guarded`, `guard_st`] >> simp[] >>
  metis_tac[inst_extends_trans]
QED

Theorem abi_valid_allocated_array_init_run:
  abi_decode_array_loop_init dst src MLOAD base_op hi maxn stride st = (setup,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  fn_inst_ids_distinct func /\ fresh_vars_wrt ceiling s /\
  en.cs_next_var <= ceiling.cs_next_var /\
  maxn < dimword (:256) /\ 32 <= outsz /\
  n = abi_head_word (DROP p xs) /\ n <= maxn /\ p+32+n*stride <= L /\
  MEM (mk_inst (en.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (en.cs_next_var-1))]) (fn_insts func) /\
  en.cs_next_id-2 IN sites ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\ fresh_vars_wrt ceiling t
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_reentry_code >> strip_tac >>
  drule abi_malformed_entry_prune >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var s`]
    abi_valid_allocated_array_init_fresh_run) >>
  (impl_tac >- simp[abi_decoder_prune_fresh]) >> strip_tac >>
  `fresh_vars_wrt ceiling t` by
    (irule fresh_vars_wrt_mono >> qexists_tac `en` >> simp[GREATER_EQ]) >>
  drule_all abi_decoder_sequence_runtime_reentry >> metis_tac[]
QED

(* Total resource interface, with the abort case eliminated by valid bounds. *)
Theorem abi_valid_allocated_array_init_resources:
  abi_decode_array_loop_init dst src MLOAD base_op hi maxn stride st = (setup,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  fn_inst_ids_distinct func /\ fresh_vars_wrt ceiling s /\
  en.cs_next_var <= ceiling.cs_next_var /\
  maxn < dimword (:256) /\ maxn*stride < dimword (:256) /\ 32 <= outsz /\
  n = abi_head_word (DROP p xs) /\ n <= maxn /\ p+32+n*stride <= L /\
  MEM (mk_inst (en.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (en.cs_next_var-1))]) (fn_insts func) /\
  en.cs_next_id-2 IN sites ==>
  ?t slot. run_inst_seq (emitted_insts st en) s = OK t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    fresh_vars_wrt ceiling t /\
    eval_operand (FST setup) t = SOME (n2w slot) /\
    eval_operand (SND setup) t = SOME (n2w n) /\ mload slot t = 0w /\
    slot+32 < dimword (:256) /\
    FLOOKUP t.vs_allocas (en.cs_next_id-2) = SOME (slot,32)
Proof
  strip_tac >> drule_all abi_valid_allocated_array_init_run >> strip_tac >>
  drule_all abi_malformed_init_total >> strip_tac >- gvs[] >>
  gvs[] >> goal_assum (drule_at Any) >> simp[]
QED
