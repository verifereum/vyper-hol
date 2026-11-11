(* Total malformed-input initialization, before recursive array traversal. *)
Theory abiMalformedInitTotal
Ancestors
  abiMalformedInitResource abiMalformedRecursiveInterface abiMalformedBulkIntegration
  ctorAbiActualAlloc abiDecoderAbortReentry abiDecoderVarExtend rich_list
  abiDecoderBytesBound abiDecoderRange abiEncoder
  abiMalformedMemberSetup fragExec abiDecoderVarSequence
  abiMalformedBulkArray abiMalformedConstructorContract abiMalformedIndexState
  abiDecoderArrayLoopInit abiDecoderArrayInitExec abiDecoderArrayInitReentry
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderIndexInit
  abiDecoderArrayHeader abiDecoderGuards abiDecoderContract abiDecoderComposition
  abiMalformedNavigation abiDecoderReentry abiDecoderReentryPointer
  exprLoweringProps localPtrsProps emitHelperProps emitHelper compileEnv context
  venomState venomInst venomMemDefs venomMemProps venomExecSemantics
  finite_map pred_set words list arithmetic

Theorem abi_malformed_init_fresh_total:
  abi_decode_array_loop_init dst src MLOAD base_op hi maxn stride st = (setup,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  fn_inst_ids_distinct func /\ fresh_vars_wrt st s /\
  maxn < dimword (:256) /\ maxn*stride < dimword (:256) /\ 32 <= outsz /\
  MEM (mk_inst (en.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (en.cs_next_var-1))]) (fn_insts func) /\
  en.cs_next_id-2 IN sites ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (?t slot n. run_inst_seq (emitted_insts st en) s = OK t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    fresh_vars_wrt en t /\ n = abi_head_word (DROP p xs) /\ n <= maxn /\
    p+32 <= L /\ p+32+n*stride <= L /\
    eval_operand (FST setup) t = SOME (n2w slot) /\
    eval_operand (SND setup) t = SOME (n2w n) /\ mload slot t = 0w /\
    slot+32 < dimword (:256) /\
    FLOOKUP t.vs_allocas (en.cs_next_id-2) = SOME (slot,32))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule abi_decode_array_loop_init_trace >> strip_tac >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `hi <> Lit 0w /\ p < dimword (:256) /\ B+L < dimword (:256) /\
   eval_operand src s = SOME (n2w p) /\
   eval_operand base_op s = SOME (n2w B) /\
   eval_operand hi s = SOME (n2w L)` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def] >>
  `L < dimword (:256)` by decide_tac >>
  drule_all abi_malformed_dynarray_prefix_total >> strip_tac
  >- (disj1_tac >> qexists_tac `t` >>
      irule run_inst_seq_abort_extends >> qexists_tac `guard_st` >>
      simp[] >> irule inst_extends_trans >> qexists_tac `header_st` >> simp[]) >>
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
  `fresh_vars_wrt en prepared` by
    (irule fresh_vars_wrt_mono >> qexists_tac `header_st` >> simp[GREATER_EQ]) >>
  `MEM (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString header_st.cs_next_var)]) (fn_insts func) /\
   header_st.cs_next_id IN sites` by
    (qpat_x_assum `MEM _ (fn_insts func)` mp_tac >>
     qpat_x_assum `_ IN sites` mp_tac >> simp[]) >>
  mp_tac (Q.INST [`ceiling` |-> `en`, `s` |-> `prepared`, `st` |-> `header_st`]
    abi_malformed_index_resource) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `run_inst_seq (emitted_insts guard_st en) guarded = OK t` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`prepared`, `header_st`] >> simp[]) >>
  `run_inst_seq (emitted_insts st en) s = OK t` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`guarded`, `guard_st`] >> simp[] >>
     irule inst_extends_trans >> qexists_tac `header_st` >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s guarded` by
    (drule_all abi_malformed_dynarray_prefix_resource >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid guarded prepared` by
    (irule abi_malformed_resource_weaken >>
     qexistsl_tac [`guard_st.cs_next_var`, `sites`] >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid prepared t` by
    (irule abi_malformed_resource_weaken >>
     qexistsl_tac [`header_st.cs_next_var`, `sites`] >> simp[]) >>
  `abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t` by
    metis_tac[abi_malformed_resource_trans] >>
  `p+32 <= L /\ c < dimword (:256)` by decide_tac >>
  `mem_bytes_at B L (abi_decode_source MLOAD s) = xs` by
    fs[abi_malformed_entry_def, abi_malformed_allocated_window_def,
       abi_decode_source_def] >>
  drule_all abi_checked_offset_load >> strip_tac >>
  `c = abi_head_word (DROP p xs)` by
    (qpat_x_assum `abi_decode_load _ _ _ = n2w c` mp_tac >> simp[]) >>
  `B+p < dimword (:256)` by decide_tac >>
  `mload (w2n (n2w (B+p):bytes32)) guarded = n2w c` by
    (fs[abi_decode_load_def, mload_def]) >>
  `abi_decoder_operand_live header_st.cs_next_var cnt` by
    (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
          fresh_id_def, emit_def, abi_decoder_operand_live_def] >>
     strip_tac >> gvs[abi_decoder_older_vars_def]) >>
  `eval_operand cnt t = SOME (n2w c)` by
    (qpat_x_assum `abi_malformed_resource_post _ _ _ _ _ header_st.cs_next_var _ _ prepared t`
       mp_tac >> simp[abi_malformed_resource_post_def] >> strip_tac >>
     qpat_x_assum `!op w. abi_decoder_operand_live _ op /\ eval_operand op prepared = SOME w ==> _`
       irule >> gvs[]) >>
  disj2_tac >> qexistsl_tac [`t`, `slot`, `c`] >> gvs[]
QED

Theorem abi_malformed_init_protected_outputs:
  abi_decode_array_loop_init dst src MLOAD base_op hi maxn stride st = (setup,en) ==>
  !x. not_fresh_at st x ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ ~MEM x i.inst_outputs)
      (emitted_insts st en)
Proof
  Cases_on `hi = Lit 0w` >> Cases_on `base_op = Lit 0w` >>
  simp[abi_decode_array_loop_init_def, abi_decode_dynarray_position_prefix_def,
    abi_decode_bytes_head_def, compile_abi_dec_addr_def, abi_decode_count_guard_def,
    abi_decode_dynarray_payload_guard_def, compile_abi_decode_range_check_def,
    abi_decode_array_header_def, abi_decode_index_init_def, compile_alloc_buffer_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def, not_fresh_at_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_malformed_init_lookup:
  abi_decode_array_loop_init dst src MLOAD base_op hi maxn stride st = (setup,en) /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  !x. not_fresh_at st x ==> lookup_var x t = lookup_var x s
Proof
  rpt strip_tac >> irule ctor_actual_sequence_var_frame >>
  qexists_tac `emitted_insts st en` >> simp[] >>
  drule abi_malformed_init_protected_outputs >> simp[]
QED

Theorem abi_malformed_init_total:
  abi_decode_array_loop_init dst src MLOAD base_op hi maxn stride st = (setup,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  fn_inst_ids_distinct func /\ fresh_vars_wrt ceiling s /\
  en.cs_next_var <= ceiling.cs_next_var /\
  maxn < dimword (:256) /\ maxn*stride < dimword (:256) /\ 32 <= outsz /\
  MEM (mk_inst (en.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (en.cs_next_var-1))]) (fn_insts func) /\
  en.cs_next_id-2 IN sites ==>
  (?t. run_inst_seq (emitted_insts st en) s = Abort Revert_abort t) \/
  (?t slot n. run_inst_seq (emitted_insts st en) s = OK t /\
    abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid s t /\
    fresh_vars_wrt ceiling t /\ n = abi_head_word (DROP p xs) /\ n <= maxn /\
    p+32 <= L /\ p+32+n*stride <= L /\
    eval_operand (FST setup) t = SOME (n2w slot) /\
    eval_operand (SND setup) t = SOME (n2w n) /\ mload slot t = 0w /\
    slot+32 < dimword (:256) /\
    FLOOKUP t.vs_allocas (en.cs_next_id-2) = SOME (slot,32))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_reentry_code >> strip_tac >>
  drule abi_malformed_entry_prune >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var s`]
    abi_malformed_init_fresh_total) >>
  (impl_tac >- simp[abi_decoder_prune_fresh]) >> strip_tac
  >- (disj1_tac >> drule_all abi_decoder_sequence_revert_reentry >> simp[]) >>
  `fresh_vars_wrt ceiling t` by
    (irule fresh_vars_wrt_mono >> qexists_tac `en` >> simp[GREATER_EQ]) >>
  drule_all abi_decoder_sequence_runtime_reentry >> strip_tac >>
  rename1 `abi_decoder_vars_extend s.vs_vars clean actual` >>
  `!x. not_fresh_at st x ==> lookup_var x actual = lookup_var x clean` by
    (rpt strip_tac >>
     `lookup_var x actual = lookup_var x s` by
       (drule abi_malformed_init_lookup >> disch_then drule >> simp[]) >>
     `lookup_var x clean = lookup_var x (abi_decoder_prune_vars st.cs_next_var s)` by
       (qpat_assum `run_inst_seq _ (abi_decoder_prune_vars _ _) = OK clean`
          (mp_then Any mp_tac abi_malformed_init_lookup) >>
        disch_then drule >> simp[]) >>
     fs[abi_decoder_prune_vars_def, lookup_var_def, FLOOKUP_DRESTRICT,
        abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `local_ptrs_reserved cenv st` by fs[abi_malformed_entry_def] >>
  drule_all abi_malformed_resource_restore >> strip_tac >>
  disj2_tac >> qexistsl_tac [`actual`, `slot`, `n`] >>
  simp[] >> reverse conj_tac >- fs[mload_def] >>
  fs[abi_malformed_resource_post_def, abi_decoder_prune_vars_def] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  `eval_operand op (abi_decoder_prune_vars st.cs_next_var s) = SOME w` by
    simp[abi_decoder_prune_eval] >>
  fs[abi_decoder_prune_vars_def] >> metis_tac[]
QED

Theorem abi_malformed_init_shape:
  abi_decode_array_loop_init dst src MLOAD base_op hi maxn stride st = (setup,en) ==>
  inst_extends st en /\ en.cs_blocks = st.cs_blocks /\
  en.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st en)
Proof
  strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_reentry_code >> strip_tac >>
  drule abi_decode_array_loop_init_trace >> strip_tac >>
  drule_all abi_decode_dynarray_position_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `inst_extends st en` by metis_tac[inst_extends_trans] >>
  `emitted_insts st header_st = emitted_insts st guard_st ++ emitted_insts guard_st header_st` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `inst_extends st header_st` by metis_tac[inst_extends_trans] >>
  `emitted_insts st en = emitted_insts st header_st ++ emitted_insts header_st en` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  fs[EVERY_CONJ]
QED

Theorem abi_malformed_init_fragment:
  abi_decode_array_loop_init dst src MLOAD base_op hi maxn stride st = (setup,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz incoming /\
  fn_inst_ids_distinct func /\ fresh_vars_wrt ceiling incoming /\
  en.cs_next_var <= ceiling.cs_next_var /\
  maxn < dimword (:256) /\ maxn*stride < dimword (:256) /\ 32 <= outsz /\
  MEM (mk_inst (en.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (en.cs_next_var-1))]) (fn_insts func) /\
  en.cs_next_id-2 IN sites ==>
  frag_exec ctx st en (\s. s = incoming)
    (\t. ?slot n.
      abi_malformed_resource_post ctx func cenv cx es st.cs_next_var sites dstid incoming t /\
      fresh_vars_wrt ceiling t /\ n = abi_head_word (DROP p xs) /\ n <= maxn /\
      p+32 <= L /\ p+32+n*stride <= L /\
      eval_operand (FST setup) t = SOME (n2w slot) /\
      eval_operand (SND setup) t = SOME (n2w n) /\ mload slot t = 0w /\
      slot+32 < dimword (:256) /\
      FLOOKUP t.vs_allocas (en.cs_next_id-2) = SOME (slot,32))
    (\r. ?v. r = Abort Revert_abort v)
Proof
  strip_tac >> drule abi_malformed_init_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> fs[inst_extends_def] >>
  rpt strip_tac >> gvs[] >> drule_all abi_malformed_init_total >> strip_tac
  >- (disj2_tac >> goal_assum (drule_at Any) >> simp[]) >>
  disj1_tac >> goal_assum (drule_at Any) >>
  qexists_tac `slot` >>
  fs[abi_malformed_resource_post_inst_idx, fresh_vars_wrt_def,
     eval_operand_def, lookup_var_def, mload_def] >>
  gvs[MULT_COMM]
QED
