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
  abiValidAllocatedContract abiMalformedSiteFrame abiDecoderArrayHeader
  exprSimAlloc venomExecSemantics venomMemProps
  abiDecoderLoop fragExec abiMalformedMemberSetup instIdxIndep
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

(* An ALLOCA can reuse a cached row; new rows begin at the old frontier. *)
Theorem abi_valid_allocated_buffer_origin:
  compile_alloc_buffer n st = (buf,en) /\
  run_inst_seq (emitted_insts st en) s = OK t ==>
  !id b sz. FLOOKUP t.vs_allocas id = SOME (b,sz) ==>
    FLOOKUP s.vs_allocas id = SOME (b,sz) \/ s.vs_alloca_next <= b
Proof
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[update_var_def, FLOOKUP_UPDATE] >>
  Cases_on `st.cs_next_id = id` >> gvs[]
QED

Theorem abi_valid_allocated_index_effect:
  abi_decode_index_init st = (ip,en) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st /\ st.cs_next_id IN sites /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) (fn_insts func) /\
  en.cs_next_var <= ceiling.cs_next_var /\ fresh_vars_wrt ceiling s ==>
  ?t slot. run_inst_seq (emitted_insts st en) s = OK t /\
    abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var
      sites dstid d outsz s t /\
    fresh_vars_wrt ceiling t /\ eval_operand ip t = SOME (n2w slot) /\
    mload slot t = 0w /\ slot+32 < dimword (:256) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (slot,32)
Proof
  strip_tac >> drule_all abi_malformed_index_resource >>
  disch_then (qspec_then `dstid` strip_assume_tac) >>
  drule abi_decode_index_init_trace >> strip_tac >>
  `32 < dimword (:256)` by
    simp[dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st allocation_st) s = OK allocated` >>
  `eval_operand (Lit 0w) allocated = SOME 0w` by simp[eval_operand_def] >>
  drule_all abi_decode_store_sequence >> strip_tac >>
  `inst_extends allocation_st en /\ inst_extends st allocation_st` by
    metis_tac[inst_extends_emit_void, abi_decode_alloc_buffer_inst_extends] >>
  drule_all run_inst_seq_emit_extend >> strip_tac >>
  `t = mstore (w2n w) 0w allocated` by gvs[] >>
  `!id b sz. FLOOKUP allocated.vs_allocas id = SOME (b,sz) ==>
     FLOOKUP s.vs_allocas id = SOME (b,sz) \/ s.vs_alloca_next <= b` by
    (rpt strip_tac >> irule abi_valid_allocated_buffer_origin >>
     qexistsl_tac [`buf`, `allocation_st`, `32`, `st`, `allocated`] >> simp[]) >>
  qexistsl_tac [`t`, `slot`] >> simp[abi_valid_allocated_effect_def] >>
  simp[abi_valid_allocated_frame_def] >> rpt strip_tac >>
  `abi_malformed_site_range sites s allocated (w2n w) 32` by
    (qpat_x_assum `!id b sz. FLOOKUP allocated.vs_allocas id = _ ==> _` drule >>
     strip_tac
     >- (simp[abi_malformed_site_range_def] >> disj1_tac >>
         qexistsl_tac [`st.cs_next_id`, `w2n w`, `32`] >> simp[]) >>
     simp[abi_malformed_site_range_def] >> disj2_tac >> simp[] >>
     fs[stmt_state_rel_def, alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `a+1 <= w2n w \/ w2n w+32 <= a` by
    (qpat_x_assum `~abi_malformed_site_range _ _ _ _ _` mp_tac >>
     qpat_x_assum `abi_malformed_site_range _ _ _ _ _` mp_tac >>
     simp[abi_malformed_site_range_def, mstore_def, write_memory_with_expansion_def] >>
     rpt strip_tac >> gvs[] >>
     Cases_on `a+1 <= w2n w \/ w2n w+32 <= a` >> simp[] >>
     `w2n w <= a /\ a+1 <= w2n w+32` by decide_tac >> metis_tac[LESS_EQ_TRANS]) >>
  `mem_bytes_at a 1 (mstore (w2n w) 0w allocated).vs_memory =
     mem_bytes_at a 1 allocated.vs_memory` by
    (irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> simp[]) >>
  fs[]
QED

Theorem abi_valid_allocated_array_header_effect:
  abi_decode_array_header dst addr MLOAD st = (cnt,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  32 <= outsz /\ fn_inst_ids_distinct func /\
  eval_operand addr s = SOME a /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\
    fresh_vars_wrt en t /\ eval_operand cnt t = SOME (mload (w2n a) s) /\
    abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var
      sites dstid d outsz s t /\
    mem_word_at d t.vs_memory = mload (w2n a) s /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >> drule_all abi_malformed_init_header_resource >> strip_tac >>
  `eval_operand dst s = SOME (n2w d) /\ d < dimword (:256)` by
    (fs[abi_malformed_entry_def] >> decide_tac) >>
  drule_all abiMalformedBulkArrayTheory.abi_malformed_array_header_exact >> strip_tac >> gvs[] >>
  simp[abi_valid_allocated_effect_def] >>
  conj_tac
  >- (conj_tac
      >- (simp[abi_valid_allocated_frame_def] >> rpt strip_tac >>
          rename1 `mem_bytes_at q 1 t.vs_memory = _` >>
          `q < d \/ d+32 <= q` by decide_tac >>
          qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
          simp[] >> irule abiDecodeStaticPropsTheory.mem_bytes_at_mstore_outside >> simp[]) >>
      qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
      simp[mstore_def, write_memory_with_expansion_def]) >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
  simp[valueEncodingPropsTheory.mstore_mem_word_at_same]
QED

Theorem abi_valid_allocated_array_guard_effect:
  abi_decode_dynarray_position_prefix src MLOAD base_op hi maxn stride st = (addr,en) /\
  run_inst_seq (emitted_insts st en) s = OK t /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s ==>
  abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var
    sites dstid d outsz s t
Proof
  strip_tac >> drule_all abi_malformed_dynarray_prefix_resource >> strip_tac >>
  drule_all abiMalformedBulkArrayTheory.abi_malformed_dynarray_prefix_exact >> strip_tac >>
  simp[abi_valid_allocated_effect_def] >>
  qpat_x_assum `t = _` (fn th => once_rewrite_tac[th]) >>
  simp[abi_valid_allocated_frame_def]
QED

Theorem abi_valid_allocated_effect_weaken:
  abi_valid_allocated_effect ctx func cenv cx es next sites dstid d n s t /\
  earlier <= next ==>
  abi_valid_allocated_effect ctx func cenv cx es earlier sites dstid d n s t
Proof
  simp_tac bool_ss [abi_valid_allocated_effect_def] >> strip_tac >> simp[] >>
  irule abi_malformed_resource_weaken >>
  qexistsl_tac [`next`, `sites`] >> simp[]
QED

Theorem abi_valid_allocated_array_init_fresh_effect:
  abi_decode_array_loop_init dst src MLOAD base_op hi maxn stride st = (setup,en) /\
  abi_malformed_entry ctx func cenv cx es st sites dstid live
    base_op hi src dst B L xs p d outsz s /\
  fn_inst_ids_distinct func /\ fresh_vars_wrt st s /\
  maxn < dimword (:256) /\ 32 <= outsz /\
  n = abi_head_word (DROP p xs) /\ n <= maxn /\ p+32+n*stride <= L /\
  MEM (mk_inst (en.cs_next_id-2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (en.cs_next_var-1))]) (fn_insts func) /\
  en.cs_next_id-2 IN sites ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\
    abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var
      sites dstid d outsz s t /\ mem_word_at d t.vs_memory = n2w n /\
    fresh_vars_wrt en t
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
  drule_all abi_valid_allocated_array_header_effect >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts guard_st header_st) guarded = OK prepared` >>
  `local_ptrs_reserved cenv header_st` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `guard_st` >>
     fs[abi_malformed_entry_def]) >>
  `stmt_state_rel ctx func cenv cx es prepared` by
    fs[abi_valid_allocated_effect_def, abi_malformed_resource_post_def] >>
  `MEM (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString header_st.cs_next_var)]) (fn_insts func) /\
   header_st.cs_next_id IN sites` by
    (qpat_x_assum `MEM _ (fn_insts func)` mp_tac >>
     qpat_x_assum `_ IN sites` mp_tac >> simp[]) >>
  `fresh_vars_wrt en prepared` by
    (irule fresh_vars_wrt_mono >> qexists_tac `header_st` >> simp[GREATER_EQ]) >>
  `en.cs_next_var <= en.cs_next_var` by simp[] >>
  drule_all (Q.INST [`ceiling` |-> `en`, `d` |-> `0`, `outsz` |-> `0`]
    abi_valid_allocated_index_effect) >>
  disch_then (qspec_then `dstid` strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts header_st en) prepared = OK indexed` >>
  suspend "compose"
QED

Resume abi_valid_allocated_array_init_fresh_effect[compose]:
  `abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var
     sites dstid d outsz s guarded` by
    (drule_all abi_valid_allocated_array_guard_effect >> simp[]) >>
  `abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var
     sites dstid d outsz guarded prepared` by
    (irule abi_valid_allocated_effect_weaken >>
     goal_assum (drule_at Any) >> simp[]) >>
  `abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var
     sites dstid d outsz prepared indexed` by
    (irule abi_valid_allocated_effect_weaken >>
     qexists_tac `header_st.cs_next_var` >> simp[] >>
     fs[abi_valid_allocated_effect_def, abi_valid_allocated_frame_def] >> metis_tac[]) >>
  `abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var
     sites dstid d outsz s prepared` by
    (irule abi_valid_allocated_effect_trans >> qexists_tac `guarded` >> simp[]) >>
  `abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var
     sites dstid d outsz s indexed` by
    (irule abi_valid_allocated_effect_trans >> qexists_tac `prepared` >> simp[]) >>
  `run_inst_seq (emitted_insts guard_st en) guarded = OK indexed` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`prepared`, `header_st`] >> simp[]) >>
  `run_inst_seq (emitted_insts st en) s = OK indexed` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`guarded`, `guard_st`] >> simp[] >>
     metis_tac[inst_extends_trans]) >>
  qexists_tac `indexed` >> simp[] >>
  `abi_malformed_destination func cenv es.scopes dstid d outsz prepared /\
   dstid NOTIN sites /\ alloca_inv prepared` by
    (conj_tac
     >- (`abi_malformed_resource_post ctx func cenv cx es st.cs_next_var
            sites dstid s prepared` by fs[abi_valid_allocated_effect_def] >>
         `abi_malformed_destination func cenv es.scopes dstid d outsz s` by
            fs[abi_malformed_entry_def] >>
         drule_all abi_malformed_resource_destination >> simp[]) >>
     fs[abi_malformed_entry_def, abi_valid_allocated_effect_def,
        abi_malformed_resource_post_def, stmt_state_rel_def]) >>
  `mem_bytes_at d 32 indexed.vs_memory = mem_bytes_at d 32 prepared.vs_memory` by
    (`abi_valid_allocated_frame sites 0 0 prepared indexed` by
       fs[abi_valid_allocated_effect_def] >>
     fs[abi_malformed_destination_def] >>
     irule abi_valid_allocated_frame_owned_slice >>
     qpat_assum `abi_valid_allocated_frame sites 0 0 prepared indexed`
       (irule_at Any) >>
     qpat_assum `FLOOKUP prepared.vs_allocas dstid = SOME _` (irule_at Any) >>
     simp[] >> decide_tac) >>
  `mem_word_at d indexed.vs_memory = mem_word_at d prepared.vs_memory` by
    fs[abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
  gvs[abi_decode_load_def, mload_def]
QED
Finalise abi_valid_allocated_array_init_fresh_effect

Theorem abi_valid_allocated_array_init_effect:
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
    abi_valid_allocated_effect ctx func cenv cx es st.cs_next_var
      sites dstid d outsz s t /\ mem_word_at d t.vs_memory = n2w n /\
    fresh_vars_wrt ceiling t /\
    eval_operand (FST setup) t = SOME (n2w slot) /\
    eval_operand (SND setup) t = SOME (n2w n) /\ mload slot t = 0w /\
    slot+32 < dimword (:256) /\
    FLOOKUP t.vs_allocas (en.cs_next_id-2) = SOME (slot,32)
Proof
  strip_tac >> drule_all abi_valid_allocated_array_init_resources >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st en) s = OK actual` >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_reentry_code >> strip_tac >>
  drule abi_malformed_entry_prune >> strip_tac >>
  mp_tac (Q.INST [`s` |-> `abi_decoder_prune_vars st.cs_next_var s`]
    abi_valid_allocated_array_init_fresh_effect) >>
  (impl_tac >- simp[abi_decoder_prune_fresh]) >> strip_tac >>
  rename1 `run_inst_seq _ (abi_decoder_prune_vars _ _) = OK clean` >>
  `fresh_vars_wrt ceiling clean` by
    (irule fresh_vars_wrt_mono >> qexists_tac `en` >> simp[GREATER_EQ]) >>
  drule_all abi_decoder_sequence_runtime_reentry >> strip_tac >> gvs[] >>
  simp[abi_valid_allocated_effect_def] >>
  fs[abi_valid_allocated_effect_def, abi_valid_allocated_frame_def,
     abi_malformed_site_range_def, abi_decoder_prune_vars_def] >>
  metis_tac[]
QED
