(* Actual-site resources at the nonbulk source-array constructor boundary. *)
Theory sourceOwnedArrayConstructorPtr
Ancestors
  sourceOwnedArrayLoopPtr decoderArrayInitPtr physicalArrayInitSequence
  calldataRecursiveProducers sourceEncodingWindows sourceEncodingLayout abiDecoderCoherence
  ctorAbiActualArrayRun entrySinkExtraction fragExec
  abiDecoderRecursiveArray abiDecoderLoop abiDecoderArraySetupCode abiDecoderLoopRegisters
  bodyPtrDefs ptrSafeRun ptrDiscipline allocaBudgetProps
  actualAllocaReplayPtr actualDecoderAllocationPtr actualAllocExec vyperCompiler allocaFrontierBound
  calldataDynInit calldataDynOwned abiDecoderRecursiveArray abiDecoderRecursiveLoopLayout
  abiDecoderArrayInit abiDecoderArrayInitExec abiDecoderArrayLoopInit abiDecoderIndexInit
  abiDecoderReentry abiDecoderFrame abiDecoderFrameCompose
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderArrayHeader
  abiDecoderGuards abiDecoderGuard ctorAbiActualAlloc
  emitHelperProps emitHelper exprLowering exprLoweringProps abiDecoderContract
  rich_list context compileEnv venomState venomInst
  venomExecSemantics venomMemDefs venomMemProofs valueEncoding valueEncodingProofs venomWf finite_map words list arithmetic

(* Initialization writes only its own registers, so freshness at the eventual
   decoder limit is preserved, not merely freshness at the initializer limit. *)
Theorem array_loop_init_future_fresh:
  abi_decode_array_loop_init dst src opc hi maxn abi_sz sa = (setup,sb) /\
  abi_decode_source_opcode opc /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  sb.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s ==>
  fresh_vars_wrt limit t
Proof
  strip_tac >>
  `!n. sb.cs_next_var <= n ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\
      ~MEM (STRING #"%" (toString n)) i.inst_outputs)
      (emitted_insts sa sb)` by
    (qpat_x_assum `abi_decode_array_loop_init _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `abi_decode_source_opcode opc` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `hi = Lit 0w` >>
     simp[abi_decode_array_loop_init_def, abi_decode_dynarray_prefix_def,
       abi_decode_count_guard_def, abi_decode_dynarray_end_guard_def,
       abi_decode_dynarray_end_def, abi_decode_le_guard_def,
       abi_decode_array_header_def, abi_decode_index_init_def,
       compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >>
     rpt (pairarg_tac >> gvs[]) >>
     rpt strip_tac >>
     gvs[] >>
     pure_rewrite_tac [emitted_insts_def] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
     simp_tac std_ss [DROP_LENGTH_APPEND] >>
     fs[abi_decode_source_opcode_def] >>
     simp_tac (srw_ss()) [DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def,
       ASCIInumbersTheory.toString_inj] >> decide_tac) >>
  `!n. limit.cs_next_var <= n ==>
    lookup_var (STRING #"%" (toString n)) t =
    lookup_var (STRING #"%" (toString n)) s` by
    (rpt strip_tac >> irule ctor_actual_sequence_var_frame >>
     goal_assum (drule_at Any) >> first_x_assum irule >> decide_tac) >>
  fs[fresh_vars_wrt_def, lookup_var_def, FLOOKUP_DEF] >> gvs[]
QED


Theorem physical_index_init_repeat[local]:
  abi_decode_index_init st = (ip,en) /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
      p = s.vs_alloca_next /\ p+32 < dimword (:256)) \/
   (FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,32) /\
      p+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256))) ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    abi_decode_frame p 32 s t /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_alloca_next = (if FLOOKUP s.vs_allocas st.cs_next_id = NONE
      then s.vs_alloca_next+32 else s.vs_alloca_next) /\
    t.vs_halted = s.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule calldata_index_init_instructions >> strip_tac >>
  `p < dimword (:256)` by (gvs[] >> decide_tac) >>
  `?allocated. step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
    eval_operand ip allocated = SOME (n2w p) /\
    FLOOKUP allocated.vs_allocas st.cs_next_id = SOME (p,32) /\
    (!id. id <> st.cs_next_id ==>
      FLOOKUP allocated.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    allocated.vs_alloca_next = (if FLOOKUP s.vs_allocas st.cs_next_id = NONE
      then s.vs_alloca_next+32 else s.vs_alloca_next) /\
    allocated.vs_halted = s.vs_halted` by
    (qpat_x_assum `(_ /\ p = _ /\ _) \/ _` strip_assume_tac
     >- (mp_tac (Q.INST [`inst` |-> `mk_inst st.cs_next_id ALLOCA [Lit 32w]
           [STRING #"%" (toString st.cs_next_var)]`,
           `out` |-> `STRING #"%" (toString st.cs_next_var)`]
           physical_word_alloca_fresh_run) >>
         impl_tac >- simp[mk_inst_def] >> strip_tac >>
         goal_assum (drule_at Any) >>
         gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE, mk_inst_def]) >>
     mp_tac (Q.INST [`inst` |-> `mk_inst st.cs_next_id ALLOCA [Lit 32w]
         [STRING #"%" (toString st.cs_next_var)]`,
         `out` |-> `STRING #"%" (toString st.cs_next_var)`, `insts` |-> `[]`]
         actual_word_alloca_reuse_run) >>
     impl_tac >- simp[mk_inst_def] >> strip_tac >>
     goal_assum (drule_at Any) >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE, mk_inst_def]) >>
  drule_all calldata_index_init_after_alloca >> strip_tac >>
  drule calldata_index_init_repeat_memory_frame >>
  disch_then (qspec_then `p` assume_tac) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op (mstore p 0w allocated) = eval_operand op s` by
    metis_tac[calldata_index_init_live_frame] >>
  qexists_tac `mstore p 0w allocated` >>
  gvs[mstore_def, write_memory_with_expansion_def]
QED

Theorem calldata_array_loop_init_repeat_physical_sequence:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    (setup,loop_st) /\
  eval_operand src s = SOME (n2w cdsbase) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load CALLDATALOAD (n2w cdsbase:bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  loop_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  ((FLOOKUP s.vs_allocas (loop_st.cs_next_id-2) = NONE /\
      p = s.vs_alloca_next /\ p+32 < dimword (:256)) \/
   (FLOOKUP s.vs_allocas (loop_st.cs_next_id-2) = SOME (p,32) /\
      p+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256))) /\
  (d+32 <= p \/ p+32 <= d) ==>
  ?t. run_inst_seq (emitted_insts st loop_st) s = OK t /\
    eval_operand (FST setup) t = SOME (n2w p) /\
    eval_operand (SND setup) t = SOME (n2w n) /\
    mload p t = 0w /\ mem_word_at d t.vs_memory = n2w n /\
    fresh_vars_wrt limit t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    abi_decode_footprint_frame [(d,32);(p,32)] s t /\
    FLOOKUP t.vs_allocas (loop_st.cs_next_id-2) = SOME (p,32) /\
    (!id. id <> loop_st.cs_next_id-2 ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_alloca_next = (if FLOOKUP s.vs_allocas (loop_st.cs_next_id-2) = NONE
      then s.vs_alloca_next+32 else s.vs_alloca_next) /\
    t.vs_halted = s.vs_halted /\ inst_extends st loop_st
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decode_array_loop_init_trace >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `?count_op. abi_decode_count_guard CALLDATALOAD src maxn st = (count_op,guard_st)` by
    (qpat_x_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_dynarray_prefix_def, abi_decode_dynarray_end_guard_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[]) >>
  `w2n (abi_decode_load CALLDATALOAD (n2w cdsbase:bytes32) s) <= maxn` by
    simp[wordsTheory.w2n_n2w] >>
  drule_all calldata_count_guard_repeat_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st guard_st) s = OK guarded` >>
  `eval_operand src guarded = SOME (n2w cdsbase) /\
    eval_operand dst guarded = SOME (n2w d) /\
    abi_decoder_operand_live guard_st.cs_next_var dst` by
    metis_tac[abi_decoder_operand_live_mono] >>
  drule_all calldata_array_header_repeat_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts guard_st header_st) guarded = OK prepared` >>
  `abi_decode_load CALLDATALOAD (n2w cdsbase:bytes32) guarded = n2w n` by
    gvs[abi_decode_load_def, abi_decode_source_def] >>
  `abi_decode_frame d 32 s prepared` by
    (gvs[abi_decode_frame_def] >> metis_tac[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op prepared = eval_operand op s` by
    metis_tac[abi_decoder_operand_live_mono] >>
  `run_inst_seq (emitted_insts st header_st) s = OK prepared /\
    inst_extends st header_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`guarded`,`guard_st`] >> simp[]) >>
  `loop_st.cs_next_id-2 = header_st.cs_next_id` by decide_tac >>
  qpat_x_assum `loop_st.cs_next_id = header_st.cs_next_id+2` kall_tac >>
  `((FLOOKUP prepared.vs_allocas header_st.cs_next_id = NONE /\
      p = prepared.vs_alloca_next /\ p+32 < dimword (:256)) \/
    (FLOOKUP prepared.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p+32 <= prepared.vs_alloca_next /\ prepared.vs_alloca_next < dimword (:256)))` by
    metis_tac[] >>
  drule physical_index_init_repeat >>
  disch_then (qspecl_then [`prepared`,`p`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts header_st loop_st) prepared = OK actual` >>
  `abi_decoder_operand_live header_st.cs_next_var cnt` by
    (qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abi_decode_array_header_def, emit_op_def, emit_void_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_inst_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def]) >>
  `eval_operand cnt actual = SOME (n2w n)` by metis_tac[] >>
  `mem_word_at d actual.vs_memory = n2w n` by
    (irule EQ_TRANS >> qexists_tac `mem_word_at d prepared.vs_memory` >>
     conj_tac >- (irule abi_decode_frame_mem_word >>
       qexistsl_tac [`p`,`32`] >> simp[]) >> simp[]) >>
  `run_inst_seq (emitted_insts st loop_st) s = OK actual /\
    inst_extends st loop_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`prepared`,`header_st`] >> simp[]) >>
  `fresh_vars_wrt limit actual` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`abi_decode_array_loop_init _ _ _ _ _ _ st = _`,
        `abi_decode_source_opcode CALLDATALOAD`,
        `run_inst_seq (emitted_insts st loop_st) s = OK actual`,
        `loop_st.cs_next_var <= limit.cs_next_var`, `fresh_vars_wrt limit s`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[array_loop_init_future_fresh]) >>
  `abi_decode_footprint_frame [(d,32);(p,32)] s actual` by
    (irule abi_decoder_array_init_exact_frame >> goal_assum (drule_at Any) >> simp[]) >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op actual = eval_operand op s` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`!op. abi_decoder_operand_live header_st.cs_next_var op ==> _`,
       `!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op prepared = _`,
       `st.cs_next_var <= guard_st.cs_next_var`,
       `header_st.cs_next_var = guard_st.cs_next_var+1`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     `st.cs_next_var <= header_st.cs_next_var` by decide_tac >>
     metis_tac[abi_decoder_operand_live_mono]) >>
  qexists_tac `actual` >> gvs[]
QED

(* Obtain the physical initializer state from actual-site resources, including
   replay.  The owner is outside the whole decoder's scratch interval. *)
Theorem source_array_init_owned_sequence:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_index_init index_st = (ip,loop_st) /\
  (!ins. MEM ins (emitted_insts index_st loop_st) ==> MEM ins (fn_insts fn)) /\
  st.cs_next_id <= index_st.cs_next_id /\ index_st.cs_next_id < last.cs_next_id /\
  loop_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  eval_operand src s = SOME (n2w cdsbase) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load CALLDATALOAD (n2w cdsbase:bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ d+32 <= base_addr+owner_cap /\
  (!id p k. st.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) ==>
  ?t p.
    run_inst_seq (emitted_insts st loop_st) s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ eval_operand cnt t = SOME (n2w n) /\
    mload p t = 0w /\ mem_word_at d t.vs_memory = n2w n /\
    fresh_vars_wrt limit t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    abi_decode_footprint_frame [(d,32);(p,32)] s t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
    FLOOKUP t.vs_allocas index_st.cs_next_id = SOME (p,32) /\
    p+32 < dimword (:256) /\
    (p+32 <= base_addr \/ base_addr+owner_cap <= p) /\
    (!id b k. FLOOKUP s.vs_allocas id = SOME (b,k) ==>
      FLOOKUP t.vs_allocas id = SOME (b,k)) /\
    (!id. id <> index_st.cs_next_id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_halted = s.vs_halted /\ inst_extends st loop_st
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule actual_index_init_literal_site >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[] >>
  `alloca_size inst = 32` by
    (qpat_assum `inst.inst_operands = _` mp_tac >>
     qpat_assum `inst.inst_opcode = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     simp[alloca_size_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]) >>
  `!entry. FLOOKUP s.vs_allocas inst.inst_id = SOME entry ==>
    ?p. entry = (p,32) /\ p+32 <= s.vs_alloca_next` by
    (rpt strip_tac >> PairCases_on `entry` >>
     qpat_x_assum `!id p k. _` (qspecl_then [`inst.inst_id`,`entry0`,`entry1`] mp_tac) >>
     impl_tac >- metis_tac[] >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
  drule_all actual_word_alloca_physical_credit >> disch_tac >>
  `index_st.cs_next_id = loop_st.cs_next_id-2` by
    (drule abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
  `oid <> index_st.cs_next_id` by decide_tac >>
  suspend "physical_run"
QED

Resume source_array_init_owned_sequence[physical_run]:
  `s.vs_alloca_next < dimword (:256)` by
    (drule alloca_frontier_inv_bound >> decide_tac) >>
  `base_addr+owner_cap <= s.vs_alloca_next` by
    (qpat_assum `alloca_inv s` mp_tac >>
     qpat_assum `FLOOKUP s.vs_allocas oid = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `?p. ((FLOOKUP s.vs_allocas (loop_st.cs_next_id-2) = NONE /\
       p = s.vs_alloca_next /\ p+32 < dimword (:256)) \/
      (FLOOKUP s.vs_allocas (loop_st.cs_next_id-2) = SOME (p,32) /\
       p+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256))) /\
    p+32 < dimword (:256) /\
    (p+32 <= base_addr \/ base_addr+owner_cap <= p)` by
    (qpat_x_assum `(_ /\ _) \/ (?p. _)` strip_assume_tac
     >- (qexists_tac `s.vs_alloca_next` >>
         simp_tac (srw_ss()) [] >> metis_tac[]) >>
     qexists_tac `p` >>
     `p+32 <= base_addr \/ base_addr+owner_cap <= p` by
       (qpat_assum `alloca_inv s` mp_tac >>
        qpat_assum `FLOOKUP s.vs_allocas oid = _` mp_tac >>
        qpat_assum `FLOOKUP s.vs_allocas inst.inst_id = _` mp_tac >>
        qpat_assum `oid <> index_st.cs_next_id` mp_tac >>
        qpat_assum `inst.inst_id = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >>
        simp_tac bool_ss [alloca_inv_def, allocas_non_overlapping_def] >> metis_tac[]) >>
     simp_tac (srw_ss()) [] >> metis_tac[LESS_EQ_LESS_TRANS]) >>
  pop_assum strip_assume_tac >>
  `d < dimword (:256) /\ (d+32 <= p \/ p+32 <= d)` by decide_tac >>
  mp_tac (Q.INST [`p` |-> `p`, `limit` |-> `limit`, `s` |-> `s`, `setup` |-> `(ip,cnt)`]
    calldata_array_loop_init_repeat_physical_sequence) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> metis_tac[])) >>
  strip_tac >>
  `((FLOOKUP s.vs_allocas index_st.cs_next_id = NONE /\ p = s.vs_alloca_next) \/
    (FLOOKUP s.vs_allocas index_st.cs_next_id = SOME (p,32) /\
     p < dimword (:256) /\ p+32 <= s.vs_alloca_next))` by
    (asm_simp_tac bool_ss [] >> metis_tac[LESS_EQ_LESS_TRANS, DECIDE ``p <= p+32``]) >>
  `FLOOKUP t.vs_allocas index_st.cs_next_id = SOME (p,32) /\
    (!id. id <> index_st.cs_next_id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (if FLOOKUP s.vs_allocas index_st.cs_next_id = NONE then
      t.vs_alloca_next = s.vs_alloca_next+32 else
      t.vs_alloca_next = s.vs_alloca_next)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`index_st.cs_next_id = _`,
        `FLOOKUP t.vs_allocas (loop_st.cs_next_id-2) = _`,
        `!id. id <> loop_st.cs_next_id-2 ==> _`, `t.vs_alloca_next = _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[] >> Cases_on `FLOOKUP s.vs_allocas (loop_st.cs_next_id-2) = NONE` >> simp[]) >>
  mp_tac (Q.INST [`st` |-> `index_st`, `st'` |-> `loop_st`, `p` |-> `p`, `t` |-> `t`]
    calldata_index_init_owned_fields) >>
  (impl_tac >- (asm_simp_tac bool_ss [] >> metis_tac[])) >> strip_tac >>
  qexistsl_tac [`t`,`p`] >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`run_inst_seq (emitted_insts st loop_st) s = OK t`,
     `eval_operand (FST (ip,cnt)) t = _`, `eval_operand (SND (ip,cnt)) t = _`,
     `mload p t = _`, `mem_word_at d t.vs_memory = _`, `fresh_vars_wrt limit t`,
     `!op. abi_decoder_operand_live st.cs_next_var op ==> _`,
     `abi_decode_footprint_frame [(d,32);(p,32)] s t`,
     `alloca_inv t`, `alloca_frontier_inv ctx fn site t`,
     `s.vs_alloca_next <= t.vs_alloca_next`,
     `FLOOKUP s.vs_allocas oid = _`, `oid <> index_st.cs_next_id`,
     `!id b cap. FLOOKUP s.vs_allocas id = SOME (b,cap) ==> FLOOKUP t.vs_allocas id = _`,
     `FLOOKUP t.vs_allocas index_st.cs_next_id = _`,
     `p+32 < dimword (:256)`,
     `!id. id <> index_st.cs_next_id ==> _`,
     `t.vs_halted = s.vs_halted`, `inst_extends st loop_st`] >>
  (Q.SUBGOAL_THEN `p+32 <= base_addr \/ base_addr+owner_cap <= p` mp_tac
    >- metis_tac[]) >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt disch_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [pairTheory.FST, pairTheory.SND]) >>
  asm_simp_tac bool_ss [] >> metis_tac[]
QED

Finalise source_array_init_owned_sequence

Theorem source_owned_nonbulk_array_ptr:
  (!middle end_st i r G tn child childsrc e srcpos.
    i < LENGTH xs /\
    compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w)
      (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
    abi_decoder_coherent ce env sf ty tv /\ value_has_type tv (EL i xs) /\
    vyper_to_abi env ty (EL i xs) = SOME (EL i avs) /\
    mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)))
      r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) (EL i avs) /\
    srcpos + LENGTH (enc (vyper_to_abi_type env ty) (EL i avs)) < dimword (:256) /\
    eval_operand childsrc r = SOME (n2w srcpos) /\
    lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
    abi_decoder_operand_live middle.cs_next_var childsrc /\
    abi_decoder_operand_live middle.cs_next_var (Var child) /\
    abi_decoder_operand_live middle.cs_next_var (Var root) /\
    ptr_covers G tn child r (type_memory_size tv) /\
    ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
    alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
    unit_alloca_budget ctx < dimword (:256) /\
    FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
    base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
    e + type_memory_size tv < dimword (:256) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
    (middle.cs_blocks = end_st.cs_blocks \/
      !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
    end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
    allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
    r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
    ?t H u fp.
      abi_decode_sim ctx fn r t /\
      ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
      t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
      val_in_memory tv (EL i xs) e t.vs_memory /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory tv (EL i xs) e mem) /\
      abi_decode_footprint_frame ((e,type_memory_size tv)::fp) r t /\
      abi_footprint_disjoint base_addr owner_cap fp /\
      alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
      r.vs_alloca_next <= t.vs_alloca_next /\
      FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
      (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
        FLOOKUP t.vs_allocas id = SOME (p,k)) /\
      (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
      (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (p,k) ==>
        k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      (!p k. MEM (p,k) fp ==> ?id. middle.cs_next_id <= id /\
        id < end_st.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (p,k)) /\
      ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
      (!op. abi_decoder_operand_live middle.cs_next_var op ==>
        eval_operand op t = eval_operand op r) /\
      (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x)) /\
      u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
      u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
        !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r)) ==>
  !s G tn st last.
    compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w)
      (DecDynArray (type_to_abi_dec_info sf ce ty)
        (abi_embedded_static_size ce.ce_struct_fields ty)
        (type_memory_size tv) dyn maxn) st = ((),last) /\
    (dyn \/ dec_info_needs_clamp (type_to_abi_dec_info sf ce ty)) /\
    LENGTH xs <= maxn /\ maxn < dimword (:256) /\
    outsz = 32 + maxn * type_memory_size tv /\
    abi_decoder_coherent ce env sf ty tv /\ 0 < type_slot_size tv /\
    EVERY (value_has_type tv) xs /\ vyper_to_abi_same env ty xs = SOME avs /\
    LIST_REL (\aty av. ~is_dynamic aty ==>
      LENGTH (enc aty av) = abi_member_head_size aty)
      (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs /\
    mem_bytes_at cdsbase
      (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
      s.vs_call_ctx.cc_calldata =
      enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
    cdsbase + LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))
      < dimword (:256) /\
    fn_has_code st last fn /\ fn_inst_ids_distinct fn /\
    (!bb. lookup_block last.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
    last.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var (Var root) /\
    eval_operand src s = SOME (n2w cdsbase) /\ lookup_var root s = SOME (n2w d) /\
    alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
    unit_alloca_budget ctx < dimword (:256) /\
    FLOOKUP s.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
    base_addr <= d /\ d+outsz <= base_addr+owner_cap /\ d+outsz < dimword (:256) /\
    (!id p k. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP s.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= s.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    ptr_covers G tn root s outsz /\ op_taint tn src = {} /\ op_prov G src = NONE /\
    allocas_from lower s /\ lower <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?t H u fp.
      abi_decode_sim ctx fn s t /\
      ~t.vs_halted /\ t.vs_current_bb = last.cs_current_bb /\
      t.vs_inst_idx = LENGTH last.cs_current_insts /\
      val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d t.vs_memory /\
      (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
        val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV xs)) d mem) /\
      abi_decode_footprint_frame ((d,outsz)::fp) s t /\
      abi_footprint_disjoint base_addr owner_cap fp /\
      alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
      s.vs_alloca_next <= t.vs_alloca_next /\ fresh_vars_wrt limit t /\
      FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
      (!id p k. FLOOKUP s.vs_allocas id = SOME (p,k) ==> FLOOKUP t.vs_allocas id = SOME (p,k)) /\
      (!id. id < st.cs_next_id \/ last.cs_next_id <= id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
      (!id p k. st.cs_next_id <= id /\ id < last.cs_next_id /\
        FLOOKUP t.vs_allocas id = SOME (p,k) ==>
        k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      (!p k. MEM (p,k) fp ==> ?id. st.cs_next_id <= id /\
        id < last.cs_next_id /\ FLOOKUP t.vs_allocas id = SOME (p,k)) /\
      ptr_covers H u root t outsz /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
      (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x)) /\
      u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
        !fuel. ptr_safe_run D lower fuel ctx fn PG G tn s)
Proof
  disch_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_nonbulk_parent_shell >> strip_tac >>
  suspend "initialize"
QED

Resume source_owned_nonbulk_array_ptr[initialize]:
  `LENGTH avs = LENGTH xs` by
    (qpat_assum `vyper_to_abi_same env ty xs = SOME avs` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp_tac bool_ss [vyperABIRoundtripTheory.vyper_to_abi_same_OPT_MMAP] >>
     metis_tac[vyperTypeABITheory.OPT_MMAP_LENGTH]) >>
  `abi_decode_load CALLDATALOAD (n2w cdsbase:bytes32) s = n2w (LENGTH xs)` by
    (qsuff_tac `abi_decode_load CALLDATALOAD (n2w cdsbase:bytes32) s = n2w (LENGTH avs)`
     >- metis_tac[] >>
     irule abiCanonicalHeadSizeTheory.canonical_dynamic_array_count_load >>
     simp_tac bool_ss [abi_decode_source_def] >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  `cs_extends loop_st st0 /\ cs_extends middle st1` by
    (conj_tac
     >- (irule abiDecoderLoopCodeTheory.abi_decoder_loop_prefix_extends >>
         goal_assum (drule_at Any)) >>
     irule abiDecoderAppendTheory.cs_extends_abi_decode >>
     goal_assum (drule_at Any)) >>
  `st0.cs_next_var <= middle.cs_next_var` by
    metis_tac[abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_operands] >>
  (* Compiler boundaries and actual initialization resources. *)
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  `middle.cs_next_var <= st1.cs_next_var` by
    metis_tac[abiDecoderCountersTheory.abi_decoder_variable_counter] >>
  `last.cs_next_var = st1.cs_next_var+1` by
    (qpat_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     qpat_assum `FST ops = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> qpat_x_assum `FST ops = _` SUBST_ALL_TAC >>
     drule abi_decoder_loop_suffix_facts >> simp_tac bool_ss [] >> metis_tac[]) >>
  `loop_st.cs_next_var <= limit.cs_next_var` by decide_tac >>
  `32 <= outsz /\ d+32 <= base_addr+owner_cap` by decide_tac >>
  `eval_operand (Var root) s = SOME (n2w d)` by simp[eval_operand_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    (irule ctorAbiActualArrayRunTheory.ctor_actual_function_ids >> first_assum ACCEPT_TAC) >>
  `header_st.cs_next_id < last.cs_next_id` by decide_tac >>
  drule_all source_array_init_owned_sequence >> strip_tac >>
  (* Attach ghosts to this exact successful physical trace. *)
  `not_fresh_at st root /\ (!x. src = Var x ==> not_fresh_at st x)` by
    (conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     rpt strip_tac >> irule (iffLR calldata_operand_live_not_fresh) >> metis_tac[]) >>
  `d < dimword (:256)` by decide_tac >>
  drule actual_index_init_literal_site >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[] >>
  `alloca_size inst = 32` by
    (qpat_assum `inst.inst_opcode = _` mp_tac >>
     qpat_assum `inst.inst_operands = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> simp[alloca_size_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]) >>
  `!entry. FLOOKUP s.vs_allocas inst.inst_id = SOME entry ==>
    ?b. entry = (b,32) /\ b+32 <= s.vs_alloca_next` by
    (rpt strip_tac >> PairCases_on `entry` >>
     qpat_assum `!id p k. st.cs_next_id <= id /\ _ ==> _` (qspecl_then [`inst.inst_id`,`entry0`,`entry1`] mp_tac) >>
     impl_tac >- metis_tac[] >> simp_tac (srw_ss()) [] >> metis_tac[]) >>
  drule_all actual_word_alloca_physical_credit >> disch_tac >>
  `header_st.cs_next_id = loop_st.cs_next_id-2` by
    (drule abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
  (Q.SUBGOAL_THEN
    `((FLOOKUP s.vs_allocas (loop_st.cs_next_id-2) = NONE /\
       s.vs_alloca_next+32 < dimword (:256)) \/
      (?b. FLOOKUP s.vs_allocas (loop_st.cs_next_id-2) = SOME (b,32) /\
       b+32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256)))`
    assume_tac >-
      (qpat_assum `(_ /\ _) \/ (?b. _)` mp_tac >>
       qpat_assum `inst.inst_id = _` mp_tac >>
       qpat_assum `header_st.cs_next_id = _` mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])) >>
  drule_all actual_array_init_endpoint_ptr_core >>
  disch_then (qspecl_then [`ARB`,`ctx`,`\g r. F`,`PG`] strip_assume_tac) >>
  (* Identify the ghost index slot and prepare header entry. *)
  `p' = p` by
    (qpat_assum `eval_operand (FST (ip,cnt)) t = _` mp_tac >>
     qpat_assum `eval_operand ip t = _` mp_tac >>
     qpat_assum `p+32 < dimword (:256)` mp_tac >>
     qpat_assum `p'+32 < dimword (:256)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp_tac (srw_ss()) [] >>
     rpt strip_tac >>
     `p < dimword (:256) /\ p' < dimword (:256)` by decide_tac >>
     gvs[LESS_MOD]) >>
  qpat_x_assum `p' = p` SUBST_ALL_TAC >>
  `ip = Var q` by
    (qpat_assum `FST (ip,cnt) = Var q` mp_tac >>
     simp_tac bool_ss [pairTheory.FST]) >>
  (* Installed loop entry code. *)
  `labels = (FST labels,FST (SND labels),SND (SND labels))` by simp[] >>
  `abi_decode_loop_prefix ip src CALLDATALOAD loop_st =
     ((FST labels,FST (SND labels),SND (SND labels)),st0)` by
    (qpat_assum `abi_decode_loop_prefix _ _ _ _ = _` mp_tac >>
     qpat_assum `labels = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[]) >>
  drule_all calldata_loop_prefix_entry_code >> strip_tac >>
  (* Ordinary control frame and normalized initializer PC. *)
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule_all run_inst_seq_preserves_entry_control >> simp_tac bool_ss []) >>
  (* Normalize physical and ghost program counters. *)
  qmatch_asmsub_abbrev_tac `ptr_covers H u root init outsz` >>
  `init = t with vs_inst_idx := LENGTH loop_st.cs_current_insts` by
    (qpat_assum `Abbrev (init = _)` mp_tac >>
     qpat_assum `inst_extends st loop_st` mp_tac >>
     qpat_assum `s.vs_inst_idx = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def, inst_extends_def, emitted_insts_def, LENGTH_DROP] >>
     rpt strip_tac >>
     `LENGTH st.cs_current_insts <= LENGTH loop_st.cs_current_insts` by
       (qpat_x_assum `loop_st.cs_current_insts = _` (mp_tac o AP_TERM ``LENGTH : instruction list -> num``) >> simp[] >> decide_tac) >>
     simp[]) >>
  (* Jump from the exact initialized state to the loop header. *)
  `init.vs_current_bb = loop_st.cs_current_bb /\
   init.vs_inst_idx = LENGTH loop_st.cs_current_insts /\ ~init.vs_halted` by
    (qpat_assum `init = t with vs_inst_idx := _` mp_tac >>
     qpat_assum `t.vs_current_bb = s.vs_current_bb` mp_tac >>
     qpat_assum `s.vs_current_bb = _` mp_tac >>
     qpat_assum `loop_st.cs_current_bb = st.cs_current_bb` mp_tac >>
     qpat_assum `t.vs_halted = s.vs_halted` mp_tac >>
     qpat_assum `~s.vs_halted` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[]) >>
  `abi_decode_sim ctx fn init (jump_to (FST labels) init)` by
    (irule abiDecoderPrimitiveLoopEntryTheory.abi_decoder_loop_entry_sim >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists `hb` >> asm_rewrite_tac []) >>
     qexistsl [`bb`,`loop_st.cs_next_id`,`loop_st.cs_current_insts`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `init.vs_current_bb = _` (fn th => rewrite_tac [th]) >>
     first_assum ACCEPT_TAC) >>
  (* Robust initialized array count. *)
  qpat_x_assum `labels = (FST labels,_)` kall_tac >>
  `!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
    mem_word_at d mem = n2w (LENGTH xs)` by
    (rpt strip_tac >>
     `mem_bytes_at d 32 mem = mem_bytes_at d 32 t.vs_memory` by
       (qpat_assum `mem_agree_outside u.t_mem _ _` mp_tac >>
        qpat_assum `u.t_mem = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
        rpt strip_tac >> irule LIST_EQ >> simp[EL_mem_bytes_at] >>
        rpt strip_tac >> rename1 `i < 32` >>
        `d+i NOTIN u.t_mem` by simp[] >>
        `mem_bytes_at (d+i) 1 t.vs_memory = mem_bytes_at (d+i) 1 mem` by
          fs[mem_agree_outside_def] >>
        pop_assum (mp_tac o Q.AP_TERM `EL 0`) >> simp[EL_mem_bytes_at]) >>
     qpat_assum `mem_word_at d t.vs_memory = _` mp_tac >>
     qpat_assum `mem_bytes_at d 32 mem = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[mem_word_at_def, GSYM mem_bytes_at_def]) >>
  (* Transport coverage to the same header state. *)
  qmatch_asmsub_abbrev_tac `abi_decode_sim ctx fn init h` >>
  `h.vs_memory = t.vs_memory /\ h.vs_call_ctx = t.vs_call_ctx /\
   h.vs_allocas = t.vs_allocas /\ h.vs_alloca_next = t.vs_alloca_next /\
   h.vs_current_bb = FST labels /\ h.vs_inst_idx = 0 /\ ~h.vs_halted /\
   (!x. lookup_var x h = lookup_var x t)` by
    (qpat_assum `Abbrev (h = _)` mp_tac >>
     qpat_assum `init = t with vs_inst_idx := _` mp_tac >>
     qpat_assum `~init.vs_halted` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def, jump_to_def, lookup_var_def] >>
     rpt strip_tac >> gvs[]) >>
  `ptr_covers H u root h outsz /\ ptr_covers H u q h 32` by
    (conj_tac >> irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     goal_assum (drule_at Any) >>
     qpat_assum `!x. lookup_var x h = _` mp_tac >>
     qpat_assum `init = t with vs_inst_idx := _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def]) >>
  suspend "loop_preconditions"
QED

Resume source_owned_nonbulk_array_ptr[loop_preconditions]:
  markerLib.RESUME_TAC >>
  `cs_extends st0 middle` by
    (drule_all abiDecoderArraySetupInputsTheory.abi_decode_array_element_setup_shape >>
     strip_tac >> irule cs_extends_same_block >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  `cs_extends st1 last` by
    (qpat_assum `abi_decode_loop_suffix _ _ _ _ _ = _` mp_tac >>
     qpat_assum `FST ops = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> qpat_x_assum `FST ops = _` SUBST_ALL_TAC >>
     drule abiDecoderLoopCodeTheory.abi_decoder_loop_suffix_extends >> simp_tac bool_ss []) >>
  `cs_extends st st0` by
    (irule cs_extends_trans >> qexists `loop_st` >>
     conj_tac >- (irule cs_extends_same_block >>
       conj_tac >- first_assum ACCEPT_TAC >>
       conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  `cs_extends st0 st1` by
    (irule cs_extends_trans >> qexists `middle` >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  `fn_has_code st0 st1 fn` by
    (qpat_assum `cs_extends st st0` mp_tac >>
     qpat_assum `cs_extends st0 st1` mp_tac >>
     qpat_assum `cs_extends st1 last` mp_tac >>
     qpat_assum `fn_has_code st last fn` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[fn_has_code_mid]) >>
  suspend "loop_code"
QED

Resume source_owned_nonbulk_array_ptr[loop_code]:
  markerLib.RESUME_TAC >>
  `abi_decode_loop_cfg fn (FST labels) (FST (SND labels)) (SND (SND labels))
    (loop_st.cs_next_id+1) (Var q) src CALLDATALOAD
    (STRING #"%" (toString loop_st.cs_next_var))
    (STRING #"%" (toString (loop_st.cs_next_var+1)))
    (STRING #"%" (toString (loop_st.cs_next_var+2)))
    (STRING #"%" (toString (loop_st.cs_next_var+3)))` by
    (rewrite_tac[abiDecoderExecutionTheory.abi_decode_loop_cfg_def] >>
     qpat_assum `ip = Var q` (fn th => rewrite_tac [GSYM th]) >>
     qpat_assum `st0.cs_current_bb = FST (SND labels)`
       (fn th => rewrite_tac [GSYM th]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qpat_assum `lookup_block (FST labels) fn.fn_blocks = SOME <| bb_label := _; bb_instructions := _ |>` mp_tac >>
        qpat_assum `st0.cs_current_bb = FST (SND labels)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     conj_tac >- (qexists `body_bb` >>
       conj_tac >- (qpat_assum `st0.cs_current_bb = FST (SND labels)`
         (fn th => rewrite_tac [th]) >> first_assum ACCEPT_TAC) >>
       first_assum ACCEPT_TAC) >>
     qexists `exit_bb` >> conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  suspend "loop_frames"
QED

Resume source_owned_nonbulk_array_ptr[loop_frames]:
  markerLib.RESUME_TAC >>
  `abi_decoder_operand_live loop_st.cs_next_var src /\
   abi_decoder_operand_live loop_st.cs_next_var (Var root)` by
    (conj_tac >> irule abiDecoderReentryTheory.abi_decoder_operand_live_mono >>
     goal_assum (drule_at Any) >> first_assum ACCEPT_TAC) >>
  `abi_decoder_operand_live loop_st.cs_next_var (Var q)` by
    (qpat_assum `abi_decode_index_init header_st = _` mp_tac >>
     qpat_assum `ip = Var q` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> drule abi_decode_index_init_shape >> strip_tac >>
     gvs[abi_decoder_operand_live_def, not_fresh_at_def] >>
     simp[abi_decoder_older_vars_def, ASCIInumbersTheory.toString_inj]) >>
  suspend "loop_initial_fields"
QED

Resume source_owned_nonbulk_array_ptr[loop_initial_fields]:
  markerLib.RESUME_TAC >>
  `lookup_var q h = SOME (n2w p) /\ mload p h = 0w /\
   mem_word_at d h.vs_memory = n2w (LENGTH xs)` by
    (conj_tac >-
       (qpat_assum `eval_operand ip t = _` mp_tac >>
        qpat_assum `ip = Var q` mp_tac >>
        qpat_assum `!x. lookup_var x h = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[eval_operand_def]) >>
     conj_tac >-
       (qpat_assum `mload p t = _` mp_tac >>
        qpat_assum `h.vs_memory = t.vs_memory` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> simp[mload_def]) >>
     qpat_assum `h.vs_memory = t.vs_memory` (fn th => rewrite_tac [th]) >>
     first_assum ACCEPT_TAC) >>
  suspend "remaining_loop_inputs"
QED

Resume source_owned_nonbulk_array_ptr[remaining_loop_inputs]:
  markerLib.RESUME_TAC >>
  `DISJOINT {a | p <= a /\ a < p+32} u.t_mem` by
    (qpat_assum `u.t_mem = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  `u.t_mem SUBSET tn.t_mem` by
    (qpat_assum `u.t_mem = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[pred_setTheory.SUBSET_DEF]) >>
  `op_taint u src = {} /\ op_prov H src = NONE` by
    (qpat_assum `!x. src = Var x ==> _` mp_tac >>
     qpat_assum `!x. not_fresh_at st x ==> _` mp_tac >>
     qpat_assum `op_taint tn src = {}` mp_tac >>
     qpat_assum `op_prov G src = NONE` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `src` >>
     simp[op_taint_def, op_prov_def] >> metis_tac[]) >>
  suspend "loop_input_transport"
QED

Resume source_owned_nonbulk_array_ptr[loop_input_transport]:
  markerLib.RESUME_TAC >>
  `alloca_inv h /\ alloca_frontier_inv ctx fn site h` by
    (qpat_assum `h.vs_allocas = t.vs_allocas` mp_tac >>
     qpat_assum `h.vs_alloca_next = t.vs_alloca_next` mp_tac >>
     qpat_assum `alloca_inv t` mp_tac >>
     qpat_assum `alloca_frontier_inv ctx fn site t` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[calldata_alloca_invariants_fields]) >>
  `fresh_vars_wrt limit h` by
    (qpat_assum `!x. lookup_var x h = _` mp_tac >>
     qpat_assum `fresh_vars_wrt limit t` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> fs[fresh_vars_wrt_def] >> rpt strip_tac >>
     qpat_x_assum `!x. lookup_var x h = _`
       (qspec_then `STRING #"%" (toString n)` mp_tac) >>
     `STRING #"%" (toString n) NOTIN FDOM t.vs_vars` by metis_tac[] >>
     simp[lookup_var_def, FLOOKUP_DEF]) >>
  suspend "loop_call_inputs"
QED
