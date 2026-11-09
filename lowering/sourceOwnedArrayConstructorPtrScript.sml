(* Actual-site resources at the nonbulk source-array constructor boundary. *)
Theory sourceOwnedArrayConstructorPtr
Ancestors
  sourceOwnedArrayLoopPtr decoderArrayInitPtr physicalArrayInitSequence
  actualAllocaReplayPtr actualDecoderAllocationPtr actualAllocExec vyperCompiler allocaFrontierBound
  calldataDynInit calldataDynOwned abiDecoderRecursiveArray abiDecoderRecursiveLoopLayout
  abiDecoderArrayInit abiDecoderArrayInitExec abiDecoderArrayLoopInit abiDecoderIndexInit
  abiDecoderReentry abiDecoderFrame abiDecoderFrameCompose
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderArrayHeader
  abiDecoderGuards abiDecoderGuard ctorAbiActualAlloc
  emitHelperProps emitHelper exprLowering exprLoweringProps abiDecoderContract
  rich_list context compileEnv venomState venomInst
  venomExecSemantics venomMemDefs venomWf finite_map words list arithmetic

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
