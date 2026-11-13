Theory calldataExactDynInitSequence
Ancestors
  calldataDynOwned calldataDynInit calldataBytesLive fragExecMem safeSequence
  abiDecoderGuards abiDecoderArrayLoopInit abiDecoderIndexInit
  arithmetic list words finite_map venomExecSemantics venomState venomMemDefs
  abiDecoderFrame abiDecoderContract abiDecoderDynarrayPrefix abiDecoderArrayHeader
  compileEnv emitHelper emitHelperProps abiEncoder actualAllocExec allocaFrontierBound
  allocaBudgetProps valueEncodingProps valueEncodingDefs rich_list
  abiDecoderDynarrayBound exprLoweringProps abiDecoderReentry venomInst abiDecoderFrameCompose
  calldataWordLeaf calldataBytesLeaf
Libs
  wordsLib

Definition calldata_exact_init_fields_def:
  calldata_exact_init_fields live slot ip cnt p d maxn srcword initial t <=>
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD srcword initial /\
    eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD srcword initial) /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
    (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= p \/ p+32 <= a) ==>
      mem_bytes_at a n t.vs_memory = mem_bytes_at a n initial.vs_memory) /\
    (!id. id <> slot ==> FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    FLOOKUP t.vs_allocas slot = SOME (p,32) /\
    (if FLOOKUP initial.vs_allocas slot = NONE then
       t.vs_alloca_next = initial.vs_alloca_next+32
     else t.vs_alloca_next = initial.vs_alloca_next) /\
    (!op. abi_decoder_operand_live live op ==>
      eval_operand op t = eval_operand op initial)
End

Theorem calldata_exact_array_loop_init_sequence:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\ unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+sz <= p \/ p+32 <= d) /\
  w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn ==>
  (!pre i post u. emitted_insts st loop_st = pre ++ i::post /\
     run_inst_seq pre initial = OK u ==> inst_mem_below_frontier i u) /\
  ?t. run_inst_seq (emitted_insts st loop_st) initial = OK t /\
    calldata_exact_init_fields st.cs_next_var header_st.cs_next_id
      ip cnt p d maxn srcword initial t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  `?cop. abi_decode_count_guard CALLDATALOAD src maxn st = (cop,guard_st)` by
    (qpat_x_assum `abi_decode_dynarray_prefix _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_dynarray_prefix_def, abi_decode_dynarray_end_guard_def,
          comp_bind_def, comp_return_def] >> pairarg_tac >> simp[] >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `inst_extends st loop_st` by metis_tac[inst_extends_trans] >>
  `emitted_insts st loop_st = emitted_insts st guard_st ++
      emitted_insts guard_st header_st ++ emitted_insts header_st loop_st` by
    metis_tac[emitted_insts_append, inst_extends_def, APPEND_ASSOC] >>
  drule_all calldata_count_guard_repeat_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st guard_st) initial = OK g` >>
  `eval_operand src g = SOME srcword /\ eval_operand dst g = SOME (n2w d)` by
    metis_tac[] >>
  `abi_decoder_operand_live guard_st.cs_next_var dst` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all calldata_array_header_repeat_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts guard_st header_st) g = OK h` >>
  `h.vs_allocas = initial.vs_allocas /\ h.vs_alloca_next = initial.vs_alloca_next` by metis_tac[] >>
  `?allocated. step_inst_base (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString header_st.cs_next_var)]) h = OK allocated /\
     eval_operand ip allocated = SOME (n2w p) /\ p < dimword (:256) /\
     p+32 <= allocated.vs_alloca_next /\
     FLOOKUP allocated.vs_allocas header_st.cs_next_id = SOME (p,32) /\
     (!id. id <> header_st.cs_next_id ==>
       FLOOKUP allocated.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
     (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
        allocated.vs_alloca_next = initial.vs_alloca_next+32
      else allocated.vs_alloca_next = initial.vs_alloca_next)` by suspend "allocation" >>
  drule_all calldata_index_init_after_alloca >> strip_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op (mstore p 0w allocated) = eval_operand op initial` by suspend "live" >>
  conj_tac >- suspend "safety" >>
  suspend "compose"
QED

Resume calldata_exact_array_loop_init_sequence[allocation]:
  qabbrev_tac `inst = mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString header_st.cs_next_var)]` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit 32w] /\
   inst.inst_outputs = [STRING #"%" (toString header_st.cs_next_var)] /\
   inst.inst_id = header_st.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `MEM inst (fn_insts fn)` by
    (first_x_assum irule >> drule calldata_index_init_instructions >> simp[Abbr `inst`]) >>
  `alloca_frontier_inv ctx fn site h` by
    (fs[alloca_frontier_inv_def, remaining_alloca_budget_def]) >>
  qpat_x_assum `(_ /\ p = _) \/ _` strip_assume_tac
  >- (`FLOOKUP h.vs_allocas inst.inst_id = NONE` by metis_tac[] >>
      drule_all actual_word_alloca_fresh_run >> strip_tac >>
      qexists_tac `t` >>
      gvs[Abbr `inst`, update_var_def, eval_operand_def, lookup_var_def,
          FLOOKUP_UPDATE] >> decide_tac) >>
  `FLOOKUP h.vs_allocas inst.inst_id = SOME (p,32)` by metis_tac[] >>
  drule_all actual_word_alloca_reuse_run >>
  disch_then (qspec_then `[]` strip_assume_tac) >> qexists_tac `t` >>
  gvs[Abbr `inst`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Resume calldata_exact_array_loop_init_sequence[live]:
  rpt strip_tac >>
  `abi_decoder_operand_live guard_st.cs_next_var op /\
   abi_decoder_operand_live header_st.cs_next_var op` by
    (conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand op h = eval_operand op initial` by metis_tac[] >>
  drule_all calldata_index_init_live_frame >> simp[]
QED

Resume calldata_exact_array_loop_init_sequence[compose]:
  qexists_tac `mstore p 0w allocated` >> conj_tac
  >- (qpat_assum `run_inst_seq _ initial = OK g` mp_tac >>
      qpat_assum `run_inst_seq _ g = OK h` mp_tac >>
      qpat_assum `run_inst_seq _ h = OK (mstore p 0w allocated)` mp_tac >>
      qpat_assum `emitted_insts st loop_st = _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      metis_tac[run_inst_seq_append]) >>
  `abi_decode_load CALLDATALOAD srcword g = abi_decode_load CALLDATALOAD srcword initial` by
    simp[abi_decode_load_def, abi_decode_source_def] >>
  `abi_decode_frame p 32 h (mstore p 0w allocated)` by
    (irule calldata_index_init_repeat_memory_frame >> goal_assum (drule_at Any)) >>
  `abi_decoder_operand_live header_st.cs_next_var cnt` by
    (qpat_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, LET_THM] >> pairarg_tac >> strip_tac >> gvs[] >>
     pairarg_tac >> gvs[] >>
     drule abi_decoder_operand_live_emit >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >> gvs[]) >>
  `eval_operand cnt (mstore p 0w allocated) = eval_operand cnt h` by
    (irule calldata_index_init_live_frame >> goal_assum (drule_at Any) >> simp[]) >>
  `mem_word_at d (mstore p 0w allocated).vs_memory = mem_word_at d h.vs_memory` by
    (irule abi_decode_frame_mem_word >> goal_assum (drule_at Any) >> decide_tac) >>
  `(!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= p \/ p+32 <= a) ==>
     mem_bytes_at a n (mstore p 0w allocated).vs_memory = mem_bytes_at a n initial.vs_memory) /\
   (mstore p 0w allocated).vs_call_ctx = initial.vs_call_ctx /\
   (mstore p 0w allocated).vs_data_section = initial.vs_data_section` by
    (qpat_assum `abi_decode_frame p 32 h _` mp_tac >>
     qpat_assum `abi_decode_frame d 32 g h` mp_tac >>
     qpat_assum `g.vs_memory = _` mp_tac >>
     qpat_assum `g.vs_call_ctx = _` mp_tac >>
     qpat_assum `g.vs_data_section = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [abi_decode_frame_def] >> rpt strip_tac >> metis_tac[]) >>
  `(mstore p 0w allocated).vs_allocas = allocated.vs_allocas /\
   (mstore p 0w allocated).vs_alloca_next = allocated.vs_alloca_next` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  simp_tac bool_ss [calldata_exact_init_fields_def] >>
  asm_rewrite_tac[] >> simp[eval_operand_mstore] >> metis_tac[]
QED

Resume calldata_exact_array_loop_init_sequence[safety]:
  asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `g` >> asm_rewrite_tac[] >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >>
      drule calldata_count_guard_instruction_safe >> simp[]) >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `h` >> asm_rewrite_tac[] >> conj_tac
  >- (`d+32 <= g.vs_alloca_next` by (asm_rewrite_tac[] >> decide_tac) >>
      ho_match_mp_tac (GEN_ALL calldata_array_header_repeat_prefix_safe) >>
      goal_assum (drule_at (Pos hd)) >>
      qexistsl_tac [`srcword`, `d`] >> asm_rewrite_tac[]) >>
  ho_match_mp_tac (GEN_ALL calldata_index_init_prefix_safe) >>
  goal_assum (drule_at (Pos hd)) >> goal_assum (drule_at (Pos hd)) >>
  qexists_tac `p` >> asm_rewrite_tac[]
QED
Finalise calldata_exact_array_loop_init_sequence

Theorem calldata_exact_array_loop_init_accepted:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\ unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+sz <= p \/ p+32 <= d) /\
  w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn ==>
  frag_exec_mem ctx st loop_st (\s. s=initial)
    (calldata_exact_init_fields st.cs_next_var header_st.cs_next_id
      ip cnt p d maxn srcword initial) (K F)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_exact_array_loop_init_sequence >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `inst_extends st loop_st` by metis_tac[inst_extends_trans] >>
  `emitted_insts st loop_st = emitted_insts st guard_st ++
      emitted_insts guard_st header_st ++ emitted_insts header_st loop_st` by
    metis_tac[emitted_insts_append, inst_extends_def, APPEND_ASSOC] >>
  `isPREFIX st.cs_current_insts loop_st.cs_current_insts` by
    (qpat_x_assum `inst_extends st loop_st` mp_tac >>
     simp_tac bool_ss [inst_extends_def] >> strip_tac >>
     simp_tac bool_ss [IS_PREFIX_APPEND] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES)
     (emitted_insts st loop_st)` by
    (imp_res_tac calldata_dynarray_prefix_opcodes >>
     imp_res_tac calldata_array_header_opcodes >>
     imp_res_tac abi_decode_index_init_opcodes >>
     asm_rewrite_tac[EVERY_APPEND]) >>
  irule safeSequenceTheory.frag_exec_mem_run_inst_seq >> asm_rewrite_tac[] >>
  simp_tac bool_ss [] >> conj_tac >- metis_tac[] >>
  disj1_tac >> qexists_tac `t` >>
  gvs[calldata_exact_init_fields_def, instIdxIndepTheory.eval_op_inst_idx,
      mload_def] >> metis_tac[]
QED
