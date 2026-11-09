(* Executed successful dynamic-array initializer, independent of owned loops. *)
Theory calldataInitSequence
Ancestors
  calldataDynOwned calldataDynInit calldataDynStep calldataChildFrame actualAllocExec fragExecMem loweringStateRelDefs
  allocaFrontierBound allocaBudgetProps abiDecoderIndexInit abiDecoderContract
  compileEnv emitHelper venomState venomInst venomExecSemantics venomMemProps venomMemDefs
  valueEncodingProps finite_map words arithmetic list rich_list
  abiDecoderIndexedAddress abiDecoderReentryAddress abiDecoderReentry
  abiDecoderGuards abiDecoderFrame emitHelperProps exprLoweringProps abiEncoder
  abiDecoderExecution valueEncoding safeSequence instIdxIndep
  abiDecoderStaticLoopSetup abiDecoderDynamicLoopSetup abiDecoderArraySetupInputs
  abiDecoderLoopEmit abiDecoderCounters abiDecoderDynarrayPrefix
  abiDecoderDynarrayBound abiDecoderArrayHeader abiDecoderReservation
  abiDecoderArrayLoopInit abiDecoderFrameCompose calldataWordLeaf calldataBytesLeaf
  abiDecoderLoopRegisters

Theorem calldata_index_init_limit_fresh[local]:
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
  st.cs_next_var < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  fresh_vars_wrt limit_st (mstore p 0w allocated)
Proof
  strip_tac >> irule fresh_vars_wrt_mstore >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  irule abi_decoder_generated_update_fresh >> gvs[fresh_vars_wrt_def]
QED

(* The common executed endpoint, including the frame used by owned clients. *)
Theorem calldata_array_loop_init_repeat_sequence:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st =
    ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  32 <= sz /\ d+sz <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
    p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
    p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+sz <= p \/ p+32 <= d) /\
  w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn ==>
  (!pre i post u. emitted_insts st loop_st = pre ++ i::post /\
     run_inst_seq pre initial = OK u ==> inst_mem_below_frontier i u) /\
  ?t. run_inst_seq (emitted_insts st loop_st) initial = OK t /\
      eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD srcword initial /\
      eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD srcword initial) /\
      t.vs_call_ctx = initial.vs_call_ctx /\
      t.vs_data_section = initial.vs_data_section /\
      (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= p \/ p+32 <= a) ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n initial.vs_memory) /\
      (!id. id <> header_st.cs_next_id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
         t.vs_alloca_next = initial.vs_alloca_next+32
       else t.vs_alloca_next = initial.vs_alloca_next) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial) /\
      (!limit_st. fresh_vars_wrt limit_st initial /\
        loop_st.cs_next_var <= limit_st.cs_next_var ==>
        fresh_vars_wrt limit_st t)
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
  `h.vs_allocas = initial.vs_allocas /\ h.vs_alloca_next = initial.vs_alloca_next` by
    metis_tac[] >>
  `?allocated. step_inst_base (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString header_st.cs_next_var)]) h = OK allocated /\
     eval_operand ip allocated = SOME (n2w p) /\ p < dimword (:256) /\
     p+32 <= allocated.vs_alloca_next /\
     FLOOKUP allocated.vs_allocas header_st.cs_next_id = SOME (p,32) /\
     (!id. id <> header_st.cs_next_id ==>
       FLOOKUP allocated.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
     (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
        allocated.vs_alloca_next = initial.vs_alloca_next+32
      else allocated.vs_alloca_next = initial.vs_alloca_next)` by
    suspend "allocation" >>
  drule_all calldata_index_init_after_alloca >> strip_tac >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
     eval_operand op (mstore p 0w allocated) = eval_operand op initial` by
    suspend "live" >>
  `!limit_st. fresh_vars_wrt limit_st initial /\
     loop_st.cs_next_var <= limit_st.cs_next_var ==>
     fresh_vars_wrt limit_st (mstore p 0w allocated)` by suspend "fresh" >>
  reverse conj_tac >- suspend "execution" >>
  suspend "safety"
QED

Resume calldata_array_loop_init_repeat_sequence[allocation]:
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
  gvs[Abbr `inst`, update_var_def, eval_operand_def, lookup_var_def,
      FLOOKUP_UPDATE]
QED

Resume calldata_array_loop_init_repeat_sequence[live]:
  rpt strip_tac >>
  `abi_decoder_operand_live guard_st.cs_next_var op /\
   abi_decoder_operand_live header_st.cs_next_var op` by
    (Cases_on `op` >>
     gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `eval_operand op h = eval_operand op initial` by metis_tac[] >>
  drule_all calldata_index_init_live_frame >> simp[]
QED

Resume calldata_array_loop_init_repeat_sequence[safety]:
  qpat_x_assum `emitted_insts st loop_st = _` (fn th => pure_rewrite_tac[th]) >>
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

Resume calldata_array_loop_init_repeat_sequence[execution]:
  qexists_tac `mstore p 0w allocated` >>
  conj_tac
  >- (qpat_x_assum `emitted_insts st loop_st = _` (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `run_inst_seq _ initial = OK g` mp_tac >>
      qpat_assum `run_inst_seq _ g = OK h` mp_tac >>
      qpat_assum `run_inst_seq _ h = OK (mstore p 0w allocated)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      metis_tac[run_inst_seq_append]) >>
  `abi_decode_load CALLDATALOAD srcword g =
     abi_decode_load CALLDATALOAD srcword initial` by
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
     simp_tac bool_ss [abi_decode_frame_def] >> rpt strip_tac >>
     metis_tac[]) >>
  `(mstore p 0w allocated).vs_allocas = allocated.vs_allocas /\
   (mstore p 0w allocated).vs_alloca_next = allocated.vs_alloca_next` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  qpat_x_assum `header_st.cs_next_var = _`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_x_assum `header_st.cs_next_id = _`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_x_assum `ip = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  `!s k. mload p (s with vs_inst_idx := k) = mload p s` by simp[mload_def] >>
  simp[instIdxIndepTheory.eval_op_inst_idx, eval_operand_mstore] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume calldata_array_loop_init_repeat_sequence[fresh]:
  rpt strip_tac >>
  `guard_st.cs_next_var <= limit_st.cs_next_var /\
   header_st.cs_next_var <= limit_st.cs_next_var /\
   header_st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  `fresh_vars_wrt limit_st g` by
    (qpat_x_assum `!lim. _ ==> fresh_vars_wrt lim g` irule >> simp[]) >>
  `fresh_vars_wrt limit_st h` by
    (qpat_x_assum `!lim. _ ==> fresh_vars_wrt lim h` irule >> simp[]) >>
  irule calldata_index_init_limit_fresh >> goal_assum (drule_at Any) >>
  qexists_tac `header_st` >> simp[]
QED

Finalise calldata_array_loop_init_repeat_sequence
