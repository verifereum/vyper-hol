(* Executed successful dynamic-array initializer, independent of owned loops. *)
Theory calldataInitSequence
Ancestors
  calldataDynInit calldataDynStep calldataChildFrame actualAllocExec fragExecMem
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

Theorem calldata_update_protected:
  abi_decoder_operand_live next op ==>
  eval_operand op (update_var (STRING #"%" (toString next)) w s) = eval_operand op s
Proof
  Cases_on `op` >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  strip_tac >> first_x_assum (qspec_then `next` mp_tac) >> simp[]
QED

Theorem calldata_index_init_live_frame:
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
  abi_decoder_operand_live st.cs_next_var op ==>
  eval_operand op (mstore p 0w allocated) = eval_operand op s
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[mstore_def, write_memory_with_expansion_def] >>
  simp[calldata_update_protected] >>
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem calldata_read_repeat:
  emit_op CALLDATALOAD [src] st = (out,st') /\ eval_operand src s = SOME p ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (abi_decode_load CALLDATALOAD p s) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    t = update_var (STRING #"%" (toString st.cs_next_var))
      (abi_decode_load CALLDATALOAD p s) s /\ inst_extends st st' /\
    (!limit_st. fresh_vars_wrt limit_st s /\ st'.cs_next_var <= limit_st.cs_next_var ==>
      fresh_vars_wrt limit_st t)
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (abi_decode_load CALLDATALOAD p s) s` >>
  `step_inst_base (mk_inst st.cs_next_id CALLDATALOAD [src]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (simp_tac bool_ss [Abbr `t`] >> irule abi_decode_read_step >>
     simp[abi_decode_source_opcode_def]) >>
  `!limit_st. fresh_vars_wrt limit_st s /\ st'.cs_next_var <= limit_st.cs_next_var ==>
     fresh_vars_wrt limit_st t` by
    (simp_tac bool_ss [Abbr `t`] >> rpt strip_tac >>
     irule abi_decoder_generated_update_fresh >> simp[] >> decide_tac) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var,
       update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED

Theorem calldata_gt_repeat:
  emit_op GT [lhs;rhs] st = (out,st') /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (bool_to_word (w2n a > w2n b)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    inst_extends st st' /\
    (!limit_st. fresh_vars_wrt limit_st s /\ st'.cs_next_var <= limit_st.cs_next_var ==>
      fresh_vars_wrt limit_st t)
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (bool_to_word (w2n a > w2n b)) s` >>
  `step_inst_base (mk_inst st.cs_next_id GT [lhs;rhs]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (simp_tac bool_ss [Abbr `t`] >> irule step_GT >> simp[]) >>
  `!limit_st. fresh_vars_wrt limit_st s /\ st'.cs_next_var <= limit_st.cs_next_var ==>
     fresh_vars_wrt limit_st t` by
    (simp_tac bool_ss [Abbr `t`] >> rpt strip_tac >>
     irule abi_decoder_generated_update_fresh >> simp[] >> decide_tac) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var,
       update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED

Theorem calldata_iszero_repeat:
  emit_op ISZERO [arg] st = (out,st') /\ eval_operand arg s = SOME a ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (bool_to_word (a = 0w)) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    inst_extends st st' /\
    (!limit_st. fresh_vars_wrt limit_st s /\ st'.cs_next_var <= limit_st.cs_next_var ==>
      fresh_vars_wrt limit_st t)
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (bool_to_word (a = 0w)) s` >>
  `step_inst_base (mk_inst st.cs_next_id ISZERO [arg]
    [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (simp_tac bool_ss [Abbr `t`] >> irule step_ISZERO >> simp[]) >>
  `!limit_st. fresh_vars_wrt limit_st s /\ st'.cs_next_var <= limit_st.cs_next_var ==>
     fresh_vars_wrt limit_st t` by
    (simp_tac bool_ss [Abbr `t`] >> rpt strip_tac >>
     irule abi_decoder_generated_update_fresh >> simp[] >> decide_tac) >>
  qexists_tac `t` >> gvs[Abbr `t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var,
       update_var_def] >>
  metis_tac[calldata_update_protected, update_var_def]
QED

Theorem calldata_count_guard_repeat_sequence:
  abi_decode_count_guard CALLDATALOAD src limit st = (count_op,st') /\
  eval_operand src s = SOME p /\ limit < dimword (:256) /\
  w2n (abi_decode_load CALLDATALOAD p s) <= limit ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand count_op t = SOME (abi_decode_load CALLDATALOAD p s) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    (!limit_st. fresh_vars_wrt limit_st s /\ st'.cs_next_var <= limit_st.cs_next_var ==>
      fresh_vars_wrt limit_st t)
Proof
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op GT [count_op; Lit (n2w limit)] c1 = (too_many,c2)` >>
  rename1 `emit_op ISZERO [too_many] c2 = (ok,c3)` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand (Lit (n2w limit)) s1 = SOME (n2w limit)` by simp[eval_operand_def] >>
  drule_all calldata_gt_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  gvs[w2n_n2w, bool_to_word_def] >>
  drule_all calldata_iszero_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  gvs[bool_to_word_def] >>
  `(1w:bytes32) <> 0w` by simp[] >>
  rename1 `emit_void ASSERT [ok] c3 = ((),last_st)` >>
  `run_inst_seq (emitted_insts c3 last_st) s3 = OK s3` by
    (drule emitted_insts_emit_void >> strip_tac >>
     simp[run_inst_seq_def, assert_ok]) >>
  imp_res_tac inst_extends_emit_void >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `s3` >> simp[] >>
  conj_tac
  >- (irule run_inst_seq_compose_ok >> qexistsl_tac [`s2`,`c2`] >>
      conj_tac >- (irule run_inst_seq_compose_ok >>
        goal_assum (drule_at Any) >> simp[]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      metis_tac[inst_extends_trans]) >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> decide_tac) >>
  conj_tac
  >- (`abi_decoder_operand_live c1.cs_next_var count_op` by
        metis_tac[abi_decoder_operand_live_emit] >>
      `abi_decoder_operand_live c2.cs_next_var count_op` by
        metis_tac[abi_decoder_operand_live_mono] >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `abi_decoder_operand_live c1.cs_next_var op /\
       abi_decoder_operand_live c2.cs_next_var op` by
        metis_tac[abi_decoder_operand_live_mono] >> metis_tac[]) >>
  suspend "fresh"
QED

Resume calldata_count_guard_repeat_sequence[fresh]:
  `c1.cs_next_var <= last_st.cs_next_var /\
   c2.cs_next_var <= last_st.cs_next_var /\
   c3.cs_next_var <= last_st.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >>
     imp_res_tac emitted_insts_emit_void >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!lim. _ ==> fresh_vars_wrt lim s3` irule >>
  conj_tac >- decide_tac >>
  qpat_x_assum `!lim. _ ==> fresh_vars_wrt lim s2` irule >>
  conj_tac >- decide_tac >>
  first_x_assum irule >> simp[] >> decide_tac
QED

Finalise calldata_count_guard_repeat_sequence

Theorem calldata_array_header_repeat_sequence:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var dst /\ d < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD p s) /\
    mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD p s /\
    abi_decode_frame d 32 s t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st' /\
    (!limit_st. fresh_vars_wrt limit_st s /\ st'.cs_next_var <= limit_st.cs_next_var ==>
      fresh_vars_wrt limit_st t)
Proof
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (cnt,c1)` >>
  rename1 `emit_void MSTORE [dst;cnt] c1 = ((),last_st)` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK loaded` >>
  `eval_operand dst loaded = SOME (n2w d)` by metis_tac[] >>
  `run_inst_seq (emitted_insts c1 last_st) loaded =
     OK (mstore d (abi_decode_load CALLDATALOAD p s) loaded)` by
    (`step_inst_base (mk_inst c1.cs_next_id MSTORE [dst;cnt] []) loaded =
       OK (mstore (w2n (n2w d : bytes32)) (abi_decode_load CALLDATALOAD p s) loaded)` by
       (irule step_MSTORE >> simp[]) >>
     `w2n (n2w d : bytes32) = d` by simp[] >>
     drule emitted_insts_emit_void >> strip_tac >>
     qpat_x_assum `loaded = _` kall_tac >> fs[run_inst_seq_def]) >>
  drule inst_extends_emit_void >> strip_tac >>
  `!limit_st. fresh_vars_wrt limit_st s /\ last_st.cs_next_var <= limit_st.cs_next_var ==>
     fresh_vars_wrt limit_st (mstore d (abi_decode_load CALLDATALOAD p s) loaded)` by
    (rpt strip_tac >> irule fresh_vars_wrt_mstore >>
     qpat_x_assum `!lim. _ ==> fresh_vars_wrt lim loaded` irule >>
     drule emitted_insts_emit_void >> strip_tac >> simp[]) >>
  qexists_tac `mstore d (abi_decode_load CALLDATALOAD p s) loaded` >>
  conj_tac
  >- (irule run_inst_seq_compose_ok >> qexistsl_tac [`loaded`,`c1`] >> simp[]) >>
  qpat_x_assum `loaded = _` kall_tac >>
  simp[eval_operand_mstore, mstore_mem_word_at_same] >>
  conj_tac
  >- (`abi_decode_frame d 32 loaded
         (mstore d (abi_decode_load CALLDATALOAD p s) loaded)` by
        irule abi_decode_mstore_frame >>
      qpat_x_assum `abi_decode_frame _ _ _ _` mp_tac >>
      simp[abi_decode_frame_def]) >>
  simp[mstore_def, write_memory_with_expansion_def] >>
  metis_tac[inst_extends_trans]
QED

Theorem calldata_array_header_repeat_prefix_safe:
  abi_decode_array_header dst src CALLDATALOAD st = (cnt,st') /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\ d+32 <= s.vs_alloca_next /\
  abi_decoder_operand_live st.cs_next_var dst ==>
  !pre i post u. emitted_insts st st' = pre ++ i::post /\
    run_inst_seq pre s = OK u ==> inst_mem_below_frontier i u
Proof
  simp_tac bool_ss [abi_decode_array_header_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] st = (cnt,c1)` >>
  rename1 `emit_void MSTORE [dst;cnt] c1 = ((),st')` >>
  drule_all calldata_read_repeat >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  imp_res_tac inst_extends_emit_void >>
  `emitted_insts st st' = emitted_insts st c1 ++ emitted_insts c1 st'` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. !u. inst_mem_below_frontier i u) (emitted_insts st c1)` by
    (drule emitted_insts_emit_op >> simp[] >>
     simp[unitTransformDefsTheory.inst_mem_below_frontier_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]) >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL run_inst_seq_prefix_safe_append) >>
  qexists_tac `s1` >> asm_rewrite_tac[] >> conj_tac
  >- (ho_match_mp_tac calldata_prefix_safe_every >> simp[]) >>
  drule emitted_insts_emit_void >> simp[] >> strip_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  ho_match_mp_tac (GEN_ALL calldata_mstore_prefix_safe) >>
  qexists_tac `d` >> simp[] >> metis_tac[]
QED

Theorem calldata_index_init_repeat_memory_frame:
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated ==>
  abi_decode_frame p 32 s (mstore p 0w allocated)
Proof
  strip_tac >>
  `abi_decode_frame p 32 allocated (mstore p 0w allocated)` by
    irule abi_decode_mstore_frame >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas st.cs_next_id` >>
  gvs[AllCaseEqs()] >> strip_tac >> gvs[] >>
  fs[abi_decode_frame_def, update_var_def] >> first_assum ACCEPT_TAC
QED

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
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) maxn abi_sz st =
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
