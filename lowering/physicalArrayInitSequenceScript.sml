(* Successful array preparation with credit for its actual index slot only. *)
Theory physicalArrayInitSequence
Ancestors actualAllocExec actualDecoderAllocationPtr abiDecoderArrayInitExec abiDecoderIndexInit
  abiDecoderArrayLoopInit abiDecoderDynarrayPrefix abiDecoderArrayHeader
  abiDecoderGuards abiDecoderContract abiDecoderAllocation abiDecoderReentry abiDecoderFrame
  abiDecoderFrameCompose abiDecoderReentryPointer exprLoweringProps emitHelperProps
  compileEnv venomState venomExecSemantics venomInst venomMemDefs valueEncoding
  exprLowering context abiDecoderLoopEmit abiDecoderExecution venomMemProps emitHelper abiEncoder abiDecoderDynarrayBound
  fragExec fragExecMem actualAllocCredit allocaFrontierBound abiDecoderReservation
  allocaBudgetProps valueEncodingProps abiDecoderRange
  finite_map words arithmetic list rich_list

Theorem calldata_array_loop_init_trace:
  abi_decode_array_loop_init dst src opc (Lit 0w) (Lit 0w) maxn abi_sz st =
    (setup,loop_st) ==>
  ?guard_st header_st cnt ip.
    abi_decode_dynarray_prefix src opc (Lit 0w) maxn abi_sz st = ((),guard_st) /\
    abi_decode_dynarray_position_prefix src opc (Lit 0w) (Lit 0w) maxn abi_sz st =
      (src,guard_st) /\
    abi_decode_array_header dst src opc guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\ setup = (ip,cnt)
Proof
  strip_tac >> drule abi_decode_array_loop_init_trace >> strip_tac >>
  qexistsl [`guard_st`,`header_st`,`cnt`,`ip`] >>
  Cases_on `abi_decode_count_guard opc src maxn st` >>
  gvs[abi_decode_dynarray_position_prefix_unbounded, compile_abi_dec_addr_def,
      abi_decode_dynarray_prefix_def, abi_decode_dynarray_end_guard_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

(* Index-slot initialization and loop-prefix code facts (from the pruned
   calldataDynInit theory). *)
Theorem calldata_index_init_instructions:
  abi_decode_index_init st = (ip,st') ==>
  ip = Var (STRING #"%" (toString st.cs_next_var)) /\
  emitted_insts st st' =
    [mk_inst st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id+1) MSTORE [ip;Lit 0w] []]
Proof
  simp[abi_decode_index_init_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[DROP_LENGTH_APPEND]
QED

Theorem calldata_index_init_after_alloca:
  abi_decode_index_init st = (ip,st') /\
  step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
  eval_operand ip allocated = SOME (n2w p) /\ p < dimword (:256) ==>
  run_inst_seq (emitted_insts st st') s = OK (mstore p 0w allocated) /\
  eval_operand ip (mstore p 0w allocated) = SOME (n2w p) /\
  mload p (mstore p 0w allocated) = 0w
Proof
  strip_tac >> drule calldata_index_init_instructions >> strip_tac >>
  simp[run_inst_seq_def] >>
  simp[Once step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operand_def, w2n_n2w, mload_mstore_same,
       abi_decoder_operand_mstore] >>
  gvs[eval_operand_def]
QED

Theorem calldata_loop_prefix_entry_code:
  !ip src start hdr body exit_lbl end_st fn.
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) start = ((hdr,body,exit_lbl),end_st) /\
  fn_has_code start end_st fn ==>
  ?bb hb.
    lookup_block start.cs_current_bb fn.fn_blocks = SOME bb /\
    bb.bb_instructions = start.cs_current_insts ++
      [mk_inst start.cs_next_id JMP [Label hdr] []] /\
    lookup_block hdr fn.fn_blocks = SOME hb /\
    phi_prefix_length hb.bb_instructions = 0
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_decode_loop_prefix_shape] >> strip_tac >>
  gvs[] >>
  qpat_x_assum `fn_has_code _ _ _` mp_tac >>
  simp[fn_has_code_def, emitted_blocks_def,
       abi_decode_loop_prefix_state_def, abi_decode_position_header_zero, abi_decode_position_header_delta_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  rpt strip_tac >>
  simp[abi_decode_position_header_zero, abi_decode_header_insts_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem physical_index_init_sequence[local]:
  abi_decode_index_init st = (ip,en) /\ fresh_vars_wrt en s /\
  ((FLOOKUP s.vs_allocas st.cs_next_id = NONE /\
      p = s.vs_alloca_next /\ p + 32 < dimword (:256)) \/
   (FLOOKUP s.vs_allocas st.cs_next_id = SOME (p,32) /\
      p + 32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256))) ==>
  ?t. run_inst_seq (emitted_insts st en) s = OK t /\
    eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
    fresh_vars_wrt en t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    abi_decode_frame p 32 s t /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_alloca_next = (if FLOOKUP s.vs_allocas st.cs_next_id = NONE
                       then s.vs_alloca_next + 32 else s.vs_alloca_next) /\
    t.vs_halted = s.vs_halted /\ inst_extends st en
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?b cap. abi_decoder_budget st.cs_next_id (st.cs_next_id+1) b cap s` by
    (irule actual_slot_singleton_budget >> metis_tac[]) >>
  `st.cs_next_id IN abi_decoder_ids st.cs_next_id (st.cs_next_id+1)` by
    simp[abi_decoder_ids_def] >>
  `en.cs_next_var <= en.cs_next_var` by simp[] >>
  drule_all abi_decode_index_init_sequence >> strip_tac >>
  `eval_operand ip t = SOME (n2w p) /\
    t.vs_alloca_next = (if FLOOKUP s.vs_allocas st.cs_next_id = NONE
                       then s.vs_alloca_next + 32 else s.vs_alloca_next)` by
    (drule calldata_index_init_instructions >> strip_tac >>
     `p < dimword (:256)` by (gvs[] >> decide_tac) >>
     `?allocated.
       step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
         [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
       eval_operand ip allocated = SOME (n2w p) /\
       allocated.vs_alloca_next =
         (if FLOOKUP s.vs_allocas st.cs_next_id = NONE then s.vs_alloca_next+32
          else s.vs_alloca_next)` by
       (qpat_x_assum `FLOOKUP s.vs_allocas st.cs_next_id = NONE /\ _ \/ _` strip_assume_tac
        >- (`step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
              [STRING #"%" (toString st.cs_next_var)]) s = OK
              (update_var (STRING #"%" (toString st.cs_next_var)) (n2w s.vs_alloca_next)
                (s with <|vs_allocas := s.vs_allocas |+ (st.cs_next_id,(s.vs_alloca_next,32));
                          vs_alloca_next := s.vs_alloca_next+32|>))` by
              (mp_tac (Q.INST [`inst` |-> `mk_inst st.cs_next_id ALLOCA [Lit 32w]
                [STRING #"%" (toString st.cs_next_var)]`,
                `out` |-> `STRING #"%" (toString st.cs_next_var)`] physical_word_alloca_fresh_run) >>
               simp[mk_inst_def]) >>
            goal_assum (drule_at Any) >>
            gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
        `?allocated. step_inst_base (mk_inst st.cs_next_id ALLOCA [Lit 32w]
             [STRING #"%" (toString st.cs_next_var)]) s = OK allocated /\
           allocated = update_var (STRING #"%" (toString st.cs_next_var)) (n2w p) s` by
          (mp_tac (Q.INST [`inst` |-> `mk_inst st.cs_next_id ALLOCA [Lit 32w]
             [STRING #"%" (toString st.cs_next_var)]`,
             `out` |-> `STRING #"%" (toString st.cs_next_var)`, `insts` |-> `[]`]
             actual_word_alloca_reuse_run) >>
           simp[mk_inst_def] >> metis_tac[]) >>
        goal_assum (drule_at Any) >>
        gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
     drule_all calldata_index_init_after_alloca >> strip_tac >>
     `t = mstore p 0w allocated` by metis_tac[exec_result_11] >>
     conj_tac >- metis_tac[] >>
     simp[mstore_def, write_memory_with_expansion_def]) >>
  `p' = p` by
    (`p' < dimword (:256)` by
       (drule abi_decoder_budget_word_bound >> decide_tac) >>
     `p < dimword (:256)` by (gvs[] >> decide_tac) >>
     `n2w p' = (n2w p:bytes32)` by metis_tac[optionTheory.SOME_11] >>
     gvs[w2n_n2w]) >>
  qexists_tac `t` >> gvs[]
QED

Theorem calldata_array_loop_init_physical_sequence:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st = (setup,loop_st) /\
  eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load CALLDATALOAD (n2w sb:bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\ fresh_vars_wrt st s /\
  ((FLOOKUP s.vs_allocas (loop_st.cs_next_id - 2) = NONE /\
    p = s.vs_alloca_next /\ p + 32 < dimword (:256)) \/
   (FLOOKUP s.vs_allocas (loop_st.cs_next_id - 2) = SOME (p,32) /\
    p + 32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256))) /\
  (d + 32 <= p \/ p + 32 <= d) ==>
  ?t. run_inst_seq (emitted_insts st loop_st) s = OK t /\
    eval_operand (FST setup) t = SOME (n2w p) /\
    eval_operand (SND setup) t = SOME (n2w n) /\
    mload p t = 0w /\ mem_word_at d t.vs_memory = n2w n /\
    fresh_vars_wrt loop_st t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    abi_decode_footprint_frame [(d,32);(p,32)] s t /\
    FLOOKUP t.vs_allocas (loop_st.cs_next_id - 2) = SOME (p,32) /\
    (!id. id <> loop_st.cs_next_id - 2 ==>
      FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_alloca_next = (if FLOOKUP s.vs_allocas (loop_st.cs_next_id - 2) = NONE
                       then s.vs_alloca_next + 32 else s.vs_alloca_next) /\
    t.vs_halted = s.vs_halted /\ inst_extends st loop_st
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule calldata_array_loop_init_trace >> strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `eval_operand (Lit 0w) s = SOME (n2w 0)` by simp[eval_operand_def] >>
  drule_all (SRULE [] (Q.INST [`hi` |-> `Lit 0w`, `base_op` |-> `Lit 0w`, `B` |-> `0`]
    abi_decode_array_prepare_sequence)) >>
  strip_tac >>
  `fresh_vars_wrt loop_st prepared` by
    (irule fresh_vars_wrt_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `loop_st.cs_next_id - 2 = header_st.cs_next_id` by decide_tac >>
  drule_at (Pat `abi_decode_index_init _ = _`) physical_index_init_sequence >>
  disch_then (qspecl_then [`prepared`,`p`] mp_tac) >>
  impl_tac >- (simp[] >> fs[] >> metis_tac[]) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts header_st loop_st) prepared = OK actual` >>
  `!op w. eval_operand op prepared = SOME w ==>
    abi_decoder_operand_live header_st.cs_next_var op` by
    metis_tac[abi_decoder_operand_live_fresh] >>
  `eval_operand cnt actual = SOME (n2w n)` by metis_tac[] >>
  `!op w. eval_operand op s = SOME w ==> eval_operand op actual = SOME w` by metis_tac[] >>
  `mem_word_at d actual.vs_memory = mem_word_at d prepared.vs_memory` by
    (irule abi_decode_frame_mem_word >> qexistsl_tac [`p`,`32`] >> simp[]) >>
  `abi_decode_footprint_frame [(d,32);(p,32)] s actual` by
    (drule_all abi_decoder_array_init_exact_frame >> simp[]) >>
  `run_inst_seq (emitted_insts st loop_st) s = OK actual /\ inst_extends st loop_st` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`prepared`,`header_st`] >> simp[]) >>
  qexists_tac `actual` >> gvs[]
QED
