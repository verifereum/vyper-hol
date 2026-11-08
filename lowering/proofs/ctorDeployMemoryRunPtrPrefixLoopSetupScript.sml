(* Paired boundaries for canonical dynamic-array loop preparation. *)
Theory ctorDeployMemoryRunPtrPrefixLoopSetup
Ancestors
  ctorDeployMemoryRunPtrPrefixLoopSlot ctorDeployMemoryRunPtrPrefixCopyRun
  ctorDeployMemoryRunPtrPrefixSteps ctorDeployMemoryRunPtrPrefixSequence
  abiDecoderContract abiDecoderArrayHeader abiDecoderArrayLoopInit
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderGuards
  ctorAbiActualArrayPrepare abiDecoderLoop abiEncoderRegisteredEffect
  abiDecoderDynamicLoopSetup abiDecoderReservation venomMemDefs
  allocaFrontierBound allocaBudgetProps ctorAbiActualFrame valueEncodingProps
  compileEnv emitHelper emitHelperProps exprLowering venomMemProps
  ctorAbiActualArrayRun ctorAbiActualArrayEntry ctorAbiActualArrayInvariant
  ctorAbiActualAlloc abiDecoderIndexInit fragExec abiDecoderReentry ctorAbiActualObservations
  ptrSafeRun ptrDiscipline venomExecSemantics venomState venomInst
  exprLoweringProps instIdxIndep memLocDefs codegenRel contextCodegenRel finite_map words arithmetic pred_set list

Theorem prefix_loop_header_no_phis:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions = 0 ==>
  entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn
Proof
  strip_tac >>
  Cases_on `bb.bb_instructions` >>
  gvs[phi_prefix_length_def,entry_prov_def,entry_taint_vars_def,
    phis_prov_def,phis_taint_def] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[]
QED

Theorem prefix_loop_entry_jump_step:
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  step_inst fuel ctx (mk_inst iid JMP [Label hdr] []) s = OK (jump_to hdr s) /\
  ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid JMP [Label hdr] []) s
Proof
  strip_tac >>
  simp[step_inst_non_invoke,step_inst_base_def,mk_inst_def] >>
  simp[ptr_safe_step_def,ptr_inst_ok_def,access_ok_def,taint_ok_def,
    step_inst_non_invoke,step_inst_base_def,mk_inst_def,
    source_memory_read_ranges_def,source_memory_write_ranges_def,jump_to_def,
    op_taint_def]
QED

Theorem prefix_loop_entry_jump_run:
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst iid JMP [Label hdr] []) /\
  lookup_block hdr fn.fn_blocks = SOME hdr_bb /\
  phi_prefix_length hdr_bb.bb_instructions = 0 ==>
  ((!fuel. ptr_safe_run D lo fuel ctx fn PG G tn (jump_to hdr s)) ==>
   !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> strip_tac >> gen_tac >>
  `step_inst fuel ctx (mk_inst iid JMP [Label hdr] []) s = OK (jump_to hdr s) /\
   ptr_safe_step D lo fuel ctx fn PG G tn (mk_inst iid JMP [Label hdr] []) s` by
    (irule prefix_loop_entry_jump_step >> simp[]) >>
  `entry_prov fn (jump_to hdr s) G = G /\
   entry_taint_vars fn (jump_to hdr s) tn = tn` by
    (irule prefix_loop_header_no_phis >> simp[jump_to_def] >> metis_tac[]) >>
  `!u. eval_phis u hdr_bb.bb_instructions = OK u` by
    (Cases_on `hdr_bb.bb_instructions` >> gvs[phi_prefix_length_def,eval_phis_def] >>
     Cases_on `h.inst_opcode = PHI` >> gvs[eval_phis_def]) >>
  `ptr_safe_blocks D lo fuel ctx fn PG G tn (jump_to hdr s)` by
    (Cases_on `fuel` >- simp[Once ptr_safe_blocks_def] >>
     simp[Once ptr_safe_blocks_def,jump_to_def] >>
     qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ _ _ _`
       (qspec_then `n` mp_tac) >>
     simp[ptr_safe_run_def,jump_to_def]) >>
  simp[ptr_safe_run_def] >>
  `is_terminator (mk_inst iid JMP [Label hdr] []).inst_opcode /\
   ~(jump_to hdr s).vs_halted` by simp[mk_inst_def,is_terminator_def,jump_to_def] >>
  drule_all ptr_safe_block_terminator >> simp[]
QED

Theorem prefix_loop_count_header_steps_interior:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  eval_operand (Var dst) s = SOME (n2w d) /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (rb,sz) /\ rb <= d /\ d+32 <= rb+sz /\ d < dimword (:256) /\ dst <> x /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst iid DLOAD [src] [x];
      j = mk_inst (iid+1) MSTORE [Var dst;Var x] [];
      w = abi_decode_load DLOAD a s;
      u = update_var x w s;
      t = mstore d w u;
      H = DRESTRICT G (COMPL {x});
      q = step_taint i s u tn;
      qt = step_taint j u t q
  in step_inst_base i s = OK u /\ step_inst_base j u = OK t /\
     ghost_step fuel ctx PG G tn i s = (H,q) /\
     ghost_step fuel ctx PG H q j u = (H,qt) /\
     ptr_safe_step D lo fuel ctx fn PG G tn i s /\
     ptr_safe_step D lo fuel ctx fn PG H q j u /\
     mload d t = w /\ DISJOINT qt.t_mem {b | d <= b /\ b < d+32} /\
     qt.t_mem SUBSET tn.t_mem /\
     op_taint qt (Var dst) = {} /\ op_taint qt (Var x) = {} /\
     FLOOKUP H dst = SOME (rb,sz)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  `step_inst_base (mk_inst iid DLOAD [src] [x]) s =
    OK (update_var x (abi_decode_load DLOAD a s) s)` by
    (qpat_assum `eval_operand src s = SOME a` (mp_then Any mp_tac prefix_dload_step) >> disch_then (qspecl_then [`iid`,`x`] mp_tac) >>
     simp[abi_decode_load_def,abi_decode_source_def]) >>
  `eval_operand (Var dst) (update_var x (abi_decode_load DLOAD a s) s) = SOME (n2w d)` by
    fs[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  `eval_operand (Var x) (update_var x (abi_decode_load DLOAD a s) s) =
    SOME (abi_decode_load DLOAD a s)` by
    simp[eval_operand_def,lookup_var_def,update_var_def,FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (iid+1) MSTORE [Var dst;Var x] [])
      (update_var x (abi_decode_load DLOAD a s) s) =
    OK (mstore d (abi_decode_load DLOAD a s) (update_var x (abi_decode_load DLOAD a s) s))` by
    (simp[step_inst_base_def,mk_inst_def,exec_write2_def]) >>
  asm_rewrite_tac[] >>
  conj_tac >-
    (qpat_assum `eval_operand src s = SOME a` (mp_then Any mp_tac prefix_dload_ghost_step) >> disch_then (qspecl_then [`iid`,`x`] mp_tac) >>
     simp[abi_decode_load_def,abi_decode_source_def]) >>
  conj_tac >-
    (irule prefix_mstore_ghost_step >>
     simp[step_inst_non_invoke,mk_inst_def] >>
     pure_rewrite_tac[GSYM mk_inst_def] >> asm_rewrite_tac[]) >>
  conj_tac >- (irule prefix_dload_ptr_step >> simp[]) >>
  conj_tac >-
    (irule prefix_mstore_ptr_step >>
     simp[prefix_copy_pure_taint,prefix_dload_output_taint,op_taint_def,FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT,allocas_from_def,update_var_def] >>
     fs[allocas_from_def,op_taint_def] >> metis_tac[w2n_n2w]) >>
  simp[mload_mstore_same,prefix_copy_pure_taint] >>
  qmatch_goalsub_abbrev_tac `step_taint j u t q` >>
  `(step_taint j u t q).t_mem = tn.t_mem DIFF {b | d <= b /\ b < d+32}` by
    (mp_tac (Q.SPECL [`iid+1`,`Var dst`,`Var x`] prefix_mstore_mem_taint) >>
     disch_then (qspec_then `u` mp_tac) >>
     simp[Abbr `u`,Abbr `t`,Abbr `q`,Abbr `j`,op_taint_def,FLOOKUP_UPDATE]) >>
  simp[] >>
  simp[Abbr `j`,SRULE [LET_THM] prefix_mstore_taint_frame,
    op_taint_def,Abbr `q`,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT] >>
  fs[op_taint_def] >> SET_TAC[]
QED

Theorem prefix_loop_count_header_block_interior:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  eval_operand (Var dst) s = SOME (n2w d) /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (rb,sz) /\ rb <= d /\ d+32 <= rb+sz /\ d < dimword (:256) /\ dst <> x /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst iid DLOAD [src] [x];
      j = mk_inst (iid+1) MSTORE [Var dst;Var x] [];
      w = abi_decode_load DLOAD a s;
      u = update_var x w s;
      t = mstore d w u;
      H = DRESTRICT G (COMPL {x});
      q = tn with t_var := tn.t_var |+ (x,{});
      qt = step_taint j u t q
  in isPREFIX [i;j] (DROP s.vs_inst_idx bb.bb_instructions) ==>
     run_inst_seq [i;j] s = OK t /\
     (ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := s.vs_inst_idx+2) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qabbrev_tac `a1 = update_var x (abi_decode_load DLOAD a s) s` >>
  qabbrev_tac `a2 = mstore d (abi_decode_load DLOAD a s) a1` >>
  qabbrev_tac `H = DRESTRICT G (COMPL {x})` >>
  qabbrev_tac `q1 = tn with t_var := tn.t_var |+ (x,{})` >>
  qabbrev_tac `q2 = step_taint (mk_inst (iid+1) MSTORE [Var dst;Var x] []) a1 a2 q1` >>
  qabbrev_tac `u = (\j. EL j [s;a1;a2])` >>
  qabbrev_tac `g = (\j. EL j [G;H;H])` >>
  qabbrev_tac `q = (\j. EL j [tn;q1;q2])` >>
  qabbrev_tac `xs = [mk_inst iid DLOAD [src] [x];mk_inst (iid+1) MSTORE [Var dst;Var x] []]` >>
  `!j. j < LENGTH xs ==>
    step_inst_base (EL j xs) (u j) = OK (u (SUC j)) /\
    step_inst fuel ctx (EL j xs) ((u j) with vs_inst_idx := s.vs_inst_idx+j) =
      OK ((u (SUC j)) with vs_inst_idx := s.vs_inst_idx+j) /\
    ptr_safe_step D lo fuel ctx fn PG (g j) (q j) (EL j xs)
      ((u j) with vs_inst_idx := s.vs_inst_idx+j) /\
    ghost_step fuel ctx PG (g j) (q j) (EL j xs)
      ((u j) with vs_inst_idx := s.vs_inst_idx+j) = (g (SUC j),q (SUC j))` by
    suspend "trace" >>
  `u 0 = s /\ g 0 = G /\ q 0 = tn` by simp[Abbr `u`,Abbr `g`,Abbr `q`] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs` by
    simp[Abbr `xs`,mk_inst_def,is_terminator_def] >>
  drule_all prefix_trace_ptr_safe_block >>
  simp[Abbr `u`,Abbr `g`,Abbr `q`,Abbr `xs`,Abbr `a1`,Abbr `a2`,
    Abbr `H`,Abbr `q1`,Abbr `q2`]
QED

Resume prefix_loop_count_header_block_interior[trace]:
  gen_tac >> simp[Abbr `xs`] >> strip_tac >>
  `j = 0 \/ j = 1` by decide_tac >>
  `!k. allocas_from lo (s with vs_inst_idx := k) /\
    abi_decode_load DLOAD a (s with vs_inst_idx := k) = abi_decode_load DLOAD a s` by
    (fs[allocas_from_def,abi_decode_load_def,abi_decode_source_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := s.vs_inst_idx+j`]
    prefix_loop_count_header_steps_interior) >>
  simp[eval_op_inst_idx,prefix_copy_pure_taint] >> strip_tac >>
  simp[Abbr `u`,Abbr `g`,Abbr `q`,Abbr `a1`,Abbr `a2`,Abbr `H`,
    Abbr `q1`,Abbr `q2`] >>
  `!v k. update_var x v (s with vs_inst_idx := k) =
    (update_var x v s) with vs_inst_idx := k` by simp[update_var_def] >>
  `!v k. mstore d v (update_var x v (s with vs_inst_idx := k)) =
    (mstore d v (update_var x v s)) with vs_inst_idx := k` by
    simp[update_var_def,mstore_def] >>
  fs[prefix_loop_slot_taint_idx,mk_inst_def] >>
  mp_tac prefix_loop_count_header_steps_interior >>
  simp[prefix_copy_pure_taint] >> strip_tac >>
  gvs[step_inst_non_invoke,mk_inst_def,update_var_def,mstore_def]
QED

Finalise prefix_loop_count_header_block_interior

Theorem prefix_loop_count_header_run_interior:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  eval_operand (Var dst) s = SOME (n2w d) /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (rb,sz) /\ rb <= d /\ d+32 <= rb+sz /\ d < dimword (:256) /\ dst <> x /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst iid DLOAD [src] [x];
    mk_inst (iid+1) MSTORE [Var dst;Var x] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  let u = update_var x (abi_decode_load DLOAD a s) s;
      t = mstore d (abi_decode_load DLOAD a s) u;
      H = DRESTRICT G (COMPL {x});
      q = tn with t_var := tn.t_var |+ (x,{});
      qt = step_taint (mk_inst (iid+1) MSTORE [Var dst;Var x] []) u t q
  in run_inst_seq [mk_inst iid DLOAD [src] [x];
       mk_inst (iid+1) MSTORE [Var dst;Var x] []] s = OK t /\
     ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
        (t with vs_inst_idx := s.vs_inst_idx+2)) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  mp_tac prefix_loop_count_header_block_interior >> simp[] >> strip_tac >>
  asm_rewrite_tac[] >> strip_tac >> qx_gen_tac `f` >>
  mp_tac (Q.INST [`fuel` |-> `f`] prefix_loop_count_header_block_interior) >>
  simp[] >> strip_tac >>
  gvs[ptr_safe_run_def,update_var_def,mstore_def] >> metis_tac[]
QED

Theorem prefix_loop_count_header_code:
  abi_decode_array_header dst src DLOAD st = (cnt,st') ==>
  ?x. cnt = Var x /\
    emitted_insts st st' = [mk_inst st.cs_next_id DLOAD [src] [x];
      mk_inst (st.cs_next_id+1) MSTORE [dst;Var x] []]
Proof
  simp[abi_decode_array_header_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def,emit_op_def,emit_void_def,fresh_var_def,fresh_id_def,emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >> simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

Theorem prefix_loop_count_header_semantic:
  abi_decode_array_header dst src DLOAD st = (cnt,st') /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w d) /\
  d < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  run_inst_seq (emitted_insts st st') s = OK t ==>
  eval_operand cnt t = SOME (abi_decode_load DLOAD a s) /\
  mem_word_at d t.vs_memory = abi_decode_load DLOAD a s /\
  fresh_vars_wrt limit_st t /\ abi_decode_frame d 32 s t /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\
  t.vs_labels = s.vs_labels /\
  abi_encoder_registered_effect {} [(d,32)] s t /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule_all ctor_actual_array_count_header_reentry >>
  strip_tac >> gvs[]
QED

Theorem prefix_loop_count_header_pair_interior:
  abi_decode_array_header (Var dst) src DLOAD st = (cnt,st') /\
  emitted_insts st st' = [mk_inst iid DLOAD [src] [x];
    mk_inst (iid+1) MSTORE [Var dst;Var x] []] /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  eval_operand (Var dst) s = SOME (n2w d) /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (rb,sz) /\ rb <= d /\ d+32 <= rb+sz /\ d < dimword (:256) /\ dst <> x /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H qt.
    run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand cnt t = SOME (abi_decode_load DLOAD a s) /\
    mem_word_at d t.vs_memory = abi_decode_load DLOAD a s /\
    fresh_vars_wrt limit_st t /\ abi_decode_frame d 32 s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    t.vs_labels = s.vs_labels /\
    abi_encoder_registered_effect {} [(d,32)] s t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    FLOOKUP H dst = SOME (rb,sz) /\
    op_taint qt (Var dst) = {} /\ op_taint qt cnt = {} /\
    DISJOINT qt.t_mem {b | d <= b /\ b < d+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. v <> x ==> FLOOKUP H v = FLOOKUP G v /\
      eval_operand (Var v) t = eval_operand (Var v) s /\
      op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
       (t with vs_inst_idx := s.vs_inst_idx+2)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  `isPREFIX [mk_inst iid DLOAD [src] [x];
    mk_inst (iid+1) MSTORE [Var dst;Var x] []]
    (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  mp_tac prefix_loop_count_header_run_interior >> simp[] >> strip_tac >>
  mp_tac prefix_loop_count_header_steps_interior >> simp[prefix_copy_pure_taint] >> strip_tac >>
  `cnt = Var x` by suspend "count_operand" >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK t` >>
  `eval_operand cnt t = SOME (abi_decode_load DLOAD a s) /\
   mem_word_at d t.vs_memory = abi_decode_load DLOAD a s /\
   fresh_vars_wrt limit_st t /\ abi_decode_frame d 32 s t /\
   (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
     eval_operand op t = SOME w) /\
   t.vs_labels = s.vs_labels /\
   abi_encoder_registered_effect {} [(d,32)] s t /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (irule prefix_loop_count_header_semantic >> simp[] >>
     qexistsl_tac [`Var dst`,`src`,`st'`] >> simp[]) >>
  qexistsl_tac [`DRESTRICT G (COMPL {x})`,
    `step_taint (mk_inst (iid+1) MSTORE [Var dst;Var x] [])
      (update_var x (abi_decode_load DLOAD a s) s) t
      (tn with t_var := tn.t_var |+ (x,{}))`] >>
  gvs[Abbr `t`,allocas_from_def,SRULE [LET_THM] prefix_mstore_taint_frame,
    FLOOKUP_DRESTRICT,op_taint_def,FLOOKUP_UPDATE,eval_operand_def,
    lookup_var_def,update_var_def] >> metis_tac[]
QED

Resume prefix_loop_count_header_pair_interior[count_operand]:
  drule prefix_loop_count_header_code >> strip_tac >> gvs[mk_inst_def]
QED

Finalise prefix_loop_count_header_pair_interior

Theorem prefix_loop_count_guard_code:
  abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn asz st = ((),st') ==>
  ?x y z. emitted_insts st st' =
    [mk_inst st.cs_next_id DLOAD [src] [x];
     mk_inst (st.cs_next_id+1) GT [Var x;Lit (n2w maxn)] [y];
     mk_inst (st.cs_next_id+2) ISZERO [Var y] [z];
     mk_inst (st.cs_next_id+3) ASSERT [Var z] []]
Proof
  simp[abi_decode_dynarray_prefix_def,abi_decode_count_guard_def,
    abi_decode_dynarray_end_guard_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def,emit_op_def,emit_void_def,fresh_var_def,fresh_id_def,emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND,mk_inst_def]
QED

Theorem prefix_loop_count_guard_run:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  abi_decode_load DLOAD a s = n2w cnt /\ cnt <= limit /\ limit < dimword (:256) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst iid DLOAD [src] [x];
    mk_inst (iid+1) GT [Var x;Lit (n2w limit)] [y];
    mk_inst (iid+2) ISZERO [Var y] [z];mk_inst (iid+3) ASSERT [Var z] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  let t = update_var z 1w (update_var y 0w (update_var x (n2w cnt) s));
      H = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x})) (COMPL {y})) (COMPL {z});
      qt = tn with t_var := ((tn.t_var |+ (x,{})) |+ (y,{})) |+ (z,{})
  in run_inst_seq [mk_inst iid DLOAD [src] [x];
       mk_inst (iid+1) GT [Var x;Lit (n2w limit)] [y];
       mk_inst (iid+2) ISZERO [Var y] [z];mk_inst (iid+3) ASSERT [Var z] []] s = OK t /\
     ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
        (t with vs_inst_idx := s.vs_inst_idx+4)) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  mp_tac prefix_copy_count_success_block >> simp[] >> strip_tac >>
  asm_rewrite_tac[] >> strip_tac >> qx_gen_tac `f` >>
  mp_tac (Q.INST [`fuel` |-> `f`] prefix_copy_count_success_block) >>
  simp[] >> strip_tac >>
  gvs[ptr_safe_run_def,update_var_def,INTER_ASSOC] >> metis_tac[]
QED

Theorem prefix_loop_index_observation_pair:
  abi_decode_index_init st = (ip,st') /\
  (!i. MEM i (emitted_insts st st') ==> MEM i (fn_insts fn)) /\
  st.cs_next_id IN ctor_actual_sites fn ids /\
  ctor_actual_scratch fn ids B N s /\ B+N <= s.vs_alloca_next /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  B <= d /\ d+32 <= B+N /\ mload d s = n2w (LENGTH vs) /\
  st.cs_next_var < limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME
    (mk_inst st.cs_next_id ALLOCA [Lit 32w] [iv]) /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME
    (mk_inst (st.cs_next_id+1) MSTORE [Var iv;Lit 0w] []) /\
  ip = Var iv ==>
  ?t p H qt.
    run_inst_seq (emitted_insts st st') s = OK t /\
    ctor_actual_array_observation ctx fn site ids B N d outsz
      st.cs_next_var limit_st tv vs st.cs_next_id p s 0 0 t /\
    FLOOKUP H iv = SOME (p,32) /\
    eval_operand ip t = SOME (n2w p) /\ op_taint qt ip = {} /\
    DISJOINT qt.t_mem {b | p <= b /\ b < p+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ lo <= p /\
    (!v. v <> iv ==> FLOOKUP H v = FLOOKUP G v /\
      eval_operand (Var v) t = eval_operand (Var v) s /\
      op_taint qt (Var v) = op_taint tn (Var v)) /\
    (!b n. b+n <= p \/ p+32 <= b ==>
      mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
    t.vs_current_bb = s.vs_current_bb /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
       (t with vs_inst_idx := s.vs_inst_idx+2)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >>
  drule_all ctor_actual_array_index_observation >>
  disch_then (qspecl_then [`tv`,`outsz`] strip_assume_tac) >>
  `FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
   alloca_inv t /\ alloca_frontier_inv ctx fn site t` by
    fs[ctor_actual_array_observation_def] >>
  `p < dimword (:256)` by (irule ctor_actual_index_slot_bound >> metis_tac[]) >>
  `emitted_insts st st' = [mk_inst st.cs_next_id ALLOCA [Lit 32w] [iv];
    mk_inst (st.cs_next_id+1) MSTORE [Var iv;Lit 0w] []]` by
    (drule ctor_actual_index_insts >> drule abi_decode_index_init_shape >> simp[]) >>
  `run_inst_seq [mk_inst st.cs_next_id ALLOCA [Lit 32w] [iv];
    mk_inst (st.cs_next_id+1) MSTORE [Var iv;Lit 0w] []] s = OK t` by metis_tac[] >>
  drule_all prefix_loop_index_slot_run >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  qexistsl_tac [`t`,`p`,`H`,`qt`] >> simp[] >> metis_tac[]
QED

(* Original base-address interfaces remain available as specializations. *)
Theorem prefix_loop_count_header_steps:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  eval_operand (Var dst) s = SOME (n2w d) /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (d,sz) /\ 32 <= sz /\ d < dimword (:256) /\ dst <> x /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst iid DLOAD [src] [x];
      j = mk_inst (iid+1) MSTORE [Var dst;Var x] [];
      w = abi_decode_load DLOAD a s;
      u = update_var x w s;
      t = mstore d w u;
      H = DRESTRICT G (COMPL {x});
      q = step_taint i s u tn;
      qt = step_taint j u t q
  in step_inst_base i s = OK u /\ step_inst_base j u = OK t /\
     ghost_step fuel ctx PG G tn i s = (H,q) /\
     ghost_step fuel ctx PG H q j u = (H,qt) /\
     ptr_safe_step D lo fuel ctx fn PG G tn i s /\
     ptr_safe_step D lo fuel ctx fn PG H q j u /\
     mload d t = w /\ DISJOINT qt.t_mem {b | d <= b /\ b < d+32} /\
     qt.t_mem SUBSET tn.t_mem /\
     op_taint qt (Var dst) = {} /\ op_taint qt (Var x) = {} /\
     FLOOKUP H dst = SOME (d,sz)
Proof
  strip_tac >> irule prefix_loop_count_header_steps_interior >> simp[]
QED

Theorem prefix_loop_count_header_block:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  eval_operand (Var dst) s = SOME (n2w d) /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (d,sz) /\ 32 <= sz /\ d < dimword (:256) /\ dst <> x /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  let i = mk_inst iid DLOAD [src] [x];
      j = mk_inst (iid+1) MSTORE [Var dst;Var x] [];
      w = abi_decode_load DLOAD a s;
      u = update_var x w s;
      t = mstore d w u;
      H = DRESTRICT G (COMPL {x});
      q = tn with t_var := tn.t_var |+ (x,{});
      qt = step_taint j u t q
  in isPREFIX [i;j] (DROP s.vs_inst_idx bb.bb_instructions) ==>
     run_inst_seq [i;j] s = OK t /\
     (ptr_safe_block D lo fuel ctx fn PG H qt bb
        (t with vs_inst_idx := s.vs_inst_idx+2) ==>
      ptr_safe_block D lo fuel ctx fn PG G tn bb s)
Proof
  strip_tac >> irule prefix_loop_count_header_block_interior >> simp[]
QED

Theorem prefix_loop_count_header_run:
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  eval_operand (Var dst) s = SOME (n2w d) /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (d,sz) /\ 32 <= sz /\ d < dimword (:256) /\ dst <> x /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst iid DLOAD [src] [x];
    mk_inst (iid+1) MSTORE [Var dst;Var x] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  let u = update_var x (abi_decode_load DLOAD a s) s;
      t = mstore d (abi_decode_load DLOAD a s) u;
      H = DRESTRICT G (COMPL {x});
      q = tn with t_var := tn.t_var |+ (x,{});
      qt = step_taint (mk_inst (iid+1) MSTORE [Var dst;Var x] []) u t q
  in run_inst_seq [mk_inst iid DLOAD [src] [x];
       mk_inst (iid+1) MSTORE [Var dst;Var x] []] s = OK t /\
     ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
        (t with vs_inst_idx := s.vs_inst_idx+2)) ==>
      !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> irule prefix_loop_count_header_run_interior >> fs[]
QED

Theorem prefix_loop_count_header_pair:
  abi_decode_array_header (Var dst) src DLOAD st = (cnt,st') /\
  emitted_insts st st' = [mk_inst iid DLOAD [src] [x];
    mk_inst (iid+1) MSTORE [Var dst;Var x] []] /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  eval_operand (Var dst) s = SOME (n2w d) /\ op_taint tn (Var dst) = {} /\
  FLOOKUP G dst = SOME (d,sz) /\ 32 <= sz /\ d < dimword (:256) /\ dst <> x /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H qt.
    run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand cnt t = SOME (abi_decode_load DLOAD a s) /\
    mem_word_at d t.vs_memory = abi_decode_load DLOAD a s /\
    fresh_vars_wrt limit_st t /\ abi_decode_frame d 32 s t /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w) /\
    t.vs_labels = s.vs_labels /\
    abi_encoder_registered_effect {} [(d,32)] s t /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\
    FLOOKUP H dst = SOME (d,sz) /\
    op_taint qt (Var dst) = {} /\ op_taint qt cnt = {} /\
    DISJOINT qt.t_mem {b | d <= b /\ b < d+32} /\ qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    (!v. v <> x ==> FLOOKUP H v = FLOOKUP G v /\
      eval_operand (Var v) t = eval_operand (Var v) s /\
      op_taint qt (Var v) = op_taint tn (Var v)) /\
    ((!fuel. ptr_safe_run D lo fuel ctx fn PG H qt
       (t with vs_inst_idx := s.vs_inst_idx+2)) ==>
     !fuel. ptr_safe_run D lo fuel ctx fn PG G tn s)
Proof
  strip_tac >> irule prefix_loop_count_header_pair_interior >>
  simp[] >> conj_tac >- (qexistsl_tac [`iid`,`src`] >> simp[]) >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> simp[]
QED

Theorem prefix_loop_guard_outputs[local]:
  abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn asz st = ((),st') /\
  emitted_insts st st' =
    [mk_inst st.cs_next_id DLOAD [src] [x];
     mk_inst (st.cs_next_id+1) GT [Var x;Lit (n2w maxn)] [y];
     mk_inst (st.cs_next_id+2) ISZERO [Var y] [z];
     mk_inst (st.cs_next_id+3) ASSERT [Var z] []] ==>
  !v. abi_decoder_older_vars st.cs_next_var v ==> v <> x /\ v <> y /\ v <> z
Proof
  simp[abi_decode_dynarray_prefix_def,abi_decode_count_guard_def,
    abi_decode_dynarray_end_guard_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def,emit_op_def,emit_void_def,fresh_var_def,fresh_id_def,emit_def] >>
  strip_tac >> gvs[emitted_insts_def] >>
  fs[GSYM APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND,mk_inst_def] >>
  simp[abi_decoder_older_vars_def] >> metis_tac[LESS_EQ_REFL,DECIDE ``n <= n+1``,DECIDE ``n <= n+2``]
QED

Theorem prefix_loop_raw_indexed[local]:
  inst_extends st st' /\ st'.cs_blocks = st.cs_blocks /\
  st'.cs_current_bb = st.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st') /\
  run_inst_seq (emitted_insts st st') s = OK raw /\
  fn_has_code st st' fn /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  let t = raw with vs_inst_idx := LENGTH st'.cs_current_insts in
  ~t.vs_halted /\ t.vs_current_bb = st'.cs_current_bb /\
  abi_decode_sim ctx fn s t
Proof
  strip_tac >>
  `frag_exec ctx st st' (\u. u = s)
    (\t. t = raw with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> fs[inst_extends_def]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]
QED

Theorem prefix_loop_observation_index[local]:
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot baseline prefix cursor s ==>
  ctor_actual_array_observation ctx func site ids D N d outsz next limit_st
    tv vs slot_id slot baseline prefix cursor (s with vs_inst_idx := k)
Proof
  rewrite_tac[ctor_actual_array_observation_def,alloca_inv_def,
    allocas_non_overlapping_def,alloca_next_valid_def,alloca_frontier_inv_def,
    remaining_alloca_budget_def,ctor_actual_scratch_def,fresh_vars_wrt_def,
    lookup_var_def,mload_def,abi_encoder_registered_effect_def] >>
  rewrite_tac[venom_state_accfupds]
QED

Theorem prefix_loop_instruction[local]:
  isPREFIX xs (DROP k bb.bb_instructions) /\ n < LENGTH xs ==>
  get_instruction bb (k+n) = SOME (EL n xs)
Proof
  rpt strip_tac >> gvs[rich_listTheory.IS_PREFIX_APPEND] >>
  `LENGTH (DROP k bb.bb_instructions) = LENGTH xs + LENGTH l` by
    metis_tac[LENGTH_APPEND] >>
  `n < LENGTH (DROP k bb.bb_instructions)` by decide_tac >>
  `k+n < LENGTH bb.bb_instructions` by gvs[LENGTH_DROP] >>
  simp[get_instruction_def] >>
  qspecl_then [`n`,`k`,`bb.bb_instructions`] mp_tac EL_DROP >>
  simp[rich_listTheory.EL_APPEND1,ADD_COMM]
QED

Theorem prefix_loop_setup_pair:
  abi_decode_dynarray_prefix src DLOAD (Lit 0w) maxn asz st = ((),guard_st) /\
  abi_decode_array_header (Var dst) src DLOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand (Var dst) initial = SOME (n2w d) /\ d < dimword (:256) /\
  abi_decode_load DLOAD (n2w sb : bytes32) initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var dst) /\
  loop_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts func)) /\
  header_st.cs_next_id IN ctor_actual_sites func ids /\
  ctor_actual_scratch func ids D N initial /\ D+N <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv ctx func site initial /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts func)) /\
  unit_alloca_budget ctx < dimword (:256) /\
  D <= d /\ d+32 <= D+N /\ 32 <= outsz /\
  fn_has_code st guard_st func /\ fn_has_code guard_st header_st func /\
  fn_has_code header_st loop_st func /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  FLOOKUP G dst = SOME (b,sz) /\ b <= d /\ d+outsz <= b+sz /\
  op_taint tn src = {} /\ op_taint tn (Var dst) = {} /\
  allocas_from lo initial /\ lo <= initial.vs_alloca_next /\ ~ctx_has_dalloca ctx
  ==>
  ?prepared slot iv H qt.
    ip = Var iv /\
    ctor_actual_array_observation ctx func site ids D N d outsz
      st.cs_next_var limit_st tv vs header_st.cs_next_id slot initial 0 0 prepared /\
    ctor_actual_array_observation ctx func site ids D N d outsz
      loop_st.cs_next_var limit_st tv vs header_st.cs_next_id slot prepared 0 0 prepared /\
    ~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
    prepared.vs_inst_idx = LENGTH loop_st.cs_current_insts /\
    abi_decode_sim ctx func initial prepared /\
    eval_operand src prepared = SOME (n2w sb) /\
    eval_operand (Var dst) prepared = SOME (n2w d) /\
    eval_operand ip prepared = SOME (n2w slot) /\
    FLOOKUP H dst = SOME (b,sz) /\ FLOOKUP H iv = SOME (slot,32) /\
    op_taint qt src = {} /\ op_taint qt (Var dst) = {} /\ op_taint qt ip = {} /\
    DISJOINT qt.t_mem {a | d <= a /\ a < d+32} /\
    DISJOINT qt.t_mem {a | slot <= a /\ a < slot+32} /\
    qt.t_mem SUBSET tn.t_mem /\
    qt.t_stor = tn.t_stor /\ qt.t_trans = tn.t_trans /\ qt.t_imm = tn.t_imm /\
    allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\ lo <= slot /\
    (!x. abi_decoder_older_vars st.cs_next_var x ==>
      FLOOKUP H x = FLOOKUP G x /\ op_taint qt (Var x) = op_taint tn (Var x)) /\
    ((!fuel. ptr_safe_run Ddead lo fuel ctx func PG H qt prepared) ==>
      !fuel. ptr_safe_run Ddead lo fuel ctx func PG G tn initial)
Proof
  strip_tac >>
  `abi_decode_source_opcode DLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule prefix_loop_count_guard_code >> strip_tac >>
  `?bb. lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX guard_st.cs_current_insts bb.bb_instructions` by
    (qpat_x_assum `fn_has_code st guard_st func` mp_tac >>
     simp[fn_has_code_def] >> metis_tac[]) >>
  `isPREFIX (emitted_insts st guard_st)
    (DROP initial.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX guard_st.cs_current_insts _` mp_tac >>
     asm_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     fs[inst_extends_def] >>
     asm_rewrite_tac[GSYM APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst st.cs_next_id DLOAD [src] [x];
    mk_inst (st.cs_next_id+1) GT [Var x;Lit (n2w maxn)] [y];
    mk_inst (st.cs_next_id+2) ISZERO [Var y] [z];
    mk_inst (st.cs_next_id+3) ASSERT [Var z] []]
    (DROP initial.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  mp_tac (Q.INST [`s` |-> `initial`, `iid` |-> `st.cs_next_id`,
    `cnt` |-> `LENGTH (vs : value list)`, `limit` |-> `maxn`, `fn` |-> `func`,
    `a` |-> `n2w sb`, `D` |-> `Ddead`]
    prefix_loop_count_guard_run) >>
  simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ initial = OK guard_raw` >>
  `guard_st.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `abi_decoder_operand_live st.cs_next_var (Lit 0w)` by
    simp[abi_decoder_operand_live_def] >>
  mp_tac (Q.INST [`hi` |-> `Lit 0w`, `n` |-> `LENGTH (vs : value list)`,
    `st'` |-> `guard_st`] ctor_actual_array_prefix_reentry) >>
  simp[] >>
  strip_tac >>
  `LENGTH guard_st.cs_current_insts = LENGTH st.cs_current_insts+4` by
    (qpat_x_assum `emitted_insts st guard_st = _` mp_tac >>
     fs[inst_extends_def,emitted_insts_def] >>
     disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `ptr_safe_run Ddead lo _ ctx func PG GG gt _` >>
  qabbrev_tac `guard = guard_raw with vs_inst_idx := LENGTH guard_st.cs_current_insts` >>
  `~guard.vs_halted /\ guard.vs_current_bb = guard_st.cs_current_bb /\
   abi_decode_sim ctx func initial guard` by
    (mp_tac (Q.INST [`st'` |-> `guard_st`, `s` |-> `initial`,
       `raw` |-> `guard_raw`, `fn` |-> `func`] prefix_loop_raw_indexed) >>
     fs[Abbr `guard`,EVERY_CONJ]) >>
  `fresh_vars_wrt limit_st guard /\
   abi_decoder_address_frame st.cs_next_var initial guard /\
   abi_encoder_registered_effect {} [] initial guard /\
   guard.vs_inst_idx = LENGTH guard_st.cs_current_insts` by
    fs[Abbr `guard`,fresh_vars_wrt_def,abi_decoder_address_frame_def,
      eval_op_inst_idx,abi_encoder_registered_effect_def] >>
  mp_tac (Q.INST [`st'` |-> `guard_st`] prefix_loop_guard_outputs) >>
  simp[] >> disch_tac >>
  `FLOOKUP GG dst = SOME (b,sz) /\ op_taint gt src = {} /\
   op_taint gt (Var dst) = {} /\
   (!v. abi_decoder_older_vars st.cs_next_var v ==>
      FLOOKUP GG v = FLOOKUP G v /\ op_taint gt (Var v) = op_taint tn (Var v))` by
    (`dst <> x /\ dst <> y /\ dst <> z` by
       (fs[abi_decoder_operand_live_def,IN_DEF] >> metis_tac[]) >>
     simp[Abbr `GG`,Abbr `gt`,FLOOKUP_DRESTRICT,op_taint_def,
       FLOOKUP_UPDATE] >>
     conj_tac >- (Cases_on `src` >> fs[op_taint_def,abi_decoder_operand_live_def,IN_DEF] >>
       metis_tac[]) >>
     fs[op_taint_def]) >>
  `eval_operand src guard = SOME (n2w sb) /\
   eval_operand (Var dst) guard = SOME (n2w d) /\
   guard.vs_allocas = initial.vs_allocas /\
   guard.vs_alloca_next = initial.vs_alloca_next /\
   guard.vs_data_section = initial.vs_data_section` by
    fs[abi_decoder_address_frame_def] >>
  `allocas_from lo guard /\ lo <= guard.vs_alloca_next /\
   abi_decoder_operand_live guard_st.cs_next_var src /\
   abi_decoder_operand_live guard_st.cs_next_var (Var dst)` by
    (fs[allocas_from_def] >> metis_tac[abi_decoder_operand_live_mono]) >>
  `?hx. emitted_insts guard_st header_st =
    [mk_inst guard_st.cs_next_id DLOAD [src] [hx];
     mk_inst (guard_st.cs_next_id+1) MSTORE [Var dst;Var hx] []]` by
    metis_tac[prefix_loop_count_header_code] >>
  `dst <> hx` by suspend "header_fresh" >>
  `?hb. lookup_block guard.vs_current_bb func.fn_blocks = SOME hb /\
    isPREFIX (emitted_insts guard_st header_st)
      (DROP guard.vs_inst_idx hb.bb_instructions)` by suspend "header_lookup" >>
  mp_tac (Q.INST [`st` |-> `guard_st`, `st'` |-> `header_st`,
    `s` |-> `guard`, `G` |-> `GG`, `tn` |-> `gt`, `fn` |-> `func`,
    `bb` |-> `hb`, `x` |-> `hx`, `iid` |-> `guard_st.cs_next_id`,
    `a` |-> `n2w sb`, `rb` |-> `b`, `D` |-> `Ddead`]
    prefix_loop_count_header_pair_interior) >>
  simp[] >>
  strip_tac >> rename1 `FLOOKUP HG dst = SOME (b,sz)` >>
  suspend "after_header"
QED

Resume prefix_loop_setup_pair[header_fresh]:
  qpat_x_assum `abi_decoder_operand_live guard_st.cs_next_var (Var dst)` mp_tac >>
  qpat_x_assum `emitted_insts guard_st header_st = _` mp_tac >>
  qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  fs[abi_decode_array_header_def,comp_bind_def,comp_ignore_bind_def,
    comp_return_def,emit_op_def,emit_void_def,fresh_var_def,fresh_id_def,emit_def] >>
  gvs[emitted_insts_def] >>
  fs[GSYM APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND,mk_inst_def] >>
  fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def]
QED

Resume prefix_loop_setup_pair[header_lookup]:
  qpat_x_assum `fn_has_code guard_st header_st func` mp_tac >>
  simp[fn_has_code_def] >> strip_tac >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `isPREFIX header_st.cs_current_insts _` mp_tac >>
  asm_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
  fs[inst_extends_def] >>
  asm_rewrite_tac[GSYM APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[rich_listTheory.IS_PREFIX_APPEND,DROP_APPEND,DROP_LENGTH_TOO_LONG]
QED

Resume prefix_loop_setup_pair[after_header]:
  `LENGTH header_st.cs_current_insts = LENGTH guard_st.cs_current_insts+2` by
    (qpat_x_assum `emitted_insts guard_st header_st = _` mp_tac >>
     fs[inst_extends_def,emitted_insts_def] >>
     disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  qabbrev_tac `header = t with vs_inst_idx := LENGTH header_st.cs_current_insts` >>
  `~header.vs_halted /\ header.vs_current_bb = header_st.cs_current_bb /\
   abi_decode_sim ctx func guard header` by
    (mp_tac (Q.INST [`st` |-> `guard_st`, `st'` |-> `header_st`, `s` |-> `guard`,
       `raw` |-> `t`, `fn` |-> `func`] prefix_loop_raw_indexed) >>
     fs[Abbr `header`,EVERY_CONJ]) >>
  `fresh_vars_wrt limit_st header /\ allocas_from lo header /\
   lo <= header.vs_alloca_next /\
   header.vs_inst_idx = LENGTH header_st.cs_current_insts /\
   abi_decode_frame d 32 guard header /\
   abi_encoder_registered_effect {} [(d,32)] guard header /\
   header.vs_labels = guard.vs_labels /\
   (!op w. abi_decoder_operand_live guard_st.cs_next_var op /\
     eval_operand op guard = SOME w ==> eval_operand op header = SOME w)` by
    (fs[Abbr `header`,fresh_vars_wrt_def,allocas_from_def,abi_decode_frame_def,
      eval_op_inst_idx,abi_encoder_registered_effect_def] >>
     metis_tac[]) >>
  `t.vs_allocas = guard.vs_allocas /\ t.vs_alloca_next = guard.vs_alloca_next` by
    (irule abi_decode_sequence_allocation_frame >>
     qexists_tac `emitted_insts guard_st header_st` >>
     simp[EVERY_CONJ,is_terminator_def,is_alloca_op_def]) >>
  `header.vs_allocas = initial.vs_allocas /\
   header.vs_alloca_next = initial.vs_alloca_next` by fs[Abbr `header`] >>
  `alloca_inv header /\ alloca_frontier_inv ctx func site header /\
   ctor_actual_scratch func ids D N header /\ D+N <= header.vs_alloca_next` by
    (qpat_x_assum `alloca_inv initial` mp_tac >>
     qpat_x_assum `alloca_frontier_inv ctx func site initial` mp_tac >>
     qpat_x_assum `ctor_actual_scratch func ids D N initial` mp_tac >>
     qpat_x_assum `D+N <= initial.vs_alloca_next` mp_tac >>
     qpat_x_assum `header.vs_allocas = initial.vs_allocas` mp_tac >>
     qpat_x_assum `header.vs_alloca_next = initial.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     fs[alloca_inv_def,allocas_non_overlapping_def,alloca_next_valid_def,
       alloca_frontier_inv_def,remaining_alloca_budget_def,ctor_actual_scratch_def] >>
     metis_tac[]) >>
  `abi_decode_load DLOAD (n2w sb : bytes32) guard = n2w (LENGTH vs)` by
    (qpat_x_assum `abi_decode_load _ _ initial = _` mp_tac >>
     simp[abi_decode_load_def,abi_decode_source_def]) >>
  `mload d header = n2w (LENGTH vs)` by fs[Abbr `header`,mem_word_at_eq_mload,mload_def] >>
  `header_st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  `emitted_insts header_st loop_st =
    [mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString header_st.cs_next_var)];
     mk_inst (header_st.cs_next_id+1) MSTORE [ip;Lit 0w] []]` by
    (drule ctor_actual_index_insts >> simp[]) >>
  `?ibb. lookup_block header.vs_current_bb func.fn_blocks = SOME ibb /\
    get_instruction ibb header.vs_inst_idx = SOME
      (mk_inst header_st.cs_next_id ALLOCA [Lit 32w]
        [STRING #"%" (toString header_st.cs_next_var)]) /\
    get_instruction ibb (SUC header.vs_inst_idx) = SOME
      (mk_inst (header_st.cs_next_id+1) MSTORE [ip;Lit 0w] [])` by
    suspend "index_lookup" >>
  qpat_x_assum `get_instruction ibb (SUC header.vs_inst_idx) = _` mp_tac >>
  qpat_assum `ip = Var _` (fn th => pure_rewrite_tac[th]) >> disch_tac >>
  drule_all prefix_loop_index_observation_pair >>
  disch_then (qspecl_then [`tv`,`qt`,`outsz`,`PG`,`HG`,`Ddead`] strip_assume_tac) >>
  rename1 `run_inst_seq (emitted_insts header_st loop_st) header = OK index_raw` >>
  suspend "after_index"
QED

Resume prefix_loop_setup_pair[index_lookup]:
  qpat_x_assum `fn_has_code header_st loop_st func` mp_tac >>
  simp[fn_has_code_def] >> strip_tac >>
  rename1 `isPREFIX loop_st.cs_current_insts iblock.bb_instructions` >>
  `isPREFIX (emitted_insts header_st loop_st)
    (DROP header.vs_inst_idx iblock.bb_instructions)` by
    (qpat_x_assum `isPREFIX loop_st.cs_current_insts _` mp_tac >>
     asm_rewrite_tac[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
     fs[inst_extends_def] >>
     asm_rewrite_tac[GSYM APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[rich_listTheory.IS_PREFIX_APPEND,DROP_APPEND,DROP_LENGTH_TOO_LONG]) >>
  drule prefix_loop_instruction >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> disch_tac >>
  drule prefix_loop_instruction >>
  disch_then (qspec_then `1` mp_tac) >> simp[ADD1] >> disch_tac >>
  qexists_tac `iblock` >> simp[]
QED

Resume prefix_loop_setup_pair[after_index]:
  `LENGTH loop_st.cs_current_insts = LENGTH header_st.cs_current_insts+2` by
    (qpat_x_assum `emitted_insts header_st loop_st = _` mp_tac >>
     fs[inst_extends_def,emitted_insts_def] >>
     disch_then (mp_tac o Q.AP_TERM `LENGTH`) >> simp[]) >>
  qabbrev_tac `prepared = index_raw with vs_inst_idx := LENGTH loop_st.cs_current_insts` >>
  `~prepared.vs_halted /\ prepared.vs_current_bb = loop_st.cs_current_bb /\
   abi_decode_sim ctx func header prepared` by
    (mp_tac (Q.INST [`st` |-> `header_st`, `st'` |-> `loop_st`, `s` |-> `header`,
       `raw` |-> `index_raw`, `fn` |-> `func`] prefix_loop_raw_indexed) >>
     fs[Abbr `prepared`,EVERY_CONJ]) >>
  `ctor_actual_array_observation ctx func site ids D N d outsz
    header_st.cs_next_var limit_st tv vs header_st.cs_next_id p header 0 0 prepared` by
    (simp[Abbr `prepared`] >> irule prefix_loop_observation_index >> simp[]) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] guard header` by
    (irule abi_encoder_registered_effect_enlarge >>
     qexistsl_tac [`{}`,`[(d,32)]`] >> simp[] >> rpt strip_tac >> decide_tac) >>
  `header.vs_call_ctx = guard.vs_call_ctx /\
   header.vs_data_section = guard.vs_data_section` by fs[abi_decode_frame_def] >>
  `ctor_actual_array_observation ctx func site ids D N d outsz
    guard_st.cs_next_var limit_st tv vs header_st.cs_next_id p guard 0 0 prepared` by
    (irule ctor_actual_array_observation_rebase >>
     qexistsl_tac [`header_st.cs_next_var`,`header`] >>
     simp[abi_decode_frame_def] >> rpt strip_tac >>
     qpat_x_assum `!op w. abi_decoder_operand_live guard_st.cs_next_var op /\ _ ==> _`
       (qspec_then `Var x'` mp_tac) >>
     simp[abi_decoder_operand_live_def,eval_operand_def,IN_DEF]) >>
  `abi_encoder_registered_effect (ctor_actual_sites func ids) [(d,outsz)] initial guard` by
    (irule abi_encoder_registered_effect_enlarge >> qexistsl_tac [`{}`,`[]`] >> simp[]) >>
  `guard.vs_call_ctx = initial.vs_call_ctx /\
   guard.vs_data_section = initial.vs_data_section` by fs[abi_decoder_address_frame_def] >>
  `ctor_actual_array_observation ctx func site ids D N d outsz
    st.cs_next_var limit_st tv vs header_st.cs_next_id p initial 0 0 prepared` by
    (irule ctor_actual_array_observation_rebase >>
     qexistsl_tac [`guard_st.cs_next_var`,`guard`] >>
     `guard.vs_labels = initial.vs_labels` by simp[Abbr `guard`] >>
     simp[] >> rpt strip_tac >>
     qpat_x_assum `abi_decoder_address_frame st.cs_next_var initial guard`
       (mp_tac o MATCH_MP ctor_actual_address_old_vars) >>
     disch_then (qspecl_then [`x'`,`w`] mp_tac) >> simp[]) >>
  `ctor_actual_array_observation ctx func site ids D N d outsz
    loop_st.cs_next_var limit_st tv vs header_st.cs_next_id p prepared 0 0 prepared` by
    (irule ctor_actual_array_observation_self >> goal_assum (drule_at Any)) >>
  `abi_decode_sim ctx func initial prepared` by
    (irule abi_decode_sim_trans >> qexists_tac `guard` >> simp[] >>
     irule abi_decode_sim_trans >> qexists_tac `header` >> simp[]) >>
  `hx = STRING #"%" (toString guard_st.cs_next_var)` by
    (qpat_x_assum `emitted_insts guard_st header_st = _` mp_tac >>
     qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     fs[abi_decode_array_header_def,comp_bind_def,comp_ignore_bind_def,
       comp_return_def,emit_op_def,emit_void_def,fresh_var_def,fresh_id_def,emit_def] >>
     gvs[emitted_insts_def] >>
     fs[GSYM APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND,mk_inst_def]) >>
  `(!v. abi_decoder_older_vars st.cs_next_var v ==>
    FLOOKUP H v = FLOOKUP G v /\ op_taint qt' (Var v) = op_taint tn (Var v))` by
    (rpt strip_tac >>
     `v <> hx /\ v <> STRING #"%" (toString header_st.cs_next_var)` by
       (fs[abi_decoder_older_vars_def,IN_DEF] >> metis_tac[LESS_EQ_TRANS,DECIDE ``n <= n+1``]) >>
     metis_tac[]) >>
  `FLOOKUP H dst = SOME (b,sz) /\ op_taint qt' (Var dst) = {}` by
    (fs[abi_decoder_operand_live_def,IN_DEF] >> metis_tac[]) >>
  `op_taint qt' src = {}` by
    (Cases_on `src` >> fs[abi_decoder_operand_live_def,op_taint_def,IN_DEF] >> metis_tac[]) >>
  `eval_operand src header = SOME (n2w sb) /\
   eval_operand (Var dst) header = SOME (n2w d)` by metis_tac[] >>
  `index_raw.vs_labels = header.vs_labels` by
    (irule ctor_actual_sequence_labels >>
     qexists_tac `emitted_insts header_st loop_st` >>
     simp[abiDecoderVarSequenceTheory.abi_decoder_reentry_opcode_def,mk_inst_def]) >>
  `eval_operand src index_raw = SOME (n2w sb) /\
   eval_operand (Var dst) index_raw = SOME (n2w d)` by
    (conj_tac >-
       (Cases_on `src` >> fs[abi_decoder_operand_live_def,eval_operand_def,IN_DEF,
          abi_decoder_older_vars_def] >> metis_tac[LESS_EQ_TRANS,DECIDE ``n <= n+1``]) >>
     `dst <> STRING #"%" (toString header_st.cs_next_var)` by
       (fs[abi_decoder_operand_live_def,abi_decoder_older_vars_def,IN_DEF] >>
        metis_tac[LESS_EQ_TRANS,DECIDE ``n <= n+1``]) >> metis_tac[]) >>
  `gt.t_mem = tn.t_mem /\ gt.t_stor = tn.t_stor /\
   gt.t_trans = tn.t_trans /\ gt.t_imm = tn.t_imm` by simp[Abbr `gt`] >>
  `DISJOINT qt'.t_mem {a | d <= a /\ a < d+32} /\ qt'.t_mem SUBSET tn.t_mem` by
    (qpat_x_assum `DISJOINT qt.t_mem _` mp_tac >>
     qpat_x_assum `qt'.t_mem SUBSET qt.t_mem` mp_tac >>
     qpat_x_assum `qt.t_mem SUBSET gt.t_mem` mp_tac >>
     qpat_x_assum `gt.t_mem = tn.t_mem` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     fs[DISJOINT_DEF,SUBSET_DEF,EXTENSION] >> metis_tac[]) >>
  `allocas_from lo prepared /\ lo <= prepared.vs_alloca_next /\
   eval_operand src prepared = SOME (n2w sb) /\
   eval_operand (Var dst) prepared = SOME (n2w d) /\
   eval_operand ip prepared = SOME (n2w p)` by
    (qpat_x_assum `allocas_from lo index_raw` mp_tac >>
     qpat_x_assum `eval_operand ip index_raw = _` mp_tac >>
     simp[Abbr `prepared`,allocas_from_def,eval_op_inst_idx]) >>
  qexistsl_tac [`prepared`,`p`,`H`,`qt'`] >>
  asm_rewrite_tac[] >>
  gs[] >>
  simp[Abbr `prepared`]
QED

Finalise prefix_loop_setup_pair
