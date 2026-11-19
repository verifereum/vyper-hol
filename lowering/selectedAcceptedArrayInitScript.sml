(* Initialize a nonbulk array from the actual calldata count, including
   when its index allocation is being replayed. *)
Theory selectedAcceptedArrayInit
Ancestors
  venomFnInstsProofs decoderOriginAllocationFrame
  sourceOwnedArrayConstructorPtr selectedAcceptedInterfaces decoderArrayInitPtr
  physicalArrayInitSequence decoderNavigationPtr fragGasOriginPtrLoop
  entryDecoderStateFrame fragGasPathFrameMem logStoreDataOriginPtr
  actualIndexInitPtr actualDecoderAllocationPtr actualAllocExec allocaFrontierBound
  abiDecoderArrayInitReentry abiDecoderFrame abiDecoderRange abiDecoderArrayInit
  abiDecoderIndexInit abiDecoderContract entrySinkExtraction calldataDynOwned
  vyperCompiler emitHelperProps venomInst
  ptrDiscipline bodyPtrDefs compileEnv venomState venomExecSemantics
  venomMemDefs valueEncoding words arithmetic finite_map list pred_set rich_list
  selectedArrayInitTaintFrame fragGasOriginPtr abiDecoderArrayLoopInit
  abiDecoderDynarrayPrefix abiDecoderGuards abiDecoderBytesBound emitHelper
  exprLoweringProps fragExec abiEncoder abiDecoderDynarrayBound
  abiDecoderArrayHeader context loweringStateRelDefs calldataFiniteTransport
  bodyPtrPrecompileBuiltinsArithmeticValue

Theorem array_init_old_outputs[local]:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w)
    maxn abi_sz st = (setup,loop_st) /\ not_fresh_at st x ==>
  EVERY (\i. ~MEM x i.inst_outputs) (emitted_insts st loop_st)
Proof
  simp[abi_decode_array_loop_init_def, abi_decode_dynarray_position_prefix_def,
    abi_decode_bytes_head_def, compile_abi_dec_addr_def, abi_decode_count_guard_def,
    abi_decode_dynarray_payload_guard_def, abi_decode_array_header_def,
    abi_decode_index_init_def, compile_alloc_buffer_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def,
    fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  fs[DROP_LENGTH_APPEND, mk_inst_def, not_fresh_at_def] >>
  rpt conj_tac >> first_x_assum irule >> decide_tac
QED

Triviality array_init_pending_credit:
  MEM bb fn.fn_blocks /\ bb.bb_instructions = prefix ++ suffix /\
  bc.bb_instructions = prefix ==>
  pending_alloca_size (fn with fn_blocks := [bc]) s <= pending_alloca_size fn s
Proof
  strip_tac >>
  qpat_x_assum `MEM bb fn.fn_blocks`
    (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  simp[fn_insts_def, fn_insts_blocks_flat, pending_alloca_size_def,
       MAP_APPEND, FLAT_APPEND, FILTER_APPEND_DISTRIB, SUM_APPEND] >>
  decide_tac
QED

Theorem selected_array_init_to_header:
  abi_decode_array_loop_init (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    maxn abi_sz st = ((ip,cnt),loop_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st =
    ((hdr,body_lbl,exit_lbl),prefix_st) /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st prefix_st fn /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  st.cs_next_id <= header_st.cs_next_id /\ header_st.cs_next_id < last.cs_next_id /\
  loop_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit s /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var (Var root) /\
  eval_operand src s = SOME a /\ eval_operand (Var root) s = SOME (n2w d) /\
  abi_decode_load CALLDATALOAD a s = n2w n /\ n <= maxn /\ maxn < dimword (:256) /\
  alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ fn_inst_ids_distinct fn /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < st.cs_next_id \/ last.cs_next_id <= oid) /\
  base_addr <= d /\ 32 <= outsz /\ d+outsz <= base_addr+owner_cap /\
  d+outsz < dimword (:256) /\ ptr_covers G tn root s outsz /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  allocas_from lower s /\ lower <= s.vs_alloca_next /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size fn s <= w2n s.vs_initial_fmp) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (!id p k. st.cs_next_id <= id /\ id < last.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w])
  ==>
  ?t h H u q b.
    run_inst_seq (emitted_insts st loop_st) s = OK t /\
    h = jump_to hdr (t with vs_inst_idx := LENGTH loop_st.cs_current_insts) /\
    ~h.vs_halted /\ h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\
    ip = Var q /\ lookup_var q h = SOME (n2w b) /\
    eval_operand cnt h = SOME (n2w n) /\
    FLOOKUP h.vs_allocas header_st.cs_next_id = SOME (b,32) /\
    b+32 < dimword (:256) /\ b+32 <= h.vs_alloca_next /\
    (b+32 <= base_addr \/ base_addr+owner_cap <= b) /\
    mload b h = 0w /\ ptr_covers H u q h 32 /\ ptr_covers H u root h outsz /\
    mem_word_at d h.vs_memory = n2w n /\
    (!mem. mem_agree_outside u.t_mem h.vs_memory mem ==> mem_word_at d mem = n2w n) /\
    abi_decode_load CALLDATALOAD a h = n2w n /\
    (!i. b <= i /\ i < b+32 ==> i NOTIN u.t_mem) /\
    op_taint u src = {} /\ op_prov H src = NONE /\
    op_taint u cnt = {} /\ op_prov H cnt = NONE /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op h = eval_operand op s) /\
    (!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP u.t_var x = FLOOKUP tn.t_var x) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    abi_decode_footprint_frame [(d,32);(b,32)] s h /\ entry_decoder_obs s h /\
    alloca_inv h /\ alloca_frontier_inv ctx fn site h /\ allocas_from lower h /\
    s.vs_alloca_next <= h.vs_alloca_next /\ lower <= h.vs_alloca_next /\
    FLOOKUP h.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (!id p k. FLOOKUP s.vs_allocas id = SOME (p,k) ==>
      FLOOKUP h.vs_allocas id = SOME (p,k)) /\
    (!id. id <> header_st.cs_next_id ==> FLOOKUP h.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    (!id p k. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP h.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= h.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    fresh_vars_wrt limit h /\
    (!fuel r. run_from fuel ctx fn h = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn h ==> mem_safe_run fuel' ctx fn s)) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG) (s,G,tn) [] (OK h,H,u))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `d+32 <= base_addr+owner_cap /\ d < dimword (:256)` by decide_tac >>
  `d+32 <= s.vs_alloca_next` by
    (qpat_assum `alloca_inv s` mp_tac >>
     qpat_assum `FLOOKUP s.vs_allocas oid = _` mp_tac >>
     qpat_assum `d+32 <= base_addr+owner_cap` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[LESS_EQ_TRANS]) >>
  `eval_operand src s = SOME (n2w (w2n a)) /\
   abi_decode_load CALLDATALOAD (n2w (w2n (a:bytes32)):bytes32) s = n2w n` by simp[] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    (irule ctorAbiActualArrayRunTheory.ctor_actual_function_ids >> first_assum ACCEPT_TAC) >>
  drule_all source_array_init_owned_sequence >>
  disch_then (qx_choose_then `t` (qx_choose_then `b` (map_every assume_tac o CONJUNCTS))) >>
  qpat_x_assum `eval_operand src s = SOME (n2w (w2n a))` kall_tac >>
  qpat_x_assum `abi_decode_load CALLDATALOAD (n2w (w2n a)) s = _` kall_tac >>
  `not_fresh_at st root /\ (!x. src = Var x ==> not_fresh_at st x)` by
    (conj_tac >- (irule (iffLR calldata_operand_live_not_fresh) >> first_assum ACCEPT_TAC) >>
     rpt strip_tac >> irule (iffLR calldata_operand_live_not_fresh) >> gvs[]) >>
  `lookup_var root s = SOME (n2w d)` by (metis_tac[eval_operand_def]) >>
  drule actual_index_init_literal_site >> strip_tac >>
  `MEM inst (fn_insts fn)` by metis_tac[] >>
  `alloca_size inst = 32` by
    (qpat_assum `inst.inst_opcode = _` mp_tac >>
     qpat_assum `inst.inst_operands = _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> simp[alloca_size_def, dimword_def, fcpLib.INDEX_CONV ``dimindex (:256)``]) >>
  `!entry. FLOOKUP s.vs_allocas inst.inst_id = SOME entry ==>
    ?p. entry = (p,32) /\ p+32 <= s.vs_alloca_next` by
    (rpt strip_tac >> PairCases_on `entry` >>
     qpat_assum `!id p k. st.cs_next_id <= id /\ _ ==> _`
       (qspecl_then [`inst.inst_id`,`entry0`,`entry1`] mp_tac) >>
     asm_rewrite_tac[] >> rpt strip_tac >> (metis_tac[])) >>
  drule_all actual_word_alloca_physical_credit >> disch_tac >>
  `header_st.cs_next_id = loop_st.cs_next_id-2` by
    (drule abi_decode_index_init_shape >> strip_tac >> decide_tac) >>
  qpat_assum `header_st.cs_next_id = loop_st.cs_next_id-2` (fn k =>
    qpat_assum `inst.inst_id = header_st.cs_next_id` (fn j =>
      qpat_x_assum `(FLOOKUP s.vs_allocas inst.inst_id = NONE /\ _) \/ _`
        (assume_tac o REWRITE_RULE [j,k]))) >>
  drule_all actual_array_init_endpoint_joint_core >>
  disch_then (qspecl_then [`ARB`,`ctx`,`ARB`,`PG`,`ARB`]
    (qx_choose_then `H` (qx_choose_then `u`
      (qx_choose_then `q` (qx_choose_then `b'`
        (map_every assume_tac o CONJUNCTS o REWRITE_RULE [pairTheory.FST,pairTheory.SND])))))) >>
  `b' = b` by
    (`b < dimword (:256) /\ b' < dimword (:256)` by decide_tac >>
     qpat_assum `b' < dimword (:256)` mp_tac >>
     qpat_assum `b < dimword (:256)` mp_tac >>
     qpat_assum `eval_operand ip t = SOME (n2w b')` mp_tac >>
     qpat_assum `eval_operand ip t = SOME (n2w b)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> rpt strip_tac >> fs[LESS_MOD]) >>
  qpat_x_assum `b' = b` SUBST_ALL_TAC >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule_all run_inst_seq_preserves_entry_control >> simp[]) >>
  `LENGTH (emitted_insts st loop_st) + s.vs_inst_idx = LENGTH loop_st.cs_current_insts` by
    (qpat_assum `inst_extends st loop_st` mp_tac >>
     qpat_assum `s.vs_inst_idx = LENGTH st.cs_current_insts` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[inst_extends_def] >> strip_tac >>
     disch_then (fn th => simp[th, ADD_COMM])) >>
  `entry_decoder_obs s t` by
    (irule entry_decoder_sequence_obs >> goal_assum (drule_at Any) >>
     drule_all abi_decode_array_loop_init_reentry_code >> simp[]) >>
  qabbrev_tac `init = t with vs_inst_idx := LENGTH loop_st.cs_current_insts` >>
  `!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK init,H,u)` by (rpt gen_tac >> simp[Abbr `init`]) >>
  drule_all physicalArrayInitSequenceTheory.calldata_loop_prefix_entry_code >> strip_tac >>
  `lookup_block init.vs_current_bb fn.fn_blocks = SOME bb /\
   get_instruction bb init.vs_inst_idx = SOME (mk_inst loop_st.cs_next_id JMP [Label hdr] []) /\
   ~init.vs_halted` by
    (qpat_assum `Abbrev (init = _)` mp_tac >>
     qpat_assum `bb.bb_instructions = _` mp_tac >>
     qpat_assum `lookup_block loop_st.cs_current_bb fn.fn_blocks = _` mp_tac >>
     qpat_assum `loop_st.cs_current_bb = st.cs_current_bb` mp_tac >>
     qpat_assum `t.vs_current_bb = s.vs_current_bb` mp_tac >>
     qpat_assum `s.vs_current_bb = st.cs_current_bb` mp_tac >>
     qpat_assum `t.vs_halted <=> s.vs_halted` mp_tac >>
     qpat_assum `~s.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[Abbr `init`, get_instruction_def, EL_APPEND_EQN]) >>
  `b+32 <= t.vs_alloca_next` by
    (qpat_assum `alloca_inv t` mp_tac >>
     qpat_assum `FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (b,32)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `lower <= b` by
    (qpat_assum `(case FLOOKUP s.vs_allocas (loop_st.cs_next_id-2) of NONE => b = s.vs_alloca_next | SOME (slot,sz) => b = slot)` mp_tac >>
     qpat_assum `allocas_from lower s` mp_tac >>
     qpat_assum `lower <= s.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `FLOOKUP s.vs_allocas (loop_st.cs_next_id-2)` >> simp[] >>
     PairCases_on `x` >> simp[allocas_from_def] >> metis_tac[]) >>
  `allocas_from lower init` by
    (qpat_assum `allocas_from lower s` mp_tac >>
     qpat_assum `!id. id <> header_st.cs_next_id ==> FLOOKUP t.vs_allocas id = _` mp_tac >>
     qpat_assum `FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (b,32)` mp_tac >>
     qpat_assum `lower <= b` mp_tac >> qpat_assum `Abbrev (init = _)` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[Abbr `init`, allocas_from_def] >>
     rpt gen_tac >> Cases_on `aid = header_st.cs_next_id` >> gvs[] >> metis_tac[]) >>
  `init.vs_fmp = s.vs_fmp` by
    (qpat_assum `entry_decoder_obs s t` (assume_tac o MATCH_MP entry_decoder_obs_fmp) >>
     asm_simp_tac bool_ss [Abbr `init`, venom_state_accfupds, combinTheory.K_THM]) >>
  `alloca_inv init` by
    (irule calldata_alloca_inv_fields >> qexists_tac `t` >> simp[Abbr `init`]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp init` by
    (qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK init,H,u)`
       (qspecl_then [`ARB`,`{}`] mp_tac) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`fn_inst_ids_distinct fn`,`init.vs_fmp = s.vs_fmp`,`alloca_inv init`,
        `ctx_has_dalloca ctx ==> allocas_below_fmp s /\ _`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[decoder_origin_path_room]) >>
  qabbrev_tac `h = jump_to hdr init` >>
  `!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,fn,PG)
    (s,G,tn) [] (OK h,H,u)` by
    (rpt gen_tac >>
     qpat_assum `!D explicit. gas_origin_ptr_path _ (s,G,tn) [] (OK init,H,u)`
       (qspecl_then [`D`,`explicit`] (mp_then Any mp_tac fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >>
     disch_then (qspecl_then [`init`,`H`,`u`,`[]`,`OK h`,`H`,`u`] mp_tac) >>
     simp[NoAsms] >> disch_then irule >>
     qpat_assum `Abbrev (h = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule decoderNavigationPtrTheory.jump_origin_ptr_path >>
     rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
      (qexistsl_tac [`bb`,`loop_st.cs_next_id`] >> rpt conj_tac >> first_assum ACCEPT_TAC) ORELSE
      (strip_tac >> first_x_assum CONTR_TAC))) >>
  qabbrev_tac `bc = <|bb_label := s.vs_current_bb;
    bb_instructions := loop_st.cs_current_insts|>` >>
  qabbrev_tac `clip = fn with fn_blocks := [bc]` >>
  `lookup_block s.vs_current_bb clip.fn_blocks = SOME bc /\
   DROP s.vs_inst_idx bc.bb_instructions = emitted_insts st loop_st /\
   fn_has_code st loop_st clip` by
    simp[Abbr `clip`, Abbr `bc`, fn_has_code_def, emitted_blocks_def,
      lookup_block_def, FIND_thm, emitted_insts_def] >>
  `pending_alloca_size clip s <= pending_alloca_size fn s` by
    (qpat_assum `Abbrev (clip = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     irule array_init_pending_credit >>
     qexists_tac `bb` >>
     qpat_assum `lookup_block loop_st.cs_current_bb fn.fn_blocks = SOME bb`
       (assume_tac o MATCH_MP venomExecProofsTheory.lookup_block_MEM) >>
     simp[Abbr `bc`]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size clip s <= w2n s.vs_initial_fmp)` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`ctx_has_dalloca ctx ==> allocas_below_fmp s /\ _`,
        `pending_alloca_size clip s <= pending_alloca_size fn s`] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     Cases_on `ctx_has_dalloca ctx` >> simp[] >> decide_tac) >>
  `gas_path_ptr ARB lower ctx clip PG G tn s 0 H u (OK init)` by
    (`gas_origin_ptr_path (ARB,lower,{},ctx,clip,PG) (s,G,tn) [] (OK init,H,u)`
       by simp[Abbr `init`] >>
     drule gas_origin_ptr_path_projections >> simp[]) >>
  `!x. not_fresh_at st x ==> FLOOKUP u.t_var x = FLOOKUP tn.t_var x` by
    (rpt strip_tac >> drule_all array_init_old_outputs >> strip_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
         ~MEM x i.inst_outputs) (emitted_insts st loop_st)` by
       metis_tac[EVERY_CONJ] >>
     drule_all_then ACCEPT_TAC gas_path_ptr_suffix_taint_frame) >>
  `~h.vs_halted` by simp[Abbr `h`, jump_to_def] >>
  `!fuel r. run_from fuel ctx fn h = r /\ (!err. r <> Error err) ==>
      ?fuel'. run_from fuel' ctx fn s = r /\
        (mem_safe_run fuel ctx fn h ==> mem_safe_run fuel' ctx fn s)` by
    (`gas_origin_ptr_path (ARB,lower,{},ctx,fn,PG) (s,G,tn) [] (OK h,H,u)` by simp[] >>
     drule selected_zero_path_mem >>
     disch_then (mp_then Any mp_tac fragGasPathMemTheory.gas_path_mem_exec) >>
     qpat_assum `~h.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[exit_result_def]) >>
  `!i. d <= i /\ i < d+32 ==> i NOTIN u.t_mem` by
    (qpat_assum `u.t_mem = _` (fn th => simp[NoAsms, th])) >>
  `op_taint u src = {} /\ op_prov H src = NONE` by
    (Cases_on `src` >> simp[op_taint_def, op_prov_def] >>
     first_assum (ACCEPT_TAC o SRULE [op_prov_def])) >>
  `h.vs_memory = t.vs_memory /\ h.vs_allocas = t.vs_allocas /\
   h.vs_alloca_next = t.vs_alloca_next /\ h.vs_call_ctx = t.vs_call_ctx /\
   h.vs_data_section = t.vs_data_section` by
    simp[NoAsms, Abbr `h`, Abbr `init`, jump_to_def] >>
  `!op. eval_operand op h = eval_operand op t` by
    (Cases >> simp[NoAsms, Abbr `h`, Abbr `init`, jump_to_def,
      eval_operand_def, lookup_var_def]) >>
  `!x sz. ptr_covers H u x h sz <=> ptr_covers H u x
       (t with vs_inst_idx := LENGTH (emitted_insts st loop_st) + s.vs_inst_idx) sz` by
    simp[NoAsms, Abbr `h`, Abbr `init`, jump_to_def, ptr_covers_def, lookup_var_def] >>
  `!id p k. st.cs_next_id <= id /\ id < last.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
      ?i. MEM i (fn_insts fn) /\ i.inst_id = id /\
        i.inst_opcode = ALLOCA /\ i.inst_operands = [Lit 32w]` by
    (rpt gen_tac >> Cases_on `id = header_st.cs_next_id`
     >- (qpat_x_assum `id = header_st.cs_next_id` SUBST_ALL_TAC >>
         strip_tac >>
         `p = b /\ k = 32` by
           (qpat_assum `FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (b,32)` mp_tac >>
            qpat_assum `FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (p,k)` mp_tac >>
            POP_ASSUM_LIST (K ALL_TAC) >> simp[]) >>
         `b < dimword (:256)` by
           (irule arithmeticTheory.LESS_EQ_LESS_TRANS >>
            qexists_tac `b+32` >> simp[NoAsms] >> first_assum ACCEPT_TAC) >>
         rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE
          (qexists_tac `inst` >> rpt conj_tac >> first_assum ACCEPT_TAC) ORELSE
          asm_rewrite_tac[])) >>
     strip_tac >>
     `FLOOKUP s.vs_allocas id = SOME (p,k)` by
       (qpat_assum `!id. id <> header_st.cs_next_id ==> _`
          (qspec_then `id` mp_tac) >>
        qpat_assum `id <> header_st.cs_next_id` mp_tac >>
        qpat_assum `FLOOKUP t.vs_allocas id = SOME (p,k)` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
     qpat_assum `!id p k. st.cs_next_id <= id /\ id < last.cs_next_id /\
                   FLOOKUP s.vs_allocas id = SOME (p,k) ==> _`
       (qspecl_then [`id`,`p`,`k`] mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_assum `p+32 <= s.vs_alloca_next` mp_tac >>
     qpat_assum `s.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[LESS_EQ_TRANS]) >>
  `h.vs_current_bb = hdr /\ h.vs_inst_idx = 0 /\
   lookup_var q h = lookup_var q t /\ mload b h = mload b t /\
   (fresh_vars_wrt limit h <=> fresh_vars_wrt limit t) /\
   (entry_decoder_obs s h <=> entry_decoder_obs s t) /\
   (allocas_from lower h <=> allocas_from lower init) /\
   (abi_decode_footprint_frame [(d,32);(b,32)] s h <=>
    abi_decode_footprint_frame [(d,32);(b,32)] s t)` by
    simp[NoAsms, Abbr `h`, Abbr `init`, jump_to_def, lookup_var_def,
      mload_def, fresh_vars_wrt_def, entry_decoder_obs_def, allocas_from_def,
      abi_decode_footprint_frame_def] >>
  `lookup_var q t = SOME (n2w b)` by
    (qpat_assum `ip = Var q` (fn eq =>
      qpat_assum `eval_operand ip t = SOME (n2w b)`
        (ACCEPT_TAC o SRULE [eq, eval_operand_def]))) >>
  `alloca_inv h /\ alloca_frontier_inv ctx fn site h` by
    (conj_tac
     >- (irule calldata_alloca_inv_fields >> qexists_tac `t` >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule calldata_alloca_frontier_inv_fields >> qexists_tac `t` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `abi_decode_load CALLDATALOAD a h = n2w n` by
    (qpat_assum `abi_decode_load CALLDATALOAD a s = _` mp_tac >>
     qpat_assum `entry_decoder_obs s h <=> entry_decoder_obs s t` mp_tac >>
     qpat_assum `entry_decoder_obs s t` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[entry_decoder_obs_def, abi_decode_load_def, abi_decode_source_def]) >>
  `lower <= t.vs_alloca_next` by
    (irule LESS_EQ_TRANS >> qexists_tac `s.vs_alloca_next` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `u.t_mem SUBSET tn.t_mem /\ (!i. b <= i /\ i < b+32 ==> i NOTIN u.t_mem)` by
    (qpat_assum `u.t_mem = _` (fn th => simp[NoAsms, th, SUBSET_DEF])) >>
  `!x. not_fresh_at st x ==> FLOOKUP H x = FLOOKUP G x /\
      FLOOKUP u.t_var x = FLOOKUP tn.t_var x` by
    (qpat_assum `!x. not_fresh_at st x ==> lookup_var x t = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at st x ==> FLOOKUP u.t_var x = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> mem_word_at d mem = n2w n` by
    (qpat_assum `mem_word_at d t.vs_memory = _` (SUBST1_TAC o SYM) >>
     rpt strip_tac >> irule (GSYM clean_word_mem_agree) >>
     qexists_tac `u.t_mem` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `header_st.cs_next_id = loop_st.cs_next_id-2` kall_tac >>
  qpat_x_assum `u.t_mem = _` kall_tac >>
  qexistsl [`t`,`h`,`H`,`u`,`q`,`b`] >>
  asm_rewrite_tac[] >>
  rpt conj_tac >> (simp[])
QED
