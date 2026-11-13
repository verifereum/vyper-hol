Theory calldataValidHeaderLocalFrontier
Ancestors
  calldataValidInitLocalFrontier calldataValidArrayInputs actualScratchSelection
  abiDecoderArrayInit abiDecoderArrayLoopInit abiDecoderIndexInit calldataDynInit
  abiDecoderContract abiDecoderTypedContract abiDecoderValidContract abiDecodeRanges fragExec exprLoweringProps emitHelperProps
  venomInst venomExecSemantics compileEnv list rich_list arithmetic fragExecMem

Theorem header_index_insts_in_function[local]:
  fn_has_code st loop_st fn /\ inst_extends header_st loop_st ==>
  !i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)
Proof
  simp_tac bool_ss [fn_has_code_def, inst_extends_def, emitted_insts_def] >>
  strip_tac >> rpt strip_tac >>
  `MEM i loop_st.cs_current_insts` by
    (qpat_x_assum `loop_st.cs_current_insts = _` (fn th => once_rewrite_tac[th]) >>
     simp[MEM_APPEND]) >>
  `MEM i bb.bb_instructions` by metis_tac[IS_PREFIX_APPEND, MEM_APPEND] >>
  metis_tac[lookup_block_fn_insts]
QED

Theorem position_prefix_unbounded_zero_base[local]:
  abi_decode_dynarray_position_prefix src opc (Lit 0w) (Lit 0w) maxn asz st = (addr,st') <=>
  addr = src /\ abi_decode_dynarray_prefix src opc (Lit 0w) maxn asz st = ((),st')
Proof
  simp[abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_position_prefix_unbounded,
       abiDecoderDynarrayPrefixTheory.abi_decode_dynarray_prefix_def,
       abiDecoderDynarrayBoundTheory.abi_decode_dynarray_end_guard_def,
       abiEncoderTheory.compile_abi_dec_addr_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> eq_tac >> strip_tac >> gvs[]
QED

Theorem calldata_array_init_compile_inputs[local]:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\ fn_has_code st loop_st fn /\
  loop_st.cs_next_id <= end_st.cs_next_id ==>
  ?guard_st header_st.
    abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
    abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\
    st.cs_next_id <= header_st.cs_next_id /\ header_st.cs_next_id < end_st.cs_next_id /\
    (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
    loop_st.cs_blocks = st.cs_blocks /\ loop_st.cs_current_bb = st.cs_current_bb /\
    isPREFIX st.cs_current_insts loop_st.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) (emitted_insts st loop_st)
Proof
  strip_tac >> drule abi_decode_array_loop_init_trace >>
  simp_tac std_ss [] >> strip_tac >>
  qpat_x_assum `abi_decode_dynarray_position_prefix _ _ _ _ _ _ _ = _`
    (strip_assume_tac o REWRITE_RULE [position_prefix_unbounded_zero_base]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_loop_init_shape >> strip_tac >>
  drule_all abi_decode_dynarray_prefix_shape >> strip_tac >>
  drule_all abi_decode_array_header_shape >> strip_tac >>
  drule abi_decode_index_init_shape >> strip_tac >>
  drule_all calldata_dynarray_prefix_opcodes >> strip_tac >>
  drule calldata_array_header_opcodes >> strip_tac >>
  drule abi_decode_index_init_opcodes >> strip_tac >>
  `inst_extends st header_st` by metis_tac[inst_extends_trans] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) (emitted_insts st header_st)` by
    (irule abi_decoder_emitted_every_append >> qexists_tac `guard_st` >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) (emitted_insts st loop_st)` by
    (irule abi_decoder_emitted_every_append >> qexists_tac `header_st` >> simp[]) >>
  `!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)` by
    (match_mp_tac header_index_insts_in_function >> simp[]) >>
  qexistsl_tac [`guard_st`, `header_st`] >> asm_rewrite_tac[] >> decide_tac
QED

Theorem calldata_valid_header_producer_local_frontier:
  let Own = \s. !id q k.
    st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w];
      H = \header_st p j s scratch.
        ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
        j <= LENGTH vs /\ LENGTH vs <= maxn /\
        eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
        eval_operand ip s = SOME (n2w p) /\ mload p s = n2w j /\
        abi_decode_load CALLDATALOAD (n2w sb : bytes32) s = n2w (LENGTH vs) /\
        mem_word_at d s.vs_memory = n2w (LENGTH vs) /\
        s.vs_call_ctx = initial.vs_call_ctx /\ s.vs_data_section = initial.vs_data_section /\
        FLOOKUP s.vs_allocas header_st.cs_next_id = SOME (p,32) /\
        FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
        alloca_inv s /\ alloca_frontier_inv ctx fn site s /\ Own s /\
        initial.vs_alloca_next <= s.vs_alloca_next /\
        (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
          FLOOKUP s.vs_allocas id = SOME (q,k)) /\
        (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
          FLOOKUP s.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
        (!op. abi_decoder_operand_live st.cs_next_var op ==>
          eval_operand op s = eval_operand op initial) /\
        abi_decode_footprint_frame ((d,32+maxn*type_memory_size tv)::scratch) initial s /\
        MEM (p,32) scratch /\
        (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
          FLOOKUP s.vs_allocas id = SOME (q,k)) /\
        fresh_vars_wrt limit_st s /\
        abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs)
          d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b reserve_cap s /\
        mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs
  in
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = ((hdr,body_lbl,exit_lbl),prefix_st) /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st prefix_st fn /\
  loop_st.cs_next_id <= end_st.cs_next_id /\
  abi_decoder_valid_pre ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    bs (ArrayV (DynArrayV vs)) st src dst CALLDATALOAD (Lit 0w) (Lit 0w) 0 sb d b reserve_cap initial /\
  maxn < dimword (:256) /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\ initial.vs_alloca_next < dimword (:256) /\
  Own initial /\ (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  base_addr <= d /\ d+(32+maxn*type_memory_size tv) <= base_addr+cap /\
  fresh_vars_wrt limit_st initial /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?guard_st header_st p t.
    abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
    abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
    abi_decode_index_init header_st = (ip,loop_st) /\
    run_inst_seq (emitted_insts st loop_st) initial = OK t /\
    run_inst_seq_mem_ok (emitted_insts st loop_st) initial /\
    ((!fuel. mem_safe_run fuel ctx fn (jump_to hdr t)) ==>
      !fuel. mem_safe_run fuel ctx fn initial) /\
    H header_st p 0 (jump_to hdr t) [(p,32)] /\
    (!fuel r. run_from fuel ctx fn (jump_to hdr t) = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn (jump_to hdr t) ==> mem_safe_run fuel' ctx fn initial))
Proof
  qmatch_goalsub_abbrev_tac `LET _ Own` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ H` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all calldata_array_init_compile_inputs >> strip_tac >>
  drule calldata_valid_array_inputs >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  (Q.SUBGOAL_THEN `?p. ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\
          p = initial.vs_alloca_next) \/
        (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
         p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
      (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
      d+(32+maxn*type_memory_size tv) <= initial.vs_alloca_next`
    (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS)) >- suspend "slot") >>
  `eval_operand dst initial = SOME (n2w d) /\ d < dimword (:256)` by
    (fs[abi_decoder_valid_pre_def, abi_decoder_ranges_def]) >>
  qpat_assum `abi_decoder_valid_pre _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_valid_pre_def]) >>
  qpat_x_assum `mem_bytes_at (0 + _) _ _ = _`
    (assume_tac o REWRITE_RULE [arithmeticTheory.ADD_CLAUSES]) >>
  mp_tac (Q.INST [`srcword` |-> `n2w sb`]
    (INST_TYPE [alpha |-> ``:value``] calldata_valid_init_header_local_frontier)) >>
  simp_tac (pure_ss ++ boolSimps.LET_ss) [] >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac[GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >> BETA_TAC >>
  qpat_assum `Abbrev (H = _)`
    (fn th => pure_rewrite_tac[GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >>
  BETA_TAC >>
  (impl_tac >- asm_rewrite_tac[]) >>
  strip_tac >> qexistsl_tac [`guard_st`,`header_st`,`p`,`t`] >>
  asm_rewrite_tac[]
QED
Resume calldata_valid_header_producer_local_frontier[slot]:
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`,
    `s` |-> `initial:venom_state`, `iid` |-> `header_st.cs_next_id`,
    `sz` |-> `32+maxn*type_memory_size tv`] actual_owned_scratch_selection) >>
  simp_tac (pure_ss ++ boolSimps.LET_ss) [] >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac[GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >> BETA_TAC >>
  disch_then irule >> asm_rewrite_tac[] >>
  qpat_x_assum `Own initial` mp_tac >>
  simp_tac pure_ss [Abbr `Own`] >> BETA_TAC >> simp_tac bool_ss []
QED
Finalise calldata_valid_header_producer_local_frontier
