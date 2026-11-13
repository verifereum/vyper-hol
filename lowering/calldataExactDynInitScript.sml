Theory calldataExactDynInit
Ancestors
  calldataExactDynInitSequence calldataExactDynInitAdapter calldataDynOwned
  calldataDynInit abiDecoderArrayLoopInit abiEncoder abiDecoderContract
  fragExecMem arithmetic list words finite_map venomExecSemantics venomState
  compileEnv emitHelper allocaFrontierBound allocaBudgetProps
  valueEncodingDefs valueEncodingProps

Theorem calldata_exact_owned_header_initial:
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st =
    ((hdr,body_lbl,exit_lbl),st0) /\
  st.cs_next_id <= header_st.cs_next_id /\ header_st.cs_next_id < end_st.cs_next_id /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d+bufsize < dimword (:256) /\
  32 <= bufsize /\ d+bufsize <= initial.vs_alloca_next /\
  alloca_frontier_inv ctx fn site initial /\ alloca_inv initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+bufsize <= p \/ p+32 <= d) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= d /\ d+bufsize <= base_addr+cap /\
  (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  (maxn < w2n (abi_decode_load CALLDATALOAD srcword initial) /\
   ?fuel z. run_from fuel ctx fn initial = Abort Revert_abort z /\
     mem_safe_run fuel ctx fn initial) \/
  ?u.
    (~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      eval_operand src u = SOME srcword /\ eval_operand dst u = SOME (n2w d) /\
      eval_operand ip u = SOME (n2w p) /\ mload p u = 0w /\
      mem_word_at d u.vs_memory = abi_decode_load CALLDATALOAD srcword initial /\
      u.vs_call_ctx = initial.vs_call_ctx /\ u.vs_data_section = initial.vs_data_section /\
      FLOOKUP u.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      FLOOKUP u.vs_allocas oid = SOME (base_addr,cap) /\
      alloca_inv u /\ alloca_frontier_inv ctx fn site u /\
      (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
        FLOOKUP u.vs_allocas id = SOME (q,k) ==>
        k = 32 /\ q < dimword (:256) /\ q+32 <= u.vs_alloca_next /\
        ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
          ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
      initial.vs_alloca_next <= u.vs_alloca_next /\
      (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
        FLOOKUP u.vs_allocas id = SOME (q,k)) /\
      (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
        FLOOKUP u.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op u = eval_operand op initial) /\
      ?scratch. abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
        !q k. MEM (q,k) scratch ==>
          ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
            FLOOKUP u.vs_allocas id = SOME (q,k)) /\
    (!fuel r. run_from fuel ctx fn u = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn u ==> mem_safe_run fuel' ctx fn initial))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `d < dimword (:256)` by decide_tac >>
  Cases_on `w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn`
  >- (disj2_tac >>
      drule_all calldata_exact_array_loop_init_accepted >>
      disch_then (assume_tac o BETA_RULE o REWRITE_RULE [lambdify calldata_exact_init_fields_def]) >>
      drule_all calldata_exact_owned_header_initial_from_fragment >>
      disch_then ACCEPT_TAC) >>
  disj1_tac >> conj_tac >- decide_tac >>
  drule_all calldata_array_loop_init_repeat_safe >> disch_tac >>
  drule calldata_init_to_header_safe >> disch_then drule >>
  disch_then (qspec_then `fn` mp_tac) >>
  disch_then (qspec_then `initial` mp_tac) >>
  asm_rewrite_tac [] >> simp_tac bool_ss [] >>
  strip_tac >> qexistsl_tac [`fuel`,`u`] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
