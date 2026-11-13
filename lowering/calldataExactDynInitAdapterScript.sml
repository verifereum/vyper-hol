Theory calldataExactDynInitAdapter
Ancestors
  calldataDynOwned calldataDynInit calldataDynStep fragExecMem abiDecoderExecution
  abiDecoderContract abiDecoderFrame abiDecoderIndexInit abiDecoderArrayLoopInit
  abiEncoder allocaFrontierBound allocaBudgetProps actualAllocExec
  arithmetic list words finite_map venomExecSemantics venomState venomMemDefs
  compileEnv emitHelper valueEncodingDefs valueEncodingProps

Theorem calldata_exact_owned_header_initial_from_fragment:
  abi_decode_index_init header_st = (ip,loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st =
    ((hdr,body_lbl,exit_lbl),st0) /\
  st.cs_next_id <= header_st.cs_next_id /\ header_st.cs_next_id < end_st.cs_next_id /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st st0 fn /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  32 <= bufsize /\
  alloca_frontier_inv ctx fn site initial /\ alloca_inv initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  ALL_DISTINCT (MAP (\ins. ins.inst_id) (fn_insts fn)) /\
  (!ins. MEM ins (emitted_insts header_st loop_st) ==> MEM ins (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  (oid < st.cs_next_id \/ end_st.cs_next_id <= oid) /\
  (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= initial.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  frag_exec_mem ctx st loop_st (\s. s=initial)
    (\t. eval_operand ip t = SOME (n2w p) /\ mload p t = 0w /\
      w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn /\
      mem_word_at d t.vs_memory = abi_decode_load CALLDATALOAD srcword initial /\
      eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD srcword initial) /\
      t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
      (!a n. (a+n <= d \/ d+32 <= a) /\ (a+n <= p \/ p+32 <= a) ==>
        mem_bytes_at a n t.vs_memory = mem_bytes_at a n initial.vs_memory) /\
      (!id. id <> header_st.cs_next_id ==>
        FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
      FLOOKUP t.vs_allocas header_st.cs_next_id = SOME (p,32) /\
      (if FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE then
        t.vs_alloca_next = initial.vs_alloca_next+32
       else t.vs_alloca_next = initial.vs_alloca_next) /\
      (!op. abi_decoder_operand_live st.cs_next_var op ==>
        eval_operand op t = eval_operand op initial)) (K F) ==>
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
  qmatch_asmsub_abbrev_tac `frag_exec_mem ctx st loop_st _ InitPost _` >>
  drule calldata_init_to_header_safe >> disch_then drule >>
  disch_then (qspec_then `fn` mp_tac) >>
  disch_then (qspec_then `initial` mp_tac) >>
  asm_rewrite_tac[] >> simp_tac bool_ss [combinTheory.K_THM] >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  qexists_tac `jump_to hdr t` >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `InitPost t` mp_tac >>
  simp_tac bool_ss [Abbr `InitPost`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all calldata_index_init_owned_fields >> strip_tac >>
  `p < dimword (:256) /\ p+32 <= t.vs_alloca_next` by
    (qpat_assum `FLOOKUP t.vs_allocas _ = SOME (p,32)` mp_tac >>
     qpat_assum `alloca_inv t` mp_tac >>
     qpat_assum `alloca_frontier_inv ctx fn site t` mp_tac >>
     qpat_assum `unit_alloca_budget ctx < _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def, alloca_frontier_inv_def] >>
     rpt strip_tac >> `p+32 <= t.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  `!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP t.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]` by suspend "ownership" >>
  `abi_decode_footprint_frame [(d,bufsize);(p,32)] initial t` by suspend "footprint" >>
  `!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
     FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id` by
    (rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `FLOOKUP t.vs_allocas oid = SOME (base_addr,cap)` by metis_tac[] >>
  `alloca_inv (jump_to hdr t) /\ alloca_frontier_inv ctx fn site (jump_to hdr t)` by
    (qpat_assum `alloca_inv t` mp_tac >>
     qpat_assum `alloca_frontier_inv ctx fn site t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     mp_tac (Q.INST [`s` |-> `t`, `t` |-> `jump_to hdr t`]
       calldata_alloca_invariants_fields) >> simp[jump_to_def]) >>
  qpat_x_assum `frag_exec_mem _ _ _ _ _ _` kall_tac >>
  `mload p (jump_to hdr t) = 0w` by
    (qpat_assum `mload p t = 0w` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[mload_def,jump_to_def]) >>
  `eval_operand src t = SOME srcword /\ eval_operand dst t = SOME (n2w d)` by
    metis_tac[] >>
  asm_rewrite_tac [abiDecoderLoopRegistersTheory.abi_decoder_operand_jump] >>
  pure_rewrite_tac [jump_to_def,
    venomStateTheory.venom_state_accfupds, combinTheory.K_THM] >>
  asm_rewrite_tac [] >>
  qexists_tac `[(p,32)]` >>
  conj_tac >-
    (qpat_assum `abi_decode_footprint_frame _ initial t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[abi_decode_footprint_frame_def]) >>
  simp_tac std_ss [listTheory.MEM, pairTheory.PAIR_EQ] >>
  qexists_tac `header_st.cs_next_id` >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume calldata_exact_owned_header_initial_from_fragment[ownership]:
  drule_all calldata_index_init_literal_site >> strip_tac >>
  ho_match_mp_tac (GEN_ALL (SIMP_RULE (pure_ss ++ boolSimps.BOOL_ss)
    [LET_THM] calldata_owned_counter_update)) >>
  qexistsl_tac [`initial`,`p`,`ins`,`header_st.cs_next_id`] >>
  asm_rewrite_tac[]
QED

Resume calldata_exact_owned_header_initial_from_fragment[footprint]:
  qpat_assum `!a n. _ ==> mem_bytes_at a n t.vs_memory = _` mp_tac >>
  qpat_assum `t.vs_call_ctx = _` mp_tac >>
  qpat_assum `t.vs_data_section = _` mp_tac >>
  qpat_assum `32 <= bufsize` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  rpt strip_tac >>
  qpat_assum `!d' sz. _` (qspecl_then [`d`,`bufsize`]
    (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_assum `!d' sz. _` (qspecl_then [`p`,`32`]
    (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  first_x_assum irule >> decide_tac
QED
Finalise calldata_exact_owned_header_initial_from_fragment


Theorem calldata_exact_owned_header_exit:
  lookup_block hdr fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|> /\
  lookup_block exit_lbl fn.fn_blocks = SOME exit_bb /\
  phi_prefix_length exit_bb.bb_instructions = 0 /\
  end_st.cs_current_bb = exit_lbl /\ end_st.cs_current_insts = [] /\
  hiv <> hcv /\ src <> Var hiv /\
  (!op. abi_decoder_operand_live st.cs_next_var op ==>
    op <> Var hiv /\ op <> Var hcv /\ op <> Var hcmp /\ op <> Var hdone) /\
  p < dimword (:256) /\ n < dimword (:256) /\
  ~u.vs_halted /\ u.vs_current_bb = hdr /\ u.vs_inst_idx = 0 /\ n <= maxn /\
  eval_operand src u = SOME srcword /\ eval_operand ip u = SOME (n2w p) /\
  abi_decode_load CALLDATALOAD srcword u = n2w n /\
  mload p u = n2w n /\ mem_word_at d u.vs_memory = n2w n /\
  u.vs_call_ctx = initial.vs_call_ctx /\ u.vs_data_section = initial.vs_data_section /\
  FLOOKUP u.vs_allocas counter_id = SOME (p,32) /\
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
  abi_decode_footprint_frame ((d,bufsize)::scratch) initial u /\
  (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP u.vs_allocas id = SOME (q,k)) /\
  LENGTH vs = n /\ EVERY (val_wf tv) vs /\
  (!k. k < n ==> val_in_memory tv (EL k vs)
    (d+32+k*type_memory_size tv) u.vs_memory) ==>
  ?t.
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    val_wf (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) /\
    val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory /\
    (!fuel r. run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn u = r /\
        (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn u)) /\
    t.vs_call_ctx = initial.vs_call_ctx /\ t.vs_data_section = initial.vs_data_section /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
    (!id q k. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k) ==>
      k = 32 /\ q < dimword (:256) /\ q+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    initial.vs_alloca_next <= t.vs_alloca_next /\
    (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
      FLOOKUP t.vs_allocas id = SOME (q,k)) /\
    (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op initial) /\
    abi_decode_footprint_frame ((d,bufsize)::scratch) initial t /\
    (!q k. MEM (q,k) scratch ==> ?id. st.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (q,k))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p+32 <= u.vs_alloca_next` by
    (qpat_assum `alloca_inv u` mp_tac >>
     qpat_assum `FLOOKUP u.vs_allocas _ = SOME (p,32)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `mload (w2n (n2w p:bytes32)) u = n2w n` by simp[] >>
  `w2n (n2w p:bytes32)+32 <= u.vs_alloca_next` by
    (qpat_assum `p < dimword (:256)` mp_tac >>
     qpat_assum `p+32 <= u.vs_alloca_next` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  qabbrev_tac `v = jump_to exit_lbl
    (abi_decode_header_state hiv hcv hcmp hdone n n u)` >>
  `v = jump_to exit_lbl (abi_decode_header_state hiv hcv hcmp hdone n n u)` by
    simp[Abbr `v`] >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME
    <|bb_label := hdr; bb_instructions :=
      abi_decode_header_insts hid ip src CALLDATALOAD hiv hcv hcmp hdone body_lbl exit_lbl|>`
    by simp[] >>
  drule_all calldata_terminal_header_array >>
  disch_then (qspecl_then [`site`,`ctx`] strip_assume_tac) >>
  qexists_tac `v` >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op v = eval_operand op initial` by
    (qpat_assum `!op. _ ==> eval_operand op v = eval_operand op u` mp_tac >>
     qpat_assum `!op. abi_decoder_operand_live _ op ==> eval_operand op u = _` mp_tac >>
     qpat_assum `!op. _ ==> op <> Var hiv /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `~v.vs_halted /\ v.vs_current_bb = exit_lbl /\ v.vs_inst_idx = 0` by
    (qpat_assum `Abbrev (v = _)` mp_tac >>
     qpat_assum `~u.vs_halted` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[markerTheory.Abbrev_def, jump_to_def,
       abi_decode_header_state_def, update_var_def]) >>
  `abi_decode_footprint_frame ((d,bufsize)::scratch) initial v` by
    (qpat_assum `abi_decode_footprint_frame _ initial u` mp_tac >>
     qpat_assum `v.vs_memory = _` mp_tac >>
     qpat_assum `v.vs_call_ctx = _` mp_tac >>
     qpat_assum `v.vs_data_section = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[abi_decode_footprint_frame_def]) >>
  qpat_x_assum `v = jump_to _ _` kall_tac >>
  qpat_x_assum `Abbrev (v = _)` kall_tac >>
  asm_rewrite_tac[listTheory.LENGTH]
QED
