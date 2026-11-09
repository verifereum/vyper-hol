(* Source-indexed H0 at the actual executed initializer endpoint. *)
Theory calldataValidInitHeader
Ancestors
  calldataInitOwnedPost calldataInitSequence calldataInitEntry calldataValidOwnedLoop loweringStateRelDefs
  abiDecoderFrame abiDecoderTypedContract abiDecoderContract venomState
  exprLoweringProps allocaFrontierBound calldataDynOwned compileEnv fragExecMem list calldataInitializerSafety

Theorem calldata_valid_init_header:
  let Own = \s. !id q k.
    st.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (q,k) ==>
    k = 32 /\ q < dimword (:256) /\ q+32 <= s.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w];
      H = \j s scratch.
        ~s.vs_halted /\ s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 /\
        j <= LENGTH vs /\ LENGTH vs <= maxn /\
        eval_operand src s = SOME srcword /\ eval_operand dst s = SOME (n2w d) /\
        eval_operand ip s = SOME (n2w p) /\ mload p s = n2w j /\
        abi_decode_load CALLDATALOAD srcword s = n2w (LENGTH vs) /\
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
          d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s /\
        mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs
  in
  abi_decode_array_loop_init dst src CALLDATALOAD (Lit 0w) (Lit 0w) maxn abi_sz st =
    ((ip,cnt),loop_st) /\
  abi_decode_dynarray_prefix src CALLDATALOAD (Lit 0w) maxn abi_sz st = ((),guard_st) /\
  abi_decode_array_header dst src CALLDATALOAD guard_st = (cnt,header_st) /\
  abi_decode_index_init header_st = (ip,loop_st) /\
  eval_operand src initial = SOME srcword /\ eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  maxn < dimword (:256) /\ d < dimword (:256) /\
  d+(32+maxn*type_memory_size tv) <= initial.vs_alloca_next /\
  alloca_inv initial /\ alloca_frontier_inv ctx fn site initial /\
  unit_alloca_budget ctx < dimword (:256) /\
  (!i. MEM i (emitted_insts header_st loop_st) ==> MEM i (fn_insts fn)) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ((FLOOKUP initial.vs_allocas header_st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
   (FLOOKUP initial.vs_allocas header_st.cs_next_id = SOME (p,32) /\
     p < dimword (:256) /\ p+32 <= initial.vs_alloca_next)) /\
  (d+(32+maxn*type_memory_size tv) <= p \/ p+32 <= d) /\
  abi_decode_load CALLDATALOAD srcword initial = n2w (LENGTH vs) /\
  LENGTH vs <= maxn /\ LENGTH vs < dimword (:256) /\
  st.cs_next_id <= header_st.cs_next_id /\ header_st.cs_next_id < end_st.cs_next_id /\
  Own initial /\ FLOOKUP initial.vs_allocas oid = SOME (base_addr,cap) /\
  fresh_vars_wrt limit_st initial /\ loop_st.cs_next_var <= limit_st.cs_next_var /\
  abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs)
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  mem_bytes_at sb (LENGTH bs) (abi_decode_source CALLDATALOAD initial) = bs /\
  loop_st.cs_blocks = st.cs_blocks /\ loop_st.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts loop_st.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    i.inst_opcode <> DLOAD /\ i.inst_opcode <> DLOADBYTES) (emitted_insts st loop_st) /\
  abi_decode_loop_prefix ip src CALLDATALOAD (Lit 0w) loop_st = ((hdr,body_lbl,exit_lbl),prefix_st) /\
  fn_has_code st loop_st fn /\ fn_has_code loop_st prefix_st fn /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. run_inst_seq (emitted_insts st loop_st) initial = OK t /\
    run_inst_seq_mem_ok (emitted_insts st loop_st) initial /\
    ((!fuel. mem_safe_run fuel ctx fn (jump_to hdr t)) ==>
      !fuel. mem_safe_run fuel ctx fn initial) /\
    H 0 (jump_to hdr t) [(p,32)] /\
    (!fuel r. run_from fuel ctx fn (jump_to hdr t) = r /\ (!e. r <> Error e) ==>
      ?fuel'. run_from fuel' ctx fn initial = r /\
        (mem_safe_run fuel ctx fn (jump_to hdr t) ==> mem_safe_run fuel' ctx fn initial))
Proof
  qmatch_goalsub_abbrev_tac `LET _ Own` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  qmatch_goalsub_abbrev_tac `LET _ H` >>
  CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n (abi_decode_load CALLDATALOAD srcword initial) <= maxn` by simp[] >>
  `32 <= 32+maxn*type_memory_size tv` by decide_tac >>
  drule_all calldata_array_loop_init_repeat_sequence >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts st loop_st) initial` by
    (irule run_inst_seq_mem_ok_of_prefix_safe >>
     asm_rewrite_tac[] >> fs[EVERY_MEM]) >>
  drule_all calldata_executed_init_to_header >> strip_tac >>
  `(!fuel. mem_safe_run fuel ctx fn (jump_to hdr t)) ==>
    !fuel. mem_safe_run fuel ctx fn initial` by
    (ho_match_mp_tac (GEN_ALL calldata_executed_init_all_fuel_pullback) >>
     qexistsl_tac [`st`, `src`, `loop_st`, `ip`, `exit_lbl`, `prefix_st`, `body_lbl`] >>
     asm_rewrite_tac[] >> fs[EVERY_MEM]) >>
  `alloca_inv t /\ alloca_frontier_inv ctx fn site t /\
   initial.vs_alloca_next <= t.vs_alloca_next /\
   (!id q k. FLOOKUP initial.vs_allocas id = SOME (q,k) ==>
     FLOOKUP t.vs_allocas id = SOME (q,k)) /\
   (!id. id < st.cs_next_id \/ end_st.cs_next_id <= id ==>
     FLOOKUP t.vs_allocas id = FLOOKUP initial.vs_allocas id) /\ Own t` by
    suspend "ownership" >>
  `abi_decode_footprint_frame [(d,32+maxn*type_memory_size tv);(p,32)] initial t` by
    suspend "footprint" >>
  `fresh_vars_wrt limit_st t` by metis_tac[] >>
  qexists_tac `t` >> asm_rewrite_tac[] >> suspend "header"
QED
Resume calldata_valid_init_header[ownership]:
  mp_tac (Q.INST [`lo` |-> `st.cs_next_id`, `hi` |-> `end_st.cs_next_id`]
    (SPEC_ALL calldata_index_init_executed_ownership)) >>
  simp_tac (pure_ss ++ boolSimps.LET_ss) [] >>
  qpat_assum `Abbrev (Own = _)`
    (fn th => pure_rewrite_tac[GSYM (BETA_RULE (SIMP_RULE pure_ss
      [markerTheory.Abbrev_def, FUN_EQ_THM] th))]) >> BETA_TAC >>
  disch_then irule >> asm_rewrite_tac[]
QED
Resume calldata_valid_init_header[footprint]:
  simp[abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
  rpt strip_tac >> first_x_assum irule >>
  conj_tac >- (first_x_assum (qspecl_then [`d`,`32+maxn*type_memory_size tv`] mp_tac) >> simp[] >> decide_tac) >>
  first_x_assum (qspecl_then [`p`,`32`] mp_tac) >> simp[]
QED
Resume calldata_valid_init_header[header]:
  `alloca_inv (jump_to hdr t) /\
   alloca_frontier_inv ctx fn site (jump_to hdr t)` by
    (mp_tac (Q.INST [`s` |-> `t`, `t` |-> `jump_to hdr t`]
      calldata_alloca_invariants_fields) >> simp[jump_to_def]) >>
  `Own (jump_to hdr t)` by
    (qpat_assum `Own t` mp_tac >>
     simp_tac pure_ss [Abbr `Own`] >> POP_ASSUM_LIST (K all_tac) >>
     BETA_TAC >>
     `(jump_to hdr t).vs_allocas = t.vs_allocas /\
      (jump_to hdr t).vs_alloca_next = t.vs_alloca_next` by simp[jump_to_def] >>
     asm_rewrite_tac[]) >>
  `eval_operand src t = SOME srcword /\ eval_operand dst t = SOME (n2w d)` by
    metis_tac[] >>
  `abi_decoder_ranges CALLDATALOAD (Lit 0w) (Lit 0w) src dst 0 sb (LENGTH bs) d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap t` by
    (gvs[abi_decoder_ranges_def]) >>
  simp_tac bool_ss [Abbr `H`] >>
  simp[jump_to_def, fresh_vars_wrt_def, mload_def,
       abi_decode_load_def, abi_decode_source_def,
       abi_decoder_ranges_def, abi_decode_footprint_frame_def] >>
  conj_tac
  >- (qpat_x_assum `mload p t = _` mp_tac >> simp[mload_def]) >>
  conj_tac
  >- (qpat_x_assum `abi_decode_load CALLDATALOAD srcword initial = _` mp_tac >>
      simp[abi_decode_load_def, abi_decode_source_def]) >>
  conj_tac
  >- (qexists_tac `header_st.cs_next_id` >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `abi_decoder_ranges _ (Lit 0w) _ _ _ 0 _ _ _ _ _ _ t` mp_tac >>
      simp[abi_decoder_ranges_def]) >>
  qpat_x_assum `mem_bytes_at sb _ (abi_decode_source _ initial) = bs` mp_tac >>
  simp[abi_decode_source_def]
QED
Finalise calldata_valid_init_header
