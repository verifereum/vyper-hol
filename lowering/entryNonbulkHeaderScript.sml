(* Frame the source-valid initializer's actual execution witness. *)
Theory entryNonbulkHeader
Ancestors
  calldataValidHeaderLocalFrontier entryDecoderLoopEndpoint
  abiDecoderContract abiDecoderTypedContract abiDecoderArrayLoopInit
  compileEnv venomState venomExecSemantics list arithmetic

Theorem entry_valid_header_producer_local_frontier:
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
  initial.vs_inst_idx = LENGTH st.cs_current_insts /\
  fn_inst_ids_distinct fn /\ alloca_history fn initial ==>
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
        (mem_safe_run fuel ctx fn (jump_to hdr t) ==> mem_safe_run fuel' ctx fn initial)) /\
    entry_decoder_obs initial (jump_to hdr t) /\ alloca_history fn (jump_to hdr t)
Proof
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (BETA_RULE (PURE_REWRITE_RULE [LET_THM]
    calldata_valid_header_producer_local_frontier)) >> strip_tac >>
  drule_all entry_array_initializer_frame >>
  disch_then (qspec_then `hdr` strip_assume_tac) >>
  qexistsl_tac [`guard_st`,`header_st`,`p`,`t`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag entry_valid_header_producer_local_frontier)
  in if null axioms andalso null (Thm.hyp entry_valid_header_producer_local_frontier) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then () else raise Fail "entry header producer inherited admission"
  end;
