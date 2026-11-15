Theory actualIndexInitPtr
Ancestors actualDecoderAllocationPtr decoderIndexInitCorePtr abiDecoderIndexInit
  actualAllocExec allocationPtr loweringHalt loweringStateRelDefs allocaFootprint
  entryDecoderHistoryFrame fragGasSeqPtr calldataDynInit ghostPcTransportPtr
  abiDecoderAllocation abiDecoderContract emitHelperProps exprLowering
  venomState venomExecSemantics venomMemDefs venomInst compileEnv fragExec bodyPtrDefs
  finite_map words arithmetic list rich_list context exprLoweringProps instIdxIndep

Theorem actual_index_init_endpoint_ptr_core:
  abi_decode_index_init sa = (ip,sb) /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\
      s.vs_alloca_next + 32 < dimword (:256)) \/
   (?p. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,32) /\
      p + 32 <= s.vs_alloca_next /\ s.vs_alloca_next < dimword (:256))) ==>
  ?HG u q p. ip = Var q /\ eval_operand ip t = SOME (n2w p) /\
    p + 32 < dimword (:256) /\
    (case FLOOKUP s.vs_allocas sa.cs_next_id of
       NONE => p = s.vs_alloca_next | SOME (slot,sz) => p = slot) /\
    mload p t = 0w /\
    ptr_covers HG u q (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) 32 /\
    frag_exec_ptr H cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = HG /\ z = u /\ v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    u.t_mem = tn.t_mem DIFF {a | p <= a /\ a < p + 32} /\
    (!a. p <= a /\ a < p + 32 ==> a NOTIN u.t_mem) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP HG x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ lower <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG HG u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  `?b cap. abi_decoder_budget sa.cs_next_id (sa.cs_next_id+1) b cap s` by
    (irule actual_slot_singleton_budget >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_id IN abi_decoder_ids sa.cs_next_id (sa.cs_next_id+1)` by
    simp[abi_decoder_ids_def] >>
  drule_all abi_decode_index_init_endpoint_exact_ptr_core >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  `p + 32 < dimword (:256)` by
    (drule abi_decoder_budget_word_bound >> decide_tac) >>
  `case FLOOKUP s.vs_allocas sa.cs_next_id of
     NONE => p = s.vs_alloca_next | SOME (slot,sz) => p = slot` by
    (map_every (fn pat => qpat_assum pat mp_tac)
      [`abi_decode_index_init sa = (ip,sb)`,
       `run_inst_seq (emitted_insts sa sb) s = OK t`,
       `ip = Var q`, `eval_operand ip t = SOME (n2w p)`,
       `p+32 < dimword (:256)`,
       `FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ _ \/ _`] >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     drule abi_decode_index_init_trace >> strip_tac >>
     `emit_op ALLOCA [Lit 32w] sa = (ip,allocation_st)` by
       (Cases_on `emit_op ALLOCA [Lit 32w] sa` >>
        gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def]) >>
     drule emitted_insts_emit_op >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
     asm_rewrite_tac [emitted_insts_def] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC] >>
     simp[DROP_LENGTH_APPEND, run_inst_seq_def] >>
     simp[Once step_inst_base_def, mk_inst_def, exec_alloca_def,
       eval_operand_def, bind_outputs_def] >>
     gvs[] >>
     qpat_x_assum `Var _ = buf.buf_operand` (SUBST_ALL_TAC o SYM) >>
     simp[Once step_inst_base_def, exec_write2_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     strip_tac >> gvs[eval_operand_def, lookup_var_def, mstore_def,
       write_memory_with_expansion_def, update_var_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`HG`,`u`,`q`,`p`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem actual_index_init_success_joint:
  abi_decode_index_init sa = (Var index,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel H0 ctx func cenv cx es s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?HG u p.
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),HG,u)) /\
    eval_operand (Var index) t = SOME (n2w p) /\ p+32 < dimword (:256) /\
    mload p t = 0w /\ ptr_covers HG u index t 32 /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    u.t_mem = tn.t_mem DIFF {a | p <= a /\ a < p+32} /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP HG x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule abi_decode_index_init_trace >> strip_tac >>
  `cs_extends sa allocation_st /\ cs_extends allocation_st sb` by
    (conj_tac >- metis_tac[compile_alloc_buffer_extends] >>
     drule emit_void_extends >> simp[same_blocks_def] >> strip_tac >>
     irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule actual_alloc_buffer_site >> goal_assum (drule_at Any) >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `s.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> fs[stmt_state_rel_def] >> metis_tac[]) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `?b cap. abi_decoder_budget sa.cs_next_id (sa.cs_next_id+1) b cap s` by
    (irule actual_slot_singleton_budget >>
     Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
     >- (disj1_tac >> simp[] >>
         drule_all stmt_state_rel_alloca_fresh_bound >> simp[]) >>
     rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME site` >>
     PairCases_on `site` >>
     `site1 = 32` by
       (drule_all stmt_state_rel_alloca_site_bound >> simp[]) >>
     disj2_tac >> qexists_tac `site0` >> simp[] >>
     fs[alloca_inv_def, alloca_next_valid_def] >> metis_tac[]) >>
  `sa.cs_next_id IN abi_decoder_ids sa.cs_next_id (sa.cs_next_id+1)` by
    simp[abi_decoder_ids_def] >>
  drule_all abi_decode_index_init_endpoint_sequence_ptr_core >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  `q = index` by fs[] >>
  qpat_x_assum `q = index` SUBST_ALL_TAC >>
  `p+32 < dimword (:256)` by
    (drule abi_decoder_budget_word_bound >> decide_tac) >>
  `ptr_covers HG u index t 32` by
    metis_tac[ptr_covers_inst_idx] >>
  drule abi_decode_index_init_shape >> strip_tac >>
  `isPREFIX sa.cs_current_insts sb.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND] >>
  drule_all entry_straight_line_code_slice >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `s.vs_inst_idx+LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    fs[inst_extends_def, IS_PREFIX_APPEND, emitted_insts_def, DROP_LENGTH_APPEND] >>
  drule abi_decode_index_init_opcodes >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (drule calldata_index_init_instructions >> simp[mk_inst_def]) >>
  qexistsl_tac [`HG`,`u`,`p`] >> asm_rewrite_tac[] >>
  rpt gen_tac >>
  mp_tac (run_inst_seq_gas_origin_ptr_path |> SPEC_ALL |> Q.INST
    [`code` |-> `emitted_insts sa sb`, `s` |-> `s`, `t` |-> `t`,
     `G` |-> `G`, `tn` |-> `tn`, `G'` |-> `HG`, `tn'` |-> `u`,
     `ctx` |-> `ctx`, `func` |-> `func`, `bb` |-> `bb`,
     `D` |-> `D`, `lo` |-> `lo`, `explicit` |-> `explicit`, `PG` |-> `PG`]) >>
  (impl_tac >- simp[]) >> simp[]
QED
