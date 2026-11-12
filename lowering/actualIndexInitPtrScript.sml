Theory actualIndexInitPtr
Ancestors actualDecoderAllocationPtr decoderIndexInitCorePtr abiDecoderIndexInit
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
  ?H u q p. ip = Var q /\ eval_operand ip t = SOME (n2w p) /\
    p + 32 < dimword (:256) /\
    (case FLOOKUP s.vs_allocas sa.cs_next_id of
       NONE => p = s.vs_alloca_next | SOME (slot,sz) => p = slot) /\
    mload p t = 0w /\
    ptr_covers H u q (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    u.t_mem = tn.t_mem DIFF {a | p <= a /\ a < p + 32} /\
    (!a. p <= a /\ a < p + 32 ==> a NOTIN u.t_mem) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ lower <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
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
  disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
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
  qexistsl_tac [`H`,`u`,`q`,`p`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
