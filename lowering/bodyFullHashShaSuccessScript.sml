(* The allocated SHA call carries a complete bounded success frame. *)
Theory bodyFullHashShaSuccess
Ancestors
  bodyFullHashShaInput bodyFullHashShaEmit bodyFullUnwrapRun bodyFullHashKeccakBytes instSeqPtrLo
  bodyPtrHashBuiltinsShaAlloc bodyPtrHashBuiltinsShaAllocInput bodyPtrHashBuiltinsShaEmit
  bodyPtrHashBuiltinsGhostFrame bodyPtrHashBuiltinsShaEndpoint
  bodyPtrDefs loweringHalt emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  fragExec exprSimHash venomState ptrDiscipline finite_map pred_set words

Theorem sha_alloc_success_frame_at:
  compile_alloc_buffer 32 sa = (buf,sn) /\ fn_has_code sa sn fn /\
  emit_op GAS [] sn = (gas_op,sg) /\
  emit_op STATICCALL [gas_op;Lit 2w;Var p;len;buf.buf_operand;Lit 32w] sg = (success_op,sc) /\
  emit_void ASSERT [success_op] sc = ((),sh) /\
  emit_op MLOAD [buf.buf_operand] sh = (op,sb) /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
  ptr_covers G tn p s (w2n n) /\ op_taint tn len = {} /\
  (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn.t_mem) /\
  (!x. x=p \/ len=Var x ==> not_fresh_at sa x) /\
  (w2n n = 0 \/
   (?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
      aid < sa.cs_next_id /\ b <= w2n w /\ w2n w+w2n n <= b+k) \/
   (?name b k. local_region cenv es.scopes s name b k /\
      b <= w2n w /\ w2n w+w2n n <= b+k)) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  mem_bytes_at (w2n w) (w2n n) s.vs_memory = bs /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
  ?t Gf tf. run_inst_seq (emitted_insts sa sb) s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    ghost_inv_at D lo d cenv cx (es with outcomes := SOME rest) Gf tf
      (t with vs_inst_idx := s.vs_inst_idx+5) /\
    ghost_kept_at lo cenv es sa G tn s Gf tf /\ op_taint tf op = {} /\
    op_prov Gf op = NONE
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all sha_literal_alloc_input_frame_at >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `!x. x=p \/ len=Var x \/ x=q ==> not_fresh_at sn x` by metis_tac[] >>
  `eval_operand (Var q) t = SOME v` by metis_tac[] >>
  drule_all hash_alloc_buffer_cursor_frame >> strip_tac >>
  `mem_bytes_at (w2n w) (w2n n) t.vs_memory = bs` by metis_tac[] >>
  drule_all hash_alloc_sha256_success_from_input >>
  disch_then (qspec_then `D` strip_assume_tac) >>
  `local_ptrs_reserved cenv sn` by
    (qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     qpat_assum `!y. not_fresh_at sa y ==> not_fresh_at sn y` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sn x` by metis_tac[] >>
  `!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sn x` by metis_tac[] >>
  `!name b k. local_region cenv es.scopes t name b k ==>
     b+k <= w2n v \/ w2n v+32 <= b` by
    (qpat_assum `!name b k. local_region cenv es.scopes t name b k ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[regions_disjoint_def] >> metis_tac[]) >>
  `emit_op STATICCALL [gas_op;Lit 2w;Var p;len;Var q;Lit 32w] sg = (success_op,sc) /\
   emit_op MLOAD [Var q] sh = (op,sb)` by metis_tac[] >>
  `t.vs_outcomes = outcome::rest` by metis_tac[] >>
  drule_all sha_emit_tail_frame_at >> strip_tac >>
  `ghost_kept_at lo cenv es sa G tn s Gf tf` by
    (irule ghost_kept_at_clean_suffix >>
     qexistsl_tac [`G1`, `tn1`] >> conj_tac
     >- (qpat_assum `ghost_kept_at lo cenv es sn G1 tn1 t Gf tf` mp_tac >>
         qpat_assum `!y. not_fresh_at sa y ==> not_fresh_at sn y` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[ghost_kept_at_def] >> metis_tac[]) >>
     qpat_assum `tf = _` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `ghost_inv_at D lo d cenv cx (es with outcomes := SOME rest) Gf tf _`
    (assume_tac o PURE_REWRITE_RULE [bytes_ghost_cursor]) >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf` by
    (irule (Q.SPECL [`emitted_insts sa sb`, `D`, `D`, `lo`,
       `ctx`, `fn`, `PG`, `G`, `tn`, `s`, `Gf`, `tf`] inst_seq_ptr_zero_to_lo) >>
     gvs[ghost_inv_at_def, arithmeticTheory.ADD_ASSOC]) >>
  qexistsl_tac [`t'`, `Gf`, `tf`] >> simp[bytes_ghost_cursor]
QED
