Theory bodyFullHashShaAbort
Ancestors
  bodyFullHashShaInput bodyPtrHashBuiltinsShaAlloc instSeqPtrLo
  bodyPtrDefs loweringHalt exprLoweringProps compileEnv venomState
  ptrDiscipline words

Theorem sha_alloc_abort_ptr_at:
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
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  ?t Gf tf. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all sha_literal_alloc_input_frame_at >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `!x. x=p \/ len=Var x \/ x=q ==> not_fresh_at sn x` by metis_tac[] >>
  `eval_operand (Var q) t = SOME v` by metis_tac[] >>
  drule_all hash_alloc_sha256_abort_from_input >>
  disch_then (qspec_then `D` strip_assume_tac) >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s Gf tf` by
    (irule (Q.SPECL [`emitted_insts sa sb`, `D`, `D`, `lo`,
       `ctx`, `fn`, `PG`, `G`, `tn`, `s`, `Gf`, `tf`] inst_seq_ptr_zero_to_lo) >>
     gvs[ghost_inv_at_def, arithmeticTheory.ADD_ASSOC]) >>
  qexistsl_tac [`t'`, `Gf`, `tf`] >> simp[]
QED

