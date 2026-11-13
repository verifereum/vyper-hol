(* Allocation/cursor glue for the counted SHA suffix. *)
Theory bodyPtrHashBuiltinsShaAlloc
Ancestors bodyPtrHashBuiltinsShaAllocPath bodyPtrHashBuiltinsShaEmit
  ghostPcTransportPtr arithmetic arithmeticProps exprSimAlloc rich_list list
  venomExecSemantics emitHelper context compileEnv loweringStateRelDefs exprLoweringProps
  emitHelperProps venomInst venomState loweringHalt exprSimHash
  fragExec instIdxIndep fragGasPathPtr words bodyPtrHashBuiltinsShaAllocInput
  bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsGhostFrame bodyPtrDefs

Theorem hash_alloc_buffer_cursor_frame:
  compile_alloc_buffer m sa = (buf,sn) /\
  run_inst_seq (emitted_insts sa sn) s = OK t ==>
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
  t.vs_halted = s.vs_halted /\ t.vs_outcomes = s.vs_outcomes
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def,
    comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, DROP_LENGTH_APPEND,
    run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_alloca_def,
    AllCaseEqs(), update_var_def]
QED

Theorem hash_alloc_sha256_code_split:
  compile_alloc_buffer 32 sa = (buf,sn) /\
  emit_op GAS [] sn = (gas_op,sg) /\
  emit_op STATICCALL [gas_op;Lit 2w;Var p;len;buf.buf_operand;Lit 32w] sg = (success_op,sc) /\
  emit_void ASSERT [success_op] sc = ((),sh) /\
  emit_op MLOAD [buf.buf_operand] sh = (op,sb) ==>
  emitted_insts sa sb = emitted_insts sa sn ++ emitted_insts sn sb /\
  LENGTH (emitted_insts sa sn) = 1 /\ LENGTH (emitted_insts sn sb) = 4
Proof
  strip_tac >> drule_all emitted_insts_sha256_tail >> strip_tac >>
  `sn.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sn /\
   LENGTH (emitted_insts sa sn) = 1` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def] >> strip_tac >>
     gvs[emitted_insts_def, DROP_LENGTH_APPEND]) >>
  conj_tac >- (irule emitted_insts_prefix_split >> metis_tac[]) >>
  simp[]
QED

Theorem hash_code_prefix_split:
  isPREFIX (xs ++ ys) (DROP k code) ==>
  isPREFIX xs (DROP k code) /\
  isPREFIX ys (DROP (k + LENGTH xs) code)
Proof
  Cases_on `xs` >- simp[] >>
  pure_rewrite_tac[IS_PREFIX_APPEND] >> strip_tac >>
  conj_tac >- (qexists_tac `ys ++ l` >> simp[]) >>
  `k + LENGTH (h::t) <= LENGTH code` by
    (qpat_x_assum `DROP k code = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_DROP] >> decide_tac) >>
  qexists_tac `l` >>
  `DROP (LENGTH (h::t)) (DROP k code) = ys ++ l` by
    (asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  metis_tac[DROP_DROP, ADD_COMM]
QED

Theorem hash_alloc_sha256_abort_from_input:
  compile_alloc_buffer 32 sa = (buf,sn) /\
  emit_op GAS [] sn = (gas_op,sg) /\
  emit_op STATICCALL [gas_op;Lit 2w;Var p;len;buf.buf_operand;Lit 32w] sg = (success_op,sc) /\
  emit_void ASSERT [success_op] sc = ((),sh) /\
  emit_op MLOAD [buf.buf_operand] sh = (op,sb) /\
  run_inst_seq (emitted_insts sa sn) s = OK a /\
  buf.buf_operand = Var q /\
  G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [q]) a /\
  tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [q]) s a tn /\
  eval_operand (Var p) a = SOME w /\ eval_operand len a = SOME n /\
  eval_operand (Var q) a = SOME r /\
  ptr_covers G1 tn1 p a (w2n n) /\ ptr_covers G1 tn1 q a 32 /\
  op_taint tn1 len = {} /\
  (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn1.t_mem) /\
  (!x. x=p \/ len=Var x \/ x=q ==> not_fresh_at sn x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  ?t j Gf tf. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
      (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  strip_tac >>
  drule_all hash_alloc_sha256_code_split >> strip_tac >>
  drule_all hash_alloc_buffer_cursor_frame >> strip_tac >>
  `isPREFIX (emitted_insts sa sn) (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts sn sb) (DROP (SUC s.vs_inst_idx) bb.bb_instructions)` by
    (`isPREFIX (emitted_insts sa sn ++ emitted_insts sn sb)
        (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
     drule hash_code_prefix_split >> simp[ADD1]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1
    (OK (a with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_all hash_literal_alloc_counted_path >> simp[]) >>
  `?t j Gf tf. run_inst_seq (emitted_insts sn sb)
      (a with vs_inst_idx := SUC s.vs_inst_idx) = Abort Revert_abort t /\
    gas_path_ptr D 0 ctx fn PG G1 tn1
      (a with vs_inst_idx := SUC s.vs_inst_idx) 1 Gf tf
      (Abort Revert_abort (t with vs_inst_idx := j))` by
    (irule (Q.INST [`p` |-> `p`, `q` |-> `q`, `len` |-> `len`, `op` |-> `op`]
       hash_emit_sha256_tail_abort_path) >>
     simp[ptr_covers_inst_idx, hash_eval_operand_inst_idx] >>
     gvs[] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sn sb)` by
    (drule_all emitted_insts_sha256_tail >>
     simp[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `?u. run_inst_seq (emitted_insts sn sb) a = Abort Revert_abort u /\
       t = u with vs_inst_idx := SUC s.vs_inst_idx` by
    (qpat_x_assum `run_inst_seq _ (_ with vs_inst_idx := _) = _` mp_tac >>
     simp[run_inst_seq_inst_idx] >>
     Cases_on `run_inst_seq (emitted_insts sn sb) a` >>
     simp[exec_result_map_def]) >>
  qexistsl_tac [`u`, `j`, `Gf`, `tf`] >> conj_tac
  >- (drule run_inst_seq_append >> disch_then (qspec_then `emitted_insts sn sb` mp_tac) >> simp[]) >>
  drule_all gas_path_ptr_then >> simp[]
QED


Theorem hash_alloc_sha256_abort_path:
  compile_alloc_buffer 32 sa = (buf,sn) /\
  emit_op GAS [] sn = (gas_op,sg) /\
  emit_op STATICCALL [gas_op;Lit 2w;Var p;len;buf.buf_operand;Lit 32w] sg = (success_op,sc) /\
  emit_void ASSERT [success_op] sc = ((),sh) /\
  emit_op MLOAD [buf.buf_operand] sh = (op,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  ghost_inv d cenv cx es G tn s /\
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
  ?t j Gf tf. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
      (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all hash_literal_alloc_input_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `!x. x=p \/ len=Var x \/ x=q ==> not_fresh_at sn x` by metis_tac[] >>
  `eval_operand (Var q) t = SOME v` by metis_tac[] >>
  drule_all hash_alloc_sha256_abort_from_input >>
  disch_then (qspec_then `D` mp_tac) >> simp[]
QED

Theorem hash_alloc_sha256_success_from_input:
  compile_alloc_buffer 32 sa = (buf,sn) /\
  emit_op GAS [] sn = (gas_op,sg) /\
  emit_op STATICCALL [gas_op;Lit 2w;Var p;len;buf.buf_operand;Lit 32w] sg = (success_op,sc) /\
  emit_void ASSERT [success_op] sc = ((),sh) /\
  emit_op MLOAD [buf.buf_operand] sh = (op,sb) /\
  run_inst_seq (emitted_insts sa sn) s = OK a /\ buf.buf_operand = Var q /\
  G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [q]) a /\
  tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [q]) s a tn /\
  eval_operand (Var p) a = SOME w /\ eval_operand len a = SOME n /\
  eval_operand (Var q) a = SOME r /\
  ptr_covers G1 tn1 p a (w2n n) /\ ptr_covers G1 tn1 q a 32 /\
  op_taint tn1 len = {} /\
  (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn1.t_mem) /\
  (!x. x=p \/ len=Var x \/ x=q ==> not_fresh_at sn x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  mem_bytes_at (w2n w) (w2n n) a.vs_memory = bs /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
  ?t Gf tf. run_inst_seq (emitted_insts sa sb) s = OK t /\
    run_inst_seq (emitted_insts sn sb) a = OK t /\
    gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
      (OK (t with vs_inst_idx := s.vs_inst_idx+5)) /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    Gf = DRESTRICT G1 (COMPL {STRING #"%" (toString sn.cs_next_var);
      STRING #"%" (toString (sn.cs_next_var+1)); STRING #"%" (toString (sn.cs_next_var+2))}) /\
    tf = tn1 with <|t_var := tn1.t_var |+
      (STRING #"%" (toString sn.cs_next_var),{}) |+
      (STRING #"%" (toString (sn.cs_next_var+1)),{}) |+
      (STRING #"%" (toString (sn.cs_next_var+2)),{});
      t_mem := tn1.t_mem DIFF range_bytes [(w2n r,32)]|>
Proof
  strip_tac >>
  drule_all hash_alloc_sha256_code_split >> strip_tac >>
  drule_all hash_alloc_buffer_cursor_frame >> strip_tac >>
  `isPREFIX (emitted_insts sa sn) (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts sn sb) (DROP (SUC s.vs_inst_idx) bb.bb_instructions)` by
    (`isPREFIX (emitted_insts sa sn ++ emitted_insts sn sb)
        (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
     drule hash_code_prefix_split >> simp[ADD1]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1
    (OK (a with vs_inst_idx := SUC s.vs_inst_idx))` by
    (drule_all hash_literal_alloc_counted_path >> simp[]) >>
  `?t Gf tf. run_inst_seq (emitted_insts sn sb)
      (a with vs_inst_idx := SUC s.vs_inst_idx) = OK t /\
    gas_path_ptr D 0 ctx fn PG G1 tn1
      (a with vs_inst_idx := SUC s.vs_inst_idx) 1 Gf tf
      (OK (t with vs_inst_idx := (a with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx+4)) /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    Gf = DRESTRICT G1 (COMPL {STRING #"%" (toString sn.cs_next_var);
      STRING #"%" (toString (sn.cs_next_var+1)); STRING #"%" (toString (sn.cs_next_var+2))}) /\
    tf = tn1 with <|t_var := tn1.t_var |+
      (STRING #"%" (toString sn.cs_next_var),{}) |+
      (STRING #"%" (toString (sn.cs_next_var+1)),{}) |+
      (STRING #"%" (toString (sn.cs_next_var+2)),{});
      t_mem := tn1.t_mem DIFF range_bytes [(w2n r,32)]|>` by
    (irule hash_emit_sha256_tail_success_path >>
     simp[ptr_covers_inst_idx, hash_eval_operand_inst_idx] >>
     gvs[] >> metis_tac[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sn sb)` by
    (drule_all emitted_insts_sha256_tail >>
     simp[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `?u. run_inst_seq (emitted_insts sn sb) a = OK u /\
       t = u with vs_inst_idx := SUC s.vs_inst_idx` by
    (qpat_x_assum `run_inst_seq _ (_ with vs_inst_idx := _) = _` mp_tac >>
     simp[run_inst_seq_inst_idx] >>
     Cases_on `run_inst_seq (emitted_insts sn sb) a` >>
     simp[exec_result_map_def]) >>
  qexistsl_tac [`u`, `Gf`, `tf`] >> conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sa sn) s = OK a`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sn sb` mp_tac) >> simp[]) >>
  simp[] >> conj_tac
  >- (drule_all gas_path_ptr_then >> simp[ADD1, ADD_ASSOC]) >>
  metis_tac[hash_eval_operand_inst_idx]
QED

Theorem hash_alloc_sha256_success_path:
  compile_alloc_buffer 32 sa = (buf,sn) /\
  emit_op GAS [] sn = (gas_op,sg) /\
  emit_op STATICCALL [gas_op;Lit 2w;Var p;len;buf.buf_operand;Lit 32w] sg = (success_op,sc) /\
  emit_void ASSERT [success_op] sc = ((),sh) /\
  emit_op MLOAD [buf.buf_operand] sh = (op,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  ghost_inv d cenv cx es G tn s /\
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
    gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
      (OK (t with vs_inst_idx := s.vs_inst_idx+5)) /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    ghost_inv d cenv cx (es with outcomes := SOME rest) Gf tf
      (t with vs_inst_idx := s.vs_inst_idx+5) /\
    ghost_kept cenv es sa G tn s Gf tf /\ op_taint tf op = {} /\
    op_prov Gf op = NONE
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all hash_literal_alloc_input_frame >>
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
  drule_all hash_emit_sha256_tail_frame >> strip_tac >>
  `ghost_kept cenv es sa G tn s Gf tf` by
    (irule hash_ghost_kept_clean_tail >>
     qexistsl_tac [`G1`, `tn1`] >> conj_tac
     >- (qpat_assum `ghost_kept cenv es sn G1 tn1 t Gf tf` mp_tac >>
         qpat_assum `!y. not_fresh_at sa y ==> not_fresh_at sn y` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[ghost_kept_def] >> metis_tac[]) >>
     qpat_assum `tf = _` SUBST1_TAC >> simp[]) >>
  qpat_x_assum `ghost_inv d cenv cx (es with outcomes := SOME rest) Gf tf _`
    (assume_tac o PURE_REWRITE_RULE [hash_ghost_inv_inst_idx]) >>
  qexistsl_tac [`t'`, `Gf`, `tf`] >> simp[hash_ghost_inv_inst_idx]
QED
