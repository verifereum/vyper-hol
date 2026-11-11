(* Dynamic SHA code decomposition and counted execution. *)
Theory bodyPtrHashBuiltinsShaBytes
Ancestors bodyPtrHashBuiltinsShaPrefix bodyPtrHashBuiltinsShaAlloc
  bodyPtrHashBuiltinsInputWindow builtinHashing emitHelper emitHelperProps
  compileEnv exprLoweringProps context loweringHalt rich_list list arithmetic
  venomState venomInst exprSimHash words arithmeticProps freshWrites
  bodyPtrHashBuiltinsGhostFrame ghostPcTransportPtr fragExec instIdxIndep
  fragGasPathPtr bodyPtrHashBuiltinsShaEndpoint

Theorem hash_sha256_bytes_parts:
  compile_sha256_bytes ptr_op sa = (op,sb) ==>
  ?len_op sl data_op sm buf sn gas_op sg success_op sc sh.
    emit_op MLOAD [ptr_op] sa = (len_op,sl) /\
    emit_op ADD [ptr_op;Lit 32w] sl = (data_op,sm) /\
    compile_alloc_buffer 32 sm = (buf,sn) /\
    emit_op GAS [] sn = (gas_op,sg) /\
    emit_op STATICCALL [gas_op;Lit 2w;data_op;len_op;buf.buf_operand;Lit 32w] sg = (success_op,sc) /\
    emit_void ASSERT [success_op] sc = ((),sh) /\
    emit_op MLOAD [buf.buf_operand] sh = (op,sb)
Proof
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_sha256_bytes_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
     comp_return_def] >>
  ntac 6 (pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) []) >>
  strip_tac >> gvs[] >>
  rename1 `emit_void ASSERT [_] _ = (u,_)` >> Cases_on `u` >>
  metis_tac[]
QED

Theorem hash_sha256_alloc_tail_layout:
  compile_alloc_buffer 32 sm = (buf,sn) /\
  emit_op GAS [] sn = (gas_op,sg) /\
  emit_op STATICCALL [gas_op;Lit 2w;ptr_op;len_op;buf.buf_operand;Lit 32w] sg = (success_op,sc) /\
  emit_void ASSERT [success_op] sc = ((),sh) /\
  emit_op MLOAD [buf.buf_operand] sh = (op,sb) ==>
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  LENGTH (emitted_insts sm sb) = 5
Proof
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def] >> strip_tac >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC]
QED

Theorem hash_sha256_alloc_tail_nonterminators:
  compile_alloc_buffer 32 sm = (buf,sn) /\
  emit_op GAS [] sn = (gas_op,sg) /\
  emit_op STATICCALL [gas_op;Lit 2w;ptr_op;len_op;buf.buf_operand;Lit 32w] sg = (success_op,sc) /\
  emit_void ASSERT [success_op] sc = ((),sh) /\
  emit_op MLOAD [buf.buf_operand] sh = (op,sb) ==>
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)
Proof
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def] >> rpt strip_tac >>
  gvs[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem hash_sha256_bytes_abort_path:
  !D ctx fn PG G tn s bb x sa op sb b base cap n d cenv cx es.
  compile_sha256_bytes (Var x) sa = (op,sb) /\ not_fresh_at sa x /\
  eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
  b+32 < dimword (:256) /\ n < dimword (:256) /\ op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  MEM (mk_inst (sa.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var+2))]) (fn_insts fn) /\
  (n = 0 \/
   (?aid a k. FLOOKUP s.vs_allocas aid = SOME (a,k) /\
      aid < sa.cs_next_id /\ a <= b+32 /\ b+32+n <= a+k) \/
   (?name a k. local_region cenv es.scopes s name a k /\
      a <= b+32 /\ b+32+n <= a+k)) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  ?t j Gf tf. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
      (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule hash_sha256_bytes_parts >> strip_tac >>
  drule_all hash_bytes_prepare_emission >> strip_tac >>
  drule_all hash_sha256_alloc_tail_layout >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   LENGTH (emitted_insts sa sm) = 2` by
    (qpat_x_assum `emit_op MLOAD [Var x] sa = _` mp_tac >>
     qpat_x_assum `emit_op ADD [Var x;Lit 32w] _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
     gvs[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_prefix_split >> metis_tac[]) >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts sm sb) (DROP (s.vs_inst_idx+2) bb.bb_instructions)` by
    (`isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
        (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
     drule hash_code_prefix_split >> simp[]) >>
  drule_all hash_bytes_prepare_endpoint >>
  disch_then (qspecl_then [`D`, `PG`]
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))) >>
  suspend "call"
QED

Resume hash_sha256_bytes_abort_path[call]:
  qpat_x_assum `data_op = Var p` SUBST_ALL_TAC >>
  `a.vs_inst_idx = s.vs_inst_idx+2` by simp[] >>
  `emit_op STATICCALL [gas_op;Lit 2w;Var p;len_op;buf.buf_operand;Lit 32w] sg = (success_op,sc) /\
   stmt_state_rel ctx fn cenv cx es a /\ ghost_inv d cenv cx es G1 tn1 a /\
   eval_operand (Var p) a = SOME (n2w (b+32)) /\
   eval_operand len_op a = SOME (n2w n) /\
   ptr_covers G1 tn1 p a (w2n (n2w n:bytes32)) /\ ~a.vs_halted /\
   lookup_block a.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sm sb) (DROP a.vs_inst_idx bb.bb_instructions)` by
    simp[IgnAsm `a = _`] >>
  `!z. z=p \/ len_op=Var z ==> not_fresh_at sm z` by metis_tac[] >>
  `!i. w2n (n2w (b+32):bytes32) <= i /\
       i < w2n (n2w (b+32):bytes32)+w2n (n2w n:bytes32) ==> i NOTIN tn1.t_mem` by simp[] >>
  `~(?outcome rest. a.vs_outcomes = outcome::rest /\ outcome.co_success)` by
    (qpat_assum `~(?outcome rest. s.vs_outcomes = _ /\ _)` mp_tac >> simp[]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sm.cs_next_var)]) (fn_insts fn)` by simp[] >>
  Q.SUBGOAL_THEN
    `(w2n (n2w n:bytes32) = 0 \/
     (?aid lb k. FLOOKUP a.vs_allocas aid = SOME (lb,k) /\
        aid < sm.cs_next_id /\ lb <= w2n (n2w (b+32):bytes32) /\
        w2n (n2w (b+32):bytes32)+w2n (n2w n:bytes32) <= lb+k) \/
     (?name lb k. local_region cenv es.scopes a name lb k /\
        lb <= w2n (n2w (b+32):bytes32) /\
        w2n (n2w (b+32):bytes32)+w2n (n2w n:bytes32) <= lb+k))` assume_tac >-
    (qpat_x_assum `n = 0 \/ (?aid lb k. FLOOKUP a.vs_allocas aid = _ /\ aid < sm.cs_next_id /\ _) \/ _` mp_tac >>
     simp[] >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM]) >>
  drule_all hash_alloc_sha256_abort_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "compose"
QED

Resume hash_sha256_bytes_abort_path[compose]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule_all hash_sha256_alloc_tail_nonterminators >> simp[]) >>
  `?u. run_inst_seq (emitted_insts sm sb) t = Abort Revert_abort u /\
       t' = u with vs_inst_idx := s.vs_inst_idx+2` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sb) a = _` mp_tac >>
     qpat_assum `a = _` SUBST1_TAC >> simp[run_inst_seq_inst_idx] >>
     Cases_on `run_inst_seq (emitted_insts sm sb) t` >>
     simp[exec_result_map_def]) >>
  qexistsl_tac [`u`, `j`, `Gf`, `tf`] >> conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK t`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[]) >>
  qpat_x_assum `t' = u with vs_inst_idx := _` SUBST_ALL_TAC >>
  drule_all gas_path_ptr_then >> simp[]
QED
Finalise hash_sha256_bytes_abort_path


Theorem hash_sha256_bytes_success_path:
  !D ctx fn PG G tn s bb x sa op sb b base cap n d cenv cx es outcome rest bs.
  compile_sha256_bytes (Var x) sa = (op,sb) /\ not_fresh_at sa x /\
  eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
  b+32 < dimword (:256) /\ n < dimword (:256) /\ op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  MEM (mk_inst (sa.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var+2))]) (fn_insts fn) /\
  (n = 0 \/
   (?aid a k. FLOOKUP s.vs_allocas aid = SOME (a,k) /\
      aid < sa.cs_next_id /\ a <= b+32 /\ b+32+n <= a+k) \/
   (?name a k. local_region cenv es.scopes s name a k /\
      a <= b+32 /\ b+32+n <= a+k)) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success /\
  mem_bytes_at (b+32) n s.vs_memory = bs ==>
  ?t Gf tf. run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
      (OK (t with vs_inst_idx := s.vs_inst_idx+7)) /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    ghost_inv d cenv cx (es with outcomes := SOME rest) Gf tf
      (t with vs_inst_idx := s.vs_inst_idx+7) /\
    ghost_kept cenv es sa G tn s Gf tf /\ op_taint tf op = {} /\
    op_prov Gf op = NONE
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule hash_sha256_bytes_parts >> strip_tac >>
  drule_all hash_bytes_prepare_emission >> strip_tac >>
  drule_all hash_sha256_alloc_tail_layout >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   LENGTH (emitted_insts sa sm) = 2` by
    (qpat_x_assum `emit_op MLOAD [Var x] sa = _` mp_tac >>
     qpat_x_assum `emit_op ADD [Var x;Lit 32w] _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >> rpt strip_tac >>
     gvs[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC]) >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_prefix_split >> metis_tac[]) >>
  `isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts sm sb) (DROP (s.vs_inst_idx+2) bb.bb_instructions)` by
    (`isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
        (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
     drule hash_code_prefix_split >> simp[]) >>
  drule_all hash_bytes_prepare_endpoint >>
  disch_then (qspecl_then [`D`, `PG`]
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))) >>
  suspend "call"
QED

Resume hash_sha256_bytes_success_path[call]:
  qpat_x_assum `data_op = Var p` SUBST_ALL_TAC >>
  `ptr_covers G1 tn1 p a (w2n (n2w n:bytes32)) /\
   isPREFIX (emitted_insts sm sb) (DROP a.vs_inst_idx bb.bb_instructions)` by
    simp[IgnAsm `a = _`] >>
  `!z. z=p \/ len_op=Var z ==> not_fresh_at sm z` by metis_tac[] >>
  `!i. w2n (n2w (b+32):bytes32) <= i /\
       i < w2n (n2w (b+32):bytes32)+w2n (n2w n:bytes32) ==> i NOTIN tn1.t_mem` by simp[] >>
  `a.vs_outcomes = outcome::rest /\
   mem_bytes_at (w2n (n2w (b+32):bytes32)) (w2n (n2w n:bytes32)) a.vs_memory = bs` by simp[] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sm.cs_next_var)]) (fn_insts fn)` by simp[] >>
  Q.SUBGOAL_THEN
    `(w2n (n2w n:bytes32) = 0 \/
     (?aid lb k. FLOOKUP a.vs_allocas aid = SOME (lb,k) /\
        aid < sm.cs_next_id /\ lb <= w2n (n2w (b+32):bytes32) /\
        w2n (n2w (b+32):bytes32)+w2n (n2w n:bytes32) <= lb+k) \/
     (?name lb k. local_region cenv es.scopes a name lb k /\
        lb <= w2n (n2w (b+32):bytes32) /\
        w2n (n2w (b+32):bytes32)+w2n (n2w n:bytes32) <= lb+k))` assume_tac >-
    (qpat_x_assum `n = 0 \/ (?aid lb k. FLOOKUP a.vs_allocas aid = _ /\ aid < sm.cs_next_id /\ _) \/ _` mp_tac >>
     simp[] >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM]) >>
  drule_all hash_alloc_sha256_success_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "compose"
QED

Resume hash_sha256_bytes_success_path[compose]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule_all hash_sha256_alloc_tail_nonterminators >> simp[]) >>
  `?u. run_inst_seq (emitted_insts sm sb) t = OK u /\
       t' = u with vs_inst_idx := s.vs_inst_idx+2` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sb) a = _` mp_tac >>
     qpat_assum `a = _` SUBST1_TAC >> simp[run_inst_seq_inst_idx] >>
     Cases_on `run_inst_seq (emitted_insts sm sb) t` >> simp[exec_result_map_def]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at sm z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `sa.cs_next_id <= sm.cs_next_id` by simp[] >>
  `!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP a.vs_allocas aid = SOME entry` by simp[] >>
  drule_all hash_ghost_kept_then >> strip_tac >>
  qpat_x_assum `t' = u with vs_inst_idx := _` SUBST_ALL_TAC >>
  qexistsl_tac [`u`, `Gf`, `tf`] >> conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK t`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[]) >>
  conj_tac
  >- (drule_all gas_path_ptr_then >> simp[]) >>
  qpat_x_assum `eval_operand op (_ with vs_inst_idx := _) = _` mp_tac >>
  qpat_x_assum `ghost_inv d cenv cx (es with outcomes := SOME rest) Gf tf _` mp_tac >>
  simp[hash_eval_operand_inst_idx, hash_ghost_inv_inst_idx]
QED
Finalise hash_sha256_bytes_success_path
