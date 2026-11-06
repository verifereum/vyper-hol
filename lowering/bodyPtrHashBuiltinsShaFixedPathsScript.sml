(* Fixed SHA wrappers reuse the shared allocated precompile tail. *)
Theory bodyPtrHashBuiltinsShaFixedPaths
Ancestors bodyPtrHashBuiltinsShaFixed bodyPtrHashBuiltinsShaAlloc
  bodyPtrHashBuiltinsShaBytes bodyPtrHashBuiltinsShaEndpoint
  bodyPtrHashBuiltinsGhostFrame builtinHashing context emitHelperProps
  exprLoweringProps compileEnv freshWrites bodyPtrDefs ptrDiscipline
  venomState venomInst fragExec instIdxIndep ghostPcTransportPtr
  fragGasPathPtr words list rich_list arithmetic finite_map pred_set arithmeticProps exprSimHash

Theorem hash_sha256_fixed_code_split:
  compile_alloc_buffer 32 sa = (ib,sl) /\
  emit_void MSTORE [ib.buf_operand;value] sl = ((),sm) /\
  sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
  isPREFIX (emitted_insts sm sb) (DROP (s.vs_inst_idx+2) bb.bb_instructions)
Proof
  strip_tac >> drule_all hash_fixed_prepare_emission >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (irule emitted_insts_prefix_split >> metis_tac[]) >> simp[] >>
  `isPREFIX (emitted_insts sa sm ++ emitted_insts sm sb)
    (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule hash_code_prefix_split >> simp[]
QED

Theorem hash_sha256_bytesm_abort_path:
  !D ctx fn PG G tn s bb value v m sa op sb d cenv cx es.
  compile_sha256_bytesm value m sa = (op,sb) /\ m <= 32 /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  eval_operand value s = SOME v /\ op_taint tn value = {} /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst (sa.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var+1))]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  ?t j Gf tf. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
      (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule hash_sha256_fixed_parts >> strip_tac >>
  drule_all hash_sha256_alloc_tail_layout >> strip_tac >>
  drule_all hash_sha256_fixed_code_split >> strip_tac >>
  drule_all hash_fixed_prepare_endpoint >>
  disch_then (qspecl_then [`D`, `PG`]
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))) >>
  suspend "call"
QED

Resume hash_sha256_bytesm_abort_path[call]:
  qpat_x_assum `ib.buf_operand = Var p` SUBST_ALL_TAC >>
  `m < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `ptr_covers G2 tn2 p a (w2n (n2w m:bytes32)) /\
   isPREFIX (emitted_insts sm sb) (DROP a.vs_inst_idx bb.bb_instructions) /\
   MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString sm.cs_next_var)]) (fn_insts fn)` by
    simp[IgnAsm `a = _`] >>
  `~(?outcome rest. a.vs_outcomes = outcome::rest /\ outcome.co_success)` by
    (qpat_x_assum `~(?outcome rest. s.vs_outcomes = _ /\ _)` mp_tac >> simp[]) >>
  `eval_operand (Lit (n2w m)) a = SOME (n2w m) /\
   op_taint tn2 (Lit (n2w m)) = {} /\
   (!x. x=p \/ Lit (n2w m:bytes32)=Var x ==> not_fresh_at sm x)` by
    simp[eval_operand_def, op_taint_def] >>
  Q.SUBGOAL_THEN
    `(w2n (n2w m:bytes32) = 0 \/
     (?aid b k. FLOOKUP a.vs_allocas aid = SOME (b,k) /\
       aid < sm.cs_next_id /\ b <= w2n w /\
       w2n w+w2n (n2w m:bytes32) <= b+k) \/
     (?name b k. local_region cenv es.scopes a name b k /\
       b <= w2n w /\ w2n w+w2n (n2w m:bytes32) <= b+k))` assume_tac >-
    (disj2_tac >> disj1_tac >> qexistsl_tac [`sa.cs_next_id`, `w2n w`, `32`] >> simp[]) >>
  `!i. w2n w <= i /\ i < w2n w+w2n (n2w m:bytes32) ==> i NOTIN tn2.t_mem` by simp[] >>
  drule_all hash_alloc_sha256_abort_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "compose"
QED

Resume hash_sha256_bytesm_abort_path[compose]:
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sb)` by
    (drule_all hash_sha256_alloc_tail_nonterminators >> simp[]) >>
  `?u. run_inst_seq (emitted_insts sm sb) t = Abort Revert_abort u /\
       t' = u with vs_inst_idx := s.vs_inst_idx+2` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sb) a = _` mp_tac >>
     qpat_assum `a = _` SUBST1_TAC >> simp[run_inst_seq_inst_idx] >>
     Cases_on `run_inst_seq (emitted_insts sm sb) t` >> simp[exec_result_map_def]) >>
  qexistsl_tac [`u`, `j`, `Gf`, `tf`] >> conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK t`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[]) >>
  qpat_x_assum `t' = u with vs_inst_idx := _` SUBST_ALL_TAC >>
  drule_all gas_path_ptr_then >> simp[]
QED
Finalise hash_sha256_bytesm_abort_path

Theorem hash_sha256_bytesm_success_path:
  !D ctx fn PG G tn s bb value v m sa op sb d cenv cx es bs outcome rest.
  compile_sha256_bytesm value m sa = (op,sb) /\ m <= 32 /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  eval_operand value s = SOME v /\ op_taint tn value = {} /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst (sa.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var+1))]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  LENGTH bs = m /\ TAKE m (word_to_bytes_be v) = bs /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
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
  drule hash_sha256_fixed_parts >> strip_tac >>
  drule_all hash_sha256_alloc_tail_layout >> strip_tac >>
  drule_all hash_sha256_fixed_code_split >> strip_tac >>
  drule_all hash_fixed_prepare_endpoint >>
  disch_then (qspecl_then [`D`, `PG`]
    (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS))) >>
  suspend "call"
QED

Resume hash_sha256_bytesm_success_path[call]:
  qpat_x_assum `ib.buf_operand = Var p` SUBST_ALL_TAC >>
  `m < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `ptr_covers G2 tn2 p a (w2n (n2w m:bytes32)) /\
   isPREFIX (emitted_insts sm sb) (DROP a.vs_inst_idx bb.bb_instructions) /\
   MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w]
     [STRING #"%" (toString sm.cs_next_var)]) (fn_insts fn)` by
    simp[IgnAsm `a = _`] >>
  `eval_operand (Lit (n2w m)) a = SOME (n2w m) /\
   op_taint tn2 (Lit (n2w m)) = {} /\
   (!x. x=p \/ Lit (n2w m:bytes32)=Var x ==> not_fresh_at sm x)` by
    simp[eval_operand_def, op_taint_def] >>
  Q.SUBGOAL_THEN
    `(w2n (n2w m:bytes32) = 0 \/
     (?aid b k. FLOOKUP a.vs_allocas aid = SOME (b,k) /\
       aid < sm.cs_next_id /\ b <= w2n w /\
       w2n w+w2n (n2w m:bytes32) <= b+k) \/
     (?name b k. local_region cenv es.scopes a name b k /\
       b <= w2n w /\ w2n w+w2n (n2w m:bytes32) <= b+k))` assume_tac >-
    (disj2_tac >> disj1_tac >> qexistsl_tac [`sa.cs_next_id`, `w2n w`, `32`] >> simp[]) >>
  `!i. w2n w <= i /\ i < w2n w+w2n (n2w m:bytes32) ==> i NOTIN tn2.t_mem` by simp[] >>
  `a.vs_outcomes = outcome::rest /\
   mem_bytes_at (w2n w) (w2n (n2w m:bytes32)) a.vs_memory = bs` by
    (simp[IgnAsm `a = _`] >>
     qpat_x_assum `!bs. LENGTH bs = m /\ _ ==> _` (qspec_then `bs` mp_tac) >>
     simp[IgnAsm `a = _`]) >>
  drule_all hash_alloc_sha256_success_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "compose"
QED

Resume hash_sha256_bytesm_success_path[compose]:
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
  drule_all hash_ghost_kept_then >> strip_tac >>
  qpat_x_assum `t' = u with vs_inst_idx := _` SUBST_ALL_TAC >>
  qexistsl_tac [`u`, `Gf`, `tf`] >> conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sa sm) s = OK t`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sm sb` mp_tac) >> simp[]) >>
  conj_tac >- (drule_all gas_path_ptr_then >> simp[]) >>
  qpat_x_assum `eval_operand op (_ with vs_inst_idx := _) = _` mp_tac >>
  qpat_x_assum `ghost_inv d cenv cx (es with outcomes := SOME rest) Gf tf _` mp_tac >>
  simp[hash_eval_operand_inst_idx, hash_ghost_inv_inst_idx]
QED
Finalise hash_sha256_bytesm_success_path

Theorem hash_sha256_word_abort_path:
  !D ctx fn PG G tn s bb value v sa op sb d cenv cx es.
  compile_sha256_word value sa = (op,sb) /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  eval_operand value s = SOME v /\ op_taint tn value = {} /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst (sa.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var+1))]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  ?t j Gf tf. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
      (Abort Revert_abort (t with vs_inst_idx := j))
Proof
  rewrite_tac[hash_sha256_word_bytesm] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `32 <= 32` by decide_tac >>
  drule_all hash_sha256_bytesm_abort_path >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >> simp[]
QED

Theorem hash_sha256_word_success_path:
  !D ctx fn PG G tn s bb value v sa op sb d cenv cx es bs outcome rest.
  compile_sha256_word value sa = (op,sb) /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  eval_operand value s = SOME v /\ op_taint tn value = {} /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  MEM (mk_inst (sa.cs_next_id+2) ALLOCA [Lit 32w]
    [STRING #"%" (toString (sa.cs_next_var+1))]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  LENGTH bs = 32 /\ TAKE 32 (word_to_bytes_be v) = bs /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
  ?t Gf tf. run_inst_seq (emitted_insts sa sb) s = OK t /\
    gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf
      (OK (t with vs_inst_idx := s.vs_inst_idx+7)) /\
    eval_operand op t = SOME (SHA_256_bytes bs) /\
    ghost_inv d cenv cx (es with outcomes := SOME rest) Gf tf
      (t with vs_inst_idx := s.vs_inst_idx+7) /\
    ghost_kept cenv es sa G tn s Gf tf /\ op_taint tf op = {} /\
    op_prov Gf op = NONE
Proof
  rewrite_tac[hash_sha256_word_bytesm] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `32 <= 32` by decide_tac >>
  drule_all hash_sha256_bytesm_success_path >>
  disch_then (qspecl_then [`D`, `PG`] mp_tac) >> simp[]
QED
