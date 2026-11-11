(* Fixed-size SHA input preparation and compiler shape boundaries. *)
Theory bodyPtrHashBuiltinsShaFixed
Ancestors bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsShaBytes
  builtinHashing emitHelper emitHelperProps compileEnv loweringStateRelDefs exprLoweringProps
  list rich_list arithmetic context fragGasSeqPtr ptrDiscipline venomState
  venomExecSemantics venomInst fragExec instIdxIndep words fragExecPtr ghostPcTransportPtr
  bodyPtrDefs finite_map pred_set freshWrites bodyPtrHashBuiltinsGhostFrame exprSimHash

Theorem hash_sha256_fixed_parts:
  compile_sha256_bytesm value m sa = (op,sb) ==>
  ?ib sl sm ob sn gas_op sg success_op sc sh.
    compile_alloc_buffer 32 sa = (ib,sl) /\
    emit_void MSTORE [ib.buf_operand;value] sl = ((),sm) /\
    compile_alloc_buffer 32 sm = (ob,sn) /\
    emit_op GAS [] sn = (gas_op,sg) /\
    emit_op STATICCALL [gas_op;Lit 2w;ib.buf_operand;Lit (n2w m);ob.buf_operand;Lit 32w] sg = (success_op,sc) /\
    emit_void ASSERT [success_op] sc = ((),sh) /\
    emit_op MLOAD [ob.buf_operand] sh = (op,sb)
Proof
  simp_tac (bool_ss ++ pairSimps.PAIR_ss)
    [compile_sha256_bytesm_def, LET_THM, comp_bind_def, comp_ignore_bind_def,
     comp_return_def] >>
  ntac 6 (pairarg_tac >> asm_simp_tac (bool_ss ++ pairSimps.PAIR_ss) []) >>
  strip_tac >> gvs[] >>
  rpt (qpat_x_assum `emit_void _ _ _ = (u,_)` mp_tac >> Cases_on `u` >> strip_tac) >>
  metis_tac[]
QED

Theorem hash_sha256_word_bytesm:
  compile_sha256_word value = compile_sha256_bytesm value 32
Proof
  simp[compile_sha256_word_def, compile_sha256_bytesm_def]
QED

Theorem hash_fixed_prepare_emission:
  compile_alloc_buffer 32 sa = (ib,sl) /\
  emit_void MSTORE [ib.buf_operand;value] sl = ((),sm) ==>
  ib.buf_operand = Var (STRING #"%" (toString sa.cs_next_var)) /\
  emitted_insts sa sm =
    [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id+1) MSTORE
       [Var (STRING #"%" (toString sa.cs_next_var));value] []] /\
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  sm.cs_next_var = sa.cs_next_var+1 /\ sm.cs_next_id = sa.cs_next_id+2
Proof
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
    fresh_id_def, emit_def] >> strip_tac >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC]
QED

Theorem hash_alloc_store_counted:
  step_inst_base (mk_inst aid ALLOCA [Lit 32w] [p]) s = OK t /\
  lookup_var p t = SOME a /\ eval_operand value t = SOME w /\
  G1 = step_prov PG G (mk_inst aid ALLOCA [Lit 32w] [p]) t /\
  tn1 = step_taint (mk_inst aid ALLOCA [Lit 32w] [p]) s t tn /\
  G2 = step_prov PG G1 (mk_inst sid MSTORE [Var p;value] []) (mstore (w2n a) w t) /\
  tn2 = step_taint (mk_inst sid MSTORE [Var p;value] []) t (mstore (w2n a) w t) tn1 /\
  ptr_covers G1 tn1 p t 32 /\ op_taint tn1 value = {} /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX [mk_inst aid ALLOCA [Lit 32w] [p];
    mk_inst sid MSTORE [Var p;value] []] (DROP s.vs_inst_idx bb.bb_instructions) ==>
  run_inst_seq [mk_inst aid ALLOCA [Lit 32w] [p];
    mk_inst sid MSTORE [Var p;value] []] s = OK (mstore (w2n a) w t) /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2
    (OK ((mstore (w2n a) w t) with vs_inst_idx := s.vs_inst_idx+2))
Proof
  strip_tac >>
  `step_inst_base (mk_inst sid MSTORE [Var p;value] []) t =
     OK (mstore (w2n a) w t)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                      combinTheory.K_THM, opcode_case_def] >>
     simp[exec_write2_def, eval_operand_def]) >>
  `run_inst_seq [mk_inst aid ALLOCA [Lit 32w] [p];
     mk_inst sid MSTORE [Var p;value] []] s = OK (mstore (w2n a) w t)` by
    simp[run_inst_seq_def] >> simp[] >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst aid ALLOCA [Lit 32w] [p]) s` by
    (irule ptr_inst_ok_alloca >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1 (mk_inst sid MSTORE [Var p;value] [])
      (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ptr_inst_ok_mstore >> simp[ptr_covers_inst_idx]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst aid ALLOCA [Lit 32w] [p]; mk_inst sid MSTORE [Var p;value] []] s G2 tn2` by
    (gvs[inst_seq_ptr_def] >>
     simp[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def,
       exec_result_map_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    [mk_inst aid ALLOCA [Lit 32w] [p]; mk_inst sid MSTORE [Var p;value] []]` by
    simp[mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_gas_path_ptr >> simp[]
QED

Theorem hash_alloca_control_fields:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [p]) s = OK t ==>
  t.vs_outcomes = s.vs_outcomes /\ t.vs_halted = s.vs_halted /\
  t.vs_current_bb = s.vs_current_bb
Proof
  pure_once_rewrite_tac[step_inst_base_def] >>
  pure_rewrite_tac[mk_inst_def, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_alloca_def, mk_inst_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[]
  >- (simp[update_var_def] >> strip_tac >> gvs[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME entry` >> PairCases_on `entry` >>
  simp[update_var_def] >> strip_tac >> gvs[]
QED

Theorem hash_fixed_prepare_endpoint:
  !D ctx fn PG G tn s bb value v sa ib sl sm m d cenv cx es.
  compile_alloc_buffer 32 sa = (ib,sl) /\
  emit_void MSTORE [ib.buf_operand;value] sl = ((),sm) /\ m <= 32 /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  eval_operand value s = SOME v /\ op_taint tn value = {} /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ghost_inv d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t a p w G2 tn2.
  a = t with vs_inst_idx := s.vs_inst_idx+2 /\
  run_inst_seq (emitted_insts sa sm) s = OK t /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2 (OK a) /\
  stmt_state_rel ctx fn cenv cx es a /\ ghost_inv d cenv cx es G2 tn2 a /\
  ghost_kept cenv es sa G tn s G2 tn2 /\ ib.buf_operand = Var p /\
  eval_operand (Var p) a = SOME w /\ ptr_covers G2 tn2 p a m /\
  (!i. w2n w <= i /\ i < w2n w+m ==> i NOTIN tn2.t_mem) /\
  FLOOKUP a.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
  sa.cs_next_id < sm.cs_next_id /\ w2n w+32 < dimword (:256) /\
  a.vs_outcomes = s.vs_outcomes /\ ~a.vs_halted /\
  lookup_block a.vs_current_bb fn.fn_blocks = SOME bb /\
  a.vs_inst_idx = s.vs_inst_idx+2 /\
  (!x. not_fresh_at sa x ==> lookup_var x a = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP a.vs_allocas aid = SOME entry) /\
  not_fresh_at sm p /\ local_ptrs_reserved cenv sm /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  sm.cs_next_var = sa.cs_next_var+1 /\ sm.cs_next_id = sa.cs_next_id+2 /\
  (!bs. LENGTH bs = m /\ TAKE m (word_to_bytes_be v) = bs ==>
    mem_bytes_at (w2n w) m a.vs_memory = bs)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all hash_fixed_prepare_emission >> strip_tac >>
  drule_all hash_literal_alloc_store_frame >>
  disch_then (qspecl_then [`PG`, `sa.cs_next_id+1`] strip_assume_tac) >>
  drule hash_alloca_control_fields >> strip_tac >>
  `isPREFIX [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p];
    mk_inst (sa.cs_next_id+1) MSTORE [Var p;value] []]
    (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all hash_alloc_store_counted >>
  disch_then (qspec_then `D` strip_assume_tac) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`mstore (w2n a) v t`,
    `(mstore (w2n a) v t) with vs_inst_idx := s.vs_inst_idx+2`,
    `p`, `a`, `G2`, `tn2`] >> suspend "post"
QED

Resume hash_fixed_prepare_endpoint[post]:
  qpat_x_assum `p = STRING _ _` SUBST_ALL_TAC >>
  qpat_x_assum `G2 = _` kall_tac >> qpat_x_assum `tn2 = _` kall_tac >>
  qpat_x_assum `G1 = _` kall_tac >> qpat_x_assum `tn1 = _` kall_tac >>
  simp[stmt_state_rel_inst_idx, hash_ghost_inv_inst_idx, ptr_covers_inst_idx] >>
  conj_tac >- simp[eval_operand_def] >>
  conj_tac >- (qpat_x_assum `ptr_covers G2 tn2 _ _ 32` mp_tac >>
    simp[ptr_covers_def] >> rpt strip_tac >>
    goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `!bs. LENGTH bs = m /\ TAKE m (word_to_bytes_be v) = bs ==>
     mem_bytes_at (w2n a) m (mstore (w2n a) v t).vs_memory = bs` by
    (rpt strip_tac >> qpat_assum `LENGTH bs = m` (fn th => rewrite_tac[GSYM th]) >>
     irule hash_mstore_prefix >> metis_tac[]) >>
  simp[] >> conj_tac
  >- simp[mstore_def] >>
  conj_tac >- (qpat_x_assum `!x. not_fresh_at sa x ==> lookup_var x t = _` mp_tac >>
    simp[mstore_def, not_fresh_at_def, lookup_var_def]) >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED
Finalise hash_fixed_prepare_endpoint
