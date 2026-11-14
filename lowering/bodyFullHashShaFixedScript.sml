(* Fixed input preparation keeps the bounded ghost before the SHA call. *)
Theory bodyFullHashShaFixed
Ancestors
  bodyFullHashShaStore bodyFullHashKeccakBytes bodyPtrHashBuiltinsShaFixed
  bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsKeccakFixed instSeqPtrLo
  bodyPtrHashBuiltinsShaAlloc
  fragGasSeqPtr fragExecMem bodyPtrDefs loweringHalt ptrDiscipline
  compileEnv loweringStateRelDefs exprLoweringProps venomState venomInst
  venomExecSemantics fragExec words list rich_list arithmetic finite_map pred_set
  freshWrites exprSimHash

Theorem sha_fixed_prepare_frame_at:
  !D lo ctx fn PG G tn s bb value v sa ib sl sm m d cenv cx es.
  compile_alloc_buffer 32 sa = (ib,sl) /\ fn_has_code sa sl fn /\
  emit_void MSTORE [ib.buf_operand;value] sl = ((),sm) /\ m <= 32 /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  eval_operand value s = SOME v /\ op_taint tn value = {} /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list)
    ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ghost_inv_at D lo d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t p w G2 tn2.
  run_inst_seq (emitted_insts sa sm) s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sm) s G2 tn2 /\
  stmt_state_rel H ctx fn cenv cx es t /\
  ghost_inv_at D lo d cenv cx es G2 tn2 t /\
  ghost_kept_at lo cenv es sa G tn s G2 tn2 /\ ib.buf_operand = Var p /\
  eval_operand (Var p) t = SOME w /\ ptr_covers G2 tn2 p t m /\
  (!i. w2n w <= i /\ i < w2n w+m ==> i NOTIN tn2.t_mem) /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32) /\
  sa.cs_next_id < sm.cs_next_id /\ w2n w+32 < dimword (:256) /\
  t.vs_outcomes = s.vs_outcomes /\ ~t.vs_halted /\
  t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
  (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  not_fresh_at sm p /\ local_ptrs_reserved cenv sm /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x) /\
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  sm.cs_next_var = sa.cs_next_var+1 /\ sm.cs_next_id = sa.cs_next_id+2 /\
  (!bs. LENGTH bs = m /\ TAKE m (word_to_bytes_be v) = bs ==>
    mem_bytes_at (w2n w) m t.vs_memory = bs)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all hash_fixed_prepare_emission >> strip_tac >>
  drule_all sha_literal_alloc_store_frame_at >>
  disch_then (qspecl_then [`PG`, `sa.cs_next_id+1`] strip_assume_tac) >>
  drule_all hash_alloc_buffer_cursor_frame >> strip_tac >>
  drule hash_alloca_control_fields >> strip_tac >>
  `isPREFIX [mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p];
    mk_inst (sa.cs_next_id+1) MSTORE [Var p;value] []]
    (DROP s.vs_inst_idx bb.bb_instructions)` by metis_tac[] >>
  drule_all hash_alloc_store_counted >>
  disch_then (qspec_then `D` strip_assume_tac) >>
  `inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sm) s G2 tn2` by
    (irule (Q.SPECL [`emitted_insts sa sm`, `D`, `D`, `lo`,
      `ctx`, `fn`, `PG`, `G`, `tn`, `s`, `G2`, `tn2`] inst_seq_ptr_zero_to_lo) >>
     fs[ghost_inv_at_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`mstore (w2n a) v t`, `p`, `a`, `G2`, `tn2`] >>
  qpat_x_assum `p = STRING _ _` SUBST_ALL_TAC >>
  qpat_x_assum `G2 = _` kall_tac >> qpat_x_assum `tn2 = _` kall_tac >>
  qpat_x_assum `G1 = _` kall_tac >> qpat_x_assum `tn1 = _` kall_tac >>
  simp[] >> conj_tac >- simp[eval_operand_def] >>
  conj_tac >- (qpat_x_assum `ptr_covers G2 tn2 _ _ 32` mp_tac >>
    simp[ptr_covers_def] >> rpt strip_tac >>
    goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `!bs. LENGTH bs = m /\ TAKE m (word_to_bytes_be v) = bs ==>
     mem_bytes_at (w2n a) m (mstore (w2n a) v t).vs_memory = bs` by
    (rpt strip_tac >> qpat_assum `LENGTH bs = m` (fn th => rewrite_tac[GSYM th]) >>
     irule hash_mstore_prefix >> metis_tac[]) >>
  simp[mstore_def, lookup_var_def, not_fresh_at_def,
    ASCIInumbersTheory.toString_inj] >> rpt conj_tac >> gvs[] >> decide_tac
QED
