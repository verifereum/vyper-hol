(* Robust literal representations and ghost frame boundaries. *)
Theory exprSimPtrLiteralBuffer
Ancestors
  exprSimPtrLiteralChunks robustCopyTransportPtr exprSimProps
  bodyPtrDefs compileEnv valueEncoding valueEncodingProofs valueEncodingProps
  venomMemProofs venomState finite_map words list pred_set
  exprSimPtrLiteralOps venomExecSemantics venomInst fragExecPtr fragExec fragGasSeqPtr exprLoweringProps ptrDiscipline instIdxIndep

Theorem literal_clean_window_agree:
  mem_agree_outside dirty mem mem' /\
  (!i. off <= i /\ i < off+len ==> i NOTIN dirty) ==>
  mem_bytes_at off len mem = mem_bytes_at off len mem'
Proof
  strip_tac >> irule LIST_EQ >> simp[] >> rpt strip_tac >>
  rename1 `j < len` >>
  `off+j NOTIN dirty` by (first_x_assum irule >> decide_tac) >>
  `mem_bytes_at (off+j) 1 mem = mem_bytes_at (off+j) 1 mem'` by
    metis_tac[mem_agree_outside_def] >>
  pop_assum mp_tac >> simp[LIST_EQ_REWRITE, EL_mem_bytes_at]
QED

Theorem literal_clean_representation_robust:
  val_in_memory tv value off mem /\ val_wf tv value /\
  (!i. off <= i /\ i < off+val_footprint tv value ==> i NOTIN dirty) ==>
  !mem'. mem_agree_outside dirty mem mem' ==>
    val_in_memory tv value off mem'
Proof
  rpt strip_tac >> irule val_in_memory_footprint_agree >>
  conj_tac >- simp[] >>
  qexists_tac `mem` >> simp[] >>
  irule literal_clean_window_agree >> metis_tac[]
QED

Theorem literal_ghost_kept:
  (!x. not_fresh_at sa x ==>
    FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem SUBSET tn.t_mem ==>
  ghost_kept cenv es sa G tn s G' tn'
Proof
  simp[ghost_kept_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem literal_clean_ptr_mem_ok:
  lookup_var p s = SOME w /\ FLOOKUP G p = SOME (base_addr,sz) /\
  base_addr <= w2n w /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    val_wf tv value /\ val_in_memory tv value (w2n w) s.vs_memory /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint tv value ==>
         i NOTIN tn.t_mem) /\
    w2n w + val_store_size tv value <= base_addr + sz) ==>
  ptr_mem_ok cx ty value (Var p) G tn s
Proof
  strip_tac >> simp[ptr_mem_ok_def, eval_operand_def] >>
  rpt strip_tac
  >- (irule literal_clean_representation_robust >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`tn.t_mem`, `s.vs_memory`] >> metis_tac[]) >>
  qexistsl_tac [`base_addr`, `sz`] >> metis_tac[]
QED

Theorem literal_site_ptr_buf_ok:
  lookup_var p s = SOME w /\ FLOOKUP G p = SOME (base_addr,sz) /\
  base_addr <= w2n w /\
  w2n w + type_memory_bytes cenv (lowered_value_type cenv e) <= base_addr + sz ==>
  ptr_buf_ok cenv e (Var p) G s
Proof
  simp[ptr_buf_ok_def, eval_operand_def] >> metis_tac[]
QED

Theorem literal_ghost_inv_frame:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x s' = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!name entry p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==>
    val_wf entry.type entry.value /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint entry.type entry.value ==>
         i NOTIN writes)) /\
  (!i. i NOTIN writes ==>
    mem_bytes_at i 1 s'.vs_memory = mem_bytes_at i 1 s.vs_memory /\
    (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_accounts = s.vs_accounts /\
  s'.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es G' tn' s'
Proof
  strip_tac >>
  `!x sz. not_fresh_at sa x /\ ptr_covers G tn x s sz ==>
          ptr_covers G' tn' x s' sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_def, stor_taint_ok_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      irule robust_val_in_memory_exterior_frame >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`s.vs_memory`, `s'.vs_memory`, `tn.t_mem`,
                     `tn'.t_mem`, `writes`] >>
      metis_tac[])
  >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
      fs[return_buf_ptr_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem literal_header_chunks_ptr:
  compile_store_byte_chunks (Var p) bs 32 sh = ((),sb) /\
  not_fresh_at sh p /\ lookup_var p s = SOME (n2w b) /\
  FLOOKUP G p = SOME (b,32+32*word_size (LENGTH bs)) /\
  op_taint tn (Var p) = {} /\ ~ctx_has_dalloca ctx /\
  b + 32 + 32*word_size (LENGTH bs) < dimword (:256) ==>
  ?t G' tn'.
    run_inst_seq (mk_inst id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
      emitted_insts sh sb) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (mk_inst id MSTORE [Var p; Lit (n2w (LENGTH bs))] [] ::
       emitted_insts sh sb) s G' tn' /\
    tn'.t_mem = tn.t_mem DIFF
      {i | b <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_imm = tn.t_imm /\
    (!v. not_fresh_at sh v ==>
      FLOOKUP G' v = FLOOKUP G v /\
      FLOOKUP tn'.t_var v = FLOOKUP tn.t_var v)
Proof
  strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `ptr_covers G tn p s 32` by
    (simp[ptr_covers_def, w2n_n2w] >> decide_tac) >>
  `step_inst_base (mk_inst id MSTORE [Var p; Lit (n2w (LENGTH bs))] []) s =
     OK (mstore b (n2w (LENGTH bs)) s)` by
    (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def, w2n_n2w]) >>
  drule literal_mstore_ghost >>
  disch_then (qspecl_then [`n2w (LENGTH bs)`, `tn`, `id`, `PG`, `G`]
    strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `OK u` >>
  `lookup_var p u = SOME (n2w b)` by
    simp[Abbr `u`, mstore_def, lookup_var_def] >>
  qabbrev_tac `uh = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `th = tn with t_mem := tn.t_mem DIFF {i | b <= i /\ i < b+32}` >>
  `lookup_var p uh = SOME (n2w b) /\ op_taint th (Var p) = {}` by
    (simp[Abbr `uh`, Abbr `th`, lookup_var_def, op_taint_def] >>
     fs[lookup_var_def, op_taint_def]) >>
  `?t G' tn'. run_inst_seq (emitted_insts sh sb) uh = OK t /\
    inst_seq_ptr D 0 ctx fn PG G th (emitted_insts sh sb) uh G' tn' /\
    tn'.t_mem = th.t_mem DIFF
      {i | b+32 <= i /\ i < b+32+32*word_size (LENGTH bs)} /\
    tn'.t_stor = th.t_stor /\ tn'.t_trans = th.t_trans /\
    tn'.t_imm = th.t_imm /\
    (!v. not_fresh_at sh v ==> lookup_var v t = lookup_var v uh /\
      FLOOKUP G' v = FLOOKUP G v /\ FLOOKUP tn'.t_var v = FLOOKUP th.t_var v)` by
    (irule (cj 6 literal_chunks_ptr) >>
     simp[] >>
     qexistsl_tac [`b`, `32+32*word_size (LENGTH bs)`, `p`] >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sh sb)` by
    metis_tac[cj 5 literal_chunks_ptr, arithmeticTheory.LESS_EQ_REFL,
              arithmeticTheory.ADD_ASSOC] >>
  Cases_on `run_inst_seq (emitted_insts sh sb) u` >>
  fs[Abbr `uh`, run_inst_seq_inst_idx, exec_result_map_def] >>
  qexistsl_tac [`v`, `G'`, `tn'`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, literal_mstore_ptr_inst_ok] >>
  gvs[Abbr `u`, Abbr `th`, w2n_n2w, mk_inst_def,
      arithmeticTheory.LESS_MOD, is_terminator_def] >>
  rpt conj_tac >> simp[] >>
  simp[pred_setTheory.EXTENSION] >> rpt gen_tac >>
  eq_tac >> simp[] >> decide_tac
QED
