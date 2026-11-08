Theory bodyPtrPrecompileBuiltinsStaging
Ancestors wordLoadStorePtr bodyPtrPrecompileBuiltinsFreshFrame bodyPtrPrecompileBuiltinsSeq
          allocationPtr typedCopyPtr fragExecPtr fragGasSeqPtr
          venomExecSemantics venomInst venomState ptrDiscipline bodyPtrDefs
          compileEnv exprLoweringProps finite_map loweringHalt context
          emitHelper contextCodegenRelProps fragExec list rich_list
          ghostPcTransportPtr

Theorem allocated_buffer_checked:
  stmt_state_rel ctx func cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  inst_seq_ptr D 0 ctx func PG G tn
    [mk_inst id ALLOCA [Lit (n2w n)] [out]] s
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn) /\
  ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn) out t n
Proof
  strip_tac >> conj_tac
  >- (simp[inst_seq_ptr_def] >> irule ptr_inst_ok_alloca >> simp[]) >>
  irule alloca_step_ptr_covers >> metis_tac[]
QED

Theorem clean_word_store_checked:
  ptr_covers G tn dst s 32 /\ op_taint tn v = {} /\
  ~ctx_has_dalloca ctx /\ lookup_var dst s = SOME a /\
  eval_operand v s = SOME w /\
  step_inst_base (mk_inst id MSTORE [Var dst; v] []) s = OK t ==>
  inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id MSTORE [Var dst; v] []] s
    (step_prov PG G (mk_inst id MSTORE [Var dst; v] []) t)
    (step_taint (mk_inst id MSTORE [Var dst; v] []) s t tn) /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==>
    i NOTIN (step_taint (mk_inst id MSTORE [Var dst; v] []) s t tn).t_mem)
Proof
  strip_tac >> conj_tac
  >- (simp[inst_seq_ptr_def] >> irule ptr_inst_ok_mstore >> simp[]) >>
  rpt gen_tac >> strip_tac >> irule mstore_word_clean >>
  simp[eval_operand_def] >> metis_tac[]
QED

(* Unlike compile_with_byte_offset this boundary executes ADD even at zero. *)
Theorem point_offset_covers:
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off + n <= capacity /\ w2n a + off < dimword (:256) ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn)
    out (update_var out (a + n2w off) s) n
Proof
  strip_tac >>
  `op_taint (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn) (Var out) = {}` by
    simp[copy_len_binop_ghost_frame] >>
  gvs[ptr_covers_def] >>
  `off < dimword (:256)` by decide_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def, op_prov_def,
       mk_inst_def, FLOOKUP_UPDATE, lookup_var_def, update_var_def,
       wordsTheory.w2n_add_2, wordsTheory.w2n_n2w,
       arithmeticTheory.LESS_MOD] >> decide_tac
QED

Theorem point_offset_checked:
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off + n <= capacity /\ w2n a + off < dimword (:256) /\
  ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [Var root; Lit (n2w off)] [out]] s
    (step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn)
Proof
  strip_tac >>
  `step_inst_base (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s =
    OK (update_var out (a + n2w off) s)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  simp[inst_seq_ptr_def] >> irule ptr_inst_ok_copy_len_binop >>
  gvs[ptr_covers_def, op_taint_def]
QED

Theorem clean_word_load_checked:
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id MLOAD [Var src] [tmp]] s
    (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn) /\
  op_taint (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn) (Var tmp) = {}
Proof
  strip_tac >> conj_tac
  >- (`step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s =
       OK (update_var tmp (mload (w2n a) s) s)` by
        (pure_once_rewrite_tac[step_inst_base_def] >>
         simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
      simp[inst_seq_ptr_def] >> irule ptr_inst_ok_mload >> simp[]) >>
  irule (cj 1 mload_ghost_clean) >> simp[eval_operand_def] >> metis_tac[]
QED

Theorem emitted_allocation_checked:
  compile_alloc_buffer n sa = (buf,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?out G' tn'. buf.buf_operand = Var out /\ not_fresh_at sb out /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G' tn' /\
    ptr_covers G' tn' out t n
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]]` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
          emit_def, emitted_insts_def, DROP_APPEND1] >>
     strip_tac >> gvs[DROP_APPEND1]) >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  drule_all allocated_buffer_checked >> strip_tac >> metis_tac[]
QED

Theorem point_offset_trace:
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off + n <= capacity /\ w2n a + off < dimword (:256) /\
  ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq [mk_inst id ADD [Var root; Lit (n2w off)] [out]] s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var root; Lit (n2w off)] [out]] s G' tn' /\
    ptr_covers G' tn' out t n /\ lookup_var out t = SOME (a + n2w off) /\
    t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!p. p <> out ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qexistsl [`update_var out (a + n2w off) s`,
    `step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s)`,
    `step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn`] >>
  conj_tac
  >- (simp[run_inst_seq_def] >>
      pure_once_rewrite_tac[step_inst_base_def] >>
      simp[mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  conj_tac >- (irule point_offset_checked >> metis_tac[]) >>
  conj_tac >- (irule point_offset_covers >> metis_tac[]) >>
  simp[copy_len_binop_ghost_frame, update_var_def, lookup_var_def,
       FLOOKUP_UPDATE]
QED

Theorem clean_word_load_trace:
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq [mk_inst id MLOAD [Var src] [tmp]] s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MLOAD [Var src] [tmp]] s G' tn' /\
    op_taint tn' (Var tmp) = {} /\
    lookup_var tmp t = SOME (mload (w2n a) s) /\
    t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!p. p <> tmp ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qexistsl [`update_var tmp (mload (w2n a) s) s`,
    `step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s)`,
    `step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn`] >>
  conj_tac
  >- (simp[run_inst_seq_def] >>
      pure_once_rewrite_tac[step_inst_base_def] >>
      simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  drule_all clean_word_load_checked >> strip_tac >> simp[] >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  drule mload_ghost_clean >> strip_tac >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       set_var_taint_def, op_taint_def, mk_inst_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem clean_word_store_trace:
  ptr_covers G tn dst s 32 /\ op_taint tn v = {} /\
  ~ctx_has_dalloca ctx /\ lookup_var dst s = SOME a /\
  eval_operand v s = SOME w ==>
  ?t tn'.
    run_inst_seq [mk_inst id MSTORE [Var dst; v] []] s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id MSTORE [Var dst; v] []] s G tn' /\
    t = mstore (w2n a) w s /\ tn'.t_var = tn.t_var /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}
Proof
  strip_tac >>
  `step_inst_base (mk_inst id MSTORE [Var dst; v] []) s =
     OK (mstore (w2n a) w s)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def]) >>
  drule_all clean_word_store_checked >> strip_tac >>
  drule_all mstore_ghost_frame >> strip_tac >>
  qexistsl [`mstore (w2n a) w s`,
    `step_taint (mk_inst id MSTORE [Var dst; v] []) s
      (mstore (w2n a) w s) tn`] >>
  simp[run_inst_seq_def] >> metis_tac[]
QED

Theorem staging_update_var_cursor[local]:
  update_var x v (s with vs_inst_idx := k) =
    (update_var x v s) with vs_inst_idx := k
Proof
  simp[update_var_def]
QED

Theorem point_offset_checked_cursors:
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off + n <= capacity /\ w2n a + off < dimword (:256) /\
  ~ctx_has_dalloca ctx ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ADD [Var root; Lit (n2w off)] [out]]
    (s with vs_inst_idx := k)
    (step_prov PG G (mk_inst id ADD [Var root; Lit (n2w off)] [out])
      (update_var out (a + n2w off) s))
    (step_taint (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s
      (update_var out (a + n2w off) s) tn)
Proof
  strip_tac >> gen_tac >>
  `ptr_covers G tn root (s with vs_inst_idx := k) capacity` by simp[] >>
  `lookup_var root (s with vs_inst_idx := k) = SOME a` by
    gvs[lookup_var_def] >>
  drule_all point_offset_checked >>
  simp[staging_update_var_cursor]
QED

Theorem clean_word_load_checked_cursors:
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id MLOAD [Var src] [tmp]]
    (s with vs_inst_idx := k)
    (step_prov PG G (mk_inst id MLOAD [Var src] [tmp])
      (update_var tmp (mload (w2n a) s) s))
    (step_taint (mk_inst id MLOAD [Var src] [tmp]) s
      (update_var tmp (mload (w2n a) s) s) tn)
Proof
  strip_tac >> gen_tac >>
  `ptr_covers G tn src (s with vs_inst_idx := k) 32` by simp[] >>
  `lookup_var src (s with vs_inst_idx := k) = SOME a` by
    gvs[lookup_var_def] >>
  drule_all clean_word_load_checked >>
  simp[staging_update_var_cursor, mload_def]
QED

Theorem staging_mstore_cursor[local]:
  mstore a w (s with vs_inst_idx := k) =
    (mstore a w s) with vs_inst_idx := k
Proof
  simp[mstore_def, write_memory_with_expansion_inst_idx]
QED

Theorem clean_word_store_checked_cursors:
  ptr_covers G tn dst s 32 /\ op_taint tn v = {} /\
  ~ctx_has_dalloca ctx /\ lookup_var dst s = SOME a /\
  eval_operand v s = SOME w ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id MSTORE [Var dst; v] []]
    (s with vs_inst_idx := k) G
    (step_taint (mk_inst id MSTORE [Var dst; v] []) s
      (mstore (w2n a) w s) tn)
Proof
  strip_tac >> gen_tac >>
  `step_inst_base (mk_inst id MSTORE [Var dst; v] [])
      (s with vs_inst_idx := k) =
    OK ((mstore (w2n a) w s) with vs_inst_idx := k)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_write2_def, eval_operand_def,
          mstore_def, write_memory_with_expansion_inst_idx]) >>
  `ptr_covers G tn dst (s with vs_inst_idx := k) 32` by simp[] >>
  `lookup_var dst (s with vs_inst_idx := k) = SOME a` by
    gvs[lookup_var_def] >>
  `eval_operand v (s with vs_inst_idx := k) = SOME w` by simp[] >>
  drule_all clean_word_store_checked >> simp[] >> strip_tac >>
  drule_all mstore_ghost_frame >>
  simp[staging_mstore_cursor] >> metis_tac[]
QED

Theorem singleton_cursor_intro[local]:
  run_inst_seq [i] s = OK t /\
  inst_seq_ptr D lo ctx fn PG G tn [i] s G' tn' /\
  (!k. inst_seq_ptr D lo ctx fn PG G tn [i] (s with vs_inst_idx := k)
    (step_prov PG G i t) (step_taint i s t tn)) ==>
  !k. inst_seq_ptr D lo ctx fn PG G tn [i] (s with vs_inst_idx := k) G' tn'
Proof
  Cases_on `step_inst_base i s` >>
  simp[run_inst_seq_def, inst_seq_ptr_def] >> metis_tac[]
QED

Theorem point_offset_trace_cursors:
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off + n <= capacity /\ w2n a + off < dimword (:256) /\
  ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq [mk_inst id ADD [Var root; Lit (n2w off)] [out]] s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var root; Lit (n2w off)] [out]]
      (s with vs_inst_idx := k) G' tn') /\
    ptr_covers G' tn' out t n /\ lookup_var out t = SOME (a + n2w off) /\
    t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!p. p <> out ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all point_offset_trace >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  qexistsl [`t`, `Gf`, `tnf`] >> simp[] >>
  irule singleton_cursor_intro >> reverse conj_tac >- simp[] >>
  qexists_tac `t` >> simp[] >>
  `step_inst_base (mk_inst id ADD [Var root; Lit (n2w off)] [out]) s =
    OK (update_var out (a + n2w off) s)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_pure2_def, eval_operand_def]) >>
  gvs[run_inst_seq_def] >> irule point_offset_checked_cursors >>
  simp[] >> qexistsl [`capacity`, `n`] >> simp[]
QED

Theorem clean_word_load_trace_cursors:
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq [mk_inst id MLOAD [Var src] [tmp]] s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id MLOAD [Var src] [tmp]]
      (s with vs_inst_idx := k) G' tn') /\
    op_taint tn' (Var tmp) = {} /\
    lookup_var tmp t = SOME (mload (w2n a) s) /\
    t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!p. p <> tmp ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all clean_word_load_trace >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  qexistsl [`t`, `Gf`, `tnf`] >> simp[] >>
  irule singleton_cursor_intro >> reverse conj_tac >- simp[] >>
  qexists_tac `t` >> simp[] >>
  `step_inst_base (mk_inst id MLOAD [Var src] [tmp]) s =
    OK (update_var tmp (mload (w2n a) s) s)` by
    (pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  gvs[run_inst_seq_def] >> irule clean_word_load_checked_cursors >> simp[]
QED

Theorem clean_word_store_trace_cursors:
  ptr_covers G tn dst s 32 /\ op_taint tn v = {} /\
  ~ctx_has_dalloca ctx /\ lookup_var dst s = SOME a /\
  eval_operand v s = SOME w ==>
  ?t tn'.
    run_inst_seq [mk_inst id MSTORE [Var dst; v] []] s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id MSTORE [Var dst; v] []]
      (s with vs_inst_idx := k) G tn') /\
    t = mstore (w2n a) w s /\ tn'.t_var = tn.t_var /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}
Proof
  strip_tac >> drule_all clean_word_store_trace >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `t` (qx_choose_then `tnf` strip_assume_tac)) >>
  qexistsl [`t`, `tnf`] >> simp[] >>
  irule singleton_cursor_intro >> reverse conj_tac >- simp[] >>
  qexists_tac `mstore (w2n a) w s` >> simp[] >>
  drule_all mstore_ghost_frame >> strip_tac >>
  simp[] >> irule clean_word_store_checked_cursors >> simp[]
QED

Theorem allocated_buffer_checked_cursors:
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id ALLOCA [Lit (n2w n)] [out]] (s with vs_inst_idx := k)
    (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) t)
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn)
Proof
  strip_tac >> gen_tac >>
  `stmt_state_rel ctx fn cenv cx es (s with vs_inst_idx := k)` by
    simp[stmt_state_rel_inst_idx] >>
  `step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out])
      (s with vs_inst_idx := k) = OK (t with vs_inst_idx := k)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep, mk_inst_def,
         is_terminator_def, instIdxIndepTheory.exec_result_map_def] >>
  drule_all allocated_buffer_checked >> simp[]
QED

Theorem emitted_allocation_checked_cursors:
  compile_alloc_buffer n sa = (buf,sb) /\
  stmt_state_rel ctx fn cenv cx es s /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
        [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  n < dimword (:256) /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?out G' tn'. buf.buf_operand = Var out /\ not_fresh_at sb out /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) G' tn') /\
    ptr_covers G' tn' out t n
Proof
  strip_tac >> drule_all emitted_allocation_checked >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `out` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  qexistsl [`out`, `Gf`, `tnf`] >> simp[] >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]]` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
          emit_def, emitted_insts_def, DROP_APPEND1] >>
     strip_tac >> gvs[DROP_APPEND1]) >>
  gvs[] >> irule singleton_cursor_intro >> reverse conj_tac >- simp[] >>
  qexists_tac `t` >> simp[] >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    (Cases_on `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s` >>
     gvs[run_inst_seq_def]) >>
  irule allocated_buffer_checked_cursors >> metis_tac[]
QED
