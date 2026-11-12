(* Ghost frames for allocating hash prefixes and clean stores. *)
Theory bodyPtrHashBuiltinsAllocFrame
Ancestors wordLoadStorePtr bodyPtrHashBuiltinsGhostFrame bodyPtrHashBuiltinsKeccakFixed
  typedCopyPtr decoderGhostFramePtr exprSimAlloc allocationPtr
  bodyPtrDefs loweringHalt emitHelperProps exprLoweringProps compileEnv loweringStateRelDefs
  ptrDiscipline venomState venomInst finite_map pred_set

Theorem hash_clean_mstore_frame:
  !PG G tn s id p value a w d cenv cx es ctx fn sa.
    lookup_var p s = SOME a /\ eval_operand value s = SOME w /\
    op_taint tn value = {} /\ ghost_inv d cenv cx es G tn s /\
    stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!n b k i. local_region cenv es.scopes s n b k /\ b <= i /\ i < b+k ==>
      ~(w2n a <= i /\ i < w2n a + 32)) ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id MSTORE [Var p;value] []) (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var p;value] []) s (mstore (w2n a) w s) tn)
      (mstore (w2n a) w s) /\
    ghost_kept cenv es sa G tn s
      (step_prov PG G (mk_inst id MSTORE [Var p;value] []) (mstore (w2n a) w s))
      (step_taint (mk_inst id MSTORE [Var p;value] []) s (mstore (w2n a) w s) tn)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all mstore_ghost_frame >> strip_tac >>
  `!x. op_taint (step_taint (mk_inst id MSTORE [Var p;value] []) s
    (mstore (w2n a) w s) tn) (Var x) = op_taint tn (Var x)` by
    simp[op_taint_def] >>
  conj_tac >- suspend "invariant" >>
  irule hash_ghost_kept_frame >> simp[]
QED

Resume hash_clean_mstore_frame[invariant]:
  `stor_taint_ok cx (step_taint (mk_inst id MSTORE [Var p;value] []) s
    (mstore (w2n a) w s) tn) (mstore (w2n a) w s)` by
    (gvs[ghost_inv_def, stor_taint_ok_def, mstore_def, step_taint_def,
      imm_taint_def, adopt_reset_def, mk_inst_def]) >>
  irule hash_ghost_inv_exterior_frame >> simp[] >>
  qexistsl_tac [`G`, `ctx`, `fn`, `s`, `sa`, `tn`,
    `{i | w2n a <= i /\ i < w2n a+32}`] >>
  simp[lookup_var_def, mstore_def] >> suspend "frame"
QED

Resume hash_clean_mstore_frame[frame]:
  conj_tac >- metis_tac[] >>
  mp_tac (Q.SPECL [`s`, `w2n (a:bytes32)`, `w`] mstore_memory_frame) >>
  simp[mem_agree_outside_def, mstore_def]
QED

Finalise hash_clean_mstore_frame

Theorem hash_alloca_exterior_effects:
  !ctx fn cenv cx es s id n out s1 b PG G tn.
    stmt_state_rel ctx fn cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    FLOOKUP s1.vs_allocas id = SOME (b,n) ==>
    s1.vs_memory = s.vs_memory /\
    (!x. x <> out ==> lookup_var x s1 = lookup_var x s /\
      FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1) x = FLOOKUP G x /\
      op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) (Var x) =
        op_taint tn (Var x)) /\
    (!i. ~(b <= i /\ i < b+n) ==>
      (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem <=>
       i IN tn.t_mem)) /\
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem
      SUBSET tn.t_mem UNION {i | b <= i /\ i < b+n}
Proof
  rpt gen_tac >> strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >> strip_tac >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, FLOOKUP_UPDATE, lookup_var_def, op_taint_def] >>
      metis_tac[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> drule reused_alloca_ghost >> strip_tac >>
  gvs[update_var_def, FLOOKUP_UPDATE, lookup_var_def, op_taint_def] >>
  metis_tac[SUBSET_UNION]
QED

Theorem hash_alloca_old_operand:
  !ctx fn cenv cx es s id n out t b PG G tn value w.
    stmt_state_rel ctx fn cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
    FLOOKUP t.vs_allocas id = SOME (b,n) /\
    (!x. value = Var x ==> x <> out) /\
    eval_operand value s = SOME w /\ op_taint tn value = {} ==>
    eval_operand value t = SOME w /\
    op_taint (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn) value = {}
Proof
  rpt gen_tac >> strip_tac >> drule_all hash_alloca_exterior_effects >>
  disch_then (qspecl_then [`PG`, `G`, `tn`] strip_assume_tac) >>
  conj_tac >- metis_tac[alloca_step_operand_preserved] >>
  Cases_on `value` >> gvs[op_taint_def] >> metis_tac[]
QED

Theorem hash_alloca_step_frame:
  !ctx fn cenv cx es s id n out s1 b PG G tn d sa.
    stmt_state_rel ctx fn cenv cx es s /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
    n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    FLOOKUP s1.vs_allocas id = SOME (b,n) /\
    ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x. not_fresh_at sa x ==> x <> out) /\
    (!name off sz i. local_region cenv es.scopes s name off sz /\
      off <= i /\ i < off+sz ==> ~(b <= i /\ i < b+n)) /\
    (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
      aid < sa.cs_next_id /\ off <= i /\ i < off+sz ==> ~(b <= i /\ i < b+n)) ==>
    ghost_inv d cenv cx es
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) s1 /\
    ghost_kept cenv es sa G tn s
      (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) /\
    ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit (n2w n)] [out]) s1)
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn) out s1 n
Proof
  rpt gen_tac >> strip_tac >>
  drule_all hash_alloca_exterior_effects >> strip_tac >>
  `stor_taint_ok cx tn s` by metis_tac[ghost_inv_def] >>
  drule_all alloca_step_stor_taint_ok >> strip_tac >>
  conj_tac >- suspend "invariant" >>
  conj_tac >- (irule hash_ghost_kept_frame >> rpt conj_tac >>
    rpt strip_tac >> metis_tac[]) >>
  drule_all alloca_step_ptr_covers >> simp[]
QED

Resume hash_alloca_step_frame[invariant]:
  irule hash_ghost_inv_exterior_frame >> simp[] >>
  qexistsl_tac [`G`, `ctx`, `fn`, `s`, `sa`, `tn`, `{i | b <= i /\ i < b+n}`] >>
  simp[] >> rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

Finalise hash_alloca_step_frame

Theorem hash_literal_alloc_buffer_frame:
  !fn cenv cx es sa sm buf n s ctx d PG G tn.
    compile_alloc_buffer n sa = (buf,sm) /\
    stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sa /\ n < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
    ghost_inv d cenv cx es G tn s /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) ==>
    ?t w p G1 tn1.
      run_inst_seq (emitted_insts sa sm) s = OK t /\
      stmt_state_rel ctx fn cenv cx es t /\
      buf.buf_operand = Var p /\ eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
      w2n w+n < dimword (:256) /\ t.vs_memory = s.vs_memory /\
      sa.cs_next_id < sm.cs_next_id /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
        regions_disjoint (w2n w) n b k) /\
      (!name b k. local_region cenv es.scopes t name b k ==>
        regions_disjoint (w2n w) n b k) /\ not_fresh_at sm p /\
      G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [p]) t /\
      tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [p]) s t tn /\
      ghost_inv d cenv cx es G1 tn1 t /\ ghost_kept cenv es sa G tn s G1 tn1 /\
      ptr_covers G1 tn1 p t n
Proof
  rpt gen_tac >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]]` by suspend "shape" >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    (gvs[run_inst_seq_def, AllCaseEqs()]) >>
  qexistsl_tac [`t`, `w`, `STRING #"%" (toString sa.cs_next_var)`,
    `step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) t`,
    `step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) s t tn`] >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  irule hash_alloca_step_frame >> simp[] >> suspend "frame"
QED

Resume hash_literal_alloc_buffer_frame[shape]:
  drule compile_alloc_buffer_emission >> strip_tac >>
  drule emitted_insts_emit_inst >>
  simp[emitted_insts_def] >> strip_tac >> gvs[]
QED

Resume hash_literal_alloc_buffer_frame[frame]:
  `!name off sz. local_region cenv es.scopes s name off sz ==>
    local_region cenv es.scopes t name off sz` by
    (gvs[local_region_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  reverse conj_tac >- (qexistsl_tac [`ctx`, `fn`] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `local_region cenv es.scopes t name off sz` by metis_tac[] >>
      qpat_x_assum `!name b len. local_region cenv es.scopes t name b len ==> _`
        (drule_then mp_tac) >>
      simp[regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _`
    (drule_then mp_tac) >> simp[regions_disjoint_def] >> decide_tac
QED

Finalise hash_literal_alloc_buffer_frame

Theorem hash_ghost_kept_clean_tail:
  !cenv es sa G tn s G1 tn1 G2 tn2.
    ghost_kept cenv es sa G tn s G1 tn1 /\
    (!x. not_fresh_at sa x ==> FLOOKUP G2 x = FLOOKUP G1 x /\
      op_taint tn2 (Var x) = op_taint tn1 (Var x)) /\
    tn2.t_mem SUBSET tn1.t_mem ==>
    ghost_kept cenv es sa G tn s G2 tn2
Proof
  simp[ghost_kept_def, SUBSET_DEF] >> metis_tac[]
QED

Theorem hash_literal_alloc_store_frame:
  !fn cenv cx es sa sm buf s ctx d PG G tn sid value v.
    compile_alloc_buffer 32 sa = (buf,sm) /\
    stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sa /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
    ghost_inv d cenv cx es G tn s /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x. value = Var x ==> not_fresh_at sa x) /\
    eval_operand value s = SOME v /\ op_taint tn value = {} ==>
    ?t a p G1 tn1 G2 tn2.
      run_inst_seq (emitted_insts sa sm) s = OK t /\
      buf.buf_operand = Var p /\ lookup_var p t = SOME a /\
      p = STRING #"%" (toString sa.cs_next_var) /\
      step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) s = OK t /\
      eval_operand value t = SOME v /\ op_taint tn1 value = {} /\
      G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) t /\
      tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) s t tn /\
      G2 = step_prov PG G1 (mk_inst sid MSTORE [Var p;value] []) (mstore (w2n a) v t) /\
      tn2 = step_taint (mk_inst sid MSTORE [Var p;value] []) t (mstore (w2n a) v t) tn1 /\
      stmt_state_rel ctx fn cenv cx es (mstore (w2n a) v t) /\
      ghost_inv d cenv cx es G2 tn2 (mstore (w2n a) v t) /\
      ghost_kept cenv es sa G tn s G2 tn2 /\
      ptr_covers G2 tn2 p (mstore (w2n a) v t) 32 /\
      (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn2.t_mem) /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n a,32) /\
      w2n a+32 < dimword (:256) /\ not_fresh_at sm p /\
      ptr_covers G1 tn1 p t 32 /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  rpt gen_tac >> strip_tac >>
  `32 < dimword (:256)` by
    simp[wordsTheory.dimword_def, fcpTheory.index_bit0, fcpTheory.finite_bit0,
      fcpTheory.index_one, fcpTheory.finite_one] >>
  drule_all hash_literal_alloc_buffer_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `lookup_var p t = SOME w` by gvs[eval_operand_def] >>
  `emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]]` by
    (drule compile_alloc_buffer_emission >> strip_tac >>
     drule emitted_insts_emit_inst >> simp[emitted_insts_def] >> strip_tac >> gvs[]) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `eval_operand value t = SOME v /\ op_taint tn1 value = {}` by
    (qpat_x_assum `tn1 = _` (fn th => rewrite_tac[th]) >>
     irule hash_alloca_old_operand >>
     gvs[] >> metis_tac[]) >>
  qexistsl_tac [`t`, `w`, `p`, `G1`, `tn1`,
    `step_prov PG G1 (mk_inst sid MSTORE [Var p;value] []) (mstore (w2n w) v t)`,
    `step_taint (mk_inst sid MSTORE [Var p;value] []) t (mstore (w2n w) v t) tn1`] >>
  simp[] >> suspend "post"
QED

Resume hash_literal_alloc_store_frame[post]:
  `STRING #"%" (toString sa.cs_next_var) = p` by gvs[] >>
  qpat_x_assum `G1 = _` (fn th => rewrite_tac[GSYM th] >> assume_tac th) >>
  qpat_x_assum `tn1 = _` (fn th => rewrite_tac[GSYM th] >> assume_tac th) >>
  simp[] >>
  `!name b k i. local_region cenv es.scopes t name b k /\ b <= i /\ i < b+k ==>
    ~(w2n w <= i /\ i < w2n w+32)` by
    (rpt strip_tac >>
     qpat_x_assum `!name b k. local_region cenv es.scopes t name b k ==> _`
       (drule_then mp_tac) >> simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac >- suspend "state" >>
  conj_tac >- (drule_all hash_clean_mstore_frame >>
    disch_then (qspecl_then [`PG`, `sid`] mp_tac) >> simp[]) >>
  conj_tac >- suspend "kept" >>
  irule hash_store_covered_clean >> gvs[]
QED

Resume hash_literal_alloc_store_frame[kept]:
  qpat_x_assum `G1 = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `tn1 = _` (fn th => rewrite_tac[GSYM th]) >>
  drule_all mstore_ghost_frame >> strip_tac >>
  irule hash_ghost_kept_clean_tail >>
  qexistsl_tac [`G1`, `tn1`] >> simp[op_taint_def]
QED

Resume hash_literal_alloc_store_frame[state]:
  irule literal_mstore_state_rel >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`w2n w`,
    `mk_inst sa.cs_next_id ALLOCA [Lit 32w] [p]`, `32`] >>
  conj_tac >- (rpt strip_tac >> fs[regions_disjoint_def] >> metis_tac[]) >>
  gvs[mk_inst_def]
QED

Finalise hash_literal_alloc_store_frame
