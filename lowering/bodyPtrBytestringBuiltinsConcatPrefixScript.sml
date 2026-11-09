(* Counted scratch allocation and zero initialization for Concat. *)
Theory bodyPtrBytestringBuiltinsConcatPrefix
Ancestors
  bodyPtrBytestringBuiltinsBuffer bodyPtrBytestringBuiltinsAllocation
  bodyPtrPopMemoryStore loweringHalt bodyPtrIfExpAllocCompiler
  annAssignPtrAllocGhost annAssignPtrStore bodyPtrHashBuiltinsAllocFrame
  bodyPtrEnvBuiltinsScalar bodyPtrIfExpAllocSource exprSimAlloc ghostPcTransportPtr
  bodyPtrAttributeAdd typedCopyPtr fragExec exprLoweringProps exprSimLiteralBuffer
  fragGasPathPtr fragGasSeqPtr loweringPosts bodyPtrDefs context emitHelper
  emitHelperProps compileEnv venomState venomInst venomExecSemantics
  ptrDiscipline words finite_map pred_set list

Theorem concat_alloc_raw_frame:
  compile_alloc_buffer n sa = (buf,sm) /\ buf.buf_operand = Var out /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ n < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn) /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK u ==>
  ?w. lookup_var out u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
    w2n w+n < dimword (:256) /\ u.vs_memory = s.vs_memory /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
      regions_disjoint (w2n w) n b k) /\
    (!name b k. local_region ce es.scopes u name b k ==>
      regions_disjoint (w2n w) n b k)
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)` by gvs[] >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  `emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]]` by
    (drule compile_alloc_buffer_emission >> strip_tac >>
     drule emitted_insts_emit_inst >> simp[emitted_insts_def] >> strip_tac >> gvs[]) >>
  gvs[run_inst_seq_def, eval_operand_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem concat_alloc_zero_counted:
  compile_alloc_buffer n sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand; Lit 0w] sm = ((),sb) /\
  fn_has_code sa sm fn /\ fn_has_code sm sb fn /\
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ 32 <= n /\ n < dimword (:256) /\
  ghost_inv d ce cx es G tn s /\
  (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out G1 tn1 t a.
    buf.buf_operand = Var out /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t) /\
    ptr_covers G1 tn1 out t n /\ lookup_var out t = SOME a /\
    mload (w2n a) t = 0w /\
    (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn1.t_mem) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)) /\
    (!x k. not_fresh_at sa x /\ ptr_covers G tn x s k ==>
      ptr_covers G1 tn1 x t k) /\
    stmt_state_rel ctx fn ce cx es t /\
    ghost_inv d ce cx es G1 tn1 t /\ ghost_kept ce es sa G tn s G1 tn1 /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n a,n) /\
    w2n a+n < dimword (:256) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
      regions_disjoint (w2n a) n b k) /\
    (!name b k. local_region ce es.scopes t name b k ==>
      regions_disjoint (w2n a) n b k) /\
    (!name b k. local_region ce es.scopes s name b k <=>
      local_region ce es.scopes t name b k)
Proof
  strip_tac >> drule_all bodyPtrBytestringBuiltinsBufferTheory.compile_alloc_buffer_counted >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
     strip_tac >> gvs[update_var_def]) >>
  `sm.cs_current_bb = sa.cs_current_bb /\
   LENGTH sm.cs_current_insts = LENGTH sa.cs_current_insts + 1` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `ptr_covers G1 tn1 out uh n` >>
  `~uh.vs_halted /\ uh.vs_current_bb = sm.cs_current_bb /\
   uh.vs_inst_idx = LENGTH sm.cs_current_insts /\
   lookup_var out uh = SOME (n2w a) /\ ptr_covers G1 tn1 out uh 32` by
    (gvs[Abbr `uh`, lookup_var_def, ptr_covers_def] >> decide_tac) >>
  `eval_operand (Lit 0w) uh = SOME 0w /\ op_taint tn1 (Lit 0w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  `emit_void MSTORE [Var out; Lit 0w] sm = ((),sb)` by metis_tac[] >>
  drule_all pop_emit_mstore_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn' (OK t)` by
    (drule_at (Pat `gas_path_ptr_edge _ _ _ _ _ G tn s _ _ _ _`)
       (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[]) >>
  `ptr_covers G1 tn' out t n` by
    gvs[ptr_covers_def, op_taint_def] >>
  suspend "finish"
QED

Resume concat_alloc_zero_counted[finish]:
  `!x. not_fresh_at sa x ==> x <> out` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)` by
    (rpt gen_tac >> disch_tac >> `x <> out` by simp[] >>
     `op_taint tn' (Var x) = op_taint tn1 (Var x)` by simp[op_taint_def] >>
     `FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)` by
       simp[alloca_old_register_ghost_frame] >>
     gvs[Abbr `uh`, lookup_var_def]) >>
  `!x k. not_fresh_at sa x /\ ptr_covers G tn x s k ==>
    ptr_covers G1 tn' x t k` by
    (rpt strip_tac >> gvs[ptr_covers_def]) >>
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (a,n) /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP t.vs_allocas aid = SOME entry) /\
   (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
     regions_disjoint a n b k) /\
   (!name b k. local_region ce es.scopes t name b k ==> regions_disjoint a n b k)`
    by suspend "sites" >>
  `!name b k. local_region ce es.scopes s name b k <=>
     local_region ce es.scopes t name b k` by
    (simp[local_region_def] >> rpt gen_tac >>
     `!p sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
        lookup_var p t = lookup_var p s` by
       (rpt strip_tac >> `not_fresh_at sa p` by
          (fs[local_ptrs_reserved_def] >> metis_tac[]) >> simp[]) >>
     metis_tac[]) >>
  qexistsl_tac [`out`,`G1`,`tn'`,`t`,`n2w a`] >> simp[] >>
  `!ss z k. mload z (ss with vs_inst_idx := k) = mload z ss` by
    simp[mload_def] >>
  simp[venomMemProofsTheory.mload_mstore_same_proof] >>
  suspend "ghost"
QED

Resume concat_alloc_zero_counted[ghost]:
  `sa.cs_next_var <= sa.cs_next_var` by simp[] >>
  drule_all compile_alloc_buffer_frame_separation >>
  disch_then (qspec_then `es.scopes` strip_assume_tac) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn)` by
    (drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[]) >>
  `ghost_inv d ce cx es G1 tn1 u` by
    (qpat_assum `G1 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `tn1 = _` (fn th => rewrite_tac[th]) >>
     irule annassign_alloca_ghost_inv_ptr >> simp[] >> metis_tac[]) >>
  `ghost_kept ce es sa G tn s G1 tn1` by
    metis_tac[annassign_alloca_ghost_kept_ptr] >>
  suspend "store_frame"
QED

Resume concat_alloc_zero_counted[store_frame]:
  qpat_assum `G1 = _` (fn th => rewrite_tac[GSYM th]) >>
  `a < dimword (:256)` by decide_tac >>
  `tn' = tn1 with t_mem := tn1.t_mem DIFF {i | a <= i /\ i < a+32}` by
    simp[taint_component_equality, w2n_n2w] >>
  simp[Abbr `uh`, exprPtrUnwrapFramesTheory.copy_mstore_inst_idx,
       exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
  conj_tac >- suspend "state" >>
  conj_tac >- suspend "inv" >>
  reverse conj_tac >-
    (conj_tac >- metis_tac[] >>
     simp[local_region_def, lookup_var_def, mstore_def] >>
     qpat_x_assum `!name b len. local_region ce es.scopes u name b len ==> _`
       mp_tac >> simp[local_region_def, lookup_var_def]) >>
  irule hash_ghost_kept_clean_tail >> qexistsl_tac [`G1`,`tn1`] >>
  simp[op_taint_def, SUBSET_DEF] >> gvs[]
QED

Resume concat_alloc_zero_counted[state]:
  irule literal_mstore_state_rel >> simp[] >>
  qexistsl_tac [`a`,`mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]`,`n`] >>
  simp[mk_inst_def] >> rpt strip_tac >>
  fs[regions_disjoint_def] >> metis_tac[]
QED

Resume concat_alloc_zero_counted[inv]:
  `w2n (n2w a : 256 word) = a` by simp[w2n_n2w] >>
  qpat_assum `G1 = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_assum `tn1 = _` (fn th => rewrite_tac[GSYM th]) >>
  `FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n (n2w a : 256 word),n)` by simp[] >>
  `(mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]).inst_opcode = ALLOCA /\
   (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]).inst_outputs = [out]` by
    simp[mk_inst_def] >>
  `(mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]).inst_id = sa.cs_next_id` by
    simp[mk_inst_def] >>
  qpat_assum `w2n (n2w a : 256 word) = a`
    (fn th => pure_once_rewrite_tac[GSYM th]) >>
  irule annassign_alloca_mstore_ghost_ptr >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`ctx`,`fn`,
    `mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]`,`out`,`n`] >> simp[]
QED

Resume concat_alloc_zero_counted[sites]:
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [out]) (fn_insts fn)` by
    (drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[]) >>
  drule_all concat_alloc_raw_frame >> strip_tac >>
  `!name b k. local_region ce es.scopes t name b k ==>
    local_region ce es.scopes u name b k` by
    (simp[local_region_def, Abbr `uh`, lookup_var_def]) >>
  gvs[Abbr `uh`, mstore_def, lookup_var_def] >> metis_tac[]
QED

Finalise concat_alloc_zero_counted

Theorem concat_slice_out_buf_counted_frame:
  compile_slice_out_buf n sa = ((root,data),sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn ce cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved ce sa /\
  32 <= n /\ n < dimword (:256) /\ ghost_inv d ce cx es G tn s /\
  (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r p a G2 tn2 t.
    root = Var r /\ data = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2 (OK t) /\
    ptr_covers G2 tn2 r t n /\ ptr_covers G2 tn2 p t (n-32) /\
    lookup_var r t = SOME a /\ lookup_var p t = SOME (a+32w) /\
    stmt_state_rel ctx fn ce cx es t /\ ghost_inv d ce cx es G2 tn2 t /\
    ghost_kept ce es sa G tn s G2 tn2 /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
      op_taint tn2 (Var x) = op_taint tn (Var x)) /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n a,n) /\
    w2n a+n < dimword (:256) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
      regions_disjoint (w2n a) n b k) /\
    (!name b k. local_region ce es.scopes t name b k ==>
      regions_disjoint (w2n a) n b k) /\
    (!name b k. local_region ce es.scopes s name b k <=>
      local_region ce es.scopes t name b k)
Proof
  strip_tac >> drule_all compile_slice_out_buf_counted >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `ghost_inv d ce cx es G2 tn2 t /\ ghost_kept ce es sa G tn s G2 tn2`
    by suspend "frame" >>
  `!name b k. local_region ce es.scopes s name b k <=>
    local_region ce es.scopes t name b k` by
    (simp[local_region_def] >> rpt gen_tac >>
     `!q sz. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var q) sz) ==>
        lookup_var q t = lookup_var q s` by
       (rpt strip_tac >> `not_fresh_at sa q` by
          (fs[local_ptrs_reserved_def] >> metis_tac[]) >> simp[]) >>
     metis_tac[]) >>
  qexistsl_tac [`r`,`p`,`a`,`G2`,`tn2`,`t`] >> simp[] >>
  suspend "sites"
QED

Resume concat_slice_out_buf_counted_frame[frame]:
  `fn_has_code sa sm fn` by
    (drule compile_slice_out_buf_compiler_parts >> strip_tac >> gvs[] >>
     drule_all fn_has_code_split >> simp[]) >>
  `sa.cs_next_var <= sa.cs_next_var` by simp[] >>
  drule_all compile_alloc_buffer_frame_separation >>
  disch_then (qspec_then `es.scopes` strip_assume_tac) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [r]) (fn_insts fn)` by
    (drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[]) >>
  `ghost_inv d ce cx es G1 tn1 u` by
    (qpat_assum `G1 = _` (fn th => rewrite_tac[th]) >>
     qpat_assum `tn1 = _` (fn th => rewrite_tac[th]) >>
     irule annassign_alloca_ghost_inv_ptr >> simp[] >> metis_tac[]) >>
  `ghost_kept ce es sa G tn s G1 tn1` by
    metis_tac[annassign_alloca_ghost_kept_ptr] >>
  `!x. not_fresh_at sa x ==> x <> p` by suspend "fresh" >>
  `tn2.t_mem = tn1.t_mem` by simp[copy_len_binop_ghost_frame] >>
  conj_tac >- suspend "inv" >>
  irule hash_ghost_kept_clean_tail >> qexistsl_tac [`G1`,`tn1`] >> simp[] >>
  rpt strip_tac >> simp[copy_len_binop_ghost_frame, alloca_old_register_ghost_frame]
QED

Resume concat_slice_out_buf_counted_frame[fresh]:
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Resume concat_slice_out_buf_counted_frame[inv]:
  qpat_assum `t = _` (fn th => rewrite_tac[th]) >>
  `!name x k. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var x) k) ==>
    x <> p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `(!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> x <> p) /\
   (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> x <> p)` by metis_tac[] >>
  irule attribute_ghost_inv_update >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`G1`,`tn1`] >>
  simp[copy_len_binop_ghost_frame] >>
  simp[step_taint_def, mk_inst_def, store_taint_def, adopt_reset_def, imm_taint_def]
QED

Resume concat_slice_out_buf_counted_frame[sites]:
  `fn_has_code sa sm fn` by
    (drule compile_slice_out_buf_compiler_parts >> strip_tac >> gvs[] >>
     drule_all fn_has_code_split >> simp[]) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [r]) (fn_insts fn)` by
    (drule_all compile_alloc_buffer_raw_step >> strip_tac >> gvs[]) >>
  drule_all compile_alloc_buffer_raw_resources >> strip_tac >>
  drule_all concat_alloc_raw_frame >> strip_tac >>
  `!name b k. local_region ce es.scopes t name b k ==>
    local_region ce es.scopes u name b k` by
    (simp[local_region_def] >> rpt strip_tac >>
     `not_fresh_at sa p'` by
       (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     `lookup_var p' u = lookup_var p' s /\ lookup_var p' t = lookup_var p' s`
       by simp[] >> metis_tac[]) >>
  gvs[update_var_def] >> metis_tac[]
QED

Finalise concat_slice_out_buf_counted_frame

Theorem concat_prefix_counted:
  compile_alloc_buffer bsz sa = (buf,s1) /\
  emit_op ADD [buf.buf_operand; Lit 32w] s1 = (data,s2) /\
  compile_alloc_buffer 64 s2 = (ob,s3) /\
  emit_void MSTORE [ob.buf_operand; Lit 0w] s3 = ((),s4) /\
  fn_has_code sa s4 fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved ce sa /\ 32 <= bsz /\ bsz < dimword (:256) /\
  stmt_state_rel ctx fn ce cx es s /\ ghost_inv d ce cx es G tn s /\
  (!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r p off a ow Gf tnf t.
    buf.buf_operand = Var r /\ data = Var p /\ ob.buf_operand = Var off /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    stmt_state_rel ctx fn ce cx es t /\ ghost_inv d ce cx es Gf tnf t /\
    ghost_kept ce es sa G tn s Gf tnf /\
    ptr_covers Gf tnf r t bsz /\ ptr_covers Gf tnf p t (bsz-32) /\
    ptr_covers Gf tnf off t 64 /\
    lookup_var r t = SOME a /\ lookup_var p t = SOME (a+32w) /\
    lookup_var off t = SOME ow /\ mload (w2n ow) t = 0w /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tnf.t_mem) /\
    ~t.vs_halted /\ t.vs_current_bb = s4.cs_current_bb /\
    t.vs_inst_idx = LENGTH s4.cs_current_insts /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n a,bsz) /\
    FLOOKUP t.vs_allocas s2.cs_next_id = SOME (w2n ow,64) /\
    w2n a+bsz < dimword (:256) /\ w2n ow+64 < dimword (:256) /\
    regions_disjoint (w2n ow) 64 (w2n a) bsz /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
      regions_disjoint (w2n a) bsz b k /\ regions_disjoint (w2n ow) 64 b k) /\
    (!name b k. local_region ce es.scopes t name b k ==>
      regions_disjoint (w2n a) bsz b k /\ regions_disjoint (w2n ow) 64 b k) /\
    (!name b k. local_region ce es.scopes s name b k <=>
      local_region ce es.scopes t name b k) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `compile_slice_out_buf bsz sa = ((buf.buf_operand,data),s2)` by
    simp[builtinBytesTheory.compile_slice_out_buf_def, comp_bind_def, comp_return_def] >>
  drule compile_slice_out_buf_compiler_parts >> strip_tac >>
  `cs_extends sa s2` by metis_tac[cs_extends_trans] >>
  `cs_extends s2 s3` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends s3 s4` by
    (irule cs_extends_emit_inst >>
     qexistsl_tac [`MSTORE`,`[ob.buf_operand; Lit 0w]`,`[]`,`()`] >>
     simp[emit_inst_def, GSYM emit_void_def]) >>
  `cs_extends s2 s4` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s2 fn /\ fn_has_code s2 s4 fn` by metis_tac[fn_has_code_split] >>
  `fn_has_code s2 s3 fn /\ fn_has_code s3 s4 fn` by metis_tac[fn_has_code_split] >>
  drule_all concat_slice_out_buf_counted_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by
    (mp_tac (ci_mono_compile_slice_out_buf |> Q.SPECL [`bsz`,`sa`]) >>
     simp[ci_mono_def]) >>
  `local_ptrs_reserved ce s2` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at sa x ==> not_fresh_at s2 x` by
    (simp[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `(!x k. ce.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at s2 x) /\
   (!x k. ce.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at s2 x)` by metis_tac[] >>
  `32 <= 64 /\ 64 < dimword (:256)` by
    (conj_tac >- decide_tac >> irule vyperArithTheory.lt_dimword_256 >>
     qexists_tac `7` >> simp[]) >>
  qpat_x_assum `compile_alloc_buffer 64 s2 = _` assume_tac >>
  drule_all concat_alloc_zero_counted >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "assemble"
QED

Resume concat_prefix_counted[assemble]:
  `r' = r /\ p' = p` by metis_tac[operand_11] >>
  gvs[] >>
  `not_fresh_at s2 r /\ not_fresh_at s2 p /\ sa.cs_next_id < s2.cs_next_id` by
    (qpat_x_assum `compile_alloc_buffer bsz sa = _` assume_tac >>
     drule compile_alloc_buffer_parts >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     gvs[not_fresh_at_def] >> rpt strip_tac >>
     gvs[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK t')` by
    (drule_all gas_path_ptr_then >> simp[]) >>
  `ptr_covers G1 tn1 r t' bsz /\ ptr_covers G1 tn1 p t' (bsz-32)` by
    (conj_tac >> first_x_assum irule >> simp[]) >>
  `lookup_var r t' = SOME a /\ lookup_var p t' = SOME (a+32w)` by simp[] >>
  qexistsl_tac [`a`,`a'`,`G1`,`tn1`,`t'`] >>
  simp[] >> conj_tac >- suspend "kept" >>
  suspend "frames"
QED

Resume concat_prefix_counted[frames]:
  conj_tac >-
    (qpat_x_assum `!aid b k. aid < s2.cs_next_id /\ _ ==> _`
       irule >> qexists_tac `sa.cs_next_id` >> simp[]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> conj_tac >- metis_tac[] >>
     qpat_x_assum `!aid b k. aid < s2.cs_next_id /\ _ ==> _` irule >>
     qexists_tac `aid` >> simp[] >> decide_tac) >>
  metis_tac[]
QED

Resume concat_prefix_counted[kept]:
  gvs[ghost_kept_def] >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `aid < s2.cs_next_id` by decide_tac >>
     `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by simp[] >>
     `i IN tn2.t_mem` by
       (qpat_x_assum `!aid off sz i. FLOOKUP t.vs_allocas aid = _ /\ _ ==> _`
          irule >> simp[] >> qexistsl_tac [`aid`,`off`,`sz`] >> metis_tac[]) >>
     qpat_x_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _`
       irule >> simp[] >> qexistsl_tac [`aid`,`off`,`sz`] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  `i IN tn2.t_mem` by metis_tac[] >>
  metis_tac[]
QED

Finalise concat_prefix_counted
