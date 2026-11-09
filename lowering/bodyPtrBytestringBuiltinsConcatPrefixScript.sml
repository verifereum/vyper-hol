(* Counted scratch allocation and zero initialization for Concat. *)
Theory bodyPtrBytestringBuiltinsConcatPrefix
Ancestors
  bodyPtrBytestringBuiltinsBuffer bodyPtrBytestringBuiltinsAllocation
  bodyPtrPopMemoryStore loweringHalt bodyPtrIfExpAllocCompiler
  annAssignPtrAllocGhost annAssignPtrStore bodyPtrHashBuiltinsAllocFrame
  bodyPtrEnvBuiltinsScalar exprSimAlloc ghostPcTransportPtr
  bodyPtrAttributeAdd typedCopyPtr fragExec exprLoweringProps
  fragGasPathPtr fragGasSeqPtr loweringPosts bodyPtrDefs context emitHelper
  emitHelperProps compileEnv venomState venomInst venomExecSemantics
  ptrDiscipline words finite_map pred_set list

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
    ghost_inv d ce cx es G1 tn1 t /\ ghost_kept ce es sa G tn s G1 tn1
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
    metis_tac[annassign_alloca_ghost_inv_ptr] >>
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
  metis_tac[annassign_alloca_mstore_ghost_ptr]
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
      op_taint tn2 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all compile_slice_out_buf_counted >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `ghost_inv d ce cx es G2 tn2 t /\ ghost_kept ce es sa G tn s G2 tn2`
    by suspend "frame" >>
  qexistsl_tac [`r`,`p`,`a`,`G2`,`tn2`,`t`] >> simp[]
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
    metis_tac[annassign_alloca_ghost_inv_ptr] >>
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

Finalise concat_slice_out_buf_counted_frame
