Theory bodyPtrCodeSliceExternalContinue
Ancestors
  bodyPtrCodeSliceExternalCopy bodyPtrCodeSliceExternalBounds
  bodyPtrCodeSliceExternalAddress bodyPtrCodeSliceSelfSuffix
  exprSimSliceExtcode exprSimSliceExtcodeContinue exprSimSliceExtcodeEntry
  bodyPtrDefs fragExecPtr fragGasSeqPtr ptrDiscipline ptrSafeRun
  emitHelperProps exprLoweringProps compileEnv loweringPosts venomState venomInst
  venomExecSemantics words list rich_list finite_map pred_set
  exprSimPtrLiteralBuffer bodyPtrCodeSliceSelfOperands
  instSeqComposePtr bodyPtrCodeSliceSelfContinue
  bodyPtrHashBuiltinsGhostFrame loweringStateRelDefs
  bodyPtrCodeSliceSelfPrefix exprSimHashBoundary wordArgsPtr

Theorem external_code_copy_store_emitted_ptr:
  emit_void EXTCODECOPY [addr;Var dst;src;len] sa = ((),sb) /\
  emit_void MSTORE [Var out;len] sb = ((),sc) /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn out s 32 /\
  eval_operand addr s = SOME av /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  lookup_var out s = SOME p /\ lookup_var dst s = SOME (p+32w) /\
  w2n p+32 < dimword (:256) /\
  w2n a+w2n n <= LENGTH (lookup_account (w2w av) s.vs_accounts).code /\
  op_taint tn addr = {} /\ op_taint tn src = {} /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx /\ ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!name off sz. local_region cenv es.scopes s name off sz ==>
    off+sz <= w2n p \/ w2n p+32+w2n n <= off) ==>
  ?t tn'. run_inst_seq (emitted_insts sa sc) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc) s G tn' /\
    ghost_inv d cenv cx es G tn' t /\ ghost_kept cenv es sa G tn s G tn' /\
    tn' = (tn with t_mem := (tn.t_mem DIFF
      {j | w2n p+32 <= j /\ j < w2n p+32+w2n n}) DIFF
      {j | w2n p <= j /\ j < w2n p+32}) /\
    t = mstore (w2n p) n (write_memory_with_expansion (w2n p+32)
      (TAKE (w2n n) (DROP (w2n a)
        (lookup_account (w2w av) s.vs_accounts).code)) s)
Proof
  strip_tac >>
  `w2n (p+32w) = w2n p+32` by
    (simp[word_add_def, w2n_n2w] >> irule arithmeticTheory.LESS_MOD >> simp[]) >>
  qabbrev_tac `bs = TAKE (w2n n) (DROP (w2n a)
    (lookup_account (w2w av) s.vs_accounts).code)` >>
  `LENGTH bs = w2n n` by simp[Abbr `bs`] >>
  `step_inst_base (mk_inst sa.cs_next_id EXTCODECOPY [addr;Var dst;src;len] []) s =
    OK (write_memory_with_expansion (w2n p+32) bs s)` by
    (qpat_x_assum `w2n (p+32w) = _`
       (fn th => once_rewrite_tac[GSYM th]) >>
     simp[Abbr `bs`] >> irule slice_extcodecopy_step >>
     simp[eval_operand_def]) >>
  `inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst sa.cs_next_id EXTCODECOPY [addr;Var dst;src;len] [];
     mk_inst sb.cs_next_id MSTORE [Var out;len] []] s G
    (tn with t_mem := (tn.t_mem DIFF
      {j | w2n p+32 <= j /\ j < w2n p+32+w2n n}) DIFF
      {j | w2n p <= j /\ j < w2n p+32})` by
    (drule_all external_code_copy_store_checked >> simp[] >>
     disch_then (qspecl_then [`D`,`fn`,`sb.cs_next_id`] mp_tac) >> simp[]) >>
  `emitted_insts sa sc =
    [mk_inst sa.cs_next_id EXTCODECOPY [addr;Var dst;src;len] [];
     mk_inst sb.cs_next_id MSTORE [Var out;len] []]` by
    (drule_all emitted_insts_emit_void >> strip_tac >>
     drule_all emit_void_extends >> strip_tac >>
     `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
       (irule emitted_insts_append >> metis_tac[emit_void_extends]) >>
     metis_tac[emitted_insts_emit_void, APPEND]) >>
  qexistsl_tac [`mstore (w2n p) n (write_memory_with_expansion (w2n p+32) bs s)`,
    `tn with t_mem := (tn.t_mem DIFF
      {j | w2n p+32 <= j /\ j < w2n p+32+w2n n}) DIFF
      {j | w2n p <= j /\ j < w2n p+32}`] >> simp[] >>
  conj_tac >-
    (Cases_on `len` >> gvs[run_inst_seq_def, mk_inst_def, is_terminator_def,
      step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def,
      lookup_var_def, write_memory_with_expansion_def]) >>
  conj_tac >- gvs[] >>
  conj_tac >-
    (`ghost_inv d cenv cx es G
       (tn with t_mem := (tn.t_mem DIFF
         {j | w2n p+32 <= j /\ j < w2n p+32+LENGTH bs}) DIFF
         {j | w2n p <= j /\ j < w2n p+32})
       (mstore (w2n p) n (write_memory_with_expansion (w2n p+32) bs s))` by
       (irule self_code_copy_store_ghost_frame >>
        metis_tac[]) >> gvs[]) >>
  irule literal_ghost_kept >> simp[op_taint_def, SUBSET_DEF]
QED

Theorem external_code_copy_store_uniform_ptr:
  emit_void EXTCODECOPY [addr;Var dst;src;len] sa = ((),sb) /\
  emit_void MSTORE [Var out;len] sb = ((),sc) /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn out s 32 /\
  eval_operand addr s = SOME av /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  lookup_var out s = SOME p /\ lookup_var dst s = SOME (p+32w) /\
  w2n p+32 < dimword (:256) /\
  w2n a+w2n n <= LENGTH (lookup_account (w2w av) s.vs_accounts).code /\
  op_taint tn addr = {} /\ op_taint tn src = {} /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx /\ ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!name off sz. local_region cenv es.scopes s name off sz ==>
    off+sz <= w2n p \/ w2n p+32+w2n n <= off) ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc)
    (s with vs_inst_idx := k) G
    (tn with t_mem := (tn.t_mem DIFF
      {j | w2n p+32 <= j /\ j < w2n p+32+w2n n}) DIFF
      {j | w2n p <= j /\ j < w2n p+32})
Proof
  strip_tac >> gen_tac >>
  mp_tac (Q.INST [`s` |-> `s with vs_inst_idx := k`]
    external_code_copy_store_emitted_ptr) >>
  impl_tac
  >- (fs[lookup_var_def] >>
      simp[hash_ghost_inv_inst_idx, stmt_state_rel_inst_idx, lookup_var_def] >>
      rpt strip_tac >> first_x_assum irule >>
      fs[local_region_def, eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  strip_tac >> gvs[]
QED

(* Attach the checked write and located-value view to the semantic suffix.
   The semantic view is supplied by slice_extcode_tail_vv_post, not a lift
   from expr_sim to the pointer judgment. *)
Theorem external_code_copy_store_result_ptr:
  emit_void EXTCODECOPY [addr;Var dst;src;len] sa = ((),sb) /\
  emit_void MSTORE [Var out;len] sb = ((),sc) /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn out s sz /\ 32 <= sz /\
  eval_operand addr s = SOME av /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  lookup_var out s = SOME p /\ lookup_var dst s = SOME (p+32w) /\
  w2n p+32 < dimword (:256) /\
  w2n a+w2n n <= LENGTH (lookup_account (w2w av) s.vs_accounts).code /\
  op_taint tn addr = {} /\ op_taint tn src = {} /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx /\ ghost_inv d cenv cx es G tn s /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!name off cap. local_region cenv es.scopes s name off cap ==>
    off+cap <= w2n p \/ w2n p+32+w2n n <= off) /\
  run_inst_seq (emitted_insts sa sc) s = OK z /\
  evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic bound))) /\
  vv_holds cenv cx ty
    (Value (BytesV (TAKE (w2n n) (DROP (w2n a)
      (lookup_account (w2w av) s.vs_accounts).code))))
    (LocatedValue ty (mk_ptr (Var out) LocMemory)) es z /\
  val_wf (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE (w2n n) (DROP (w2n a)
      (lookup_account (w2w av) s.vs_accounts).code))) /\
  val_store_size (BaseTV (BytesT (Dynamic bound)))
    (BytesV (TAKE (w2n n) (DROP (w2n a)
      (lookup_account (w2w av) s.vs_accounts).code))) <= sz /\
  type_memory_bytes cenv (lowered_value_type cenv e) <= sz ==>
  ?tn'. (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc)
      (s with vs_inst_idx := k) G tn') /\
    ghost_inv d cenv cx es G tn' z /\ ghost_kept cenv es sa G tn s G tn' /\
    ptr_vv_ok cx ty
      (Value (BytesV (TAKE (w2n n) (DROP (w2n a)
        (lookup_account (w2w av) s.vs_accounts).code))))
      (LocatedValue ty (mk_ptr (Var out) LocMemory)) es G tn' z /\
    ptr_buf_ok cenv e (Var out) G z
Proof
  strip_tac >>
  `ptr_covers G tn out s 32` by
    (fs[ptr_covers_def] >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all external_code_copy_store_uniform_ptr >>
  disch_then (qspecl_then [`PG`,`D`] assume_tac) >>
  drule_all external_code_copy_store_emitted_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `z = t` by gvs[] >>
  qexists_tac `tn'` >> gvs[] >>
  irule self_code_covered_result >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`bound`,`p`,`sz`,`tn`] >>
  `LENGTH (TAKE (w2n n) (DROP (w2n a)
    (lookup_account (w2w av) s.vs_accounts).code)) = w2n n` by simp[] >>
  simp[] >>
  qpat_x_assum `ptr_covers G tn out s sz` mp_tac >>
  simp[NoAsms, ptr_covers_def, mstore_def,
    write_memory_with_expansion_def, lookup_var_def]
QED

Theorem external_code_prefix_success_frame:
  emit_op EXTCODESIZE [addr] sa = (limit,sb) /\
  compile_assert_slice_bounds src len limit sb = ((),sc) /\
  eval_operand addr s = SOME av /\ op_taint tn addr = {} /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  op_taint tn src = {} /\ op_taint tn len = {} /\
  op_prov G src = NONE /\ op_prov G len = NONE /\
  (!z. src = Var z ==> not_fresh_at sa z) /\
  (!z. len = Var z ==> not_fresh_at sa z) /\ ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sb ++ emitted_insts sb sc) s = OK t /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!p j. cenv.ce_return_buf = SOME (PtrVar (Var p) j) ==> not_fresh_at sa p) /\
  (!p j. cenv.ce_return_pc = SOME (PtrVar (Var p) j) ==> not_fresh_at sa p) ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sa sb ++ emitted_insts sb sc) s Gf tnf /\
    ghost_inv d cenv cx es Gf tnf t /\ ghost_kept cenv es sa G tn s Gf tnf /\
    (!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
      eval_operand op t = eval_operand op s /\
      op_prov Gf op = op_prov G op /\ op_taint tnf op = op_taint tn op) /\
    (!p sz. not_fresh_at sa p /\ ptr_covers G tn p s sz ==>
      ptr_covers Gf tnf p t sz)
Proof
  strip_tac >> drule_all external_code_size_bounds_checked >>
  disch_then (qspecl_then [`D`,`fn`,`PG`] strip_assume_tac) >>
  drule_all external_code_size_bounds_frame >> strip_tac >>
  qexistsl_tac [`Gf`,`tnf`] >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> irule self_code_prefix_operand_frame >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  rpt strip_tac >>
  `lookup_var p t = lookup_var p s` by metis_tac[] >>
  qpat_x_assum `ghost_kept cenv es sa G tn s Gf tnf` mp_tac >>
  qpat_x_assum `ptr_covers G tn p s sz` mp_tac >>
  qpat_x_assum `not_fresh_at sa p` mp_tac >>
  qpat_x_assum `lookup_var p t = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  rw[ghost_kept_def, ptr_covers_def] >> metis_tac[]
QED

Theorem external_code_tail_abort_checked:
  compile_slice_extcode addr src len sz sa = (r,sb) /\
  eval_operand addr s = SOME av /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  (!x. MEM (Var x) [addr;src;len] ==> not_fresh_at sa x) /\
  LENGTH (lookup_account (w2w av) s.vs_accounts).code < dimword (:256) /\
  LENGTH (lookup_account (w2w av) s.vs_accounts).code < w2n a+w2n n /\
  op_taint tn addr = {} /\ op_taint tn src = {} /\ op_taint tn len = {} /\
  op_prov G src = NONE /\ op_prov G len = NONE /\ ~ctx_has_dalloca ctx ==>
  ?t Gf tnf. run_inst_seq (emitted_insts sa sb) s = Abort Revert_abort t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf
Proof
  strip_tac >> drule slice_extcode_shape >> strip_tac >>
  drule_all slice_extcode_prefix_run >>
  qpat_assum `LENGTH _ < w2n a + w2n n` (fn th => rewrite_tac[th]) >>
  strip_tac >>
  `(!z. src = Var z ==> not_fresh_at sa z) /\
   (!z. len = Var z ==> not_fresh_at sa z)` by metis_tac[MEM] >>
  drule_all external_code_size_bounds_checked >>
  disch_then (qspecl_then [`D`,`fn`,`PG`] strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (emitted_insts sa sc ++ emitted_insts sc sd)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule exprSimSliceBoundsTheory.slice_bounds_shape >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`u`,`Gf`,`tnf`] >>
  qpat_x_assum `emitted_insts sa sb = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `emitted_insts sa sd = _` (fn th => pure_rewrite_tac[th]) >>
  conj_tac
  >- (`!ys. run_inst_seq ((emitted_insts sa sc ++ emitted_insts sc sd) ++ ys) s =
         run_inst_seq (emitted_insts sa sc ++ emitted_insts sc sd) s` by
        (gen_tac >> irule run_inst_seq_append_err >> simp[]) >>
      pop_assum (fn th => rewrite_tac[GSYM listTheory.APPEND_ASSOC,
        REWRITE_RULE [GSYM listTheory.APPEND_ASSOC] th]) >>
      first_assum ACCEPT_TAC) >>
  match_mp_tac instSeqComposePtrTheory.inst_seq_ptr_abort_append >>
  qexistsl_tac [`Revert_abort`,`u`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* The whole success tail: the size check and bounds, the output
   allocation, then the copy and the length store. *)
Theorem external_code_tail_success_checked:
  compile_slice_extcode addr src len sz sa = (r,sb) /\
  fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
  eval_operand addr s = SOME av /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  (!x. MEM (Var x) [addr;src;len] ==> not_fresh_at sa x) /\
  LENGTH (lookup_account (w2w av) s.vs_accounts).code < dimword (:256) /\
  w2n a+w2n n <= LENGTH (lookup_account (w2w av) s.vs_accounts).code /\
  32+w2n n <= sz /\ sz < dimword (:256) /\
  op_taint tn addr = {} /\ op_taint tn src = {} /\ op_taint tn len = {} /\
  op_prov G src = NONE /\ op_prov G len = NONE /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) ==>
  ?z Gf tnf out p. run_inst_seq (emitted_insts sa sb) s = OK z /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    ghost_inv d cenv cx es Gf tnf z /\ ghost_kept cenv es sa G tn s Gf tnf /\
    r = Var out /\ lookup_var out z = SOME p /\
    (?tn0. ptr_covers Gf tn0 out z sz /\
      tnf = (tn0 with t_mem := (tn0.t_mem DIFF
        {j | w2n p+32 <= j /\ j < w2n p+32+w2n n}) DIFF
        {j | w2n p <= j /\ j < w2n p+32}))
Proof
  strip_tac >> drule slice_extcode_shape >> strip_tac >>
  `(!x. addr = Var x ==> not_fresh_at sa x) /\
   (!x. src = Var x ==> not_fresh_at sa x) /\
   (!x. len = Var x ==> not_fresh_at sa x)` by metis_tac[MEM] >>
  `~(LENGTH (lookup_account (w2w av) s.vs_accounts).code < w2n a + w2n n)` by
    decide_tac >>
  drule_all slice_extcode_prefix_run >>
  pop_assum (fn th => rewrite_tac[th]) >> strip_tac >>
  drule_all external_code_prefix_success_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `u.vs_accounts = s.vs_accounts /\ u.vs_labels = s.vs_labels /\
   u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[]) >>
  `stmt_state_rel ctx fn cenv cx es u` by
    (irule exprSimHashBoundaryTheory.hash_readonly_state_rel >>
     qexistsl_tac [`s`,`sa`] >> simp[] >>
     qpat_x_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[]) >>
  `sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_var <= se.cs_next_var /\
   sa.cs_next_id <= sd.cs_next_id /\ sa.cs_next_id <= se.cs_next_id` by simp[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sd x /\ not_fresh_at se x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sd /\ local_ptrs_reserved cenv se` by
    (conj_tac >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[]) >>
  `(!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sd x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sd x) /\
   (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at se x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at se x)` by
    metis_tac[] >>
  `MEM (mk_inst sd.cs_next_id ALLOCA [Lit (n2w sz)]
     [STRING #"%" (toString sd.cs_next_var)]) (fn_insts fn)` by
    (drule exprSimHashTheory.hash_emitted_inst_mem >> disch_then irule >>
     qpat_x_assum `emitted_insts sa sb = _` (fn th => rewrite_tac[th]) >>
     qpat_x_assum `emitted_insts sd se = _` (fn th => rewrite_tac[th]) >>
     simp[]) >>
  suspend "alloc"
QED

Resume external_code_tail_success_checked[alloc]:
  qabbrev_tac `i0 = s.vs_inst_idx +
    LENGTH (emitted_insts sa sc ++ emitted_insts sc sd)` >>
  mp_tac (Q.INST [`s` |-> `u with vs_inst_idx := i0`, `sa` |-> `sd`,
    `sb` |-> `se`, `out` |-> `r`, `G` |-> `Gf`, `tn` |-> `tnf`]
    self_code_out_buffer_checked) >>
  impl_tac
  >- simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       hash_ghost_inv_inst_idx] >>
  strip_tac >>
  rename1 `run_inst_seq (emitted_insts sd se) _ = OK t1x` >>
  rename1 `r = Var xo` >> rename1 `dst = Var xd` >>
  qpat_x_assum `r = Var xo` SUBST_ALL_TAC >>
  qpat_x_assum `dst = Var xd` SUBST_ALL_TAC >>
  mp_tac (Q.INST [`s` |-> `u`, `sa` |-> `sd`, `sb` |-> `se`, `out` |-> `Var xo`,
    `data` |-> `Var xd`, `func` |-> `fn`]
    exprSimSliceMemoryTheory.slice_out_buf_run) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sd se) u = OK t1` >>
  rename1 `FLOOKUP t1.vs_allocas sd.cs_next_id = SOME (w2n pw,sz)` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sd se)` by
    (qpat_x_assum `emitted_insts sd se = _` (fn th => rewrite_tac[th]) >>
     simp[mk_inst_def, is_terminator_def]) >>
  `t1x = t1 with vs_inst_idx := i0` by
    (qpat_x_assum `run_inst_seq (emitted_insts sd se)
        (u with vs_inst_idx := i0) = _` mp_tac >>
     simp[fragExecTheory.run_inst_seq_inst_idx,
       instIdxIndepTheory.exec_result_map_def]) >>
  qpat_x_assum `t1x = _` SUBST_ALL_TAC >>
  suspend "frames"
QED

Resume external_code_tail_success_checked[frames]:
  `ghost_inv d cenv cx es G1 tn1 t1` by
    (qpat_x_assum `ghost_inv d cenv cx es G1 tn1 _` mp_tac >>
     simp[hash_ghost_inv_inst_idx]) >>
  `ghost_kept cenv es sd Gf tnf u G1 tn1` by
    (`!k. ghost_kept cenv es sd Gf tnf (u with vs_inst_idx := k) G1 tn1 <=>
          ghost_kept cenv es sd Gf tnf u G1 tn1` by
       (rpt (pop_assum kall_tac) >>
        simp[ghost_kept_def, local_region_def, lookup_var_def]) >>
     pop_assum (fn th => qpat_x_assum `ghost_kept cenv es sd Gf tnf _ G1 tn1`
       (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  `!x c c'. ptr_covers G1 tn1 x (t1 with vs_inst_idx := i0) c /\ c' <= c ==>
     ptr_covers G1 tn1 x t1 c'` by
    (simp[ptr_covers_def, lookup_var_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS,
       arithmeticTheory.LESS_EQ_MONO_ADD_EQ]) >>
  `ptr_covers G1 tn1 xo t1 32 /\ ptr_covers G1 tn1 xd t1 (w2n n)` by
    (conj_tac >> first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x t1 = lookup_var x s` by
    metis_tac[] >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
     eval_operand op t1 = eval_operand op s /\ op_taint tn1 op = op_taint tn op` by
    (rpt gen_tac >> strip_tac >>
     `!x. op = Var x ==> not_fresh_at sd x` by metis_tac[] >>
     `eval_operand op t1 = eval_operand op u /\
      op_prov G1 op = op_prov Gf op /\ op_taint tn1 op = op_taint tnf op` by
       (irule self_code_prefix_operand_frame >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [`cenv`,`es`,`sd`] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
     metis_tac[]) >>
  `eval_operand addr t1 = SOME av /\ op_taint tn1 addr = {} /\
   eval_operand src t1 = SOME a /\ op_taint tn1 src = {} /\
   eval_operand len t1 = SOME n /\ op_taint tn1 len = {}` by metis_tac[] >>
  `!name off c. local_region cenv es.scopes s name off c <=>
     local_region cenv es.scopes t1 name off c` by
    (rpt gen_tac >> irule (GSYM local_region_lookup_cong) >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!name off c. local_region cenv es.scopes s name off c <=>
     local_region cenv es.scopes u name off c` by
    (rpt gen_tac >> irule (GSYM local_region_lookup_cong) >>
     fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `t1.vs_accounts = s.vs_accounts` by
    (`t1.vs_accounts = u.vs_accounts` suffices_by simp[] >>
     irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_accounts`
       exprLoweringPropsTheory.run_inst_seq_preserves_field)) >>
     qexists_tac `emitted_insts sd se` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `emitted_insts sd se = _` (fn th => rewrite_tac[th]) >>
     rw[]
     >- (qspecl_then [`sd.cs_next_id`, `n2w sz`,
           `STRING #"%" (toString sd.cs_next_var)`, `ss1`] strip_assume_tac
           loweringHaltTheory.step_alloca_frame >> gvs[]) >>
     gvs[venomExecSemanticsTheory.step_inst_base_opcode_eqs, mk_inst_def,
         venomExecSemanticsTheory.exec_pure2_def, AllCaseEqs(),
         update_var_def]) >>
  suspend "copy"
QED

Resume external_code_tail_success_checked[copy]:
  `lookup_var xo t1 = SOME pw /\ lookup_var xd t1 = SOME (pw+32w)` by
    fs[eval_operand_def] >>
  `w2n pw+32 < dimword (:256)` by decide_tac >>
  `!name off c. local_region cenv es.scopes t1 name off c ==>
     off+c <= w2n pw \/ w2n pw+32+w2n n <= off` by
    (rpt strip_tac >>
     qpat_x_assum `!name off len. local_region cenv es.scopes t1 _ _ _ ==> _`
       drule >> simp[regions_disjoint_def]) >>
  mp_tac (Q.INST [`s` |-> `t1`, `G` |-> `G1`, `tn` |-> `tn1`, `sa` |-> `se`,
    `sb` |-> `sf`, `sc` |-> `sb`, `out` |-> `xo`, `dst` |-> `xd`, `p` |-> `pw`]
    external_code_copy_store_uniform_ptr) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `!name off c. local_region cenv es.scopes t1 name off c ==>
        off + c <= w2n pw \/ _` drule >> decide_tac) >>
  disch_then assume_tac >>
  mp_tac (Q.INST [`s` |-> `t1`, `G` |-> `G1`, `tn` |-> `tn1`, `sa` |-> `se`,
    `sb` |-> `sf`, `sc` |-> `sb`, `out` |-> `xo`, `dst` |-> `xd`, `p` |-> `pw`]
    external_code_copy_store_emitted_ptr) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `!name off c. local_region cenv es.scopes t1 name off c ==>
        off + c <= w2n pw \/ _` drule >> decide_tac) >>
  strip_tac >>
  mp_tac (Q.INST [`es0` |-> `es`, `es1` |-> `es`, `sb` |-> `sd`, `G0` |-> `G`,
    `tn0` |-> `tn`, `s0` |-> `s`, `G1` |-> `Gf`, `tn1` |-> `tnf`, `s1` |-> `u`,
    `G2` |-> `G1`, `tn2` |-> `tn1`]
    (INST_TYPE [alpha |-> ``:num # num``] wordArgsPtrTheory.ghost_kept_trans)) >>
  impl_tac >- simp[] >> strip_tac >>
  mp_tac (Q.INST [`es0` |-> `es`, `es1` |-> `es`, `sb` |-> `se`, `G0` |-> `G`,
    `tn0` |-> `tn`, `s0` |-> `s`, `s1` |-> `t1`, `G2` |-> `G1`, `tn2` |-> `tn'`]
    (INST_TYPE [alpha |-> ``:num # num``] wordArgsPtrTheory.ghost_kept_trans)) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  suspend "compose"
QED

Resume external_code_tail_success_checked[compose]:
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (emitted_insts sa sc ++ emitted_insts sc sd)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule exprSimSliceBoundsTheory.slice_bounds_shape >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G1 tn1 (emitted_insts se sb)
     ((t1 with vs_inst_idx := i0) with vs_inst_idx := k) G1 tn'` by
    (gen_tac >>
     qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ (emitted_insts se sb) _ _ _`
       (qspec_then `k` mp_tac) >>
     simp[]) >>
  `inst_seq_ptr D 0 ctx fn PG Gf tnf (emitted_insts sd se ++ emitted_insts se sb)
     (u with vs_inst_idx := i0) G1 tn'` by
    (match_mp_tac (Q.SPECL [`emitted_insts sd se`, `u with vs_inst_idx := i0`,
       `t1 with vs_inst_idx := i0`, `Gf`, `tnf`, `G1`, `tn1`, `G1`, `tn'`,
       `emitted_insts se sb`] instSeqComposePtrTheory.inst_seq_ptr_append) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`t`,`G1`,`tn'`,`xo`,`pw`] >>
  qpat_x_assum `emitted_insts sa sb = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `emitted_insts sa sd = _` (fn th => pure_rewrite_tac[th]) >>
  conj_tac
  >- (qpat_x_assum `run_inst_seq (_ ++ _) s = OK u`
        (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
      qpat_x_assum `run_inst_seq (emitted_insts sd se) u = OK t1`
        (fn th => rewrite_tac[MATCH_MP run_inst_seq_append th]) >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (match_mp_tac (Q.SPECL [`emitted_insts sa sc ++ emitted_insts sc sd`, `s`,
        `u`, `G`, `tn`, `Gf`, `tnf`, `G1`, `tn'`,
        `emitted_insts sd se ++ emitted_insts se sb`]
        exprSimPtrLiteralChunksTheory.literal_inst_seq_ptr_append) >>
      rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC >>
      qpat_x_assum `Abbrev (i0 = _)` (fn th => rewrite_tac[GSYM
        (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
      first_assum ACCEPT_TAC) >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC
  >- simp[]
  >- (qpat_x_assum `lookup_var xo t1 = _` mp_tac >>
      qpat_assum `t = mstore _ _ _` (fn th => rewrite_tac[th]) >>
      simp_tac (srw_ss())
        [lookup_var_def, mstore_def, write_memory_with_expansion_def]) >>
  qexists_tac `tn1` >> simp[] >>
  `ptr_covers G1 tn1 xo t1 sz` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[]) >>
  pop_assum mp_tac >>
  simp[NoAsms, ptr_covers_def, lookup_var_def, mstore_def,
    write_memory_with_expansion_def] >> metis_tac[]
QED

Finalise external_code_tail_success_checked
