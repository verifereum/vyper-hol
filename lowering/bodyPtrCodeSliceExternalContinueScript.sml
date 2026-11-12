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
  annAssignPtrSetup bodyPtrCodeSliceSelfPrefix exprSimHashBoundary wordArgsPtr

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
  rpt strip_tac >> irule annassign_declared_pointer_after_rhs_ptr >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem external_code_tail_abort_checked:
  compile_slice_extcode addr src len out dst sa = (r,sf) /\
  eval_operand addr s = SOME av /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  (!x. MEM (Var x) [addr;src;len] ==> not_fresh_at sa x) /\
  LENGTH (lookup_account (w2w av) s.vs_accounts).code < dimword (:256) /\
  LENGTH (lookup_account (w2w av) s.vs_accounts).code < w2n a+w2n n /\
  op_taint tn addr = {} /\ op_taint tn src = {} /\ op_taint tn len = {} /\
  op_prov G src = NONE /\ op_prov G len = NONE /\ ~ctx_has_dalloca ctx ==>
  ?t Gf tnf. run_inst_seq (emitted_insts sa sf) s = Abort Revert_abort t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sf) s Gf tnf
Proof
  strip_tac >> drule slice_extcode_shape >> strip_tac >>
  drule_all slice_extcode_prefix_run >> simp[] >> strip_tac >>
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
  qpat_x_assum `emitted_insts sa sf = _` (fn th => pure_rewrite_tac[th]) >>
  rewrite_tac[APPEND_ASSOC] >> conj_tac
  >- simp[run_inst_seq_append_err] >>
  irule inst_seq_ptr_abort_append >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem external_code_tail_success_checked:
  compile_slice_extcode addr src len (Var out) (Var dst) sa = (r,sf) /\
  eval_operand addr s = SOME av /\
  eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
  lookup_var out s = SOME p /\ lookup_var dst s = SOME (p+32w) /\
  (!x. MEM (Var x) [addr;src;len;Var out;Var dst] ==> not_fresh_at sa x) /\
  LENGTH (lookup_account (w2w av) s.vs_accounts).code < dimword (:256) /\
  w2n a+w2n n <= LENGTH (lookup_account (w2w av) s.vs_accounts).code /\
  w2n p+32 < dimword (:256) /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn out s sz /\ 32 <= sz /\
  op_taint tn addr = {} /\ op_taint tn src = {} /\ op_taint tn len = {} /\
  op_prov G src = NONE /\ op_prov G len = NONE /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx fn cenv cx es s /\
  local_ptrs_reserved cenv sa /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!name off sz. local_region cenv es.scopes s name off sz ==>
    off+sz <= w2n p \/ w2n p+32+w2n n <= off) ==>
  ?z Gf tnf. run_inst_seq (emitted_insts sa sf) s = OK z /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sf) s Gf tnf /\
    ghost_inv d cenv cx es Gf tnf z /\ ghost_kept cenv es sa G tn s Gf tnf /\
    lookup_var out z = SOME p /\
    (?tn0. ptr_covers Gf tn0 out z sz /\
      tnf = (tn0 with t_mem := (tn0.t_mem DIFF
        {j | w2n p+32 <= j /\ j < w2n p+32+w2n n}) DIFF
        {j | w2n p <= j /\ j < w2n p+32}))
Proof
  strip_tac >> drule slice_extcode_shape >> strip_tac >>
  `(!x. MEM (Var x) [addr;src;len] ==> not_fresh_at sa x) /\
   (!x. src = Var x ==> not_fresh_at sa x) /\
   (!x. len = Var x ==> not_fresh_at sa x)` by metis_tac[MEM] >>
  drule_all slice_extcode_prefix_run >> simp[] >> strip_tac >>
  drule_all external_code_prefix_success_frame >>
  disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
  `(!op. MEM op [addr;src;len;Var out;Var dst] ==>
     eval_operand op u = eval_operand op s /\
     op_prov Gf op = op_prov G op /\ op_taint tnf op = op_taint tn op)` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!op. (!x. op = Var x ==> _) ==> _ /\ _`
       (qspec_then `op` irule) >> metis_tac[]) >>
  `sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id /\
   local_ptrs_reserved cenv sd /\
   (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sd x) /\
   (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sd x)` by
    suspend "compiler_frame" >>
  `!name off sz. local_region cenv es.scopes u name off sz <=>
     local_region cenv es.scopes s name off sz` by suspend "local_frame" >>
  `stmt_state_rel ctx fn cenv cx es u` by
    (irule exprSimHashBoundaryTheory.hash_readonly_state_rel >>
     qexistsl_tac [`s`,`sa`] >> simp[] >>
     qpat_x_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[]) >>
  `eval_operand addr u = SOME av /\ eval_operand src u = SOME a /\
   eval_operand len u = SOME n /\ lookup_var out u = SOME p /\
   lookup_var dst u = SOME (p+32w) /\
   op_taint tnf addr = {} /\ op_taint tnf src = {} /\ op_taint tnf len = {} /\
   ptr_covers Gf tnf out u sz /\ ptr_covers Gf tnf dst u (w2n n)` by
    (fs[eval_operand_def] >> metis_tac[MEM]) >>
  `ptr_covers Gf tnf out u 32` by
    (fs[ptr_covers_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `u.vs_accounts = s.vs_accounts` by
    (qpat_x_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `!name off sz. local_region cenv es.scopes u name off sz ==>
     off+sz <= w2n p \/ w2n p+32+w2n n <= off` by metis_tac[] >>
  mp_tac (Q.INST [`s` |-> `u`, `G` |-> `Gf`, `tn` |-> `tnf`,
    `sa` |-> `sd`, `sb` |-> `se`, `sc` |-> `sf`]
    external_code_copy_store_uniform_ptr) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> disch_then assume_tac >>
  mp_tac (Q.INST [`s` |-> `u`, `G` |-> `Gf`, `tn` |-> `tnf`,
    `sa` |-> `sd`, `sb` |-> `se`, `sc` |-> `sf`]
    external_code_copy_store_emitted_ptr) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  suspend "compose"
QED

Resume external_code_tail_success_checked[compiler_frame]:
  drule emitted_insts_emit_op >> strip_tac >>
  drule exprSimSliceBoundsTheory.slice_bounds_shape >> strip_tac >>
  `sa.cs_next_var <= sd.cs_next_var /\ sa.cs_next_id <= sd.cs_next_id` by
    (gvs[] >> simp[]) >>
  simp[] >> conj_tac
  >- (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >> rpt strip_tac >> fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Resume external_code_tail_success_checked[local_frame]:
  gvs[local_region_def, local_ptrs_reserved_def, eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED

Resume external_code_tail_success_checked[compose]:
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (emitted_insts sa sc ++ emitted_insts sc sd)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule exprSimSliceBoundsTheory.slice_bounds_shape >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`t`,`Gf`,`tn'`] >> conj_tac
  >- (rewrite_tac[APPEND_ASSOC] >>
      qpat_x_assum `run_inst_seq (_ ++ _) s = OK u`
        (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sd sf` mp_tac) >> simp[]) >>
  conj_tac
  >- (rewrite_tac[APPEND_ASSOC] >> irule inst_seq_ptr_append >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> gvs[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (irule ghost_kept_trans >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[] >>
      qpat_x_assum `u = s with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  conj_tac >- simp[] >>
  qexists_tac `tnf` >> simp[] >>
  qpat_x_assum `ptr_covers Gf tnf out u sz` mp_tac >>
  simp[NoAsms, ptr_covers_def, lookup_var_def, mstore_def,
    write_memory_with_expansion_def] >> metis_tac[]
QED

Finalise external_code_tail_success_checked
