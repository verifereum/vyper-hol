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
