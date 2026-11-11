Theory bodyPtrCodeSliceExternalContinue
Ancestors
  bodyPtrCodeSliceExternalCopy bodyPtrCodeSliceExternalBounds
  bodyPtrCodeSliceExternalAddress bodyPtrCodeSliceSelfSuffix
  exprSimSliceExtcode exprSimSliceExtcodeContinue exprSimSliceExtcodeEntry
  bodyPtrDefs fragExecPtr fragGasSeqPtr ptrDiscipline ptrSafeRun
  emitHelperProps exprLoweringProps compileEnv loweringPosts venomState venomInst
  venomExecSemantics words list rich_list finite_map pred_set
  exprSimPtrLiteralBuffer bodyPtrCodeSliceSelfOperands

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
