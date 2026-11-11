(* Runtime copy/store boundary, independent of operand evaluation and
   allocation implementation.  The code source is not a memory read. *)
Theory bodyPtrCodeSliceSelfSuffix
Ancestors
  bodyPtrCodeSliceSelfCopy fragExecPtr fragGasSeqPtr typedCopyPtr
  exprSimPtrTopLevelImmutableCopy bodyPtrHashBuiltinsGhostFrame
  lowerDloadPtrExpansionTransport emitHelperProps bodyPtrDefs
  ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
  codegenRel words list finite_map pred_set valueEncodingProps
  abiDecodeStaticProps exprSimPtrLiteralBuffer bodyPtrAttributeFields loweringPosts context

Theorem self_code_copy_store_checked:
  !D ctx fn PG G tn s t id sid dst out src len a n p b.
    ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn out s 32 /\
    eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
    lookup_var out s = SOME p /\ lookup_var dst s = SOME b /\
    op_taint tn src = {} /\ op_taint tn len = {} /\
    ~ctx_has_dalloca ctx /\
    step_inst_base (mk_inst id CODECOPY [Var dst;src;len] []) s = OK t ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id CODECOPY [Var dst;src;len] [];
       mk_inst sid MSTORE [Var out;len] []] s G
      (tn with t_mem := (tn.t_mem DIFF
        {j | w2n b <= j /\ j < w2n b + w2n n}) DIFF
        {j | w2n p <= j /\ j < w2n p + 32})
Proof
  rpt strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id CODECOPY [Var dst;src;len] []) s` by
    (irule ptr_inst_ok_codecopy >> simp[] >> metis_tac[]) >>
  `step_prov PG G (mk_inst id CODECOPY [Var dst;src;len] []) t = G /\
   step_taint (mk_inst id CODECOPY [Var dst;src;len] []) s t tn =
     tn with t_mem := tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b + w2n n}` by
    (drule_at (Pat `step_inst_base _ _ = _`) dload_codecopy_state_ghost >>
     simp[mk_inst_def, eval_operand_def] >> metis_tac[]) >>
  `t.vs_vars = s.vs_vars /\ t.vs_labels = s.vs_labels` by
    (drule_at (Pat `step_inst_base _ _ = _`) dload_codecopy_state_ghost >>
     simp[mk_inst_def, eval_operand_def, write_memory_with_expansion_def] >>
     metis_tac[]) >>
  simp[inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `ptr_inst_ok _ _ _ _ _ _ un _ u` >>
  `lookup_var out u = SOME p /\ eval_operand len u = SOME n` by
    (Cases_on `len` >> gvs[Abbr `u`, lookup_var_def, eval_operand_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G un (mk_inst sid MSTORE [Var out;len] []) u` by
    (irule ptr_inst_ok_mstore >>
     gvs[Abbr `un`, Abbr `u`, ptr_covers_def, op_taint_def, lookup_var_def]) >>
  simp[] >>
  `step_inst_base (mk_inst sid MSTORE [Var out;len] []) u =
    OK (mstore (w2n p) n u)` by
    simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def, eval_operand_def] >>
  simp[] >>
  `step_prov PG G (mk_inst sid MSTORE [Var out;len] []) (mstore (w2n p) n u) = G /\
   step_taint (mk_inst sid MSTORE [Var out;len] []) u (mstore (w2n p) n u) un =
     un with t_mem := un.t_mem DIFF {j | w2n p <= j /\ j < w2n p + 32}` by
    (irule toplevel_immutable_mstore_ghost_frame >> gvs[Abbr `un`, op_taint_def]) >>
  gvs[Abbr `u`, Abbr `un`, inst_seq_ptr_def]
QED

Theorem self_code_copy_store_exterior:
  !p bs w s i.
    (i < p \/ p + 32 + LENGTH bs <= i) ==>
    mem_bytes_at i 1
      (mstore p w (write_memory_with_expansion (p+32) bs s)).vs_memory =
    mem_bytes_at i 1 s.vs_memory
Proof
  rpt gen_tac >> disch_tac >>
  irule EQ_TRANS >>
  qexists_tac `mem_bytes_at i 1 (write_memory_with_expansion (p+32) bs s).vs_memory` >>
  conj_tac >- (irule mem_bytes_at_mstore_outside >> decide_tac) >>
  irule valueEncodingPropsTheory.write_memory_mem_bytes_at_disjoint >> decide_tac
QED

Theorem self_code_copy_store_ghost_frame:
  !d cenv cx es G tn s ctx fn sa p bs w.
    ghost_inv d cenv cx es G tn s /\
    stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!n b k. local_region cenv es.scopes s n b k ==>
      b+k <= p \/ p+32+LENGTH bs <= b) ==>
    ghost_inv d cenv cx es G
      (tn with t_mem := (tn.t_mem DIFF
        {j | p+32 <= j /\ j < p+32+LENGTH bs}) DIFF
        {j | p <= j /\ j < p+32})
      (mstore p w (write_memory_with_expansion (p+32) bs s))
Proof
  rpt strip_tac >> irule hash_ghost_inv_exterior_frame >>
  conj_tac >-
    (once_rewrite_tac[mstore_with_memory] >>
     simp[stor_taint_ok_def, write_memory_with_expansion_def] >>
     qpat_x_assum `ghost_inv _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_inv_def, stor_taint_ok_def]) >>
  qexistsl_tac [`G`, `ctx`, `fn`, `s`, `sa`, `tn`,
    `{j | p <= j /\ j < p+32+LENGTH bs}`] >>
  `!x. lookup_var x (mstore p w (write_memory_with_expansion (p+32) bs s)) =
        lookup_var x s` by
    simp[lookup_var_def, write_memory_with_expansion_def] >>
  simp[op_taint_def] >>
  conj_tac >- (rpt strip_tac >> res_tac >> decide_tac) >>
  rpt gen_tac >> disch_tac >> irule self_code_copy_store_exterior >> decide_tac
QED

Theorem self_code_copy_store_result:
  !cx ty cap bs out G tn s p base_addr sz.
    evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic cap))) /\
    lookup_var out s = SOME p /\ FLOOKUP G out = SOME (base_addr,sz) /\
    base_addr <= w2n p /\
    w2n p + val_store_size (BaseTV (BytesT (Dynamic cap))) (BytesV bs) <= base_addr+sz /\
    val_wf (BaseTV (BytesT (Dynamic cap))) (BytesV bs) /\
    val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) (w2n p) s.vs_memory ==>
    ptr_mem_ok cx ty (BytesV bs) (Var out) G
      (tn with t_mem := (tn.t_mem DIFF
        {j | w2n p+32 <= j /\ j < w2n p+32+LENGTH bs}) DIFF
        {j | w2n p <= j /\ j < w2n p+32}) s
Proof
  rpt strip_tac >> irule literal_clean_ptr_mem_ok >>
  qexistsl_tac [`base_addr`, `sz`, `p`] >> simp[] >>
  rpt strip_tac >> gvs[] >>
  gvs[val_footprint_def] >> decide_tac
QED

Theorem self_code_copy_store_ptr:
  !D ctx fn PG G tn s id sid dst out src len a n p b bs d cenv cx es sa.
    ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn out s 32 /\
    eval_operand src s = SOME a /\ eval_operand len s = SOME n /\
    lookup_var out s = SOME p /\ lookup_var dst s = SOME b /\
    op_taint tn src = {} /\ op_taint tn len = {} /\ ~ctx_has_dalloca ctx /\
    w2n b = w2n p+32 /\ w2n n = LENGTH bs /\
    step_inst_base (mk_inst id CODECOPY [Var dst;src;len] []) s =
      OK (write_memory_with_expansion (w2n p+32) bs s) /\
    ghost_inv d cenv cx es G tn s /\
    stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!name off sz. local_region cenv es.scopes s name off sz ==>
      off+sz <= w2n p \/ w2n p+32+LENGTH bs <= off) ==>
    inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id CODECOPY [Var dst;src;len] [];
       mk_inst sid MSTORE [Var out;len] []] s G
      (tn with t_mem := (tn.t_mem DIFF
        {j | w2n p+32 <= j /\ j < w2n p+32+LENGTH bs}) DIFF
        {j | w2n p <= j /\ j < w2n p+32}) /\
    ghost_inv d cenv cx es G
      (tn with t_mem := (tn.t_mem DIFF
        {j | w2n p+32 <= j /\ j < w2n p+32+LENGTH bs}) DIFF
        {j | w2n p <= j /\ j < w2n p+32})
      (mstore (w2n p) n (write_memory_with_expansion (w2n p+32) bs s)) /\
    ghost_kept cenv es sa G tn s G
      (tn with t_mem := (tn.t_mem DIFF
        {j | w2n p+32 <= j /\ j < w2n p+32+LENGTH bs}) DIFF
        {j | w2n p <= j /\ j < w2n p+32})
Proof
  rpt strip_tac
  >- (drule_all self_code_copy_store_checked >> simp[])
  >- (irule self_code_copy_store_ghost_frame >> metis_tac[]) >>
  irule literal_ghost_kept >> simp[op_taint_def, SUBSET_DEF]
QED

Theorem self_code_copy_store_located_result:
  !cx ty cap bs out G tn tn' s p base_addr sz cenv e tv es lowty.
    evaluate_type (get_tenv cx) ty = SOME (BaseTV (BytesT (Dynamic cap))) /\
    lookup_var out s = SOME p /\ FLOOKUP G out = SOME (base_addr,sz) /\
    base_addr <= w2n p /\
    w2n p + val_store_size (BaseTV (BytesT (Dynamic cap))) (BytesV bs) <= base_addr+sz /\
    val_wf (BaseTV (BytesT (Dynamic cap))) (BytesV bs) /\
    val_in_memory (BaseTV (BytesT (Dynamic cap))) (BytesV bs) (w2n p) s.vs_memory /\
    tn' = (tn with t_mem := (tn.t_mem DIFF
      {j | w2n p+32 <= j /\ j < w2n p+32+LENGTH bs}) DIFF
      {j | w2n p <= j /\ j < w2n p+32}) /\
    op_taint tn (Var out) = {} /\ read_result cx tv es = (INL (BytesV bs),es) /\
    w2n p + type_memory_bytes cenv (lowered_value_type cenv e) <= base_addr+sz ==>
    ptr_vv_ok cx ty tv (LocatedValue lowty (mk_ptr (Var out) LocMemory)) es G tn' s /\
    ptr_buf_ok cenv e (Var out) G s
Proof
  rpt gen_tac >> strip_tac >>
  `ptr_mem_ok cx ty (BytesV bs) (Var out) G tn' s` by
    (drule_all self_code_copy_store_result >> gvs[]) >>
  conj_tac >-
    (irule ptr_vv_ok_memory >> simp[mk_ptr_def] >>
     gvs[op_taint_def]) >>
  irule literal_site_ptr_buf_ok >> metis_tac[]
QED
