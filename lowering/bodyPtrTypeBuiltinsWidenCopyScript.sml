Theory bodyPtrTypeBuiltinsWidenCopy
Ancestors
  bodyPtrTypeBuiltinsWidenCopyShape bodyPtrTypeBuiltinsCopyFrame
  bodyPtrTypeBuiltinsSeq bodyPtrTypeBuiltinsEmptyAlloc
  bodyPtrTypeBuiltinsCopyCounted bodyPtrDefs ghostPcTransportPtr
  fragGasSeqPtr instIdxIndep ptrSafeRun fragExecPtr words
  normalizationAllocPtr loweringPosts loweringHalt allocationPtr exprSimAlloc
  context emitHelper emitHelperProps exprLoweringProps exprSimProps rich_list
  compileEnv venomExecSemantics
  venomInst venomState ptrDiscipline robustCopyTransportPtr

(* Placement, not source-register reservedness alone, excludes overlap with
   a reused allocation site.  Keep the source's semantic type explicit. *)
Theorem alloc_buffer_source_robust:
  compile_alloc_buffer capacity sa = (buf,sm) /\ fn_has_code sa sm fn /\
  run_inst_seq (emitted_insts sa sm) s = OK t /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ capacity < dimword(:256) /\
  expr_val_at cenv cx tsrc slo sa es v (Var src) s /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\ ~is_word_type tsrc /\
  val_wf tv v /\ lookup_var src s = SOME a /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  !m. mem_agree_outside
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w capacity)]
      [STRING #"%" (toString sa.cs_next_var)]) s t tn).t_mem t.vs_memory m ==>
    val_in_memory tv v (w2n a) m
Proof
  strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w capacity)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)` by
    metis_tac[buffer_alloc_code] >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def, AllCaseEqs()] >>
  drule_all alloca_step_site >> strip_tac >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac alloca_step_expr_robust_preserved) >>
  simp[eval_operand_def] >> disch_then assume_tac >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem alloc_buffer_source_resources:
  compile_alloc_buffer capacity sa = (buf,sm) /\ fn_has_code sa sm fn /\
  run_inst_seq (emitted_insts sa sm) s = OK t /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sm) s G1 tn1 /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ capacity < dimword(:256) /\ not_fresh_at sa src /\
  expr_val_at cenv cx tsrc slo sa es v (Var src) s /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\ ~is_word_type tsrc /\
  val_wf tv v /\ lookup_var src s = SOME a /\ ptr_covers G tn src s n /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  lookup_var src t = SOME a /\ ptr_covers G1 tn1 src t n /\
  (!m. mem_agree_outside tn1.t_mem t.vs_memory m ==>
    val_in_memory tv v (w2n a) m)
Proof
  strip_tac >>
  qpat_assum `expr_val_at _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac alloc_buffer_source_robust) >>
  disch_then (fn th => qpat_assum `compile_alloc_buffer _ _ = _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `run_inst_seq _ _ = OK _`
    (mp_then Any mp_tac th)) >>
  disch_then (fn th => qpat_assum `stmt_state_rel _ _ _ _ _ _`
    (mp_then Any mp_tac th)) >>
  simp[] >> disch_then (qspec_then `tn` assume_tac) >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w capacity)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn)` by
    metis_tac[buffer_alloc_code] >>
  `lookup_var src t = SOME a` by
    (drule_all literal_alloc_buffer_run >> strip_tac >> gvs[]) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def, AllCaseEqs(),
    fragGasSeqPtrTheory.inst_seq_ptr_def] >>
  irule alloca_step_old_ptr_covers >> simp[] >>
  conj_tac >- (fs[not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem widen_copy_checked_certificate:
  compile_bytestring_widen_copy capacity (Var src) n sa = (op,sb) /\
  fn_has_code sa sb fn /\ run_inst_seq (emitted_insts sa sb) s0 = OK t /\
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct fn /\ capacity < dimword(:256) /\ n <= capacity /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  expr_val_at cenv cx tsrc slo sa es v (Var src) s0 /\
  evaluate_type (get_tenv cx) tsrc = SOME tv /\ ~is_word_type tsrc /\
  val_wf tv v /\ val_footprint tv v <= n /\ lookup_var src s0 = SOME a /\
  ptr_covers G0 tn0 src s0 n /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  (!m. mem_agree_outside tn0.t_mem s0.vs_memory m ==> val_in_memory tv v (w2n a) m) ==>
  ?dst b G th. op = Var dst /\ lookup_var dst t = SOME b /\
    inst_seq_ptr D 0 ctx fn PG G0 tn0 (emitted_insts sa sb) s0 G th /\
    ptr_covers G th dst t capacity /\ ghost_inv d cenv cx es G th t /\
    ghost_kept cenv es sa G0 tn0 s0 G th /\
    (!m. mem_agree_outside th.t_mem t.vs_memory m ==> val_in_memory tv v (w2n b) m)
Proof
  strip_tac >> drule_all widen_copy_split_certificate >> strip_tac >>
  drule_all empty_alloc_buffer_certificate >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  drule_all alloc_buffer_source_resources >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >> gvs[eval_operand_def] >>
  `capacity < dimword(:256) /\ lookup_var src s = SOME a` by
    (conj_tac >- decide_tac >> simp[]) >>
  drule_all allocated_copy_ghost_frame >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `n < dimword(:256) /\ ptr_covers G' tn' p s n` by
    (conj_tac >- decide_tac >>
     qpat_assum `ptr_covers G' tn' p s capacity` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >> strip_tac >> simp[] >>
     goal_assum (drule_at Any) >> decide_tac) >>
  `!m. mem_agree_outside tn'.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m` by simp[] >>
  `!m. mem_agree_outside th.t_mem t.vs_memory m ==>
    val_in_memory tv v (w2n w) m` by
    (qpat_assum `compile_copy_memory _ _ _ _ = _`
       (mp_then Any mp_tac copy_memory_destination_robust) >>
     disch_then (fn h => qpat_assum `run_inst_seq (emitted_insts sm sb) s = OK t`
       (mp_then Any mp_tac h)) >>
     disch_then (fn h => qpat_assum `th.t_mem = _` (mp_then Any mp_tac h)) >>
     simp[] >> metis_tac[]) >>
  drule_all copy_memory_endpoint_frame >> strip_tac >>
  qexistsl_tac [`w`,`G'`,`th`] >> simp[] >>
  suspend "sequence"
QED

Resume widen_copy_checked_certificate[sequence]:
  drule_all widen_copy_code_split >> strip_tac >>
  `buf' = buf /\ sm' = sm` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `buf' = buf` SUBST_ALL_TAC >>
  qpat_x_assum `sm' = sm` SUBST_ALL_TAC >>
  qpat_x_assum `emitted_insts sa sb = _` (fn h => rewrite_tac[h]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sm)` by
    (drule compile_alloc_buffer_insts >> strip_tac >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G' tn' (emitted_insts sm sb)
    (s with vs_inst_idx := k) G' th` by suspend "cursor" >>
  irule inst_seq_ptr_append_run >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`G'`,`tn'`] >> simp[]
QED

Resume widen_copy_checked_certificate[cursor]:
  qpat_assum `compile_copy_memory (Var p) _ _ _ = _`
    (mp_then Any mp_tac copy_memory_emitted_shape) >> disch_tac >>
  Cases_on `n = 0`
  >- (qpat_x_assum `inst_seq_ptr _ _ _ _ _ G' tn' _ s G' th` mp_tac >>
      qpat_x_assum `emitted_insts sm sb = _` mp_tac >>
      qpat_x_assum `n = 0` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >> strip_tac >> simp[inst_seq_ptr_def]) >>
  `!k. ptr_inst_ok D 0 0 ctx fn G' tn'
    (mk_inst sm.cs_next_id MCOPY [Var p;Var src;Lit (n2w n)] [])
    (s with vs_inst_idx := k)` by
    (gen_tac >> irule ptr_inst_ok_mcopy_operand >>
     simp[eval_operand_def, lookup_var_def, w2n_n2w, op_taint_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ G' tn' _ s G' th` mp_tac >>
  qpat_x_assum `emitted_insts sm sb = _` mp_tac >>
  qpat_x_assum `!k. ptr_inst_ok _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `n <> 0` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >> strip_tac >> strip_tac >>
  simp[inst_seq_ptr_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def, lookup_var_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `FLOOKUP s.vs_vars p` >> gvs[] >>
  Cases_on `FLOOKUP s.vs_vars src` >> gvs[mcopy_def]
QED

Finalise widen_copy_checked_certificate
