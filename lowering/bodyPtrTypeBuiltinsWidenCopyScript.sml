Theory bodyPtrTypeBuiltinsWidenCopy
Ancestors
  bodyPtrTypeBuiltinsWidenCopyShape bodyPtrTypeBuiltinsCopyFrame
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
