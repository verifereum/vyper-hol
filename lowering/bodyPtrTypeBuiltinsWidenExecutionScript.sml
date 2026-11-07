Theory bodyPtrTypeBuiltinsWidenExecution
Ancestors bodyPtrTypeBuiltinsWidenCopyShape exprSimAlloc exprSimBufferStore
  exprLoweringProps exprLowering context compileEnv emitHelperProps
  venomExecSemantics venomState words arithmetic exprSimOperands exprSimProps
  loweringPosts valueEncoding loweringHalt venomInst

Theorem widen_copy_actual_run:
  compile_bytestring_widen_copy d x k sm = (op,sb) /\
  0 < k /\ k <= d /\ d < dimword(:256) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ eval_operand x s = SOME p ==>
  ?t w. run_inst_seq (emitted_insts sm sb) s = OK (mcopy (w2n w) (w2n p) k t) /\
    stmt_state_rel ctx func cenv cx es t /\ eval_operand op t = SOME w /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,d) /\
    w2n w + d < dimword(:256) /\ t.vs_memory = s.vs_memory /\
    (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) d b len) /\
    (!name b len. local_region cenv es.scopes t name b len ==>
       regions_disjoint (w2n w) d b len) /\
    sm.cs_next_id < sb.cs_next_id
Proof
  strip_tac >> drule_all widen_copy_code_split >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule_all hash_alloc_buffer_labels >> strip_tac >>
  `eval_operand x t = SOME p` by
    (Cases_on `x` >> gvs[eval_operand_def]) >>
  `emit_void MCOPY [buf.buf_operand;x;Lit (n2w k)] sm' = ((),sb)` by
    (Cases_on `k` >> gvs[compile_copy_memory_def]) >>
  `eval_operand (Lit (n2w k)) t = SOME (n2w k)` by simp[eval_operand_def] >>
  drule_all buffer_emit_mcopy_run >> strip_tac >>
  `k < dimword(:256)` by decide_tac >>
  qexistsl_tac [`t`,`w`] >> simp[w2n_n2w, LESS_MOD] >>
  conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts sm sm') s = OK t`
        (mp_then Any mp_tac run_inst_seq_append) >>
      disch_then (qspec_then `emitted_insts sm' sb` mp_tac) >>
      simp[w2n_n2w, LESS_MOD]) >>
  gvs[ci_mono_def] >> metis_tac[LESS_LESS_EQ_TRANS]
QED

Theorem widen_copy_actual_post:
  compile_bytestring_widen_copy d x k sm = (op,sb) /\
  0 < k /\ k <= d /\ d < dimword(:256) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ eval_operand x s = SOME p /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_in_memory tv v (w2n p) s.vs_memory /\
  val_footprint tv v <= k ==>
  ?t. run_inst_seq (emitted_insts sm sb) s = OK t /\
    expr_post ctx func cenv cx e es sm sb s es v op t
Proof
  strip_tac >> drule_all widen_copy_actual_run >> strip_tac >>
  drule_all widen_copy_code_split >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sm.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (mcopy (w2n w) (w2n p) k t)` by
    (irule stmt_state_rel_mcopy_alloca >> simp[] >>
     qexistsl_tac [`d`,`mk_inst sm.cs_next_id ALLOCA [Lit (n2w d)]
       [STRING #"%" (toString sm.cs_next_var)]`,
       `STRING #"%" (toString sm.cs_next_var)`] >> simp[mk_inst_def]) >>
  `val_in_memory tv v (w2n w) (mcopy (w2n w) (w2n p) k t).vs_memory` by
    (irule buffer_mcopy_encoding >> simp[]) >>
  qexists_tac `mcopy (w2n w) (w2n p) k t` >> simp[] >>
  suspend "owned_post"
QED

Resume widen_copy_actual_post[owned_post]:
  `wb_frame cenv es sm s (mcopy (w2n w) (w2n p) k t)` by
    suspend "wb_frame" >>
  `!name lb lsz. local_region cenv es.scopes (mcopy (w2n w) (w2n p) k t)
       name lb lsz ==> w2n w + d <= lb \/ lb + lsz <= w2n w` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ _ (mcopy _ _ _ _)`
       (mp_then Any mp_tac alloca_clear_of_locals) >>
     disch_then (qspec_then `mk_inst sm.cs_next_id ALLOCA [Lit (n2w d)]
       [STRING #"%" (toString sm.cs_next_var)]` mp_tac) >>
     simp[mk_inst_def, mcopy_def, write_memory_with_expansion_def] >>
     disch_then (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     gvs[mcopy_def, write_memory_with_expansion_def]) >>
  gvs[expr_post_def, expr_val_rel_def, expr_val_at_def, wb_frame_def,
      mcopy_def, write_memory_with_expansion_def, eval_operand_def, lookup_var_def] >>
  reverse conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!aid off sz. _` irule >> simp[] >> metis_tac[]) >>
  disj1_tac >> qexistsl_tac [`sm.cs_next_id`,`w2n w`,`buf.buf_size`] >>
  simp[] >> metis_tac[LESS_EQ_TRANS]
QED

Resume widen_copy_actual_post[wb_frame]:
  simp[wb_frame_def] >> rpt conj_tac
  >- (simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
      metis_tac[lookup_var_def])
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. _` drule_all >>
      simp[regions_disjoint_def] >> disch_tac >>
      irule EQ_TRANS >> qexists_tac `mem_bytes_at off sz t.vs_memory` >>
      conj_tac >- (irule buffer_mcopy_exterior >> decide_tac) >> simp[]) >>
  irule locals_kept_regions >> rpt strip_tac >>
  `local_region cenv es.scopes t n b sz` by
    (irule local_region_frame_fwd >>
     qexistsl_tac [`s`,`sm`,`es.scopes`] >> simp[]) >>
  qpat_x_assum `!name b len. _` drule >>
  simp[regions_disjoint_def] >> disch_tac >>
  irule EQ_TRANS >> qexists_tac `mem_bytes_at b sz t.vs_memory` >>
  conj_tac >- (irule buffer_mcopy_exterior >> decide_tac) >> simp[]
QED

Finalise widen_copy_actual_post
