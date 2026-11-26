Theory bodyRawTupleAllocCopyEntryMods
Ancestors
  bodyPtrIfExpAllocCompiler bodyPtrIfExpAllocSource bodyPtrMakeArrayAllocBuffer
  allocationPtr bodyFullHashKeccakFixed exprSimProps loweringPosts
  compileEnv ptrDiscipline venomState venomInst venomMemDefs
  fragGasSeqPtr fragExecPtr instSeqPtrLo bodyFullRawCallTupleAllocFrame
  bodyPtrPrecompileBuiltinsStaging bodyLiteralBufferMemory
  finite_map words

Theorem raw_tuple_alloc_copy_entry:
  compile_alloc_buffer kbuf s4 = (buf,s5) /\
  fn_has_code s4 s5 func /\ fn_inst_ids_distinct func /\
  stmt_state_rel H ctx func cenv cx es u /\
  wb_frame cenv es0 es sf s0 u /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv s4 /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  sf.cs_next_var <= s4.cs_next_var /\ sf.cs_next_id <= s4.cs_next_id /\
  0 < n /\ kbuf = 64 + ((n+31) DIV 32)*32 /\
  kbuf < dimword (:256) /\ n < dimword (:256) /\
  allocas_from lo u /\ lo <= u.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp) /\
  FLOOKUP u.vs_allocas aid = SOME (a,L) /\ aid < s4.cs_next_id /\
  L = 32 + ((n+31) DIV 32)*32 /\
  lookup_var x u = SOME (n2w a) /\
  ptr_covers G1 tn1 x u L /\
  val_wf (BaseTV (BytesT (Dynamic n))) (BytesV bs) /\ LENGTH bs <= n /\
  (!mem. mem_agree_outside tn1.t_mem u.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) a mem) /\
  safe_operand s4 (Var x) /\ safe_operand s4 ok /\
  eval_operand ok u = SOME (if success then 1w else 0w) /\
  op_taint tn1 ok = {} ==>
  ?p r b.
    buf.buf_operand = Var p /\
    not_local_ptr cenv es.scopes p /\
    MEM (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) (fn_insts func) /\
    emitted_insts s4 s5 =
      [mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]] /\
    step_inst_base (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) u = OK r /\
    run_inst_seq (emitted_insts s4 s5) u = OK r /\
    stmt_state_rel H ctx func cenv cx es r /\
    wb_frame cenv es0 es sf s0 r /\
    FLOOKUP r.vs_allocas s4.cs_next_id = SOME (b,kbuf) /\
    lookup_var p r = SOME (n2w b) /\ b+kbuf < dimword (:256) /\
    u.vs_memory = r.vs_memory /\ u.vs_alloca_next <= r.vs_alloca_next /\
    (!aid' row. FLOOKUP u.vs_allocas aid' = SOME row ==>
      FLOOKUP r.vs_allocas aid' = SOME row) /\
    allocas_from lo r /\
    ptr_covers (step_prov PG G1 (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) r)
      (step_taint (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) u r tn1)
      x r L /\
    ptr_covers (step_prov PG G1 (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) r)
      (step_taint (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) u r tn1)
      p r kbuf /\
    (!mem. mem_agree_outside
      (step_taint (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) u r tn1).t_mem
      r.vs_memory mem ==>
      val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) a mem) /\
    (!v. not_fresh_at s4 v ==>
      lookup_var v r = lookup_var v u /\
      FLOOKUP (step_prov PG G1 (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) r) v = FLOOKUP G1 v /\
      op_taint (step_taint (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) u r tn1) (Var v) =
        op_taint tn1 (Var v)) /\
    (step_taint (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) u r tn1).t_stor = tn1.t_stor /\
    (step_taint (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) u r tn1).t_trans = tn1.t_trans /\
    (step_taint (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) u r tn1).t_imm = tn1.t_imm /\
    p = STRING #"%" (toString s4.cs_next_var) /\
    FLOOKUP r.vs_allocas aid = SOME (a,L) /\
    lookup_var x r = SOME (n2w a) /\
    safe_operand s5 (Var p) /\ safe_operand s5 (Var x) /\ safe_operand s5 ok /\
    eval_operand ok r = SOME (if success then 1w else 0w) /\
    op_taint (step_taint (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) u r tn1) ok = {} /\
    (!i. i < b \/ b+kbuf <= i ==>
      (i IN (step_taint (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) u r tn1).t_mem <=>
       i IN tn1.t_mem)) /\
    (!D j. inst_seq_ptr D lo ctx func PG G1 tn1
      [mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]]
      (u with vs_inst_idx := j)
      (step_prov PG G1 (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) r)
      (step_taint (mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]) u r tn1))
Proof
  rpt strip_tac >>
  drule_all bodyPtrIfExpAllocCompilerTheory.compile_alloc_buffer_raw_step >>
  disch_then (qx_choose_then `p` (qx_choose_then `r` strip_assume_tac)) >>
  drule_all bodyPtrIfExpAllocSourceTheory.compile_alloc_buffer_raw_resources >>
  strip_tac >>
  drule_all abiBufferAllocationCodeTheory.compile_alloc_buffer_code >>
  strip_tac >>
  `not_local_ptr cenv es.scopes p` by
    (irule exprSimOperandsTheory.fresh_not_local_ptr >> qexists_tac `s4` >>
     gvs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  `u.vs_memory = r.vs_memory` by simp[] >>
  drule_all allocationPtrTheory.alloca_step_site >>
  disch_then (qx_choose_then `b` strip_assume_tac) >>
  `p = STRING #"%" (toString s4.cs_next_var)` by
    (qpat_assum `buf.buf_operand = Var p` mp_tac >>
     qpat_assum `buf.buf_operand = Var _` mp_tac >> simp[]) >>
  `emitted_insts s4 s5 =
      [mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]]` by
    (qpat_assum `emitted_insts s4 s5 = _` mp_tac >>
     qpat_assum `p = _` (fn th => pure_rewrite_tac[th]) >> simp[]) >>
  `!v. not_fresh_at s4 v ==> v <> p` by
    (pure_once_rewrite_tac [loweringStateRelDefsTheory.not_fresh_at_def] >>
     gen_tac >> disch_then (qspec_then `s4.cs_next_var` mp_tac) >>
     qpat_assum `p = _` (fn th => simp_tac (srw_ss()) [th])) >>
  `!op v. safe_operand s4 op /\ op = Var v ==> v <> p` by
    (pure_rewrite_tac [exprSafeOperandTheory.safe_operand_def] >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `op = Var v` SUBST_ALL_TAC >>
     first_x_assum irule >> simp[]) >>
  `x <> p` by
    (qpat_assum `!op v. safe_operand s4 op /\ _ ==> _` (qspecl_then [`Var x`,`x`] irule) >> simp[]) >>
  `!v. ok = Var v ==> v <> p` by
    (qpat_assum `!op v. safe_operand s4 op /\ _ ==> _` (qspec_then `ok` mp_tac) >>
     qpat_assum `safe_operand s4 ok` (fn th => simp_tac bool_ss [th])) >>
  (* Both ghost frames refer to the same literal allocation and row. *)
  drule_all bodyPtrMakeArrayAllocBufferTheory.literal_alloca_old_ghost >>
  disch_then (qspecl_then [`tn1`,`PG`,`G1`] strip_assume_tac) >>
  drule_all (Q.INST [`tn1` |-> `step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s u tn`]
    bodyPtrMakeArrayAllocBufferTheory.literal_alloca_exterior_taint |> SIMP_RULE bool_ss []) >>
  disch_then (qspec_then `tn1` strip_assume_tac) >>
  qexistsl_tac [`p`,`r`,`b`] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `emitted_insts s4 s5 = _`
        (fn th => pure_rewrite_tac[th]) >>
      qpat_assum `step_inst_base _ _ = OK r`
        (fn th => pure_rewrite_tac[th]) >>
      simp[exprLoweringPropsTheory.run_inst_seq_def])
  >- first_assum ACCEPT_TAC
  >- (irule exprSimHashTheory.wb_frame_allocating_tail >>
      conj_tac
      >- first_assum ACCEPT_TAC
      >- (qexistsl_tac [`u`,`es.scopes`,`s4`] >>
          rpt conj_tac
          >- (qpat_assum `r.vs_memory = _` (fn th => pure_rewrite_tac[th]) >> simp[])
          >- first_assum ACCEPT_TAC
          >- (qpat_assum `r.vs_memory = _` (fn th => pure_rewrite_tac[th]) >> simp[])
          >- first_assum ACCEPT_TAC
          >- first_assum ACCEPT_TAC
          >- first_assum ACCEPT_TAC
          >- first_assum ACCEPT_TAC
          >- simp[]))
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `eval_operand (Var p) r = _` mp_tac >>
      simp_tac (srw_ss()) [venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (irule bodyLiteralBufferMemoryTheory.literal_alloca_frontier >>
      qexistsl_tac [`s4.cs_next_id`,`[Lit (n2w kbuf)]`,`[p]`] >>
      qpat_assum `step_inst_base _ _ = OK r` (fn th =>
        simp_tac (srw_ss()) [exprLoweringPropsTheory.run_inst_seq_def,th]))
  >- first_assum ACCEPT_TAC
  >- (irule frameActivationSeparationTheory.allocas_from_step >>
      qexistsl_tac [`ctx`,`0`,`mk_inst s4.cs_next_id ALLOCA [Lit (n2w kbuf)] [p]`,`u`] >>
      qpat_assum `step_inst_base _ u = OK r` (fn th =>
        simp_tac (srw_ss()) [venomExecSemanticsTheory.step_inst_non_invoke,
          venomInstTheory.mk_inst_def,
          REWRITE_RULE [venomInstTheory.mk_inst_def] th]) >>
      conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC)
  >- (drule_all allocationPtrTheory.alloca_step_old_ptr_covers >> simp_tac bool_ss [])
  >- (drule_all allocationPtrTheory.alloca_step_ptr_covers >> simp_tac bool_ss [])
  >- (`a + L <= u.vs_alloca_next` by
        (qpat_assum `stmt_state_rel _ _ _ _ _ _ u`
           (mp_then Any mp_tac stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
         simp_tac (srw_ss()) [alloca_inv_def,alloca_next_valid_def] >>
         strip_tac >> first_x_assum drule >> simp[]) >>
      `n <= ((n+31) DIV 32)*32` by
        (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
         simp_tac (srw_ss()) [vfmConstantsTheory.word_size_def,arithmeticTheory.MULT_COMM]) >>
      `!i. a <= i /\ i < a + val_footprint (BaseTV (BytesT (Dynamic n))) (BytesV bs) ==>
           i < u.vs_alloca_next` by
        (simp_tac (srw_ss()) [loweringPostsTheory.val_footprint_def] >> decide_tac) >>
      gen_tac >> strip_tac >>
      irule bodyPtrIfExpAllocFrameTheory.alloca_step_robust_below_frontier >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`s4.cs_next_id`,`kbuf`,`p`,`u`,`r`,`tn1`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (gen_tac >> strip_tac >>
      `v <> p` by
        (qpat_assum `!v. not_fresh_at s4 v ==> v <> p` irule >> first_assum ACCEPT_TAC) >>
      conj_tac >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
      first_x_assum drule >> simp_tac bool_ss [])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (first_x_assum irule >> first_assum ACCEPT_TAC)
  >- (`not_fresh_at s4 x` by
        (qpat_assum `safe_operand s4 (Var x)` mp_tac >>
         simp_tac (srw_ss()) [exprSafeOperandTheory.safe_operand_def]) >>
      qpat_assum `!v. not_fresh_at s4 v ==> lookup_var v r = _` drule >> simp[])
  >- (drule exprSafeOperandTheory.alloc_buffer_safe_operand >>
      qpat_assum `buf.buf_operand = Var p` (fn th => simp_tac bool_ss [th]))
  >- (irule exprSafeOperandTheory.safe_operand_mono >> qexists_tac `s4` >> simp[])
  >- (irule exprSafeOperandTheory.safe_operand_mono >> qexists_tac `s4` >> simp[])
  >- (`eval_operand ok r = eval_operand ok u` by
        (irule allocationPtrTheory.alloca_step_operand_preserved >>
         qexistsl_tac [`s4.cs_next_id`,`kbuf`,`p`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[])
  >- (qpat_assum `op_taint tn1 ok = {}` (fn th => pure_rewrite_tac[GSYM th]) >>
      irule bodyPtrIfExpAllocSourceTheory.alloca_step_operand_taint >>
      first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- (`ctx_has_dalloca ctx ==> allocas_below_fmp u` by
        (qpat_assum `ctx_has_dalloca ctx ==> _` mp_tac >> tautLib.TAUT_TAC) >>
      rpt gen_tac >> irule bodyFullAllocGenericTheory.inst_seq_ptr_lower_bound_from_alloca_next >>
      conj_tac >- simp[] >>
      conj_tac >- simp_tac (srw_ss()) [venomInstTheory.mk_inst_def] >>
      conj_tac >- (qpat_assum `allocas_from lo u` mp_tac >> simp_tac (srw_ss()) [ptrDisciplineTheory.allocas_from_def]) >>
      qexists_tac `0` >> simp_tac (srw_ss()) [] >>
      drule_all bodyPtrPrecompileBuiltinsStagingTheory.allocated_buffer_checked_cursors >>
      simp[])
QED
