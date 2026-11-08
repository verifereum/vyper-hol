(* Allocation ownership and robust input transport at dynamic tuple entry. *)
Theory logTupleEntryPtr
Ancestors
  logCursorAllocPtr logAllocFramePtr logMembersInvariantPtr logDataAllocPtr
  stmtSimLogTrace fragGasSeqPtr ASCIInumbers string instIdxIndep codegenRel
  abiDecoderReentry appendStorageGhostPtr
  stmtSimLogEncodeLayout abiEncoderComplexDynamic abiEncoderInput
  allocationPtr loweringHalt bodyPtrDefs abiBuiltinAllocation emitHelperProps exprLoweringProps
  context compileEnv venomExecSemantics venomState venomInst ptrDiscipline ptrSafeRun
  finite_map words list arithmetic pred_set

(* ALLOCA can taint its own newly registered bytes, never exterior bytes. *)
Theorem alloca_step_taint_outside_site:
  stmt_state_rel ctx func ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword(:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
  FLOOKUP t.vs_allocas id = SOME (p,n) ==>
  !tn.
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_imm = tn.t_imm /\
    (!i. ~(p <= i /\ i < p+n) ==>
      (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem <=>
       i IN tn.t_mem))
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`[]`,`FEMPTY`] assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, FLOOKUP_UPDATE] >> simp[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >> gvs[] >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`,`[]`,`FEMPTY`] assume_tac) >> simp[]
QED

(* The layout constructor needs no initialization of destination bytes when the
   processed prefix is empty.  Only source robustness and output capacity matter. *)
Theorem log_tuple_layout_entry:
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos /\
  (!q. mem_agree_outside m mem q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q) /\
  mem_agree_outside writes mem' mem /\
  (!i. sb <= i /\ i < sb+abi_encoder_member_span infos ==> i NOTIN writes) /\
  (!i. sb <= i /\ i < sb+abi_encoder_member_span infos ==> (i IN m' <=> i IN m)) /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= cap ==>
  log_members_layout infos tys avs [] [] sb 0 0 d
    (SUM (MAP (\(_,asz,_,_). asz) infos)) cap mem' /\
  (!q. mem_agree_outside m' mem' q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q)
Proof
  strip_tac >>
  `!q. mem_agree_outside m' mem' q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q` by
    (rpt strip_tac >> irule robust_abi_encoder_input_separated_write >>
     qexistsl_tac [`m`,`m'`,`mem`,`mem'`,`writes`] >> asm_simp_tac bool_ss []) >>
  `abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) mem'` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule abi_encoder_complex_input_metadata >> strip_tac >>
  conj_tac >- (asm_rewrite_tac[] >> irule log_members_layout_initial >> simp[] >>
    qexists_tac `abi_encoder_member_span infos` >> simp[]) >>
  first_assum ACCEPT_TAC
QED

(* Ghost fields omitted by the semantic allocation/init boundary. *)
Theorem log_cursor_prefix_frames:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;Lit w] sm = ((),sb) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t /\
  inst_seq_ptr D 0 ctx func PG G tn
    (emitted_insts sa sm ++ emitted_insts sm sb) s Gf tm /\
  FLOOKUP t.vs_allocas sa.cs_next_id = SOME (p,32) ==>
  (!x. x <> STRING #"%" (toString sa.cs_next_var) ==>
    FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (!i. ~(p <= i /\ i < p+32) ==> (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule_all log_buffer_trace_code >> strip_tac >>
  gvs[run_inst_seq_def, inst_seq_ptr_def, AllCaseEqs()] >>
  `32 < dimword(:256)` by simp[dimword_def] >>
  drule alloca_step_old_ghost >>
  disch_then (qspecl_then [`ss'`,
    `STRING #"%" (toString sa.cs_next_var)`,`32`,`sa.cs_next_id`] mp_tac) >>
  simp[] >> disch_then (qspecl_then [`PG`,`G`,`tn`] assume_tac) >>

  gvs[step_inst_inst_idx_indep, mk_inst_def, is_terminator_def,
      exec_result_map_def] >>
  qpat_x_assum `step_inst_base _ ss' = OK t` mp_tac >>
  simp[Once step_inst_base_def, exec_write2_def, eval_operand_def,
       AllCaseEqs()] >> strip_tac >>
  `FLOOKUP ss'.vs_allocas sa.cs_next_id = SOME (p,32)` by gvs[mstore_def] >>
  `!tt. (step_taint
     (mk_inst sa.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sa.cs_next_var)]) s ss' tt).t_stor = tt.t_stor /\
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sa.cs_next_var)]) s ss' tt).t_trans = tt.t_trans /\
    (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sa.cs_next_var)]) s ss' tt).t_imm = tt.t_imm /\
    (!i. ~(p <= i /\ i < p+32) ==> (i IN (step_taint
       (mk_inst sa.cs_next_id ALLOCA [Lit (n2w 32)]
       [STRING #"%" (toString sa.cs_next_var)]) s ss' tt).t_mem <=> i IN tt.t_mem))` by
    (irule alloca_step_taint_outside_site >> simp[mk_inst_def] >> metis_tac[]) >>
  `?b. FLOOKUP ss'.vs_allocas sa.cs_next_id = SOME (b,32) /\
    b+32 < dimword(:256) /\
    eval_operand (Var (STRING #"%" (toString sa.cs_next_var))) ss' = SOME (n2w b)` by
    (irule alloca_step_site >> simp[mk_inst_def] >> metis_tac[]) >>
  gvs[eval_operand_def] >>
  gvs[mk_inst_def] >>
  qmatch_goalsub_abbrev_tac `step_prov PG ga _ _` >>
  qmatch_goalsub_abbrev_tac `step_taint _ ss' _ ta` >>
  simp[step_prov_def, set_prov_def, mk_inst_def, step_taint_def,
       set_var_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, written_taint_def, range_bytes_def,
       new_site_bytes_def, eval_operand_def, mstore_def, op_taint_def,
       w2n_n2w] >>
  gvs[FLOOKUP_DEF, DRESTRICT_UNIV, GSYM op_taint_def] >>
  qpat_x_assum `!tt. _` (qspec_then `tn` mp_tac) >>
  simp[GSYM (markerTheory.Abbrev_def)] >>
  strip_tac >> gvs[op_taint_def, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem log_cursor_prefix_fresh:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;Lit w] sm = ((),sb) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sm.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~ctx_has_dalloca ctx /\
  run_inst_seq (emitted_insts sa sm ++ emitted_insts sm sb) s = OK t ==>
  fresh_vars_wrt limit_st t
Proof
  strip_tac >> `32 < dimword(:256)` by simp[dimword_def] >>
  drule_all log_buffer_seq_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ t' = OK t` mp_tac >>
  simp[Once step_inst_base_def, mk_inst_def, exec_write2_def,
       eval_operand_def, AllCaseEqs()] >>
  strip_tac >> gvs[fresh_vars_wrt_def, mstore_def]
QED

Theorem log_tuple_cursor_entry:
  compile_alloc_buffer 32 sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;Lit (n2w hl)] sm = ((),final) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  sm.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~ctx_has_dalloca ctx /\
  srcid <> sa.cs_next_id /\ dstid <> sa.cs_next_id /\
  FLOOKUP s.vs_allocas srcid = SOME (sb,srcCap) /\
  FLOOKUP s.vs_allocas dstid = SOME (d,cap) /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME (n2w sb) /\ lookup_var dst s = SOME (n2w d) /\
  ptr_covers G tn src s srcCap /\ ptr_covers G tn dst s cap /\
  sb+srcCap < dimword(:256) /\ d+cap < dimword(:256) /\
  (sb+srcCap <= d \/ d+cap <= sb) /\
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos /\
  (!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
      (abi_encoder_member_span infos) q) /\
  abi_encoder_member_span infos <= srcCap /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= cap /\
  hl = SUM (MAP (\(_,asz,_,_). asz) infos) ==>
  ?t p H tm dp.
    run_inst_seq (emitted_insts sa sm ++ emitted_insts sm final) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn
      (emitted_insts sa sm ++ emitted_insts sm final) s H tm /\
    buf.buf_operand = Var dp /\ buf.buf_size = 32 /\
    fresh_vars_wrt limit_st t /\ inst_extends sa sm /\ inst_extends sm final /\
    not_fresh_at final src /\ not_fresh_at final dst /\ not_fresh_at final dp /\
    log_members_layout infos tys avs [] [] sb 0 0 d hl cap t.vs_memory /\
    (!q. mem_agree_outside tm.t_mem t.vs_memory q ==>
      abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
        (abi_encoder_member_span infos) q) /\
    lookup_var src t = SOME (n2w sb) /\ lookup_var dst t = SOME (n2w d) /\
    lookup_var dp t = SOME (n2w p) /\ mload p t = n2w hl /\
    ptr_covers H tm src t srcCap /\ ptr_covers H tm dst t cap /\
    ptr_covers H tm dp t 32 /\ p+32 < dimword(:256) /\
    (sb+abi_encoder_member_span infos <= d \/ d+cap <= sb) /\
    (sb+abi_encoder_member_span infos <= p \/ p+32 <= sb) /\
    (d+cap <= p \/ p+32 <= d) /\
    (!i. p <= i /\ i < p+32 ==> i NOTIN tm.t_mem) /\
    mem_agree_outside {i | p <= i /\ i < p+32} t.vs_memory s.vs_memory /\
    (!i. ~(p <= i /\ i < p+32) ==> (i IN tm.t_mem <=> i IN tn.t_mem)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all log_cursor_allocate_init_seq_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`] strip_assume_tac) >>
  `fresh_vars_wrt limit_st t` by (irule log_cursor_prefix_fresh >> metis_tac[]) >>
  drule_all log_cursor_prefix_frames >> strip_tac >>
  `(p+32 <= sb \/ sb+srcCap <= p) /\ (p+32 <= d \/ d+cap <= p)` by
    metis_tac[log_cursor_registered_buffers_separate] >>
  `!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     `x <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[not_fresh_at_def, LESS_EQ_REFL] >>
     `abi_decoder_operand_live sa.cs_next_var (Var x)` by
       (simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
        metis_tac[not_fresh_at_def]) >>
     first_x_assum (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def] >> metis_tac[]) >>
  `ptr_covers Gf tm src t srcCap /\ ptr_covers Gf tm dst t cap` by
    (conj_tac >> irule ptr_covers_old_transport >>
     qexistsl_tac [`G`,`s`,`sa`,`tn`] >> asm_simp_tac bool_ss [] >>
     rpt strip_tac >> metis_tac[]) >>
  `log_members_layout infos tys avs [] [] sb 0 0 d hl cap t.vs_memory /\
   (!q. mem_agree_outside tm.t_mem t.vs_memory q ==>
      abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb
        (abi_encoder_member_span infos) q)` by
    (asm_rewrite_tac[] >> irule log_tuple_layout_entry >>
     asm_simp_tac bool_ss [] >> qexistsl_tac [`tn.t_mem`,`s.vs_memory`, `{i | p <= i /\ i < p+32}`] >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     fs[IN_GSPEC_IFF] >>
     `~(p <= i /\ i < p+32)` by decide_tac >> metis_tac[]) >>
  `not_fresh_at final src /\ not_fresh_at final dst /\ not_fresh_at final out` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     `sa.cs_next_var < final.cs_next_var` by decide_tac >>
     conj_tac >- (fs[not_fresh_at_def] >> rpt strip_tac >>
       first_x_assum irule >> decide_tac) >>
     conj_tac >- (fs[not_fresh_at_def] >> rpt strip_tac >>
       first_x_assum irule >> decide_tac) >>
     `out = STRING #"%" (toString sa.cs_next_var)` by
       (qpat_x_assum `buf.buf_operand = Var out` mp_tac >>
        asm_simp_tac bool_ss [operand_11]) >>
     asm_rewrite_tac[] >> rewrite_tac[not_fresh_at_def] >>
     simp[ASCIInumbersTheory.toString_11] >> decide_tac) >>
  qexistsl_tac [`t`,`p`,`Gf`,`tm`,`out`] >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >> decide_tac
QED
