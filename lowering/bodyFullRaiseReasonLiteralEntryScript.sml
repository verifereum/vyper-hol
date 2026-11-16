(* Annotation-capacity literal shortcut: one endpoint and ghosts for all H. *)
Theory bodyFullRaiseReasonLiteralEntry
Ancestors
  reasonLiteralBufferPtr exprSimPtrLiteralBuffer exprSimUnwrapProps exprSimMemDefs
  reasonCompilerProps instSeqPtrLo fragGasOriginPtrLoop fragGasSeqPtr
  stmtReasonLitMemory allocaHistoryFragment bodyFullUnwrapSlotPost
  exprSimHyps vyperTypeSystem vyperAST valueEncodingDefs exprSimHash
  venomState venomInst words vyperValue
  bodyPtrDefs vyperStorageFootprint loweringStateRelDefs
  exprSimHypsDefs stmtLowering exprLowering context compileEnv list

Theorem reason_literal_entry_source_family:
  compile_bytelike_literal (MAP (n2w o ORD) str) ml sa = (buf,sb) /\
  expr_body_pre cenv cx env (Literal (BaseT (StringT ml)) (StringL str)) es /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  32+32*word_size ml < dimword (:256) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?t p Gf tnf.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    buf.buf_operand = Var p /\
    !H. valid_horizon cx st0 H es.storage_trace ==>
      inst_seq_ptr (DF H) lo ctx func PG G tn (emitted_insts sa sb) s Gf tnf /\
      expr_post H ctx func cenv cx (Literal (BaseT (StringT ml)) (StringL str))
        es sa sb s es (StringV str) (Var p)
        (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      ptr_val_ok cx (BaseT (StringT ml)) (StringV str) (Var p) Gf tnf
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  `LENGTH str <= ml` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def] >>
  `LENGTH (MAP (n2w o ORD) str : word8 list) <= ml` by simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by gvs[storage_trace_domain_def] >>
  first_assum (drule_then strip_assume_tac) >>
  drule_all reason_literal_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`,`func`,`PG`,`G`,`DF (storage_trace_horizon es.storage_trace)`]
    (strip_assume_tac o REWRITE_RULE [LENGTH_MAP])) >>
  qexistsl_tac [`t`,`p`,`G'`,`tn'`] >> simp[NoAsms] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  drule_all reason_literal_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`,`func`,`PG`,`G`,`DF H`]
    (strip_assume_tac o REWRITE_RULE [LENGTH_MAP])) >>
  qpat_x_assum `run_inst_seq _ _ = OK t'` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >> gvs[] >>
  `G'' = G' /\ tn'' = tn'` by
    (irule inst_seq_ptr_ghost_unique >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >> gvs[] >>
  conj_tac >- (irule inst_seq_ptr_zero_to_lo >>
    qpat_assum `!H. valid_horizon _ _ H _ ==> _`
      (drule_then strip_assume_tac) >>
    fs[ghost_inv_at_def] >>
    qexists_tac `DF H` >> simp[]) >>
  `word_size (LENGTH str) <= word_size ml` by
    metis_tac[exprSimPropsTheory.word_size_monotone] >>
  `b < dimword (:256)` by decide_tac >>
  `val_wf (BaseTV (StringT ml)) (StringV str) /\
   val_in_memory (BaseTV (StringT ml)) (StringV str) b t.vs_memory /\
   val_footprint (BaseTV (StringT ml)) (StringV str) <= 32+32*word_size (LENGTH str) /\
   (!i. b <= i /\ i < b+val_footprint (BaseTV (StringT ml)) (StringV str) ==>
      i NOTIN tn'.t_mem) /\
   val_store_size (BaseTV (StringT ml)) (StringV str) = 32+32*word_size (LENGTH str)` by
    (irule literal_ptr_string_representation >> simp[] >>
     qexists_tac `tn with t_mem := tn.t_mem UNION dirty'` >> simp[]) >>
  conj_tac >- suspend "source" >> suspend "pointer"
QED

Resume reason_literal_entry_source_family[pointer]:
  `lookup_var p t = SOME (n2w b)` by
    (qpat_assum `!x. not_fresh_at sh x ==> _` drule >> simp[]) >>
  fs[lookup_var_def] >>
  simp[ptr_val_ok_def, is_word_type_def] >>
  irule literal_clean_ptr_mem_ok >>
  qexistsl_tac [`b`, `32+32*word_size ml`, `n2w b`] >>
  simp[lookup_var_def, w2n_n2w, evaluate_type_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED

Resume reason_literal_entry_source_family[source]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  drule reason_literal_compiler_shape >> strip_tac >>
  `vv_post H ctx func cenv cx (Literal (BaseT (StringT ml)) (StringL str))
     es sa sb s es (Value (StringV str))
     (LocatedValue (expr_type (Literal (BaseT (StringT ml)) (StringL str))) (base_ptr buf))
     (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule literal_ptr_memory_vv_frame_post >>
     simp[expr_type_def, evaluate_type_def, loweringPostsTheory.post_value_type_def, is_word_type_def] >>
     qexistsl_tac [`32+32*word_size ml`, `p`, `sh'`, `u'`, `n2w b`] >>
     simp[w2n_n2w] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (rpt strip_tac >>
       qpat_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _` irule >>
       decide_tac) >>
     conj_tac >- (`p' = p` by gvs[eval_operand_def] >>
       qpat_assum `!x. not_fresh_at sh' x ==> _`
         (qspec_then `p` mp_tac) >> gvs[eval_operand_def]) >>
     conj_tac >- (qspec_then `ml` mp_tac exprSimPropsTheory.le_word_size_mul >> decide_tac) >>
     conj_tac >- (simp[type_slot_size_def] >> decide_tac) >>
     irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
     goal_assum (drule_at Any) >> gvs[]) >>
  drule expr_post_of_vv_post_memory >> gvs[base_ptr_def, expr_type_def, is_word_type_def]
QED

Finalise reason_literal_entry_source_family

Theorem reason_literal_message_full_entry:
  compile_bytelike_literal (MAP (n2w o ORD) str) ml sa = (buf,sb) /\
  expr_body_pre cenv cx env (Literal (BaseT (StringT ml)) (StringL str)) es /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  32+32*word_size ml < dimword (:256) /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?t p Gf tnf.
    compile_reason_message cenv (Literal (BaseT (StringT ml)) (StringL str)) sa =
      (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf),sb) /\
    buf.buf_operand = Var p /\
    vv_operand (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf)) = Var p /\
    vv_location (LocatedValue (BaseT (StringT (LENGTH str))) (base_ptr buf)) = SOME LocMemory /\
    not_fresh_at sb p /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_kept_at lo cenv es sa G tn s Gf tnf /\
    expr_store_bound cx (BaseT (StringT (LENGTH str))) (StringV str) (Var p) t /\
    ptr_val_ok cx (BaseT (StringT (LENGTH str))) (StringV str) (Var p) Gf tnf t /\
    ptr_val_ok cx (BaseT (StringT ml)) (StringV str) (Var p) Gf tnf t /\
    ptr_buf_ok cenv (Literal (BaseT (StringT ml)) (StringL str)) (Var p) Gf t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tnf) /\
      expr_post H ctx func cenv cx (Literal (BaseT (StringT ml)) (StringL str))
        es sa sb s es (StringV str) (Var p) t /\
      ghost_inv_at (DF H) lo d cenv cx es Gf tnf t)
Proof
  strip_tac >>
  drule_all reason_literal_entry_source_family >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `LENGTH str <= ml` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_literal_def] >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by gvs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule reason_literal_compiler_shape >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s /\
   s.vs_alloca_next <= t.vs_alloca_next /\
   t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (`MEM (mk_inst sa.cs_next_id ALLOCA
        [Lit (n2w (32+32*word_size ml))] [STRING #"%" (toString sa.cs_next_var)])
        (fn_insts func)` by
       (irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
        goal_assum (drule_at Any) >> gvs[]) >>
     `alloca_room ctx func s /\ alloca_next_valid s /\
      (!x. FLOOKUP s.vs_allocas sa.cs_next_id = SOME x ==>
        SND x = 32+32*word_size ml)` by
       (conj_tac >- metis_tac[exprLoweringPropsTheory.stmt_state_rel_def] >>
        conj_tac >- metis_tac[exprLoweringPropsTheory.stmt_state_rel_def,
          venomMemDefsTheory.alloca_inv_def] >>
        rpt strip_tac >> Cases_on `x` >>
        drule_all allocationPtrTheory.stmt_state_rel_alloca_site_bound >> simp[]) >>
     drule bytelike_literal_run_mem >>
     disch_then (qspecl_then [`ctx`,`func`,`s`] mp_tac) >>
     (impl_tac >-
       (`32+(ml+31) DIV 32*32 = 32+32*word_size ml` by
          simp_tac std_ss [vfmConstantsTheory.word_size_def, arithmeticTheory.MULT_COMM] >>
        asm_rewrite_tac[LENGTH_MAP])) >>
     strip_tac >> gvs[]) >>
  `LENGTH (MAP (n2w o ORD) str : word8 list) <= ml` by simp[] >>
  drule_all reason_literal_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`,`func`,`PG`,`G`,`DF (storage_trace_horizon es.storage_trace)`]
    (strip_assume_tac o REWRITE_RULE [LENGTH_MAP])) >>
  `t' = t` by gvs[] >>
  qpat_x_assum `t' = t` SUBST_ALL_TAC >>
  `G' = Gf /\ tn' = tnf` by
    (irule inst_seq_ptr_ghost_unique >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     `inst_seq_ptr (DF (storage_trace_horizon es.storage_trace)) lo ctx func PG G tn
       (emitted_insts sa sb) s G' tn'` by
       (irule inst_seq_ptr_zero_to_lo >>
        qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
          (drule_then strip_assume_tac) >>
        fs[ghost_inv_at_def] >>
        qexists_tac `DF (storage_trace_horizon es.storage_trace)` >> gvs[]) >>
     goal_assum (drule_at Any) >>
     qexists_tac `DF (storage_trace_horizon es.storage_trace)` >> simp[]) >>
  qpat_x_assum `G' = Gf` SUBST_ALL_TAC >>
  qpat_x_assum `tn' = tnf` SUBST_ALL_TAC >>
  `MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32+32*word_size ml))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
     goal_assum (drule_at Any) >> gvs[]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _ u` mp_tac >>
  drule_all exprSimLiteralBufferTheory.alloc_buffer_frame_run >> strip_tac >> disch_tac >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (32+32*word_size ml))] [p']) s = OK t'` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = _` mp_tac >>
     simp[exprLoweringPropsTheory.run_inst_seq_def, mk_inst_def, is_terminator_def, AllCaseEqs()]) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `allocas_from lo t' /\ lo <= t'.vs_alloca_next` by
    (irule ptrSafetyTransportTheory.step_inst_allocas_from >>
     qexistsl_tac [`ctx`,`0`,`mk_inst sa.cs_next_id ALLOCA
       [Lit (n2w (32+32*word_size ml))] [p']`,`s`] >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke, mk_inst_def]) >>
  `word_size (LENGTH str) <= word_size ml` by
    metis_tac[exprSimPropsTheory.word_size_monotone] >>
  `lookup_var p' t' = SOME (n2w (w2n w))` by
    gvs[eval_operand_def] >>
  `run_inst_seq (mk_inst sm.cs_next_id MSTORE [Var p'; Lit (n2w (LENGTH (MAP (n2w o ORD) str)))] [] ::
      emitted_insts sh sb) t' = OK t` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >>
     qpat_assum `emitted_insts sa sb = _` (fn th => pure_once_rewrite_tac [th]) >>
     pure_rewrite_tac [APPEND, exprLoweringPropsTheory.run_inst_seq_def] >>
     asm_rewrite_tac[venomExecSemanticsTheory.exec_result_case_def] >> simp[]) >>
  `w2n w+32+32*word_size (LENGTH (MAP (n2w o ORD) str : word8 list)) < dimword (:256)` by
    (simp[LENGTH_MAP] >> decide_tac) >>
  `t with <|vs_vars := t'.vs_vars; vs_memory := t'.vs_memory|> = t'` by
    (irule (cj 4 exprSimPtrLiteralPayloadTheory.literal_header_chunks_functional) >>
     qexistsl_tac [`w2n w`,`MAP (n2w o ORD) str : word8 list`,`sm.cs_next_id`,`p'`,`sb`,`sh`] >>
     gvs[]) >>
  `t'.vs_allocas = u.vs_allocas` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
     qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = t'` mp_tac >>
     simp_tac std_ss [venom_state_component_equality, venom_state_accfupds] >>
     rpt strip_tac >> simp[]) >>
  `w2n w = b` by
    (qpat_x_assum `FLOOKUP t'.vs_allocas _ = SOME _` mp_tac >> simp[]) >>
  `lo <= b` by
    (fs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`p`,`Gf`,`tnf`] >>
  simp_tac bool_ss [venom_state_accfupds, venom_state_fupdfupds] >>
  conj_tac >- (simp[compile_reason_message_def, comp_bind_def, comp_return_def] >>
    gvs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- gvs[vv_operand_def, base_ptr_def] >>
  conj_tac >- simp[vv_location_def, base_ptr_def] >>
  conj_tac >- suspend "fresh" >>
  conj_tac >- suspend "history" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- simp[] >>
  conj_tac >- (gvs[exprLoweringPropsTheory.same_blocks_def]) >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "kept" >>
  conj_tac >- suspend "store" >>
  conj_tac >- suspend "actualptr" >>
  conj_tac >- suspend "annotatedptr" >>
  conj_tac >- suspend "buf" >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >- suspend "path" >>
  conj_tac >- first_assum ACCEPT_TAC >> suspend "inv"
QED

Resume reason_literal_message_full_entry[fresh]:
  `sh.cs_next_var <= sb.cs_next_var` by
    (mp_tac exprLoweringPropsTheory.ci_mono_compile_store_byte_chunks >>
     disch_then (qspecl_then [`Var p'`,`MAP (n2w o ORD) str`,`32`,`sh`] mp_tac) >>
     asm_rewrite_tac[pairTheory.SND, exprLoweringPropsTheory.ci_mono_def] >> simp[]) >>
  irule freshWritesTheory.not_fresh_at_mono >>
  qexists_tac `sh` >> gvs[]
QED
Resume reason_literal_message_full_entry[history]:
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[exprLoweringPropsTheory.same_blocks_def] >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `LENGTH sb.cs_current_insts = s.vs_inst_idx + LENGTH (emitted_insts sa sb)` by
    simp[] >> pop_assum SUBST1_TAC >>
  irule alloca_history_run_inst_seq >>
  goal_assum (drule_at (Pat `run_inst_seq _ _ = _`)) >>
  fs[exprLoweringPropsTheory.stmt_state_rel_def, rich_listTheory.IS_PREFIX_APPEND] >>
  qpat_x_assum `EVERY _ (emitted_insts sa sb)` mp_tac >>
  asm_rewrite_tac[EVERY_APPEND, EVERY_DEF, mk_inst_def] >>
  simp[EVERY_MEM, is_terminator_def]
QED
Resume reason_literal_message_full_entry[kept]:
  `!name a len. local_region cenv es.scopes s name a len ==>
      regions_disjoint b (32+32*word_size ml) a len` by
    (drule_all literal_ptr_local_region_frame >> metis_tac[]) >>
  `ghost_kept cenv es sa G tn s Gf tnf` by
    (irule bodyPtrMakeArrayAllocationFrameTheory.ghost_kept_disjoint_taint_frame >>
     conj_tac >- (simp[ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
     qexistsl_tac [`b`,`32+32*word_size ml`] >>
     conj_tac >- metis_tac[] >>
     conj_tac >- metis_tac[] >>
     fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  `!i. i < lo /\ i IN tnf.t_mem ==> i IN tn.t_mem` by
    (gen_tac >> strip_tac >>
     `i NOTIN dirty` by
       (qpat_x_assum `dirty SUBSET _`
          (mp_tac o REWRITE_RULE [pred_setTheory.SUBSET_DEF]) >>
        disch_then (qspec_then `i` mp_tac) >> simp[] >> decide_tac) >>
     gvs[]) >>
  qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[ghost_kept_at_def, ghost_kept_def] >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume reason_literal_message_full_entry[store]:
  `word_size (LENGTH str) <= word_size ml` by
    metis_tac[exprSimPropsTheory.word_size_monotone] >>
  simp[exprSimMemDefsTheory.expr_store_bound_def, evaluate_type_def, is_word_type_def,
       eval_operand_def, lookup_var_def, exprSimPropsTheory.val_store_size_def] >>
  rpt strip_tac >>
  `lookup_var p t = SOME (n2w b)` by gvs[] >>
  `b+32+32*word_size ml <= u.vs_alloca_next` by
    (fs[exprLoweringPropsTheory.stmt_state_rel_def,
        venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. FLOOKUP u.vs_allocas aid = SOME (base,sz) ==> _`
       (drule_then assume_tac) >> gvs[]) >>
  `u.vs_alloca_next = t.vs_alloca_next` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
     simp_tac std_ss [venom_state_component_equality, venom_state_accfupds] >>
     rpt strip_tac >> simp[]) >>
  gvs[lookup_var_def, w2n_n2w] >> decide_tac
QED
Resume reason_literal_message_full_entry[actualptr]:
  `b < dimword (:256)` by decide_tac >>
  `word_size (LENGTH str) <= word_size ml` by
    metis_tac[exprSimPropsTheory.word_size_monotone] >>
  `val_wf (BaseTV (StringT (LENGTH str))) (StringV str) /\
   val_in_memory (BaseTV (StringT (LENGTH str))) (StringV str) b t.vs_memory /\
   val_footprint (BaseTV (StringT (LENGTH str))) (StringV str) <= 32+32*word_size (LENGTH str) /\
   (!i. b <= i /\ i < b+val_footprint (BaseTV (StringT (LENGTH str))) (StringV str) ==>
      i NOTIN tnf.t_mem) /\
   val_store_size (BaseTV (StringT (LENGTH str))) (StringV str) = 32+32*word_size (LENGTH str)` by
    (irule literal_ptr_string_representation >> simp[] >>
     qexists_tac `tn with t_mem := tn.t_mem UNION dirty` >> simp[]) >>
  `lookup_var p t = SOME (n2w b) /\ FLOOKUP Gf p = SOME (b,32+32*word_size ml)` by gvs[] >>
  simp[ptr_val_ok_def, is_word_type_def] >>
  conj_tac >- gvs[] >>
  fs[lookup_var_def] >>
  irule literal_clean_ptr_mem_ok >>
  qexistsl_tac [`b`, `32+32*word_size ml`, `n2w b`] >>
  simp[lookup_var_def, w2n_n2w, evaluate_type_def] >>
  rpt strip_tac >> gvs[] >> decide_tac
QED
Resume reason_literal_message_full_entry[annotatedptr]:
  metis_tac[]
QED
Resume reason_literal_message_full_entry[buf]:
  `b < dimword (:256)` by decide_tac >>
  `lookup_var p t = SOME (n2w b) /\ FLOOKUP Gf p = SOME (b,32+32*word_size ml)` by gvs[] >>
  fs[lookup_var_def] >>
  irule literal_site_ptr_buf_ok >>
  qexistsl_tac [`b`,`32+32*word_size ml`,`n2w b`] >>
  simp[lookup_var_def, w2n_n2w, lowered_value_type_def, expr_type_def,
       type_memory_bytes_def, type_slot_size_def] >>
  `word_size (LENGTH str) <= word_size ml` by
    metis_tac[exprSimPropsTheory.word_size_monotone] >>
  qpat_x_assum `word_size (LENGTH str) <= word_size ml` mp_tac >>
  simp_tac std_ss [vfmConstantsTheory.word_size_def]
QED
Resume reason_literal_message_full_entry[path]:
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[exprLoweringPropsTheory.same_blocks_def] >>
  drule_all stmtReasonLitFragMemoryTheory.fn_has_code_code >> strip_tac >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    gvs[] >>
  drule_all run_inst_seq_gas_origin_ptr_path >> simp[]
QED
Resume reason_literal_message_full_entry[inv]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  irule unwrap_slot_copy_ghost_inv_at >>
  simp_tac std_ss [venom_state_accfupds] >>
  conj_tac >- decide_tac >>
  conj_tac >- (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = t'` mp_tac >>
    simp_tac std_ss [venom_state_component_equality, venom_state_accfupds] >>
    rpt strip_tac >> gvs[ptrDisciplineTheory.allocas_from_def] >> metis_tac[]) >>
  conj_tac >- suspend "storinv" >>
  qexistsl_tac [`G`,`func`,`32+32*word_size ml`,`s`,`sa`,`b`,`tn`] >>
  simp_tac std_ss [venom_state_accfupds] >>
  conj_tac >- (drule_all literal_ptr_local_region_frame >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    `local_region cenv es.scopes t' name b' len` by metis_tac[] >>
    qpat_assum `!name b len. local_region _ _ t' _ _ _ ==> _` drule >>
    simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (gen_tac >> strip_tac >>
    `lookup_var x t = lookup_var x s` by
      (qpat_assum `!x. not_fresh_at sh' x ==> _` (qspec_then `x` mp_tac) >>
       qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _` (qspec_then `x` mp_tac) >>
       simp[] >> metis_tac[]) >>
    fs[lookup_var_def, ptrDisciplineTheory.op_taint_def]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_assum `!a len. _ ==> mem_bytes_at a len t.vs_memory = _` mp_tac >>
    disch_then (qspecl_then [`a`,`k`] mp_tac) >> simp[]) >>
  conj_tac >- suspend "taintinv" >>
  simp[] >> fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def]
QED
Resume reason_literal_message_full_entry[storinv]:
  `stor_taint_ok_at (DF H) tn s` by fs[ghost_inv_at_def] >>
  drule bodyPtrMakeArrayAllocBufferTheory.literal_alloca_static_frame >> strip_tac >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = t'` mp_tac >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = u` mp_tac >>
  simp_tac std_ss [venom_state_component_equality, venom_state_accfupds] >>
  rpt strip_tac >>
  fs[stor_taint_ok_at_def, exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def]
QED
Resume reason_literal_message_full_entry[taintinv]:
  gen_tac >> strip_tac >>
  `j NOTIN dirty` by
    (qpat_x_assum `dirty SUBSET _`
      (mp_tac o REWRITE_RULE [pred_setTheory.SUBSET_DEF]) >>
     disch_then (qspec_then `j` mp_tac) >> simp[] >> decide_tac) >>
  simp[] >> decide_tac
QED
Finalise reason_literal_message_full_entry
