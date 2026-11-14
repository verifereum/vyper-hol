(* Literal MethodId composition, conditional on the fixed endpoint data post. *)
Theory bodyFullBuiltinEnvMethodIdCompose
Ancestors
  bodyFullLiteralBuffer bodyFullExprGeneric bodyFullPreds bodyFullGhostFrame
  bodyFullUnwrapRun
  bodySimFull exprSimMemDefs fragGasOriginPtr fragGasSeqPtr ptrDiscipline venomState vyperStorageFootprint
  exprSimPrecompiles exprSimVVFrame loweringStateRelDefs exprSimWordArgs
  gasOutcomeFullCompose exprSimHash exprSimSource exprSimProps exprLoweringProps
  exprSimLiteralBuffer exprSimMemoryStack loweringPosts bodyPtrDefs
  bodyLiteralBufferMemory exprPtrUnwrapRetained stmtReasonLitFragMemory
  exprLowering compileEnv context vyperAST vyperInterpreter vyperState vyperValue
  vyperContext valueEncoding vyperTypeBytesCrypto words list finite_map

Theorem method_id_literal_dynamic_sim_full_from_endpoint:
  (!DF lo d ctx PG func cenv cx st0 es s0 G0 tn0 la l bs sa sb buf
    u t b p sh G' tn'.
    method_id_literal (Literal la l) = SOME bs /\
    compile_bytelike_literal (TAKE 4 (Keccak_256_w64 bs))
      (LENGTH (TAKE 4 (Keccak_256_w64 bs))) sa = (buf,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    buf.buf_operand = Var p /\ not_fresh_at sh p /\
    (!x. not_fresh_at sa x ==> not_fresh_at sh x) /\
    run_inst_seq (emitted_insts sa sb) s0 = OK t /\
    u.vs_memory = s0.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,64) /\ lo <= b /\
    (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid a len. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (a,len) ==>
       regions_disjoint b 64 a len) /\
    (!name a len. local_region cenv es.scopes u name a len ==>
       regions_disjoint b 64 a len) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s0) /\
    u.vs_labels = s0.vs_labels /\ wb_frame cenv es es sa s0 u /\
    (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory|>) = u /\
    LENGTH u.vs_memory <= LENGTH t.vs_memory /\
    (!x. not_fresh_at sh x ==> lookup_var x t = lookup_var x u) /\
    (!a len. a + len <= b \/ b + 64 <= a ==>
       mem_bytes_at a len t.vs_memory = mem_bytes_at a len u.vs_memory) /\
    FLOOKUP G' p = SOME (b,64) /\ lookup_var p t = SOME (n2w b) /\
    op_taint tn' (Var p) = {} /\ b + 64 < dimword (:256) /\
    mem_word_at b t.vs_memory = 4w /\
    mem_bytes_at (b + 32) 4 t.vs_memory = TAKE 4 (Keccak_256_w64 bs) /\
    tn'.t_mem = tn0.t_mem DIFF {i | b <= i /\ i < b + 64} /\
    tn'.t_stor = tn0.t_stor /\ tn'.t_trans = tn0.t_trans /\ tn'.t_imm = tn0.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G0 x /\
       FLOOKUP tn'.t_var x = FLOOKUP tn0.t_var x) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       inst_seq_ptr (DF H) lo ctx func PG G0 tn0 (emitted_insts sa sb) s0 G' tn' /\
       stmt_state_rel H ctx func cenv cx es u) ==>
    !H. valid_horizon cx st0 H es.storage_trace ==>
      vv_post H ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es sa sb s0
        es (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
        (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf)) t /\
      vv_store_bound cx (BaseT (BytesT (Dynamic 4))) (BaseT (BytesT (Dynamic 4)))
        es (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
        (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf)) t /\
      ghost_inv_at (DF H) lo d cenv cx es G' tn' t /\
      ptr_vv_ok cx (BaseT (BytesT (Dynamic 4)))
        (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
        (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf)) es G' tn' t /\
      ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l])
        buf.buf_operand G' t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn') ==>
  !DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty la l bs es.
    method_id_literal (Literal la l) = SOME bs ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es
Proof
  disch_then (mk_asm "endpoint" o SIMP_RULE (srw_ss())
    [LENGTH_TAKE, LENGTH_Keccak_256_w64, vfmConstantsTheory.word_size_def]) >>
  rpt gen_tac >> strip_tac >> conj_tac >>
  rw[expr_sim_full_def, expr_vv_sim_full_def] >>
  drule compile_expr_method_id_literal >>
  disch_then (qspecl_then [`cenv`, `ty`, `BaseT (BytesT (Dynamic 4))`, `sa`] assume_tac) >>
  gvs[lower_value_def, compile_literal_vv_def, comp_bind_def,
      unwrap_value_def, base_ptr_def, is_word_type_def, comp_return_def] >>
  pairarg_tac >>
  gvs[unwrap_value_def, is_word_type_def, comp_return_def] >>
  irule gas_outcome_full_initial_domain >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_bind,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >> strip_tac >>
  `32 + 32 * word_size (LENGTH (TAKE 4 (Keccak_256_w64 bs))) < dimword (:256)` by
    simp[LENGTH_TAKE, LENGTH_Keccak_256_w64, dimword_def,
         vfmConstantsTheory.word_size_def] >>
  drule literal_bytelike_full_run >>
  disch_then (qspecl_then [`DF`, `lo`, `d`, `PG`, `ctx`, `func`, `cenv`, `cx`, `st0`, `es`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (asm_x "endpoint" kall_tac >> simp[] >>
    gen_tac >> strip_tac >> first_x_assum drule >> simp[])) >> strip_tac >>
  fs[LENGTH_TAKE, LENGTH_Keccak_256_w64, vfmConstantsTheory.word_size_def] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
      vv_post H ctx func cenv cx
        (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es sa cs' s0
        es (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
        (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf)) t /\
      vv_store_bound cx (BaseT (BytesT (Dynamic 4))) (BaseT (BytesT (Dynamic 4)))
        es (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
        (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf)) t /\
      ghost_inv_at (DF H) lo d cenv cx es G' tn' t /\
      ptr_vv_ok cx (BaseT (BytesT (Dynamic 4)))
        (Value (BytesV (TAKE 4 (Keccak_256_w64 bs))))
        (LocatedValue (BaseT (BytesT (Dynamic 4))) (base_ptr buf)) es G' tn' t /\
      ptr_buf_ok cenv (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l])
        buf.buf_operand G' t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (simp[] >> asm "endpoint" MATCH_MP_TAC >> qexistsl_tac [`PG`, `u`, `b`, `sh`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm_x "endpoint" kall_tac >>
  `!st. eval_expr cx
    (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) st =
    (INL (Value (BytesV (TAKE 4 (Keccak_256_w64 bs)))),st)` by
    (gen_tac >> Cases_on `eval_expr cx
      (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) st` >>
     drule_all eval_expr_method_id_literal >> simp[]) >>
  irule gas_outcome_full_pure >> (reverse conj_tac >- simp[]) >>
  qrefinel [`G'`, `es`, `_`,
    `t with vs_inst_idx := LENGTH cs'.cs_current_insts`, `tn'`] >>
  simp[bind_def, read_result_def, return_def] >>
  qx_gen_tac `H` >> strip_tac >>
  drule_all literal_bytelike_counted_shape >> strip_tac >>
  drule_all bytelike_literal_shape >> strip_tac >>
  drule_all fn_has_code_code >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 64w]
     [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (first_x_assum irule >> simp[emitted_insts_def] >>
     metis_tac[APPEND_11]) >>
  `run_inst_seq_mem_ok (emitted_insts sa cs') s0 /\
   s0.vs_alloca_next <= t.vs_alloca_next` by
    (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`) literal_bytelike_seq_mem >>
     disch_then (qspec_then `TAKE 4 (Keccak_256_w64 bs)` mp_tac) >>
     simp[LENGTH_TAKE, LENGTH_Keccak_256_w64,
          vfmConstantsTheory.word_size_def, dimword_def] >>
     disch_then drule_all >> simp[]) >>
  conj_tac
  >- (`inst_seq_ptr (DF H) lo ctx func PG G0 tn0
         (emitted_insts sa cs') s0 G' tn'` by metis_tac[] >>
      drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
        run_inst_seq_gas_origin_ptr_path >>
      disch_then (qspec_then `gas_explicit_sites ctx shadow_ctx` mp_tac) >>
      simp[emitted_insts_def, DROP_PREFIX] >>
      disch_then irule >> gvs[emitted_insts_def, DROP_PREFIX]) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `expr_post H ctx func cenv cx
    (Builtin (BaseT (BytesT (Dynamic 4))) MethodId [Literal la l]) es sa cs' s0 es
    (BytesV (TAKE 4 (Keccak_256_w64 bs))) (Var p) t` by
    (drule exprSimUnwrapPropsTheory.expr_post_of_vv_post_memory >>
     simp[base_ptr_def, is_word_type_def]) >>
  `t.vs_current_bb = cs'.cs_current_bb` by
    (drule_at (Pat `EVERY _ _`) fragExecTheory.exec_block_run_inst_seq >>
     disch_then (qspecl_then [`s0`, `0`, `ctx`, `bb`] mp_tac) >>
     simp[emitted_insts_def, DROP_PREFIX] >> gvs[]) >>
  `alloca_history func (t with vs_inst_idx := LENGTH cs'.cs_current_insts)` by
    (irule emitted_alloca_history >> simp[] >> qexistsl_tac [`emitted_insts sa cs'`, `s0`, `sa`] >>
     simp[] >> conj_tac
     >- gvs[stmt_state_rel_def, state_rel_def] >>
     fs[EVERY_MEM]) >>
  simp[] >> rpt conj_tac
  >~ [`expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`]
  >- (qpat_x_assum `expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[NoAsms, expr_post_def, stmt_state_rel_inst_idx, expr_val_rel_def,
           expr_val_at_def, expr_val_own_def, lookup_var_def, eval_operand_def,
           local_region_def, locals_kept_def, popped_kept_def,
           storage_well_formed_on_def, oneline vyperStorageBackendTheory.get_storage_def,
           get_storage_backend_def] >> strip_tac >> simp[] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`expr_store_bound _ _ _ _ _`]
  >- (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
      simp[expr_store_bound_def, vv_store_bound_def, base_ptr_def,
           eval_operand_def, lookup_var_def, read_result_def, return_def,
           expr_type_def] >>
      qpat_x_assum `lookup_var p t = _` mp_tac >>
      qpat_x_assum `b + 64 < _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[])
  >~ [`ghost_inv_at _ _ _ _ _ _ _ _ _`]
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G'`, `es`, `t`, `sa`, `tn'`] >>
      simp[NoAsms, lookup_var_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`ptr_val_ok _ _ _ _ _ _ _`]
  >- (qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >>
      simp[ptr_vv_ok_def, ptr_val_ok_def, ptr_mem_ok_def, base_ptr_def,
           expr_type_def, is_word_type_def, read_result_def, return_def,
           ptr_covers_def, eval_operand_def, lookup_var_def] >>
      qpat_x_assum `lookup_var p t = _` mp_tac >>
      qpat_x_assum `b + 64 < _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[lookup_var_def] >>
      rpt strip_tac >> gvs[] >> metis_tac[])
  >~ [`ptr_buf_ok _ _ _ _ _`]
  >- (qpat_x_assum `ptr_buf_ok _ _ _ _ t` mp_tac >>
      qpat_x_assum `buf.buf_operand = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[NoAsms, ptr_buf_ok_def, lookup_var_def, eval_operand_def] >>
      rpt strip_tac >> gvs[])
  >~ [`gas_origin_ptr_path _ _ _ _`]
  >- (`inst_seq_ptr (DF H) lo ctx func PG G0 tn0
         (emitted_insts sa cs') s0 G' tn'` by metis_tac[] >>
      drule_at (Pat `inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`)
        run_inst_seq_gas_origin_ptr_path >>
      disch_then (qspec_then `gas_explicit_sites ctx shadow_ctx` mp_tac) >>
      simp[emitted_insts_def, DROP_PREFIX] >>
      disch_then irule >> gvs[emitted_insts_def, DROP_PREFIX])
  >~ [`vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`]
  >- (qpat_x_assum `vv_post H _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      qpat_x_assum `buf.buf_operand = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[NoAsms, base_ptr_def, read_result_def, return_def,
           vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
           stmt_state_rel_def, state_rel_def, expr_val_rel_def, expr_val_at_def,
           expr_val_own_def, local_region_def, locals_kept_def, popped_kept_def,
           storage_well_formed_on_def, oneline vyperStorageBackendTheory.get_storage_def,
           get_storage_backend_def] >> disch_then SUBST1_TAC >> strip_tac >> simp[] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`vv_store_bound _ _ _ _ _ _ _`]
  >- (qpat_x_assum `vv_store_bound _ _ _ _ _ _ t` mp_tac >>
      qpat_x_assum `buf.buf_operand = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[NoAsms, vv_store_bound_def, expr_type_def, lowered_value_type_def,
           base_ptr_def, read_result_def, return_def, eval_operand_def, lookup_var_def])
  >~ [`ghost_inv_at _ _ _ _ _ _ _ _ _`]
  >- (irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G'`, `es`, `t`, `sa`, `tn'`] >>
      simp[NoAsms, lookup_var_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`ptr_vv_ok _ _ _ _ _ _ _ _`]
  >- (qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ t` mp_tac >>
      qpat_x_assum `buf.buf_operand = _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      simp[NoAsms, ptr_vv_ok_def, ptr_mem_ok_def, ptr_covers_def,
           expr_type_def, base_ptr_def, read_result_def, return_def,
           eval_operand_def, lookup_var_def]) >>
  simp[vv_location_def] >>
  qpat_x_assum `ptr_buf_ok _ _ _ _ t` mp_tac >>
  qpat_x_assum `buf.buf_operand = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[NoAsms, ptr_buf_ok_def, lowered_value_type_def, base_ptr_def,
       vv_operand_def, eval_operand_def, lookup_var_def]
QED
