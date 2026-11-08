(* Allocation and zero-store share one endpoint ghost and continuation. *)
Theory decoderIndexInitCorePtr
Ancestors wordLoadStorePtr decoderBudgetAllocaCorePtr decoderSetupStepPtr ptrSafetyTransport decoderAllocationBoundsPtr
  abiDecoderIndexInit abiDecoderAllocation allocationPtr typedCopyPtr fragExecPtr
  bodyPtrDefs ptrDiscipline ptrSafeRun compileEnv context emitHelper emitHelperProps
  loweringHalt localPtrsProps exprLoweringProps venomExecSemantics venomMemProps venomState venomInst finite_map
  words list rich_list arithmetic pred_set instIdxIndep codegenRel contextCodegenRel

Theorem abi_decode_index_init_endpoint_exact_ptr_core:
  abi_decode_index_init sa = (ip,sb) /\
  abi_decoder_budget first last b cap s /\
  sa.cs_next_id IN abi_decoder_ids first last /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u q p. ip = Var q /\ eval_operand ip t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\ mload p t = 0w /\
    ptr_covers H u q (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    u.t_mem = tn.t_mem DIFF {a | p <= a /\ a < p + 32} /\
    (!a. p <= a /\ a < p + 32 ==> a NOTIN u.t_mem) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx' func.
      fn_has_code sa sb func /\ allocas_from lower s /\ lower <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx' /\
      s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx' func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx' func PG G tn s)
Proof
  strip_tac >> drule abi_decode_index_init_trace >> strip_tac >>
  `emit_op ALLOCA [Lit 32w] sa = (ip,allocation_st)` by
    (Cases_on `emit_op ALLOCA [Lit 32w] sa` >>
     gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa allocation_st ++ emitted_insts allocation_st sb` by
    (simp[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]) >>
  `?v. run_inst_seq (emitted_insts sa allocation_st) s = OK v /\
       run_inst_seq (emitted_insts allocation_st sb) v = OK t` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK t` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all budget_alloca_endpoint_exact_ptr_core >>
  disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  `t = mstore p 0w v` by
    (qpat_x_assum `run_inst_seq (emitted_insts allocation_st sb) v = OK t` mp_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
          exec_write2_def, eval_operand_def, w2n_n2w] >>
     gvs[eval_operand_def] >> simp[w2n_n2w]) >>
  `sb.cs_current_bb = allocation_st.cs_current_bb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, fresh_id_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]) >>
  qabbrev_tac `v1 = v with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `ins = mk_inst allocation_st.cs_next_id MSTORE [Var q; Lit 0w] []` >>
  qabbrev_tac `u1 = step_taint ins v1 (mstore p 0w v1) u` >>
  `step_prov PG H ins (mstore p 0w v1) = H /\
   u1.t_var = u.t_var /\ u1.t_stor = u.t_stor /\ u1.t_trans = u.t_trans /\
   u1.t_mem = u.t_mem DIFF {a | p <= a /\ a < p + 32}` by
    (mp_tac mstore_ghost_frame >>
     disch_then (qspecl_then [`PG`,`H`,`u`,`v1`,`allocation_st.cs_next_id`,
       `q`,`Lit 0w`,`n2w p`,`0w`] mp_tac) >>
     simp[Abbr `ins`, Abbr `u1`, Abbr `v1`, lookup_var_def,
          eval_operand_def, op_taint_def, w2n_n2w] >> gvs[lookup_var_def]) >>
  `u1.t_imm = tn.t_imm` by
    simp[Abbr `u1`, Abbr `ins`, step_taint_def, imm_taint_def, mk_inst_def] >>
  `frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u1 /\ v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R` by
    (irule frag_exec_ptr_seq >>
     qexistsl_tac [`\g z v. g = H /\ z = u /\ v = v1`, `allocation_st`] >>
     simp[] >> conj_tac >-
       (drule emit_op_extends >> simp[same_blocks_def] >> strip_tac >>
        irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
     conj_tac >-
       (drule emit_void_extends >> simp[same_blocks_def] >> strip_tac >>
        irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
     gvs[] >> irule mstore_frag_ptr >> simp[] >>
     qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`, `sa.cs_next_id + 1`, `Lit 0w`] >>
     simp[Abbr `ins`, op_taint_def] >> qexistsl_tac [`n2w p`,`0w`] >>
     simp[Abbr `v1`, lookup_var_def, eval_operand_def, w2n_n2w] >>
     gvs[lookup_var_def, mstore_def, ADD1, ADD_ASSOC]) >>
  qexistsl_tac [`H`,`u1`,`q`,`p`] >>
  gvs[eval_operand_def] >>
  conj_tac >- simp[mload_mstore_same] >>
  conj_tac >- (fs[ptr_covers_def, Abbr `v1`, eval_operand_def, lookup_var_def] >>
               gvs[ptr_covers_def, eval_operand_def, lookup_var_def, op_taint_def]) >>
  conj_tac >- (rpt strip_tac >> fs[op_taint_def]) >>
  rpt gen_tac >> strip_tac >>
  `cs_extends sa allocation_st /\ cs_extends allocation_st sb` by
    (conj_tac >-
      (drule emit_op_extends >> simp[same_blocks_def] >> strip_tac >>
       irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
     drule emit_void_extends >> simp[same_blocks_def] >> strip_tac >>
     irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  `step_inst_base
     (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString sa.cs_next_var)]) s = OK v` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  `allocas_from lower v` by
    (irule (INST_TYPE [alpha |-> ``:256``] exec_alloca_preserves_allocas_from) >>
     qexistsl_tac [`32w:bytes32`, `mk_inst sa.cs_next_id ALLOCA [Lit 32w]
       [STRING #"%" (toString sa.cs_next_var)]`, `s`] >>
     simp[] >> qpat_x_assum `step_inst_base _ s = OK v` mp_tac >>
     simp[Once step_inst_base_def, mk_inst_def, eval_operand_def]) >>
  `v.vs_current_bb = s.vs_current_bb` by
    (drule_all budget_alloca_observations >>
     disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >> simp[]) >>
  `allocation_st.cs_current_bb = sa.cs_current_bb` by
    metis_tac[emit_op_same_blocks, same_blocks_def] >>
  `!fuel. ptr_safe_run D lower fuel ctx' func PG H u v1` suffices_by
    (strip_tac >>
     qpat_x_assum `!D lower ctx' func. _`
       (qspecl_then [`D`,`lower`,`ctx'`,`func`] mp_tac) >>
     gvs[Abbr `v1`, ADD1]) >>
  irule setup_instruction_continuation >>
  qexistsl_tac [`H`,`ins`,`allocation_st`,`sb`,`mstore p 0w v1`,`u1`] >>
  simp[Abbr `ins`, is_terminator_def] >>
  conj_tac >-
    gvs[Abbr `v1`, mstore_def] >>
  conj_tac >-
    (`allocas_from lower v1` by
       (simp[Abbr `v1`, allocas_from_def] >> metis_tac[allocas_from_def]) >>
     gen_tac >> irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[] >>
     irule ptr_inst_ok_mstore >> simp[op_taint_def]) >>
  simp[Abbr `v1`, Once step_inst_base_def, mk_inst_def,
       exec_write2_def, eval_operand_def, lookup_var_def, w2n_n2w] >>
  gvs[lookup_var_def, mstore_def]
QED
