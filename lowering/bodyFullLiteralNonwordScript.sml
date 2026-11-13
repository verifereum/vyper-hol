Theory bodyFullLiteralNonword
Ancestors
  bodyFullLiteralGhost bodyFullLiteralEndpoint bodyFullLiteralBuffer
  vyperStorageTrace vyperStorageFootprint bodySimFull gasOutcomeFullCompose
  exprSimSource exprSimHypsDefs exprSimHyps exprSimUnwrapProps exprSimProps
  exprLoweringProps exprLowering loweringPosts bodyPtrDefs gasShadow
  vyperTyping vyperTypeSystem valueEncodingProofs valueEncodingDefs
  vyperInterpreter vyperState vyperValue venomState context compileEnv
  list finite_map pred_set words
  exprSimPtrLiteralBuffer exprSimLiteralBuffer bodyPtrMakeArrayAllocBuffer
  exprSimPtrLiteralPayload venomInst venomExecSemantics exprSimMemDefs ptrDiscipline

Theorem literal_bytelike_full_static_frame:
  compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  32+32*word_size (LENGTH bs) < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables
Proof
  strip_tac >> drule literal_ptr_bytelike_shape >> strip_tac >>
  drule_all literal_ptr_bytelike_alloca_mem >> strip_tac >>
  drule_all alloc_buffer_frame_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w (32+32*word_size (LENGTH bs)))] [p]) s = OK u` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = _` mp_tac >>
     simp[run_inst_seq_def, mk_inst_def, is_terminator_def, AllCaseEqs()]) >>
  drule literal_alloca_static_frame >> strip_tac >>
  `run_inst_seq (mk_inst sm.cs_next_id MSTORE
      [Var p; Lit (n2w (LENGTH bs))] [] :: emitted_insts sh sb) u = OK t` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = _` mp_tac >>
     pure_asm_rewrite_tac [APPEND] >>
     once_rewrite_tac [run_inst_seq_def] >>
     gvs[mk_inst_def, is_terminator_def] >>
     simp[run_inst_seq_def, is_terminator_def]) >>
  `lookup_var p u = SOME (n2w (w2n w))` by
    gvs[eval_operand_def, wordsTheory.n2w_w2n] >>
  `w2n w+32+32*word_size (LENGTH bs) < dimword (:256)` by decide_tac >>
  drule_all literal_header_chunks_functional >> strip_tac >>
  qpat_x_assum `(t with <|vs_vars := _; vs_memory := _|>) = u` mp_tac >>
  simp[Once venom_state_component_equality] >> strip_tac >> simp[]
QED

Theorem literal_buffer_full_vv:
  post_value_type cenv (Literal ann l) = ann /\ ~is_word_type ann /\
  (!sa vv sb. compile_expr cenv ty (Literal ann l) sa = (vv,sb) ==>
    ?buf. vv = LocatedValue ann (base_ptr buf) /\
      compile_bytelike_literal bs (LENGTH bs) sa = (buf,sb)) /\
  (!st. eval_expr cx (Literal ann l) st = (INL (Value v),st)) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ val_wf tv v /\
  val_footprint tv v <= 32+32*word_size (LENGTH bs) /\
  val_store_size tv v <= 32+32*word_size (LENGTH bs) /\
  type_memory_bytes cenv (lowered_value_type cenv (Literal ann l)) <=
    32+32*word_size (LENGTH bs) /\
  (!rt. evaluate_type (get_tenv cx) (lowered_value_type cenv (Literal ann l)) =
    SOME rt ==> type_memory_size rt <= 32+32*word_size (LENGTH bs)) /\
  (!a mem. mem_word_at a mem = n2w (LENGTH bs) /\
    mem_bytes_at (a+32) (LENGTH bs) mem = bs ==> val_in_memory tv v a mem) /\
  32+32*word_size (LENGTH bs) < dimword (:256) ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Literal ann l) es
Proof
  strip_tac >> rw[expr_vv_sim_full_def] >>
  qpat_x_assum `!sa vv sb. _` drule >> strip_tac >> gvs[] >>
  irule gas_outcome_full_initial_domain >>
  simp[storage_trace_frame_def] >> strip_tac >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
  drule_all (SPEC_ALL (SRULE [Once arithmeticTheory.ADD_COMM] literal_bytelike_full_run)) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`, `es`, `INL (Value v)`,
    `t with vs_inst_idx := LENGTH sb.cs_current_insts`, `tn'`] >>
  simp[] >> gen_tac >> strip_tac >> suspend "posts"
QED

Resume literal_buffer_full_vv[posts]:
  qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ _`
    (qspec_then `H` (fn th => mp_tac th >> impl_tac >- simp[] >> strip_tac)) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` (fn th => mp_tac th >> impl_tac >- simp[] >> strip_tac)) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    inst_seq_ptr (DF H) lo ctx func PG G0 tn0 (emitted_insts sa sb) s0 G' tn'`
    by metis_tac[] >>
  drule_all (SPEC_ALL (SIMP_RULE (srw_ss() ++ ARITH_ss) []
    literal_bytelike_full_endpoint)) >>
  disch_then (qspec_then `gas_explicit_sites ctx shadow_ctx` mp_tac) >>
  simp[] >> strip_tac >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    gvs[ghost_inv_at_def] >>
  drule_all (SIMP_RULE (srw_ss() ++ ARITH_ss) []
    literal_bytelike_full_run_allocas_from) >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s0 /\
    lookup_var x t = lookup_var x u /\ FLOOKUP G' x = FLOOKUP G0 x /\
    FLOOKUP tn'.t_var x = FLOOKUP tn0.t_var x` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss() ++ ARITH_ss) []
    literal_bytelike_full_static_frame) >> strip_tac >>
  drule_all literal_bytelike_full_ghost_post >> strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (qpat_assum `storage_well_formed_on cx es (FST H)` mp_tac >>
     simp_tac (srw_ss()) [vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     strip_tac >> qx_gen_tac `tr` >>
     qpat_x_assum `!b slot tv. _` (qspec_then `tr` mp_tac) >>
     Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  simp[base_ptr_def, contextTheory.vv_location_def] >>
  conj_tac
  >- (qpat_x_assum `vv_post H _ _ _ _ _ _ _ _ _ es _ _ _` mp_tac >>
      simp_tac (srw_ss()) [vv_post_def, vv_holds_def, vv_at_def, vv_storage_live_def,
        read_result_def, return_def, stmt_state_rel_start_gas_obs,
        locals_kept_def, popped_kept_def, pure_frame_def,
        base_ptr_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `vv_store_bound _ _ _ es _ _ _` mp_tac >>
      simp[vv_store_bound_def, read_result_def, return_def]) >>
  conj_tac
  >- (qpat_x_assum `ghost_inv_at _ _ _ _ _ es _ _ _` mp_tac >>
      simp[ghost_inv_at_def] >> metis_tac[]) >>
  simp[ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def,
       read_result_def, return_def, eval_operand_def, lookup_var_def,
       op_prov_def] >> FAIL_TAC "ptr remaining"
QED

Finalise literal_buffer_full_vv
