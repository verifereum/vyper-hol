Theory bodyFullLiteralNonword
Ancestors
  bodyFullLiteralGhost bodyFullLiteralEndpoint bodyFullLiteralBuffer gasOutcomeFull
  vyperStorageTrace vyperStorageFootprint bodySimFull gasOutcomeFullCompose
  exprSimSource exprSimHypsDefs exprSimHyps exprSimUnwrapProps exprSimProps
  exprLoweringProps exprLowering loweringPosts bodyPtrDefs gasShadow
  vyperTyping vyperTypeSystem valueEncodingProofs valueEncodingDefs
  vyperInterpreter vyperState vyperValue venomState context compileEnv
  list finite_map pred_set words vyperTypeCallGraph exprSimPtrLiteralOps allocLimits vyperAST
  vyperValueOperation valueEncoding gasShadowCompile gasShadowState gasContext exprSimDefs
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
  >- (`locals_kept cenv es (es with gas_obs := []) s0 t <=>
       locals_kept cenv es es s0 t` by
        simp[NoAsms, locals_kept_def, popped_kept_def] >>
      qpat_x_assum `vv_post H _ _ _ _ _ _ _ _ _ es _ _ _` mp_tac >>
      simp[vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
           base_ptr_def, read_result_def, return_def,
           stmt_state_rel_start_gas_obs] >> strip_tac >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `vv_store_bound _ _ _ es _ _ _` mp_tac >>
      simp[vv_store_bound_def, read_result_def, return_def, base_ptr_def]) >>
  conj_tac
  >- (qpat_x_assum `ghost_inv_at _ _ _ _ _ es _ _ _` mp_tac >>
      simp[ghost_inv_at_def] >> metis_tac[]) >>
  simp[ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def,
       read_result_def, return_def, eval_operand_def, lookup_var_def,
       op_prov_def] >>
  rpt strip_tac >> irule val_in_memory_footprint_agree >>
  simp[] >> qexists_tac `t.vs_memory` >>
  reverse conj_tac >- metis_tac[] >>
  irule exprPtrCleanBufferPostTheory.clean_window_memory_agree >>
  goal_assum (drule_at Any) >> simp[] >> decide_tac
QED

Finalise literal_buffer_full_vv

Theorem literal_nonword_vv_full:
  expr_body_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Literal ann l) es
Proof
  strip_tac >>
  `expr_sim_pre cenv cx env (Literal ann l) es` by
    gvs[expr_sim_pre_def, expr_body_pre_def, int_calls_expr_def] >>
  drule_all literal_nonword_classify >> strip_tac >> gvs[]
  >- suspend "bytes"
  >> suspend "string"
QED

Resume literal_nonword_vv_full[bytes]:
  gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_literal_def,
      alloc_limits_expr_def, literal_alloc_ok_def, compatible_bound_def,
      well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
  irule literal_buffer_full_vv >>
  simp[is_word_type_def, post_value_type_def, expr_type_def] >>
  qexistsl_tac [`bs`, `BaseTV (BytesT (Dynamic n))`, `BytesV bs`] >>
  simp[post_value_type_def, expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def, val_wf_def, val_footprint_def,
       val_store_size_def, literal_bytes_buffer_size,
       lowered_value_type_def, type_memory_size_def] >>
  rpt conj_tac
  >- (rpt gen_tac >>
      simp[compile_expr_def, compile_literal_vv_def, expr_type_def, is_word_type_def,
           comp_bind_def, comp_return_def] >>
      Cases_on `compile_bytelike_literal bs (LENGTH bs) sa` >> simp[])
  >- simp[Once evaluate_def, return_def, evaluate_literal_def]
  >- (simp[val_in_memory_def] >> metis_tac[])
  >> gvs[vfmConstantsTheory.word_size_def] >>
  simp[wordsTheory.dimword_def] >>
  mp_tac (Q.SPEC `n` le_word_size_mul) >>
  mp_tac (Q.SPEC `LENGTH (bs:word8 list)` le_word_size_mul) >>
  simp[vfmConstantsTheory.word_size_def] >> decide_tac
QED

Resume literal_nonword_vv_full[string]:
  gvs[expr_sim_pre_def, well_typed_expr_def, well_typed_literal_def,
      alloc_limits_expr_def, literal_alloc_ok_def, compatible_bound_def,
      well_formed_type_def, vyperValueTheory.evaluate_type_def] >>
  irule literal_buffer_full_vv >>
  simp[is_word_type_def, post_value_type_def, expr_type_def] >>
  qexistsl_tac [`MAP (n2w o ORD) str`, `BaseTV (StringT n)`, `StringV str`] >>
  simp[post_value_type_def, expr_type_def, is_word_type_def,
       vyperValueTheory.evaluate_type_def, val_wf_def, val_footprint_def,
       val_store_size_def, literal_string_buffer_size, LET_THM,
       lowered_value_type_def, type_memory_size_def] >>
  rpt conj_tac
  >- (rpt gen_tac >>
      simp[compile_expr_def, compile_literal_vv_def, expr_type_def, is_word_type_def,
           comp_bind_def, comp_return_def] >>
      Cases_on `compile_bytelike_literal (MAP (n2w o ORD) str) (LENGTH str) sa` >> simp[])
  >- simp[Once evaluate_def, return_def, evaluate_literal_def]
  >- (simp[val_in_memory_def] >> metis_tac[])
  >> gvs[vfmConstantsTheory.word_size_def] >>
  simp[wordsTheory.dimword_def] >>
  mp_tac (Q.SPEC `n` le_word_size_mul) >>
  mp_tac (Q.SPEC `LENGTH (str:string)` le_word_size_mul) >>
  simp[vfmConstantsTheory.word_size_def] >> decide_tac
QED

Finalise literal_nonword_vv_full

Theorem literal_nonword_memory_compile[local]:
  expr_body_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann ==>
  ?p sb. compile_expr cenv ty (Literal ann l) sa = (LocatedValue ann p,sb) /\
    p.ptr_location = LocMemory
Proof
  strip_tac >>
  `expr_sim_pre cenv cx env (Literal ann l) es` by
    gvs[expr_sim_pre_def, expr_body_pre_def, int_calls_expr_def] >>
  drule_all literal_nonword_classify >> strip_tac >> gvs[] >>
  simp[compile_expr_def, compile_literal_vv_def, comp_bind_def,
       comp_return_def, is_word_type_def, base_ptr_def, expr_type_def] >>
  pairarg_tac >> simp[base_ptr_def]
QED

Theorem literal_nonword_value_full:
  expr_body_pre cenv cx env (Literal ann l) es /\ ~is_word_type ann ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Literal ann l) es
Proof
  strip_tac >>
  drule_all literal_nonword_vv_full >>
  simp[expr_vv_sim_full_def] >> disch_tac >>
  rw[expr_sim_full_def] >>
  `?p sm. compile_expr cenv ty (Literal ann l) sa = (LocatedValue ann p,sm) /\
    p.ptr_location = LocMemory` by metis_tac[literal_nonword_memory_compile] >>
  `op = p.ptr_operand /\ sb = sm` by
    (drule_all lower_value_nonword_memory >> simp[]) >>
  gvs[] >>
  `?sc. compile_expr cenv ty (gas_shadow_expr (Literal ann l)) shadow_sa =
     (LocatedValue ann p,sc)` by
    (mp_tac (Q.SPECL [`cenv`, `ty`, `Literal ann l`, `T`]
      (CONJUNCT1 gas_shadow_compile_expr)) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >>
     simp[] >> Cases_on `compile_expr cenv ty (gas_shadow_expr (Literal ann l)) shadow_sa` >>
     simp[]) >>
  `sc = shadow_sb` by
    (qpat_x_assum `lower_value _ _ _ _ shadow_sa = _` mp_tac >>
     simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def]) >>
  gvs[] >>
  `!st. eval_expr cx (Literal ann l) st = (INL (Value (evaluate_literal l)),st)` by
    simp[Once evaluate_def, return_def] >>
  `gas_admissible (eval_expr cx (Literal ann l)) expr_vv_res_ok es` by
    simp[gas_admissible_def, expr_vv_res_ok_def] >>
  first_x_assum drule_all >> disch_then (qspec_then `PG` assume_tac) >>
  suspend "value"
QED

Resume literal_nonword_value_full[value]:
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Q R` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_expr cx (Literal ann l)) (es,s0,G0,tn0)
     (\H res ee G tn t. Q H res ee G tn t /\ res = INL (Value (evaluate_literal l))) R` by
    (irule gas_outcome_full_post_source >> goal_assum (drule_at Any) >> simp[] >>
     rpt strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx (Literal ann l)) (read_result cx))
     (es,s0,G0,tn0)
     (\H raw ee G tn t. ?res.
       raw = (case res of INL raw => INL (evaluate_literal l) | INR ex => INR ex) /\
       (Q H res ee G tn t /\ res = INL (Value (evaluate_literal l))))
     (\H raw ee gt r. ?res.
       raw = (case res of INL raw => INL (evaluate_literal l) | INR ex => INR ex) /\
       R H res ee gt r)` by
    (ho_match_mp_tac (Q.ISPEC `eval_expr cx (Literal ann l)`
       (Q.GEN `source` (SPEC_ALL gas_outcome_full_source_map))) >>
     simp[bind_def, read_result_def, return_def] >> goal_assum (drule_at Any)) >>
  irule gas_outcome_full_post_mono >> goal_assum (drule_at Any) >>
  conj_tac >- suspend "post" >>
  simp[Abbr `R`] >> rpt strip_tac >> gvs[] >>
  simp[expr_exit_success_map] >>
  Cases_on `res'` >> gvs[halt_exit_def]
QED

Resume literal_nonword_value_full[post]:
  simp[Abbr `Q`] >> rpt strip_tac >> gvs[]
  >~ [`expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`] >-
    (drule_all expr_post_of_vv_post_memory >> simp[])
  >~ [`expr_store_bound _ _ _ _ _`] >-
    (gvs[vv_store_bound_def, expr_store_bound_def, read_result_def, return_def] >>
     metis_tac[]) >>
  gvs[ptr_vv_ok_def, ptr_val_ok_def, read_result_def, return_def, expr_type_def]
QED

Finalise literal_nonword_value_full
