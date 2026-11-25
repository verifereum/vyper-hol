(* Keep the raw run and the all-horizon post at the same comparison exit. *)
Theory bodyFullBopBytesEqSelected
Ancestors
  bodyFullBopBytesEqSuffix exprSimFullBundleProps exprSimHyps
  exprBopSimProps exprSimCompare exprSimExtract32Post bodyFullGhostFrame
  bodyPtrHashBuiltinsGhostCompose bodyPtrSignedConvertSourceFrame
  entryDecoderHistoryFrame bodyUnopFragMemory exprSimSource
  vyperStorageTrace vyperStorageFootprint fragGasFresh fragGasSeqPtr stmtSimDefs
  compileEnv loweringPosts vyperAST vyperInterpreter vyperValueOperation
  exprLoweringProps loweringSlice bodyPtrDefs venomState venomInst ptrDiscipline
  exprSimDefs exprSimMemDefs finite_map vyperTyping vyperContext list
  freshWrites valueEncoding bodyFullHashKeccakFixed vyperState

Theorem bop_bytes_eq_suffix_selected:
  (bop = Eq \/ bop = NotEq) /\
  (expr_type e1 = BaseT AddressT \/
   ?m. expr_type e1 = BaseT (BytesT (Fixed m))) /\
  expr_type e2 = expr_type e1 /\ ann = BaseT BoolT /\
  expr_body_pre cenv cx env e1 es /\ expr_body_pre cenv cx env e2 mid /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e1) e2 s1 = (y,s2) /\
  compile_binop bop x y (expr_type e1) NONE NONE s2 = (op,sb) /\
  ci_mono sa s1 /\ ci_mono s1 s2 /\ cs_extends s2 sb /\
  fn_has_code s2 sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0) /\
  bind (eval_expr cx e1) (read_result cx) (es with gas_obs := incoming1) = (INL v,mid) /\
  bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := incoming2) = (INL v',mid2) /\
  mid2.gas_obs = [] /\ ~u.vs_halted /\
  storage_trace_domain cx st0 mid2.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e1
         (es,sa,s1,s0,x,G0,tn0) H (INL v) mid G1 tn1 t) /\
  (!H. valid_horizon cx st0 H mid2.storage_trace ==>
       expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e2
         (mid,s1,s2,t,y,G1,tn1) H (INL v') mid2 G2 tn2 u) ==>
  ?raw G' tn' res.
    run_inst_seq (emitted_insts s2 sb) u = OK raw /\
    (!tail. bop_result cx ann bop [expr_type e1;expr_type e2] v v'
               (mid2 with gas_obs := tail) = res) /\
    !H. valid_horizon cx st0 H mid2.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,ctx,func,PG) (u,G2,tn2) []
        (OK (raw with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
      expr_sim_full_post (DF,lo,d,ctx,func) cenv cx (Builtin ann (Bop bop) [e1;e2])
        (es,sa,sb,s0,op,G0,tn0) H res (mid2 with gas_obs := []) G' tn'
        (raw with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?ot. evaluate_type (get_tenv cx) (expr_type e1) = SOME ot` by
    (drule exprSimHypsTheory.expr_body_pre_type_evaluates >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  `is_word_type (expr_type e1) /\ is_word_type (expr_type e2)` by
    (qpat_x_assum `expr_type e1 = _ \/ _` strip_assume_tac >>
     gvs[vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION,
         is_word_type_def]) >>
  `?tv1. evaluate_type (get_tenv cx) (expr_type e1) = SOME tv1 /\
      value_has_type tv1 v` by
    (`expr_body_pre cenv cx env e1 (es with gas_obs := incoming1)` by
       simp[expr_body_pre_gas_obs] >>
     drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_type_result) >> simp[]) >>
  `?tv2. evaluate_type (get_tenv cx) (expr_type e2) = SOME tv2 /\
      value_has_type tv2 v'` by
    (`expr_body_pre cenv cx env e2 (mid with gas_obs := incoming2)` by
       simp[expr_body_pre_gas_obs] >>
     drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_type_result) >> simp[]) >>
  rule_assum_tac (SIMP_RULE bool_ss [expr_sim_full_post_def,
    expr_sim_full_endpoint_def,sumTheory.INL_11,UNWIND_THM2]) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx e2) (read_result cx))` by
       (irule storage_trace_frame_bind_all >>
        simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
     rpt strip_tac >> drule_all valid_horizon_frame >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace)
     mid2.storage_trace` by fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace)
     mid.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `post_value_type cenv e1 = expr_type e1 /\ post_value_type cenv e2 = expr_type e2` by
    simp[post_value_type_word] >>
  suspend "run"
QED

Resume bop_bytes_eq_suffix_selected[run]:
  `(!z. x = Var z ==> not_fresh_at s1 z) /\
   (!z. y = Var z ==> not_fresh_at s2 z)` by
    (conj_tac
     >- (qpat_assum `lower_value _ _ _ e1 sa = _`
           (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >> metis_tac[]) >>
     qpat_assum `lower_value _ _ _ e2 s1 = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >> metis_tac[]) >>
  `(!z. x = Var z ==> not_fresh_at s2 z)` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def] >>
  `eval_operand x t = SOME (typed_val_to_w256 tv1 v) /\
   eval_operand y u = SOME (typed_val_to_w256 tv2 v')` by
    (conj_tac
     >- (qpat_assum `expr_post _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
          (mp_tac o REWRITE_RULE [expr_post_def,expr_val_rel_def]) >>
         strip_tac >> metis_tac[]) >>
     qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_post_def,expr_val_rel_def]) >>
     strip_tac >> metis_tac[]) >>
  `eval_operand x u = SOME (typed_val_to_w256 tv1 v)` by
    (qpat_assum `lower_value _ _ _ e1 sa = _`
       (mp_then Any mp_tac expr_body_pre_lower_value_word_shape) >>
     strip_tac >>
     qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
       (mp_tac o SIMP_RULE (srw_ss()) [expr_post_def]) >>
     strip_tac >> Cases_on `x`
     >- (qpat_x_assum `eval_operand _ t = _` mp_tac >> simp[eval_operand_def])
     >- (rename1 `Var z` >>
         qpat_x_assum `!x w. not_fresh_at s1 x /\ _ ==> _`
           (qspecl_then [`z`, `typed_val_to_w256 tv1 v`] mp_tac) >>
         simp[] >>
         qpat_x_assum `eval_operand _ t = _` mp_tac >> simp[eval_operand_def]) >>
     metis_tac[]) >>
  drule_all bop_bytes_eq_suffix_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `run_inst_seq _ u = OK u'` >>
  `allocas_from lo u` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ mid2 _ _ u`
       (mp_tac o SIMP_RULE (srw_ss()) [ghost_inv_at_def]) >> simp[]) >>
  `op_prov G2 y = NONE /\ op_taint tn2 y = {}` by
    (qpat_assum `ptr_val_ok _ _ _ y G2 tn2 u`
       (mp_tac o SIMP_RULE (srw_ss()) [ptr_val_ok_def]) >> simp[]) >>
  `op_prov G2 x = NONE /\ op_taint tn2 x = {}` by
    (qpat_assum `ptr_val_ok _ _ _ x G1 tn1 t`
       (mp_tac o SIMP_RULE (srw_ss()) [ptr_val_ok_def]) >>
     simp[] >> strip_tac >>
     qpat_assum `ghost_kept_at lo _ _ s1 G1 tn1 t G2 tn2`
       (mp_tac o SIMP_RULE (srw_ss()) [ghost_kept_at_def]) >>
     strip_tac >> Cases_on `x` >> simp[op_prov_def, op_taint_def] >>
     rename1 `Var z` >>
     qpat_x_assum `!x. not_fresh_at s1 x ==> _`
       (qspec_then `z` mp_tac) >> simp[] >> strip_tac >>
     qpat_x_assum `op_prov G1 (Var z) = NONE` mp_tac >>
     qpat_x_assum `op_taint tn1 (Var z) = {}` mp_tac >>
     simp[op_prov_def, op_taint_def]) >>
  drule_all bop_bytes_eq_suffix_ptr >>
  disch_then (qspecl_then [`func`, `PG`] strip_assume_tac) >>
  suspend "source"
QED

Resume bop_bytes_eq_suffix_selected[source]:
  `tv2 = tv1` by metis_tac[optionTheory.SOME_11] >>
  Q.SUBGOAL_THEN `?b1 b2. v = BytesV b1 /\ v' = BytesV b2 /\
    (tv1 = BaseTV AddressT \/
     ?m. tv1 = BaseTV (BytesT (Fixed m)) /\ m <= 32)`
    (qx_choose_then `b1` (qx_choose_then `b2` (map_every assume_tac o CONJUNCTS)))
  >- (qpat_assum `value_has_type tv1 v` mp_tac >>
     qpat_assum `value_has_type tv2 v'` mp_tac >>
     qpat_assum `evaluate_type _ (expr_type e1) = SOME tv1` mp_tac >>
     qpat_assum `expr_type e1 = _ \/ _` mp_tac >>
     qpat_assum `tv2 = tv1` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
     Cases_on `v` >> fs[value_has_type_def] >>
     Cases_on `v'` >> fs[value_has_type_def]) >>
  `typed_val_to_w256 tv1 v = typed_val_to_w256 tv2 v' <=> v = v'` by
    (gvs[] >> irule exprSimCompareTheory.typed_val_to_w256_bytes_11 >> simp[]) >>
  qexistsl_tac [`u'`,`G'`,`tn'`, `INL (BoolV (eval_compare bop (expr_type e1)
    (typed_val_to_w256 tv1 v) (typed_val_to_w256 tv2 v')))`] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (qpat_assum `typed_val_to_w256 tv1 v = _ <=> _` mp_tac >>
      qpat_assum `v = BytesV b1` mp_tac >>
      qpat_assum `v' = BytesV b2` mp_tac >>
      qpat_assum `bop = Eq \/ bop = NotEq` mp_tac >>
      qpat_assum `expr_type e1 = _ \/ _` mp_tac >>
      qpat_assum `expr_type e2 = expr_type e1` mp_tac >>
      qpat_assum `ann = BaseT BoolT` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
      gvs[exprBopSimDefsTheory.bop_result_def, evaluate_builtin_def,
          evaluate_binop_def, binop_negate_def, arithmeticPropsTheory.eval_compare_def, oEL_def,
          vyperValueTheory.evaluate_type_def, optionTheory.IF_EQUALS_OPTION] >>
      IF_CASES_TAC >> simp[]) >>
  suspend "endpoint"
QED

Resume bop_bytes_eq_suffix_selected[endpoint]:
  gen_tac >> disch_tac >>
  `straight_fresh (compile_binop bop x y (expr_type e1) NONE NONE)` by
    (irule exprSimCompareTheory.straight_fresh_compare >> simp[] >> metis_tac[]) >>
  `writes_fresh s2 (emitted_insts s2 sb) /\
   sb.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 sb` by
    metis_tac[freshWritesTheory.straight_fresh_def] >>
  drule_all freshWritesTheory.run_inst_seq_writes_fresh >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac
  >- (drule_all fragGasFreshTheory.straight_fresh_code_prefix >> strip_tac >>
      drule fragGasFreshTheory.writes_fresh_path_opcodes >> strip_tac >>
      drule fragGasFreshTheory.writes_fresh_gas_count >> strip_tac >>
      `run_inst_seq_mem_ok (emitted_insts s2 sb) u` by
        metis_tac[bodyUnopFragMemoryTheory.writes_fresh_mem_ok] >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts s2 sb)` by fs[EVERY_MEM] >>
      `(ctx_has_dalloca ctx ==> !pre i post v.
        emitted_insts s2 sb = pre ++ i::post /\
        run_inst_seq pre u = OK v ==> dalloca_no_wrap i v)` by
        (rpt strip_tac >>
         irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
         `MEM i (emitted_insts s2 sb)` by simp[] >>
         qpat_assum `writes_fresh _ _`
           (qspec_then `i` mp_tac o REWRITE_RULE[writes_fresh_def, EVERY_MEM]) >>
         Cases_on `i.inst_opcode = DALLOCA` >> simp[fresh_write_op_def]) >>
      qpat_assum `!D. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `DF H` assume_tac) >>
      drule_all fragGasSeqPtrTheory.run_inst_seq_gas_origin_ptr_path >>
      fs[LENGTH_NIL] >> simp[]) >>
  simp_tac bool_ss [expr_sim_full_post_def,expr_sim_full_endpoint_def,
    sumTheory.INL_11,UNWIND_THM2] >>
  `mid2 with gas_obs := [] = mid2` by simp[evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >>
  `post_value_type cenv (Builtin ann (Bop bop) [e1;e2]) = ann` by
    simp[post_value_type_word,expr_type_def,is_word_type_def] >>
  suspend "joint"
QED

Resume bop_bytes_eq_suffix_selected[joint]:
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  `stmt_state_rel H ctx func cenv cx mid2 u` by
    metis_tac[expr_post_def] >>
  `stmt_state_rel H ctx func cenv cx mid2
     (u' with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule bodyPtrSignedConvertSourceFrameTheory.stmt_state_rel_readonly_vars_pc >>
     qexistsl_tac [`u`, `s2`] >> simp[] >>
     qpat_assum `u' = u with vs_vars := _` mp_tac >>
     qpat_assum `!z. not_fresh_at s2 z ==> FLOOKUP u'.vs_vars z = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[lookup_var_def, venom_state_component_equality]) >>
  `valid_horizon cx st0 H mid.storage_trace` by simp[] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `storage_trace_frame (bind (eval_expr cx e1) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then assume_tac) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `bind _ _ (es with gas_obs := _) = (INL v,mid)`
       (mp_tac o MATCH_MP stmtSimDefsTheory.eval_read_preserves_scopes_dom) >> simp[]) >>
  conj_tac
  >- (simp[exprSimExtract32PostTheory.extract32_expr_post_end_gas_obs] >>
      irule exprBopSimPropsTheory.expr_post_bop >>
      simp[is_word_type_def, word_value_def, val_to_w256_def] >>
      (conj_tac >- (qmatch_goalsub_abbrev_tac `bool_to_word b` >>
                    Cases_on `b` >> simp[])) >>
      (conj_tac >- (qpat_assum `stmt_state_rel H ctx func cenv cx mid2
         (u' with vs_inst_idx := _)` mp_tac >>
         qpat_assum `sb.cs_current_insts = _ ++ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringPropsTheory.stmt_state_rel_inst_idx])) >>
      qexistsl_tac [`mid`, `s1`, `s2`, `t`, `u`, `v`, `v'`, `x`, `y`] >>
      simp[] >>
      (conj_tac >- (qpat_assum `!z. not_fresh_at s2 z ==> FLOOKUP u'.vs_vars z = _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[lookup_var_def])) >>
      (conj_tac >- (qpat_assum `u' = u with vs_vars := _` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality] >> metis_tac[])) >>
      (conj_tac >- fs[ci_mono_def]) >>
      (conj_tac >- fs[ci_mono_def]) >>
      (conj_tac >- fs[ci_mono_def]) >>
      qpat_assum `u' = u with vs_vars := _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality]) >>
  suspend "resources"
QED

Resume bop_bytes_eq_suffix_selected[resources]:
  `ctx_has_dalloca ctx ==> allocas_below_fmp u'` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx mid2 (u' with vs_inst_idx := _)`
       (mp_tac o MATCH_MP stmt_state_rel_allocas_below_fmp) >>
     POP_ASSUM_LIST (K all_tac) >> simp[allocas_below_fmp_def] >> metis_tac[]) >>
  `sb.cs_current_bb = s2.cs_current_bb` by
    metis_tac[freshWritesTheory.straight_fresh_def] >>
  simp[expr_type_def, is_word_type_def, exprSimMemDefsTheory.expr_store_bound_word] >>
  (conj_tac >- (qpat_assum `u' = u with vs_vars := _` mp_tac >>
    qpat_assum `u.vs_current_bb = _` mp_tac >>
    qpat_assum `cs_extends s2 sb` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality, cs_extends_def] >> metis_tac[])) >>
  (conj_tac >- (
    `alloca_inv u` by metis_tac[stmt_state_rel_def] >>
    `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s2 sb)` by
      (drule fragGasFreshTheory.writes_fresh_path_opcodes >> simp[EVERY_MEM]) >>
    `alloca_history func (u' with vs_inst_idx := LENGTH sb.cs_current_insts)` by
      (irule entryDecoderHistoryFrameTheory.entry_straight_line_alloca_history >>
       (conj_tac >- first_assum ACCEPT_TAC) >>
       qexistsl_tac [`u`, `s2`] >> simp[] >>
       simp[rich_listTheory.IS_PREFIX_APPEND]) >>
    qpat_x_assum `alloca_history func (u' with vs_inst_idx := _)` mp_tac >>
    qpat_assum `sb.cs_current_insts = _ ++ _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[])) >>
  (conj_tac >- (qpat_assum `u' = u with vs_vars := _` mp_tac >>
    qpat_assum `s0.vs_alloca_next <= t.vs_alloca_next` mp_tac >>
    qpat_assum `t.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality] >> decide_tac)) >>
  (conj_tac >- (
    irule bodyFullGhostFrameTheory.ghost_inv_at_exterior_frame >>
    qexistsl_tac [`G2`, `mid2`, `u`, `s2`, `tn2`] >>
    simp[] >>
    (conj_tac >- (rpt strip_tac >>
      `sa.cs_next_var <= s2.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
      irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[])) >>
    (conj_tac >- (rpt strip_tac >>
      `sa.cs_next_var <= s2.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
      irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[])) >>
    (conj_tac >- (
      qpat_assum `!z. not_fresh_at s2 z ==> FLOOKUP u'.vs_vars z = _` mp_tac >>
      qpat_assum `!z. not_fresh_at s2 z ==> FLOOKUP G' z = _ /\ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[lookup_var_def, op_taint_def])) >>
    qpat_assum `u' = u with vs_vars := _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[venom_state_component_equality])) >>
  (conj_tac >- (
    qpat_assum `op_prov G' op = NONE` mp_tac >>
    qpat_assum `op_taint tn' op = {}` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[ptr_val_ok_def, is_word_type_def])) >>
  suspend "kept"
QED

Resume bop_bytes_eq_suffix_selected[kept]:
  `(!z. not_fresh_at sa z ==> not_fresh_at s1 z) /\
   (!z. not_fresh_at sa z ==> not_fresh_at s2 z) /\
   sa.cs_next_id <= s1.cs_next_id` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono, arithmeticTheory.LESS_EQ_TRANS]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G1 tn1` by
    (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ghost_kept_at_def, ghost_kept_def] >> metis_tac[]) >>
  `ghost_kept cenv mid s1 G1 tn1 t G2 tn2` by
    (qpat_assum `ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ghost_kept_at_def, ghost_kept_def] >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s0` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G2 tn2` by
    (qpat_assum `expr_post H _ _ _ _ e1 _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `local_ptrs_rel func cenv es.scopes s0` mp_tac >>
     qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
     qpat_assum `MAP FDOM es.scopes = MAP FDOM mid.scopes` mp_tac >>
     qpat_assum `!z. not_fresh_at sa z ==> not_fresh_at s1 z` mp_tac >>
     qpat_assum `sa.cs_next_id <= s1.cs_next_id` mp_tac >>
     qpat_assum `ghost_kept cenv es sa G0 tn0 s0 G1 tn1` mp_tac >>
     qpat_assum `ghost_kept cenv mid s1 G1 tn1 t G2 tn2` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     drule_all hash_expr_post_ghost_kept_compose >> simp[]) >>
  qpat_assum `ghost_kept cenv es sa G0 tn0 s0 G2 tn2` mp_tac >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` mp_tac >>
  qpat_assum `ghost_kept_at lo cenv mid s1 G1 tn1 t G2 tn2` mp_tac >>
  qpat_assum `!z. not_fresh_at sa z ==> not_fresh_at s2 z` mp_tac >>
  qpat_assum `!z. not_fresh_at s2 z ==> FLOOKUP G' z = _ /\ _` mp_tac >>
  qpat_assum `tn'.t_mem = tn2.t_mem` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[ghost_kept_at_def, ghost_kept_def, op_taint_def] >>
  rpt strip_tac >> metis_tac[]
QED

Finalise bop_bytes_eq_suffix_selected
