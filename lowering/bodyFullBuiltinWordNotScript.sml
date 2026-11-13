Theory bodyFullBuiltinWordNot
Ancestors
  bodyFullPreds bodySimFull bodyFullGhostFrame exprSimWordBuiltins exprSimHypsDefs
  exprSimUnopProps exprSimUnopCompose gasOutcomeFullCompose
  gasShadowCompileStmtHelpers gasExemptCert vyperStorageTrace exprSimDefs
  fragGasSeqPtr fragGasOriginPtr exprSimSource
  decoderGhostFramePtr lowerDloadPtrScalar ptrDisciplineEmptyTaint
  emitHelperProps emitHelper compileEnv fragExec venomInst venomState exprLowering
  finite_map venomExecSemantics builtinSimple vyperValueOperation valueEncoding vyperInterpreter vyperContext
  vyperTypeSystem vyperTyping vyperAST list

Theorem word_not_pre[local]:
  expr_body_pre cenv cx env (Builtin ann Not args) es ==>
  ?e. args = [e] /\ ann = expr_type e /\
      expr_body_pre cenv cx env e es /\
      (is_bool_type ann \/ is_uint256_type ann \/
       is_bytes32_type ann \/ is_flag_type ann)
Proof
  strip_tac >>
  `well_typed_builtin_app ann Not (MAP expr_type args)` by
    gvs[expr_body_pre_def, well_typed_expr_def] >>
  gvs[well_typed_builtin_app_def] >>
  Cases_on `args` >> gvs[] >>
  (irule expr_body_pre_builtin_arg >> simp[] >>
   conj_tac >- gvs[expr_body_pre_def] >>
   qexistsl_tac [`expr_type h`, `[h]`, `Not`, `es`] >> simp[])
QED

Theorem word_not_typed_suffix[local]:
  (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/
   is_flag_type ann) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  (!nsid m. ann = FlagT nsid /\ tv = FlagTV m ==>
    cenv.ce_flag_n_members (nsid_to_string nsid) = m) /\
  (if ann = BaseT BoolT then emit_op ISZERO [x]
   else compile_invert x ann cenv) sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\ op_taint tn x = {} /\
  local_ptrs_reserved cenv sa /\
  (!y sz. cenv.ce_return_buf = SOME (PtrVar (Var y) sz) ==>
    not_fresh_at sa y) /\
  (!y sz. cenv.ce_return_pc = SOME (PtrVar (Var y) sz) ==>
    not_fresh_at sa y) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) ==>
  ?v' t G' tn'.
    unop_result cx ann Not tys v es = INL v' /\
    alloca_history func t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es t) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK t,G',tn')) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      ghost_inv_at (DF H) lo d cenv cx es G' tn' t) /\
    eval_operand op t = SOME (typed_val_to_w256 tv v') /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ op_taint tn' op = {} /\ op_prov G' op = NONE /\
    (!y. not_fresh_at sa y ==>
      lookup_var y t = lookup_var y s /\
      FLOOKUP G' y = FLOOKUP G y /\
      op_taint tn' (Var y) = op_taint tn (Var y)) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
    t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  SUBGOAL_THEN ``?k xs v' w'.
    emit_op k xs sa = (op,sb) /\
    unop_result cx ann Not tys v es = INL v' /\
    w' = typed_val_to_w256 tv v' /\
    (k = ISZERO \/ k = NOT \/ k = XOR) /\
    EVERY (\a. op_taint tn a = {}) xs /\
    (!out. step_inst_base (mk_inst sa.cs_next_id k xs [out]) s =
      OK (update_var out w' s))``
    (qx_choose_then `k` (qx_choose_then `xs`
      (qx_choose_then `v'` (qx_choose_then `w'`
        (map_every assume_tac o CONJUNCTS)))))
  >- (drule not_type_cases >> strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     Cases_on `v` >>
     gvs[value_has_type_def, unop_result_def, evaluate_builtin_def,
       type_to_int_bound_def, typed_val_to_w256_def, val_to_w256_def,
       compile_invert_def, vyperValueTheory.evaluate_type_def]
     >~ [`emit_op ISZERO`]
     >- (qexistsl_tac [`ISZERO`, `[x]`] >> simp[] >> gen_tac >>
         drule step_ISZERO >> Cases_on `b` >> simp[bool_to_word_def])
     >~ [`i2w i`]
     >- (qexistsl_tac [`NOT`, `[x]`] >> simp[] >> gen_tac >>
         `~(i < 0)` by intLib.COOPER_TAC >>
         drule step_NOT >> simp[integer_wordTheory.i2w_def])
     >~ [`LENGTH bs = 32`]
     >- (qexistsl_tac [`NOT`, `[x]`] >>
         simp[PAD_RIGHT, length_word_to_bytes_be, word_of_bytes_be_to_bytes] >>
         gen_tac >> drule step_NOT >> simp[PAD_RIGHT]) >>
     qmatch_asmsub_abbrev_tac `emit_op XOR [x; mask]` >>
     qexistsl_tac [`XOR`, `[x; mask]`] >>
     simp[Abbr `mask`, ptrDisciplineTheory.op_taint_def] >>
     gen_tac >> drule_all flag_not_xor >> disch_then (rewrite_tac o single o GSYM) >>
     irule step_XOR >> simp[eval_operand_def]) >>
  `!D out. ptr_inst_ok D lo 0 ctx func G tn
    (mk_inst sa.cs_next_id k xs [out]) s` by
    (rpt gen_tac >> simp[ptrSafeRunTheory.ptr_inst_ok_def,
       ptrDisciplineTheory.access_ok_def, ptrDisciplineTheory.taint_ok_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, mk_inst_def] >>
     `step_inst 0 ctx (mk_inst sa.cs_next_id k xs [out]) s =
       OK (update_var out w' s)` by
       (qpat_x_assum `k = ISZERO \/ _` strip_assume_tac >>
        simp[step_inst_non_invoke, mk_inst_def] >>
        metis_tac[mk_inst_def]) >>
     gvs[mk_inst_def, update_var_def, EVERY_MEM] >> metis_tac[]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id k xs
      [STRING #"%" (toString sa.cs_next_var)])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qmatch_asmsub_abbrev_tac `get_instruction bb _ = SOME inst` >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `u = update_var out w' s` >>
  qabbrev_tac `z = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `out_taint tn inst s = {} /\ written_taint tn inst s = {}` by
    (conj_tac
     >- (irule out_taint_opcode_exclusion >>
         qpat_x_assum `k = ISZERO \/ _` strip_assume_tac >>
         simp[Abbr `inst`, mk_inst_def]) >>
     irule written_taint_opcode_exclusion >>
     qpat_x_assum `k = ISZERO \/ _` strip_assume_tac >>
     simp[Abbr `inst`, mk_inst_def]) >>
  `new_site_bytes s u = {}` by
    (irule new_site_bytes_unchanged >> simp[Abbr `u`, update_var_def]) >>
  `step_taint inst s u tn = tn with t_var := tn.t_var |+ (out,{})` by
    (simp[ptrDisciplineTheory.step_taint_def,
      ptrDisciplineTheory.mem_taint_def, ptrDisciplineTheory.set_var_taint_def,
      Abbr `inst`, mk_inst_def] >>
     qpat_x_assum `k = ISZERO \/ _` strip_assume_tac >>
     simp[ptrDisciplineTheory.step_writes_def,
       codegenRelTheory.source_memory_write_ranges_def,
       ptrDisciplineTheory.range_bytes_def, ptrDisciplineTheory.store_taint_def,
       ptrDisciplineTheory.imm_taint_def, ptrDisciplineTheory.adopt_reset_def] >>
     simp[ptrDisciplineTheory.taint_component_equality]) >>
  `alloca_history func z` by
    (`~is_terminator inst.inst_opcode` by
       (qpat_x_assum `k = ISZERO \/ _` strip_assume_tac >>
        simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
     `step_inst_base inst s = OK u` by simp[Abbr `inst`, Abbr `u`] >>
     `lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     drule_all allocaHistoryTheory.alloca_history_base_step >>
     simp[Abbr `z`]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es z` by
    (rpt strip_tac >> simp[Abbr `z`, Abbr `u`,
       exprLoweringPropsTheory.stmt_state_rel_inst_idx] >>
     irule exprLoweringPropsTheory.stmt_state_rel_update_var >>
     simp[Abbr `out`] >> irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >>
     qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`v'`, `z`, `step_prov PG G inst u`,
    `step_taint inst s u tn`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK z, step_prov PG G inst u, step_taint inst s u tn)` by
       (`k <> GAS` by
          (qpat_x_assum `k = ISZERO \/ _` strip_assume_tac >> simp[]) >>
        mp_tac (straight_line_origin_ptr_edge |> Q.INST
         [`i` |-> `inst`, `u` |-> `u`, `D` |-> `DF (H : (bool # 256 word # type_value) list # num list)`]) >>
        simp[Abbr `inst`, mk_inst_def] >> disch_then irule >>
        simp[GSYM mk_inst_def, Abbr `u`, Abbr `z`, Abbr `out`] >>
        gvs[is_terminator_def,
          unitTransformDefsTheory.inst_mem_below_frontier_def,
          contextCodegenRelTheory.source_memory_read_ranges_def,
          codegenRelTheory.source_memory_write_ranges_def, mk_inst_def]) >>
      `~z.vs_halted` by simp[Abbr `z`, Abbr `u`, update_var_def] >>
      metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]) >>
  conj_tac
  >- (rpt strip_tac >> irule ghost_inv_at_exterior_frame >>
      qexistsl_tac [`G`, `es`, `s`, `sa`, `tn`] >>
      simp[Abbr `z`, Abbr `u`, update_var_def] >>
      qx_gen_tac `y` >> strip_tac >>
      `y <> out` by gvs[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `out`] >>
      simp[lookup_var_def, FLOOKUP_UPDATE, ptrDisciplineTheory.op_taint_def] >>
      irule step_prov_other_output >> simp[Abbr `inst`, mk_inst_def]) >>
  simp[Abbr `z`, Abbr `u`, eval_operand_def, lookup_var_def,
    update_var_def, FLOOKUP_UPDATE, ptrDisciplineTheory.op_taint_def] >>
  conj_tac
  >- (irule bodyPtrDefsTheory.step_prov_out_none >>
      simp[Abbr `inst`, mk_inst_def] >>
      irule bodyPtrDefsTheory.out_prov_other_none >>
      qpat_x_assum `k = ISZERO \/ _` strip_assume_tac >>
      simp[mk_inst_def]) >>
  rpt strip_tac >>
  `y <> out` by gvs[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `out`] >>
  simp[FLOOKUP_UPDATE, GSYM ptrDisciplineTheory.op_taint_def] >>
  irule step_prov_other_output >> simp[Abbr `inst`, mk_inst_def]
QED

Theorem word_not_parent_post[local]:
  expr_post H ctx func cenv cx e es sa s1 s0 mid v x t /\
  stmt_state_rel H ctx func cenv cx mid t' /\
  expr_val_rel cx ann v' op t' /\
  (!z w. not_fresh_at s1 z /\ lookup_var z t = SOME w ==>
         lookup_var z t' = SOME w) /\
  (!aid b. FLOOKUP t.vs_allocas aid = SOME b ==>
           FLOOKUP t'.vs_allocas aid = SOME b) /\
  t'.vs_memory = t.vs_memory /\ is_word_type ann /\
  sa.cs_next_var <= s1.cs_next_var ==>
  expr_post H ctx func cenv cx (Builtin ann Not [e]) es sa sb s0
    (mid with gas_obs := []) v' op t'
Proof
  strip_tac >> irule expr_post_unop >>
  simp[exprLoweringPropsTheory.stmt_state_rel_start_gas_obs] >>
  qexistsl_tac [`s1`, `t`, `v`, `x`] >> simp[] >>
  `(storage_well_formed_on cx (mid with gas_obs := []) (FST H) <=>
    storage_well_formed_on cx mid (FST H))` by
    (irule vyperStorageFootprintTheory.storage_well_formed_on_backends >> simp[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[loweringPostsTheory.expr_post_def,
    loweringPostsTheory.expr_val_at_def, loweringPostsTheory.expr_val_own_def,
    loweringPostsTheory.locals_kept_def, loweringPostsTheory.popped_kept_def,
    exprLoweringPropsTheory.stmt_state_rel_start_gas_obs] >>
  simp[] >> strip_tac >> simp[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem word_not_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a bt args es.
    (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
       (~is_word_type (expr_type e) ==>
        !tvt. evaluate_type (get_tenv cx) (lowered_value_type cenv e) =
                SOME tvt ==> type_memory_size tvt = 0) /\
       expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx ty e es /\
       (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
       (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
       expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
         cenv cx ty e es) /\
    bt = Not /\
    (builtin_args_length_ok bt (LENGTH args) ==> body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a bt args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a bt args) es
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule word_not_pre >>
  disch_then (qx_choose_then `e` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `args = [e]` SUBST_ALL_TAC >>
  qpat_x_assum `a = expr_type e` SUBST_ALL_TAC >>
  `body_exprs_full_ok cx [e]` by
    (first_x_assum irule >> simp[builtin_args_length_ok_def]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_exprs_full_ok cx [e]` mp_tac >>
     simp[body_exprs_full_ok_def] >>
     simp[Once body_expr_full_ok_def] >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin (expr_type e) Not [e]) es` by
    (rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
     drule lower_value_not >> strip_tac >>
     `?shadow_s1. lower_value compile_expr cenv (expr_type e)
        (gas_shadow_expr e) shadow_sa = (x,shadow_s1) /\
        gas_shadow_state s1 shadow_s1` by
       (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e`, `e` |-> `e`]
          gas_shadow_stmt_lower_value) >>
        simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
        disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >>
        simp[] >> strip_tac >>
        qexists_tac `SND (lower_value compile_expr cenv (expr_type e)
          (gas_shadow_expr e) shadow_sa)` >> simp[pairTheory.PAIR]) >>
     `is_word_type (expr_type e)` by
       (qpat_x_assum `is_bool_type _ \/ _` mp_tac >>
        Cases_on `expr_type e` >> simp[is_word_type_def] >>
        rename1 `BaseT b` >> Cases_on `b` >> simp[is_word_type_def] >>
        rename1 `BytesT bs` >> Cases_on `bs` >> simp[is_word_type_def] >>
        strip_tac >> gvs[]) >>
     drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
     `cs_extends s1 sb /\ s1.cs_next_var <= sb.cs_next_var` by
       (qpat_assum `(if _ then _ else _) s1 = _` mp_tac >>
        mp_tac (Q.SPECL [`expr_type e`, `cenv`, `x`] straight_fresh_not) >>
        metis_tac[straight_fresh_cs_extends]) >>
     `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
       (irule fn_has_code_split >> metis_tac[]) >>
     `(if expr_type e = BaseT BoolT then emit_op ISZERO [x]
        else compile_invert x (expr_type e) cenv) shadow_s1 = (op,shadow_sb)` by
       (qpat_x_assum `is_bool_type _ \/ _` kall_tac >>
        qpat_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _`
          mp_tac >>
        pure_rewrite_tac[gasShadowTheory.gas_shadow_expr_def,
          gasShadowTheory.gas_shadow_builtin_def, MAP] >>
        simp[NoAsms] >>
        disch_then (strip_assume_tac o MATCH_MP lower_value_not) >>
        gvs[gasShadowTheory.gas_shadow_expr_type]) >>
     `cs_extends shadow_sa shadow_s1` by
       metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
     `cs_extends shadow_s1 shadow_sb` by
       metis_tac[straight_fresh_not, straight_fresh_cs_extends] >>
     `fn_has_code shadow_sa shadow_s1 shadow_func` by
       metis_tac[fn_has_code_split] >>
     qpat_x_assum `expr_sim_full _ _ _ _ e es`
       (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
     disch_then (qspecl_then [`st0`, `sa`, `s1`, `shadow_sa`, `shadow_s1`,
       `x`, `s0`, `G0`, `tn0`] mp_tac) >>
     (impl_tac >- (simp[] >> metis_tac[expr_body_pre_gas_admissible])) >>
     strip_tac >>
     qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
     rewrite_tac[Q.INST [`bi` |-> `Not`] eval_expr_unop_action |> SIMP_RULE (srw_ss()) []] >>
     irule gas_outcome_full_bind_all >> rpt conj_tac
     >~ [`gas_marked_exec _ _ _ _ _ _ _`]
     >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
         qexistsl_tac [`mid`, `t`, `v`] >> fs[])
     >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
     >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
     >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
     >- (irule storage_trace_frame_bind_all >>
         simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
     >~ [`storage_trace_frame _`]
     >- (simp[storage_trace_frame_def, unop_result_def]) >>
     qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted` >>
     reverse conj_tac
     >- (qunabbrev_tac `childR` >>
         irule gas_outcome_full_post_source >>
         qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
         simp[expr_exit_def] >> rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def]) >>
     qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
     strip_tac >>
     `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
        mid.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qunabbrev_tac `childQ` >> BETA_TAC >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (assume_tac o SIMP_RULE (srw_ss()) []) >>
     qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
     disj1_tac >> qexists_tac `v` >> simp[] >>
     `bind (eval_expr cx e) (read_result cx)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
        (INL v, mid with gas_obs := [])` by
       (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
        pure_rewrite_tac[APPEND_NIL] >> disch_then ACCEPT_TAC) >>
     `expr_body_pre cenv cx env e
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     drule_at (Pos last) (CONV_RULE (DEPTH_CONV ETA_CONV)
       exprSimSourceTheory.expr_body_pre_eval) >>
     disch_then (qspecl_then [`cenv`, `env`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
           value_has_type tv v` by
       (qpat_x_assum `!v'. INL v = INL v' ==> _` (qspec_then `v` mp_tac) >>
        simp[vyperTypeExprResultTheory.expr_result_typed_def,
          vyperTypeExprSoundnessTheory.expr_runtime_typed_def,
          vyperTypeInvariantsTheory.value_result_typed_def] >>
        gvs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
     `eval_operand x t = SOME (typed_val_to_w256 tv v)` by
       (irule exprBopSimPropsTheory.expr_val_rel_typed >>
        qexistsl_tac [`cx`, `expr_type e`] >> simp[] >>
        qpat_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ _`
          (mp_tac o cj 3 o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
        simp[]) >>
     `local_ptrs_reserved cenv s1` by
       metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
     `allocas_from lo t` by
       (qpat_assum `ghost_inv_at _ _ _ _ _ mid _ _ t`
          (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
        simp[]) >>
     `op_taint tn1 x = {}` by
       (qpat_assum `ptr_val_ok _ _ _ x _ _ _`
          (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_val_ok_def]) >>
        simp[]) >>
     `stmt_state_rel (storage_trace_horizon mid.storage_trace)
        ctx func cenv cx mid t` by
       (qpat_assum `expr_post _ _ _ _ _ e _ _ _ _ _ _ _ _`
          (mp_tac o cj 1 o REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
        simp[]) >>
     `alloca_inv t` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
     `!nsid m. expr_type e = FlagT nsid /\ tv = FlagTV m ==>
        cenv.ce_flag_n_members (nsid_to_string nsid) = m` by
       (qpat_assum `expr_sim_inv _ _ _ _`
          (mp_tac o REWRITE_RULE [expr_sim_inv_def]) >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        rpt strip_tac >>
        qpat_x_assum `evaluate_type (get_tenv cx) _ = SOME _` mp_tac >>
        asm_rewrite_tac[vyperValueTheory.evaluate_type_def] >>
        simp[AllCaseEqs()] >> metis_tac[]) >>
     `!y sz. cenv.ce_return_buf = SOME (PtrVar (Var y) sz) ==>
        not_fresh_at s1 y` by
       metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
     `!y sz. cenv.ce_return_pc = SOME (PtrVar (Var y) sz) ==>
        not_fresh_at s1 y` by
       metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
     `!H. valid_horizon cx st0 H mid.storage_trace ==>
        stmt_state_rel H ctx func cenv cx mid t /\
        ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
       (rpt strip_tac >>
        qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
          (qspec_then `H` mp_tac) >> simp[] >>
        metis_tac[cj 1 loweringPostsTheory.expr_post_def]) >>
     drule_all (word_not_typed_suffix |> SPEC_ALL |> Q.INST
       [`tys` |-> `[expr_type e]`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
        `DF` |-> `DF`, `st0` |-> `st0`, `PG` |-> `PG`]) >>
     disch_then (qspecl_then [`shadow_ctx`, `e`, `PG`] strip_assume_tac) >>
     irule gas_outcome_full_pure >>
     reverse conj_tac >- simp[] >>
     qexistsl_tac [`G'`, `mid`, `INL v'`, `t'`, `tn'`] >>
     simp[] >> conj_tac
     >- (gen_tac >> simp[exprSimUnopComposePropsTheory.unop_result_gas_obs]) >>
     qx_gen_tac `H` >> strip_tac >> simp[] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       (?v. _) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
     `expr_val_rel cx (expr_type e) v' op t'` by
       (simp[loweringPostsTheory.expr_val_rel_def] >> metis_tac[]) >>
     conj_tac
     >- (irule word_not_parent_post >> simp[] >>
         qexistsl_tac [`s1`, `t`, `v`, `x`] >> simp[] >>
         metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
     simp[vyperASTTheory.expr_type_def, exprSimMemDefsTheory.expr_store_bound_def,
          loweringPostsTheory.post_value_type_def] >>
     conj_tac
     >- (qpat_assum `!H. valid_horizon _ _ H _ ==> ghost_inv_at _ _ _ _ _ _ G' tn' t'`
           (qspec_then `H` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         simp[NoAsms, bodyPtrDefsTheory.ghost_inv_at_def] >>
         rpt strip_tac >> first_assum ACCEPT_TAC) >>
     conj_tac
     >- (irule bodyPtrDefsTheory.ptr_val_ok_word >> simp[]) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> (?v. _) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
     qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ G1 tn1` mp_tac >>
     simp[bodyPtrDefsTheory.ghost_kept_at_def] >>
     strip_tac >> reverse conj_tac
     >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     `not_fresh_at s1 x'` by
       metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
     metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  first_x_assum (irule o SPEC_ALL) >>
  simp[vyperASTTheory.expr_type_def] >>
  conj_tac >- metis_tac[exprSimUnopPropsTheory.compile_not_abs_stack] >>
  conj_tac >- metis_tac[exprLoweringPropsTheory.eval_expr_builtin_value] >>
  `is_word_type (expr_type e)` by
    (qpat_x_assum `is_bool_type _ \/ _` mp_tac >>
     Cases_on `expr_type e` >> simp[is_word_type_def] >>
     rename1 `BaseT b` >> Cases_on `b` >> simp[is_word_type_def] >>
     rename1 `BytesT bs` >> Cases_on `bs` >> simp[is_word_type_def] >>
     strip_tac >> gvs[]) >> simp[]
QED
