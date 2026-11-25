(* The linked forced-value run for a unary Not application. *)
Theory bodyWordNotEndpointMods
Ancestors
  bodyWordNotShapeMods bodyFullPostsMods bodyFullShadowBodyInv bodyForRangeScalarFrameMods
  bodyWriteSubscriptSourceMods gasOutcomeFullBindMods gasOutcomeFullPostMods
  exprSimWordBuiltins exprSimUnopProps exprSimUnopCompose exprBopSimProps
  gasShadowCompileStmtHelpers gasShadowCompileBase vyperStorageTrace
  fragGasSeqPtr fragGasOriginPtr exprSimSource stateRelProj exprBodyPreProps
  decoderGhostFramePtr lowerDloadPtrScalar ptrDisciplineEmptyTaint
  emitHelperProps emitHelper compileEnv fragExec venomInst venomState exprLowering
  finite_map venomExecSemantics builtinSimple vyperValueOperation valueEncoding
  vyperInterpreter vyperContext vyperTypeSystem vyperTyping vyperAST list
  gasShadowState exprLoweringProps bodyFullPredsMods exprSimHypsDefs
  gasContext exprSimDefs vyperState gasExemptCertMods exprSimWordArgs
  loweringPosts bodyPtrDefs exprSimMemDefs
Libs
  intLib

Theorem not_inst[local]:
  (is_bool_type ann \/ is_uint256_type ann \/ is_bytes32_type ann \/
   is_flag_type ann) /\
  evaluate_type (get_tenv cx) ann = SOME tv /\ value_has_type tv v /\
  (!nsid m. ann = FlagT nsid /\ tv = FlagTV m ==>
    cenv.ce_flag_n_members (nsid_to_string nsid) = m) /\
  (if ann = BaseT BoolT then emit_op ISZERO [x]
   else compile_invert x ann cenv) sa = (op,sb) /\
  eval_operand x s = SOME (typed_val_to_w256 tv v) /\ op_taint tn x = {} ==>
  ?k xs v'.
    emit_op k xs sa = (op,sb) /\
    unop_result cx ann Not [ann] v es = INL v' /\
    (k = ISZERO \/ k = NOT \/ k = XOR) /\
    EVERY (\a. op_taint tn a = {}) xs /\
    !out. step_inst_base (mk_inst sa.cs_next_id k xs [out]) s =
      OK (update_var out (typed_val_to_w256 tv v') s)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule not_type_cases >> strip_tac >>
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
  irule step_XOR >> simp[eval_operand_def]
QED

Theorem not_scalar_step[local]:
  (k = ISZERO \/ k = NOT \/ k = XOR) /\
  EVERY (\a. op_taint tn a = {}) xs /\
  step_inst_base (mk_inst iid k xs [out]) s = OK (update_var out w s) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  !D lo func G. allocas_from lo s ==>
    ptr_inst_ok D lo 0 ctx func G tn (mk_inst iid k xs [out]) s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  `step_inst 0 ctx (mk_inst iid k xs [out]) s = OK (update_var out w s)` by
    (qpat_x_assum `k = ISZERO \/ _` strip_assume_tac >>
     simp[step_inst_non_invoke, mk_inst_def] >> metis_tac[mk_inst_def]) >>
  simp[ptrSafeRunTheory.ptr_inst_ok_def, ptrDisciplineTheory.access_ok_def,
       ptrDisciplineTheory.taint_ok_def, contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def, mk_inst_def] >>
  gvs[mk_inst_def, update_var_def, EVERY_MEM] >> metis_tac[]
QED

Theorem not_scalar_taint[local]:
  (k = ISZERO \/ k = NOT \/ k = XOR) ==>
  step_taint (mk_inst iid k xs [out]) s (update_var out w s) tn =
    tn with t_var := tn.t_var |+ (out,{})
Proof
  strip_tac >>
  `out_taint tn (mk_inst iid k xs [out]) s = {}` by
    (irule out_taint_opcode_exclusion >> gvs[mk_inst_def]) >>
  `written_taint tn (mk_inst iid k xs [out]) s = {}` by
    (irule written_taint_opcode_exclusion >> gvs[mk_inst_def]) >>
  `new_site_bytes s (update_var out w s) = {}` by
    (irule new_site_bytes_unchanged >> simp[update_var_def]) >>
  simp[ptrDisciplineTheory.step_taint_def, ptrDisciplineTheory.mem_taint_def,
       ptrDisciplineTheory.set_var_taint_def, mk_inst_def] >>
  gvs[ptrDisciplineTheory.step_writes_def,
      codegenRelTheory.source_memory_write_ranges_def,
      ptrDisciplineTheory.range_bytes_def, ptrDisciplineTheory.store_taint_def,
      ptrDisciplineTheory.imm_taint_def, ptrDisciplineTheory.adopt_reset_def,
      ptrDisciplineTheory.taint_component_equality]
QED

Theorem not_scalar_suffix[local]:
  emit_op k xs sa = (op,sb) /\ (k = ISZERO \/ k = NOT \/ k = XOR) /\
  EVERY (\a. op_taint tn a = {}) xs /\
  (!out. step_inst_base (mk_inst sa.cs_next_id k xs [out]) s = OK (update_var out w s)) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out t G' tn'.
    out = STRING #"%" (toString sa.cs_next_var) /\
    t = (update_var out w s) with vs_inst_idx := LENGTH sb.cs_current_insts /\
    alloca_history func t /\ t.vs_current_bb = sb.cs_current_bb /\
    eval_operand op t = SOME w /\ op_prov G' op = NONE /\ op_taint tn' op = {} /\
    (!y. not_fresh_at sa y ==>
       lookup_var y t = lookup_var y s /\ FLOOKUP G' y = FLOOKUP G y /\
       op_taint tn' (Var y) = op_taint tn (Var y)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!D lo. allocas_from lo s ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn'))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id k xs [out]` >>
  qabbrev_tac `u = update_var out w s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `inst`, Abbr `out`]) >>
  `step_inst_base inst s = OK u` by simp[Abbr `inst`, Abbr `u`] >>
  `~is_terminator inst.inst_opcode` by gvs[Abbr `inst`, mk_inst_def, is_terminator_def] >>
  `alloca_history func t` by
    (`lookup_block s.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
     drule_all allocaHistoryTheory.alloca_history_base_step >> simp[Abbr `t`]) >>
  `step_taint inst s u tn = tn with t_var := tn.t_var |+ (out,{})` by
    (simp[Abbr `inst`, Abbr `u`] >> irule not_scalar_taint >> simp[]) >>
  `!D lo. allocas_from lo s ==>
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,step_prov PG G inst u,step_taint inst s u tn)` by
    suspend "path" >>
  qexistsl_tac [`out`, `t`, `step_prov PG G inst u`, `step_taint inst s u tn`] >>
  `op = Var out` by
    gvs[Abbr `out`, emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by fs[] >>
  simp[] >>
  suspend "frame"
QED

Resume not_scalar_suffix[frame]:
  `op_prov (step_prov PG G inst u) (Var out) = NONE` by
    (irule bodyPtrDefsTheory.step_prov_out_none >>
     simp[Abbr `inst`, mk_inst_def] >>
     irule bodyPtrDefsTheory.out_prov_other_none >> gvs[mk_inst_def]) >>
  `!y. not_fresh_at sa y ==> y <> out` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def, Abbr `out`] >>
  `!y. not_fresh_at sa y ==> FLOOKUP (step_prov PG G inst u) y = FLOOKUP G y` by
    (rpt strip_tac >> irule step_prov_other_output >> simp[Abbr `inst`, mk_inst_def]) >>
  simp[Abbr `t`, Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, ptrDisciplineTheory.op_taint_def,
       ptrDisciplineTheory.allocas_below_fmp_def] >>
  qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s`
    (ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_below_fmp_def])
QED

Resume not_scalar_suffix[path]:
  rpt gen_tac >> strip_tac >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (simp[Abbr `inst`] >> irule not_scalar_step >> simp[] >>
     qexists_tac `w` >> simp[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK t, step_prov PG G inst u, step_taint inst s u tn)` by
    (`inst.inst_opcode <> GAS` by gvs[Abbr `inst`, mk_inst_def] >>
     mp_tac (straight_line_origin_ptr_edge |> Q.INST [`i` |-> `inst`, `u` |-> `u`]) >>
     simp[] >> simp[Abbr `t`] >> disch_then irule >>
     simp[] >> gvs[Abbr `inst`, mk_inst_def, is_terminator_def,
         unitTransformDefsTheory.inst_mem_below_frontier_def,
         contextCodegenRelTheory.source_memory_read_ranges_def,
         codegenRelTheory.source_memory_write_ranges_def]) >>
  `~t.vs_halted` by simp[Abbr `t`, Abbr `u`, update_var_def] >>
  metis_tac[gas_origin_ptr_path_rules, APPEND_NIL]
QED

Finalise not_scalar_suffix

Theorem not_lower_cuts[local]:
  lower_value compile_expr cenv ty (Builtin (expr_type e) Not [e]) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin (expr_type e) Not [e])) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func ==>
  ?x s1 shadow_s1.
    lower_value compile_expr cenv (expr_type e) e sa = (x,s1) /\
    lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
      (gas_shadow_expr e) shadow_sa = (x,shadow_s1) /\
    (if expr_type e = BaseT BoolT then emit_op ISZERO [x]
     else compile_invert x (expr_type e) cenv) s1 = (op,sb) /\
    gas_shadow_state s1 shadow_s1 /\ sa.cs_next_var <= s1.cs_next_var /\
    fn_has_code sa s1 func /\ fn_has_code s1 sb func /\
    fn_has_code shadow_sa shadow_s1 shadow_func
Proof
  strip_tac >>
  qpat_assum `lower_value _ cenv _ (Builtin _ Not [_]) _ = _`
    (strip_assume_tac o MATCH_MP lower_value_not) >>
  Cases_on `lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
    (gas_shadow_expr e) shadow_sa` >>
  rename1 `lower_value _ _ _ (gas_shadow_expr e) _ = (shadow_x,shadow_s1)` >>
  `shadow_x = x /\ gas_shadow_state s1 shadow_s1` by
    (`gas_shadow_compiles (lower_value compile_expr cenv (expr_type e) e)
        (lower_value compile_expr (gas_shadow_env T cenv) (expr_type e)
          (gas_shadow_expr e))` by irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  qpat_x_assum `shadow_x = x` SUBST_ALL_TAC >>
  `(if expr_type e = BaseT BoolT then emit_op ISZERO [x]
    else compile_invert x (expr_type e) cenv) shadow_s1 = (op,shadow_sb)` by
    (qpat_assum `lower_value _ _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _` mp_tac >>
     pure_rewrite_tac[gasShadowTheory.gas_shadow_expr_def,
       gasShadowTheory.gas_shadow_builtin_def, MAP] >>
     simp[NoAsms] >> disch_then (strip_assume_tac o MATCH_MP lower_value_not) >>
     gvs[gasShadowTheory.gas_shadow_expr_type, compile_invert_gas_shadow_env]) >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\ cs_extends shadow_sa shadow_s1` by
    metis_tac[cj 2 compile_expr_grows] >>
  `cs_extends s1 sb /\ cs_extends shadow_s1 shadow_sb` by
    metis_tac[straight_fresh_not, straight_fresh_cs_extends] >>
  qexistsl_tac [`x`,`s1`,`shadow_s1`] >> simp[] >>
  metis_tac[fn_has_code_split]
QED

Theorem not_child_pre[local]:
  expr_body_pre_mods mods cenv cx env (Builtin (expr_type e) Not [e]) es /\
  body_expr_full_ok_mods mods exps cx e ==>
  expr_body_pre_mods mods cenv cx env e es /\
  (is_bool_type (expr_type e) \/ is_uint256_type (expr_type e) \/
   is_bytes32_type (expr_type e) \/ is_flag_type (expr_type e))
Proof
  strip_tac >>
  `body_exprs_full_ok_mods mods exps cx [e]` by
    (simp[Once body_exprs_full_ok_mods_def] >> simp[Once body_exprs_full_ok_mods_def]) >>
  `builtin_args_length_ok Not (LENGTH [e])` by simp[builtin_args_length_ok_def] >>
  drule_all word_not_shape_mods >> simp[] >> strip_tac >>
  qpat_assum `expr_body_pre_mods _ _ _ _ (Builtin _ Not _) _`
    (mp_tac o MATCH_MP expr_body_pre_mods_well_typed) >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def]
QED

Theorem not_child_type_result[local]:
  expr_body_pre_mods mods cenv cx env e es /\ body_const_cells_agree_mods mods cx env es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := readings) = (INL v,mid) ==>
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v /\
       (!nsid m. expr_type e = FlagT nsid /\ tv = FlagTV m ==>
         cenv.ce_flag_n_members (nsid_to_string nsid) = m)
Proof
  strip_tac >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := readings) /\
   body_const_cells_agree_mods mods cx env (es with gas_obs := readings)` by
    simp[bodyBranchCellFrameModsTheory.body_const_cells_agree_mods_branch_updates] >>
  drule_all_then strip_assume_tac write_index_read_source_mods >>
  `env.type_defs = get_tenv cx` by
    (drule expr_sim_inv_mods_env >>
     simp[vyperTypeInvariantsTheory.env_consistent_def,
          vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  gvs[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `evaluate_type _ (FlagT _) = _` mp_tac >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  qpat_x_assum `expr_sim_inv_mods _ _ _ _ mid`
    (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
  qpat_assum `!nsid m. FLOOKUP (get_tenv cx) nsid = SOME (FlagArgs m) ==> _` irule >> simp[]
QED

Theorem not_admissible_head[local]:
  gas_admissible (bind src next) expr_res_ok es ==>
  gas_admissible (src : evaluation_state -> value evaluation_result) expr_res_ok es
Proof
  simp[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum irule >> qexistsl_tac [`ee`,`gs`] >> simp[bind_def]
QED

Theorem not_parent_post[local]:
  expr_post_mods H ctx func cenv cx e es sa s1 s0 mid v x t /\
  u = (update_var out w t) with vs_inst_idx := idx /\
  local_ptrs_reserved cenv s1 /\ out = STRING #"%" (toString s1.cs_next_var) /\
  (!y. not_fresh_at s1 y ==> lookup_var y u = lookup_var y t) /\
  expr_val_rel cx (expr_type e) v' op u /\ is_word_type (expr_type e) /\
  sa.cs_next_var <= s1.cs_next_var ==>
  expr_post_mods H ctx func cenv cx (Builtin (expr_type e) Not [e]) es sa sb s0
    mid v' op u
Proof
  strip_tac >> fs[expr_post_mods_def] >>
  `stmt_state_rel H ctx func cenv cx mid u` by
    (simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_update_var >>
     conj_tac >- (irule local_ptrs_reserved_fresh >> qexists_tac `s1` >> simp[]) >>
     metis_tac[expr_post_state]) >>
  gvs[] >> conj_tac
  >- (irule expr_post_unop >> simp[] >>
      qexistsl_tac [`s1`,`t`,`v`,`x`] >> fs[update_var_def]) >>
  irule immutable_frame_mods_exterior_frame >>
  qexistsl_tac [`mid`, `t`, `s1`] >> fs[update_var_def]
QED

Theorem not_ghost_kept[local]:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!y. not_fresh_at sa y ==> FLOOKUP G' y = FLOOKUP G y /\
      op_taint tn' (Var y) = op_taint tn (Var y)) /\ tn'.t_mem = tn.t_mem ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'
Proof
  simp[ghost_kept_at_def] >> metis_tac[]
QED

Theorem word_not_value_sim_mods:
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\ body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin (expr_type e) Not [e]) es /\
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx (expr_type e) e es /\
  (!sa. ?a x s1. compile_expr cenv (expr_type e) e sa = (StackValue a x,s1)) /\
  (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) /\
  is_word_type (expr_type e) /\ body_expr_full_ok_mods mods exps cx e ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  strip_tac >> drule_all not_child_pre >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_sim_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac not_lower_cuts >>
  qpat_x_assum `gas_admissible _ _ _`
    (assume_tac o PURE_REWRITE_RULE [SIMP_RULE (srw_ss()) []
       (Q.INST [`bi` |-> `Not`] eval_expr_unop_action)]) >>
  simp[eval_expr_unop_action] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    (drule not_admissible_head >> simp[]) >>
  qpat_x_assum `expr_sim_full_mods _ _ _ _ e es` (mp_tac o REWRITE_RULE [expr_sim_full_mods_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`s1`,`shadow_sa`,`shadow_s1`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_value >> goal_assum (drule_at Any) >> fs[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame, storage_trace_frame_read_result]
  >~ [`storage_trace_frame _`] >- simp[storage_trace_frame_def, unop_result_def] >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      simp[Abbr `childR`] >> gen_tac >> Cases >> simp[expr_exit_def]) >>
  suspend "continue"
QED

Resume word_not_value_sim_mods[continue]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?v. res = INL v /\ _`
    (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `res = INL v` SUBST_ALL_TAC >> disj1_tac >> qexists_tac `v` >> simp[] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn frame =>
       qpat_assum `!tail. bind _ _ _ = _`
         (qspec_then `[]` (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL,frame])))) >>
  drule_all_then strip_assume_tac not_child_type_result >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx
     e es sa s1 s0 mid v x t` by fs[expr_post_mods_def] >>
  drule_then assume_tac expr_post_state >> drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `eval_operand x t = SOME (typed_val_to_w256 tv v)` by
    (irule expr_val_rel_typed >> qexistsl_tac [`cx`, `expr_type e`] >> simp[] >>
     qhdtm_assum `expr_post` (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     qpat_assum `post_value_type cenv e = expr_type e` (fn ty_eq =>
       qhdtm_assum `expr_val_rel` (ACCEPT_TAC o REWRITE_RULE [ty_eq]))) >>
  `op_taint tn1 x = {}` by
    (qhdtm_assum `ptr_val_ok` (mp_tac o REWRITE_RULE [ptr_val_ok_def]) >> simp[]) >>
  drule_at (Pat `(if _ then _ else _) _ = _`)
    (not_inst |> Q.INST [`ann` |-> `expr_type e`, `es` |-> `mid`, `tn` |-> `tn1`]) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (qspecl_then [`tn1`,`mid`,`cx`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `k` (qx_choose_then `xs` (qx_choose_then `v'`
    (map_every assume_tac o CONJUNCTS)))) >>
  `!out. step_inst_base (mk_inst s1.cs_next_id k xs [out]) t =
      OK (update_var out (typed_val_to_w256 tv v') t)` by simp[] >>
  drule_all not_scalar_suffix >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`,`G1`]
    (qx_choose_then `out` (qx_choose_then `t'` (qx_choose_then `G'` (qx_choose_then `tn'`
      (map_every assume_tac o CONJUNCTS)))))) >>
  suspend "suffix"
QED

Resume word_not_value_sim_mods[suffix]:
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`G'`,`mid`,`INL v'`,`t'`,`tn'`] >>
  conj_tac >- simp[exprSimUnopComposePropsTheory.unop_result_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >> BETA_TAC >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?v'. INL v = INL v' /\ _` strip_assume_tac >>
  conj_tac
  >- (qpat_assum `!D lo. _ ==> gas_origin_ptr_path _ _ _ _` irule >>
      qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ mid _ _ t`
        (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
      first_assum ACCEPT_TAC) >>
  suspend "post"
QED

Resume word_not_value_sim_mods[post]:
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!y. not_fresh_at sa y ==> not_fresh_at s1 y` by
    (rpt strip_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `expr_val_rel cx (expr_type e) v' op t'` by
    (simp[expr_val_rel_def] >> goal_assum (drule_at Any) >> simp[]) >>
  `expr_post_mods H ctx func cenv cx (Builtin (expr_type e) Not [e])
     es sa sb s0 mid v' op t'` by
    (irule not_parent_post >>
     qpat_assum `expr_post_mods H _ _ _ _ e _ _ _ _ mid _ x t` (irule_at Any) >>
     qpat_assum `t' = (_ with vs_inst_idx := _)` (irule_at Any) >> simp[]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx mid G' tn' t'` by
    (irule ghost_inv_at_mods_exterior_frame >> qexistsl_tac [`G1`,`mid`,`t`,`s1`,`tn1`] >>
     simp[update_var_def]) >>
  `t'.vs_inst_idx = LENGTH sb.cs_current_insts /\ t'.vs_alloca_next = t.vs_alloca_next` by
    simp[update_var_def] >>
  qpat_x_assum `t' = (_ with vs_inst_idx := _)` kall_tac >>
  simp[expr_type_def, expr_store_bound_word, ptr_val_ok_word] >>
  irule not_ghost_kept >> qexistsl_tac [`G1`,`tn1`] >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!y. not_fresh_at s1 y ==> _` (drule_then strip_assume_tac) >> simp[]
QED

Finalise word_not_value_sim_mods
