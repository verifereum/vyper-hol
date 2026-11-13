(* Counted immutable target root and attribute construction. *)
Theory popNestedImmutableConstructorMemory
Ancestors
  exprSimPopImmutableTarget fragGasPathMem allocaHistoryFragment
  exprLowering compileEnv gasOutcome gasSummary gasSummaryCompose fragGasMode
  vyperInterpreter vyperState venomExecSemantics loweringStateRelDefs vyperLookup
  loweringPosts venomState bodyFieldMemoryProps emitHelperProps emitHelper
  fragGasSeqMem fragExecMem fragExec venomInst list rich_list exprSimDefs exprLoweringProps
  targetPlaceSim targetPlaceSimDefs targetPlaceSimCasesBase targetSubscriptSplit
  stmtLoweringMono exprSimHypsDefs vyperTypeSystem vyperTypeEnv vyperTypeInvariants
  fragGasPath gasExemptCert stmtSimProps stmtSimAssignAttr pair gasContext

Theorem imm_target_root_walk_mem:
  !ctx func cenv cx env es ty src id sa sb r s0.
    cx.in_deploy /\ cenv.ce_is_ctor /\
    (!ts. get_module_code cx src = SOME ts ==>
          find_var_decl_by_name id ts = NONE) /\
    (!ty0. FLOOKUP env.bare_global_assignable (src,id) = SOME ty0 ==>
           cenv.ce_module_var_type (src,id) = SOME ty0) /\
    expr_sim_inv cenv cx env es /\
    type_place_target env (TopLevelNameTarget (src,id)) = SOME (Type ty) /\
    compile_get_target_ptr compile_expr cenv (TopLevelNameTarget (src,id)) sa = (r,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_base_place cx (TopLevelNameTarget (src,id))) target_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (eval_base_place cx (TopLevelNameTarget (src,id))) (es,s0)
      (\res ee t. ?pv. res = INL pv /\
         imm_target_post ctx func cenv cx es sa sb s0 ee pv ty r t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts /\
         alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
      (\res ee r. expr_exit res r)
Proof
  rpt strip_tac >>
  drule_all imm_target_root_assignable >> strip_tac >>
  drule_all imm_target_root_layout >> strip_tac >>
  `cenv.ce_module_var_type (src,id) = SOME ty` by metis_tac[] >>
  gvs[compile_get_target_ptr_def, comp_return_def] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (ImmutablePlace cenv.ce_module id []))`, `es`, `OK s0`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, gas_marked_path_def, gas_path_mem_rules,
           evaluate_def, lookup_global_def, bind_def,
           lift_option_type_def, return_def, get_immutables_def,
           get_address_immutables_def] >>
      Cases_on `ALOOKUP es.immutables cx.txn.target` >>
      gvs[get_source_immutables_def, return_def, raise_def]) >>
  disj1_tac >> simp[] >>
  simp[imm_target_post_def, imm_place_at_def, eval_operand_def,
       exprSimPropsTheory.locals_kept_mem, mem_path_offset_def, evaluate_subscripts_def]
QED

Theorem imm_attr_add_path_mem[local]:
  imm_target_post ctx func cenv cx es sa sm s0 ee pv ty rb t /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [FST rb; Lit (n2w off)] sm = (dst,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ alloca_history func t /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand (FST rb) t = SOME w0 /\
  imm_place_at cenv cx ee pv' (w0 + n2w off) ty' ==>
  ?q. gas_marked_path T ctx func t 0 (OK q) /\
    imm_target_post ctx func cenv cx es sa sb s0 ee pv' ty'
      (dst,SOME LocCode,SOME (ValPT ty')) q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ t.vs_alloca_next <= q.vs_alloca_next
Proof
  strip_tac >> drule_all imm_target_post_add >> strip_tac >>
  `alloca_inv t` by fs[imm_target_post_def, stmt_state_rel_def] >>
  `alloca_history func (q with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (drule_all attr_add_history >> simp[]) >>
  drule_all buffer_emit_add_run >> strip_tac >>
  `q = update_var (STRING #"%" (toString sm.cs_next_var)) (w0 + n2w off) t` by
    gvs[] >>
  qexists `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def] >> reverse conj_tac
  >- (gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
          comp_ignore_bind_def, comp_return_def, emit_def, update_var_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `?bb rest. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    DROP t.vs_inst_idx bb.bb_instructions = emitted_insts sm sb ++ rest` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) t` by
    (irule attr_add_prefix_mem_ok >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sm sb)` by simp[mk_inst_def, is_terminator_def] >>
  `isPREFIX (emitted_insts sm sb) (DROP t.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_mem >>
  simp[mk_inst_def]
QED

Theorem imm_target_attr_step_mem:
  !ctx func cenv cx env es sa sb s0 bt fld fty r.
    target_pre cenv cx env (AttributeTarget bt fld) es /\
    local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\ alloca_history func s0 /\
    type_place_target env (AttributeTarget bt fld) = SOME (Type fty) /\
    compile_get_target_ptr compile_expr cenv (AttributeTarget bt fld) sa = (r,sb) /\
    fn_has_code sa sb func /\
    gas_admissible (eval_base_place cx (AttributeTarget bt fld)) target_res_ok es /\
    (!bty sm rb.
      type_place_target env bt = SOME (Type bty) /\
      compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
      fn_has_code sa sm func /\
      gas_admissible (eval_base_place cx bt) target_res_ok es ==>
      gas_outcome T (cx_tops cx) (ctx,func) (eval_base_place cx bt) (es,s0)
        (\res ee t. ?pv. res = INL pv /\
          imm_target_post ctx func cenv cx es sa sm s0 ee pv bty rb t /\
          t.vs_current_bb = sm.cs_current_bb /\
          t.vs_inst_idx = LENGTH sm.cs_current_insts /\
          alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
        (\res ee r. expr_exit res r)) ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (eval_base_place cx (AttributeTarget bt fld)) (es,s0)
      (\res ee t. ?pv. res = INL pv /\
        imm_target_post ctx func cenv cx es sa sb s0 ee pv fty r t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
      (\res ee r. expr_exit res r)
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[target_pre_def] >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ bty fld = SOME fty` >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?sid. bty = StructT sid` by
    (Cases_on `bty` >> gvs[attribute_type_def]) >> gvs[] >>
  drule compile_get_target_ptr_attr >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_get_target_ptr, SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_emit_op, SND] >>
  `cs_extends sa sm /\ cs_extends sm sb /\ sa.cs_next_var <= sm.cs_next_var`
    by fs[ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `eval_base_place cx (AttributeTarget bt fld) =
     bind (eval_base_place cx bt) (\pv. extend_place cx pv (AttrSubscript fld))`
    by simp[FUN_EQ_THM, Once evaluate_def] >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >> REWRITE_TAC [th]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, bind_def] >> rpt strip_tac >>
     Cases_on `res` >> simp[target_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >> simp[target_res_ok_def]) >>
  qpat_x_assum `fn_has_code sa sm func /\ _ ==> gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "summary" >>
  qexists `marks` >> disj2_tac >>
  qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_result >> fs[ignore_bind_def]
QED

Resume imm_target_attr_step_mem[summary]:
  qexists `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >> gvs[]
  >~ [`exit_result r`]
  >- (Cases_on `res` >> gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >> qexistsl [`INR y`, `es_end`, `r`] >> simp[] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `expr_sim_inv cenv cx env (es_end with gas_obs := [])` by
    metis_tac[target_subscript_marked_base_inv] >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL pv, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  Cases_on `extend_place cx pv (AttrSubscript fld) (es_end with gas_obs := [])` >>
  rename1 `extend_place _ _ _ _ = (res1,es2)` >>
  `!m. res1 <> INR (Error (TypeError m))` by
    (qpat_x_assum `gas_admissible (bind _ _) _ _` mp_tac >>
     simp[gas_admissible_def] >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[bind_def] >> rpt strip_tac >> gvs[target_res_ok_def]) >>
  `?w0. eval_operand (FST rb) t = SOME w0 /\
    imm_place_at cenv cx (es_end with gas_obs := []) pv w0 (StructT sid)` by
    (fs[imm_target_post_def] >> metis_tac[]) >>
  `FST (SND rb) = SOME LocCode /\
    SND (SND rb) = SOME (ValPT (StructT sid))` by fs[imm_target_post_def] >>
  `target_field_type cenv (SND (SND rb)) fld = SOME (ValPT fty)` by
    (drule_all attribute_type_struct_field >> strip_tac >> simp[target_field_type_def]) >>
  drule_all imm_attr_source_tail >> strip_tac >>
  drule_all imm_attr_place_step >> strip_tac >> gvs[] >>
  suspend "append"
QED

Resume imm_target_attr_step_mem[append]:
  drule_at (Pat `emit_op _ _ _ = _`) imm_attr_add_path_mem >>
  disch_then (drule_at (Pat `imm_target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL pv'`, `es_end`, `OK q`] >> simp[] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
         |> REWRITE_RULE [APPEND_NIL]) >>
  qexistsl [`es_end`, `t`, `pv`] >>
  simp[gas_marked_exec_def, gas_explicit_nil] >> gen_tac >>
  qpat_x_assum `!gs. extend_place _ _ _ _ = _` (qspec_then `tail` mp_tac) >> simp[]
QED

Finalise imm_target_attr_step_mem
