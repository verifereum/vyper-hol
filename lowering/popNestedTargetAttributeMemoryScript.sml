(* Counted ADD continuation for nested target fields. *)
Theory popNestedTargetAttributeMemory
Ancestors
  popNestedTargetReadinessMemory
  targetPlaceSimMem targetPlaceSimCasesBase bodyMemEmitOpFrame
  exprLoweringProps emitHelperProps stmtSimProps compileEnv loweringPosts
  loweringStateRelDefs exprSimDefs exprSimHypsDefs fragExec
  venomExecProofs venomState venomInst exprSimBuffer
  stmtLoweringMono fragGasMode fragGasPath fragGasPathMem gasOutcome gasSummary
  gasSummaryCompose gasExemptCert gasContext exprSimSource vyperTypeSystem
  vyperTypeEnv vyperTypeInvariants vyperInterpreter vyperState vyperAST
  exprLowering targetPlaceSimDefs targetPlaceSim pair list

Theorem pop_nested_target_attr_add_mem[local]:
  target_post ctx func cenv cx es sa sm s0 es1 pv vt rb t /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [FST rb; Lit (n2w off)] sm = (dst, sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
  eval_operand (FST rb) t = SOME w0 /\
  place_ptr_rel cenv cx t pv' (w0 + n2w off) (FST (SND rb)) vt' /\
  place_readable cx es1 pv' ==>
  ?q. gas_marked_path T ctx func t 0 (OK q) /\
      target_post ctx func cenv cx es sa sb s0 es1 pv' vt'
        (dst, FST (SND rb), SOME (value_type_place vt')) q /\
      q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func q /\ q.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  drule_all target_post_add >> strip_tac >>
  drule_all buffer_emit_add_run >> strip_tac >> gvs[] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es1 t` by fs[target_post_def] >>
  `step_inst_base
     (mk_inst sm.cs_next_id ADD [FST rb; Lit (n2w off)]
       [STRING #"%" (toString sm.cs_next_var)]) t =
     OK (update_var (STRING #"%" (toString sm.cs_next_var)) (w0 + n2w off) t)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  drule_at (Pat `emit_op _ _ _ = _`) emit_op_word_path_frame_mem >>
  disch_then (qspec_then `w0 + n2w off` mp_tac) >>
  disch_then (qspec_then `t` mp_tac) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString sm.cs_next_var))
    (w0 + n2w off) t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[]
QED

Theorem pop_nested_target_attr_mem:
  target_pre cenv cx env (AttributeTarget bt fld) es /\
  target_sim_mem ctx func cenv cx env bt es ==>
  target_sim_mem ctx func cenv cx env (AttributeTarget bt fld) es
Proof
  strip_tac >> simp[target_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  irule pop_nested_target_outcome_ready_mem >>
  conj_tac >- (qexists `env` >> first_assum ACCEPT_TAC) >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ bty fld = SOME fty` >>
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
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >>
                      REWRITE_TAC [th]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def, bind_def] >> rpt strip_tac >>
     Cases_on `res` >> simp[target_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >> simp[target_res_ok_def]) >>
  qpat_x_assum `target_sim_mem _ _ _ _ _ bt _`
    (mp_tac o SIMP_RULE std_ss [target_sim_mem_def]) >>
  disch_then (qspecl_then [`Type bty`, `sa`, `sm`, `rb`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "summary" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_result >> fs[ignore_bind_def]
QED

Resume pop_nested_target_attr_mem[summary]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >> gvs[]
  >~ [`exit_result r`]
  >- (Cases_on `res` >> gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  rename1 `target_post _ _ _ _ _ _ _ _ _ pv _ _ t` >>
  qabbrev_tac `es1 = es_end with gas_obs := []` >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL pv, es1)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >>
     simp[Abbr `es1`]) >>
  `expr_sim_inv cenv cx env es1` by
    (irule eval_base_place_sim_inv >>
     qexistsl_tac [`bt`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
                   `INL pv`] >> fs[target_pre_def]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?sid. bty = StructT sid` by
    (Cases_on `bty` >> gvs[attribute_type_def]) >> gvs[] >>
  Cases_on `extend_place cx pv (AttrSubscript fld) es1` >>
  rename1 `extend_place _ _ _ _ = (res1, es2)` >>
  `!m. res1 <> INR (Error (TypeError m))` by
    (qpat_x_assum `gas_admissible (bind _ _) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[bind_def] >> rpt strip_tac >> gvs[target_res_ok_def]) >>
  `?w0. eval_operand (FST rb) t = SOME w0 /\
        place_ptr_rel cenv cx t pv w0 (FST (SND rb)) (Type (StructT sid)) /\
        SND (SND rb) = SOME (ValPT (StructT sid)) /\
        place_readable cx es1 pv` by
    (fs[target_post_def, value_type_place_def] >> metis_tac[]) >>
  drule_all attr_place_step >> strip_tac >> gvs[] >>
  suspend "append"
QED

Resume pop_nested_target_attr_mem[append]:
  drule_at (Pat `emit_op _ _ _ = _`) pop_nested_target_attr_add_mem >>
  disch_then (drule_at (Pat `place_ptr_rel _ _ _ _ (_ + _) _ _`)) >>
  disch_then (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> strip_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL pv'`, `es_end`, `OK q`] >> simp[Abbr `es1`] >>
  irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
         |> REWRITE_RULE [APPEND_NIL]) >>
  qexistsl_tac [`es_end`, `t`, `pv`] >>
  simp[gas_marked_exec_def, gas_explicit_nil] >> gen_tac >>
  `(es_end with gas_obs := []) with gas_obs := tail =
     es_end with gas_obs := tail` by
    simp[evaluation_state_component_equality] >> simp[] >>
  qspecl_then [`cx`, `pv`, `fld`, `es_end`, `tail`] mp_tac
    extend_place_attr_gas_obs >>
  qspecl_then [`cx`, `pv`, `fld`, `es_end`, `[]`] mp_tac
    extend_place_attr_gas_obs >> simp[]
QED

Finalise pop_nested_target_attr_mem
