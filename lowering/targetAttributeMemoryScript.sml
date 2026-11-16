(* Counted field extension of a target pointer. *)
Theory targetAttributeMemory
Ancestors
  targetMemoryContracts targetPlaceSimCasesBase targetPlaceSimDefs
  targetPlaceSim exprSimHypsDefs exprSimDefs exprSimProps loweringPosts
  exprLowering exprLoweringProps compileEnv loweringStateRelDefs
  bodyDeclMemoryCounted bodyFieldMemoryProps allocaHistory allocaFootprint
  emitHelper emitHelperProps freshWrites stmtLoweringMono
  exprSimBuffer exprSimAttributeFields
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath fragGasPathMem fragExec
  vyperInterpreter vyperState vyperAST vyperTypeSystem vyperTypeEnv
  vyperValue valueEncoding venomState venomInst vyperTypeInvariants
  exprSimPopNestedBase targetPlaceLive vyperStorageBackend targetSubscriptStorage
  gasStorage vyperStorageTrace vyperStorageFootprint
Libs
  pairLib

Theorem target_attr_add_path_mem[local]:
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    target_post H ctx func cenv cx es sa sm s0 es1 pv vt rb t) /\
  valid_horizon cx st0 H0 es1.storage_trace /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [FST rb; Lit (n2w off)] sm = (dst,sb) /\
  fn_has_code sm sb func /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand (FST rb) t = SOME w0 /\
  place_ptr_rel cenv cx t pv' (w0 + n2w off) (FST (SND rb)) vt' /\
  place_readable cx es1 pv' /\ alloca_history func t /\
  fn_inst_ids_distinct func ==>
  ?q. gas_marked_path T ctx func t 0 (OK q) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
      target_post H ctx func cenv cx es sa sb s0 es1 pv' vt'
        (dst,FST (SND rb),SOME (value_type_place vt')) q) /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ q.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >>
  `target_post H0 ctx func cenv cx es sa sm s0 es1 pv vt rb t` by simp[] >>
  `alloca_inv t` by gvs[target_post_def, stmt_state_rel_def] >>
  drule_all buffer_emit_add_run >> strip_tac >>
  drule_all attr_add_history >> strip_tac >>
  drule_all attr_add_gas_path >> strip_tac >> gvs[] >>
  qexists `update_var (STRING #"%" (toString sm.cs_next_var))
    (w0 + n2w off) t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[] >> rpt conj_tac
  >- simp[gas_marked_path_def]
  >- (rpt strip_tac >>
      qpat_x_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
        (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
      drule_all target_post_add >> strip_tac >> gvs[] >>
      fs[target_post_def, stmt_state_rel_def]) >>
  drule emit_op_extends >> simp[same_blocks_def, update_var_def]
QED

Theorem target_attribute_memory:
  target_pre cenv cx env (AttributeTarget bt fld) es /\
  (!st0 vt sa sb op s0.
    type_place_target env bt = SOME vt /\
    compile_get_target_ptr compile_expr cenv bt sa = (op,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    gas_admissible (eval_base_place cx bt) target_res_ok es /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome T (cx_tops cx) (ctx,func) cx st0 (eval_base_place cx bt) (es,s0)
      (\H res ee t. ?pv. res = INL pv /\
        target_post H ctx func cenv cx es sa sb s0 ee pv vt op t /\
        (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
          slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
          storage_read_live H tr (get_storage cx ee tr) slot tv) /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
      (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)) ==>
  !st0 vt sa sb op s0.
    type_place_target env (AttributeTarget bt fld) = SOME vt /\
    compile_get_target_ptr compile_expr cenv (AttributeTarget bt fld) sa = (op,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    gas_admissible (eval_base_place cx (AttributeTarget bt fld)) target_res_ok es /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome T (cx_tops cx) (ctx,func) cx st0
      (eval_base_place cx (AttributeTarget bt fld)) (es,s0)
      (\H res ee t. ?pv. res = INL pv /\
        target_post H ctx func cenv cx es sa sb s0 ee pv vt op t /\
        (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
          slots_in_range (get_storage cx ee tr) (w2n slot) tv /\
          storage_read_live H tr (get_storage cx ee tr) slot tv) /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next)
      (\H res ee r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  strip_tac >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ _ = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ bty fld = SOME fty` >>
  drule compile_get_target_ptr_attr >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_get_target_ptr, pairTheory.SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
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
  qpat_x_assum `!st0 sa sb op s0. _`
    (qspecl_then [`st0`, `sa`, `sm`, `rb`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >> simp[storage_trace_frame_extend_place])
  >- suspend "summary" >>
  qexists `marks` >> disj2_tac >> disj2_tac >>
  qexistsl [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_result >> fs[ignore_bind_def]
QED

Resume target_attribute_memory[summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
  disch_then (qx_choosel_then [`res`, `es_end`, `r`]
    (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
  >- (qexists `marks` >> disj1_tac >>
      irule gas_bad_storage_at_bind_left >> simp[storage_trace_frame_extend_place] >>
      irule gas_bad_storage_at_counted_prefix >> metis_tac[]) >>
  qabbrev_tac `H0 = storage_trace_horizon es_end.storage_trace` >>
  `valid_horizon cx st0 H0 es_end.storage_trace` by
    fs[storage_trace_domain_def, Abbr `H0`] >>
  qpat_x_assum `_ \/ _` strip_assume_tac >>
  qexists `marks` >> disj2_tac >> disj1_tac >> gvs[]
  >~ [`exit_result r`]
  >- (`expr_exit res r` by metis_tac[] >>
      Cases_on `res` >> gvs[expr_exit_def] >>
      simp[gas_summary_at_def] >>
      qexistsl [`INR y`, `es_end`, `r`] >> simp[] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?pv. _`
    (drule_then strip_assume_tac) >> gvs[] >>
  rename1 `target_post _ _ _ _ _ _ _ _ _ _ pv _ _ t` >>
  qabbrev_tac `es1 = es_end with gas_obs := []` >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
    target_post H ctx func cenv cx es sa sm s0 es1 pv (Type bty) rb t` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> fs[Abbr `es1`]) >>
  `~t.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `eval_base_place cx bt
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL pv, es1)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[Abbr `es1`]) >>
  `expr_sim_inv cenv cx env es1` by
    (irule eval_base_place_sim_inv >>
     qexistsl [`bt`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`, `INL pv`] >>
     fs[target_pre_def]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?sid. bty = StructT sid` by (Cases_on `bty` >> gvs[attribute_type_def]) >>
  gvs[] >>
  Cases_on `extend_place cx pv (AttrSubscript fld) es1` >>
  rename1 `extend_place _ _ _ _ = (res1, es2)` >>
  `!m. res1 <> INR (Error (TypeError m))` by
    (qpat_x_assum `gas_admissible (bind _ _) _ _`
       (mp_tac o REWRITE_RULE [gas_admissible_def]) >>
     disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
     simp[bind_def] >> rpt strip_tac >> gvs[target_res_ok_def]) >>
  `?w0. eval_operand (FST rb) t = SOME w0 /\
    place_ptr_rel cenv cx t pv w0 (FST (SND rb)) (Type (StructT sid)) /\
    SND (SND rb) = SOME (ValPT (StructT sid)) /\ place_readable cx es1 pv` by
    (`target_post H0 ctx func cenv cx es sa sm s0 es1 pv
       (Type (StructT sid)) rb t` by fs[Abbr `es1`] >>
     fs[target_post_def, value_type_place_def] >> metis_tac[]) >>
  drule_all attr_place_step >> strip_tac >> gvs[] >>
  suspend "normal"
QED

Resume target_attribute_memory[normal]:
  `!H tr slot tv. valid_horizon cx st0 H es1.storage_trace /\
    pv' = PlaceR (StoragePlace tr slot tv) ==>
    slots_in_range (get_storage cx es1 tr) (w2n slot) tv /\
    storage_read_live H tr (get_storage cx es1 tr) slot tv` by
    (rpt gen_tac >> strip_tac >>
     `eval_base_place cx (AttributeTarget bt fld)
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
        (INL (PlaceR (StoragePlace tr slot tv)),es1)` by
       simp[Once evaluate_def, bind_def] >>
     irule target_storage_result_ready_mem >>
     rpt conj_tac
     >- (qexistsl [`AttributeTarget bt fld`,
           `es with gas_obs := gas_explicit marks s0.vs_gas_readings`] >> simp[])
     >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> target_post H _ _ _ _ _ _ _ _ _ _ _ _ _`
           (qspec_then `H` mp_tac) >> simp[] >>
         simp[target_post_def, stmt_state_rel_def]) >>
     qexists `st0` >> simp[]) >>
  `?q. gas_marked_path T ctx func t 0 (OK q) /\
    (!H. valid_horizon cx st0 H es1.storage_trace ==>
      target_post H ctx func cenv cx es sa sb s0 es1 pv' (Type fty)
        (dst,FST (SND rb),SOME (value_type_place (Type fty))) q) /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ q.vs_alloca_next = t.vs_alloca_next` by
    (irule target_attr_add_path_mem >> simp[] >>
     conj_tac >- (qexists `H0` >> fs[Abbr `es1`]) >>
     qexistsl [`target_field_offset cenv (FST (SND rb))
        (SOME (ValPT (StructT sid))) fld`, `pv`, `sm`, `Type (StructT sid)`] >>
     simp[]) >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl [`INL pv'`, `es_end`, `OK q`] >> simp[Abbr `es1`] >>
  conj_tac
  >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
         |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
      qexistsl [`es_end`, `t`, `pv`] >>
      simp[gas_marked_exec_def, gas_explicit_nil] >> gen_tac >>
      `(es_end with gas_obs := []) with gas_obs := tail = es_end with gas_obs := tail`
        by simp[evaluation_state_component_equality] >> simp[] >>
      qspecl_then [`cx`, `pv`, `fld`, `es_end`, `tail`] mp_tac extend_place_attr_gas_obs >>
      qspecl_then [`cx`, `pv`, `fld`, `es_end`, `[]`] mp_tac extend_place_attr_gas_obs >> simp[]) >>
  rpt strip_tac >>
  fs[] >> metis_tac[]
QED

Finalise target_attribute_memory
