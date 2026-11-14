(* Resolved storage aggregate Append: target, value and staging composition. *)
Theory stmtSimAppendNestedAggregate
Ancestors
  stmtSimAppendAggregateContinuation stmtSimAppendNestedCode
  tuplePlaceHeadGas tuplePlaceTargetGas bodyAppendResolvedPre
  targetPlaceSimCases targetPlaceSim exprSimDefs exprSimHypsDefs
  stmtSimDefs stmtSimProps loweringPosts gasOutcome gasSummary gasSummaryCompose
  gasExemptCert fragGasMode fragGasPath exprLoweringProps stmtLoweringMono
  varsExt freshWrites stateFrame vyperInterpreter vyperState
  context compileEnv fragExec rich_list venomState exprOperandVar

Theorem compile_append_nested_aggregate_stmt_frag:
  target_sim ctx func cenv cx env bt es /\ target_pre cenv cx env bt es /\
  type_place_target env bt = SOME (Type (ArrayT elem (Dynamic cap))) /\
  call_evaluation_safe cx (int_calls_target bt) /\ expr_body_pre cenv cx env e es /\
  ~is_word_type elem /\ ~is_bytestring_type elem /\
  lowered_value_type cenv e = elem /\ post_value_type cenv e = elem /\
  evaluate_type (get_tenv cx) elem = SOME tv /\ 0 < type_slot_size tv /\
  type_memory_bytes cenv elem = 32 * type_slot_size tv /\
  type_memory_bytes cenv elem < dimword (:256) /\ cap < dimword (:256) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type (get_tenv cx) fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  (!gs p et. eval_target_place cx bt (es with gas_obs := gs) = (INL p,et) ==>
    expr_sim ctx func cenv cx elem e et /\
    ?tr slot. p = StoragePlace tr slot (ArrayTV tv (Dynamic cap)) /\
      w2n slot + type_slot_size (ArrayTV tv (Dynamic cap)) <= dimword (:256) /\
      (!raw. storage_read_live cx tr raw slot (ArrayTV tv (Dynamic cap))) /\
      (!es0 s0 u cut (b:bytes32) len v0 writes ks res es1.
        stmt_state_rel ctx func cenv cx es0 s0 /\ local_ptrs_reserved cenv cut /\
        value_has_type tv v0 /\ val_in_memory tv v0 (w2n b) s0.vs_memory /\
        encode_value tv v0 = SOME writes /\
        (!i. MEM i ks <=> MEM i (MAP FST writes)) /\
        w2n b + 32 * type_slot_size tv <= dimword (:256) /\
        len = w2n (lookup_storage slot (get_storage cx es0 tr)) /\ len < cap /\
        store_copy_normalize s0 u =
          (if tr then tstore else sstore) slot (n2w (len+1))
            (FOLDL (\t i. (if tr then tstore else sstore)
              (slot+n2w (1+len*type_slot_size tv)+n2w i)
              (mem_word_at (w2n b+32*i) s0.vs_memory) t) s0 ks) /\
        (!x. not_fresh_at cut x ==> lookup_var x u = lookup_var x s0) /\
        append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v0 es0 = (res,es1) ==>
        res = INL () /\ stmt_state_rel ctx func cenv cx es1 u) /\
      (!hs v ee. bind (eval_expr cx e) (read_result cx) (et with gas_obs := hs) = (INL v,ee) ==>
        value_has_type tv v /\ val_wf tv v /\ val_footprint tv v <= type_memory_bytes cenv elem)) ==>
  stmt_frag ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (Append bt e))
    (eval_stmt cx (Append bt e)) es
Proof
  strip_tac >> simp[stmt_frag_def, stmt_framed_frag_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all stmtSimAppendResolvedTheory.append_resolved_target_prefix >> strip_tac >>
  rpt (qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC) >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (irule tuple_place_target_gas_admissible >> simp[] >>
     qexistsl_tac [`cenv`, `env`, `ArrayT elem (Dynamic cap)`] >>
     fs[target_pre_def, vyperTypeSystemTheory.well_typed_target_def]) >>
  drule_all target_place_sim >> strip_tac >>
  `eval_stmt cx (Append bt e) =
    bind (eval_target_place cx bt)
      (\p. bind (bind (eval_expr cx e) (read_result cx)) (append_place cx p))` by
    (simp[FUN_EQ_THM] >> gen_tac >> simp[Once evaluate_def, bind_def] >>
     Cases_on `eval_target_place cx bt x` >> Cases_on `q` >> simp[] >>
     Cases_on `eval_expr cx e r'` >> Cases_on `q` >> simp[] >>
     Cases_on `read_result cx a r''` >> Cases_on `q` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  irule tuple_place_gas_outcome_bind_exec >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_INR_type, stmt_exit_def]) >>
  rpt strip_tac >> gvs[] >>
  `eval_target_place cx bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL v, mid with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  first_assum (drule_at (Pat `eval_target_place _ _ _ = _`)) >> strip_tac >> gvs[] >>
  `expr_body_pre cenv cx env e (mid with gas_obs := [])` by
    (irule append_resolved_rhs_body_pre >>
     goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  PairCases_on `r` >> simp[target_post_def, place_ptr_rel_def,
    slot_loc_def, exprLoweringTheory.value_type_place_def] >> strip_tac >> gvs[] >>
  drule_all append_nested_aggregate_code_parts >> strip_tac >>
  rename1 `lower_value _ _ _ _ sm = (raw,sB)` >>
  `cs_extends sm sB /\ cs_extends sB sc /\ cs_extends sc sd /\ cs_extends sd sb` by
    (conj_tac >- metis_tac[cj 2 compile_expr_grows] >>
     conj_tac >- metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
     conj_tac
     >- (`compile_copy_memory tmp.buf_operand raw
           (type_memory_bytes cenv (lowered_value_type cenv e)) sc = ((),sd)` by
           gvs[compile_store_memory_def] >>
         drule abiTuplePropsTheory.compile_copy_memory_extends >>
         strip_tac >> gvs[same_blocks_def] >> irule cs_extends_same_block >>
         simp[IS_PREFIX_APPEND]) >>
     metis_tac[externalEntryShapeTheory.compile_dynarray_append_labels, pairTheory.SND]) >>
  `fn_has_code sm sB func /\ fn_has_code sB sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (mid with gas_obs := [])` by
    (irule exprSimSourceTheory.expr_body_pre_gas_admissible >>
     qexistsl_tac [`cenv`, `env`] >> simp[]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[gas_marked_exec_def] >>
     strip_tac >> drule gas_marked_path_exec >> strip_tac >>
     drule gas_path_normal >> simp[]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sm`, `sB`, `raw`, `t`] mp_tac) >>
  impl_tac >- simp[] >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "rhs_summary" >>
  qexists_tac `marks'` >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks' (err,ee) (leaf,fin)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fin`] >>
  qmatch_goalsub_abbrev_tac `ignore_bind (bind rhs app) (return ())` >>
  `ignore_bind (bind rhs app) (return ()) =
    bind rhs (\v. ignore_bind (app v) (return ()))` by
    (simp[ignore_bind_def, FUN_EQ_THM, bind_def] >> gen_tac >>
     Cases_on `rhs x` >> Cases_on `q` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_value >>
  simp[Abbr `rhs`]
QED

Resume compile_append_nested_aggregate_stmt_frag[rhs_summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- suspend "rhs_value" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexists_tac `marks'` >> disj1_tac >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_append_nested_aggregate_stmt_frag[rhs_value]:
  gvs[] >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `?sw. eval_operand raw t' = SOME sw /\ val_in_memory tv v (w2n sw) t'.vs_memory` by
    (gvs[expr_val_rel_def] >> metis_tac[]) >>
  `~t'.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ marks' _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[gas_marked_exec_def] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  `value_has_type tv v /\ val_wf tv v /\ val_footprint tv v <= 32 * type_slot_size tv` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ marks' _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` strip_assume_tac o CONJUNCT1) >>
     qpat_x_assum `!hs v ee. bind (eval_expr cx e) (read_result cx) _ = _ ==> _` drule >> simp[]) >>
  `!x. raw = Var x ==> not_fresh_at sB x` by metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `ci_mono sm sB` by
    (qpat_assum `lower_value _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     qspecl_then [`cenv`, `lowered_value_type cenv e`, `e`, `sm`]
       mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
  `local_ptrs_reserved cenv sB` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  `t'.vs_labels = t.vs_labels` by
    (qpat_assum `gas_marked_exec _ _ _ _ marks' _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >>
     drule exprSimAbiEncodeArgsCountedLabelsTheory.abi_args_marked_path_labels >> simp[]) >>
  `eval_operand r0 t' = SOME slot` by
    (qpat_assum `eval_operand r0 t = SOME slot` mp_tac >>
     qpat_assum `!x. r0 = Var x ==> _` mp_tac >>
     qpat_assum `!x w. not_fresh_at sm x /\ _ ==> _` mp_tac >>
     qpat_assum `t'.vs_labels = t.vs_labels` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `r0` >> simp[eval_operand_def]) >>
  `!x. r0 = Var x ==> not_fresh_at sB x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >>
     fs[ci_mono_def]) >>
  drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)
    append_aggregate_staging_continuation >> simp[] >>
  disch_then (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_dynarray_append _ _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ t'`)) >>
  disch_then (qspecl_then [`slot`, `lctx`, `RetQ`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> asm_rewrite_tac []) >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (qexists_tac `marks' ++ marks''` >> disj1_tac >>
      suspend "suffix_normal")
  >- (qexists_tac `marks' ++ marks''` >> disj1_tac >>
      suspend "suffix_exit") >>
  qexists_tac `marks' ++ marks''` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  qmatch_goalsub_abbrev_tac `ignore_bind (bind rhs app) (return ())` >>
  `ignore_bind (bind rhs app) (return ()) =
    bind rhs (\v. ignore_bind (app v) (return ()))` by
    (simp[ignore_bind_def, FUN_EQ_THM, bind_def] >> gen_tac >>
     Cases_on `rhs x` >> Cases_on `q` >> simp[]) >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >> simp[Abbr `rhs`, Abbr `app`]
QED

Resume compile_append_nested_aggregate_stmt_frag[suffix_exit]:
  qexistsl_tac [`res`, `es_end'`, `r`] >> conj_tac
  >- (irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >> simp[]) >>
  disj2_tac >> conj_tac >- asm_rewrite_tac [] >>
  qpat_x_assum `(\res ff r. _) _ _ _` mp_tac >> simp[]
QED

Resume compile_append_nested_aggregate_stmt_frag[suffix_normal]:
  gvs[] >> qexistsl_tac [`res`, `es_end'`, `OK t''`] >> conj_tac
  >- (irule gas_marked_exec_bind_normal >> goal_assum (drule_at Any) >> simp[]) >>
  disj1_tac >> simp[] >>
  qpat_x_assum `stmt_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[stmt_post_def] >> strip_tac >>
  qexists_tac `cenv''` >> asm_rewrite_tac [] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x /\ not_fresh_at sB x` by
    (gen_tac >> disch_tac >> conj_tac >> irule not_fresh_at_mono >>
     qexists_tac `sa` >> fs[ci_mono_def]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> metis_tac[]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes /\
   MAP FDOM es_end.scopes = MAP FDOM mid.scopes` by
    fs[locals_kept_def] >>
  irule alloca_frame_expr_prefix >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac >- (goal_assum (drule_at Any)) >>
  qexistsl_tac [`mid`, `sm`, `t`] >>
  asm_rewrite_tac [] >> conj_tac >- fs[ci_mono_def] >>
  irule alloca_frame_expr_prefix >>
  conj_tac >- asm_rewrite_tac [] >>
  conj_tac >- (goal_assum (drule_at Any)) >>
  qexistsl_tac [`es_end with gas_obs := []`, `sB`, `t'`] >>
  gvs[ci_mono_def] >> asm_rewrite_tac []
QED

Finalise compile_append_nested_aggregate_stmt_frag
