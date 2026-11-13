Theory bodyPtrAugAssignStorageArrayPrefix
Ancestors
  bodyPtrPopTargetSimArrayConstructor bodyPtrPopTargetSimArrayCompose
  bodyPtrPopTargetSimAttribute bodyPtrPopTargetSimSubscriptCuts
  fragGasPathPtr fragGasSeqPtr fragExec pair freshWrites
  bodyPtrPopTargetSimIndexSource bodyPtrPopTargetSimIndexFrame
  exprLoweringProps exprSimHypsDefs exprSimHyps vyperTyping vyperTypeSystem
  gasExemptCert gasSummaryComposePtr targetPlaceSimCasesBase
  exprLowering emitHelperProps stmtLoweringMono compileEnv loweringPosts
  bodyPtrPopTargetDefs targetPlaceSimDefs targetPlaceSim exprSimSource exprSimDefs
  vyperInterpreter vyperState bodyPtrPopTargetSimArraySuffix
  stmtSimAugAssignPlaceStorage list vyperTypeInvariants targetPlaceLive

Theorem augassign_storage_array_sim_ptr_using_suffix:
  (!cenv cx env bt e es et bd sa bop loc sm idx sn dst sb func ctx s0 ee tr slot tv
    t G tn d G0 tn0 em source_start gs v ef H un u PG.
   target_pre cenv cx env (SubscriptTarget bt e) es /\
   type_place_target env bt = SOME (Type (ArrayT et bd)) /\
   well_typed_expr env e /\ is_int_type (expr_type e) /\
   slots_in_range (get_storage cx ef tr) (w2n slot) tv /\
   storage_read_live cx tr (get_storage cx ef tr) slot tv /\
   compile_get_target_ptr compile_expr cenv bt sa = ((bop,loc,SOME (ValPT (ArrayT et bd))),sm) /\
   lower_value compile_expr cenv (expr_type e) e sm = (idx,sn) /\
   compile_array_subscript bop idx (case bd of Fixed _ => F | Dynamic _ => T)
     (case bd of Fixed n => n | Dynamic _ => 0)
     (word_scale (case loc of SOME l => l | NONE => LocMemory))
     (elem_size_in_location cenv (case loc of SOME l => l | NONE => LocMemory) et)
     (is_signed_type (expr_type e))
     (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca
       (case loc of SOME l => l | NONE => LocMemory)) sn = (dst,sb) /\
   fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
   local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
   ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn sb /\
   stmt_state_rel ctx func cenv cx es s0 /\
   target_post ctx func cenv cx es sa sm s0 ee (PlaceR (StoragePlace tr slot tv))
     (Type (ArrayT et bd)) (bop,loc,SOME (ValPT (ArrayT et bd))) t /\
   target_ptr_ok cenv (PlaceR (StoragePlace tr slot tv))
     (bop,loc,SOME (ValPT (ArrayT et bd))) G tn t /\
   ghost_inv d cenv cx ee G tn t /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
   ee = em with gas_obs := [] /\ source_start = es with gas_obs := gs /\
   eval_base_place cx bt source_start = (INL (PlaceR (StoragePlace tr slot tv)),em) /\
   bind (eval_expr cx e) (read_result cx) em = (INL v,ef) /\
   expr_body_pre cenv cx env e em /\ expr_sim_inv cenv cx env em /\
   expr_sim_inv cenv cx env ef /\ ef.gas_obs = [] /\
   expr_post ctx func cenv cx e ee sm sn t ef v idx u /\
   ghost_inv d cenv cx ef H un u /\
   ptr_val_ok cx (post_value_type cenv e) v idx H un u /\
   ghost_kept cenv ee sm G tn t H un /\
   u.vs_current_bb = sn.cs_current_bb /\
   u.vs_inst_idx = LENGTH sn.cs_current_insts /\ ~u.vs_halted ==>
   gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
     (extend_place cx (PlaceR (StoragePlace tr slot tv)) (ValueSubscript v)) (ef,u,H,un)
     (\res ef' H' un' q. ?pv'. res = INL pv' /\
       target_post ctx func cenv cx es sa sb s0 ef' pv' (Type et)
         (dst,loc,SOME (ValPT et)) q /\
       q.vs_current_bb = sb.cs_current_bb /\
       q.vs_inst_idx = LENGTH sb.cs_current_insts /\
       ghost_inv d cenv cx ef' H' un' q /\
       target_ptr_ok cenv pv' (dst,loc,SOME (ValPT et)) H' un' q /\
       ghost_kept cenv es sa G0 tn0 s0 H' un')
     (\res ef' gt r. expr_exit res r)) ==>
  !tops ctx cenv cx bt e env es et bd d PG func.
  body_inv tops ctx cenv cx /\
  body_base_target_ptr_ok cx (SubscriptTarget bt e) /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  (?nsid. target_root bt = TopLevelNameTarget nsid) /\
  EVERY (supported_pure_expr tops) (target_indices (SubscriptTarget bt e)) /\
  type_place_target env bt = SOME (Type (ArrayT et bd)) /\
  target_sim_ptr d ctx PG func cenv cx env bt es ==>
  target_sim_ptr d ctx PG func cenv cx env (SubscriptTarget bt e) es
Proof
  disch_then (assume_tac o PURE_REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  rpt gen_tac >> strip_tac >> simp[target_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  simp[Once well_typed_expr_def] >> strip_tac >> gvs[] >> suspend "base"
QED

Resume augassign_storage_array_sim_ptr_using_suffix[base]:
  Cases_on `compile_get_target_ptr compile_expr cenv bt sa` >>
  rename1 `compile_get_target_ptr _ _ bt sa = (rb,sm)` >>
  `fn_has_code sa sm func /\ cs_extends sm sb` by
    (mp_tac (cj 1 compile_expr_ci_mono) >> strip_tac >>
     drule_all target_subscript_base_code_ptr >> simp[]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    metis_tac[target_subscript_base_admissible_ptr] >>
  qpat_x_assum `target_sim_ptr _ _ _ _ _ _ _ bt _`
    (mp_tac o REWRITE_RULE [target_sim_ptr_def]) >>
  disch_then (qspecl_then [`Type (ArrayT et bd)`, `sa`, `sm`, `rb`,
                         `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> strip_tac
  >- suspend "base_summary" >> suspend "base_exempt"
QED

Resume augassign_storage_array_sim_ptr_using_suffix[base_summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >> gvs[]
  >~ [`exit_result r`]
  >- (qexists_tac `marks` >> disj1_tac >> simp[Once evaluate_def] >>
      Cases_on `res` >> gvs[expr_exit_def] >>
      irule gas_summary_ptr_at_bind_exception >> simp[] >> metis_tac[]) >>
  drule_all target_subscript_index_ready_ptr >>
  disch_then (qspecl_then [`expr_type e`, `d`] strip_assume_tac) >> suspend "index"
QED

Resume augassign_storage_array_sim_ptr_using_suffix[index]:
  `SND (SND rb) = SOME (ValPT (ArrayT et bd))` by
    fs[target_post_def, value_type_place_def] >>
  PairCases_on `rb` >> gvs[] >>
  drule_all target_array_compile_parts_ptr >> strip_tac >> gvs[] >> suspend "index_run"
QED

Resume augassign_storage_array_sim_ptr_using_suffix[index_run]:
  `ci_mono sa sm` by metis_tac[ci_mono_compile_get_target_ptr, SND] >>
  `ci_mono sm sn` by metis_tac[compile_expr_ci_mono, ci_mono_lower_value_cfn, SND] >>
  `ci_mono sn sb` by metis_tac[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load, SND] >>
  `fn_has_code sm sn func` by (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  `~t.vs_halted` by metis_tac[gas_marked_exec_ptr_def, gas_path_ptr_ok_not_halted] >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`sm`, `sn`, `idx`, `t`, `G`, `tn`] mp_tac) >>
  (impl_tac >- (fs[target_post_def, ci_mono_def] >> metis_tac[not_fresh_at_mono])) >>
  strip_tac >> suspend "index_outcome"
QED

Resume augassign_storage_array_sim_ptr_using_suffix[index_outcome]:
  rewrite_tac[GSYM gas_outcome_ptr_def] >> simp[Once evaluate_def] >>
  irule gas_outcome_ptr_bind_normal >>
  qexistsl_tac [`G`, `marks`, `es_end`, `t`, `tn`, `pv`] >> conj_tac
  >- (rpt strip_tac >> BETA_TAC >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`es_end`, `t`, `pv`] >> fs[]) >>
  reverse conj_tac >- simp[] >> suspend "index_suffix"
QED

Resume augassign_storage_array_sim_ptr_using_suffix[index_suffix]:
  BETA_TAC >> once_rewrite_tac[GSYM vyperStateTheory.bind_assoc] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- suspend "index_summary" >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks'` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >> drule gas_exempt_cert_error_value >>
  disch_then (qspec_then
    `\v. ignore_bind (extend_place cx pv (ValueSubscript v)) (return ())` mp_tac) >>
  simp[ignore_bind_def, vyperStateTheory.bind_assoc]
QED

Resume augassign_storage_array_sim_ptr_using_suffix[index_summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_ptr_at_marked]) >> gvs[]
  >~ [`exit_result r`]
  >- (simp[gas_outcome_ptr_def] >> qexists_tac `marks'` >> disj1_tac >>
      Cases_on `res` >> gvs[expr_exit_def] >>
      irule gas_summary_ptr_at_bind_exception >> simp[] >>
      qexistsl_tac [`G'`, `y`, `es_end'`, `r`, `tn'`] >> fs[oneline expr_exit_def]) >>
  irule gas_outcome_ptr_bind_normal >>
  qexistsl_tac [`G'`, `marks'`, `es_end'`, `t'`, `tn'`, `v`] >> conj_tac
  >- (rpt strip_tac >> BETA_TAC >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`es_end'`, `t'`, `v`] >> fs[]) >>
  reverse conj_tac >- simp[] >> BETA_TAC >> suspend "array_suffix"
QED

Resume augassign_storage_array_sim_ptr_using_suffix[array_suffix]:
  qabbrev_tac `em = es_end with gas_obs := gas_explicit marks' t.vs_gas_readings` >>
  qabbrev_tac `ef = es_end' with gas_obs := []` >>
  `eval_base_place cx bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ em.gas_obs) =
    (INL pv,em)` by
    (fs[gas_marked_exec_ptr_def] >>
     qpat_x_assum `!tail. eval_base_place _ _ _ = _`
       (qspec_then `em.gas_obs` mp_tac) >> simp[Abbr `em`]) >>
  `bind (eval_expr cx e) (read_result cx) em = (INL v,ef)` by
    (fs[gas_marked_exec_ptr_def] >>
     qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[Abbr `em`, Abbr `ef`]) >>
  `expr_sim_inv cenv cx env em` by simp[Abbr `em`] >>
  `expr_body_pre cenv cx env e em` by
    (fs[target_pre_def, target_indices_pre_def] >> first_x_assum irule >> metis_tac[]) >>
  `expr_sim_inv cenv cx env ef` by
    (qpat_x_assum `bind _ _ em = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     metis_tac[exprSimSourceTheory.expr_body_pre_eval_result]) >>
  `vt = Type et /\ is_int_type (expr_type e)` by
    fs[subscript_vtype_def, AllCaseEqs()] >> gvs[] >>
  `~t'.vs_halted` by
    (qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ (OK t')` mp_tac >>
     simp[gas_marked_exec_ptr_def] >> metis_tac[gas_path_ptr_ok_not_halted]) >>
  suspend "storage_ready"
QED

Resume augassign_storage_array_sim_ptr_using_suffix[storage_ready]:
  `?tr slot tv. pv = PlaceR (StoragePlace tr slot tv)` by
    (qpat_x_assum `!cenv' cx' env' bt' e' es' et' bd' sa' bop loc sm idx sn dst sb' func' ctx' s0' tr slot tv t G tn d' G0' tn0' em gs v ef H un u PG. _` kall_tac >>
     fs[target_post_def] >>
     Cases_on `pv` >> gvs[place_ptr_rel_def] >>
     Cases_on `p` >> gvs[place_ptr_rel_def] >>
     drule target_base_memory_root_ptr >> simp[]) >> gvs[] >>
  `EVERY (supported_pure_expr tops) (target_indices bt) /\ supported_pure_expr tops e` by
    fs[target_indices_def, EVERY_APPEND] >>
  `get_storage cx ef tr = get_storage cx em tr` by
    metis_tac[aug_place_pure_index_storage] >>
  `contract_storage_well_formed cx
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ em.gas_obs)` by
    (qpat_x_assum `!cenv' cx' env' bt' e' es' et' bd' sa' bop loc sm idx sn dst sb' func' ctx' s0' tr slot tv t G tn d' G0' tn0' em gs v ef H un u PG. _` kall_tac >>
     irule vyperStorageLayoutSafetyTheory.contract_storage_well_formed_storage_frame >>
     qexists_tac `es` >> reverse conj_tac
     >- fs[target_pre_def, expr_sim_inv_def] >>
     Cases >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  `slots_in_range (get_storage cx ef tr) (w2n slot) tv /\
   storage_read_live cx tr (get_storage cx ef tr) slot tv` by
    (drule_all aug_place_pure_base_storage_range >>
     drule_all aug_place_pure_base_storage_live >> simp[]) >>
  qpat_x_assum `!cenv' cx' env' bt' e' es' et' bd' sa' bop loc sm idx sn dst sb' func' ctx' s0' tr slot tv t G tn d' G0' tn0' em gs v ef H un u PG. _` irule >>
  simp[Abbr `em`, Abbr `ef`] >>
  qpat_assum `eval_base_place cx bt (_ with gas_obs := _) = _` (irule_at Any) >>
  qpat_assum `compile_get_target_ptr compile_expr cenv bt sa = _` (irule_at Any) >>
  qpat_assum `lower_value compile_expr cenv (expr_type e) e sm = _` (irule_at Any) >>
  simp[] >>
  qpat_assum `target_post _ _ _ _ _ _ sm _ _ _ _ _ t` (irule_at Any) >>
  qpat_assum `target_ptr_ok _ _ _ G tn t` (irule_at Any) >>
  qexists_tac `env` >> simp[] >> gvs[]
QED

Resume augassign_storage_array_sim_ptr_using_suffix[base_exempt]:
  qexists_tac `marks` >> disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[Once evaluate_def, ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_result >> fs[ignore_bind_def]
QED

Finalise augassign_storage_array_sim_ptr_using_suffix
