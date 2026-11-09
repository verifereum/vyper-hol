(* Captured RHS views preserved by pure place evaluation. *)
Theory assignPlaceValueFrame
Ancestors
  supportedTargets targetPlaceLive stmtSimAugAssignPlaceStorage
  bodySimAugPlaceScopes targetPlaceSimCasesBase exprSimSubscriptArraySource
  supportedExprs vyperInterpreter vyperState vyperContext vyperMisc vyperAST
  pair sum list vyperStatePreservation vyperPlaceFrames vyperCallFrame
  vyperImmutablesPreservation vyperStorageBackend vyperScopePreservation
  loweringPosts targetPlaceSimMem exprSimProps valueEncodingProofs
  valueEncoding compileEnv venomState words arithmetic finite_map

Theorem assign_target_pure_indices[local]:
  !tops bt. supported_target_pure tops bt ==>
    EVERY (supported_pure_expr tops) (target_indices bt)
Proof
  gen_tac >> ho_match_mp_tac base_assignment_target_induct >>
  simp[supported_target_pure_def, target_indices_def]
QED

Theorem assign_pure_expr_immutables_mutual[local]:
  (!tops e. supported_pure_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==> s'.immutables = s.immutables) /\
  (!tops es. supported_pure_exprs tops es ==>
    (!cx s r s'. eval_exprs cx es s = (r,s') ==> s'.immutables = s.immutables) /\
    (!e. MEM e es ==> !cx s r s'.
      eval_expr cx e s = (r,s') ==> s'.immutables = s.immutables)) /\
  (!tops fields. supported_pure_fields tops fields ==>
    !cx s r s'. eval_exprs cx (MAP SND fields) s = (r,s') ==> s'.immutables = s.immutables) /\
  (!tops e. supported_place_expr tops e ==>
    !cx s r s'. eval_expr cx e s = (r,s') ==> s'.immutables = s.immutables)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> simp[supported_pure_expr_def]
  >- (rpt strip_tac >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()])
  >- simp[Once evaluate_def, return_def]
  >- (PairCases_on `id` >> rpt strip_tac >>
      gvs[Once evaluate_def] >> metis_tac[lookup_global_immutables])
  >- suspend "ifexp"
  >- suspend "structlit"
  >- suspend "subscript"
  >- suspend "attribute"
  >- suspend "builtin"
  >- suspend "typebuiltin"
  >- suspend "nil"
  >- suspend "cons"
  >- suspend "fields_nil"
  >- suspend "fields_cons"
  >- suspend "place_name"
  >- suspend "place_global"
  >- suspend "place_subscript"
  >> suspend "place_rest"
QED

Resume assign_pure_expr_immutables_mutual[ifexp]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac conditional_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >> metis_tac[]
QED
Resume assign_pure_expr_immutables_mutual[structlit]:
  PairCases_on `id` >> rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >> metis_tac[]
QED
Resume assign_pure_expr_immutables_mutual[subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume assign_pure_expr_immutables_mutual[attribute]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume assign_pure_expr_immutables_mutual[builtin]:
  rpt strip_tac >>
  `code_slice_source blt es = NONE` by
    (Cases_on `code_slice_source blt es` >> simp[] >>
     rename1 `SOME p` >> PairCases_on `p` >>
     gvs[code_slice_source_SOME, supportedExprFormsTheory.supported_builtin_form_def]) >>
  Cases_on `blt = Len` >> Cases_on `blt = Env MsgGas` >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac result_array_length_state >> imp_res_tac next_gas_reading_state >>
  imp_res_tac lift_sum_state >> imp_res_tac get_accounts_state >>
  imp_res_tac precompile_call_success_state >> gvs[] >>
  gvs[builtin_args_length_ok_def] >>
  Cases_on `es` >> gvs[] >> metis_tac[]
QED
Resume assign_pure_expr_immutables_mutual[typebuiltin]:
  rpt strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac lift_sum_state >> gvs[] >> metis_tac[]
QED
Resume assign_pure_expr_immutables_mutual[nil]:
  simp[Once evaluate_def, return_def]
QED
Resume assign_pure_expr_immutables_mutual[cons]:
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Resume assign_pure_expr_immutables_mutual[fields_nil]:
  simp[Once evaluate_def, return_def]
QED
Resume assign_pure_expr_immutables_mutual[fields_cons]:
  rpt strip_tac >> gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_result_state >> gvs[] >> metis_tac[]
QED
Resume assign_pure_expr_immutables_mutual[place_name]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
      type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]
QED
Resume assign_pure_expr_immutables_mutual[place_global]:
  PairCases_on `id` >> rpt strip_tac >>
  gvs[Once evaluate_def] >> metis_tac[lookup_global_immutables]
QED
Resume assign_pure_expr_immutables_mutual[place_subscript]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_result_state >> imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Resume assign_pure_expr_immutables_mutual[place_rest]:
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac select_result_state >> gvs[] >> metis_tac[]
QED
Finalise assign_pure_expr_immutables_mutual

Theorem assign_pure_expr_immutables[local]:
  supported_pure_expr tops e /\ eval_expr cx e s = (r,s') ==>
  s'.immutables = s.immutables
Proof
  metis_tac[assign_pure_expr_immutables_mutual]
QED

Theorem assign_pure_indices_base_views[local]:
  !bt tops cx es res ee.
    EVERY (supported_pure_expr tops) (target_indices bt) /\
    eval_base_place cx bt es = (res,ee) ==>
    ee.scopes = es.scopes /\ ee.immutables = es.immutables
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac
  >~ [`TopLevelNameTarget p`]
  >- (PairCases_on `p` >> simp[target_indices_def, Once evaluate_def] >>
      rpt strip_tac >>
      metis_tac[lookup_global_scopes, lookup_global_immutables]) >>
  simp[target_indices_def, Once evaluate_def] >> rpt gen_tac >> strip_tac
  >- (gvs[bind_def, get_scopes_def, type_check_def, assert_def,
          ignore_bind_def, return_def, raise_def, AllCaseEqs()]) >>
  gvs[bind_def, AllCaseEqs()] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  metis_tac[aug_place_pure_expr_scopes, assign_pure_expr_immutables,
            read_result_state, extend_place_state, raise_def]
QED

Theorem assign_pure_target_views:
  supported_target_pure tops bt /\ eval_target_place cx bt es = (res,ee) ==>
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  (!tr. get_storage cx ee tr = get_storage cx es tr)
Proof
  strip_tac >> drule assign_target_pure_indices >> strip_tac >>
  `ee.scopes = es.scopes /\ ee.immutables = es.immutables` by
    (qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
     metis_tac[assign_pure_indices_base_views, get_place_state, raise_def]) >>
  simp[] >> gen_tac >> drule_all aug_place_pure_target_storage >> simp[]
QED

Theorem assign_pure_target_read_frame:
  supported_target_pure tops bt /\ eval_target_place cx bt es = (res,ee) ==>
  FST (read_result cx r ee) = FST (read_result cx r es)
Proof
  strip_tac >> drule_all assign_pure_target_views >> strip_tac >>
  Cases_on `?tr slot tv. r = PlaceR (StoragePlace tr slot tv)`
  >- (gvs[read_result_def, read_place_def, read_storage_slot_eq] >>
      CASE_TAC >> simp[]) >>
  irule read_result_nonstorage_frame >> simp[] >> metis_tac[]
QED

Theorem assign_target_region_window[local]:
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sm.cs_next_id /\
      b <= off /\ off + len <= b + sz /\
      (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
          b + sz <= lb \/ lb + lsz <= b)) \/
   (?name b sz. local_region cenv es.scopes s name b sz /\
      b <= off /\ off + len <= b + sz) \/ len = 0) /\
  target_post ctx func cenv cx es sm sc s ee pv vt op t /\
  target_pure_frame cenv cx es s t ==>
  mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory
Proof
  strip_tac
  >- (`mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (gvs[target_post_def] >> first_x_assum irule >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[])
  >- (`mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (gvs[target_pure_frame_def] >> first_x_assum irule >>
         qexists_tac `name` >> simp[]) >>
      drule mem_bytes_at_agree_window >> simp[]) >>
  simp[mem_bytes_at_def]
QED

Theorem assign_located_value_bytes[local]:
  vv_at cenv cx ty sa sm es r (LocatedValue lty p) s /\
  p.ptr_location = LocMemory /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  target_post ctx func cenv cx es sm sc s ee pv vt op t /\
  target_pure_frame cenv cx es s t ==>
  mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >> irule assign_target_region_window >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  gvs[vv_at_def] >> metis_tac[]
QED
