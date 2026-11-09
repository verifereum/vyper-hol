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
  exprSimIfExp bodyMemAssignAttrStorage

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

Theorem assign_immutable_holds_frame[local]:
  immutable_holds cenv cx ty r w es s /\
  target_pure_frame cenv cx es s t ==>
  immutable_holds cenv cx ty r w es t
Proof
  strip_tac >> gvs[immutable_holds_def]
  >- metis_tac[] >>
  qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`] >> simp[] >>
  disj2_tac >> simp[] >>
  irule valueEncodingPropsTheory.val_in_memory_mem_agree >>
  conj_tac >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  qexistsl_tac [`type_memory_size tvt`, `s.vs_memory`] >> simp[] >>
  `mem_bytes_at off (type_memory_size itv) t.vs_memory =
   mem_bytes_at off (type_memory_size itv) s.vs_memory` by
    (gvs[target_pure_frame_def] >> first_x_assum irule >> metis_tac[]) >>
  drule mem_bytes_at_agree_window >> simp[]
QED

Theorem assign_stack_value_frame[local]:
  expr_val_rel cx ty v rhs s /\
  expr_val_at cenv cx ty sa sm es v rhs s /\
  (!w. eval_operand rhs s = SOME w ==> eval_operand rhs t = SOME w) /\
  target_post ctx func cenv cx es sm sc s ee pv vt op t /\
  target_pure_frame cenv cx es s t ==>
  expr_val_rel cx ty v rhs t
Proof
  strip_tac >> gvs[expr_val_rel_def] >>
  rpt strip_tac >>
  Cases_on `is_word_type ty` >> gvs[] >>
  `val_wf tv v` by (gvs[expr_val_at_def] >> metis_tac[]) >>
  irule val_in_memory_footprint_agree >> simp[] >>
  qexists_tac `s.vs_memory` >> simp[] >>
  irule EQ_SYM >> irule assign_target_region_window >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  gvs[expr_val_at_def] >> metis_tac[]
QED

Theorem assign_word_footprint[local]:
  is_word_type ty /\ evaluate_type tenv ty = SOME tv ==>
  val_footprint tv v = 32
Proof
  Cases_on `ty` >> simp[is_word_type_def, vyperValueTheory.evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `v` >> simp[val_footprint_def, type_memory_size_def] >>
  gvs[is_word_type_def, AllCaseEqs(), type_memory_size_def]
QED


Theorem assign_located_memory_frame[local]:
  vv_holds cenv cx ty r (LocatedValue lty p) es s /\
  vv_at cenv cx ty sa sm es r (LocatedValue lty p) s /\
  p.ptr_location = LocMemory /\
  (!w. eval_operand p.ptr_operand s = SOME w ==>
       eval_operand p.ptr_operand t = SOME w) /\
  target_post ctx func cenv cx es sm sc s ee pv vt op t /\
  target_pure_frame cenv cx es s t ==>
  vv_holds cenv cx ty r (LocatedValue lty p) es t
Proof
  strip_tac >> fs[vv_holds_def] >>
  (qexists_tac `w` >> simp[] >> gen_tac >> disch_tac >>
  `val_wf tvt v` by (gvs[vv_at_def] >> metis_tac[]) >>
  `mem_bytes_at (w2n w) (val_footprint tvt v) t.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tvt v) s.vs_memory` by
    (irule assign_located_value_bytes >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (irule val_in_memory_footprint_agree >> simp[] >> metis_tac[]) >>
  strip_tac >>
  `val_footprint tvt v = 32` by metis_tac[assign_word_footprint] >>
  gvs[] >>
  `mem_word_at (w2n w) t.vs_memory = mem_word_at (w2n w) s.vs_memory` by
    (pure_rewrite_tac[abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
     asm_rewrite_tac[]) >>
  metis_tac[])
QED

Theorem assign_vv_holds_target_frame:
  vv_holds cenv cx ty r vv es s /\ vv_at cenv cx ty sa sm es r vv s /\
  (!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) t = SOME w) /\
  target_post ctx func cenv cx es sm sc s ee pv vt op t /\
  target_pure_frame cenv cx es s t ==>
  vv_holds cenv cx ty r vv es t
Proof
  Cases_on `vv`
  >- (simp[contextTheory.vv_operand_def, vv_holds_def, vv_at_def] >>
      rpt strip_tac >> qexists_tac `v` >> simp[] >>
      irule assign_stack_value_frame >> goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  strip_tac >> fs[contextTheory.vv_operand_def] >> Cases_on `p.ptr_location`
  >- (irule assign_located_memory_frame >> goal_assum (drule_at Any) >>
      simp[contextTheory.vv_operand_def] >> metis_tac[]) >>
  gvs[vv_holds_def, contextTheory.vv_operand_def]
  >- gvs[storage_holds_def, target_pure_frame_def]
  >- gvs[storage_holds_def, target_pure_frame_def] >>
  irule assign_immutable_holds_frame >> metis_tac[]
QED

Theorem assign_vv_holds_source_frame[local]:
  supported_target_pure tops bt /\ eval_target_place cx bt es = (res,ee) /\
  vv_holds cenv cx ty r vv es s ==>
  vv_holds cenv cx ty r vv ee s
Proof
  strip_tac >>
  `ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
   (!tr. get_storage cx ee tr = get_storage cx es tr)` by
    metis_tac[assign_pure_target_views] >>
  `!v. read_result cx r es = (INL v,es) ==>
       read_result cx r ee = (INL v,ee)` by
    (rpt strip_tac >>
     `FST (read_result cx r ee) = INL v` by
       metis_tac[assign_pure_target_read_frame, FST] >>
     Cases_on `read_result cx r ee` >> gvs[] >>
     drule read_result_state >> simp[]) >>
  `!tr w tv v. read_storage_slot cx tr w tv es = (INL v,es) ==>
              read_storage_slot cx tr w tv ee = (INL v,ee)` by
    (simp[read_storage_slot_eq] >> rpt gen_tac >> CASE_TAC >> simp[]) >>
  Cases_on `vv`
  >- (fs[vv_holds_def] >> metis_tac[]) >>
  Cases_on `p.ptr_location` >> fs[vv_holds_def]
  >- (qexists_tac `v` >> simp[])
  >- (qexists_tac `v` >> simp[])
  >- (fs[storage_holds_def] >> qexists_tac `v` >> simp[])
  >- (fs[storage_holds_def] >> qexists_tac `v` >> simp[]) >>
  fs[immutable_holds_def] >>
  qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`, `v`] >> simp[]
QED

Theorem assign_pure_target_vv_holds:
  supported_target_pure tops bt /\ eval_target_place cx bt es = (res,ee) /\
  vv_holds cenv cx ty r vv es s /\ vv_at cenv cx ty sa sm es r vv s /\
  (!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) t = SOME w) /\
  target_post ctx func cenv cx es sm sc s ee pv vt op t /\
  target_pure_frame cenv cx es s t ==>
  vv_holds cenv cx ty r vv ee t
Proof
  strip_tac >> irule assign_vv_holds_source_frame >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  irule assign_vv_holds_target_frame >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem assign_pure_target_vv_at:
  supported_target_pure tops bt /\ eval_target_place cx bt es = (res,ee) /\
  vv_at cenv cx ty sa sm es r vv s /\
  (!w. eval_operand (vv_operand vv) s = SOME w ==>
       eval_operand (vv_operand vv) t = SOME w) /\
  local_ptrs_reserved cenv sm /\ local_ptrs_rel func cenv es.scopes s /\
  sm.cs_next_id <= sc.cs_next_id /\
  target_post ctx func cenv cx es sm sc s ee pv vt op t ==>
  vv_at cenv cx ty sa sc ee r vv t
Proof
  strip_tac >>
  `ee.scopes = es.scopes` by metis_tac[assign_pure_target_views] >>
  `!n b sz. local_region cenv ee.scopes t n b sz <=>
             local_region cenv es.scopes s n b sz` by
    (rpt gen_tac >> eq_tac >> strip_tac
     >- (irule local_region_frame >> conj_tac >- metis_tac[] >>
         gvs[target_post_def] >> metis_tac[]) >>
     irule local_region_frame_fwd >>
     gvs[target_post_def] >> metis_tac[]) >>
  `!v. read_result cx r ee = (INL v,ee) ==>
       read_result cx r es = (INL v,es)` by
    (rpt strip_tac >>
     `FST (read_result cx r es) = INL v` by
       metis_tac[assign_pure_target_read_frame, FST] >>
     Cases_on `read_result cx r es` >> gvs[] >>
     drule read_result_state >> simp[]) >>
  `!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
            FLOOKUP t.vs_allocas aid = SOME b` by gvs[target_post_def] >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  Cases_on `vv`
  >- (gvs[vv_at_def, expr_val_at_def, contextTheory.vv_operand_def] >>
      rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      `read_result cx r es = (INL v,es)` by metis_tac[] >>
      qpat_x_assum `!v. read_result cx r es = _ ==> _` drule_all >>
      strip_tac >> simp[] >> qexists_tac `w` >> simp[]
      >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
          first_assum ACCEPT_TAC) >>
      disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]) >>
  gvs[vv_at_def, contextTheory.vv_operand_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `read_result cx r es = (INL v,es)` by metis_tac[] >>
  qpat_x_assum `p.ptr_location = LocMemory ==> _` (drule_all_then strip_assume_tac) >>
  simp[] >>
  qexists_tac `w` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC)
  >- (disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[]) >>
  simp[]
QED

Theorem assign_pure_target_vv_own:
  supported_target_pure tops bt /\ eval_target_place cx bt es = (res,ee) /\
  vv_own cenv cx ty sa sm es r vv s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  local_ptrs_reserved cenv sm /\ local_ptrs_rel func cenv es.scopes s /\
  sm.cs_next_id <= sc.cs_next_id /\
  target_post ctx func cenv cx es sm sc s ee pv vt op t ==>
  vv_own cenv cx ty sa sc ee r vv t
Proof
  strip_tac >>
  `ee.scopes = es.scopes` by metis_tac[assign_pure_target_views] >>
  `!v. read_result cx r ee = (INL v,ee) ==>
       read_result cx r es = (INL v,es)` by
    (rpt strip_tac >>
     `FST (read_result cx r es) = INL v` by
       metis_tac[assign_pure_target_read_frame, FST] >>
     Cases_on `read_result cx r es` >> gvs[] >>
     drule read_result_state >> simp[]) >>
  `vv_own cenv cx ty sa sm ee r vv s` by
    (Cases_on `vv` >> gvs[vv_own_def, expr_val_own_def] >> metis_tac[]) >>
  irule ifexp_vv_own_alloc_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- (gvs[target_post_def] >>
    rpt gen_tac >> eq_tac >> strip_tac
    >- (irule local_region_frame >> conj_tac >- metis_tac[] >>
        metis_tac[]) >>
    irule local_region_frame_fwd >> metis_tac[]) >>
  gvs[target_post_def]
QED

Theorem assign_pure_target_store_bound:
  supported_target_pure tops bt /\ eval_target_place cx bt es = (res,ee) /\
  vv_store_bound cx ty lt es r vv s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  vv_store_bound cx ty lt ee r vv t
Proof
  strip_tac >>
  `!v. read_result cx r ee = (INL v,ee) ==>
       read_result cx r es = (INL v,es)` by
    (rpt strip_tac >>
     `FST (read_result cx r es) = INL v` by
       metis_tac[assign_pure_target_read_frame, FST] >>
     Cases_on `read_result cx r es` >> gvs[] >>
     drule read_result_state >> simp[]) >>
  irule vv_store_bound_frame_mem_src >>
  goal_assum (drule_at Any) >> simp[] >>
  Cases_on `vv` >> gvs[exprSimMemDefsTheory.vv_store_bound_def] >> metis_tac[]
QED

Theorem assign_pure_target_vv_post:
  supported_target_pure tops bt /\ eval_target_place cx bt es = (res,ee) /\
  vv_post ctx func cenv cx e old sa sm s0 es r vv s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  local_ptrs_reserved cenv sm /\ local_ptrs_rel func cenv es.scopes s /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_id <= sc.cs_next_id /\
  target_post ctx func cenv cx es sm sc s ee pv vt op t /\
  target_pure_frame cenv cx es s t ==>
  vv_post ctx func cenv cx e es sa sc s ee r vv t
Proof
  strip_tac >>
  `vv_holds cenv cx (post_value_type cenv e) r vv ee t` by
    (irule assign_pure_target_vv_holds >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     gvs[vv_post_def] >> metis_tac[]) >>
  `vv_at cenv cx (post_value_type cenv e) sa sc ee r vv t` by
    (irule assign_pure_target_vv_at >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     gvs[vv_post_def] >> metis_tac[]) >>
  `(post_value_type cenv e <> expr_type e ==>
    vv_own cenv cx (post_value_type cenv e) sa sc ee r vv t)` by
    (strip_tac >> irule assign_pure_target_vv_own >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     gvs[vv_post_def] >> metis_tac[]) >>
  `~expr_has_effect e ==> vv_storage_live cx vv ee t` by
    (strip_tac >> drule_all assign_pure_target_views >> strip_tac >>
     Cases_on `vv` >> gvs[vv_post_def, contextTheory.vv_operand_def] >> metis_tac[]) >>
  gvs[vv_post_def, target_post_def] >> rpt conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      gvs[not_fresh_at_def]) >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists_tac `aid` >> simp[]
QED
