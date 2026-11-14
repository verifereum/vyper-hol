(* Fresh pure evaluation cannot manufacture a history-only local path. *)
Theory bodyIntCallPostProvenanceLiveSource
Ancestors
  bodyIntCallJointPureSource bodySimAugPlaceMemory bodySimAugPlaceScopes
  exprSimProps supportedExprTraverse vyperAST vyperInterpreter vyperState
  vyperStatePreservation vyperPlaceFrames vyperContext vyperMisc list pair sum

Theorem effect_free_memory_result_live:
  !e cx es n path ee.
    ~expr_has_effect e /\
    eval_expr cx e es = (INL (PlaceR (MemoryPlace n path)),ee) ==>
    ?entry v. lookup_scopes n ee.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v
Proof
  measureInduct_on `expr_size e` >> Cases_on `e` >>
  simp[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def] >>
  rpt gen_tac
  >~ [`Name ty nm`]
  >- (simp[Once evaluate_def, bind_def, ignore_bind_def, get_scopes_def,
           type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[evaluate_subscripts_def] >>
      Cases_on `lookup_scopes n ee.scopes` >> gvs[])
  >~ [`Literal ty lit`]
  >- simp[Once evaluate_def, return_def]
  >~ [`TopLevelName ty nsid`]
  >- (PairCases_on `nsid` >> simp[Once evaluate_def] >> rpt strip_tac >>
      drule aug_place_lookup_global_not_memory >> simp[])
  >~ [`FlagMember ty nsid mid`]
  >- (PairCases_on `nsid` >>
      simp[Once evaluate_def, lookup_flag_mem_def, option_CASE_rator,
           return_def, raise_def, AllCaseEqs()])
  >~ [`StructLit ty sid fields`]
  >- (PairCases_on `sid` >>
      simp[Once evaluate_def, bind_def, return_def, AllCaseEqs()])
  >~ [`IfExp ty c a b`]
  >- suspend "ifexp"
  >~ [`Attribute ty ae fld`]
  >- suspend "attribute"
  >~ [`Subscript ty ae idx`]
  >- suspend "subscript"
  >~ [`Builtin ty bt args`]
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
  >~ [`TypeBuiltin ty tb typ args`]
  >- simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
QED

Resume effect_free_memory_result_live[attribute]:
  strip_tac >>
  qpat_x_assum `!y. _` (qspec_then `ae` mp_tac) >>
  simp[expr_size_def, expr_has_effect_def] >> strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  drule select_result_memory_place >>
  disch_then (qspecl_then [`n`, `path`] mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  gvs[select_result_def] >>
  drule_all aug_place_extend_memory_live >> metis_tac[]
QED
Resume effect_free_memory_result_live[subscript]:
  strip_tac >>
  qpat_x_assum `!y. _` (qspec_then `ae` mp_tac) >>
  simp[expr_size_def, expr_has_effect_def] >> strip_tac >>
  Cases_on `subscript_reads_base cx ae idx` >>
  gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()] >>
  drule select_result_memory_place >>
  disch_then (qspecl_then [`n`, `path`] mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  gvs[GSYM expr_has_effect_def] >>
  rename1 `eval_expr cx idx mid = (INL ir,after)` >>
  drule_all effect_free_eval_expr_frame >>
  simp[evaluation_state_component_equality] >> strip_tac >>
  imp_res_tac read_result_state >> gvs[select_result_def] >>
  `lookup_scopes n after.scopes = SOME entry` by simp[] >>
  drule_all aug_place_extend_memory_live >> metis_tac[]
QED
Resume effect_free_memory_result_live[ifexp]:
  strip_tac >>
  first_assum (qspec_then `a` mp_tac) >>
  simp[expr_size_def, expr_has_effect_def] >> strip_tac >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def, expr_has_effect_def] >> strip_tac >>
  gvs[Once evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs(),
      return_def, raise_def] >>
  imp_res_tac conditional_result_state >> gvs[] >>
  gvs[COND_RATOR, AllCaseEqs(), raise_def] >>
  Cases_on `res` >>
  gvs[conditional_result_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `p` >>
  gvs[conditional_result_def, bind_def, return_def, raise_def,
      COND_RATOR, AllCaseEqs()] >> metis_tac[]
QED
Finalise effect_free_memory_result_live

Theorem effect_free_memory_result_selection:
  ~expr_has_effect e /\
  eval_expr cx e es = (INL (PlaceR (MemoryPlace n path)),ee) /\
  read_result cx (PlaceR (MemoryPlace n path)) ee = (INL v,ee) ==>
  ?entry. lookup_scopes n ee.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL v
Proof
  strip_tac >> drule_all effect_free_memory_result_live >> strip_tac >>
  gvs[read_result_def, read_place_def, read_memory_path_def,
      get_scopes_def, bind_def, lift_option_type_def, lift_sum_def,
      return_def, raise_def] >> metis_tac[]
QED
