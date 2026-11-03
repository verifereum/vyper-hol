Theory bodySimAugPlaceLoad
Ancestors
  bodySimAugPlaceLive bodySimAugPlaceScopes supportedTargets
  targetPlaceSim valueEncoding valueEncodingProps
  vyperState vyperValue vyperMisc list pair finite_map words
  vyperTypeInvariants exprSimHyps vyperTyping vyperPlaceFrames
  vyperInterpreter vyperScopePreservation

Theorem aug_place_projection_needs_shape:
  mem_path_offset (StructTV [("a",BaseTV BoolT);("b",BaseTV BoolT)])
    [AttrSubscript "a"] = SOME (0,BaseTV BoolT) /\
  evaluate_subscripts (StructTV [("a",BaseTV BoolT);("b",BaseTV BoolT)])
    (StructV [("b",BoolV T);("a",BoolV F)]) [AttrSubscript "a"] = INL (BoolV F) /\
  val_in_memory (StructTV [("a",BaseTV BoolT);("b",BaseTV BoolT)])
    (StructV [("b",BoolV T);("a",BoolV F)]) 0 (REPLICATE 31 0w ++ [1w]) /\
  ~val_in_memory (BaseTV BoolT) (BoolV F) 0 (REPLICATE 31 0w ++ [1w])
Proof
  EVAL_TAC >> simp[]
QED

Theorem aug_place_lookup_typed:
  !scopes id entry.
    EVERY scope_well_typed scopes /\ lookup_scopes id scopes = SOME entry ==>
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  Induct >> simp[lookup_scopes_def] >> rpt gen_tac >>
  Cases_on `FLOOKUP h id` >> simp[] >>
  metis_tac[scope_well_typed_def]
QED

Theorem aug_place_projection_shape_excluded:
  ~value_has_type (StructTV [("a",BaseTV BoolT);("b",BaseTV BoolT)])
    (StructV [("b",BoolV T);("a",BoolV F)])
Proof
  EVAL_TAC
QED

Theorem aug_place_scopes_target_induct[local]:
  !P. (!id. P (NameTarget id)) /\ (!nsid. P (TopLevelNameTarget nsid)) /\
      (!bt e. P bt ==> P (SubscriptTarget bt e)) /\
      (!bt s. P bt ==> P (AttributeTarget bt s)) ==> !bt. P bt
Proof
  rpt strip_tac >>
  `(!e:expr. T) /\ !bt. P bt` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >> simp[]
QED

Theorem aug_place_base_scopes:
  !t tops bindings info cx s r s'.
    supported_target_info tops bindings t = SOME info /\
    eval_base_place cx t s = (r,s') ==> s'.scopes = s.scopes
Proof
  recInduct aug_place_scopes_target_induct >> rpt conj_tac >> rpt gen_tac
  >- (simp[Once evaluate_def, get_scopes_def, bind_def, ignore_bind_def,
           type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (PairCases_on `nsid` >> simp[Once evaluate_def] >>
      metis_tac[lookup_global_scopes])
  >- suspend "subscript"
  >> suspend "attribute"
QED
Resume aug_place_base_scopes[subscript]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  strip_tac >> gvs[supported_target_info_def, AllCaseEqs()] >>
  imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
  imp_res_tac aug_place_supported_expr_scopes >> gvs[] >> metis_tac[]
QED
Resume aug_place_base_scopes[attribute]:
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  strip_tac >> gvs[supported_target_info_def, AllCaseEqs()] >>
  imp_res_tac extend_place_state >> gvs[] >> metis_tac[]
QED
Finalise aug_place_base_scopes

Theorem aug_place_target_scopes:
  supported_target_info tops bindings t = SOME info /\
  eval_target_place cx t s = (r,s') ==> s'.scopes = s.scopes
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  imp_res_tac get_place_state >> gvs[] >> metis_tac[aug_place_base_scopes]
QED

Theorem aug_place_target_entry_typed:
  expr_sim_inv cenv cx env s /\
  supported_target_info tops bindings t = SOME info /\
  eval_target_place cx t s = (INL p,s') /\
  lookup_scopes id s'.scopes = SOME entry ==>
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  rpt strip_tac >>
  `s'.scopes = s.scopes` by metis_tac[aug_place_target_scopes] >>
  gvs[expr_sim_inv_def, state_well_typed_def] >>
  metis_tac[aug_place_lookup_typed]
QED

Theorem aug_place_rhs_entry_typed:
  expr_sim_inv cenv cx env s /\
  supported_target_info tops bindings t = SOME info /\
  eval_target_place cx t s = (INL p,st) /\
  supported_expr tops e /\ eval_expr cx e st = (r,s') /\
  lookup_scopes id s'.scopes = SOME entry ==>
  value_has_type entry.type entry.value /\ well_formed_type_value entry.type
Proof
  rpt strip_tac >>
  `s'.scopes = st.scopes` by metis_tac[aug_place_supported_expr_scopes] >>
  gvs[] >> metis_tac[aug_place_target_entry_typed]
QED
