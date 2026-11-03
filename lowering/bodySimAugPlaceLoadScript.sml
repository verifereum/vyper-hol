Theory bodySimAugPlaceLoad
Ancestors
  bodySimAugPlaceLive bodySimAugPlaceScopes supportedTargets
  targetPlaceSim valueEncoding valueEncodingProps
  vyperState vyperValue vyperMisc list pair finite_map words
  vyperTypeInvariants exprSimHyps vyperTyping vyperPlaceFrames
  vyperInterpreter vyperScopePreservation vyperValueOperation
  vyperPlaceStatePreservation vyperAssignPreservesType
  exprSimBuffer exprLoweringProps compileEnv exprSim

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

Theorem aug_place_fields_project:
  !fts fs id off ptv base mem v.
    struct_has_type fts fs /\ fields_in_memory fs fts base mem /\
    mem_field_offset fts id = SOME (off,ptv) /\ ALOOKUP fs id = SOME v ==>
    value_has_type ptv v /\ val_in_memory ptv v (base + off) mem
Proof
  Induct >> gen_tac >> Cases_on `fs` >>
  simp[value_has_type_def, mem_field_offset_def] >>
  rename1 `struct_has_type (ft::fts) (fv::rest)` >>
  PairCases_on `ft` >> PairCases_on `fv` >>
  simp[value_has_type_def, val_in_memory_def] >> rpt gen_tac >>
  strip_tac >> gvs[] >> Cases_on `ft0 = id` >>
  gvs[mem_field_offset_def, AllCaseEqs()] >>
  PairCases_on `z` >> gvs[] >> first_x_assum drule_all >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem aug_place_elems_project:
  !vs i base tv mem.
    elems_in_memory vs base tv mem /\ i < LENGTH vs ==>
    val_in_memory tv (EL i vs) (base + i * type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def] >> rpt gen_tac >>
  Cases_on `i` >> simp[val_in_memory_def] >> strip_tac >>
  first_x_assum drule_all >>
  simp_tac bool_ss [arithmeticTheory.MULT_CLAUSES,
    AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem aug_place_sparse_project:
  !kvs i base tv mem v.
    kvs_in_memory kvs base tv mem /\ ALOOKUP kvs i = SOME v ==>
    val_in_memory tv v (base + i * type_memory_size tv) mem
Proof
  Induct >> simp[val_in_memory_def] >> PairCases >>
  simp[val_in_memory_def] >> rpt gen_tac >>
  Cases_on `h0 = i` >> simp[] >> metis_tac[]
QED

Theorem aug_place_tuple_project:
  !tvs vs i base mem.
    values_have_types tvs vs /\ tuple_in_memory vs tvs base mem /\
    i < LENGTH tvs ==>
    val_in_memory (EL i tvs) (EL i vs)
      (base + type_memory_size_list (TAKE i tvs)) mem
Proof
  Induct >> gen_tac >> Cases_on `vs` >>
  simp[value_has_type_def, val_in_memory_def] >> rpt gen_tac >>
  Cases_on `i` >> simp[value_has_type_def, val_in_memory_def, type_memory_size_def] >>
  strip_tac >> first_x_assum drule_all >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem aug_place_array_project:
  !tv bd av i off etv base mem v.
    value_has_type (ArrayTV tv bd) (ArrayV av) /\
    val_in_memory (ArrayTV tv bd) (ArrayV av) base mem /\
    mem_step_offset (ArrayTV tv bd) (ValueSubscript (IntV i)) = SOME (off,etv) /\
    array_index (ArrayTV tv bd) av i = SOME v ==>
    val_in_memory etv v (base + off) mem
Proof
  rpt gen_tac >> Cases_on `bd` >> Cases_on `av` >>
  simp[value_has_type_def, val_in_memory_def, mem_step_offset_def,
       array_index_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- (Cases_on `ALOOKUP l (Num i)` >> gvs[] >>
      metis_tac[aug_place_sparse_project])
  >> gvs[oEL_THM] >> drule_all aug_place_elems_project >>
  simp_tac bool_ss [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem aug_place_step_project:
  !tv a sb off etv v base mem.
    value_has_type tv a /\ well_formed_type_value tv /\
    val_in_memory tv a base mem /\ mem_step_offset tv sb = SOME (off,etv) /\
    evaluate_subscripts tv a [sb] = INL v ==>
    val_in_memory etv v (base + off) mem
Proof
  Cases >> rpt gen_tac >> Cases_on `sb` >>
  TRY (rename1 `ValueSubscript sv` >> Cases_on `sv`) >>
  simp[mem_step_offset_def] >> rpt strip_tac
  >~ [`value_has_type (ArrayTV _ _) _`] >- suspend "array"
  >~ [`value_has_type (TupleTV _) _`] >- suspend "tuple"
  >> suspend "struct"
QED
Resume aug_place_step_project[array]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  irule aug_place_array_project >> goal_assum (drule_at Any) >>
  gvs[evaluate_subscripts_def, AllCaseEqs()] >> metis_tac[]
QED
Resume aug_place_step_project[tuple]:
  Cases_on `a` >> gvs[value_has_type_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >> gvs[value_has_type_def] >>
  gvs[evaluate_subscripts_def, array_index_def, oEL_THM,
      subscript_type_def, val_in_memory_def, AllCaseEqs()] >>
  irule aug_place_tuple_project >> goal_assum (drule_at Any) >> simp[]
QED
Resume aug_place_step_project[struct]:
  Cases_on `a` >> gvs[value_has_type_def, val_in_memory_def] >>
  gvs[evaluate_subscripts_def, AllCaseEqs()] >>
  drule_all aug_place_fields_project >> simp[]
QED
Finalise aug_place_step_project

Theorem aug_place_field_type:
  !fts id off etv.
    mem_field_offset fts id = SOME (off,etv) ==> ALOOKUP fts id = SOME etv
Proof
  Induct >> simp[mem_field_offset_def] >> PairCases >>
  simp[mem_field_offset_def] >> rpt gen_tac >>
  Cases_on `h0 = id` >> simp[AllCaseEqs()] >> rpt strip_tac >>
  PairCases_on `z` >> gvs[] >> metis_tac[]
QED

Theorem aug_place_step_type:
  !tv sb off etv.
    mem_step_offset tv sb = SOME (off,etv) ==>
    subscript_type tv sb = SOME etv
Proof
  Cases >> Cases >> simp[mem_step_offset_def, subscript_type_def] >>
  TRY (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
       simp[mem_step_offset_def, subscript_type_def]) >>
  rpt gen_tac
  >- (Cases_on `b` >> simp[mem_step_offset_def, subscript_type_def,
                          vyperASTTheory.bound_length_def] >> metis_tac[])
  >> metis_tac[aug_place_field_type]
QED

Theorem aug_place_path_project:
  !path tv a base mem off ptv v.
    value_has_type tv a /\ well_formed_type_value tv /\
    val_in_memory tv a base mem /\ mem_path_offset tv path = SOME (off,ptv) /\
    evaluate_subscripts tv a path = INL v ==>
    val_in_memory ptv v (base + off) mem
Proof
  Induct >> simp[mem_path_offset_def, evaluate_subscripts_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[AllCaseEqs()] >> PairCases_on `z` >> gvs[] >>
  `subscript_type tv h = SOME etv` by metis_tac[aug_place_step_type] >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`,`a`] mp_tac) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `well_formed_type_value etv` by metis_tac[subscript_type_well_formed] >>
  `subscripts_type tv [h] = SOME etv` by simp[subscripts_type_def] >>
  `value_has_type etv v'` by metis_tac[evaluate_subscripts_type] >>
  `val_in_memory etv v' (base' + k) mem` by
    metis_tac[aug_place_step_project] >>
  `evaluate_subscripts etv v' path = INL v` by metis_tac[] >>
  first_x_assum drule_all >>
  simp_tac bool_ss [arithmeticTheory.ADD_ASSOC]
QED

Theorem aug_place_memory_word:
  !ctx func cenv cx es s id p sz w entry path off ptv v ty.
    stmt_state_rel ctx func cenv cx es s /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w /\ lookup_scopes id es.scopes = SOME entry /\
    value_has_type entry.type entry.value /\ well_formed_type_value entry.type /\
    mem_path_offset entry.type path = SOME (off,ptv) /\
    evaluate_subscripts entry.type entry.value path = INL v /\
    is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME ptv ==>
    mload (w2n (w + n2w off)) s = typed_val_to_w256 ptv v
Proof
  rpt strip_tac >>
  `local_ptrs_rel func cenv es.scopes s /\ alloca_room ctx func s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `w2n w + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz /\
   val_in_memory entry.type entry.value (w2n w) s.vs_memory` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `s.vs_alloca_next < dimword (:256)` by metis_tac[alloca_room_next_lt] >>
  drule mem_path_offset_sound >> strip_tac >>
  `w2n (w + n2w off) = w2n w + off` by
    (irule buffer_offset_no_wrap >> qexists_tac `sz` >> decide_tac) >>
  `val_in_memory ptv v (w2n w + off) s.vs_memory` by
    metis_tac[aug_place_path_project] >>
  `value_has_type ptv v` by metis_tac[evaluate_subscripts_type] >>
  simp[GSYM mem_word_at_eq_mload] >>
  irule val_in_memory_word_type >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem aug_place_entry_type_agrees:
  expr_sim_inv cenv cx env s /\ s'.scopes = s.scopes /\
  lookup_scopes id s'.scopes = SOME entry /\
  cenv.ce_var_type id = SOME ty ==>
  evaluate_type (get_tenv cx) ty = SOME entry.type
Proof
  rpt strip_tac >>
  gvs[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
  `?ety. FLOOKUP env.var_types id = SOME ety` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem aug_place_memory_load:
  expr_sim_inv cenv cx env es /\
  supported_target_info tops bindings t = SOME info /\
  eval_target_place cx t es = (INL (MemoryPlace id path),st) /\
  read_place cx (MemoryPlace id path) st = (INL cur,st') /\
  stmt_state_rel ctx func cenv cx st s /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) /\
  is_word_type ty ==>
  ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
       mload (w2n w) s = typed_val_to_w256 tv cur
Proof
  rpt strip_tac >>
  drule_all aug_place_target_memory_live >> strip_tac >>
  `value_has_type entry.type entry.value /\ well_formed_type_value entry.type` by
    metis_tac[aug_place_target_entry_typed] >>
  `st.scopes = es.scopes` by metis_tac[aug_place_target_scopes] >>
  gvs[place_ptr_rel_def] >>
  `tv0 = entry.type` by metis_tac[aug_place_entry_type_agrees, optionTheory.SOME_11] >>
  gvs[] >>
  `cur = v` by
    gvs[read_place_def, get_scopes_def, bind_def, lift_option_type_def,
        lift_sum_def, return_def, read_memory_path_def] >>
  irule aug_place_memory_word >>
  goal_assum (drule_at Any) >> metis_tac[]
QED
