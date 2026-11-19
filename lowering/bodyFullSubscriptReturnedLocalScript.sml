(* Source liveness at the original local, before the ordered Pop trace. *)
Theory bodyFullSubscriptReturnedLocal
Ancestors
  exprSimSource exprSimSubscriptArrayOrigin bodySimAugPlaceMemory
  vyperEvalExprPreservesScopesDom vyperTypeEvalSoundness vyperTypeEnv
  vyperTypeEnvPreservation vyperPlaceMutationSoundness vyperPlaceResultTyping
  vyperTypeEvalProofs vyperState vyperInterpreter vyperLookup vyperMisc
  vyperTypeInvariants vyperAST vyperCallFrame vyperCreateFrame
  vyperLocalAccessFrame sum pair exprSimIfExp

Theorem original_local_root[local]:
  typed_scope_transition es s /\ IS_SOME (lookup_scopes id s.scopes) ==>
  ?initial v. lookup_scopes id es.scopes = SOME initial /\
              evaluate_subscripts initial.type initial.value [] = INL v
Proof
  strip_tac >> fs[typed_scope_transition_def] >>
  drule scope_pop_trace_scopes_dom >> strip_tac >>
  drule lookup_scopes_is_some_same_fdoms >>
  disch_then (qspec_then `id` mp_tac) >>
  Cases_on `lookup_scopes id es.scopes` >>
  simp[evaluate_subscripts_def]
QED

Theorem original_local_entry_trace[local]:
  typed_scope_transition es s /\
  lookup_scopes id es.scopes = SOME initial /\
  lookup_scopes id s.scopes = SOME entry ==>
  ?events. entry_pop_trace initial events entry /\ entry_pop_trace_valid events
Proof
  strip_tac >> fs[typed_scope_transition_def] >>
  drule_all scope_pop_trace_lookup >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> irule entry_events_valid >> simp[]
QED

Theorem original_local_extend[local]:
  (!initial events entry p tv v sb w v0.
     value_has_type initial.type initial.value /\
     well_formed_type_value initial.type /\
     EVERY (\k. ?err. evaluate_subscripts initial.type initial.value k = INR err)
           (MAP FST initial.popped) /\
     entry_pop_trace initial events entry /\ entry_pop_trace_valid events /\
     evaluate_subscripts initial.type initial.value p = INL v0 /\
     subscripts_type entry.type p = SOME tv /\
     read_memory_path entry p = INL v /\ evaluate_subscripts tv v [sb] = INL w ==>
     ?w0. evaluate_subscripts initial.type initial.value (p ++ [sb]) = INL w0) /\
  state_well_typed es /\ popped_keys_indexed es.scopes /\
  typed_scope_transition es s /\
  lookup_scopes id s.scopes = SOME entry /\
  subscripts_type entry.type p = SOME tv /\
  read_memory_path entry p = INL v /\ evaluate_subscripts tv v [sb] = INL w /\
  (?initial v0. lookup_scopes id es.scopes = SOME initial /\
                evaluate_subscripts initial.type initial.value p = INL v0) ==>
  ?initial w0. lookup_scopes id es.scopes = SOME initial /\
               evaluate_subscripts initial.type initial.value (p ++ [sb]) = INL w0
Proof
  strip_tac >> drule_all original_local_entry_trace >> strip_tac >>
  drule_all popped_keys_indexed_lookup_dead >> strip_tac >>
  fs[state_well_typed_def] >> drule_all scope_well_typed_lookup_scopes >> strip_tac >>
  first_x_assum (drule_all_then strip_assume_tac) >> metis_tac[]
QED

Theorem extend_place_memory_success_read[local]:
  extend_place cx pv sb s = (INL (PlaceR (MemoryPlace id p)),t) ==>
  ?q entry tv v w.
    pv = PlaceR (MemoryPlace id q) /\ p = q ++ [sb] /\
    lookup_scopes id s.scopes = SOME entry /\
    subscripts_type entry.type q = SOME tv /\ read_memory_path entry q = INL v /\
    evaluate_subscripts tv v [sb] = INL w
Proof
  strip_tac >> drule aug_place_extend_memory_inversion >> strip_tac >>
  Cases_on `lookup_scopes id s.scopes` >>
  gvs[extend_place_def, place_type_value_def, read_place_def, get_scopes_def,
      bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
      return_def, raise_def, extend_memory_place_def, AllCaseEqs()] >>
  rename1 `lookup_scopes id s.scopes = SOME e` >>
  Cases_on `subscripts_type e.type old` >> gvs[return_def, raise_def] >>
  Cases_on `read_memory_path e old` >> gvs[return_def, raise_def] >>
  qmatch_asmsub_rename_tac `evaluate_subscripts tv v [sb]` >>
  Cases_on `evaluate_subscripts tv v [sb]` >> gvs[return_def, raise_def]
QED

Theorem select_result_memory_success_read[local]:
  select_result cx ty pv sb s = (INL (PlaceR (MemoryPlace id p)),t) ==>
  ?q entry tv v w.
    pv = PlaceR (MemoryPlace id q) /\ p = q ++ [sb] /\
    lookup_scopes id s.scopes = SOME entry /\
    subscripts_type entry.type q = SOME tv /\ read_memory_path entry q = INL v /\
    evaluate_subscripts tv v [sb] = INL w
Proof
  strip_tac >> drule select_result_memory_origin >> strip_tac >>
  gvs[select_result_def] >> drule extend_place_memory_success_read >> simp[]
QED

Theorem subscript_returned_local_live_from_extension:
  !es.
  state_well_typed es /\ popped_keys_indexed es.scopes /\
  (!initial events entry p tv v sb w v0.
     value_has_type initial.type initial.value /\
     well_formed_type_value initial.type /\
     EVERY (\k. ?err. evaluate_subscripts initial.type initial.value k = INR err)
           (MAP FST initial.popped) /\
     entry_pop_trace initial events entry /\ entry_pop_trace_valid events /\
     evaluate_subscripts initial.type initial.value p = INL v0 /\
     subscripts_type entry.type p = SOME tv /\
     read_memory_path entry p = INL v /\ evaluate_subscripts tv v [sb] = INL w ==>
     ?w0. evaluate_subscripts initial.type initial.value (p ++ [sb]) = INL w0) ==>
  (!cx:evaluation_context. !s:stmt. T) /\
  (!cx:evaluation_context. !ss:stmt list. T) /\
  (!cx:evaluation_context. !it:iterator. T) /\
  (!cx:evaluation_context. !tyv:type_value. !id:string. !body:stmt list. !vs:eval_result list. T) /\
  (!cx e env s t id p.
    (well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
    env_consistent env cx s /\ state_well_typed s /\
    context_well_typed cx /\ accounts_well_typed s.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\ typed_scope_transition es s /\
    eval_expr cx e s = (INL (PlaceR (MemoryPlace id p)),t) ==>
    ?initial v. lookup_scopes id es.scopes = SOME initial /\
                evaluate_subscripts initial.type initial.value p = INL v) /\
  (!cx:evaluation_context. !args:expr list. T) /\
  (!cx bt env vt s t id p.
    type_place_target env bt = SOME vt /\ env_consistent env cx s /\ state_well_typed s /\
    context_well_typed cx /\ accounts_well_typed s.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ typed_scope_transition es s /\
    eval_base_place cx bt s = (INL (PlaceR (MemoryPlace id p)),t) ==>
    ?initial v. lookup_scopes id es.scopes = SOME initial /\
                evaluate_subscripts initial.type initial.value p = INL v) /\
  (!cx bt env ty s t id p.
    well_typed_target env bt ty /\ env_consistent env cx s /\ state_well_typed s /\
    context_well_typed cx /\ accounts_well_typed s.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\ typed_scope_transition es s /\
    eval_target_place cx bt s = (INL (MemoryPlace id p),t) ==>
    ?initial v. lookup_scopes id es.scopes = SOME initial /\
                evaluate_subscripts initial.type initial.value p = INL v) /\
  (!cx:evaluation_context. !g:assignment_target. !v:value. T) /\
  (!cx:evaluation_context. !gs:assignment_target list. !vs:value list. T)
Proof
  gen_tac >> strip_tac >> ho_match_mp_tac evaluate_ind >>
  rpt conj_tac >> simp[] >> rpt strip_tac >>
  FIRST [qpat_x_assum `eval_expr _ _ _ = _` mp_tac,
         qpat_x_assum `eval_base_place _ _ _ = _` mp_tac,
         qpat_x_assum `eval_target_place _ _ _ = _` mp_tac] >>
  simp[NoAsms, Once evaluate_def, bind_def, ignore_bind_def,
       return_def, raise_def, get_scopes_def, type_check_def, assert_def, AllCaseEqs(),
       lookup_global_not_memory] >> strip_tac >> gvs[]
  >>~- ([`?initial v. lookup_scopes _ _.scopes = SOME initial /\
                      evaluate_subscripts initial.type initial.value [] = INL v`],
        drule_all_then ACCEPT_TAC original_local_root) >>
  TRY (drule lookup_flag_mem_to_lookup_flag_member_some >>
       PairCases_on `nsid` >> simp[lookup_flag_member_def, AllCaseEqs()] >> NO_TAC) >>
  TRY (drule_then strip_assume_tac eval_send_success_value >> gvs[] >> NO_TAC) >>
  TRY (drule_then strip_assume_tac eval_ext_call_success_value >> gvs[] >> NO_TAC) >>
  TRY (drule_then strip_assume_tac eval_raw_call_success_value >> gvs[] >> NO_TAC) >>
  TRY (drule_then strip_assume_tac eval_create_success_value >> gvs[] >> NO_TAC) >>
  TRY (qpat_assum `well_typed_expr _ (IfExp _ _ _ _)` (K (suspend "IfExp"))) >>
  TRY (qpat_assum `well_typed_expr _ (Attribute _ _ _)` (K (suspend "Attribute"))) >>
  TRY (qpat_assum `well_typed_expr _ (Subscript _ _ _)` (K (suspend "Subscript"))) >>
  TRY (qpat_assum `type_place_expr _ (Subscript _ _ _) = SOME _` (K (suspend "Subscript"))) >>
  TRY (qpat_x_assum `type_place_expr _ _ = SOME _`
       (fn th => mp_tac th >> simp[Once vyperTypeSystemTheory.well_typed_expr_def] >> NO_TAC)) >>
  TRY (qpat_assum `well_typed_expr _ (Pop _ _)` (K (suspend "Pop"))) >>
  TRY (qpat_assum `type_place_target _ (AttributeTarget _ _) = _` (K (suspend "AttributeTarget"))) >>
  TRY (qpat_assum `type_place_target _ (SubscriptTarget _ _) = _` (K (suspend "SubscriptTarget"))) >>
  TRY (qpat_assum `get_place _ _ = _` (K (suspend "Target"))) >>
  gvs[lift_option_type_def, lift_sum_def, bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  drule_then strip_assume_tac eval_create_operands_success_value >> gvs[]
QED

Resume subscript_returned_local_live_from_extension[Target]:
  qpat_x_assum `get_place _ _ = _` mp_tac >>
  qmatch_goalsub_rename_tac `get_place pv _` >>
  Cases_on `pv` >> simp[get_place_def, return_def, raise_def] >>
  strip_tac >> gvs[vyperTypeSystemTheory.well_typed_target_def] >>
  first_x_assum (drule_all_then strip_assume_tac) >> metis_tac[]
QED

Resume subscript_returned_local_live_from_extension[Attribute]:
  drule select_result_memory_success_read >> strip_tac >> gvs[] >>
  qpat_x_assum `well_typed_expr _ (Attribute _ _ _)` mp_tac >>
  simp[Once vyperTypeSystemTheory.well_typed_expr_def] >> strip_tac >>
  gvs[vyperTypeCallGraphTheory.int_calls_expr_def] >>
  Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac)
    `well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt` >- simp[] >>
  drule_all (cj 2 (cj 5 eval_scc_type_sound_mutual)) >> strip_tac >>
  drule_all typed_scope_transition_trans >> strip_tac >>
  qpat_assum `!env' ss tt ii pp. _ ==> _` (drule_all_then assume_tac) >>
  drule_all original_local_extend >> simp[]
QED

Resume subscript_returned_local_live_from_extension[AttributeTarget]:
  drule extend_place_memory_success_read >> strip_tac >> gvs[] >>
  gvs[type_place_target_AttributeTarget, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  drule_all (cj 2 (cj 7 eval_scc_type_sound_mutual)) >> strip_tac >>
  drule_all typed_scope_transition_trans >> strip_tac >>
  qpat_assum `!env' vt' ss tt ii pp. _ ==> _` (drule_all_then assume_tac) >>
  drule_all original_local_extend >> simp[]
QED

Resume subscript_returned_local_live_from_extension[IfExp]:
  drule ifexp_conditional_result_shape >> strip_tac >> gvs[] >>
  qpat_x_assum `well_typed_expr _ (IfExp _ _ _ _)` mp_tac >>
  simp[Once vyperTypeSystemTheory.well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `switch_BoolV _ _ _ _ _ = _` mp_tac >>
  simp[switch_BoolV_def, bind_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  gvs[vyperTypeCallGraphTheory.int_calls_expr_def] >>
  ntac 2 (imp_res_tac vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left) >>
  imp_res_tac vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right >>
  drule_all (cj 1 (cj 5 eval_scc_type_sound_mutual)) >>
  disch_then (drule_then strip_assume_tac o CONJUNCT1) >>
  Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac)
    `well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt` >- simp[] >>
  drule_all (cj 2 (cj 5 eval_scc_type_sound_mutual)) >> strip_tac >>
  drule_all typed_scope_transition_trans >> strip_tac >>
  rpt (qpat_x_assum `!ss rr tt. eval_expr _ _ ss = (INL rr,tt) ==> _`
       (drule_then assume_tac)) >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  rpt IF_CASES_TAC >> simp[raise_def] >> strip_tac >> metis_tac[]
QED

Resume subscript_returned_local_live_from_extension[SubscriptTarget]:
  drule extend_place_memory_success_read >> strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  gvs[type_place_target_SubscriptTarget, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  imp_res_tac vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left >>
  imp_res_tac vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right >>
  qpat_assum `!env' vt' ss tt ii pp. _ ==> _` (drule_all_then assume_tac) >>
  drule_all (cj 1 (cj 7 eval_scc_type_sound_mutual)) >> strip_tac >>
  drule_all (cj 2 (cj 7 eval_scc_type_sound_mutual)) >> strip_tac >>
  Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac)
    `well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt` >- simp[] >>
  drule_all (cj 2 (cj 5 eval_scc_type_sound_mutual)) >> strip_tac >>
  `typed_scope_transition es s'³'` by metis_tac[typed_scope_transition_trans] >>
  drule_all original_local_extend >> simp[]
QED

Resume subscript_returned_local_live_from_extension[Subscript]:
  markerLib.RESUME_TAC >>
  drule select_result_memory_success_read >> strip_tac >> gvs[] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  Cases_on `subscript_reads_base cx e e'` >>
  simp[bind_def, return_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  imp_res_tac read_result_state >> gvs[] >>
  gvs[vyperTypeCallGraphTheory.int_calls_expr_def] >>
  imp_res_tac vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_left >>
  imp_res_tac vyperTypeCallStackSoundnessTheory.call_evaluation_safe_append_right >>
  (Q_TAC (fn tm => SUBGOAL_THEN tm (CONJUNCTS_THEN2 assume_tac assume_tac))
     `(well_typed_expr env e \/ ?vt. type_place_expr env e = SOME vt) /\
      well_typed_expr env e'` >-
   (irule constSubstCorrectTheory.frame_subscript_typing >> metis_tac[])) >>
  qpat_assum `!env' ss tt ii pp. _ ==> _` (drule_all_then assume_tac) >>
  rename1 `eval_expr cx e' sm = (INL idx,sf)` >>
  `state_well_typed sm /\ env_consistent env cx sm /\ accounts_well_typed sm.accounts` by
    (drule_all (cj 1 (cj 5 eval_scc_type_sound_mutual)) >> metis_tac[]) >>
  drule_all (cj 2 (cj 5 eval_scc_type_sound_mutual)) >> strip_tac >>
  qpat_x_assum `eval_expr cx e s = _` kall_tac >>
  Q_TAC (fn tm => SUBGOAL_THEN tm assume_tac)
    `well_typed_expr env e' \/ ?vt. type_place_expr env e' = SOME vt` >>
  TRY (simp[] >> NO_TAC) >>
  drule_all (cj 2 (cj 5 eval_scc_type_sound_mutual)) >> strip_tac >>
  `typed_scope_transition es sf` by metis_tac[typed_scope_transition_trans] >>
  drule_all original_local_extend >> simp[]
QED

Resume subscript_returned_local_live_from_extension[Pop]:
  qpat_x_assum `pop_place cx p' _ = _` mp_tac >>
  Cases_on `p'`
  >- (rename1 `StoragePlace tr slot tv` >>
      Cases_on `tv` >> simp[pop_place_def, raise_def] >>
      rename1 `ArrayTV el bd` >> Cases_on `bd` >>
      simp[pop_place_def, raise_def, vyperStorageBackendTheory.get_storage_backend_eq,
           bind_def, check_def, assert_def, ignore_bind_apply, return_def, AllCaseEqs()])
  >~ [`pop_place _ (ImmutablePlace _ _ _) _ = _ ==> _`]
  >- simp[pop_place_def, bind_def, return_def, raise_def, lift_sum_def,
          lift_option_type_def, ignore_bind_apply, AllCaseEqs()] >>
  strip_tac >> drule pop_memory_place_success >> strip_tac >> gvs[] >>
  rename1 `well_typed_expr env (Pop ann bt)` >>
  drule vyperTypeAssignContextTheory.well_typed_expr_Pop_dynamic_target_assignable >> strip_tac >>
  `well_typed_target env bt (ArrayT ann (Dynamic n))` by
    simp[vyperTypeSystemTheory.well_typed_target_def] >>
  gvs[vyperTypeCallGraphTheory.int_calls_expr_def] >>
  drule_all (cj 1 (cj 8 eval_scc_type_sound_mutual)) >> strip_tac >>
  drule_all (cj 2 (cj 8 eval_scc_type_sound_mutual)) >> strip_tac >>
  drule_all (cj 3 (cj 8 eval_scc_type_sound_mutual)) >> strip_tac >>
  drule_all typed_scope_transition_trans >> strip_tac >>
  drule find_containing_scope_lookup >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  rename1 `runtime_place_typed cx sm (MemoryPlace id path) (ArrayTV et (Dynamic n))` >>
  `subscripts_type entry.type path = SOME (ArrayTV et (Dynamic n)) /\
   value_has_type (ArrayTV et (Dynamic n)) (ArrayV (DynArrayV vs))` by
    (irule memory_dynamic_array_authoritative_read >>
     conj_tac >- simp[] >>
     qexistsl [`cx`,`id`,`sm`] >> fs[live_memory_result_def] >> metis_tac[]) >>
  `evaluate_subscripts (ArrayTV et (Dynamic n)) (ArrayV (DynArrayV vs))
     [ValueSubscript (IntV (&(LENGTH vs - 1)))] = INL (LAST vs)` by
    (`LENGTH vs - 1 < LENGTH vs` by (Cases_on `vs` >> gvs[]) >>
     simp[evaluate_subscripts_def, vyperValueOperationTheory.array_index_def,
          listTheory.oEL_THM, listTheory.LAST_EL, arithmeticTheory.PRE_SUB1]) >>
  qpat_assum `!env' ty ss tt ii pp. _ ==> _` (drule_all_then assume_tac) >>
  drule_all original_local_extend >> simp[]
QED

Finalise subscript_returned_local_live_from_extension
