Theory bodyPtrSubscriptPathRebuild
Ancestors
  bodyPtrSubscriptMemoryRebuild bodyPtrSubscriptCurrentMemory exprSimProps
  vyperPlaceStatePreservation vyperAssignPreservesType vyperState vyperTyping
  loweringPosts valueEncoding list arithmetic

Theorem assign_subscripts_cons_replace_decompose:
  !tv sb etv a path new a'.
    subscript_type tv sb = SOME etv /\
    assign_subscripts tv a (sb::path) (Replace new) = INL a' ==>
    ?child changed.
      evaluate_subscripts tv a [sb] = INL child /\
      assign_subscripts etv child path (Replace new) = INL changed /\
      assign_subscripts tv a [sb] (Replace changed) = INL a'
Proof
  rpt gen_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      simp[subscript_type_def] >> Cases_on `tv` >>
      simp[subscript_type_def] >> Cases_on `a` >>
      simp[assign_subscripts_def, evaluate_subscripts_def, CaseEq "option",
           CaseEq "sum"] >> rpt strip_tac >> gvs[subscript_type_def] >> metis_tac[]) >>
  Cases_on `tv` >> Cases_on `a` >>
  simp[subscript_type_def, assign_subscripts_def, evaluate_subscripts_def,
       CaseEq "option", CaseEq "sum"] >> rpt strip_tac >> gvs[subscript_type_def] >> metis_tac[]
QED

Theorem assign_subscripts_step_preserves_type:
  !tv a sb etv new a'.
    subscript_type tv sb = SOME etv /\ value_has_type tv a /\
    well_formed_type_value tv /\ value_has_type etv new /\
    assign_subscripts tv a [sb] (Replace new) = INL a' ==>
    value_has_type tv a'
Proof
  rpt gen_tac >> Cases_on `sb`
  >- (rename1 `ValueSubscript sv` >> Cases_on `sv` >>
      simp[subscript_type_def] >> Cases_on `tv` >> simp[subscript_type_def]
      >- (Cases_on `a` >> simp[value_has_type_def] >>
          rename1 `ArrayV av` >> Cases_on `av` >>
          simp[value_has_type_def, assign_subscripts_def,
               vyperValueOperationTheory.array_set_index_def, CaseEq "option"] >>
          rpt strip_tac >> gvs[]) >>
      rpt strip_tac >> gvs[] >> drule assign_subscripts_preserves_type >>
      simp[leaf_type_def]) >>
  Cases_on `tv` >> simp[subscript_type_def, CaseEq "option"] >>
  rpt strip_tac >> gvs[] >> drule assign_subscripts_preserves_type >>
  simp[leaf_type_def]
QED

Theorem mem_path_replace_in_memory_typed:
  !path tv a old a' new off mem mem' k ptv.
    value_has_type tv a /\ well_formed_type_value tv /\
    val_in_memory tv a off mem /\ mem_path_offset tv path = SOME (k,ptv) /\
    evaluate_subscripts tv a path = INL old /\
    assign_subscripts tv a path (Replace new) = INL a' /\
    value_has_type ptv new /\ val_in_memory ptv new (off+k) mem' /\
    (!addr. addr < off+k \/ off+k+type_memory_size ptv <= addr ==>
      (if addr < LENGTH mem' then EL addr mem' else 0w) =
      (if addr < LENGTH mem then EL addr mem else 0w)) ==>
    value_has_type tv a' /\ val_in_memory tv a' off mem'
Proof
  Induct >> rpt gen_tac
  >- (simp[mem_path_offset_def, evaluate_subscripts_def, assign_subscripts_def] >>
      rpt strip_tac >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `mem_path_offset tv (h::path) = _` mp_tac >>
  simp[Once mem_path_offset_def, CaseEq "option", pairTheory.EXISTS_PROD] >>
  strip_tac >> qpat_x_assum `k = _` SUBST_ALL_TAC >>
  rename1 `mem_step_offset tv h = SOME (d,etv)` >>
  `subscript_type tv h = SOME etv` by
    (mp_tac (Q.SPEC `[h]` mem_path_offset_sound) >>
     disch_then (qspecl_then [`tv`, `d`, `etv`] mp_tac) >>
     simp[mem_path_offset_def, subscripts_type_def] >>
     Cases_on `subscript_type tv h` >> simp[]) >>
  drule_all assign_subscripts_cons_replace_decompose >> strip_tac >>
  `value_has_type etv child` by
    (irule evaluate_subscripts_type >>
     qexistsl_tac [`a`, `[h]`, `tv`] >> simp[subscripts_type_def]) >>
  `well_formed_type_value etv` by metis_tac[subscript_type_well_formed] >>
  `val_in_memory etv child (off+d) mem` by
    (irule mem_step_offset_current_value >> metis_tac[]) >>
  `evaluate_subscripts etv child path = INL old` by
    (drule evaluate_subscripts_cons_typed >>
     disch_then (qspecl_then [`path`, `a`] mp_tac) >> simp[]) >>
  `value_has_type etv changed /\ val_in_memory etv changed (off+d) mem'` by
    (first_x_assum irule >>
     asm_simp_tac (srw_ss()) [arithmeticTheory.ADD_ASSOC] >>
     qexistsl_tac [`child`, `mem`, `new`, `old`] >>
     asm_simp_tac (srw_ss()) [GSYM ADD_ASSOC] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qpat_x_assum `!tv a old a' new off mem mem' k ptv. _` kall_tac >>
  conj_tac >- (irule assign_subscripts_step_preserves_type >> metis_tac[]) >>
  drule mem_path_offset_sound >> strip_tac >>
  irule mem_step_replace_in_memory >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac >- metis_tac[ADD_COMM] >>
  qx_gen_tac `addr` >> strip_tac >>
  qpat_x_assum `!addr. _` (qspec_then `addr` mp_tac) >>
  (impl_tac >- decide_tac) >> simp[]
QED
