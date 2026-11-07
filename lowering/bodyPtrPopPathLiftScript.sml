Theory bodyPtrPopPathLift
Ancestors bodyPtrPopPathStep vyperState vyperTyping vyperValueOperation
  valueTypingMemoryProps vyperLookup exprSimProps loweringPosts
  vyperPlaceStatePreservation bodyPtrDefs

Theorem pop_assign_subscripts_cons_typed:
  !tv sb etv root rest ao updated.
  subscript_type tv sb = SOME etv /\
  assign_subscripts tv root (sb::rest) ao = INL updated ==>
  ?child child'. evaluate_subscripts tv root [sb] = INL child /\
    assign_subscripts etv child rest ao = INL child' /\
    assign_subscripts tv root [sb] (Replace child') = INL updated
Proof
  Cases_on `sb`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >> Cases_on `tv` >>
      simp[subscript_type_def] >> Cases_on `root` >>
      simp[assign_subscripts_def, evaluate_subscripts_def] >>
      rpt strip_tac >> gvs[AllCaseEqs(), subscript_type_def] >> metis_tac[]) >>
  Cases_on `tv` >> simp[subscript_type_def] >> Cases_on `root` >>
  simp[assign_subscripts_def, evaluate_subscripts_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), subscript_type_def] >> metis_tac[]
QED

Theorem pop_path_robust_memory_replace:
  !path rt root old updated k ct new addr dirty mem mem' writes.
  well_formed_type_value rt /\ value_has_type rt root /\
  evaluate_subscripts rt root path = INL old /\
  assign_subscripts rt root path (Replace new) = INL updated /\
  mem_path_offset rt path = SOME (k,ct) /\
  (!x. x IN writes ==> addr+k <= x /\ x < addr+k+type_memory_size ct) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory rt root addr m) /\
  (!m. mem_agree_outside dirty mem' m ==> val_in_memory ct new (addr+k) m) ==>
  !m. mem_agree_outside dirty mem' m ==> val_in_memory rt updated addr m
Proof
  Induct_on `path`
  >- simp[evaluate_subscripts_def, assign_subscripts_def, mem_path_offset_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[Once mem_path_offset_def, AllCaseEqs()] >>
  rename1 `mem_step_offset rt h = SOME (step0,step1)` >>
  rename1 `mem_path_offset step1 path = SOME tail` >> PairCases_on `tail` >> gvs[] >>
  `mem_path_offset rt [h] = SOME (step0,step1)` by simp[mem_path_offset_def] >>
  drule mem_path_offset_sound >> simp[subscripts_type_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all pop_assign_subscripts_cons_typed >> strip_tac >>
  `evaluate_subscripts step1 child path = INL old` by
    (drule evaluate_subscripts_cons_typed >>
     disch_then (qspecl_then [`path`, `root`] mp_tac) >> simp[] >> metis_tac[]) >>
  `well_formed_type_value step1` by
    (irule subscripts_type_well_formed >> goal_assum (drule_at Any) >>
     qexists_tac `[h]` >> simp[subscripts_type_def]) >>
  `value_has_type step1 child` by
    (irule evaluate_subscripts_type >> qexistsl_tac [`root`, `[h]`, `rt`] >>
     simp[subscripts_type_def]) >>
  `!m. mem_agree_outside dirty mem m ==>
    val_in_memory step1 child (addr+step0) m` by
    (rpt strip_tac >> drule_all pop_step_robust_memory_extract >> simp[]) >>
  `!m. mem_agree_outside dirty mem' m ==>
    val_in_memory step1 child' (addr+step0) m` by
    (rpt strip_tac >> first_x_assum irule >> simp[] >>
     qexistsl_tac [`dirty`, `mem`, `mem'`] >>
     qexists_tac `new` >> simp[] >>
     ntac 2 (goal_assum (drule_at Any) >> simp[])) >>
  qpat_x_assum `mem_path_offset rt [h] = _` kall_tac >>
  drule mem_path_offset_sound >> strip_tac >>
  `!x. x IN writes ==> addr+step0 <= x /\
    x < addr+step0+type_memory_size step1` by
    (rpt strip_tac >> qpat_x_assum `!x. x IN writes ==> _` drule >> decide_tac) >>
  `val_wf rt root` by metis_tac[value_has_type_memory_wf] >>
  qpat_x_assum `!rt root old updated k ct new addr dirty mem mem' writes. _` kall_tac >>
  rpt strip_tac >> irule pop_step_robust_memory_replace >> simp[] >>
  qpat_assum `assign_subscripts rt root [h] _ = _` (irule_at Any) >> simp[] >>
  qexistsl_tac [`writes`, `mem'`, `mem`, `dirty`] >>
  fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED

Theorem pop_path_robust_memory_pop:
  !path rt root old updated k ct new addr dirty mem mem' writes.
  well_formed_type_value rt /\ value_has_type rt root /\
  evaluate_subscripts rt root path = INL old /\
  assign_subscripts rt root path PopOp = INL updated /\
  pop_element old = INL new /\
  mem_path_offset rt path = SOME (k,ct) /\
  (!x. x IN writes ==> addr+k <= x /\ x < addr+k+type_memory_size ct) /\
  mem_agree_outside writes mem' mem /\
  (!m. mem_agree_outside dirty mem m ==> val_in_memory rt root addr m) /\
  (!m. mem_agree_outside dirty mem' m ==> val_in_memory ct new (addr+k) m) ==>
  !m. mem_agree_outside dirty mem' m ==> val_in_memory rt updated addr m
Proof
  rpt gen_tac >> strip_tac >>
  drule_all assign_subscripts_pop_replace >>
  disch_then (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  rpt strip_tac >> irule pop_path_robust_memory_replace >> simp[] >>
  qpat_assum `assign_subscripts rt root path _ = _` (irule_at Any) >> simp[] >>
  qexistsl_tac [`writes`, `mem'`, `mem`, `dirty`] >>
  fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
QED
