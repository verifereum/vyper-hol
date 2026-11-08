Theory bodyPtrPopLivePath
Ancestors bodyPtrPopLiveStep bodyPtrPopLiveSupport bodyPtrPopPathLift vyperPlaceStatePreservation
  exprSimProps loweringPosts vyperState vyperTyping pred_set list arithmetic

Theorem pop_path_support_extract:
  !path rt root child k ct addr supp.
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root path = INL child /\
  mem_path_offset rt path = SOME (k,ct) ==>
  ?cs. pop_live_support ct child (addr+k) cs /\ cs SUBSET supp
Proof
  Induct_on `path`
  >- (simp[evaluate_subscripts_def, mem_path_offset_def] >> metis_tac[SUBSET_REFL]) >>
  rpt gen_tac >> strip_tac >>
  gvs[Once mem_path_offset_def, AllCaseEqs()] >>
  rename1 `mem_step_offset rt h = SOME (step0,step1)` >>
  rename1 `mem_path_offset step1 path = SOME tail` >> PairCases_on `tail` >> gvs[] >>
  `mem_path_offset rt [h] = SOME (step0,step1)` by simp[mem_path_offset_def] >>
  drule mem_path_offset_sound >> simp[subscripts_type_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule evaluate_subscripts_cons_typed >>
  disch_then (qspecl_then [`path`, `root`] mp_tac) >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule_all pop_step_support_extract >> strip_tac >>
  `evaluate_subscripts step1 v path = INL child` by metis_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `cs'` >> FULL_SIMP_TAC bool_ss [ADD_ASSOC] >>
  metis_tac[SUBSET_TRANS]
QED

Theorem pop_path_support_header:
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root path = INL (ArrayV (DynArrayV vs)) /\
  mem_path_offset rt path = SOME (k,ArrayTV et (Dynamic cap)) ==>
  {i | addr+k <= i /\ i < addr+k+32} SUBSET supp
Proof
  strip_tac >> drule_all pop_path_support_extract >> strip_tac >>
  drule pop_live_support_header >> metis_tac[SUBSET_TRANS]
QED

Theorem pop_path_support_split:
  !path rt root addr supp pre last k et cap updated.
  pop_live_support rt root addr supp /\
  evaluate_subscripts rt root path = INL (ArrayV (DynArrayV (pre ++ [last]))) /\
  mem_path_offset rt path = SOME (k,ArrayTV et (Dynamic cap)) /\
  assign_subscripts rt root path PopOp = INL updated ==>
  ?left right. supp = left UNION right /\ DISJOINT left right /\
    pop_live_support rt updated addr left /\
    pop_live_support et last (addr+k+32+LENGTH pre*type_memory_size et) right
Proof
  Induct_on `path`
  >- (simp[evaluate_subscripts_def, mem_path_offset_def, assign_subscripts_def,
        vyperValueOperationTheory.pop_element_def] >>
      rpt strip_tac >> gvs[FRONT_SNOC, GSYM SNOC_APPEND] >>
      drule (SRULE [GSYM SNOC_APPEND] pop_live_support_split) >>
      simp_tac bool_ss [AC ADD_ASSOC ADD_COMM]) >>
  rpt gen_tac >> strip_tac >>
  gvs[Once mem_path_offset_def, AllCaseEqs()] >>
  rename1 `mem_step_offset rt h = SOME (step0,step1)` >>
  rename1 `mem_path_offset step1 path = SOME tail` >> PairCases_on `tail` >> gvs[] >>
  `mem_path_offset rt [h] = SOME (step0,step1)` by simp[mem_path_offset_def] >>
  drule mem_path_offset_sound >> simp[subscripts_type_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all pop_assign_subscripts_cons_typed >> strip_tac >>
  `evaluate_subscripts step1 child path = INL (ArrayV (DynArrayV (pre ++ [last])))` by
    (drule evaluate_subscripts_cons_typed >>
     disch_then (qspecl_then [`path`, `root`] mp_tac) >> simp[] >> metis_tac[]) >>
  drule_all pop_step_support_extract >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `pop_live_support rt updated addr ((supp DIFF cs) UNION left)` by
    (irule pop_step_support_replace >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`(supp DIFF cs) UNION left`, `right`] >>
  FULL_SIMP_TAC bool_ss [ADD_ASSOC] >> ASM_SET_TAC []
QED
