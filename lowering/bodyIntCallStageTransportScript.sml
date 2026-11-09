(* Physical staging ownership survives the actual path of later staging. *)
Theory bodyIntCallStageTransport
Ancestors
  bodyIntCallStageOwned bodyIntCallValueWindow exprSimProps
  stmtSimAugAssignPlaceMemory

Theorem wb_frame_owned_value:
  wb_frame ce es sm s t /\
  FLOOKUP s.vs_allocas aid = SOME (off,sz) /\ aid < sm.cs_next_id /\
  (!n b lsz. local_region ce es.scopes s n b lsz ==>
    regions_disjoint off sz b lsz) /\
  val_in_memory tv v p s.vs_memory /\ val_wf tv v /\
  off <= p /\ p + type_memory_size tv <= off + sz ==>
  val_in_memory tv v p t.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory` by
    (gvs[loweringPostsTheory.wb_frame_def, compileEnvTheory.regions_disjoint_def] >>
     metis_tac[]) >>
  irule val_in_memory_window_agree >>
  conj_tac >- simp[] >>
  qexistsl_tac [`off`,`s.vs_memory`,`sz`] >> simp[] >>
  drule val_footprint_le >> decide_tac
QED

Theorem staged_arg_path_transport:
  staged_arg ce func es a sm s d /\
  gas_marked_path memory ctx func s n (OK t) /\
  wb_frame ce es sm s t /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id ==>
  staged_arg ce func es a sn t d
Proof
  PairCases_on `d` >> simp[staged_arg_def] >> strip_tac >>
  `!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
      lookup_var x t = SOME w` by gvs[loweringPostsTheory.wb_frame_def] >>
  `eval_operand d4 t = SOME w` by
    (irule aug_place_saved_operand >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  conj_tac >- metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  qexists_tac `w` >> simp[] >>
  Cases_on `d3` >> gvs[] >>
  `val_in_memory d1 d2 (w2n w) t.vs_memory` by
    (irule wb_frame_owned_value >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[arithmeticTheory.ADD_COMM] >>
     metis_tac[]) >>
  `!n b lsz. local_region ce es.scopes t n b lsz ==>
      regions_disjoint off sz b lsz` by
    (rpt strip_tac >> rename1 `local_region ce es.scopes t nm b lsz` >>
     first_x_assum irule >> qexists_tac `nm` >>
     irule local_region_frame >> conj_tac
     >- (qexists_tac `func` >>
         gvs[exprLoweringPropsTheory.stmt_state_rel_def,
             compileEnvTheory.state_rel_def]) >>
     qexistsl_tac [`sm`,`es.scopes`,`t`] >> simp[]) >>
  simp[] >> qexistsl_tac [`inst.inst_id`,`off`,`sz`] >>
  gvs[loweringPostsTheory.wb_frame_def] >> metis_tac[]
QED

Theorem staged_args_path_transport:
  EVERY (staged_arg ce func es a sm s) ds /\
  gas_marked_path memory ctx func s n (OK t) /\
  wb_frame ce es sm s t /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s /\
  sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id ==>
  EVERY (staged_arg ce func es a sn t) ds
Proof
  simp[listTheory.EVERY_MEM] >> metis_tac[staged_arg_path_transport]
QED
