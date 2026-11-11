(* Ghost frames compose when allocations and local regions survive. *)
Theory logGhostFramePtr
Ancestors
  bodyPtrDefs stmtSimLogArgs loweringPosts compileEnv loweringStateRelDefs
  venomState finite_map list arithmetic

Theorem ghost_kept_refl:
  ghost_kept cenv es sa G tn s G tn
Proof
  simp[ghost_kept_def]
QED

Theorem ghost_kept_trans:
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sm G1 tn1 s1 G2 tn2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s1.vs_allocas aid = SOME b) /\
  (!n b sz. local_region cenv es1.scopes s1 n b sz <=>
            local_region cenv es.scopes s0 n b sz) ==>
  ghost_kept cenv es sa G0 tn0 s0 G2 tn2
Proof
  simp[ghost_kept_def] >> rpt strip_tac
  >- ( `not_fresh_at sm x` by (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[])
  >- ( `not_fresh_at sm x` by (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[])
  >- (`i IN tn1.t_mem` suffices_by metis_tac[] >>
      qpat_x_assum `!aid off sz i. FLOOKUP s1.vs_allocas aid = _ /\ _ ==> _` irule >>
      conj_tac >- (qexistsl_tac [`aid`,`off`,`sz`] >> simp[] >> metis_tac[]) >> simp[])
  >> `i IN tn1.t_mem` suffices_by metis_tac[] >>
  qpat_x_assum `!n b sz i. local_region cenv es1.scopes s1 n b sz /\ _ ==> _` irule >>
  conj_tac >- simp[] >> qexistsl_tac [`b`,`n`,`sz`] >> simp[] >> metis_tac[]
QED

Theorem ghost_kept_wb_trans:
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sm G1 tn1 s1 G2 tn2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\ wb_frame cenv es es' sa s0 s1 ==>
  ghost_kept cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >> irule ghost_kept_trans >>
  qexistsl_tac [`G1`,`es1`,`s1`,`sm`,`tn1`] >> simp[] >>
  reverse conj_tac >- (gvs[wb_frame_def] >> metis_tac[]) >>
  rpt gen_tac >> irule log_frame_local_region >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
