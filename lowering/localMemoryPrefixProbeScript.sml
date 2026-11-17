(* Restore the statement's initial allocation obligations after the store. *)
Theory localMemoryPrefixProbe
Ancestors
  bodySimFull stmtSimDefs bodyPtrDefs loweringPosts exprLoweringProps
  loweringStateRelDefs compileEnv venomState vyperState finite_map list

Theorem rhs_target_store_allocation_posts:
  vv_post H ctx func cenv cx e es sa sm s0 mid raw vv u /\
  target_post H ctx func cenv cx mid sm st u ee pv vt r z /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv mid sm G1 tn1 u G2 tn2 /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= st.cs_next_id /\
  alloca_frame cenv ee st z cenv ff t /\
  (!aid off sz i.
    FLOOKUP z.vs_allocas aid = SOME (off,sz) /\ aid < st.cs_next_id /\
    (!n b sz'. local_region cenv ee.scopes z n b sz' ==>
      off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn2.t_mem) ==>
  alloca_frame cenv es sa s0 cenv ff t /\
  (!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
      off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz /\ i IN tf.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes /\
   MAP FDOM ee.scopes = MAP FDOM mid.scopes` by
    fs[vv_post_def,target_post_def,locals_kept_def] >>
  `stmt_state_rel H ctx func cenv cx mid u` by fs[vv_post_def] >>
  `alloca_frame cenv es sa s0 cenv mid u` by
    (drule_all vv_post_alloca_frame >> simp[]) >>
  `alloca_frame cenv mid sm u cenv ee z` by
    (drule_all target_post_alloca_frame >> simp[]) >>
  `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
    FLOOKUP u.vs_allocas aid = SOME ent` by fs[vv_post_def] >>
  `!aid ent. FLOOKUP u.vs_allocas aid = SOME ent ==>
    FLOOKUP z.vs_allocas aid = SOME ent` by fs[target_post_def] >>
  `!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
    FLOOKUP z.vs_allocas aid = SOME ent` by metis_tac[] >>
  `sa.cs_next_id <= st.cs_next_id` by decide_tac >>
  `alloca_frame cenv es sa s0 cenv ee z` by
    (irule alloca_frame_trans >> qexistsl_tac [`cenv`,`mid`,`u`,`sm`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_frame cenv es sa s0 cenv ff t` by
    (irule alloca_frame_trans >> qexistsl_tac [`cenv`,`ee`,`z`,`st`] >>
     simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1`
    (assume_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ghost_kept_at_def]) >>
  qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 u G2 tn2`
    (assume_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [ghost_kept_at_def]) >>
  `!aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
      off+sz <= b \/ b+sz' <= off) /\
    off <= i /\ i < off+sz /\ i IN tn2.t_mem ==> i IN tn0.t_mem` by
    (MATCH_MP_TAC (Q.INST [`c0` |-> `cenv`,`e0` |-> `es`,
       `sa0` |-> `sa`,`s0` |-> `s0`,`c1` |-> `cenv`,`e1` |-> `mid`,
       `s1` |-> `u`,`sa1` |-> `sm`,`tn0` |-> `tn0`,
       `tn1` |-> `tn1`,`tn2` |-> `tn2`] alloca_taint_kept_trans) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  MATCH_MP_TAC (Q.INST [`c0` |-> `cenv`,`e0` |-> `es`,
    `sa0` |-> `sa`,`s0` |-> `s0`,`c1` |-> `cenv`,`e1` |-> `ee`,
    `s1` |-> `z`,`sa1` |-> `st`,`tn0` |-> `tn0`,
    `tn1` |-> `tn2`,`tn2` |-> `tf`] alloca_taint_kept_trans) >>
  simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
