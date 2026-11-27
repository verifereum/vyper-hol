(* Compose the statement-entry and packed-cut frames across a Log topic. *)
Theory bodyLogTopicAnchorFramesMods
Ancestors
  bodyPtrDefs loweringPosts exprBopSimProps exprSimProps freshWrites
  arithmetic finite_map

val _ = Parse.hide "base";

Theorem log_topic_anchor_frames_mods:
  local_ptrs_reserved ce base /\ MAP FDOM mid.scopes = MAP FDOM es.scopes /\
  base.cs_next_var <= a.cs_next_var /\ base.cs_next_id <= a.cs_next_id /\
  wb_frame ce es mid base s0 u /\
  ghost_kept_at lo ce es base G0 tn0 s0 Gu tu /\
  wb_frame ce mid mid a u z /\ ghost_kept_at lo ce mid a Gu tu u Gz tz /\
  (!aid off sz. aid < a.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (off,sz) ==>
     mem_bytes_at off sz z.vs_memory = mem_bytes_at off sz u.vs_memory /\
     (!i. off <= i /\ i < off+sz /\ i IN tz.t_mem ==> i IN tu.t_mem)) ==>
  wb_frame ce es mid base s0 z /\ ghost_kept_at lo ce es base G0 tn0 s0 Gz tz
Proof
  pure_rewrite_tac[wb_frame_def, ghost_kept_at_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. not_fresh_at base x ==> not_fresh_at a x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!aid off sz. aid < base.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (off,sz) ==>
     mem_bytes_at off sz z.vs_memory = mem_bytes_at off sz u.vs_memory /\
     (!i. off <= i /\ i < off+sz /\ i IN tz.t_mem ==> i IN tu.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     `aid < a.cs_next_id` by metis_tac[LESS_LESS_EQ_TRANS] >>
     `FLOOKUP u.vs_allocas aid = SOME (off,sz)` by simp[] >>
     qpat_assum `!aid off sz. aid < a.cs_next_id /\ _ ==> _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[]) >>
  rpt conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at a x` by simp[] >>
      `lookup_var x u = SOME w` by simp[] >> simp[])
  >- (rpt strip_tac >>
      `FLOOKUP u.vs_allocas aid = SOME b` by simp[] >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz s0.vs_memory` by
        (qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz u.vs_memory = _`
           (qspecl_then [`aid`,`off`,`sz`] MATCH_MP_TAC) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      qpat_assum `!aid off sz. aid < base.cs_next_id /\ _ ==> _`
        (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[])
  >- (irule locals_kept_trans >> qexistsl [`mid`,`base`,`u`] >> simp[])
  >- (rpt gen_tac >> strip_tac >> `not_fresh_at a x` by simp[] >> simp[])
  >- (rpt gen_tac >> strip_tac >>
      `i IN tu.t_mem` by
        (qpat_assum `!aid off sz. aid < base.cs_next_id /\ _ ==> _`
           (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[]) >>
      qpat_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
        (qspecl_then [`aid`,`off`,`sz`,`i`] MATCH_MP_TAC) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >> rpt gen_tac >> strip_tac >>
  `local_region ce mid.scopes u n b sz` by
    (irule local_region_frame_fwd >> qexistsl [`s0`,`base`,`es.scopes`] >> simp[]) >>
  `i IN tu.t_mem` by
    (qpat_assum `!n b sz i. local_region ce mid.scopes u n b sz /\ _ ==> _`
       (qspecl_then [`n`,`b`,`sz`,`i`] MATCH_MP_TAC) >> simp[]) >>
  qpat_assum `!n b sz i. local_region ce es.scopes s0 n b sz /\ _ ==> _`
    (qspecl_then [`n`,`b`,`sz`,`i`] MATCH_MP_TAC) >> simp[]
QED
