Theory bodyIntCallBufferHeadFrameMods
Ancestors
  freshWrites loweringPosts loweringStateRelDefs vyperState
  vyperEvalScopesProgress vyperEvalPreservesScopes arithmetic

Theorem wb_frame_stage_trans:
  wb_frame cenv es0 es1 sa s0 s /\ wb_frame cenv es1 es2 si s u /\
  sa.cs_next_id <= si.cs_next_id /\ sa.cs_next_var <= si.cs_next_var /\
  (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
            local_region cenv es1.scopes s n b sz) ==>
  wb_frame cenv es0 es2 sa s0 u
Proof
  rewrite_tac[wb_frame_def] >> strip_tac >>
  conj_tac >- (
    rpt strip_tac >>
    `not_fresh_at si x` by (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
    `lookup_var x s = SOME w` by simp[] >> simp[]) >>
  conj_tac >- (
    rpt strip_tac >> `FLOOKUP s.vs_allocas aid = SOME b` by simp[] >> simp[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    `aid < si.cs_next_id` by decide_tac >>
    `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by simp[] >>
    `!n b sz'. local_region cenv es1.scopes s n b sz' ==>
               off + sz <= b \/ b + sz' <= off` by
      (rpt gen_tac >> disch_tac >>
       qpat_assum `!n b sz'. local_region _ es0.scopes s0 n b sz' ==> _`
         (qspecl_then [`n`,`b`,`sz'`] mp_tac) >>
       qpat_assum `!n b sz'. local_region _ es0.scopes s0 n b sz' <=> _`
         (qspecl_then [`n`,`b`,`sz'`] mp_tac) >> simp[]) >>
    `mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory` by
      (qpat_assum `!j p k. FLOOKUP s0.vs_allocas j = _ /\ _ ==> _`
         (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
       impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
       DISCH_THEN ACCEPT_TAC) >>
    qpat_assum `!j p k. FLOOKUP s.vs_allocas j = _ /\ _ ==> _`
      (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  fs[locals_kept_def] >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[scopes_progress_trans]
  >- (rpt strip_tac >>
      `?e e1. lookup_scopes n es0.scopes = SOME e /\
              lookup_scopes n es1.scopes = SOME e1` by
        (gvs[local_region_def] >>
         metis_tac[lookup_scopes_none_map_fdom,optionTheory.NOT_SOME_NONE,
                   optionTheory.option_CASES]) >>
      `e1 = e` by
        (qpat_assum `scopes_progress es0.scopes _`
           (qspecl_then [`n`,`e`,`e1`] mp_tac o REWRITE_RULE[scopes_progress_def]) >>
         qpat_assum `scopes_progress es1.scopes _`
           (qspecl_then [`n`,`e1`,`e`] mp_tac o REWRITE_RULE[scopes_progress_def]) >>
         gvs[] >> rw[] >> gvs[]) >>
      gvs[] >> metis_tac[]) >>
  fs[popped_kept_def] >> rpt strip_tac >>
  qpat_assum `!n b sz entry' h. local_region _ es1.scopes _ _ _ _ /\ _ ==> _`
    irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `n` >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!n b sz entry' h. _ /\ lookup_scopes n es1.scopes = SOME entry' /\ _ ==>
                      snapshot_in _ b sz h s.vs_memory`
        irule >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists `n` >> fs[])
  >- simp[] >>
  metis_tac[]
QED
