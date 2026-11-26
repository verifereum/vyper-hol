(* Compose anchored Concat frames using their local-region agreement. *)
Theory bodyConcatRegionFrameMods
Ancestors
  bodyConcatCutsMods wordArgsPtr freshWrites loweringPosts
  loweringStateRelDefs vyperState vyperEvalScopesProgress vyperEvalPreservesScopes arithmetic

Theorem concat_locals_kept_trans[local]:
  (!n b sz. local_region cenv es.scopes s n b sz ==>
            local_region cenv ee.scopes t n b sz) /\
  locals_kept cenv es ee s t /\ locals_kept cenv ee ef t u ==>
  locals_kept cenv es ef s u
Proof
  strip_tac >> fs[locals_kept_def] >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[scopes_progress_trans]
  >- (rpt strip_tac >>
      `?e e1. lookup_scopes n es.scopes = SOME e /\
              lookup_scopes n ee.scopes = SOME e1` by
        (gvs[local_region_def] >>
         metis_tac[lookup_scopes_none_map_fdom,optionTheory.NOT_SOME_NONE,
                   optionTheory.option_CASES]) >>
      `e1 = e` by
        (qpat_x_assum `scopes_progress es.scopes _`
           (qspecl_then [`n`,`e`,`e1`] mp_tac o REWRITE_RULE[scopes_progress_def]) >>
         qpat_x_assum `scopes_progress ee.scopes _`
           (qspecl_then [`n`,`e1`,`e`] mp_tac o REWRITE_RULE[scopes_progress_def]) >>
         gvs[] >> rw[] >> gvs[]) >>
      gvs[] >> metis_tac[]) >>
  fs[popped_kept_def] >> rpt strip_tac >>
  qpat_x_assum `!n b sz entry' h. local_region _ ee.scopes _ _ _ _ /\ _ ==> _`
    irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `n` >> rpt conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!n b sz entry' h. local_region _ es.scopes _ _ _ _ /\ _ ==> _`
        irule >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists `n` >> fs[])
  >- simp[] >>
  metis_tac[]
QED

Theorem concat_old_frame_compose_regions_mods:
  concat_old_frame_mods (func,cenv,lo,pure) scratch
    (es,sa,s,G,tn) (ee,sb,t,G1,tn1) /\
  concat_old_frame_mods (func,cenv,lo,pure) scratch
    (ee,sb,t,G1,tn1) (ef,sc,u,G2,tn2) ==>
  concat_old_frame_mods (func,cenv,lo,pure) scratch
    (es,sa,s,G,tn) (ef,sc,u,G2,tn2)
Proof
  PairCases_on `scratch` >> pure_rewrite_tac[concat_old_frame_mods_def] >> strip_tac >>
  conj_tac >- (irule LESS_EQ_TRANS >> qexists `sb.cs_next_var` >> simp[]) >>
  conj_tac >- (irule LESS_EQ_TRANS >> qexists `sb.cs_next_id` >> simp[]) >>
  conj_tac >- (irule LESS_EQ_TRANS >> qexists `t.vs_alloca_next` >> simp[]) >>
  conj_tac >- (drule_all wordArgsPtrTheory.ghost_kept_at_trans >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sb z` by (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
      simp[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `aid < sb.cs_next_id` by decide_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (p,n)` by simp[] >>
      `mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory` by
        (qpat_assum `!aid p n. _ ==> mem_bytes_at p n t.vs_memory = _`
           (qspecl_then [`aid`,`p`,`n`] MATCH_MP_TAC) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `mem_bytes_at p n u.vs_memory = mem_bytes_at p n t.vs_memory` by
        (qpat_assum `!aid p n. _ ==> mem_bytes_at p n u.vs_memory = _`
           (qspecl_then [`aid`,`p`,`n`] MATCH_MP_TAC) >>
         asm_simp_tac bool_ss [] >> first_assum ACCEPT_TAC) >>
      asm_rewrite_tac[]) >>
  conj_tac
  >- (irule concat_locals_kept_trans >> qexistsl_tac [`ee`,`t`] >> simp[]) >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> metis_tac[]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `pure ==> _ /\ !p n. _ ==> mem_bytes_at p n t.vs_memory = _`
    (drule_then (assume_tac o CONJUNCT2)) >>
  qpat_assum `pure ==> _ /\ !p n. _ ==> mem_bytes_at p n u.vs_memory = _`
    (drule_then (assume_tac o CONJUNCT2)) >>
  `mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t.vs_memory = _`
       (qspecl_then [`p`,`n`] MATCH_MP_TAC) >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint p n b sz`
       (qspecl_then [`inst`,`b`,`sz`] MATCH_MP_TAC) >> simp[]) >>
  `mem_bytes_at p n u.vs_memory = mem_bytes_at p n t.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n u.vs_memory = _`
       (qspecl_then [`p`,`n`] MATCH_MP_TAC) >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint p n b sz`
       (qspecl_then [`inst`,`b`,`sz`] MATCH_MP_TAC) >> simp[] >> decide_tac) >>
  asm_rewrite_tac[]
QED
