(* Frames relative to an earlier allocation cut through scratch-writing phases. *)
Theory protectedAllocationFrame
Ancestors
  exprSimWordArgs exprBopSimProps exprSimProps loweringPosts exprLoweringProps
  localPtrsProps compileEnv venomState finite_map list arithmetic loweringStateRelDefs

Theorem protected_allocation_frame_tail:
  wb_frame cenv es ee sa s0 t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_id <= sc.cs_next_id /\
  (!x w. not_fresh_at sa x /\ lookup_var x t = SOME w ==>
         lookup_var x u = SOME w) /\
  (!aid a. FLOOKUP t.vs_allocas aid = SOME a ==>
           FLOOKUP u.vs_allocas aid = SOME a) /\
  locals_kept cenv ee es' t u /\
  (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
             aid < sa.cs_next_id ==> H p n) /\
  (!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\
     aid < sc.cs_next_id /\ H p n /\
     (!name lo sz. local_region cenv ee.scopes t name lo sz ==>
                   p+n <= lo \/ lo+sz <= p) ==>
     mem_bytes_at p n u.vs_memory = mem_bytes_at p n t.vs_memory) ==>
  wb_frame cenv es es' sa s0 u
Proof
  strip_tac >>
  `locals_kept cenv es es' s0 u` by
    (irule locals_kept_trans >> qexistsl_tac [`ee`, `sa`, `t`] >>
     fs[wb_frame_def]) >>
  fs[wb_frame_def] >> rpt strip_tac >>
  `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
  `H off sz` by metis_tac[] >>
  `aid < sc.cs_next_id` by decide_tac >>
  `!name lo len. local_region cenv ee.scopes t name lo len ==>
                off+sz <= lo \/ lo+len <= off` by
    (rpt strip_tac >>
     qpat_x_assum `!n b sz'. local_region cenv es.scopes s0 _ _ _ ==> _` irule >>
     qexists_tac `name` >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `ee.scopes`, `t`] >> simp[]) >>
  `mem_bytes_at off sz u.vs_memory = mem_bytes_at off sz t.vs_memory` by
    (qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = _ /\ _ ==> _` irule >>
     simp[Once arithmeticTheory.ADD_COMM] >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `aid` >> simp[]) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _` irule >>
  conj_tac >- first_assum ACCEPT_TAC >> qexists_tac `aid` >> simp[]
QED
