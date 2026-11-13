(* Composition depends on local-region identity, not total variable equality. *)
Theory bodyPtrHashBuiltinsGhostCompose
Ancestors bodyPtrDefs exprSimProps loweringPosts arithmetic

Theorem hash_ghost_kept_compose:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  ghost_kept cenv ee sm G tn s Gf tf /\
  (!z. not_fresh_at sa z ==> not_fresh_at sm z) /\
  sa.cs_next_id <= sm.cs_next_id /\
  (!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
    FLOOKUP s.vs_allocas aid = SOME entry) /\
  (!n b sz. local_region cenv ee.scopes s n b sz <=>
    local_region cenv es.scopes s0 n b sz) ==>
  ghost_kept cenv es sa G0 tn0 s0 Gf tf
Proof
  strip_tac >> gvs[ghost_kept_def] >> conj_tac
  >- (rpt strip_tac >>
      `aid < sm.cs_next_id` by decide_tac >>
      `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      qpat_assum `!aid off sz i. FLOOKUP _ aid = _ /\ _ ==> i IN tn.t_mem`
        drule_all >> strip_tac >>
      qpat_assum `!aid off sz i. FLOOKUP _ aid = _ /\ _ ==> i IN tn0.t_mem`
        drule_all >> simp[]) >>
  rpt strip_tac >>
  qpat_assum `!n b sz i. local_region _ _ _ n b sz /\ _ ==> i IN tn.t_mem`
    drule_all >> strip_tac >>
  qpat_assum `!n b sz i. local_region _ _ _ n b sz /\ _ ==> i IN tn0.t_mem`
    drule_all >> simp[]
QED

Theorem hash_expr_post_local_regions:
  expr_post ctx fn cenv cx e es sa sm s0 ee v x s /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes ==>
  !n b sz. local_region cenv ee.scopes s n b sz <=>
    local_region cenv es.scopes s0 n b sz
Proof
  simp[expr_post_def] >> rpt strip_tac >> eq_tac
  >- (strip_tac >> irule local_region_frame >> metis_tac[]) >>
  strip_tac >> irule local_region_frame_fwd >> metis_tac[]
QED

Theorem hash_expr_post_ghost_kept_compose:
  expr_post ctx fn cenv cx e es sa sm s0 ee v x s /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (!z. not_fresh_at sa z ==> not_fresh_at sm z) /\
  sa.cs_next_id <= sm.cs_next_id /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  ghost_kept cenv ee sm G tn s Gf tf ==>
  ghost_kept cenv es sa G0 tn0 s0 Gf tf
Proof
  strip_tac >> drule_all hash_expr_post_local_regions >> strip_tac >>
  irule hash_ghost_kept_compose >>
  first_assum (irule_at (Pat `ghost_kept _ _ sa _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `ghost_kept _ _ sm _ _ _ _ _`)) >>
  simp[] >> fs[expr_post_def]
QED
