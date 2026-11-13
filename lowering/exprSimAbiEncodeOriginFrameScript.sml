Theory exprSimAbiEncodeOriginFrame
Ancestors
  exprSimAbiEncodeNonwordCounted exprBopSimProps exprSimProps
  loweringPosts compileEnv venomMemDefs freshWrites

Theorem abi_encode_nonword_origin_frame:
  expr_post ctx func ce cx e es origin sa s0 es' v op s /\
  local_ptrs_reserved ce origin /\
  origin.cs_next_var <= sa.cs_next_var /\
  origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x actual = SOME w) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==>
    FLOOKUP actual.vs_allocas aid = SOME row) /\
  (!aid off sz. FLOOKUP s.vs_allocas aid = SOME(off,sz) /\ aid < sa.cs_next_id ==>
    mem_bytes_at off sz actual.vs_memory = mem_bytes_at off sz s.vs_memory) /\
  (!name b n. local_region ce es'.scopes s name b n ==>
    mem_bytes_at b n actual.vs_memory = mem_bytes_at b n s.vs_memory) ==>
  wb_frame ce es es' origin s0 actual
Proof
  simp_tac bool_ss [expr_post_def] >> strip_tac >>
  `locals_kept ce es' es' s actual` by
    (irule locals_kept_regions >> first_assum ACCEPT_TAC) >>
  simp_tac bool_ss [wb_frame_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sa x` by
        (irule not_fresh_at_mono >> qexists `origin` >> asm_rewrite_tac[]) >>
      metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME(off,sz)` by metis_tac[] >>
      `aid < sa.cs_next_id` by decide_tac >>
      metis_tac[]) >>
  irule locals_kept_trans >>
  qexistsl [`es'`, `origin`, `s`] >> asm_rewrite_tac[]
QED
