Theory exprSimAbiEncodeStagedFrame
Ancestors
  exprSimAbiEncodeStagedObserver exprBopSimProps exprSimProps freshWrites
  loweringPosts compileEnv vyperState

Theorem abi_encode_staged_origin_frame:
  abi_encode_staged_observation ctx func ce cx es' st out mid outsz p at av s actual /\
  wb_frame ce es origin s0 s /\ local_ptrs_reserved ce origin /\
  origin.cs_next_var <= st.cs_next_var /\ origin.cs_next_id <= st.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  wb_frame ce es origin s0 actual
Proof
  simp_tac bool_ss [abi_encode_staged_observation_def, wb_frame_def] >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> metis_tac[not_fresh_at_mono]) >>
  reverse conj_tac
  >- (irule locals_kept_regions_tail >> qexists `s` >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt strip_tac >> rename1 `local_region _ _ _ nm lb lsz` >>
      qpat_x_assum `!name b n. local_region _ _ _ name b n ==> _` irule >>
      qexists `nm` >> irule local_region_frame_fwd >>
      qexistsl [`s0`, `origin`, `es.scopes`] >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
  `aid < st.cs_next_id` by decide_tac >>
  metis_tac[]
QED
