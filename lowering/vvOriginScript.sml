(* Value-location origins weaken when the compiler allocation cursor grows. *)
Theory vvOrigin
Ancestors
  loweringPosts context compileEnv arithmetic finite_map

Theorem vv_at_start_mono:
  sa.cs_next_id <= sm.cs_next_id /\
  vv_at cenv cx ty sm sb es tv vv u ==>
  vv_at cenv cx ty sa sb es tv vv u
Proof
  Cases_on `vv` >> simp[vv_at_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP u.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
        first_assum ACCEPT_TAC)
  >>~- ([`local_region cenv es.scopes u n b sz`],
        disj2_tac >> disj1_tac >> qexistsl [`n`, `b`, `sz`] >> simp[])
  >> metis_tac[]
QED
