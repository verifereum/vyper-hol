(* A captured value remains in its own allocation while the index executes. *)
Theory bodyIntCallPostProvenanceCapturedFrame
Ancestors
  exprSimAbiEncodeArgsMaterializePath bodyIntCallValueWindow exprSimProps
  loweringPosts exprLoweringProps loweringStateRelDefs venomState finite_map
  valueEncodingProps words

Theorem intcall_captured_index_frame:
  materialize_owned_post ctx func ce cx obj es sa sm sb s0 mid v dst tv s /\
  expr_post ctx func ce cx idx mid sb sc s ee iv iop t /\
  val_wf tv v /\ local_ptrs_reserved ce sb /\
  (!x. dst = Var x ==> not_fresh_at sb x) /\ (!l. dst <> Label l) ==>
  ?w. eval_operand dst t = SOME w /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    val_in_memory tv v (w2n w) t.vs_memory /\
    (!name b len. local_region ce ee.scopes t name b len ==>
      w2n w + type_memory_size tv <= b \/ b + len <= w2n w)
Proof
  strip_tac >>
  qpat_x_assum `materialize_owned_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[materialize_owned_post_def] >> strip_tac >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_post_def] >> strip_tac >>
  `eval_operand dst t = SOME w` by
    (Cases_on `dst` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,type_memory_size tv)` by metis_tac[] >>
  `mem_bytes_at (w2n w) (type_memory_size tv) t.vs_memory =
   mem_bytes_at (w2n w) (type_memory_size tv) s.vs_memory` by metis_tac[] >>
  qexists_tac `w` >> simp[] >> conj_tac
  >- (`val_footprint tv v <= type_memory_size tv` by metis_tac[val_footprint_le] >>
      irule val_in_memory_window_agree >>
      conj_tac >- simp[] >>
      qexistsl_tac [`w2n w`, `s.vs_memory`, `type_memory_size tv`] >> simp[]) >>
  rpt strip_tac >>
  `local_region ce mid.scopes s name b len` by
    (irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >>
       qpat_x_assum `stmt_state_rel _ _ _ _ _ s` mp_tac >>
       simp[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sb`, `ee.scopes`, `t`] >> simp[] >>
     gvs[locals_kept_def]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
