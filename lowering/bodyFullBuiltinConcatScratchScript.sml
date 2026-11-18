(* Old nonlocal Concat scratch survives an effectful child evaluation. *)
Theory bodyFullBuiltinConcatScratch
Ancestors
  bodyPtrDefs loweringPosts finite_map pred_set

Theorem concat_scratch_child_frame:
  expr_post H ctx func cenv cx e es sa sb s ee v op t /\
  ghost_kept_at lo cenv es sa G tn s G' tn' /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
    b+sz <= lb \/ lb+lsz <= b) ==>
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
  mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory /\
  (!i. b <= i /\ i < b+sz /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
  (!z. not_fresh_at sa z ==> FLOOKUP G' z = FLOOKUP G z /\
    op_taint tn' (Var z) = op_taint tn (Var z)) /\
  (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==>
    lookup_var z t = SOME w)
Proof
  rewrite_tac[expr_post_def, ghost_kept_at_def] >> strip_tac >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (first_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
    qexists `aid` >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!aid off sz i. _` (qspecl_then [`aid`,`b`,`sz`,`i`] mp_tac) >>
    simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  simp[]
QED
