(* Guarded preservation of a staged typed snapshot across an expression.
   The existing root boundary supplies the allocation, operand and local
   separation facts; only the typed subwindow is added here. *)
Theory bodyIntCallNRStageFrame
Ancestors
  bodyIntCallJointAggCore bodyIntCallJointContract valueEncodingProps freshWrites

Theorem intcall_guarded_snapshot_cont:
  intcall_expr_res fp ce env es sa s /\
  intcall_expr_cont fp ce env es sa s ee sb u /\
  FLOOKUP s.vs_allocas aid = SOME (b,k) /\ aid < sa.cs_next_id /\
  eval_operand buf s = SOME w /\ (!lbl. buf <> Label lbl) /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  (!n a z. local_region ce es.scopes s n a z ==>
           regions_disjoint b k a z) /\
  val_in_memory tv v (b+off) s.vs_memory /\ val_wf tv v /\
  off + type_memory_size tv <= k /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id ==>
  FLOOKUP u.vs_allocas aid = SOME (b,k) /\ aid < sb.cs_next_id /\
  eval_operand buf u = SOME w /\
  (!x. buf = Var x ==> not_fresh_at sb x) /\
  mem_bytes_at b k u.vs_memory = mem_bytes_at b k s.vs_memory /\
  val_in_memory tv v (b+off) u.vs_memory /\ val_wf tv v /\
  (!n a z. local_region ce ee.scopes u n a z ==>
           regions_disjoint b k a z)
Proof
  rpt gen_tac >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    fs[intcall_expr_cont_def, loweringPostsTheory.locals_kept_def] >>
  drule_all intcall_expr_cont_root >> strip_tac >>
  `mem_bytes_at (b+off) (type_memory_size tv) s.vs_memory =
   mem_bytes_at (b+off) (type_memory_size tv) u.vs_memory` by
    (irule mem_bytes_at_translated_window >>
     qexists_tac `k` >> simp[]) >>
  `val_in_memory tv v (b+off) u.vs_memory` by
    (irule val_in_memory_mem_agree >> conj_tac >- simp[] >>
     qexistsl_tac [`type_memory_size tv`, `s.vs_memory`] >> simp[]) >>
  simp[] >> metis_tac[not_fresh_at_mono]
QED
