(* Previously allocated temporary values survive later target evaluation. *)
Theory allocaPtrValueFrame
Ancestors
  logValueFramePtr bodyPtrDefs loweringPosts valueEncodingProofs
  venomState ptrDiscipline compileEnv arithmetic

Theorem alloca_ptr_val_frame:
  ptr_val_ok cx ty v (Var p) G tn s /\ ~is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  eval_operand (Var p) s = SOME w /\ not_fresh_at sa p /\
  wb_frame cenv es es' sa s t /\ ghost_kept cenv es sa G tn s H un /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
  (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz ==>
  ptr_val_ok cx ty v (Var p) H un t
Proof
  rpt strip_tac >>
  `lookup_var p s = SOME w /\ lookup_var p t = SOME w` by
    fs[wb_frame_def, eval_operand_def] >>
  `FLOOKUP H p = FLOOKUP G p /\
   op_taint un (Var p) = op_taint tn (Var p)` by
    fs[ghost_kept_def] >>
  `mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (fs[wb_frame_def] >> metis_tac[]) >>
  `mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory` by
    (drule mem_bytes_at_agree_window >> strip_tac >> metis_tac[]) >>
  `!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\
       i IN un.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     qpat_x_assum `ghost_kept _ _ _ _ _ _ _ _` mp_tac >>
     simp[ghost_kept_def] >> strip_tac >>
     qpat_x_assum `!aid off sz i. FLOOKUP _ aid = _ /\ _ ==> _` irule >>
     simp[] >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> metis_tac[]) >>
  irule ptr_val_ok_footprint_frame >>
  qexistsl_tac [`G`, `s`, `tn`] >> simp[eval_operand_def]
QED
