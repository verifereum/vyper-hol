(* Owned return buffers survive effectful target evaluation.  The local
   separation premise is deliberately relative to the target's input scopes. *)
Theory placeRelayoutSource
Ancestors
  loweringPosts exprSimProps exprBopSimProps valueEncodingProofs valueEncoding valueEncodingDefs

Theorem target_post_owned_source:
  target_post ctx func cenv cx es sa sb s0 es' pv vt r s /\
  expr_val_own cenv cx ty own_start own_end es v op s0 /\
  own_end.cs_next_id <= sa.cs_next_id /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  val_wf tv v /\ val_in_memory tv v (w2n w) s0.vs_memory /\
  eval_operand op s0 = SOME w /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  (!l. op <> Label l) ==>
  eval_operand op s = SOME w /\
  expr_val_rel cx ty v op s /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
       own_start.cs_next_id <= aid /\ aid < own_end.cs_next_id /\
       b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
       mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory) \/
   val_footprint tv v = 0)
Proof
  strip_tac >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[target_post_def] >> strip_tac >>
  `eval_operand op s = SOME w` by
    (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sa`, `s0`] >> simp[]) >>
  qpat_x_assum `expr_val_own _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_own_def] >> strip_tac >> gvs[] >>
  `mem_bytes_at (w2n w) (val_footprint tv v) s0.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory` by
    (Cases_on `val_footprint tv v = 0` >- simp[mem_bytes_at_def] >>
     gvs[] >>
     `mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory` by
       (first_x_assum irule >> conj_tac >- metis_tac[] >>
        qexists_tac `aid` >> simp[] >> decide_tac) >>
     drule mem_bytes_at_agree_window >> strip_tac >>
     first_x_assum irule >> simp[]) >>
  `val_in_memory tv v (w2n w) s.vs_memory` by
    (irule val_in_memory_footprint_agree >> simp[] >>
     qexists_tac `s0.vs_memory` >> simp[mem_bytes_at_def]) >>
  simp[expr_val_rel_def] >>
  disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
  first_x_assum irule >> conj_tac >- metis_tac[] >>
  qexists_tac `aid` >> simp[] >> decide_tac
QED
