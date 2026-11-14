(* The RHS and suffix frames give the counted statement boundary. *)
Theory immutableAssignMemPost
Ancestors
  bodyMemoryDefs bodyMemAggregatePath fragGasPathFrameMem fragGasMode
  stmtSimDefs loweringPosts exprLoweringProps loweringShapeDefs venomState
  loweringStateRelDefs arithmetic

Theorem immutable_assign_mem_entry_post:
  expr_post ctx func ce cx e es sa su s0 ee v op u /\
  stmt_post ctx func cx lctx ce ce su sb ee u (INL ()) fin t /\
  sa.cs_next_var <= su.cs_next_var /\ sa.cs_next_var <= sb.cs_next_var /\
  return_buf_frame d ce sa s0 /\ alloca_history func u /\
  fn_inst_ids_distinct func /\ gas_marked_path T ctx func u 0 (OK t) /\
  s0.vs_alloca_next <= t.vs_alloca_next ==>
  stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\ ~block_is_terminated sb /\
  cenv_top_ext ce ce fin.scopes /\ stmt_state_rel ctx func ce cx fin t /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
     lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
     FLOOKUP t.vs_allocas aid = SOME b) /\
  return_buf_frame d ce sb t /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
     lookup_var x t = SOME w` by
    (fs[expr_post_def, stmt_post_def] >>
     metis_tac[not_fresh_at_mono]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
     FLOOKUP t.vs_allocas aid = SOME b` by
    (fs[expr_post_def, stmt_post_def] >> metis_tac[]) >>
  `return_buf_frame d ce sb t` by
    (mp_tac (Q.SPECL [`d`, `ce`, `ce`, `sa`, `sb`, `s0`, `t`]
       return_buf_frame_frame) >> simp[]) >>
  `alloca_inv u` by fs[expr_post_def, stmt_state_rel_def] >>
  `gas_path_mem ctx func u 0 (OK t)` by fs[gas_marked_path_def] >>
  `!z. gas_path_mem ctx func u 0 (OK z) ==> alloca_inv z` by
    metis_tac[aggregate_mem_path_alloca_inv] >>
  `alloca_history func t` by
    metis_tac[gas_path_mem_zero_history] >>
  fs[stmt_post_def]
QED
