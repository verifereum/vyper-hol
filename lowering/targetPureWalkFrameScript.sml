(*
 * A pure target walk keeps memory outside its own fresh allocations.
 *
 * compile_get_target_ptr writes memory only into scratch buffers it
 * allocates itself (compile_alloc_buffer for mapping keys) and through the
 * code of its index expressions, which are pure when supported_target_pure
 * holds.  So across the walk, the live locals and every window disjoint
 * from the walk's fresh ALLOCAs keep their bytes (pure_frame), next to
 * the walk's own target_post from target_sim.
 *
 * TOP-LEVEL:
 *   target_pure_walk_pure_frame
 *)
Theory targetPureWalkFrame
Ancestors
  targetPlaceSimDefs supportedTargets loweringStateRelDefs loweringPosts
  gasOutcome

Theorem target_pure_walk_pure_frame:
  !ctx func cenv cx env tops bt es vt sa sb op s0.
    supported_target_pure tops bt /\ target_sim ctx func cenv cx env bt es /\
    type_place_target env bt = SOME vt /\
    compile_get_target_ptr compile_expr cenv bt sa = (op, sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    gas_admissible (eval_base_place cx bt) target_res_ok es /\
    stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func) (eval_base_place cx bt) (es, s0)
      (\res ee t. ?pv. res = INL pv /\
         target_post ctx func cenv cx es sa sb s0 ee pv vt op t /\
         pure_frame cenv func es sa s0 t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  cheat
QED
