(*
 * A pure target walk keeps an earlier value's post.
 *
 * Assign evaluates its RHS e first and computes the target's pointer
 * after (eval_stmt, compile_stmt).  When the target's indices are pure
 * (supported_target_pure: no internal calls, no pop()), the walk
 * (eval_base_place, compile_get_target_ptr) changes the source state only
 * in its gas observations, and its code writes neither the memory of the
 * live locals and earlier allocations nor storage, transient storage,
 * immutables, accounts or code.  So e's value post (vv_post), whatever e
 * is, holds again after the walk, next to the walk's own target_post.
 *
 * TOP-LEVEL:
 *   target_pure_vv_frame
 *)

Theory targetPureVvFrame
Ancestors
  targetPlaceSimDefs supportedTargets loweringPosts

Theorem target_pure_vv_frame:
  !ctx func cx cenv env tops bt e es es1 vt sa sm sb s0 s1 tv vv op.
    supported_target_pure tops bt /\
    target_sim ctx func cenv cx env bt es1 /\
    type_place_target env bt = SOME vt /\
    vv_post ctx func cenv cx e es sa sm s0 es1 tv vv s1 /\
    vv_storage_live cx vv es1 s1 /\
    (cenv.ce_is_ctor ==> vv_location vv <> SOME LocCode) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!l. vv_operand vv <> Label l) /\
    sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
    stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
    compile_get_target_ptr compile_expr cenv bt sm = (op, sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\
    gas_admissible (eval_base_place cx bt) target_res_ok es1 /\
    ~s1.vs_halted /\
    s1.vs_current_bb = sm.cs_current_bb /\
    s1.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx, func) (eval_base_place cx bt) (es1, s1)
      (\res ee t. ?pv. res = INL pv /\
         target_post ctx func cenv cx es1 sm sb s1 ee pv vt op t /\
         vv_post ctx func cenv cx e es sa sb s0 ee tv vv t /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\res ee r. expr_exit res r)
Proof
  cheat
QED
