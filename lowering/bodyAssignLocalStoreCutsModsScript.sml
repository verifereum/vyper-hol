(* Cut vocabulary for the local Assign write.  These predicates expose the
   normal post and endpoint facts without introducing a new execution. *)
Theory bodyAssignLocalStoreCutsMods
Ancestors
  bodyFullPostsMods bodyAssignLocalInstallMods bodyAssignLocalSavedMods
  bodyAssignLocalWordPathMods bodyAssignLocalPlaceRoutesMods
  bodyFullShared bodyPtrDefs loweringPosts loweringStateRelDefs
  compileEnv stmtSimDefs exprSimProps vyperState vyperAST words finite_map

(* This is the concrete normal branch of the consequent of
   stmt_frag_full_mods_def.  Keeping it as a named predicate makes the
   endpoint cut independent of the particular store opcode. *)
Definition local_assign_normal_mods_def[nocompute]:
  local_assign_normal_mods DF lo d lctx sb cenv cenv' H ctx func cx ee t G tn
    s0 sa es G0 tn0 res <=>
    stmt_lands lctx sb res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb /\ cenv' = cenv) /\
    cenv_top_ext cenv cenv' ee.scopes /\
    stmt_state_rel H ctx func cenv' cx ee t /\
    immutable_frame_mods func cenv' cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv' sb t /\
    alloca_history func t /\
    return_buf_sep d cenv' ee t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv' cx ee G tn t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv' ee t /\
    (!aid off sz i.
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\
       off <= i /\ i < off + sz /\ i IN tn.t_mem ==>
       i IN tn0.t_mem)
End

(* Machine/source frame at a store cut.  The actual write footprint and the
   endpoint are intentionally parameters, rather than a desired suffix run. *)
Definition local_assign_mem_frame_mods_def[nocompute]:
  local_assign_mem_frame_mods DF lo d H ctx cenv cx func ee s sm t id w k
    bytes cap sa sb G tn tf s0 es <=>
    stmt_state_rel H ctx func cenv cx ee s /\
    immutable_frame_mods func cenv cx ee s /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
    local_region cenv ee.scopes s id (w2n w) cap /\
    w2n w <= w2n w + k /\ w2n w + k + bytes <= w2n w + cap /\
    typed_copy_state_frame sm (w2n w + k) bytes s t /\
    local_ptrs_reserved cenv sm /\
    sm.cs_next_var <= sb.cs_next_var /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~block_is_terminated sb /\ ~t.vs_halted /\ alloca_history func t /\
    return_buf_frame d cenv sm s /\ return_buf_sep d cenv ee s /\
    s0.vs_alloca_next <= s.vs_alloca_next /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm
End

(* Facts about the evaluated operand and the selected destination.  This is
   deliberately endpoint-local: it does not quantify over a compiled suffix. *)
Definition local_assign_operand_mods_def[nocompute]:
  local_assign_operand_mods lo cenv cx env ee s id p cap path entry ptv v w k
    dty G tn tf bytes <=>
    lookup_scopes id ee.scopes = SOME entry /\
    mem_path_offset entry.type path = SOME (k,ptv) /\
    value_has_type entry.type entry.value /\
    well_formed_type_value entry.type /\
    value_has_type ptv v /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) cap) /\
    lookup_var p s = SOME w /\
    type_place_target env (NameTarget id) = SOME (Type dty) /\
    (!m. mem_agree_outside tf.t_mem tn.vs_memory m ==>
         val_in_memory ptv v (w2n w + k) m) /\
    bytes <= type_memory_size ptv /\ k + bytes <= cap /\
    lo <= w2n w + k
End

(* Conversion at the original local-Assign cut.  The right hand side is the
   literal normal lambda after specializing the returned compiler environment
   to cenv; no positional projection of a body invariant is involved. *)
Theorem local_assign_normal_at_cut_mods:
  local_assign_normal_mods DF lo d lctx sb cenv cenv H ctx func cx ee t G tn s0 sa es G0 tn0
    (INL ()) <=>
    stmt_lands lctx sb (INL ()) t /\ ~t.vs_halted /\
    ~block_is_terminated sb /\ cenv_top_ext cenv cenv ee.scopes /\
    stmt_state_rel H ctx func cenv cx ee t /\
    immutable_frame_mods func cenv cx ee t /\
    storage_well_formed_on cx ee (FST H) /\
    return_buf_frame d cenv sb t /\ alloca_history func t /\
    return_buf_sep d cenv ee t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv ee t /\
    (!aid off sz i.
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                    off + sz <= b \/ b + sz' <= off) /\
       off <= i /\ i < off + sz /\ i IN tn.t_mem ==>
       i IN tn0.t_mem)
Proof
  simp[local_assign_normal_mods_def, AC CONJ_ASSOC CONJ_COMM] >>
  tautLib.TAUT_TAC
QED
