Theory createSizeRawTotalMods
Ancestors
  createSizeRawTotal createExprSizeExitDefsMods
  fragExec venomExecSemantics venomInst venomState relation list words pair arithmetic
  vfmConstants loweringShapeRules exprLoweringProps freshWrites rich_list bodyPtrDefs
  loweringPosts vyperStorageFootprint integer_word loweringStateRelDefs bodyFullGhostFrame
  stateFrame ptrDiscipline stmtReasonMemory emitHelperProps loweringShapeDefs
  createExprSizeExitDefs createSizeBlueprintRawScalarsMods

(* The post-encoder ADD does not consume source observations or change
   reserved variables. Its sole ghost update is at the new output. *)

Theorem create_raw_total_add_entry_at_cuts_mods:
  emit_op ADD [lhs;rhs] a = (sum_op,b) /\ fn_has_code a b fn /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  create_expr_prefix a b explicit ctx fn s chunk t /\ ~s.vs_halted /\
  (!bb. MEM bb fn.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!f i z. frag_reachable ctx fn s f i z ==> dalloca_fmp_headroom i z) /\
  local_ptrs_reserved ce a /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history fn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!H. valid_horizon cx st0 H p.storage_trace ==>
    stmt_state_rel H ctx fn ce cx p s /\
    immutable_frame_mods fn ce cx p s /\ storage_well_formed_on cx p (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx p G tn s) ==>
  chunk = [] /\ t.vs_gas_readings = s.vs_gas_readings /\
  return_buf_frame d ce b t /\ alloca_history fn t /\ ~t.vs_halted /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  (!f i z. frag_reachable ctx fn t f i z ==> dalloca_fmp_headroom i z) /\
  local_ptrs_reserved ce b /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at b x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at b x) /\
  ?out u v G' tn'.
    sum_op = Var out /\ not_fresh_at b out /\
    eval_operand lhs s = SOME u /\ eval_operand rhs s = SOME v /\
    eval_operand sum_op t = SOME (u + v) /\
    G' = step_prov PG G (mk_inst a.cs_next_id ADD [lhs;rhs] [out])
      (update_var out (u + v) s) /\
    tn' = step_taint (mk_inst a.cs_next_id ADD [lhs;rhs] [out]) s
      (update_var out (u + v) s) tn /\
    (!x. not_fresh_at a x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!H. valid_horizon cx st0 H p.storage_trace ==>
      stmt_state_rel H ctx fn ce cx p t /\
      immutable_frame_mods fn ce cx p t /\ storage_well_formed_on cx p (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx p G' tn' t)
Proof
  cheat
QED
