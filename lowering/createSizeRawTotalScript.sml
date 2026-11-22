Theory createSizeRawTotal
Ancestors
  fragExec venomExecSemantics venomInst venomState relation list words pair arithmetic
  vfmConstants loweringShapeRules exprLoweringProps freshWrites rich_list bodyPtrDefs
  loweringPosts vyperStorageFootprint integer_word loweringStateRelDefs bodyFullGhostFrame
  stateFrame ptrDiscipline stmtReasonMemory emitHelperProps loweringShapeDefs
  createExprSizeExitDefs createSizeBlueprintRawScalars

(* The post-encoder ADD does not consume source observations or change
   reserved variables. Its sole ghost update is at the new output. *)
Theorem create_raw_total_add_entry_at_cuts:
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
    stmt_state_rel H ctx fn ce cx p s /\ storage_well_formed_on cx p (FST H) /\
    ghost_inv_at (DF H) lo d ce cx p G tn s) ==>
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
      stmt_state_rel H ctx fn ce cx p t /\ storage_well_formed_on cx p (FST H) /\
      ghost_inv_at (DF H) lo d ce cx p G' tn' t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (Q.INST [`opc` |-> `ADD`] blueprint_raw_scalar_step |>
             SIMP_RULE (srw_ss()) [is_terminator_def]) >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = OK _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [step_add_eq, AllCaseEqs()]) >>
  rename1 `eval_operand lhs s = SOME u` >>
  rename1 `eval_operand rhs s = SOME v` >>
  rename1 `sum_op = Var out` >>
  qpat_x_assum `update_var out _ s = raw` (SUBST_ALL_TAC o SYM) >>
  `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts a b) /\
   b.cs_current_insts = a.cs_current_insts ++ emitted_insts a b /\
   b.cs_current_bb = a.cs_current_bb /\ ~not_fresh_at a out` by
    (drule emitted_insts_emit_op >> strip_tac >> drule emit_op_facts >>
     strip_tac >> gvs[mk_inst_def]) >>
  `state_frame t = state_frame (s with vs_inst_idx := t.vs_inst_idx) /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_gas_readings = s.vs_gas_readings /\ eval_operand sum_op t = SOME (u + v) /\
   (!x. not_fresh_at a x ==> lookup_var x t = lookup_var x s)` by
    (simp[update_var_def, state_frame_def, eval_operand_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE, SF CONJ_ss] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H p.storage_trace ==>
    stmt_state_rel H ctx fn ce cx p s /\ ghost_inv_at (DF H) lo d ce cx p G tn s` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  suspend "frames"
QED
Resume create_raw_total_add_entry_at_cuts[frames]:
  drule_all blueprint_raw_load_add_frame >> strip_tac >>
  `!f i z. frag_reachable ctx fn t f i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `create_expr_prefix a b explicit ctx fn s chunk t`
       (mp_tac o MATCH_MP (SRULE[GSYM AND_IMP_INTRO] blueprint_raw_reach_at_cut)) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `local_ptrs_reserved ce b /\
   (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at b x) /\
   (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at b x)` by
    metis_tac[local_ptrs_reserved_next_var, freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `t = (update_var _ _ _ with vs_inst_idx := _)` kall_tac >>
  simp[] >> suspend "ghost"
QED
Resume create_raw_total_add_entry_at_cuts[ghost]:
  qabbrev_tac `ins = mk_inst a.cs_next_id ADD [lhs;rhs] [out]` >>
  qabbrev_tac `raw = update_var out (u + v) s` >>
  qabbrev_tac `Gp = step_prov PG G ins raw` >>
  qabbrev_tac `tp = step_taint ins s raw tn` >>
  `tp.t_mem = tn.t_mem /\ tp.t_stor = tn.t_stor /\
   tp.t_imm = tn.t_imm /\ tp.t_trans = tn.t_trans /\
   (!x. x <> out ==> FLOOKUP Gp x = FLOOKUP G x /\
                     op_taint tp (Var x) = op_taint tn (Var x))` by
    simp[Abbr `Gp`, Abbr `tp`, Abbr `ins`, Abbr `raw`,
         typedCopyOriginPtrBaseTheory.typed_copy_origin_ptr_binop_ghost_frame] >>
  `!x. not_fresh_at a x ==> lookup_var x t = lookup_var x t /\
      FLOOKUP Gp x = FLOOKUP G x /\ op_taint tp (Var x) = op_taint tn (Var x)` by metis_tac[] >>
  (rpt conj_tac >>> LASTGOAL
    (gen_tac >> strip_tac >>
     qpat_assum `!h. valid_horizon _ _ h _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
       (drule_then strip_assume_tac) >>
     irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G`,`p`,`t`,`a`,`tn`] >> simp[])) >>
  rpt strip_tac >> metis_tac[]
QED
Finalise create_raw_total_add_entry_at_cuts
