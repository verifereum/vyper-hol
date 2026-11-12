(* The suffix preserves allocations; the operand need not do so. *)
Theory bodyPtrEnvBuiltinsBlockHashOperand
Ancestors bodyPtrEnvBuiltinsBlockHashPost bodyPtrEnvBuiltinsOperandFrame
  bodyPtrEnvBuiltinsEdges bodyPtrDefs exprLoweringProps stmtFragPtr compileEnv venomState
  venomExecSemantics

Theorem operand_blockhash_suffix_run:
  lower_value compile_expr cenv ty e sa = (arg,sm) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es sa sm s0 ee v arg s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_reserved cenv sa /\
  compile_blockhash arg sm = (op,sb) /\ fn_has_code sm sb fn /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\
  (!x. arg = Var x ==> not_fresh_at sm x) /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx ee G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx ee s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sb) s = OK u /\ eval_operand op u = SOME w ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d cenv cx ee G' tn' t /\
    ghost_kept cenv es sa G0 tn0 s0 G' tn' /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    eval_operand op t = SOME w /\
    stmt_state_rel ctx fn cenv cx ee t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by
    metis_tac[cj 2 compile_expr_grows] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sm x` by metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sm x` by metis_tac[] >>
  `ghost_kept cenv ee sm G tn s G tn` by simp[ghost_kept_refl] >>
  drule_all blockhash_normal_suffix_run >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (drule_all operand_suffix_ghost_kept >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[]
QED
