(* Allocation-aware account suffix transport at the operand-final frame. *)
Theory bodyPtrEnvBuiltinsAccountOperand
Ancestors bodyPtrEnvBuiltinsAccountRuns bodyPtrEnvBuiltinsOperandFrame
  bodyPtrEnvBuiltinsOperandCompose bodyPtrDefs exprLoweringProps
  exprSimAccounts exprLowering compileEnv stmtFragPtr
  venomState venomInst vyperInterpreter vyperValue vyperContext
  vyperTypeSystem list

Theorem operand_account_suffix_run:
  lower_value compile_expr cenv ty e sa = (arg,sm) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) /\
  expr_post ctx fn cenv cx e es sa sm s0 ee v arg s /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_rel fn cenv es.scopes s0 /\ local_ptrs_reserved cenv sa /\
  item <> Code /\
  (case item of
     Balance => emit_op BALANCE [arg]
   | Codesize => emit_op EXTCODESIZE [arg]
   | Codehash => emit_op EXTCODEHASH [arg]
   | IsContract => comp_bind (emit_op EXTCODESIZE [arg]) (\c. emit_op GT [c; Lit 0w])
   | Address => comp_return arg
   | Code => comp_return arg) sm = (op,sb) /\
  fn_has_code sm sb fn /\ LENGTH bs = 20 /\ accounts_well_typed ee.accounts /\
  eval_operand arg s = SOME (typed_val_to_w256 (BaseTV AddressT) (BytesV bs)) /\
  evaluate_type (get_tenv cx) (account_item_type item) = SOME tv /\
  op_taint tn arg = {} /\ op_prov G arg = NONE /\ ~ctx_has_dalloca ctx /\
  ghost_inv d cenv cx ee G tn s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  local_ptrs_rel fn cenv ee.scopes s /\ stmt_state_rel ctx fn cenv cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    ghost_inv d cenv cx ee G' tn' t /\
    ghost_kept cenv es sa G0 tn0 s0 G' tn' /\
    op_taint tn' op = {} /\ op_prov G' op = NONE /\
    eval_operand op t = SOME (typed_val_to_w256 tv
      (evaluate_account_op item bs (lookup_account (word_of_bytes_be bs) ee.accounts))) /\
    stmt_state_rel ctx fn cenv cx ee t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by metis_tac[cj 2 compile_expr_grows] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    metis_tac[] >>
  `item = Address ==> op_prov G arg = NONE` by simp[] >>
  drule_all account_suffix_counted_run >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (drule_all operand_suffix_ghost_kept >> simp[]) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[]
QED
