(* Consumer boundary: compile and value anchors determine the scalar run;
   the preserved frame is indexed independently of the current source state. *)
Theory augAssignPtrOperator
Ancestors augAssignPtrCompiler augAssignPtrTypedContinuation

Theorem augassign_clean_operator_ptr:
  compile_binop bop x y ty NONE
    (if bop = Exp then expr_int_literal e else NONE) sa = (op,sb) ==>
  eval_operand x s = SOME (val_to_w256 v1) ==>
  eval_operand y s = SOME (val_to_w256 v2) ==>
  well_typed_binop ty bop ty (expr_type e) /\ type_bits ty MOD 8 = 0 /\
  (bop = Exp ==>
    (?n. expr_int_literal e = SOME n /\ 0 <= n) /\
    (!n. expr_int_literal e = SOME n ==> v2 = IntV n)) /\
  (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
  word_value_type ty /\ word_value_type (expr_type e) /\
  evaluate_type tenv ty = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type tenv (expr_type e) = SOME tv2 /\ value_has_type tv2 v2 /\
  bop <> In /\ bop <> NotIn /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] v1 v2 es0) /\
  (!l. x <> Label l /\ y <> Label l) /\
  op_prov G x = NONE /\ op_taint tn x = {} /\
  op_prov G y = NONE /\ op_taint tn y = {} /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx fn cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  ghost_kept cenv frame_es origin G0 tn0 s0 G tn /\
  (!z. not_fresh_at origin z ==> not_fresh_at sa z) ==>
  (?v t H tm.
    bop_result cx ty bop [ty;expr_type e] v1 v2 es0 = INL v /\ word_value v /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    stmt_state_rel ctx fn cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    eval_operand op (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME (val_to_w256 v) /\
    (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==>
       lookup_var z (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    ghost_inv d cenv cx es H tm (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ghost_kept cenv frame_es origin G0 tn0 s0 H tm /\
    op_prov H op = NONE /\ op_taint tm op = {}) \/
  (?msg t j H tm.
    bop_result cx ty bop [ty;expr_type e] v1 v2 es0 = INR (Error (RuntimeError msg)) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (Abort Revert_abort (t with vs_inst_idx := j)))
Proof
  rpt strip_tac >>
  drule_all typed_binop_scalar_member_ptr >> strip_tac >>
  drule_all compile_binop_clean_certificate_ptr >> strip_tac >>
  irule binop_typed_scalar_continuation >>
  simp[] >>
  (conj_tac >- metis_tac[]) >>
  (conj_tac >- (qexists_tac `A` >> simp[])) >>
  qexistsl [`NONE`, `if bop = Exp then expr_int_literal e else NONE`,
            `ty`, `expr_type e`, `tenv`, `tv1`, `tv2`, `x`, `y`] >>
  simp[] >>
  irule compile_binop_straight_fresh_ptr >> simp[]
QED
