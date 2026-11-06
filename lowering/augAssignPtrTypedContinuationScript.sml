Theory augAssignPtrTypedContinuation
Ancestors augAssignPtrTypedNumeric augAssignPtrBinopContinuation

Theorem binop_typed_scalar_continuation:
  well_typed_binop ann bop t1 t2 /\ type_bits t1 MOD 8 = 0 /\
  (bop = Exp ==>
    (IS_SOME bl \/ ?n. el = SOME n /\ 0 <= n) /\
    (!n. bl = SOME n ==> v1 = IntV n) /\
    (!n. el = SOME n ==> v2 = IntV n)) /\
  (bop = ShL \/ bop = ShR ==> ?i. v2 = IntV i /\ 0 <= i) /\
  word_value_type t1 /\ word_value_type t2 /\
  evaluate_type tenv t1 = SOME tv1 /\ value_has_type tv1 v1 /\
  evaluate_type tenv t2 = SOME tv2 /\ value_has_type tv2 v2 /\
  bop <> In /\ bop <> NotIn /\
  expr_res_ok (bop_result cx ann bop tys v1 v2 es0) /\
  straight_fresh (compile_binop bop x y t1 bl el) /\
  compile_binop bop x y t1 bl el sa = (op,sb) /\ fn_has_code sa sb fn /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  scalar_code A (emitted_insts sa sb) /\
  (!z. z IN A ==> op_prov G (Var z) = NONE /\ op_taint tn (Var z) = {}) /\
  ~ctx_has_dalloca ctx /\
  eval_operand x s = SOME (val_to_w256 v1) /\
  eval_operand y s = SOME (val_to_w256 v2) /\
  (!z. x = Var z ==> not_fresh_at sa z) /\
  (!z. y = Var z ==> not_fresh_at sa z) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx fn cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  ghost_kept cenv es origin G0 tn0 s0 G tn /\
  (!z. not_fresh_at origin z ==> not_fresh_at sa z) /\
  scalar_available
    (A UNION BIGUNION (set (MAP (\i. set i.inst_outputs)
                               (emitted_insts sa sb)))) op ==>
  (?v t H tm.
    bop_result cx ann bop tys v1 v2 es0 = INL v /\ word_value v /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    stmt_state_rel ctx fn cenv cx es (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    eval_operand op (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME (val_to_w256 v) /\
    (!z w. not_fresh_at sa z /\ lookup_var z s = SOME w ==>
       lookup_var z (t with vs_inst_idx := LENGTH sb.cs_current_insts) = SOME w) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    ghost_inv d cenv cx es H tm (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    ghost_kept cenv es origin G0 tn0 s0 H tm /\
    op_prov H op = NONE /\ op_taint tm op = {}) \/
  (?msg t j H tm.
    bop_result cx ann bop tys v1 v2 es0 = INR (Error (RuntimeError msg)) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (Abort Revert_abort (t with vs_inst_idx := j)))
Proof
  strip_tac >>
  irule binop_numeric_scalar_continuation >>
  simp[] >>
  conj_tac
  >- (qexistsl [`bl`, `el`, `t1`, `x`, `y`] >> simp[] >>
      irule binop_typed_numeric_witness >> simp[] >>
      (conj_tac >- metis_tac[]) >> qexistsl [`t2`, `tenv`, `tv1`, `tv2`] >> simp[]) >>
  qexists `A` >> simp[]
QED
