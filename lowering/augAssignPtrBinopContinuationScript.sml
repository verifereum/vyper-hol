Theory augAssignPtrBinopContinuation
Ancestors augAssignPtrScalarContinuation exprBopStraight freshWrites varsExt

Theorem binop_numeric_scalar_continuation:
  ((?v. bop_result cx ann bop tys v1 v2 es0 = INL v /\ word_value v /\
       !x y sa sb op ss.
         compile_binop bop x y ty bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 v1) /\
         eval_operand y ss = SOME (val_to_w256 v2) ==>
         ?ss'. run_inst_seq (emitted_insts sa sb) ss = OK ss' /\
               eval_operand op ss' = SOME (val_to_w256 v)) \/
   (?msg. bop_result cx ann bop tys v1 v2 es0 = INR (Error (RuntimeError msg)) /\
       !x y sa sb op ss.
         compile_binop bop x y ty bl el sa = (op,sb) /\
         fresh_vars_wrt sa ss /\
         eval_operand x ss = SOME (val_to_w256 v1) /\
         eval_operand y ss = SOME (val_to_w256 v2) ==>
         ?ss'. run_inst_seq (emitted_insts sa sb) ss = Abort Revert_abort ss')) /\
  straight_fresh (compile_binop bop x y ty bl el) /\
  compile_binop bop x y ty bl el sa = (op,sb) /\ fn_has_code sa sb fn /\
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
  ghost_kept cenv frame_es origin G0 tn0 s0 G tn /\
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
    ghost_kept cenv frame_es origin G0 tn0 s0 H tm /\
    op_prov H op = NONE /\ op_taint tm op = {}) \/
  (?msg t j H tm.
    bop_result cx ann bop tys v1 v2 es0 = INR (Error (RuntimeError msg)) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tm
      (Abort Revert_abort (t with vs_inst_idx := j)))
Proof
  strip_tac
  >- (disj1_tac >>
      `eval_operand x (drop_fresh sa s) = SOME (val_to_w256 v1) /\
       eval_operand y (drop_fresh sa s) = SOME (val_to_w256 v2)` by
        simp[eval_operand_drop_fresh] >>
      qpat_x_assum `!x y sa sb op ss. _`
        (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
      disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
      simp[fresh_vars_wrt_drop_fresh] >> strip_tac >>
      drule_all straight_fresh_scalar_success_post >>
      disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
      qexistsl [`t`, `H`, `tm`] >> gvs[]) >>
  disj2_tac >>
  `eval_operand x (drop_fresh sa s) = SOME (val_to_w256 v1) /\
   eval_operand y (drop_fresh sa s) = SOME (val_to_w256 v2)` by
    simp[eval_operand_drop_fresh] >>
  qpat_x_assum `!x y sa sb op ss. _`
    (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  disch_then (qspec_then `drop_fresh sa s` mp_tac) >>
  simp[fresh_vars_wrt_drop_fresh] >> strip_tac >>
  drule_all straight_fresh_scalar_abort_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl [`t`, `j`, `H`, `tm`] >> simp[]
QED
