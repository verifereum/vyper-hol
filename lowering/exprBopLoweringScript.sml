(*
 * How a binary operator lowers (#636, part 2)
 *
 * TOP-LEVEL:
 *   compile_expr_bop   — a binary operator goes to the builtin dispatcher
 *   lower_value_bop    — the operands' fragments, then compile_binop
 *
 * Helpers: compile_expr_body_bop, lower_value_child_call, as_stack_val_pair
 *)

Theory exprBopLowering
Ancestors
  list
  exprCallBounds exprLowering emitHelper compileEnv vyperAST
Libs
  pairLib

(* ===== Lowering of a binary operator ===== *)

val expr_sizes = [listTheory.list_size_def, vyperASTTheory.expr_size_def,
                  basicSizeTheory.option_size_def];

(* The binary-operator case of compile_expr_body, for any callbacks.  The
   AddMod/MulMod/PowMod256 patterns split on the first three arguments; every
   branch passes the whole argument list to the builtin callback. *)
Theorem compile_expr_body_bop:
  !f g h cenv ty ann bop args st.
    compile_expr_body f g h cenv ty (Builtin ann (Bop bop) args) st =
    g cenv (expr_type (Builtin ann (Bop bop) args)) ty (Bop bop) args st
Proof
  rpt gen_tac >> simp[compile_expr_body_def] >>
  Cases_on `args` >> simp[] >> rename1 `Builtin ann (Bop bop) (a1::r1)` >>
  Cases_on `a1` >> simp[] >> Cases_on `r1` >> simp[] >>
  rename1 `Builtin ann (Bop bop) (_::a2::r2)` >>
  Cases_on `a2` >> simp[] >> Cases_on `r2` >> simp[] >>
  rename1 `Builtin ann (Bop bop) (_::_::a3::r3)` >>
  Cases_on `a3` >> simp[] >> Cases_on `r3` >> simp[]
QED

(* A binary operator goes to the builtin dispatcher, whatever its
   operands. *)
Theorem compile_expr_bop:
  !cenv ty ann bop args st.
    compile_expr cenv ty (Builtin ann (Bop bop) args) st =
    compile_builtin_dispatch cenv (expr_type (Builtin ann (Bop bop) args)) ty
      (Bop bop) args st
Proof
  rpt gen_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_bop] >>
  simp expr_sizes
QED
Theorem lower_value_child_call:
  !n f cenv ty e.
    expr_size e < n ==>
    lower_value (expr_child_callback n f) cenv ty e = lower_value f cenv ty e
Proof
  rw[FUN_EQ_THM, lower_value_def, comp_bind_def]
QED

Theorem as_stack_val_pair:
  !ty p. as_stack_val ty p = (StackValue ty (FST p), SND p)
Proof
  Cases_on `p` >> simp[as_stack_val_def]
QED

Theorem lower_value_bop:
  !cenv ty ann bop e1 e2 sa op sb.
    lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1; e2]) sa =
      (op, sb) /\
    ~((bop = In \/ bop = NotIn) /\ is_ArrayT (expr_type e2)) /\
    ~(is_bytestring_type (expr_type e1) /\ (bop = Eq \/ bop = NotEq)) ==>
    ?x s1 y s2.
      lower_value compile_expr cenv (expr_type e1) e1 sa = (x, s1) /\
      lower_value compile_expr cenv (expr_type e1) e2 s1 = (y, s2) /\
      compile_binop bop x y (expr_type e1)
        (if bop = Exp then expr_int_literal e1 else NONE)
        (if bop = Exp then expr_int_literal e2 else NONE) s2 = (op, sb)
Proof
  rpt strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_bop] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_child_call] >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >> metis_tac[]
QED
