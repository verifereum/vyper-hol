(*
 * Fuel bound for an iteration loop (For over an Array), the loop part of
 * the statement-level fuel bound.
 *
 * Why it terminates: the index is a fresh variable, set to 0 in the entry
 * block and incremented by one (mod 2^256) in the incr block, and the loop
 * exits when it EQuals len_op: a literal (static array) or the fresh
 * result of compile_ptr_load (dynamic array), computed once before the
 * loop.  The body writes only the pointer variables of its environment's
 * locals (all allocated before the index and len_op: cenv_ptrs_below) and
 * the variables it allocates itself, so neither the index nor len_op
 * changes in the body, and the loop runs at most 2^256 rounds, each
 * within the body's bound plus a constant.  The array pointer arr_op only
 * feeds address arithmetic, so its value doesn't matter.  A jump out of
 * the body goes to exit_lbl (break: the end of the loop), incr_lbl
 * (continue) or the constructor's exit label (in E).
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_for_iter
 *)

Theory fragFuelLoopForIter
Ancestors
  fragFuel fragFuelContextBase fragFuelContext fragFuelStmtBase
  stmtLowering exprLowering compileEnv emitHelper context venomInst
Libs
  fragFuelLib

Theorem fuel_okS_compile_for_iter:
  !cenv lctx ty id fty arr_e bound body Wv E.
    (!c t e Wv' E'. fuel_ok Wv' {} E' (compile_expr c t e)) /\
    (!cenv' lc Wv' E'.
       cenv_ptrs_in Wv' cenv' /\ stmt_exits_in E' cenv' lc ==>
       fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv') Wv' {} E'
         (compile_stmts cenv' lc ty body)) /\
    cenv_ptrs_in Wv cenv /\ stmt_exits_in E cenv lctx ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv) Wv {} E
      (compile_stmt cenv lctx ty (For id fty (Array arr_e) bound body))
Proof
  cheat
QED
