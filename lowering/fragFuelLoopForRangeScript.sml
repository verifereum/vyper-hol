(*
 * Fuel bound for a range loop (For over Range), the loop part of the
 * statement-level fuel bound.
 *
 * Why it terminates: the counter is a fresh variable, set to start in the
 * entry block and incremented by one (mod 2^256) in the incr block, and
 * the loop exits when it EQuals end_val, a fresh variable computed once in
 * the entry block.  The body writes only the pointer variables of its
 * environment's locals (all allocated before the counter: cenv_ptrs_below)
 * and the variables it allocates itself, so neither the counter nor
 * end_val changes in the body, and the loop runs at most 2^256 rounds,
 * each within the body's bound plus a constant.  A jump out of the body
 * goes to exit_lbl (break: the end of the loop), incr_lbl (continue) or
 * the constructor's exit label (in E).
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_for_range
 *)

Theory fragFuelLoopForRange
Ancestors
  fragFuel fragFuelContextBase fragFuelContext fragFuelStmtBase
  stmtLowering exprLowering compileEnv emitHelper context venomInst
Libs
  fragFuelLib

Theorem fuel_okS_compile_for_range:
  !cenv lctx ty id fty start_e end_e bound body Wv E.
    (!c t e Wv' E'. fuel_ok Wv' {} E' (lower_value compile_expr c t e)) /\
    (!cenv' lc Wv' E'.
       cenv_ptrs_in Wv' cenv' /\ stmt_exits_in E' cenv' lc ==>
       fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv') Wv' {} E'
         (compile_stmts cenv' lc ty body)) /\
    cenv_ptrs_in Wv cenv /\ stmt_exits_in E cenv lctx ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv) Wv {} E
      (compile_stmt cenv lctx ty (For id fty (Range start_e end_e) bound body))
Proof
  cheat
QED
