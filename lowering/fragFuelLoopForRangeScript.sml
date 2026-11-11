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

(* Unsigned modular distance decreases even when the counter wraps. *)
Theorem range_distance_decreases[local]:
  !(a:256 word) b.
    a <> b ==> w2n (b - (a + 1w)) < w2n (b - a)
Proof
  rpt strip_tac >> rewrite_tac[wordsTheory.WORD_SUB_PLUS] >>
  irule wordsTheory.WORD_PRED_THM >> simp[wordsTheory.WORD_EQ_SUB_ZERO]
QED

(* Recover the caller's frame from the smaller body write set.  The
   optional fresh local pointer need not be in the caller's write set. *)
Theorem range_body_frame[local]:
  !N M p W Wb s t.
    N <= M /\ N <= p /\
    Wb SUBSET (STRING #"%" (toString p) INSERT
                 {x | x IN W /\ var_below N x}) /\
    vars_kept M Wb s t ==>
    vars_kept N W s t
Proof
  rw[vars_kept_def] >>
  `x NOTIN Wb` by
    (gvs[pred_setTheory.SUBSET_DEF] >> metis_tac[var_below_fresh]) >>
  first_x_assum irule >> simp[] >>
  gvs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Declaration changes only the new pointer's write permission. *)
Theorem range_body_declare[local]:
  !ce id ty st bc st1 N W E lc b c.
    cenv_ptrs_in W ce /\ cenv_ptrs_below N ce /\
    N <= st.cs_next_var /\ stmt_exits_in E ce lc /\
    declare_local ce id ty st = (bc,st1) ==>
    cenv_ptrs_in
      (if ce.ce_alloca_locals then
         STRING #"%" (toString st.cs_next_var) INSERT
           {x | x IN W /\ var_below N x}
       else {x | x IN W /\ var_below N x}) bc /\
    cenv_ptrs_below st1.cs_next_var bc /\
    stmt_exits_in (E UNION {b;c}) bc (InLoop b c)
Proof
  rpt gen_tac >>
  Cases_on `ce.ce_alloca_locals` >>
  simp[declare_local_def, comp_bind_def, comp_return_def, fresh_var_def, LET_THM,
       cenv_ptrs_in_def, cenv_ptrs_below_def, stmt_exits_in_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE, AllCaseEqs()]
  >~ [`var_below (k + 1) (STRING #"%" (toString k))`]
  >- simp[var_below_def, ASCIInumbersTheory.toString_inj] >>
  qpat_assum `!i v z. FLOOKUP _ i = SOME (PtrVar (Var v) z) ==> v IN _`
    (drule_then assume_tac) >>
  qpat_assum `!i v z. FLOOKUP _ i = SOME (PtrVar (Var v) z) ==> var_below N v`
    (drule_then assume_tac) >>
  simp[] >> gvs[var_below_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

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
