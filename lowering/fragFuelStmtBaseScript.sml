(*
 * Fuel bounds for statements: the environment conditions and the
 * statement helpers that compile no expressions.
 *
 * A statement writes the pointer variables of its locals (their ALLOCA),
 * which were allocated before it, so its Wv must hold them
 * (cenv_ptrs_in).  A loop's counter is fresh, so none of them is the
 * counter once they were all allocated before the loop (cenv_ptrs_below).
 *
 * TOP-LEVEL:
 *   cenv_ptrs_below_def, cenv_ptrs_in_def, stmt_exits_in_def,
 *   next_stable_cenv_ptrs_below, var_below_le, cenv_ptrs_below_le,
 *   cenv_ptrs_below_update, emit_op_next,
 *   fuel_ok_emit_local_alloca, fuel_ok_compile_range_bound_checks,
 *   fuel_ok_compile_iter_elem_copy
 *)

Theory fragFuelStmtBase
Ancestors
  fragFuel fragFuelContextBase fragFuelContext stmtLowering exprLowering
  compileEnv emitHelper context venomInst finite_map
Libs
  fragFuelLib

(* The pointer variables of cenv's locals were allocated before n. *)
Definition cenv_ptrs_below_def:
  cenv_ptrs_below n cenv <=>
    !id x sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var x) sz) ==>
              var_below n x
End

(* The pointer variables of cenv's locals are in Wv. *)
Definition cenv_ptrs_in_def:
  cenv_ptrs_in Wv cenv <=>
    !id x sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var x) sz) ==> x IN Wv
End

(* The labels a statement may jump to outside its own code: the
   constructor's exit label, and the enclosing loop's break and continue
   labels. *)
Definition stmt_exits_in_def:
  stmt_exits_in E cenv lc <=>
    (!l. cenv.ce_ctor_exit_label = SOME l ==> l IN E) /\
    (!b c. lc = InLoop b c ==> b IN E /\ c IN E)
End

Theorem var_below_le:
  !n n' x. var_below n x /\ n <= n' ==> var_below n' x
Proof
  rw[var_below_def]
QED

Theorem cenv_ptrs_below_le:
  !n n' c. cenv_ptrs_below n c /\ n <= n' ==> cenv_ptrs_below n' c
Proof
  rw[cenv_ptrs_below_def] >> metis_tac[var_below_le]
QED

Theorem cenv_ptrs_below_update:
  !n n' cenv name op sz.
    cenv_ptrs_below n cenv /\ n <= n' /\ (!x. op = Var x ==> var_below n' x) ==>
    cenv_ptrs_below n'
      (cenv with ce_vars updated_by (\m. m |+ (name, PtrVar op sz)))
Proof
  rw[cenv_ptrs_below_def, FLOOKUP_UPDATE] >> gvs[AllCaseEqs()] >>
  metis_tac[var_below_le]
QED

Theorem emit_op_next:
  !opc ops st x st'.
    emit_op opc ops st = (x, st') ==> st'.cs_next_var = st.cs_next_var + 1
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem next_stable_cenv_ptrs_below:
  !cenv. next_stable (\st. cenv_ptrs_below st.cs_next_var cenv)
Proof
  rw[next_stable_def, cenv_ptrs_below_def, var_below_def] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem fuel_ok_emit_local_alloca:
  !cenv id Wv E.
    cenv_ptrs_in Wv cenv ==> fuel_ok Wv {} E (emit_local_alloca cenv id)
Proof
  rw[emit_local_alloca_def] >> rpt BasicProvers.TOP_CASE_TAC >> simp[fuel_ok_return] >>
  irule fuel_ok_emit_inst >> fs[cenv_ptrs_in_def, is_terminator_def] >>
  metis_tac[]
QED

Theorem fuel_ok_compile_range_bound_checks:
  !s e r b sg Wv E.
    fuel_ok Wv {} E (compile_range_bound_checks s e r b sg)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_range_bound_checks_def] >>
  fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void] >> simp[is_terminator_def]
QED

Theorem fuel_ok_compile_iter_elem_copy:
  !cenv ep ip sz loc sa tty ety Wv E.
    fuel_ok Wv {} E (compile_iter_elem_copy cenv ep ip sz loc sa tty ety)
Proof
  rpt gen_tac >> simp_tac std_ss [compile_iter_elem_copy_def] >>
  rpt (match_mp_tac fuel_ok_if >> conj_tac >> strip_tac)
  >- fuel_auto [fuel_ok_context_copies]
  >- (fuel_auto [fuel_ok_compile_ptr_load, fuel_ok_emit_void] >> simp[is_terminator_def])
  >- (Cases_on `loc` >>
      simp[fuel_ok_emit_void, fuel_ok_compile_imm_copy_to_memory,
           fuel_ok_compile_copy_memory, is_terminator_def])
  >- (fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void] >> simp[is_terminator_def]) >>
  simp[fuel_ok_compile_store_memory]
QED
