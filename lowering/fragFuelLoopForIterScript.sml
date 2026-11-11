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

(* Restrict writes to pre-loop variables and, when present, the newly
   allocated local pointer.  Later compiler temporaries remain protected. *)
Theorem iter_body_kept_outer[local]:
  vars_kept M ({x | x IN Wv /\ var_below N0 x} UNION P) s t /\
  N <= M /\ N <= N0 /\ (!x. x IN P ==> ~var_below N x) ==>
  vars_kept N Wv s t
Proof
  rw[vars_kept_def, var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem iter_body_fresh_protected[local]:
  N0 <= n /\ n < M /\
  (!x. x IN P ==> x <> STRING #"%" (toString n)) ==>
  var_below M (STRING #"%" (toString n)) /\
  STRING #"%" (toString n) NOTIN
    ({x | x IN Wv /\ var_below N0 x} UNION P)
Proof
  simp[var_below_def, ASCIInumbersTheory.toString_inj] >>
  rpt strip_tac >> gvs[] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem iter_body_kept_protected[local]:
  vars_kept M ({x | x IN Wv /\ var_below N0 x} UNION P) s t /\
  var_below M x /\ ~var_below N0 x /\ x NOTIN P ==>
  lookup_var x t = lookup_var x s
Proof
  simp[vars_kept_def] >> metis_tac[]
QED

Theorem iter_declare_ctor_exit[local]:
  declare_local ce id ty st = (bc,st') ==>
  bc.ce_ctor_exit_label = ce.ce_ctor_exit_label
Proof
  simp[declare_local_def] >>
  Cases_on `ce.ce_alloca_locals` >>
  simp[comp_bind_def, comp_return_def, fresh_var_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem iter_declare_ptrs[local]:
  declare_local ce id ty st = (bc,st') /\
  cenv_ptrs_in Wv ce /\ cenv_ptrs_below N0 ce /\
  N0 <= st.cs_next_var /\ st'.cs_next_var <= M ==>
  cenv_ptrs_in
    ({x | x IN Wv /\ var_below N0 x} UNION
     (if ce.ce_alloca_locals then {STRING #"%" (toString st.cs_next_var)} else {})) bc /\
  cenv_ptrs_below M bc
Proof
  Cases_on `ce.ce_alloca_locals` >>
  simp[declare_local_def, comp_bind_def, comp_return_def, fresh_var_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[cenv_ptrs_in_def, cenv_ptrs_below_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[] >>
  rpt (first_x_assum (drule_then assume_tac)) >>
  fs[var_below_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem iter_ptr_load_fresh[local]:
  !ctor imm loc op st v st'.
  compile_ptr_load ctor imm loc op st = (v,st') ==>
  ?n. v = Var (STRING #"%" (toString n)) /\
      st.cs_next_var <= n /\ n < st'.cs_next_var
Proof
  rpt gen_tac >> Cases_on `ctor` >> Cases_on `imm` >>
  Cases_on `loc` >> simp[compile_ptr_load_def] >>
  simp[compile_imm_load_word_def, emit_op_def, fresh_id_def,
       fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt strip_tac >> gvs[] >> simp[]
QED

Theorem iter_declare_exits[local]:
  declare_local ce id ty st = (bc,st') /\ stmt_exits_in E ce lc ==>
  stmt_exits_in (E UNION {exit_lbl; incr_lbl}) bc (InLoop exit_lbl incr_lbl)
Proof
  rpt strip_tac >> drule iter_declare_ctor_exit >>
  gvs[stmt_exits_in_def] >> metis_tac[]
QED

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
