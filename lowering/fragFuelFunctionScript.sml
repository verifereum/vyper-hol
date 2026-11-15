(*
 * Fuel bound for an internal function's code (compile_internal_function),
 * given one for its body.
 *
 * The body runs under cenv_ptrs_below for the environment with the
 * materialized parameters, whose pointer variables are the PARAM and
 * ALLOCA outputs emitted before it; the code around the body is
 * straight-line.
 *
 * TOP-LEVEL:
 *   fuel_okS_compile_internal_function
 *)

Theory fragFuelFunction
Ancestors
  fragFuel fragFuelStmtBase fragFuelContextBase fragFuelContext
  fragFuelExprHelpers moduleLowering stmtLowering compileEnv emitHelper
  context venomInst finite_map
Libs
  fragFuelLib

Theorem caps_below_le[local]:
  !n n' caps.
    EVERY (\p. !x. SND (SND p) = Var x ==> var_below n x) caps /\ n <= n' ==>
    EVERY (\p. !x. SND (SND p) = Var x ==> var_below n' x) caps
Proof
  rw[listTheory.EVERY_MEM] >> metis_tac[var_below_le]
QED

Theorem next_stable_caps[local]:
  !cenv caps.
    next_stable (\st. cenv_ptrs_below st.cs_next_var cenv /\
      EVERY (\p. !x. SND (SND p) = Var x ==> var_below st.cs_next_var x) caps)
Proof
  rpt gen_tac >> simp_tac std_ss [next_stable_def] >> rpt gen_tac >>
  strip_tac >> conj_tac
  >- (irule cenv_ptrs_below_le >> qexists_tac `st.cs_next_var` >> fs[]) >>
  irule caps_below_le >> qexists_tac `st.cs_next_var` >> fs[]
QED

Theorem emit_void_next[local]:
  !opc ops st x st'.
    emit_void opc ops st = (x, st') ==> st'.cs_next_var = st.cs_next_var
Proof
  simp[emit_void_def, comp_bind_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem fuel_ok_compile_internal_param_decls[local]:
  !ps i Wv E. fuel_ok Wv {} E (compile_internal_param_decls ps i)
Proof
  Induct >- simp[compile_internal_param_decls_def, fuel_ok_return] >>
  Cases >> rpt gen_tac >>
  PURE_ONCE_REWRITE_TAC [compile_internal_param_decls_def] >>
  fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]
QED

(* The declared parameters are variables allocated by the end. *)
Theorem compile_internal_param_decls_below[local]:
  !ps i st res st'.
    compile_internal_param_decls ps i st = (res, st') ==>
    st.cs_next_var <= st'.cs_next_var /\
    EVERY (\p. !x. SND (SND p) = Var x ==> var_below st'.cs_next_var x)
      (FST res)
Proof
  Induct
  >- (rw[compile_internal_param_decls_def, comp_return_def] >> simp[]) >>
  Cases >> rpt gen_tac >>
  simp[compile_internal_param_decls_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op PARAM _ st = (pop, s1)` >>
  rename1 `compile_internal_param_decls ps _ s1 = (rr, s2)` >>
  imp_res_tac emit_op_next >> imp_res_tac emit_op_var >>
  last_x_assum drule >> strip_tac >> rpt conj_tac
  >- decide_tac
  >- (rpt strip_tac >> irule var_below_le >> qexists_tac `s1.cs_next_var` >>
      fs[]) >>
  first_assum ACCEPT_TAC
QED

Theorem fuel_ok_materialize_internal_params[local]:
  !caps cenv Wv E. fuel_ok Wv {} E (materialize_internal_params cenv caps)
Proof
  Induct >- simp[materialize_internal_params_def, fuel_ok_return] >>
  PairCases >> rpt gen_tac >>
  PURE_ONCE_REWRITE_TAC [materialize_internal_params_def] >>
  IF_CASES_TAC
  >- (rpt BasicProvers.TOP_CASE_TAC >>
      fuel_auto [fuel_ok_emit_op, fuel_ok_emit_void_any] >>
      simp[is_terminator_def]) >>
  fuel_auto []
QED

(* Materializing the parameters keeps the pointer variables allocated. *)
Theorem materialize_internal_params_ptrs[local]:
  !caps cenv st c st'.
    materialize_internal_params cenv caps st = (c, st') /\
    cenv_ptrs_below st.cs_next_var cenv /\
    EVERY (\p. !x. SND (SND p) = Var x ==> var_below st.cs_next_var x) caps ==>
    cenv_ptrs_below st'.cs_next_var c /\
    c.ce_ctor_exit_label = cenv.ce_ctor_exit_label
Proof
  Induct
  >- (rw[materialize_internal_params_def, comp_return_def] >> fs[]) >>
  PairCases >> rpt gen_tac >> Cases_on `h1` >>
  simp[materialize_internal_params_def, LET_THM] >> strip_tac
  >- (Cases_on `FLOOKUP cenv.ce_vars h0` >> fs[]
      >- (last_x_assum drule_all >> simp[]) >>
      rename1 `FLOOKUP _ _ = SOME vl` >> Cases_on `vl` >> fs[]
      >- (fs[comp_bind_def, comp_ignore_bind_def] >>
          rpt (pairarg_tac >> fs[]) >>
          rename1 `emit_op ALLOCA _ st = (pv, s1)` >>
          rename1 `emit_void MSTORE _ s1 = (u, s2)` >>
          imp_res_tac emit_op_next >> imp_res_tac emit_void_next >>
          imp_res_tac emit_op_var >>
          last_x_assum drule >> impl_tac
          >- (conj_tac
              >- (match_mp_tac (Q.SPEC `st.cs_next_var` cenv_ptrs_below_update) >>
                  rpt conj_tac >- first_assum ACCEPT_TAC >- fs[] >>
                  rpt strip_tac >>
                  irule var_below_le >> qexists_tac `s1.cs_next_var` >> fs[]) >>
              irule caps_below_le >> qexists_tac `st.cs_next_var` >> fs[]) >>
          simp[]) >>
      last_x_assum drule_all >> simp[]) >>
  last_x_assum drule >> impl_tac
  >- (conj_tac
      >- (match_mp_tac (Q.SPEC `st.cs_next_var` cenv_ptrs_below_update) >>
          fs[]) >>
      first_assum ACCEPT_TAC) >>
  simp[]
QED

val ok_tac = match_mp_tac fuel_okS_of_ok

val keep_tac =
  match_mp_tac fuel_okS_ignore_bind_keep >> rpt conj_tac
  >- MATCH_ACCEPT_TAC next_stable_cenv_ptrs_below

Theorem fuel_okS_compile_internal_function:
  !cenv params has_ret_buf is_nr nkey use_trans is_view is_ctor imm_len body ret_type.
    cenv.ce_ctor_exit_label = NONE /\
    (!cenv' Wv E.
       cenv_ptrs_in Wv cenv' /\ stmt_exits_in E cenv' NoLoop ==>
       fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv') Wv {} E
         (compile_stmts cenv' NoLoop
            (case ret_type of SOME t => t | NONE => BaseT BoolT) body)) ==>
    fuel_okS (\st. cenv_ptrs_below st.cs_next_var cenv) UNIV {} {}
      (compile_internal_function cenv params has_ret_buf is_nr nkey use_trans
         is_view is_ctor imm_len body ret_type)
Proof
  rpt gen_tac >> Cases_on `ret_type` >> (
  PURE_ONCE_REWRITE_TAC [compile_internal_function_def] >>
  PURE_REWRITE_TAC [optionTheory.option_case_def, comp_bind_return] >>
  BETA_TAC >> strip_tac >>
  (* the return-buffer parameter *)
  match_mp_tac fuel_okS_bind_keep >> rpt conj_tac
  >- MATCH_ACCEPT_TAC next_stable_cenv_ptrs_below
  >- (ok_tac >> fuel_auto [fuel_ok_emit_op] >> simp[is_terminator_def]) >>
  qx_gen_tac `rbv` >> BETA_TAC >>
  (* the user parameters' declarations *)
  match_mp_tac fuel_okS_bind_dep >>
  qexists_tac `\pr st. cenv_ptrs_below st.cs_next_var cenv /\
     EVERY (\p. !x. SND (SND p) = Var x ==> var_below st.cs_next_var x)
       (FST pr)` >>
  rpt conj_tac
  >- (ok_tac >> MATCH_ACCEPT_TAC fuel_ok_compile_internal_param_decls)
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
      drule compile_internal_param_decls_below >> strip_tac >> fs[] >>
      irule cenv_ptrs_below_le >> qexists_tac `st.cs_next_var` >> fs[]) >>
  qx_gen_tac `pr` >> BETA_TAC >>
  (* the return PC and the immutables base *)
  match_mp_tac fuel_okS_bind_keep >> rpt conj_tac
  >- MATCH_ACCEPT_TAC next_stable_caps
  >- (ok_tac >> irule fuel_ok_emit_op >> simp[is_terminator_def]) >>
  qx_gen_tac `rpc` >> BETA_TAC >>
  match_mp_tac fuel_okS_bind_keep >> rpt conj_tac
  >- MATCH_ACCEPT_TAC next_stable_caps
  >- (ok_tac >> fuel_auto [fuel_ok_compile_fixed_region_with_id]) >>
  qx_gen_tac `imm_opt` >> BETA_TAC >>
  (* materializing the parameters *)
  match_mp_tac fuel_okS_bind_dep >>
  qexists_tac `\c st. cenv_ptrs_below st.cs_next_var c /\
                      c.ce_ctor_exit_label = NONE` >>
  rpt conj_tac
  >- (ok_tac >> MATCH_ACCEPT_TAC fuel_ok_materialize_internal_params)
  >- (rpt gen_tac >> BETA_TAC >> strip_tac >>
      drule materialize_internal_params_ptrs >>
      impl_tac >- (fs[cenv_ptrs_below_def] >> metis_tac[]) >>
      strip_tac >> fs[]) >>
  qx_gen_tac `c` >> BETA_TAC >>
  ho_match_mp_tac fuel_okS_pre_conj >> strip_tac >>
  (* the return-value region, the lock, the body *)
  keep_tac >- (ok_tac >> fuel_auto [fuel_ok_compile_alloc_buffer]) >>
  keep_tac >- (ok_tac >> fuel_auto [fuel_ok_context_storage]) >>
  keep_tac
  >- (match_mp_tac fuel_okS_mono >>
      qexistsl_tac [`\st. cenv_ptrs_below st.cs_next_var
                      (c with <|ce_imm_alloca := imm_opt;
                                ce_alloca_locals := T|>)`,
                    `UNIV`, `{}`, `{}`] >>
      rpt conj_tac
      >- (first_x_assum irule >> fs[cenv_ptrs_in_def, stmt_exits_in_def]) >>
      simp[cenv_ptrs_below_def]) >>
  (* the epilogue *)
  ok_tac >> fuel_auto [fuel_ok_context_storage, fuel_ok_emit_inst_any] >>
  simp[])
QED
