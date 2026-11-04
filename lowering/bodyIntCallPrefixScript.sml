(* Completed block history is preserved by recursive compiler consumers. *)
Theory bodyIntCallPrefix
Ancestors
  exprLoweringProps stmtLoweringMono fragExec moduleLowering abiDecoderAppend compileEnv context

Theorem compile_expr_cs_appends:
  cs_appends (compile_expr ce ty e)
Proof
  rw[cs_appends_def] >> drule (cj 1 compile_expr_grows) >> simp[]
QED

Theorem lower_value_compile_expr_cs_appends:
  cs_appends (lower_value compile_expr ce ty e)
Proof
  rw[cs_appends_def] >> drule (cj 2 compile_expr_grows) >> simp[]
QED

Theorem cs_mono_cs_appends:
  cs_mono m ==> cs_appends m
Proof
  simp[cs_mono_def, cs_appends_def] >> metis_tac[]
QED

Theorem compile_stmt_cs_appends:
  cs_appends (compile_stmt ce lc ty s)
Proof
  irule cs_mono_cs_appends >> simp[cj 1 compile_stmt_cs_mono]
QED

Theorem compile_stmts_cs_appends:
  cs_appends (compile_stmts ce lc ty ss)
Proof
  irule cs_mono_cs_appends >> simp[cj 2 compile_stmt_cs_mono]
QED

Theorem intcall_appends_check[local]:
  cs_appends (compile_expr ce ty (Call ann (IntCall fid) args dflt))
Proof
  simp[compile_expr_cs_appends]
QED

Theorem external_return_appends_check[local]:
  ce.ce_return_pc = NONE ==>
  cs_appends (compile_stmt ce lc ty (Return (SOME e)))
Proof
  simp[compile_stmt_cs_appends]
QED

val append_simps = [cs_appends_return, cs_appends_prims,
  cs_appends_emit_helpers, compile_stmts_cs_appends,
  cs_appends_abi_alloc_buffer, cs_appends_abi_clamp,
  cj 1 cs_appends_abi_decode_mutual];
val APPEND_BIND = ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp append_simps >> gen_tac >> BETA_TAC;

Theorem compile_decode_args_cs_appends:
  !xs ce off opc hi adj.
    cs_appends (compile_decode_args ce xs off opc hi adj)
Proof
  Induct >> simp[compile_decode_args_def, cs_appends_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  rename1 `compile_decode_args ce ((name, prim, dyn, sz, info)::xs) off opc hi adj` >>
  simp[compile_decode_args_def] >>
  IF_CASES_TAC
  >- (simp_tac pure_ss [LET_THM, comp_ignore_bind_def] >>
      BETA_TAC >> ntac 3 APPEND_BIND >>
      ho_match_mp_tac cs_appends_bind >> conj_tac
      >- (Cases_on `FLOOKUP ce.ce_vars name` >> simp[cs_appends_return] >>
          rename1 `_ = SOME loc` >>
          Cases_on `var_location_decode_operand loc` >> simp append_simps) >>
      gen_tac >> BETA_TAC >> simp[]) >>
  IF_CASES_TAC >>
  Cases_on `FLOOKUP ce.ce_vars name` >> simp[] >>
  rename1 `_ = SOME loc` >>
  Cases_on `var_location_decode_operand loc` >> simp[] >>
  rewrite_tac[comp_ignore_bind_def] >>
  rpt APPEND_BIND >> simp[]
QED

Theorem compile_register_positional_args_cs_appends:
  !xs ce off. cs_appends (compile_register_positional_args ce xs off)
Proof
  Induct >> simp[compile_register_positional_args_def, cs_appends_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  rename1 `compile_register_positional_args ce ((name, prim, dyn, sz, info)::xs) off` >>
  simp[compile_register_positional_args_def] >>
  Cases_on `FLOOKUP ce.ce_vars name` >> simp[] >>
  rename1 `_ = SOME loc` >>
  Cases_on `var_location_memory_size loc` >> simp[] >>
  rewrite_tac[comp_ignore_bind_def] >> ntac 2 APPEND_BIND >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[compile_decode_args_cs_appends] >>
  gen_tac >> BETA_TAC >> simp[]
QED

Theorem compile_nonreentrant_unlock_cs_appends:
  cs_appends (compile_nonreentrant_unlock key trans view)
Proof
  Cases_on `view` >> Cases_on `trans` >>
  simp[compile_nonreentrant_unlock_def, cs_appends_return, cs_appends_emit_helpers]
QED

Theorem compile_nonreentrant_lock_cs_appends:
  cs_appends (compile_nonreentrant_lock key trans view)
Proof
  Cases_on `trans` >> rewrite_tac[compile_nonreentrant_lock_def,
    comp_ignore_bind_def] >> ntac 4 APPEND_BIND >>
  Cases_on `view` >> simp append_simps
QED

Theorem cs_appends_get:
  cs_appends comp_get
Proof
  simp[cs_appends_def, comp_get_def, cs_extends_refl]
QED

Theorem compile_guarded_body_cs_appends:
  cs_appends (compile_guarded_body ce nr key trans view stmts ret)
Proof
  rewrite_tac[compile_guarded_body_def, comp_ignore_bind_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (Cases_on `nr` >> simp[compile_nonreentrant_lock_cs_appends,
                            cs_appends_return]) >>
  gen_tac >> BETA_TAC >> APPEND_BIND >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[cs_appends_get] >>
  gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[cs_appends_return] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (Cases_on `nr` >> simp[compile_nonreentrant_unlock_cs_appends,
                            cs_appends_return]) >>
  gen_tac >> BETA_TAC >> Cases_on `ret` >> simp append_simps
QED

Theorem compile_external_function_body_cs_appends:
  cs_appends (compile_external_function_body ce args nr key trans view stmts ret)
Proof
  rewrite_tac[compile_external_function_body_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[compile_register_positional_args_cs_appends] >>
  gen_tac >> BETA_TAC >> simp[compile_guarded_body_cs_appends]
QED

Theorem compile_fallback_body_cs_appends:
  cs_appends (compile_fallback_body ce pay nr key trans view stmts ret)
Proof
  rewrite_tac[compile_fallback_body_def, comp_ignore_bind_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (Cases_on `pay` >> simp[cs_appends_return] >>
      ntac 2 APPEND_BIND >> simp append_simps) >>
  gen_tac >> BETA_TAC >> simp[compile_guarded_body_cs_appends]
QED

Theorem compile_entry_checks_cs_appends:
  cs_appends (compile_entry_checks cds pay)
Proof
  rewrite_tac[compile_entry_checks_def, comp_ignore_bind_def] >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- (Cases_on `pay` >> simp[cs_appends_return] >>
      ntac 2 APPEND_BIND >> simp append_simps) >>
  gen_tac >> BETA_TAC >> IF_CASES_TAC >> simp[cs_appends_return] >>
  ntac 3 APPEND_BIND >> simp append_simps
QED

Theorem compile_external_fn_bodies_cs_appends:
  !xs. cs_appends (compile_external_fn_bodies xs)
Proof
  Induct >> simp[compile_external_fn_bodies_def, cs_appends_return] >>
  gen_tac >> PairCases_on `h` >> rewrite_tac[compile_external_fn_bodies_def,
    comp_ignore_bind_def] >> APPEND_BIND >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[compile_entry_checks_cs_appends] >>
  gen_tac >> BETA_TAC >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[compile_external_function_body_cs_appends] >>
  gen_tac >> BETA_TAC >> simp[]
QED

Theorem compile_selector_checks_cs_appends:
  !xs mid. cs_appends (compile_selector_checks mid xs)
Proof
  Induct >> simp[compile_selector_checks_def, cs_appends_return] >>
  rpt gen_tac >> PairCases_on `h` >>
  rewrite_tac[compile_selector_checks_def, comp_ignore_bind_def] >>
  ntac 7 APPEND_BIND >> simp[]
QED

Theorem compile_selector_dispatch_linear_cs_appends:
  cs_appends (compile_selector_dispatch_linear sels fallback)
Proof
  rewrite_tac[compile_selector_dispatch_linear_def, comp_ignore_bind_def] >>
  ntac 8 APPEND_BIND >>
  ho_match_mp_tac cs_appends_bind >> conj_tac
  >- simp[compile_selector_checks_cs_appends] >>
  gen_tac >> BETA_TAC >> simp append_simps
QED

Theorem compile_runtime_fallback_cs_appends:
  cs_appends
    (case fb of
       NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
     | SOME (ce, pay, nr, key, trans, view, stmts, ret) =>
         compile_fallback_body ce pay nr key trans view stmts ret)
Proof
  namedCases_on `fb` ["", "desc"] >> simp append_simps >>
  PairCases_on `desc` >>
  simp[compile_fallback_body_cs_appends]
QED

(* This is the Linear runtime prefix, stopping before internal functions.
   No definition is needed just to name this monadic subcomputation. *)
Theorem compile_linear_runtime_prefix_cs_appends:
  cs_appends
    (comp_bind (fresh_label "fallback") (\fallback.
       comp_ignore_bind (compile_selector_dispatch_linear sels fallback)
         (comp_ignore_bind (compile_external_fn_bodies externals)
           (comp_ignore_bind (new_block fallback)
             (case fb of
                NONE => emit_inst REVERT [Lit 0w; Lit 0w] []
              | SOME (ce, pay, nr, key, trans, view, stmts, ret) =>
                  compile_fallback_body ce pay nr key trans view stmts ret)))))
Proof
  APPEND_BIND >> irule cs_appends_ignore_bind >> conj_tac
  >- simp[compile_selector_dispatch_linear_cs_appends] >>
  irule cs_appends_ignore_bind >> conj_tac
  >- simp[compile_external_fn_bodies_cs_appends] >>
  irule cs_appends_ignore_bind >> simp[cs_appends_prims,
                                        compile_runtime_fallback_cs_appends]
QED
