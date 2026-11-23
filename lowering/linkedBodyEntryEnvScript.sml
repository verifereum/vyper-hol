(* The shared contract tables are independent of a selected entry's locals. *)
Theory linkedBodyEntryEnv
Ancestors
  bodyInvSplit compileUnit bodySim bodyExprPreFacts allocLimitsProps
  compileVyper compileEnv pair

Theorem contract_inv_build_compile_env_unit:
  contract_inv mods exps ctx ce cx /\ (vis = Deploy <=> cx.in_deploy) ==>
  contract_inv mods exps ctx
    (build_compile_env_unit mods src vis mut name args ret ss T
      with ce_target := ce.ce_target) cx
Proof
  simp[contract_inv_def, cenv_module_pins_mods_def, immutable_section_layout_mods_def,
       build_compile_env_unit_def, pairTheory.ELIM_UNCURRY] >>
  strip_tac >> fs[] >> rpt conj_tac
  >- (qpat_assum `!src tops. ALOOKUP mods src = SOME tops ==> _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (qpat_assum `ce.ce_module_vars = _` (SUBST1_TAC o SYM) >>
      first_assum ACCEPT_TAC)
  >> first_assum ACCEPT_TAC
QED

Theorem stmts_exprs_ok_entry_target:
  stmts_exprs_ok (ce with ce_target := target) ss <=> stmts_exprs_ok ce ss
Proof
  irule stmts_exprs_ok_agree >> simp[alloc_env_agree_def, return_buffer_ok_def]
QED
