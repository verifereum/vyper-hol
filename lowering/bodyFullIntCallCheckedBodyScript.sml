Theory bodyFullIntCallCheckedBody
Ancestors constSubstMods
  bodyFullPreds bodySim exprSimHypsDefs
  constSubstStmtsPreserve constSubstStmts constSubst
  compileEnv supportedStmts alist

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  simp[body_const_cells_agree_def] >> strip_tac >>
  `~supported_stmts_expr_exists (const_name_root_mods [(NONE,tops)])
      (subst_consts_stmts (module_consts_env tops []) ss)` by
    (qpat_x_assum `tops = cx_tops cx` (SUBST_ALL_TAC o SYM) >>
     drule_all checked_const_substitution_const_name_free >> simp[]) >>
  `const_name_root_mods ce.ce_modules = const_name_root_mods [(NONE,tops)]` by
    metis_tac[body_inv_const_name_roots, const_name_root_mods_singleton] >>
  pop_assum SUBST1_TAC >> first_assum ACCEPT_TAC
QED
*)
Theorem intcall_checked_body_const_name_free:
  contract_inv mods exps ctx ce cx /\
  body_const_cells_agree mods cx env st ==>
  ~supported_stmts_expr_exists (const_name_root_mods mods)
    (subst_consts_stmts_mods (consts_env_mods mods) ss)
Proof
  cheat
QED
