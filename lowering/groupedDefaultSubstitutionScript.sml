Theory groupedDefaultSubstitution
Ancestors
  e2eDefs compileVyper constSubstCorrect vyperInterpreter vyperState
  vyperTypeContract list finite_map alist

Theorem grouped_substituted_defaults_eval:
  lower_vyper_runtime_unit tops policy = SOME unit /\
  source_typing_ok tops am tx /\ source_deployment_rel tops am tx /\
  check_contract F am.layouts tx.target [(NONE,tops)] = SOME art /\
  well_typed_exprs (artifact_env art [(NONE,tops)] NONE) es /\
  s.immutables = am.immutables ==>
  eval_exprs (initial_evaluation_context am.sources am.layouts tx NONE) es s =
  eval_exprs (initial_evaluation_context am.sources am.layouts tx NONE)
    (subst_consts_exprs (module_consts_env tops []) es) s
Proof
  strip_tac >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  drule_all lower_vyper_runtime_unit_consts_guard >> strip_tac >>
  drule source_typing_ok_consts_ready >>
  disch_then (qx_choosel_then [`artifact`,`constants`] strip_assume_tac) >>
  `artifact = art` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `artifact = art` SUBST_ALL_TAC >>
  `ALOOKUP am.sources tx.target = SOME [(NONE,tops)]` by fs[source_deployment_rel_def] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx NONE` >>
  mp_tac (Q.INST [`cx` |-> `cx`, `mods` |-> `[(NONE,tops)]`, `artifact` |-> `art`,
    `imms` |-> `account_immutables am tx.target`, `sc` |-> `[]`,
    `current_src` |-> `NONE:num option`, `A` |-> `constants`]
    checked_module_consts_subst_context) >>
  impl_tac >- simp[Abbr `cx`, initial_evaluation_context_def] >>
  disch_then (qx_choose_then `roots` strip_assume_tac) >>
  `const_cells_agree roots s` by
    (qpat_assum `const_cells_agree roots (initial_state am [])`
       (mp_tac o SIMP_RULE (srw_ss()) [const_cells_agree_def, initial_state_def]) >>
     asm_rewrite_tac[const_cells_agree_def]) >>
  `const_subst_exprs_ok roots cx (artifact_env art [(NONE,tops)] NONE)
    (module_consts_env tops []) es` by
    (qpat_assum `const_subst_context _ _ _ _ _ _` (fn context =>
       let
         val elements = MATCH_MP (Q.SPECL [`module_consts_env tops []`,`es`]
           (cj 3 const_subst_structural)) context
       in
         ACCEPT_TAC (MATCH_MP (Q.SPEC `es` const_subst_exprs_from_elements)
           (CONJ context elements))
       end)) >>
  qpat_assum `const_subst_exprs_ok _ _ _ _ _`
    (mp_tac o REWRITE_RULE [const_subst_exprs_ok_def]) >>
  asm_rewrite_tac[] >> disch_then irule >> first_assum ACCEPT_TAC
QED
