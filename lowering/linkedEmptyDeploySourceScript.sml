(* The checked linked source execution for a synthetic empty constructor. *)
Theory linkedEmptyDeploySource
Ancestors
  linkedEmptyDeployTrace linkedZeroImmutables ctorDeployLoweringArms
  ctorDeployLoweringNoCtor vyperTypeDeploymentSoundness vyperConstantsStorageFrame
  compileUnit compileVyper e2eModsDefs e2eDeployModsDefs e2eDefs
  vyperInterpreter vyperContext vyperState vyperABI alist list pair

Theorem linked_empty_deploy_source:
  classify_functions_unit mods exps = (exts,ints,fb,NONE,imp_ctors) /\
  check_contract F am.layouts tx.target mods = SOME art /\
  layouts_agree_mods mods exps am tx /\
  constructor_args_encode_mods mods tx args_bytes /\
  tx.function_name = "__init__" /\ value_transfer_ok tx am.accounts ==>
  tx.args = [] /\ args_bytes = [] /\
  ?installed. ALOOKUP installed.sources tx.target = SOME mods /\
    installed.accounts = process_deletions am.pending_deletions
      (accounts_after_transfer tx am.accounts) /\
    installed.tStorage = am.tStorage /\ installed.logs = am.logs /\
    immutables_section_rel_mods mods (account_immutables installed tx.target)
      (REPLICATE (imm_len_mods mods) 0w) /\
    (!orc gs. load_contract_trace orc gs am tx mods exps =
      (INL (installed,[]),[]))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?me mi mf. classify_functions (main_module mods) = (me,mi,mf,NONE)` by
    (Cases_on `FOLDR classify_function ([],[],NONE,NONE) (main_module mods)` >>
     PairCases_on `r` >> Cases_on `r2` >>
     fs[classify_functions_unit_def,classify_functions_def,LET_THM]) >>
  drule_then assume_tac no_ctor_lookup >>
  `tx.args = [] /\ args_bytes = []` by
    (gvs[constructor_args_encode_mods_def, LET_THM] >> EVAL_TAC) >>
  asm_rewrite_tac[] >>
  drule_then (qx_choose_then `imms` assume_tac) check_contract_initial_immutables >>
  qabbrev_tac `cx = deploy_evaluation_context_mods mods am tx` >>
  qabbrev_tac `start = am with <|immutables updated_by CONS (tx.target,imms);
      exports updated_by CONS (tx.target,exps)|>` >>
  `ALOOKUP cx.sources cx.txn.target = SOME mods /\
   ALOOKUP start.immutables cx.txn.target = SOME imms /\
   cx.txn.target = tx.target` by
    simp[Abbr `cx`, Abbr `start`, deploy_evaluation_context_mods_def,
         initial_evaluation_context_def] >>
  drule_all check_contract_evaluate_all_constants_trace >>
  disch_then (qx_choose_then `am_c` assume_tac) >>
  qpat_assum `cx.txn.target = tx.target` (fn target =>
    qpat_x_assum `evaluate_module_constants_trace _ _ cx.txn.target _ = _`
      (assume_tac o REWRITE_RULE [target])) >>
  `evaluate_all_constants cx start tx.target mods = SOME am_c` by
    simp[evaluate_all_constants_def,evaluate_module_constants_def] >>
  `am_c.pending_deletions = am.pending_deletions /\
   am_c.tStorage = am.tStorage /\ am_c.logs = am.logs` by
    (drule_then (mp_tac o Q.AP_TERM `\m. (m.pending_deletions,m.tStorage,m.logs)`)
       evaluate_all_constants_machine_frame >> simp[Abbr `start`]) >>
  qunabbrev_tac `cx` >> qunabbrev_tac `start` >>
  drule_all_then assume_tac linked_initialized_zero_immutables >>
  drule_all_then assume_tac load_contract_empty_ctor_trace >>
  qexists_tac `finalize_pending_deletions (am_c with
    <|accounts := accounts_after_transfer tx am.accounts;
      sources updated_by CONS (tx.target,mods)|>)` >>
  fs[finalize_pending_deletions_def, account_immutables_def]
QED
