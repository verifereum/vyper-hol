Theory sourceMeaningModules
Ancestors
  sourceMeaningDispatch sourceMeaningCall sourceMeaningCallDefs sourceMeaningDecl
  sourceMeaningPolicy sourceMeaningPolicyDecl sourceMeaningProgramDefs sourceMeaningDefs sourceMeaningRuntime
  sourceMeaningStmtDefs vyperInterpreter vyperState vyperContext vyperAST
  alist list option pair

(* Selection still uses source declaration meanings. The module identity only
   routes dispatch; it does not choose an executable body as its denotation. *)
Theorem source_meaning_lookup_module_transport:
  !ms ts. LIST_REL (source_meaning_decl_code tenv) ms ts ==>
  !src name vis. OPTREL
    (\(mut,nr,args,dms,ret,bms) (mut',nr',args',ds,ret',ss).
      mut = mut' /\ nr = nr' /\ args = args' /\ ret = ret' /\
      !cx. get_tenv cx = tenv ==>
        LIST_REL (\m e. eval_expr cx e =
          source_meaning_eval cx (\p. source_meaning_local (LAST p)) m) dms ds /\
        eval_stmts cx ss = source_meaning_execute cx bms)
    (source_meaning_lookup name vis ms) (lookup_function src name vis ts)
Proof
  Induct >> Cases_on `ts` >> simp[]
  >- (rpt gen_tac >> Cases_on `vis` >>
      simp[OPTREL_def, source_meaning_lookup_def, lookup_function_def,
        source_meaning_execute_def, source_meaning_run_def, Once evaluate_def]) >>
  gen_tac >> strip_tac >> rename1 `source_meaning_decl_code _ m tl` >>
  Cases_on `m` >> gvs[source_meaning_decl_code_def] >> rpt gen_tac >>
  simp[source_meaning_lookup_def, lookup_function_def] >>
  TRY (IF_CASES_TAC >> simp[]) >>
  Cases_on `vis` >> simp[lookup_function_def]
QED

(* Ordinary calls do not reinstall globals. Consequently all module code may
   be retained for the combined nominal environment without requiring the old
   single-module installation hypothesis. Deployment remains a separate phase. *)
Theorem source_meaning_invoke_modules_transport:
  ~cx.in_deploy /\
  LIST_REL (\m e. eval_expr cx e =
    source_meaning_eval cx (\p. source_meaning_local (LAST p)) m) dms ds /\
  eval_stmts cx ss = source_meaning_execute cx bms ==>
  call_external_function orc am cx nr mut (ts : toplevel list) modules args ds vals ss ret =
    source_meaning_invoke orc am cx meanings nr mut modules args dms vals bms ret
Proof
  strip_tac >> drule LIST_REL_LENGTH >> strip_tac >>
  drule source_meaning_defaults_drop >> strip_tac >>
  fs[call_external_function_def, source_meaning_invoke_def, source_meaning_result_eta]
QED

(* A successful source-selected imported external entry has exactly this API
   behavior. Linkage evidence supplies exports; derivations supply the body.
   No call to eval_expr/eval_stmts occurs in the source-side computation. *)
Theorem source_meaning_exported_call_transport:
  ALOOKUP am.sources tx.target = SOME modules /\
  ALOOKUP am.exports tx.target = SOME exports /\
  ALOOKUP exports tx.function_name = SOME src /\
  ALOOKUP modules (SOME src) = SOME tops /\
  LIST_REL (source_meaning_decl_code (type_env_all_modules modules)) meanings tops /\
  source_meaning_lookup tx.function_name External meanings =
    SOME (mut,nr,args,dms,ret,bms) ==>
  let cx = initial_evaluation_context am.sources am.layouts tx (SOME src) in
  call_external orc am tx =
    case source_meaning_invoke orc am cx meanings nr mut modules args dms tx.args bms ret of
      (INL v,am',rqs) => (INL v,finalize_pending_deletions am',rqs)
    | failure => failure
Proof
  strip_tac >> simp[] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx (SOME src)` >>
  `get_tenv cx = type_env_all_modules modules /\ ~cx.in_deploy` by
    simp[Abbr`cx`, get_tenv_def, initial_evaluation_context_def] >>
  drule source_meaning_lookup_module_transport >>
  disch_then (qspecl_then [`SOME src`,`tx.function_name`,`External`] mp_tac) >>
  simp[OPTREL_def] >> strip_tac >>
  rename1 `lookup_function _ _ _ _ = SOME runtime_entry` >>
  PairCases_on `runtime_entry` >> gvs[] >>
  rename1 `lookup_function (SOME src) tx.function_name External tops =
    SOME (mut,nr,args,ds,ret,ss)` >>
  first_x_assum drule >> strip_tac >>
  `call_external_function orc am cx nr mut tops modules args ds
      tx.args ss ret =
    source_meaning_invoke orc am cx meanings nr mut modules args dms tx.args bms ret` by
    (irule source_meaning_invoke_modules_transport >> simp[]) >>
  simp[call_external_def, find_function_module_def, lookup_exported_function_def,
    get_module_code_def, initial_evaluation_context_def, Abbr`cx`] >>
  gvs[initial_evaluation_context_def]
QED
