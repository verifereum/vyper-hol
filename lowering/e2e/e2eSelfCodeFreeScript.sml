(* A program that never reads self.code runs the same whatever code its
   transaction carries.

   The source semantics reads the transaction's code (cx.txn.code) only in
   evaluate_code_source, for slice(self.code, ...), which
   ~program_reads_self_code excludes.  The optimizer case of the top
   theorems uses this to run the lowering proof (whose entry relation pins
   the Venom state's code to tx.code) on the unoptimized code layout while
   the frame runs the optimized one.  The deployment also evaluates
   constant initialisers, which program_reads_self_code doesn't scan;
   supported_program excludes Constant declarations.

   TOP-LEVEL: call_external_self_code_free, load_contract_self_code_free.
 *)
Theory e2eSelfCodeFree
Ancestors
  e2eProducers supportedProgram vyperInterpreter selfCodeFreeEntry
  selfCodeFreeInvariant selfCodeFreeSyntax selfCodeFreeConstants vyperContext

Theorem call_external_self_code_free:
  !orc gobs am tx c tops.
    ALOOKUP am.sources tx.target = SOME [(NONE, tops)] /\
    ~program_reads_self_code tops ==>
    call_external orc gobs am (tx with code := c) =
    call_external orc gobs am tx
Proof
  rpt strip_tac >>
  simp[call_external_def, initial_context_txn_code] >>
  qabbrev_tac `cx = initial_evaluation_context am.sources am.layouts tx
    (find_function_module am tx.target tx.function_name)` >>
  `tx = cx.txn` by simp[Abbr `cx`, initial_evaluation_context_def] >>
  qpat_assum `tx = cx.txn` (fn th =>
    simp[Once th, selfCodeFreeContextTheory.get_self_code_txn_code,
         selfCodeFreeContextTheory.get_module_code_txn_code]) >>
  `self_code_free_context cx` by
    (irule singleton_sources_self_code_free >> qexists `tops` >>
     simp[Abbr `cx`, initial_evaluation_context_def]) >>
  `!sid. get_module_code cx sid = ALOOKUP [(NONE,tops)] sid` by
    simp[get_module_code_def, Abbr `cx`, initial_evaluation_context_def] >>
  Cases_on `find_function_module am cx.txn.target cx.txn.function_name` >>
  simp[get_self_code_def] >>
  Cases_on `lookup_exported_function cx am cx.txn.function_name` >> simp[] >>
  rename1 `lookup_exported_function _ _ _ = SOME fn` >>
  PairCases_on `fn` >> simp[] >>
  `~supported_exprs_exists is_self_code fn3 /\
   ~supported_stmts_expr_exists is_self_code fn5` by
    (irule lookup_exported_function_self_code_free >>
     goal_assum (drule_at Any) >>
     gvs[self_code_free_context_def]) >>
  `call_external_function orc gobs am
     (cx with txn := (cx.txn with code := c)) fn1 fn0 tops
     [(NONE,tops)] fn2 fn3 cx.txn.args fn5 fn4 =
   call_external_function orc gobs am cx fn1 fn0 tops
     [(NONE,tops)] fn2 fn3 cx.txn.args fn5 fn4` by
    (irule call_external_function_self_code_free >>
     simp[Abbr `cx`, initial_evaluation_context_def]) >> simp[]
QED

Theorem load_contract_self_code_free:
  !orc gobs am tx c tops.
    supported_program tops /\ ~program_reads_self_code tops ==>
    load_contract orc gobs am (tx with code := c) [(NONE, tops)] [] =
    load_contract orc gobs am tx [(NONE, tops)] []
Proof
  rpt strip_tac >>
  simp[load_contract_def] >>
  Cases_on `initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)]` >>
  simp[] >>
  Cases_on `lookup_function NONE tx.function_name Deploy tops` >> simp[] >>
  rename1 `lookup_function _ _ _ _ = SOME fn` >>
  PairCases_on `fn` >> simp[] >>
  qabbrev_tac `cx = initial_evaluation_context
    ((tx.target,[(NONE,tops)])::am.sources) am.layouts
    (tx with created_in_tx := T) NONE with in_deploy := T` >>
  `initial_evaluation_context ((tx.target,[(NONE,tops)])::am.sources) am.layouts
     (tx with <|code := c; created_in_tx := T|>) NONE with in_deploy := T =
   cx with txn := (cx.txn with code := c)` by
    simp[Abbr `cx`, initial_evaluation_context_def,
         evaluation_context_component_equality, call_txn_component_equality] >>
  simp[] >>
  `self_code_free_context cx` by
    (irule singleton_sources_self_code_free >> qexists `tops` >>
     simp[Abbr `cx`, initial_evaluation_context_def]) >>
  drule_all lookup_function_self_code_free >> strip_tac >>
  qmatch_goalsub_abbrev_tac `call_external_function orc gobs am1 _ _ _ _ _ _ _ _ _ _` >>
  `call_external_function orc gobs am1
      (cx with txn := (cx.txn with code := c)) fn1 fn0 tops
      [(NONE,tops)] fn2 fn3 tx.args fn5 fn4 =
   call_external_function orc gobs am1 cx fn1 fn0 tops
      [(NONE,tops)] fn2 fn3 tx.args fn5 fn4` by
    (irule call_external_function_self_code_free >> simp[] >>
     strip_tac >> irule supported_program_constants_context_cong >> simp[]) >> simp[]
QED
