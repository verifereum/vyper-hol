(* Entry boundaries for transaction-code independence. *)
Theory selfCodeFreeEntry
Ancestors
  selfCodeFreeInterpreter selfCodeFreeConstants selfCodeFreeContext
  selfCodeFreeInvariant selfCodeFreeSyntax vyperInterpreter vyperContext

val _ = Parse.hide "body";

Theorem call_external_function_self_code_free:
  self_code_free_context cx /\
  ~supported_exprs_exists is_self_code dflts /\
  ~supported_stmts_expr_exists is_self_code body /\
  (cx.in_deploy ==>
    evaluate_all_constants (cx with txn := (cx.txn with code := c)) am
      cx.txn.target mods = evaluate_all_constants cx am cx.txn.target mods) ==>
  call_external_function orc gobs am
    (cx with txn := (cx.txn with code := c)) nr mut ts mods args dflts vals body ret =
  call_external_function orc gobs am cx nr mut ts mods args dflts vals body ret
Proof
  strip_tac >>
  `eval_stmts (cx with txn := (cx.txn with code := c)) body =
   eval_stmts cx body` by metis_tac[eval_stmts_self_code_free] >>
  `!n. eval_exprs (cx with txn := (cx.txn with code := c)) (DROP n dflts) =
       eval_exprs cx (DROP n dflts)` by
    metis_tac[eval_exprs_self_code_free, supported_exprs_exclusion_DROP] >>
  simp[call_external_function_def, eval_external_defaults_def]
QED

Theorem singleton_sources_self_code_free:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  ~program_reads_self_code tops ==> self_code_free_context cx
Proof
  simp[self_code_free_context_def, get_module_code_def] >>
  strip_tac >> Cases_on `sid` >> simp[] >> metis_tac[]
QED

Theorem initial_context_txn_code:
  initial_evaluation_context srcs layouts (tx with code := c) sid =
  (initial_evaluation_context srcs layouts tx sid) with txn := (tx with code := c)
Proof
  simp[initial_evaluation_context_def, evaluation_context_component_equality]
QED

Theorem lookup_exported_function_txn_code[simp]:
  lookup_exported_function (cx with txn := (cx.txn with code := c)) am name =
  lookup_exported_function cx am name
Proof
  simp[lookup_exported_function_def]
QED
