Theory callCodeTraceFromEval
Ancestors
  vyperInterpreter vyperContext vyperState alist bodyStorageCases e2eProducers

(* The runtime entry wrapper does not evaluate module constants. Once the
   default and body actions agree, so do all success and rollback traces. *)
Theorem runtime_function_trace_code_update[local]:
  ~cx.in_deploy /\
  eval_exprs (cx with txn := (cx.txn with code := c))
    (DROP (LENGTH ds - (LENGTH args - LENGTH vals)) ds) =
  eval_exprs cx (DROP (LENGTH ds - (LENGTH args - LENGTH vals)) ds) /\
  eval_stmts (cx with txn := (cx.txn with code := c)) ss = eval_stmts cx ss ==>
  call_external_function_trace orc gobs am
    (cx with txn := (cx.txn with code := c)) nr mut ts mods args ds vals ss ret =
  call_external_function_trace orc gobs am cx nr mut ts mods args ds vals ss ret
Proof
  strip_tac >>
  `eval_external_defaults (cx with txn := (cx.txn with code := c))
      (DROP (LENGTH ds - (LENGTH args - LENGTH vals)) ds) =
   eval_external_defaults cx (DROP (LENGTH ds - (LENGTH args - LENGTH vals)) ds)`
     by (asm_rewrite_tac [FUN_EQ_THM, eval_external_defaults_run]) >>
  gvs[call_external_function_trace_def, send_call_value_def,
      check_not_static_def, LET_THM]
QED

Theorem initial_context_code_update[local]:
  initial_evaluation_context srcs layouts (tx with code := c) sid =
    ((initial_evaluation_context srcs layouts tx sid) with txn :=
      ((initial_evaluation_context srcs layouts tx sid).txn with code := c))
Proof
  simp[initial_evaluation_context_def]
QED

Theorem initial_context_runtime_fields[local]:
  (initial_evaluation_context srcs layouts tx sid).txn = tx /\
  ~(initial_evaluation_context srcs layouts tx sid).in_deploy
Proof
  simp[initial_evaluation_context_def]
QED

Theorem singleton_runtime_module[local]:
  ALOOKUP srcs tx.target = SOME [(NONE,tops)] ==>
  get_module_code (initial_evaluation_context srcs layouts tx sid) mid =
    if mid = NONE then SOME tops else NONE
Proof
  simp[get_module_code_def, initial_evaluation_context_def, ALOOKUP_def]
QED

Theorem singleton_runtime_lookup[local]:
  ALOOKUP am.sources tx.target = SOME [(NONE,tops)] ==>
  lookup_exported_function (initial_evaluation_context am.sources am.layouts tx sid)
    am tx.function_name =
  if find_function_module am tx.target tx.function_name = NONE then
    lookup_function NONE tx.function_name External tops
  else NONE
Proof
  strip_tac >> drule_then assume_tac singleton_runtime_module >>
  Cases_on `ALOOKUP am.exports tx.target` >>
  simp[find_function_module_def, lookup_exported_function_def,
       initial_context_runtime_fields, get_self_code_def] >>
  rename1 `ALOOKUP am.exports tx.target = SOME exps` >>
  Cases_on `ALOOKUP exps tx.function_name` >> simp[]
QED

Theorem call_external_trace_code_update_from_eval:
  ALOOKUP am.sources tx.target = SOME [(NONE,tops)] /\
  ~program_reads_self_code tops /\
  (!sid name vis mut nr args ds rt ss.
     lookup_function sid name vis tops = SOME (mut,nr,args,ds,rt,ss) ==>
     ~supported_exprs_exists is_self_code ds /\
     ~supported_stmts_expr_exists is_self_code ss) /\
  (!sid cx cx'.
     cx = initial_evaluation_context am.sources am.layouts tx sid /\
     cx' = (cx with txn := (cx.txn with code := c)) ==>
     (!ds. ~supported_exprs_exists is_self_code ds ==>
           eval_exprs cx' ds = eval_exprs cx ds) /\
     (!ss. ~supported_stmts_expr_exists is_self_code ss ==>
           eval_stmts cx' ss = eval_stmts cx ss)) ==>
  call_external_trace (SOME os) gobs am (tx with code := c) =
  call_external_trace (SOME os) gobs am tx
Proof
  simp_tac bool_ss [] >>
  strip_tac >>
  drule_then assume_tac singleton_runtime_module >>
  drule_then assume_tac singleton_runtime_lookup >>
  drule_then assume_tac
    (SRULE [] (Q.INST [`tx` |-> `tx with code := c`] singleton_runtime_module)) >>
  drule_then assume_tac
    (SRULE [] (Q.INST [`tx` |-> `tx with code := c`] singleton_runtime_lookup)) >>
  Cases_on `find_function_module am tx.target tx.function_name` >>
  simp[call_external_trace_def, LET_THM, get_self_code_def] >>
  Cases_on `lookup_function NONE tx.function_name External tops` >> simp[] >>
  rename1 `lookup_function NONE tx.function_name External tops = SOME entry` >>
  PairCases_on `entry` >> gvs[] >>
  rename1 `lookup_function NONE tx.function_name External tops =
           SOME (mut,nr,args,ds,ret,ss)` >>
  qpat_x_assum `!sid name vis mut nr args ds rt ss. _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!sid. (!ds. _ ==> eval_exprs _ ds = _) /\ _`
    (qspec_then `NONE` strip_assume_tac) >>
  `call_external_function_trace (SOME os) gobs am
      (initial_evaluation_context am.sources am.layouts (tx with code := c) NONE)
      nr mut tops [(NONE,tops)] args ds tx.args ss ret =
   call_external_function_trace (SOME os) gobs am
      (initial_evaluation_context am.sources am.layouts tx NONE)
      nr mut tops [(NONE,tops)] args ds tx.args ss ret`
    by (rewrite_tac [initial_context_code_update] >>
        irule runtime_function_trace_code_update >>
        simp[initial_context_runtime_fields, supported_exprs_exists_DROP]) >>
  simp[]
QED
