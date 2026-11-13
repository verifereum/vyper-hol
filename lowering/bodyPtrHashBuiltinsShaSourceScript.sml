(* Source outcome consumption and implicit-GAS exceptional summaries. *)
Theory bodyPtrHashBuiltinsShaSource
Ancestors exprSimHash exprLoweringProps compileEnv loweringStateRelDefs vyperState vyperInterpreter
  gasSummaryComposePtr fragGasPathPtr list rich_list

Theorem hash_counted_exit_summary:
  (!tail. source (ee with gas_obs := tail) =
    (res,ef with gas_obs := tail)) /\ ef.gas_obs = [] /\
  gas_path_ptr D 0 ctx fn PG G tn s n Gf tf rr /\
  exit_result rr /\ R res ef (Gf,tf) rr ==>
  gas_summary_ptr_at D (ctx,fn) PG (REPLICATE n F) source (ee,s,G,tn) Q R
Proof
  strip_tac >> rewrite_tac[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`res`, `ef`, `Gf`, `tf`, `rr`] >>
  conj_tac
  >- (irule gas_marked_exec_ptr_no_source_read >> simp[]) >>
  `ef with gas_obs := [] = ef` by
    simp[evaluation_state_component_equality] >> simp[]
QED

Theorem hash_sha256_source_success:
  stmt_state_rel ctx fn cenv cx ee s /\
  builtin_result cx ee.accounts ann Sha256 tys [v] = INL r /\
  s.vs_outcomes = outcome::rest /\ outcome.co_success ==>
  !tail.
  (case builtin_result cx (ee with gas_obs := tail).accounts ann Sha256 tys [v] of
     INR exc => (INR exc,ee with gas_obs := tail)
   | INL w => (do precompile_call_success Sha256; return (Value w) od)
       (ee with gas_obs := tail)) =
  (INL (Value r),(ee with outcomes := SOME rest) with gas_obs := tail)
Proof
  strip_tac >>
  `ee.outcomes = SOME s.vs_outcomes` by
    fs[stmt_state_rel_def, state_rel_def] >>
  simp[ignore_bind_def, bind_def, sha256_source_outcome_step, return_def]
QED

Theorem hash_sha256_source_failure:
  stmt_state_rel ctx fn cenv cx ee s /\ ee.gas_obs = [] /\
  builtin_result cx ee.accounts ann Sha256 tys [v] = INL r /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) ==>
  ?ef. ef = (case s.vs_outcomes of [] => ee
                        | outcome::rest => ee with outcomes := SOME rest) /\
    ef.gas_obs = [] /\
    !tail.
    (case builtin_result cx (ee with gas_obs := tail).accounts ann Sha256 tys [v] of
       INR exc => (INR exc,ee with gas_obs := tail)
     | INL w => (do precompile_call_success Sha256; return (Value w) od)
         (ee with gas_obs := tail)) =
    (INR (Error (RuntimeError "precompile failed")),ef with gas_obs := tail)
Proof
  strip_tac >>
  `ee.outcomes = SOME s.vs_outcomes` by
    fs[stmt_state_rel_def, state_rel_def] >>
  Cases_on `s.vs_outcomes`
  >- (qexists_tac `ee` >>
      simp[ignore_bind_def, bind_def, sha256_source_outcome_step]) >>
  rename1 `s.vs_outcomes = outcome::rest` >>
  qexists_tac `ee with outcomes := SOME rest` >>
  gvs[ignore_bind_def, bind_def, sha256_source_outcome_step, return_def]
QED

(* Shared exceptional packaging for both fixed and dynamic SHA paths. *)
Theorem hash_sha256_abort_summary:
  stmt_state_rel ctx fn cenv cx ee s /\ ee.gas_obs = [] /\
  builtin_result cx ee.accounts ann Sha256 tys [v] = INL r /\
  ~(?outcome rest. s.vs_outcomes = outcome::rest /\ outcome.co_success) /\
  gas_path_ptr D 0 ctx fn PG G tn s 1 Gf tf (Abort Revert_abort t) ==>
  gas_summary_ptr_at D (ctx,fn) PG [F]
    (\es'. case builtin_result cx es'.accounts ann Sha256 tys [v] of
       INR exc => (INR exc,es')
     | INL w => (do precompile_call_success Sha256; return (Value w) od) es')
    (ee,s,G,tn) Q (\res ef gt rr. expr_exit res rr)
Proof
  strip_tac >> drule_all hash_sha256_source_failure >> strip_tac >>
  `REPLICATE 1 F = [F]` by EVAL_TAC >>
  pop_assum (fn th => once_rewrite_tac[GSYM th]) >>
  irule hash_counted_exit_summary >>
  first_assum (irule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`INR (Error (RuntimeError "precompile failed"))`, `ef`] >>
  simp[fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def]
QED
