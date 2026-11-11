(* Source endpoint interfaces for the external-call joint leaf.
   Source-invariant preservation is already exported as
   exprSimSource.expr_body_pre_eval_result; only the immutable frame is new. *)
Theory bodyIntCallFamCallExtSource
Ancestors
  bodyIntCallJointCallSource exprSimSource exprSimExtCallCase
  supportedExprs vyperInterpreter vyperState list rich_list
Libs
  monadsyntax

Theorem extcall_pure_args_immutables:
  supported_pure_exprs tops args /\
  eval_expr cx (Call ann (ExtCall stat skip sig opts) args dflt) es = (res,ee) ==>
  ee.immutables = es.immutables
Proof
  strip_tac >>
  `supported_pure_exprs tops (TAKE 1 args) /\
   supported_pure_exprs tops (TAKE (LENGTH (FST (SND sig))) (DROP 1 args)) /\
   supported_pure_exprs tops (DROP (1 + LENGTH (FST (SND sig))) args)` by
    (fs[supported_pure_exprs_every, EVERY_TAKE, EVERY_DROP]) >>
  gvs[eval_extcall_stages, bind_def, AllCaseEqs()] >>
  imp_res_tac read_results_state >> gvs[] >>
  imp_res_tac (cj 2 intcall_pure_immutables_mutual) >>
  imp_res_tac intcall_pure_results_immutables >>
  imp_res_tac eval_ext_call_preserves_non_accounts >> gvs[]
QED

Theorem send_pure_args_immutables:
  supported_pure_exprs tops args /\
  eval_expr cx (Call ann (Send has_gas) args dflt) es = (res,ee) ==>
  ee.immutables = es.immutables
Proof
  strip_tac >>
  gvs[Once evaluate_def, type_check_def, assert_def, bind_def,
      ignore_bind_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac (cj 2 intcall_pure_immutables_mutual) >>
  imp_res_tac eval_send_preserves_non_accounts >> gvs[]
QED

Theorem supported_extcall_immutables:
  supported_expr tops (Call ann (ExtCall stat skip sig opts) args dflt) /\
  eval_expr cx (Call ann (ExtCall stat skip sig opts) args dflt) es = (res,ee) ==>
  ee.immutables = es.immutables
Proof
  strip_tac >>
  `supported_pure_exprs tops args` suffices_by
    (strip_tac >> drule_all extcall_pure_args_immutables >> simp[]) >>
  gvs[supported_expr_def, supported_pure_expr_def] >>
  PairCases_on `sig` >> Cases_on `dflt` >>
  gvs[supported_effect_expr_def]
QED

Theorem supported_send_immutables:
  supported_expr tops (Call ann (Send has_gas) args dflt) /\
  eval_expr cx (Call ann (Send has_gas) args dflt) es = (res,ee) ==>
  ee.immutables = es.immutables
Proof
  strip_tac >>
  `supported_pure_exprs tops args` suffices_by
    (strip_tac >> drule_all send_pure_args_immutables >> simp[]) >>
  gvs[supported_expr_def, supported_pure_expr_def] >>
  Cases_on `ann` >> Cases_on `has_gas` >> Cases_on `dflt` >>
  Cases_on `args` >> gvs[supported_effect_expr_def] >>
  rename1 `h::rest` >> Cases_on `rest` >> gvs[supported_effect_expr_def] >>
  rename1 `h::h'::rest` >> Cases_on `rest` >>
  gvs[supported_effect_expr_def, supported_pure_expr_def] >>
  rename1 `h::h'::h''::rest` >> Cases_on `rest` >>
  gvs[supported_effect_expr_def, supported_pure_expr_def]
QED
