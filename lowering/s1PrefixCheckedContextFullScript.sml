(* The checked source module supplies the guard for both full judgments. *)
Theory s1PrefixCheckedContextFull
Ancestors
  bodyCallLiveness
  bodySimFullMain bodyFullPreds bodyLoopCalls typedCopyProducer alist

val _ = Parse.hide "body";

Theorem checked_context_full_guards:
  body_const_cells_agree [(NONE,tops)] cx env es ==>
  !ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
    struct_args_unique ts /\
    (!vis mut nr raw fn args dflts ret body.
      MEM (FunctionDecl vis mut nr raw fn args dflts ret body) ts ==>
      stmts_loop_calls_ok [(NONE,ts)]
        (subst_consts_stmts (module_consts_env ts []) body))
Proof
  disch_then (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_def]) >>
  rpt gen_tac >> strip_tac >> gvs[ALOOKUP_def] >>
  conj_tac
  >- (drule checked_contract_struct_args_unique >> simp[]) >>
  drule_then assume_tac checked_module_loop_calls_ok >>
  rpt strip_tac >>
  first_x_assum (drule_then assume_tac) >>
  drule_all checked_subst_consts_loop_calls_ok >> simp[]
QED

Theorem checked_context_full_exprs:
  body_const_cells_agree [(NONE,tops)] cx env es ==>
  (!a. EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
         (vyperTypeCallGraph$int_calls_expr a) ==> body_expr_full_ok cx a) /\
  (!xs. EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
          (vyperTypeCallGraph$int_calls_exprs xs) ==> body_exprs_full_ok cx xs)
Proof
  strip_tac >>
  drule_then assume_tac checked_context_full_guards >>
  drule_then assume_tac body_const_cells_agree_runtime_check >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    fs[body_const_cells_agree_def] >>
  conj_tac >> gen_tac >> disch_tac
  >- (match_mp_tac (cj 5 body_sim_full_mutual) >> gvs[] >> metis_tac[])
  >> match_mp_tac (cj 6 body_sim_full_mutual) >> gvs[] >> metis_tac[]
QED
