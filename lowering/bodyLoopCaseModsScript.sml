(* Linked For dispatch at the statement-judgment boundary. *)
Theory bodyLoopCaseMods
Ancestors
  bodyFullPredsMods bodyForRangeCaseMods bodyForArrayFragMods

val _ = Parse.hide "body";

Theorem body_for_case_full_mods:
  !mods exps cx id typ it n body.
    (!tenv s tv t s1 vs t1 s2 u t2. tenv = get_tenv cx /\
      lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) /\
      eval_iterator cx it s1 = (INL vs,t1) /\
      check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s2 = (INL u,t2) ==>
      body_for_full_ok_mods mods exps cx tv id body vs) /\
    (!tenv s tv t. tenv = get_tenv cx /\
      lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) ==>
      body_iterator_full_ok_mods mods exps cx it) /\
    stmt_loop_calls_ok mods (For id typ it n body) ==>
    body_stmt_full_ok_mods mods exps cx (For id typ it n body)
Proof
  rpt gen_tac >> reverse (Cases_on `it`) >> strip_tac
  >- (irule body_for_range_case_full_mods >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  rewrite_tac[body_stmt_full_ok_mods_def] >> rpt gen_tac >> strip_tac >>
  irule compile_for_array_frag_full_mods >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bindings`, `env`, `env'`, `exps`, `mods`, `src`, `tops`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
