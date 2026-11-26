(* Lift the compiled linked Range fragment to the statement judgment. *)
Theory bodyForRangeCaseMods
Ancestors
  bodyFullPredsMods bodyForRangeFragMods

val _ = Parse.hide "body";

Theorem body_for_range_case_full_mods:
  !mods exps cx id typ e1 e2 bound body.
    (!tenv s tv t. tenv = get_tenv cx /\
      lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) ==>
      body_iterator_full_ok_mods mods exps cx (Range e1 e2)) /\
    (!tenv s tv t s1 vs t1 s2 u t2. tenv = get_tenv cx /\
      lift_option_type (evaluate_type tenv typ) "For evaluate_type" s = (INL tv,t) /\
      eval_iterator cx (Range e1 e2) s1 = (INL vs,t1) /\
      check (compatible_bound (Dynamic bound) (LENGTH vs)) "For too long" s2 = (INL u,t2) ==>
      body_for_full_ok_mods mods exps cx tv id body vs) ==>
    body_stmt_full_ok_mods mods exps cx (For id typ (Range e1 e2) bound body)
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[body_stmt_full_ok_mods_def] >> rpt gen_tac >> strip_tac >>
  irule compile_for_range_frag_full_mods >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bindings`, `env`, `env'`, `exps`, `mods`, `src`, `tops`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
