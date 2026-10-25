(*
 * Soundness of the checker's constants fold against deployment.
 *
 * TOP-LEVEL:
 * - constant_value_eval_expr
 * - constants_fold_evaluate_all_constants
 * - check_contract_evaluate_all_constants
 *
 * Helper:
 * - get_tenv_constant_context, get_tenv_sources
 * - evaluate_builtin_constant_context, evaluate_type_builtin_constant_context
 * - constant_length_toplevel_array_length, merge_constants_immutables
 * - constants_fold_module_constants_env
 *)

Theory vyperTypeConstantFold
Ancestors
  list finite_map alist option pair
  vyperAST vyperValue vyperState vyperContext vyperInterpreter
  vyperTypeContract

(* ===== Context independence of constant builtins ===== *)

Theorem get_tenv_constant_context:
  get_tenv (constant_context mods) = type_env_all_modules mods
Proof
  simp[get_tenv_def, constant_context_def]
QED

(* Helper: the constant builtins read the context only through get_tenv, and
   never the accounts. *)
Theorem evaluate_builtin_constant_context:
  !bt cx mods acc ty tys vs.
  constant_builtin bt /\ get_tenv cx = type_env_all_modules mods ==>
  evaluate_builtin cx acc ty bt tys vs =
  evaluate_builtin (constant_context mods) empty_accounts ty bt tys vs
Proof
  rpt gen_tac >> Cases_on `bt` >>
  simp[constant_builtin_def, evaluate_builtin_def, get_tenv_constant_context]
QED

Theorem evaluate_type_builtin_constant_context:
  !tb cx mods typ vs.
  constant_type_builtin tb /\ get_tenv cx = type_env_all_modules mods ==>
  evaluate_type_builtin cx tb typ vs =
  evaluate_type_builtin (constant_context mods) tb typ vs
Proof
  rpt gen_tac >> Cases_on `tb` >> simp[constant_type_builtin_def] >>
  Cases_on `vs` >>
  simp[evaluate_type_builtin_def, get_tenv_constant_context]
QED

Theorem constant_length_toplevel_array_length:
  !v n cx st.
  constant_length v = SOME n ==>
  toplevel_array_length cx (Value v) st = (INL n, st)
Proof
  rpt gen_tac >> Cases_on `v` >> simp[constant_length_def] >>
  TRY (rename1 `ArrayV av` >> Cases_on `av`) >>
  rw[constant_length_def, toplevel_array_length_def, return_def]
QED

(* ===== Expression soundness ===== *)

Theorem get_tenv_sources:
  ALOOKUP cx.sources cx.txn.target = SOME mods ==>
  get_tenv cx = type_env_all_modules mods
Proof
  simp[get_tenv_def]
QED

(* TOP-LEVEL: a folded constant value is what eval_expr returns, without
   changing the state, in any context whose contract code is mods and any
   state whose immutables for the contract are imms. *)
Theorem constant_value_eval_expr:
  (!mods imms e v cx st.
     constant_value mods imms e = SOME v /\
     ALOOKUP cx.sources cx.txn.target = SOME mods /\
     ALOOKUP st.immutables cx.txn.target = SOME imms ==>
     eval_expr cx e st = (INL (Value v), st)) /\
  (!mods imms es vs cx st.
     constant_values mods imms es = SOME vs /\
     ALOOKUP cx.sources cx.txn.target = SOME mods /\
     ALOOKUP st.immutables cx.txn.target = SOME imms ==>
     eval_exprs cx es st = (INL vs, st) /\
     LIST_REL (\e v. eval_expr cx e st = (INL (Value v), st)) es vs)
Proof
  ho_match_mp_tac constant_value_ind >>
  rpt strip_tac >>
  gvs[constant_value_def, AllCaseEqs(), OPTION_MAP_EQ_SOME] >>
  imp_res_tac get_tenv_sources
  >~ [`TopLevelName`]
  >- simp[Once evaluate_def, lookup_global_def, bind_def, return_def,
          lift_option_type_def, get_module_code_def, get_immutables_def,
          get_address_immutables_def]
  >~ [`Literal`] >- simp[Once evaluate_def, return_def]
  >~ [`StructLit`]
  >- (first_x_assum drule_all >> strip_tac >>
      rename1 `StructLit _ nsid kes` >> PairCases_on `nsid` >>
      simp[Once evaluate_def, bind_def, return_def])
  >~ [`Subscript`]
  >- (first_x_assum drule_all >> last_x_assum drule_all >> rpt strip_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
           lift_option_type_def, lift_sum_def] >>
      Cases_on `v2` >> simp[check_array_bounds_def, return_def])
  >~ [`Attribute`]
  >- (first_x_assum drule_all >> strip_tac >>
      simp[Once evaluate_def, bind_def, return_def, lift_sum_def])
  >~ [`Builtin _ Len`]
  >- (first_x_assum drule_all >> strip_tac >>
      gvs[builtin_args_length_ok_def, LENGTH_EQ_NUM_compute] >>
      drule_then (qspecl_then [`cx`,`st`] assume_tac)
        constant_length_toplevel_array_length >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
           type_check_def, assert_def, builtin_args_length_ok_def])
  >>~- ([`Builtin`], first_x_assum drule_all >> strip_tac >>
      FIRST [
        qpat_assum `evaluate_membership _ _ _ _ = INL _` kall_tac >>
        gvs[] >>
        simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
             type_check_def, assert_def, lift_option_type_def, lift_sum_def],
      qspecl_then [`bt`,`cx`,`mods`,`st.accounts`,`ty`,`MAP expr_type es`,`vs`] mp_tac
        evaluate_builtin_constant_context >>
      simp[] >> strip_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
           type_check_def, assert_def, get_accounts_def, lift_sum_def]])
  >~ [`TypeBuiltin`]
  >- (first_x_assum drule_all >> strip_tac >>
      rename1 `TypeBuiltin _ tb typ es` >>
      qspecl_then [`tb`,`cx`,`mods`,`typ`,`vs`] mp_tac
        evaluate_type_builtin_constant_context >>
      simp[] >> strip_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, return_def,
           type_check_def, assert_def, lift_sum_def])
  >- simp[Once evaluate_def, return_def] >>
  first_x_assum drule_all >> last_x_assum drule_all >> rpt strip_tac >>
  simp[Once evaluate_def, bind_def, return_def, materialise_def]
QED

(* ===== Fold soundness ===== *)

Theorem merge_constants_immutables:
  ALOOKUP am.immutables addr = SOME imms ==>
  ALOOKUP (merge_constants addr src cenv am).immutables addr =
    SOME (merge_constant_imms src cenv imms)
Proof
  simp[merge_constants_def, merge_constant_imms_def]
QED

Theorem constants_fold_module_constants_env:
  !mods imms src ts acc cenv cx am addr.
    constants_fold_module mods imms src ts acc = SOME cenv /\
    cx.txn.target = addr /\
    ALOOKUP cx.sources addr = SOME mods /\
    ALOOKUP am.immutables addr = SOME imms ==>
    constants_env cx am addr src ts acc = SOME cenv
Proof
  ho_match_mp_tac constants_fold_module_ind >>
  rw[constants_fold_module_def, constants_env_def] >>
  gvs[AllCaseEqs()] >>
  `get_tenv cx = type_env_all_modules mods` by simp[get_tenv_def] >>
  qmatch_goalsub_abbrev_tac `eval_expr cx e st` >>
  `eval_expr cx e st = (INL (Value v), st)` by
    (irule (CONJUNCT1 constant_value_eval_expr) >>
     qexistsl [`merge_constant_imms src acc imms`,`mods`] >>
     simp[Abbr `st`, initial_state_def, merge_constants_immutables]) >>
  simp[]
QED

(* TOP-LEVEL: when the checker's fold succeeds, so does deployment's, leaving
   the same immutables for the contract. *)
Theorem constants_fold_evaluate_all_constants:
  !rest imms am imms'.
    constants_fold mods imms rest = SOME imms' /\
    cx.txn.target = addr /\
    ALOOKUP cx.sources addr = SOME mods /\
    ALOOKUP am.immutables addr = SOME imms ==>
    ?am_c.
      evaluate_all_constants cx am addr rest = SOME am_c /\
      ALOOKUP am_c.immutables addr = SOME imms'
Proof
  Induct >- rw[constants_fold_def, evaluate_all_constants_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  rw[constants_fold_def, evaluate_all_constants_def] >>
  gvs[AllCaseEqs()] >>
  `constants_env (set_current_module cx h0) am cx.txn.target h0 h1 FEMPTY =
     SOME cenv` by
    (irule constants_fold_module_constants_env >>
     simp[set_current_module_def] >> metis_tac[]) >>
  simp[] >>
  first_x_assum irule >>
  qexists `merge_constant_imms h0 cenv imms` >>
  simp[merge_constants_immutables]
QED

(* TOP-LEVEL: for a checked contract the deployment constants fold succeeds
   from the immutables load_contract installs, in any context whose contract
   code is mods. *)
Theorem check_contract_evaluate_all_constants:
  check_contract in_deploy layouts addr mods = SOME art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  ALOOKUP am.immutables cx.txn.target = SOME imms ==>
  IS_SOME (evaluate_all_constants cx am cx.txn.target mods)
Proof
  strip_tac >>
  `contract_constants_ok mods` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     simp[check_contract_def] >> rw[]) >>
  gvs[contract_constants_ok_def, IS_SOME_EXISTS] >>
  drule constants_fold_evaluate_all_constants >>
  disch_then (qspecl_then [`cx`,`cx.txn.target`,`am`] mp_tac) >>
  simp[] >> metis_tac[]
QED
