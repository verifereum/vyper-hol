(* S2 from the type checker: a checked contract lowers to an O1 source unit
   once it avoids raw_call and creation. The checker allows these;
   the unit shape rejects delegate or calldata raw_call,
   and the body-shape proof has no case for plain raw_call or creation yet.
   TOP-LEVEL: lower_vyper_runtime_unit_source_unit_ok_checked,
   supported_program_raw_shape_free_program,
   supported_names_internal_names_distinct. *)
Theory loweringShapeSource
Ancestors
  list option loweringShapeProps vyperTypeSystem vyperTypeContract
  vyperTypeContractContext supportedProgram supportedExprTraverse
  supportedStmtTraverse compileVyper vyperAST supportedNames

(* The shape roots the type checker doesn't exclude: expr_shape_root less its
   builtin arity cases. The unit shape rejects creation,
   delegate raw_call (DELEGATECALL) and the calldata form (DALLOCA); a plain
   raw_call passes it, but the body-shape proof has no case for it yet. *)
Definition expr_raw_shape_root_def:
  expr_raw_shape_root e <=>
    (?ty flags es d. e = Call ty (RawCallTarget flags) es d) \/
    (?ty flags es d. e = Call ty (RawCallCalldataTarget flags) es d) \/
    (?ty kind salted rof order es d.
       e = Call ty (CreateTarget kind salted rof order) es d)
End

Definition raw_shape_free_program_def:
  raw_shape_free_program tops <=>
    !vis mut nr rr name args dflts ret body.
      MEM (FunctionDecl vis mut nr rr name args dflts ret body) tops /\
      vis <> Deploy ==>
      ~supported_stmts_expr_exists expr_raw_shape_root body /\
      EVERY (\e. ~supported_expr_exists expr_raw_shape_root e) dflts
End

(* ===== Typing gives builtin arity ===== *)

Theorem well_typed_builtin_app_arity[local]:
  well_typed_builtin_app ty bi ts ==> builtin_arity bi <= LENGTH ts
Proof
  Cases_on `bi` >> rw[well_typed_builtin_app_def, builtin_arity_def] >> gvs[]
QED

Theorem well_typed_type_builtin_args_arity[local]:
  well_typed_type_builtin_args tb target ts ==>
  type_builtin_arity tb <= LENGTH ts
Proof
  Cases_on `tb` >>
  rw[well_typed_type_builtin_args_def, type_builtin_arity_def] >> gvs[]
QED

Theorem well_typed_expr_raw_shape[local]:
  (!env e. well_typed_expr env e ==>
     ~supported_expr_exists expr_raw_shape_root e ==>
     ~supported_expr_exists expr_shape_root e) /\
  (!env e vt. type_place_expr env e = SOME vt ==>
     ~supported_expr_exists expr_raw_shape_root e ==>
     ~supported_expr_exists expr_shape_root e) /\
  (!env t vt. type_place_target env t = SOME vt ==>
     ~supported_target_exists expr_raw_shape_root t ==>
     ~supported_target_exists expr_shape_root t) /\
  (!env es. well_typed_exprs env es ==>
     ~supported_exprs_exists expr_raw_shape_root es ==>
     ~supported_exprs_exists expr_shape_root es) /\
  (!env opt. well_typed_opt env opt ==>
     ~supported_opt_exists expr_raw_shape_root opt ==>
     ~supported_opt_exists expr_shape_root opt) /\
  (!env kes. well_typed_named_exprs env kes ==>
     ~supported_fields_exists expr_raw_shape_root kes ==>
     ~supported_fields_exists expr_shape_root kes)
Proof
  ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  gvs[well_typed_expr_def, supported_expr_exists_def, expr_shape_root_def,
      expr_raw_shape_root_def, AllCaseEqs()] >>
  rpt (qpat_x_assum `_ \/ _` strip_assume_tac) >>
  res_tac >> imp_res_tac well_typed_builtin_app_arity >>
  imp_res_tac well_typed_type_builtin_args_arity >> gvs[]
QED

Theorem well_typed_atarget_raw_shape[local]:
  (!p t. p = expr_raw_shape_root ==>
     !ty. well_typed_atarget env t ty ==>
     ~supported_assignment_exists p t ==>
     ~supported_assignment_exists expr_shape_root t) /\
  (!p ts. p = expr_raw_shape_root ==>
     !tys. LIST_REL (\t ty. well_typed_atarget env t ty) ts tys ==>
     ~supported_assignments_exists p ts ==>
     ~supported_assignments_exists expr_shape_root ts)
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  rw[supported_assignment_exists_def] >>
  gvs[well_typed_atarget_def, well_typed_target_def, LIST_REL_CONS1] >>
  imp_res_tac well_typed_expr_raw_shape >> res_tac >> gvs[]
QED

Theorem atarget_accepts_raw_shape[local]:
  atarget_accepts env tgt t /\
  ~supported_assignment_exists expr_raw_shape_root tgt ==>
  ~supported_assignment_exists expr_shape_root tgt
Proof
  Cases_on `tgt` >>
  simp[atarget_accepts_def, supported_assignment_exists_def] >>
  rpt strip_tac
  >- (rename1 `type_place_target env b` >>
      Cases_on `type_place_target env b` >> fs[] >>
      metis_tac[well_typed_expr_raw_shape]) >>
  metis_tac[well_typed_atarget_raw_shape, supported_assignment_exists_def]
QED

Theorem well_typed_iterator_raw_shape[local]:
  well_typed_iterator env typ it /\
  ~supported_iterator_exists expr_raw_shape_root it ==>
  ~supported_iterator_exists expr_shape_root it
Proof
  Cases_on `it` >>
  rw[well_typed_iterator_def, supported_iterator_exists_def] >>
  metis_tac[well_typed_expr_raw_shape]
QED

Theorem type_stmt_raw_shape[local]:
  (!env ret s env1. type_stmt env ret s = SOME env1 ==>
     ~supported_stmt_expr_exists expr_raw_shape_root s ==>
     ~supported_stmt_expr_exists expr_shape_root s) /\
  (!env ret ss env1. type_stmts env ret ss = SOME env1 ==>
     ~supported_stmts_expr_exists expr_raw_shape_root ss ==>
     ~supported_stmts_expr_exists expr_shape_root ss)
Proof
  ho_match_mp_tac type_stmt_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  gvs[type_stmt_def, supported_stmt_expr_exists_def, AllCaseEqs(),
      IS_SOME_EXISTS, supported_assert_exists_def, supported_raise_exists_def,
      supported_iterator_exists_def, well_typed_iterator_def,
      well_typed_custom_error_def, well_typed_target_def,
      GSYM supported_exprs_exists_every, supported_expr_exists_def] >>
  rpt (qpat_x_assum `_ \/ _` strip_assume_tac) >>
  res_tac >> imp_res_tac well_typed_expr_raw_shape >>
  imp_res_tac atarget_accepts_raw_shape >>
  imp_res_tac well_typed_iterator_raw_shape >> gvs[]
QED

(* ===== The checker's facts about the main module ===== *)

Theorem classify_internal_names_fn_sig_keys[local]:
  !src tops.
    MAP (\p. (src, FST (SND (SND (SND p)))))
      (FST (SND (classify_functions tops))) =
    FLAT (MAP (fn_sig_keys_toplevel F src) tops)
Proof
  gen_tac >> simp[classify_functions_def] >> Induct >> simp[] >>
  rpt gen_tac >>
  Cases_on `FOLDR classify_function ([],[],NONE,NONE) tops` >>
  PairCases_on `r` >> Cases_on `h` >>
  gvs[classify_function_def, fn_sig_keys_toplevel_def] >>
  BasicProvers.every_case_tac >> gvs[include_fn_sig_def] >> rw[]
QED

Theorem ALL_DISTINCT_MAP_name_key[local]:
  !l. ALL_DISTINCT (MAP (\p. (c, FST (SND (SND (SND p))))) l) ==>
      ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p)))) l)
Proof
  Induct >> rw[MEM_MAP] >> metis_tac[]
QED

Theorem check_contract_internal_names_distinct:
  check_contract F layouts addr [(NONE, tops)] = SOME art ==>
  ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
                  (FST (SND (classify_functions tops))))
Proof
  strip_tac >> drule check_contract_namespaces_ok >>
  simp[contract_namespaces_ok_def, contract_keys_def,
       GSYM classify_internal_names_fn_sig_keys] >>
  strip_tac >> drule ALL_DISTINCT_MAP_name_key >> simp[]
QED

Theorem well_typed_exprs_raw_shape[local]:
  !es env. well_typed_exprs env es /\
    EVERY (\e. ~supported_expr_exists expr_raw_shape_root e) es ==>
    EVERY (\e. ~supported_expr_exists expr_shape_root e) es
Proof
  Induct >> simp[well_typed_expr_def] >> metis_tac[well_typed_expr_raw_shape]
QED

Theorem check_contract_runtime_bodies_shape_ok:
  check_contract F layouts addr [(NONE, tops)] = SOME art /\
  raw_shape_free_program tops ==>
  runtime_bodies_shape_ok tops
Proof
  rw[runtime_bodies_shape_ok_def, raw_shape_free_program_def] >>
  first_x_assum drule_all >> strip_tac >>
  drule check_contract_main_module_allocated >> simp[] >> strip_tac >>
  drule check_contract_runtime_function_body_MEM >> simp[] >>
  disch_then drule_all >>
  simp[check_function_body_def, IS_SOME_EXISTS] >> strip_tac >>
  metis_tac[type_stmt_raw_shape, well_typed_exprs_raw_shape]
QED

(* S2 from the checker. *)
Theorem lower_vyper_runtime_unit_source_unit_ok_checked:
  !tops rpolicy unit layouts addr art.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    check_contract F layouts addr [(NONE, tops)] = SOME art /\
    raw_shape_free_program tops ==>
    o1_source_unit_ok unit
Proof
  rpt strip_tac >>
  drule lower_vyper_runtime_unit_source_unit_ok_shape >>
  impl_tac
  >- metis_tac[check_contract_runtime_bodies_shape_ok,
               check_contract_internal_names_distinct] >>
  simp[]
QED

(* ===== supported_program excludes the raw shape roots ===== *)

Theorem supported_assignment_exists_mono[local]:
  (!p t. !q. (!x. p x ==> q x) /\ supported_assignment_exists p t ==>
     supported_assignment_exists q t) /\
  (!p ts. !q. (!x. p x ==> q x) /\ supported_assignments_exists p ts ==>
     supported_assignments_exists q ts)
Proof
  ho_match_mp_tac supported_assignment_exists_ind >>
  rw[supported_assignment_exists_def] >>
  metis_tac[supported_expr_exists_mono]
QED

Theorem supported_stmt_parts_exists_mono[local]:
  (!x. p x ==> q x) ==>
  (supported_iterator_exists p it ==> supported_iterator_exists q it) /\
  (supported_assert_exists p a ==> supported_assert_exists q a) /\
  (supported_raise_exists p r ==> supported_raise_exists q r)
Proof
  strip_tac >> rpt conj_tac
  >- (Cases_on `it` >> rw[supported_iterator_exists_def] >>
      metis_tac[supported_expr_exists_mono])
  >- (Cases_on `a` >> rw[supported_assert_exists_def, EXISTS_MEM] >>
      metis_tac[supported_expr_exists_mono]) >>
  Cases_on `r` >> rw[supported_raise_exists_def, EXISTS_MEM] >>
  metis_tac[supported_expr_exists_mono]
QED

Theorem supported_stmt_expr_exists_mono[local]:
  (!p s. !q. (!x. p x ==> q x) /\ supported_stmt_expr_exists p s ==>
     supported_stmt_expr_exists q s) /\
  (!p ss. !q. (!x. p x ==> q x) /\ supported_stmts_expr_exists p ss ==>
     supported_stmts_expr_exists q ss)
Proof
  ho_match_mp_tac supported_stmt_expr_exists_ind >>
  rw[supported_stmt_expr_exists_def] >>
  metis_tac[supported_expr_exists_mono, supported_assignment_exists_mono,
            supported_stmt_parts_exists_mono]
QED

Theorem supported_program_raw_shape_free_program:
  !tops. supported_program tops ==> raw_shape_free_program tops
Proof
  rpt gen_tac >> strip_tac >> REWRITE_TAC [raw_shape_free_program_def] >>
  rpt gen_tac >> strip_tac >>
  drule supported_program_runtime_bodies_shape_ok >>
  REWRITE_TAC [runtime_bodies_shape_ok_def] >>
  disch_then drule_all >> strip_tac >> conj_tac
  >- (strip_tac >>
      qpat_x_assum `~supported_stmts_expr_exists expr_shape_root _` mp_tac >>
      simp[] >> irule (CONJUNCT2 supported_stmt_expr_exists_mono) >>
      first_x_assum (irule_at Any) >>
      simp[expr_raw_shape_root_def, expr_shape_root_def] >> metis_tac[]) >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  qpat_x_assum `!e. MEM e dflts ==> _` drule >> simp[] >>
  irule (CONJUNCT1 supported_expr_exists_mono) >>
  first_x_assum (irule_at Any) >>
  simp[expr_raw_shape_root_def, expr_shape_root_def] >> metis_tac[]
QED

(* supported_program's distinct function names keep the internal ones
   apart, as lower_vyper_runtime_unit_source_unit_ok_shape asks. *)
Theorem supported_names_internal_names_distinct:
  !tops. ALL_DISTINCT (supported_function_names tops) ==>
         ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
                         (FST (SND (classify_functions tops))))
Proof
  Induct >- simp[classify_functions_def] >>
  rpt strip_tac >>
  `!name. MEM name (MAP (\p. FST (SND (SND (SND p))))
                      (FST (SND (classify_functions tops)))) ==>
          MEM name (supported_function_names tops)` by
    (simp[MEM_MAP, pairTheory.EXISTS_PROD, PULL_EXISTS,
          MEM_classify_internal, MEM_supported_function_names] >>
     metis_tac[]) >>
  `classify_functions (h::tops) = classify_function h (classify_functions tops)`
    by simp[classify_functions_def] >>
  Cases_on `classify_functions tops` >> PairCases_on `r` >>
  Cases_on `h` >> gvs[classify_function_def, supported_function_names_def] >>
  BasicProvers.every_case_tac >> gvs[] >> metis_tac[]
QED
