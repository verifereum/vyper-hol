(* Typing facts about the expressions a checked contract evaluates without a
   frame: constant initialisers and argument defaults.

   TOP-LEVEL:
   - well_typed_vtypes_restrict: a runtime-constant expression reads the
     top-level types only at constants and immutables, so cutting
     toplevel_vtypes down to those keys leaves its typing unchanged.
   - constant_value_no_neg_exp: an expression whose constant value exists
     has no ** with a negative literal exponent (evaluating one fails).
   - runtime_constant_main_types: a typed runtime-constant expression whose
     type environment holds only main-module names and whose top-level types
     are all value types mentions only main-module types. *)
Theory whitelistCheckerConsts
Ancestors
  list pred_set finite_map vyperAST vyperValue vyperValueOperation vyperContext
  vyperTypeSystem vyperTypeContract vyperTypeContractContext constSubst
  supportedTypes supportedExprTraverse supportedStmtTraverse
  whitelistCheckerStmts

(* ===== Constant and runtime-constant expressions ===== *)

Theorem constant_expr_runtime_constant:
  !mods e. constant_expr mods e ==> runtime_constant_expr mods e
Proof
  ho_match_mp_tac constant_expr_ind >>
  rw[constant_expr_def, runtime_constant_expr_def] >> fs[EVERY_MEM]
QED

Triviality runtime_constant_builtin_args:
  runtime_constant_expr mods (Builtin ty bt es) ==>
  EVERY (runtime_constant_expr mods) es
Proof
  rw[runtime_constant_expr_def] >> fs[EVERY_MEM, constant_expr_runtime_constant]
QED

(* ===== Typing reads toplevel_vtypes only at constants and immutables ===== *)

Triviality subscript_base_type_exact_vtypes:
  subscript_base_type_exact (env with toplevel_vtypes := X) e =
  subscript_base_type_exact env e
Proof
  Cases_on `e` >> simp[subscript_base_type_exact_def] >>
  rename1 `Call _ c` >> Cases_on `c` >> simp[subscript_base_type_exact_def]
QED

Theorem well_typed_vtypes_restrict:
  (!src id. declared_constant mods src id \/ declared_immutable mods src id ==>
     (src,id) IN ks) ==>
  (!env e. runtime_constant_expr mods e ==>
     (well_typed_expr
        (env with toplevel_vtypes := DRESTRICT env.toplevel_vtypes ks) e <=>
      well_typed_expr env e)) /\
  (!env e. runtime_constant_expr mods e ==>
     type_place_expr
       (env with toplevel_vtypes := DRESTRICT env.toplevel_vtypes ks) e =
     type_place_expr env e) /\
  (!env tgt. type_place_target env tgt = type_place_target env tgt) /\
  (!env es. EVERY (runtime_constant_expr mods) es ==>
     (well_typed_exprs
        (env with toplevel_vtypes := DRESTRICT env.toplevel_vtypes ks) es <=>
      well_typed_exprs env es)) /\
  (!env opt. well_typed_opt env opt <=> well_typed_opt env opt) /\
  (!env kes. EVERY (runtime_constant_expr mods) (MAP SND kes) ==>
     (well_typed_named_exprs
        (env with toplevel_vtypes := DRESTRICT env.toplevel_vtypes ks) kes <=>
      well_typed_named_exprs env kes))
Proof
  strip_tac >> ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >>
  rpt gen_tac >> rpt strip_tac >> imp_res_tac runtime_constant_builtin_args >>
  fs[runtime_constant_expr_def] >> res_tac >>
  ONCE_REWRITE_TAC[well_typed_expr_def] >>
  fs[FLOOKUP_DRESTRICT, subscript_base_type_exact_vtypes]
QED

(* ===== Constant values never raise a negative exponent ===== *)

Triviality constant_exp_literal_nonneg:
  constant_values mods imms es = SOME vs /\
  evaluate_builtin cx acc ty (Bop Exp) tys vs = INL v ==>
  case es of [b; Literal _ (IntL n)] => 0 <= n | _ => T
Proof
  strip_tac >> BasicProvers.every_case_tac >>
  gvs[constant_value_def, AllCaseEqs(), evaluate_literal_def,
      evaluate_builtin_def, evaluate_binop_def, integerTheory.INT_NOT_LT]
QED

Theorem constant_value_no_neg_exp:
  (!mods imms e v. constant_value mods imms e = SOME v ==> no_neg_exp_expr e) /\
  (!mods imms es vs. constant_values mods imms es = SOME vs ==>
     EVERY no_neg_exp_expr es)
Proof
  ho_match_mp_tac constant_value_ind >>
  rw[constant_value_def, no_neg_exp_expr_def, no_neg_exp_collections] >>
  gvs[AllCaseEqs(), EVERY_MAP] >> res_tac >>
  metis_tac[constant_exp_literal_nonneg]
QED

(* ===== Runtime-constant expressions mention only main-module types ===== *)

Theorem evaluate_type_namespace:
  (!tenv ty. IS_SOME (evaluate_type tenv ty) ==>
     (!id x. FLOOKUP tenv id = SOME x ==> FST id = NONE) ==>
     supported_type_namespace ty) /\
  (!tenv ts acc. IS_SOME (evaluate_types tenv ts acc) ==>
     (!id x. FLOOKUP tenv id = SOME x ==> FST id = NONE) ==>
     supported_types_namespace ts)
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >>
  gvs[evaluate_type_def, supported_type_namespace_def, optionTheory.IS_SOME_EXISTS,
      AllCaseEqs()] >>
  rename1 `supported_main_nsid nsid` >> PairCases_on `nsid` >>
  res_tac >> gvs[supported_main_nsid_def]
QED

Definition main_typed_env_def:
  main_typed_env env <=>
    (!id x. FLOOKUP env.type_defs id = SOME x ==> FST id = NONE) /\
    (!k vt. FLOOKUP env.toplevel_vtypes k = SOME vt ==>
       ?t. vt = Type t /\ supported_type_namespace t)
End

Theorem well_formed_type_namespace:
  (!id x. FLOOKUP tenv id = SOME x ==> FST id = NONE) /\
  well_formed_type tenv ty ==>
  supported_type_namespace ty
Proof
  rw[well_formed_type_def] >> metis_tac[evaluate_type_namespace]
QED

Triviality main_typed_well_formed:
  main_typed_env env /\ well_formed_type env.type_defs ty ==>
  supported_type_namespace ty
Proof
  rw[main_typed_env_def] >> metis_tac[well_formed_type_namespace]
QED

Triviality main_typed_vtype:
  main_typed_env env /\ FLOOKUP env.toplevel_vtypes k = SOME vt /\
  vtype_annotation_ok vt ty ==>
  vt = Type ty /\ supported_type_namespace ty
Proof
  rw[main_typed_env_def] >> res_tac >> gvs[vtype_annotation_ok_def]
QED

Triviality subscript_vtype_main:
  supported_type_namespace t /\ subscript_vtype (Type t) ity = SOME vt /\
  vtype_annotation_ok vt ty ==>
  vt = Type ty /\ supported_type_namespace ty
Proof
  Cases_on `t` >>
  simp[subscript_vtype_def, AllCaseEqs(), supported_type_namespace_def] >>
  rw[] >> gvs[vtype_annotation_ok_def]
QED

Triviality constant_type_builtin_target:
  constant_type_builtin tb /\ type_builtin_result_ok tenv tb ty target tys ==>
  target = ty
Proof
  Cases_on `tb` >> simp[constant_type_builtin_def, type_builtin_result_ok_def]
QED

Theorem runtime_constant_main_types:
  (!env e. well_typed_expr env e ==> main_typed_env env ==>
     runtime_constant_expr mods e ==>
     ~supported_expr_exists expr_nonmain_type_root e) /\
  (!env e. IS_SOME (type_place_expr env e) ==> main_typed_env env ==>
     runtime_constant_expr mods e ==>
     ~supported_expr_exists expr_nonmain_type_root e /\
     ?t. type_place_expr env e = SOME (Type t) /\ supported_type_namespace t) /\
  (!env tgt. type_place_target env tgt = type_place_target env tgt) /\
  (!env es. well_typed_exprs env es ==> main_typed_env env ==>
     EVERY (runtime_constant_expr mods) es ==>
     ~supported_exprs_exists expr_nonmain_type_root es) /\
  (!env opt. well_typed_opt env opt <=> well_typed_opt env opt) /\
  (!env kes. well_typed_named_exprs env kes ==> main_typed_env env ==>
     EVERY (runtime_constant_expr mods) (MAP SND kes) ==>
     ~supported_fields_exists expr_nonmain_type_root kes)
Proof
  ho_match_mp_tac well_typed_expr_ind >> rpt conj_tac >> rpt gen_tac >>
  rpt strip_tac >> imp_res_tac runtime_constant_builtin_args >>
  fs[runtime_constant_expr_def] >>
  gvs[well_typed_expr_def, AllCaseEqs(), optionTheory.IS_SOME_EXISTS] >>
  imp_res_tac main_typed_well_formed >> imp_res_tac main_typed_vtype >>
  imp_res_tac constant_type_builtin_target >>
  gvs[supported_expr_exists_def, expr_nonmain_type_root_def, expr_type_def] >>
  imp_res_tac subscript_vtype_main >> gvs[]
QED
