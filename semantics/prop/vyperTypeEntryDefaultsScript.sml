(*
 * Default arguments of a checked external entry: they either evaluate to
 * values of the remaining parameters' types, or one of them fails at run time
 * with an error of its own evaluation; on success the arguments bind.
 *
 * Vyper accepts any RUNTIME_CONSTANT default (e.g. `msg.value - 1`), which can
 * revert at call time, so success is not a theorem.  The failing default is
 * characterised by its own `eval_expr` result: a runtime error that is not a
 * TypeError.  The checker requires defaults to be runtime-constant
 * (`runtime_constant_expr`), so a default never reads storage and never
 * yields a storage reference.
 *
 * The entry is the tuple selected by `lookup_exported_function` from the
 * initial call context, as in `call_external`.
 *
 * TOP-LEVEL:
 * - checked_selected_entry_defaults_cases
 * - checked_selected_entry_bind_arguments
 *
 * Helper:
 * - evaluate_defaults_NONE_stop
 * - evaluate_defaults_typed_cases
 * - defaults_env_function_entry_env
 * - checked_entry_defaults_env_consistent
 * - checked_public_getter_args_well_formed
 *)

Theory vyperTypeEntryDefaults
Ancestors
  list rich_list arithmetic finite_map option pair
  vyperAST vyperValue vyperState vyperInterpreter vyperContext
  vyperTypeSystem vyperTypeContract vyperTypeInvariants vyperTypeValues
  vyperTypeExprSoundness vyperTypeExprResult vyperTypeInitialState
  vyperTypeEvalSoundness vyperTypeCallGraph vyperTypeCallGraphSoundness
  vyperTypeCallStackSoundness vyperTypeBindArguments
  vyperTypeContractStaticMaps vyperTypeContractContext
  vyperTypeContractFunction vyperTypeContractGetter
  vyperTypeEntryReadiness vyperTypeContractSoundness

val _ = Parse.hide "body";

(* ===== Evaluating a list of well-typed defaults ===== *)

(* evaluate_defaults stops at the first default whose own evaluation is not a
 * value; every default before it evaluated to one. *)
Theorem evaluate_defaults_NONE_stop:
  !es.
    evaluate_defaults cx am es = NONE ==>
    ?pre e post.
      es = pre ++ e::post /\
      EVERY (\e'. ?v. FST (eval_expr cx e' (initial_state am [FEMPTY])) =
                        INL (Value v)) pre /\
      !v. FST (eval_expr cx e (initial_state am [FEMPTY])) <> INL (Value v)
Proof
  Induct >- simp[evaluate_defaults_def] >>
  rpt strip_tac >>
  Cases_on `?v. FST (eval_expr cx h (initial_state am [FEMPTY])) = INL (Value v)`
  >- (gvs[evaluate_defaults_def, AllCaseEqs()] >>
      qexistsl [`h::pre`, `e`, `post`] >> simp[]) >>
  qexistsl [`[]`, `h`, `es`] >> gvs[]
QED

(* A well-typed default whose evaluation is not a value either raised a
 * non-TypeError exception or yielded a storage array reference; HashMap
 * references are excluded by its type. *)
Theorem default_eval_not_value_cases[local]:
  well_typed_expr env e /\
  (!tyv. evaluate_type env.type_defs (expr_type e) = SOME tyv ==> tyv <> NoneTV) /\
  env_consistent env cx (initial_state am [FEMPTY]) /\
  state_well_typed (initial_state am [FEMPTY]) /\
  context_well_typed cx /\
  accounts_well_typed am.accounts /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  (!v. FST (eval_expr cx e (initial_state am [FEMPTY])) <> INL (Value v)) ==>
  (?err. FST (eval_expr cx e (initial_state am [FEMPTY])) = INR err /\
         no_type_error_result (INR err : toplevel_value + exception)) \/
  (?is_transient slot elem_tv bd.
     FST (eval_expr cx e (initial_state am [FEMPTY])) =
       INL (ArrayRef is_transient slot elem_tv bd))
Proof
  strip_tac >>
  `accounts_well_typed (initial_state am [FEMPTY]).accounts` by
    simp[initial_state_def] >>
  Cases_on `eval_expr cx e (initial_state am [FEMPTY])` >>
  rename1 `eval_expr cx e _ = (res1,st1)` >>
  drule_all (cj 8 eval_all_type_sound_mutual) >> strip_tac >>
  Cases_on `res1` >> gvs[] >>
  rename1 `expr_result_typed env e tv` >>
  Cases_on `tv` >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, toplevel_value_typed_def]
QED

Theorem well_typed_exprs_MEM[local]:
  !es. well_typed_exprs env es /\ MEM e es ==> well_typed_expr env e
Proof
  Induct >> rw[well_typed_expr_def] >> gvs[]
QED

(* Defaults dichotomy for a list of well-typed defaults evaluated from the
 * same entry state: they all evaluate to values of their types, or
 * evaluation stops at a default whose own evaluation raised a non-TypeError
 * exception or yielded a storage array reference. *)
Theorem evaluate_defaults_typed_cases:
  well_typed_exprs env es /\
  (!e tyv. MEM e es /\ evaluate_type env.type_defs (expr_type e) = SOME tyv ==>
     tyv <> NoneTV) /\
  env_consistent env cx (initial_state am [FEMPTY]) /\
  state_well_typed (initial_state am [FEMPTY]) /\
  context_well_typed cx /\
  accounts_well_typed am.accounts /\
  functions_well_typed cx /\
  (!e. MEM e es ==> call_evaluation_safe cx (int_calls_expr e)) ==>
  (?vs.
     evaluate_defaults cx am es = SOME vs /\
     LIST_REL
       (\v e. ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
                   value_has_type tv v)
       vs es) \/
  (evaluate_defaults cx am es = NONE /\
   ?pre e post.
     es = pre ++ e::post /\
     EVERY (\e'. ?v. FST (eval_expr cx e' (initial_state am [FEMPTY])) =
                       INL (Value v)) pre /\
     ((?err. FST (eval_expr cx e (initial_state am [FEMPTY])) = INR err /\
             no_type_error_result (INR err : toplevel_value + exception)) \/
      (?is_transient slot elem_tv bd.
         FST (eval_expr cx e (initial_state am [FEMPTY])) =
           INL (ArrayRef is_transient slot elem_tv bd))))
Proof
  strip_tac >>
  Cases_on `evaluate_defaults cx am es`
  >- (disj2_tac >> simp[] >>
      drule evaluate_defaults_NONE_stop >> strip_tac >>
      qexistsl [`pre`, `e`, `post`] >> simp[] >>
      `MEM e es` by simp[] >>
      irule default_eval_not_value_cases >> simp[] >>
      qexists_tac `env` >> simp[] >>
      metis_tac[well_typed_exprs_MEM]) >>
  disj1_tac >> simp[] >>
  drule_all evaluate_defaults_success_values_typed >> simp[]
QED

(* The typed values of the needed defaults are typed against the parameters
 * they fill. *)
Theorem defaults_values_typed_args[local]:
  LIST_REL
    (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                value_has_type tv v)
    vs es /\
  MAP expr_type es = MAP SND params ==>
  args_values_typed tenv params vs
Proof
  rw[args_values_typed_def, listTheory.LIST_REL_EL_EQN]
  >- metis_tac[listTheory.LENGTH_MAP] >>
  `LENGTH params = LENGTH es` by metis_tac[listTheory.LENGTH_MAP] >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  `expr_type (EL i es) = SND (EL i params)` by
    metis_tac[listTheory.EL_MAP] >>
  gvs[]
QED

(* As intcall_needed_defaults_param_types, but for provided arguments of any
 * type (an external entry's are values, not expressions). *)
Theorem needed_defaults_param_types[local]:
  MAP expr_type dflts =
    MAP SND (DROP (LENGTH params - LENGTH dflts) (params:argument list)) /\
  LENGTH vals <= LENGTH params /\
  LENGTH params - LENGTH vals <= LENGTH dflts ==>
  MAP expr_type (DROP (LENGTH dflts - (LENGTH params - LENGTH vals)) dflts) =
  MAP SND (DROP (LENGTH vals) params)
Proof
  strip_tac >>
  `LENGTH dflts <= LENGTH params` by
    metis_tac[intcall_defaults_map_param_types_length_le] >>
  simp[listTheory.MAP_DROP, rich_listTheory.DROP_DROP_T] >>
  `LENGTH params - LENGTH dflts +
     (LENGTH dflts - (LENGTH params - LENGTH vals)) = LENGTH vals` by
    decide_tac >>
  simp[]
QED

(* ===== Entry setup for default evaluation ===== *)

Theorem defaults_env_FOLDL_extend_local[local]:
  !args env.
    defaults_env (FOLDL (\env (id,ty). extend_local env id ty T) env args) =
    defaults_env env
Proof
  Induct >> simp[] >> Cases >> simp[extend_local_def, defaults_env_def]
QED

Theorem defaults_env_function_entry_env:
  defaults_env (function_entry_env art mods src args) = artifact_env art mods src
Proof
  simp[function_entry_env_def, defaults_env_FOLDL_extend_local] >>
  simp[defaults_env_def, artifact_env_def]
QED

(* Defaults are evaluated in the artifact environment of the selected module,
 * at the entry machine's initial state with one empty frame. *)
Theorem checked_entry_defaults_env_consistent:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  call_tx_well_typed tx /\
  cx = initial_evaluation_context am.sources am.layouts tx src ==>
  env_consistent (artifact_env art mods src) cx (initial_state am [FEMPTY]) /\
  state_well_typed (initial_state am [FEMPTY]) /\
  context_well_typed cx /\
  accounts_well_typed am.accounts /\
  functions_well_typed cx
Proof
  strip_tac >> gvs[checked_contract_runtime_ready_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
     (initial_evaluation_context am.sources am.layouts tx src) am.immutables` by
    metis_tac[immutables_ready_initial_evaluation_context_source] >>
  rpt conj_tac
  >- (rw[env_consistent_def]
      >- (irule check_contract_env_context_consistent_initial_src >> simp[])
      >- simp[env_scopes_consistent_def, artifact_env_def, initial_state_def,
              lookup_scopes_def]
      >- (gvs[env_immutables_consistent_def, immutables_ready_def,
              initial_state_def, artifact_env_def] >>
          metis_tac[]))
  >- gvs[machine_well_typed_def, initial_state_def, state_well_typed_def,
         scope_well_typed_def]
  >- gvs[call_tx_well_typed_def, context_well_typed_def,
         initial_evaluation_context_def]
  >- gvs[machine_well_typed_def]
  >- (irule check_contract_functions_well_typed_initial >> simp[])
QED

Theorem MEM_int_calls_exprs[local]:
  !es. MEM e es /\ MEM c (int_calls_expr e) ==> MEM c (int_calls_exprs es)
Proof
  Induct >> rw[int_calls_expr_def] >> simp[]
QED

Theorem checked_explicit_external_defaults_call_evaluation_safe[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  MEM e dflts ==>
  call_evaluation_safe
    (initial_evaluation_context am.sources am.layouts tx src)
    (int_calls_expr e)
Proof
  rpt strip_tac >>
  `calls_follow_call_graph (contract_call_edges mods) (src,tx.function_name)
     (int_calls_expr e)` by (
    rw[calls_follow_call_graph_def, EVERY_MEM, call_edge_rel_def] >>
    irule contract_call_edges_function >>
    qexistsl [`args`, `body`, `dflts`, `mut`, `nr`, `raw`, `ret`, `ts`,
              `External`] >>
    simp[function_int_calls_def] >>
    metis_tac[alistTheory.ALOOKUP_MEM, MEM_int_calls_exprs]) >>
  `(initial_evaluation_context am.sources am.layouts tx src) =
   ((initial_evaluation_context am.sources am.layouts tx src) with
      stk := [(src,tx.function_name)])` by
    simp[initial_evaluation_context_def] >>
  pop_assum SUBST1_TAC >>
  irule (INST_TYPE [``:'a`` |-> ``:num``]
    checked_contract_call_evaluation_safe_singleton) >>
  qexistsl [`art`, `am.layouts`, `mods`] >>
  simp[initial_evaluation_context_def]
QED

Theorem checked_explicit_external_defaults_typed[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts ==>
  well_typed_exprs (artifact_env art mods src) dflts /\
  EVERY (runtime_constant_expr mods) dflts /\
  MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args) /\
  (!arg. MEM arg args ==> assignable_type (type_env_all_modules mods) (SND arg)) /\
  (!e. MEM e dflts ==>
     call_evaluation_safe
       (initial_evaluation_context am.sources am.layouts tx src)
       (int_calls_expr e))
Proof
  strip_tac >>
  `External <> Deploy` by simp[] >>
  `check_function_body am.layouts tx.target mods art src mut nr args dflts ret body` by
    metis_tac[check_contract_runtime_function_body_MEM] >>
  rpt conj_tac
  >- fs[check_function_body_def, defaults_env_function_entry_env]
  >- fs[check_function_body_def]
  >- fs[check_function_body_def]
  >- (simp[FORALL_PROD] >>
      fs[check_function_body_def, params_ok_def, EVERY_MEM, FORALL_PROD]) >>
  rpt strip_tac >>
  irule checked_explicit_external_defaults_call_evaluation_safe >>
  metis_tac[]
QED

(* ===== Public getters: no defaults, well-formed parameter types ===== *)

Theorem build_getter_args_well_formed[local]:
  !e kt vt n args ret exp.
    build_getter e kt vt n = (args,ret,exp) /\
    well_formed_type tenv kt /\
    check_value_type tenv vt ==>
    !arg. MEM arg args ==> well_formed_type tenv (SND arg)
Proof
  ho_match_mp_tac build_getter_ind >> rpt conj_tac >> rpt gen_tac
  >- (strip_tac >> simp[Once build_getter_def] >>
      IF_CASES_TAC >> simp[] >>
      pairarg_tac >> gvs[] >> rpt strip_tac >> gvs[] >>
      first_x_assum irule >> simp[] >>
      conj_tac
      >- (Cases_on `vt` >>
          gvs[is_ArrayT_def, ArrayT_type_def, check_value_type_def,
              assignable_type_def, well_formed_type_def]) >>
      simp[well_formed_type_def, evaluate_type_def]) >>
  strip_tac >> simp[Once build_getter_def] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >> gvs[] >>
  first_x_assum irule >> gvs[check_value_type_def]
QED

Theorem checked_public_getter_args_well_formed:
  check_contract F layouts addr mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) ==>
  dflts = [] /\
  !arg. MEM arg args ==> well_formed_type (type_env_all_modules mods) (SND arg)
Proof
  strip_tac >>
  `check_toplevel_decl layouts addr mods art src decl` by
    metis_tac[check_contract_toplevel_decl_MEM] >>
  Cases_on `decl` >> gvs[external_getter_tuple_def]
  >~ [`VariableDecl vis vmut id typ init`]
  >- (Cases_on `vis` >> gvs[external_getter_tuple_def] >>
      Cases_on `is_ArrayT typ` >> gvs[getter_def] >>
      pairarg_tac >> gvs[] >>
      rpt strip_tac >>
      drule_then irule build_getter_args_well_formed >>
      simp[well_formed_type_def, evaluate_type_def] >>
      `assignable_type (type_env_all_modules mods) typ` by
        (Cases_on `vmut` >> gvs[check_toplevel_decl_def]) >>
      Cases_on `typ` >>
      gvs[is_ArrayT_def, ArrayT_type_def, check_value_type_def,
          assignable_type_def, well_formed_type_def]) >>
  rename1 `HashMapDecl vis is_t id kt vt init` >>
  Cases_on `vis` >> gvs[external_getter_tuple_def, getter_def] >>
  pairarg_tac >> gvs[] >>
  rpt strip_tac >>
  drule_then irule build_getter_args_well_formed >>
  gvs[check_toplevel_decl_def]
QED

(* ===== The selected external entry ===== *)

Theorem lookup_exported_function_initial_module_code[local]:
  src = find_function_module am tx.target tx.function_name /\
  lookup_exported_function
    (initial_evaluation_context am.sources am.layouts tx src) am
    tx.function_name = SOME tup ==>
  ?ts. get_module_code
         (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts
Proof
  rw[lookup_exported_function_def, find_function_module_def] >>
  gvs[AllCaseEqs(), get_self_code_def, initial_evaluation_context_def]
QED

(* Everything the default-evaluation and binding lemmas need, established for
 * the entry call_external selects. *)
Theorem checked_selected_entry_defaults_setup[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  src = find_function_module am tx.target tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  lookup_exported_function cx am tx.function_name =
    SOME (mut,nr,args,dflts,ret,body) ==>
  well_typed_exprs (artifact_env art mods src) dflts /\
  EVERY (runtime_constant_expr mods) dflts /\
  MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args) /\
  (!arg. MEM arg args ==>
     ?tv. evaluate_type (type_env_all_modules mods) (SND arg) = SOME tv) /\
  (!e tyv. MEM e dflts /\
     evaluate_type (type_env_all_modules mods) (expr_type e) = SOME tyv ==>
     tyv <> NoneTV) /\
  (!e. MEM e dflts ==> call_evaluation_safe cx (int_calls_expr e))
Proof
  strip_tac >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    gvs[checked_contract_runtime_ready_def] >>
  qpat_x_assum `cx = _` SUBST_ALL_TAC >>
  drule_all lookup_exported_function_initial_module_code >> strip_tac >>
  `ALOOKUP mods src = SOME ts` by
    gvs[get_module_code_def, initial_evaluation_context_def] >>
  drule_all lookup_exported_function_checked_cases_current >> strip_tac
  >- (drule_all checked_explicit_external_defaults_typed >> strip_tac >>
      simp[] >> rpt strip_tac
      >- metis_tac[assignable_type_well_formed, well_formed_type_def,
                   optionTheory.IS_SOME_EXISTS] >>
      `MEM (expr_type e) (MAP SND (DROP (LENGTH args - LENGTH dflts) args))` by
        metis_tac[listTheory.MEM_MAP] >>
      gvs[listTheory.MEM_MAP] >>
      metis_tac[rich_listTheory.MEM_DROP_IMP,
                assignable_type_evaluate_not_NoneTV]) >>
  drule_all checked_public_getter_args_well_formed >> strip_tac >>
  gvs[well_typed_expr_def] >>
  metis_tac[well_formed_type_def, optionTheory.IS_SOME_EXISTS]
QED

(* ===== Runtime-constant defaults evaluate to values ===== *)

(* A runtime-constant expression never evaluates to a storage or HashMap
 * reference: its top-level names are constants and immutables, which
 * lookup_global reads from the immutables map. *)
Theorem runtime_constant_expr_eval_value[local]:
  !mods e. runtime_constant_expr mods e ==>
    !env cx st tv st'.
      env_context_consistent env cx /\
      (!src id. declared_constant mods src id \/ declared_immutable mods src id ==>
         ?ty. FLOOKUP env.bare_globals (src,id) = SOME ty) /\
      eval_expr cx e st = (INL tv, st') ==>
      ?v. tv = Value v
Proof
  ho_match_mp_tac runtime_constant_expr_ind >>
  rw[runtime_constant_expr_def]
  >~ [`TopLevelName`]
  >- (`?ty. FLOOKUP env.bare_globals (src,id) = SOME ty` by metis_tac[] >>
      drule_all env_context_consistent_bare_global_find_NONE >> strip_tac >>
      gvs[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
          get_immutables_def, get_address_immutables_def, return_def,
          raise_def, vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator, AllCaseEqs()])
  >~ [`TopLevelName`]
  >- (`?ty. FLOOKUP env.bare_globals (src,id) = SOME ty` by metis_tac[] >>
      drule_all env_context_consistent_bare_global_find_NONE >> strip_tac >>
      gvs[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
          get_immutables_def, get_address_immutables_def, return_def,
          raise_def, vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator, AllCaseEqs()])
  >~ [`Subscript`]
  >- (gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
          lift_sum_def, lift_option_type_def, AllCaseEqs()] >>
      rename1 `eval_expr cx e1 st = (INL tv1, s1)` >>
      `?v1. tv1 = Value v1` by metis_tac[] >>
      gvs[] >> Cases_on `v1` >> Cases_on `v2` >>
      gvs[evaluate_subscript_def, return_def, raise_def, bind_def,
          vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
          AllCaseEqs()])
  >~ [`StructLit`]
  >- (rename1 `StructLit _ nsid kes` >> Cases_on `nsid` >>
      gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
          AllCaseEqs()])
  >~ [`IfExp`]
  >- (gvs[Once evaluate_def, bind_def, switch_BoolV_def, return_def,
          raise_def, COND_RATOR, AllCaseEqs()] >> metis_tac[])
  >~ [`IfExp`]
  >- (gvs[Once evaluate_def, bind_def, switch_BoolV_def, return_def,
          raise_def, COND_RATOR, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_sum_def, type_check_def, assert_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, runtime_constant_builtin_def]) >>
  rw[] >> gvs[return_def, raise_def]
QED

(* Constants and immutables of a checked contract are bare globals of every
 * module's artifact environment. *)
Theorem checked_declared_globals_bare[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods ==>
  !src id. declared_constant mods src id \/ declared_immutable mods src id ==>
    ?ty. FLOOKUP art.cta_bare_globals (src,id) = SOME ty
Proof
  rpt strip_tac >>
  `contract_namespaces_ok F mods` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     simp[check_contract_def] >> metis_tac[]) >>
  `bare_globals_complete art.cta_bare_globals
     (initial_evaluation_context am.sources am.layouts tx src)` by
    (irule check_contract_bare_globals_complete_initial >> metis_tac[]) >>
  gvs[declared_constant_def, declared_immutable_def, bare_globals_complete_def,
      get_module_code_def, initial_evaluation_context_def] >>
  `ALOOKUP mods src = SOME tls` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     gvs[contract_namespaces_ok_def]) >>
  metis_tac[]
QED

(* Defaults dichotomy: under a checked contract, the needed default suffix of
 * the selected entry either evaluates to values of the remaining parameters'
 * types, or `evaluate_defaults` stops at a default `e`: every default before
 * it evaluated to a value, and `e`'s own evaluation fails with a runtime error
 * that is not a TypeError.  A checked default is runtime-constant, so it
 * cannot evaluate to a storage reference. *)
Theorem checked_selected_entry_defaults_cases:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  call_tx_well_typed tx /\
  src = find_function_module am tx.target tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  lookup_exported_function cx am tx.function_name =
    SOME (mut,nr,args,dflts,ret,body) /\
  LENGTH tx.args <= LENGTH args /\
  LENGTH args - LENGTH tx.args <= LENGTH dflts ==>
  (?vs.
     evaluate_defaults cx am
       (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) = SOME vs /\
     args_values_typed (type_env_all_modules mods)
       (DROP (LENGTH tx.args) args) vs) \/
  (evaluate_defaults cx am
     (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) = NONE /\
   ?pre e post.
     DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts =
       pre ++ e::post /\
     EVERY (\e'. ?v. FST (eval_expr cx e' (initial_state am [FEMPTY])) =
                       INL (Value v)) pre /\
     ?err. FST (eval_expr cx e (initial_state am [FEMPTY])) = INR err /\
           no_type_error_result (INR err : toplevel_value + exception))
Proof
  strip_tac >>
  drule_all checked_selected_entry_defaults_setup >> strip_tac >>
  drule_all checked_entry_defaults_env_consistent >> strip_tac >>
  qabbrev_tac `needed = DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts` >>
  `MAP expr_type needed = MAP SND (DROP (LENGTH tx.args) args)` by
    (qunabbrev_tac `needed` >> irule needed_defaults_param_types >> simp[]) >>
  mp_tac (Q.INST [`env` |-> `artifact_env art mods src`, `es` |-> `needed`]
            evaluate_defaults_typed_cases) >>
  impl_tac
  >- (simp[Abbr `needed`, well_typed_exprs_DROP] >>
      simp[artifact_env_def] >>
      metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  strip_tac
  >- (disj1_tac >> qexists_tac `vs` >> simp[] >>
      irule defaults_values_typed_args >>
      qexists_tac `needed` >> gvs[artifact_env_def]) >>
  disj2_tac >> simp[] >>
  qexistsl [`pre`, `e`, `post`] >> simp[] >>
  (* The remaining case, a default yielding a storage reference, is
     impossible for a runtime-constant default. *)
  `MEM e needed` by (qpat_x_assum `_ = _ ++ _ :: _` SUBST1_TAC >> simp[]) >>
  `MEM e dflts` by
    (fs[markerTheory.Abbrev_def] >> metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  `runtime_constant_expr mods e` by metis_tac[listTheory.EVERY_MEM] >>
  `env_context_consistent (artifact_env art mods src) cx` by
    gvs[env_consistent_def] >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    gvs[checked_contract_runtime_ready_def] >>
  `!s i. declared_constant mods s i \/ declared_immutable mods s i ==>
          ?ty. FLOOKUP (artifact_env art mods src).bare_globals (s,i) = SOME ty` by
    (drule checked_declared_globals_bare >> simp[artifact_env_def]) >>
  Cases_on `eval_expr cx e (initial_state am [FEMPTY])` >> gvs[] >>
  drule_all runtime_constant_expr_eval_value >> strip_tac >> gvs[]
QED

(* Binding corollary: when the needed defaults evaluate, the provided and
 * default values bind to the selected parameters and are typed by them. *)
Theorem checked_selected_entry_bind_arguments:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  call_tx_well_typed tx /\
  src = find_function_module am tx.target tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  lookup_exported_function cx am tx.function_name =
    SOME (mut,nr,args,dflts,ret,body) /\
  LENGTH tx.args <= LENGTH args /\
  LENGTH args - LENGTH tx.args <= LENGTH dflts /\
  provided_args_typed (type_env_all_modules mods) args tx.args /\
  evaluate_defaults cx am
    (DROP (LENGTH dflts - (LENGTH args - LENGTH tx.args)) dflts) = SOME dflt_vs ==>
  ?scope.
    bind_arguments (type_env_all_modules mods) args (tx.args ++ dflt_vs) =
      SOME scope /\
    args_values_typed (type_env_all_modules mods) args (tx.args ++ dflt_vs)
Proof
  strip_tac >>
  drule_all checked_selected_entry_defaults_setup >> strip_tac >>
  drule_all checked_entry_defaults_env_consistent >> strip_tac >>
  `checked_call_inputs_ready (type_env_all_modules mods) cx am args dflts tx.args` by
    simp[checked_call_inputs_ready_def, checked_defaults_ready_def] >>
  mp_tac (Q.INST [`tenv` |-> `type_env_all_modules mods`,
                  `params` |-> `args`, `vals` |-> `tx.args`,
                  `env` |-> `artifact_env art mods src`]
           checked_call_inputs_ready_bind_arguments) >>
  impl_tac
  >- (simp[artifact_env_def, well_typed_exprs_DROP] >>
      metis_tac[rich_listTheory.MEM_DROP_IMP]) >>
  strip_tac >> gvs[]
QED
