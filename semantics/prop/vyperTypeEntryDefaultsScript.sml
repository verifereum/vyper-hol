(* Actual-state default evaluation and successful argument binding. *)

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
  vyperTypeEntryReadiness vyperTypeContractSoundness vyperTypeExternalDefaults

val _ = Parse.hide "body";

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


Theorem eval_external_defaults_typed_cases:
  checked_call_inputs_ready env.type_defs cx am args dflts vals /\
  well_typed_exprs env (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) /\
  env_consistent env cx (st with scopes := [FEMPTY]) /\
  state_well_typed st /\ state_well_typed (st with scopes := [FEMPTY]) /\
  context_well_typed cx /\ accounts_well_typed st.accounts /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs
    (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts)) /\
  (!arg. MEM arg args ==> ?tv. evaluate_type env.type_defs (SND arg) = SOME tv) /\
  MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args) /\
  eval_external_defaults cx
    (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) st = (res,rt) ==>
  state_well_typed rt /\ accounts_well_typed rt.accounts /\
  ((?vs scope. res = INL vs /\
      bind_arguments env.type_defs args (vals ++ vs) = SOME scope /\
      args_values_typed env.type_defs args (vals ++ vs)) \/
   (?exc. res = INR exc /\ no_type_error_result (INR exc : value list + exception) /\
      no_control_exc exc))
Proof
  strip_tac >> drule_all eval_external_defaults_type_sound >> strip_tac >>
  simp[] >> Cases_on `res`
  >- (disj1_tac >> simp[] >>
      drule_all (SRULE [] (Q.INST [`tenv` |-> `env.type_defs`]
        checked_call_inputs_ready_bind_arguments)) >> metis_tac[]) >>
  disj2_tac >> simp[] >>
  drule eval_external_defaults_no_control >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED
