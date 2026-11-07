Theory bodyPtrBopInJointSource
Ancestors
  bodyPtrBopInUnit bodyPtrBopInUnitMetadata bodyPtrBopInLiveSourceFrame
  bodyPtrBopInLocalSuffix bodyPtrBopInSourceFrame bodySim compileEnv
  compileVyper vyperContext vyperState finite_map

(* Finite witnesses share the actual supported program and local bindings. *)
Definition joint_cenv_def:
  joint_cenv = (build_compile_env equality_tops External View "probe" []
    (BaseT BoolT) [] F) with
    <| ce_vars := FEMPTY |+ ("x",PtrVar (Var "%10") 64) |+
                             ("y",PtrVar (Var "%13") 64);
       ce_var_type := (\id. if id = "x" \/ id = "y" then
                                  SOME (BaseT (StringT 1)) else NONE) |>
End

Definition joint_cx_def:
  joint_cx = probe_live_cx with sources :=
    [(probe_live_cx.txn.target,[(NONE,equality_tops)])]
End

Theorem joint_body_inv:
  body_inv equality_tops (equality_runtime_context equality_selector)
    joint_cenv joint_cx
Proof
  simp[body_inv_def, equality_tops_supported, joint_cenv_def, joint_cx_def,
       probe_live_cx_def, probe_cx_def, empty_evaluation_context_def,
       get_module_code_def, get_tenv_def, build_compile_env_def] >>
  conj_tac
  >- (qexistsl_tac [`probe_policy`,
        `<| cu_context := equality_runtime_context equality_selector;
            cu_data_segment := [] |>`] >>
      simp[equality_lower_runtime, probe_policy_def] >> EVAL_TAC) >>
  EVAL_TAC >> simp[]
QED

Definition joint_env_def:
  joint_env = probe_env with
    <| var_types := FEMPTY |+ ("x",BaseT (StringT 1)) |+
                             ("y",BaseT (StringT 1));
       var_assignable := FEMPTY |+ ("x",F) |+ ("y",F) |>
End

Definition joint_es_def:
  joint_es = probe_es with scopes :=
    [FEMPTY |+ ("x",<| assignable := F; type := BaseTV (StringT 1);
                       value := StringV "a"; popped := [] |>) |+
                ("y",<| assignable := F; type := BaseTV (StringT 1);
                       value := StringV "a"; popped := [] |>)]
End

Theorem joint_source_invariant:
  expr_sim_inv joint_cenv joint_cx joint_env joint_es
Proof
  rw[exprSimHypsDefsTheory.expr_sim_inv_def, joint_cenv_def, joint_cx_def,
     joint_env_def, joint_es_def, probe_env_def, probe_es_def,
     probe_live_cx_def, probe_cx_def, empty_evaluation_context_def,
     build_compile_env_def, get_tenv_def, get_module_code_def] >>
  simp[vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def,
       vyperTypeInvariantsTheory.env_scopes_consistent_def,
       vyperTypeInvariantsTheory.env_immutables_consistent_def] >>
  simp[get_tenv_def, get_module_code_def, type_env_all_modules_def,
       type_env_for_module_def, current_module_def,
       vyperTypeInvariantsTheory.fn_sigs_consistent_def,
       vyperTypeInvariantsTheory.fn_sigs_live_def,
       vyperTypeInvariantsTheory.fn_sigs_declared_complete_def,
       vyperTypeInvariantsTheory.toplevel_vtypes_complete_def,
       vyperTypeInvariantsTheory.bare_globals_complete_def,
       vyperTypeInvariantsTheory.bare_global_assignable_complete_def,
       vyperTypeInvariantsTheory.flag_members_complete_def,
       vyperTypeInvariantsTheory.context_well_typed_def,
       vyperTypeInvariantsTheory.functions_well_typed_def,
       empty_call_txn_def, equality_tops_def] >>
  rpt conj_tac >>
  gvs[AllCaseEqs(), vyperStateTheory.lookup_flag_def,
      vyperInterpreterTheory.lookup_function_def] >>
  simp[vyperInterpreterTheory.initial_state_def,
       vyperInterpreterTheory.initial_machine_state_def, lookup_scopes_def,
       vyperTypeInvariantsTheory.state_well_typed_def,
       vyperTypeInvariantsTheory.scope_well_typed_def,
       vyperTypeInvariantsTheory.imms_well_typed_def,
       vyperTypeInvariantsTheory.accounts_well_typed_def,
       vyperTypeInvariantsTheory.account_well_typed_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.empty_accounts_def,
       vfmStateTheory.empty_account_state_def] >>
  gvs[type_env_all_modules_def, type_env_for_module_def, type_env_def,
      build_flag_info_def, allocate_args_def] >>
  rpt (pop_assum mp_tac) >> CONV_TAC (computeLib.RESTR_EVAL_CONV [``equality_fixture``]) >> simp[] >>
  rpt strip_tac >>
  gvs[find_var_decl_by_name_def, AllCaseEqs(),
      vyperInterpreterTheory.lookup_callable_function_def] >>
  Cases_on `id = "y"` >> gvs[] >>
  Cases_on `id = "x"` >> gvs[] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

Theorem joint_membership_pre:
  expr_body_pre joint_cenv joint_cx joint_env local_membership_fixture joint_es
Proof
  simp[exprSimHypsDefsTheory.expr_body_pre_def, joint_source_invariant,
       local_membership_fixture_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256,
                   vyperValueTheory.type_slot_size_def] >>
  conj_tac >- (EVAL_TAC >>
    CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
    qexists_tac `Fixed 1` >> simp[]) >>
  qexists_tac `[]` >>
  simp[vyperInterpreterTheory.lookup_function_def,
       vyperTypeCallGraphSoundnessTheory.call_edge_rel_def,
       relationTheory.irreflexive_def] >>
  once_rewrite_tac[relationTheory.TC_CASES1] >>
  simp[vyperTypeCallGraphSoundnessTheory.call_edge_rel_def]
QED

Theorem joint_membership_evaluation:
  bind (eval_expr joint_cx local_membership_fixture) (read_result joint_cx)
    joint_es = (INL (BoolV T),joint_es)
Proof
  simp[local_membership_fixture_def, vyperInterpreterTheory.evaluate_def,
       bind_def, return_def, ignore_bind_def, read_result_def,
       type_check_def, assert_def, get_scopes_def, get_accounts_def,
       builtin_args_length_ok_def, vyperValueTheory.compatible_bound_def,
       vyperASTTheory.expr_type_def, joint_es_def, probe_es_def,
       probe_make_array_builtin, probe_in_builtin, lookup_scopes_def,
       read_place_def, read_memory_path_def, lift_option_type_def, lift_sum_def,
       evaluate_subscripts_def, FLOOKUP_UPDATE]
QED
