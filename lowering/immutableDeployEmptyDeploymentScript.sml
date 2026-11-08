(* Shared deployment fixture for the empty immutable gate. *)
Theory immutableDeployEmptyDeployment
Ancestors
  immutableDeployEmptyFixture compileVyper vyperCompiler venomCompilerTypes
  bodySim vyperContext typedCopyMetadata compileEnv

Definition empty_immutable_policy_def:
  empty_immutable_policy =
    <|rpol_target := all_capabilities; rpol_frontend_dispatch := Linear;
      rpol_final_assembly := FAP_Optimize|>
End

Theorem empty_immutable_lowering_succeeds:
  IS_SOME (lower_vyper_deploy_unit empty_immutable_tops empty_immutable_policy [])
Proof
  rewrite_tac[empty_immutable_deploy_boundary, empty_immutable_policy_def] >>
  EVAL_TAC >>
  simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]
QED

Definition empty_immutable_unit_def:
  empty_immutable_unit =
    THE (lower_vyper_deploy_unit empty_immutable_tops empty_immutable_policy [])
End

Theorem empty_immutable_lowering_unit:
  lower_vyper_deploy_unit empty_immutable_tops empty_immutable_policy [] =
    SOME empty_immutable_unit
Proof
  mp_tac empty_immutable_lowering_succeeds >>
  Cases_on `lower_vyper_deploy_unit empty_immutable_tops empty_immutable_policy []` >>
  simp[empty_immutable_unit_def]
QED

Definition empty_immutable_ce_def:
  empty_immutable_ce =
    build_compile_env empty_immutable_tops Deploy Payable "__init__" [] NoneT [] F
End

Definition empty_immutable_cx_def:
  empty_immutable_cx = empty_evaluation_context with
    <|in_deploy := T; sources := [(0w,[(NONE,empty_immutable_tops)])]|>
End

Theorem empty_immutable_cx_metadata:
  get_module_code empty_immutable_cx NONE = SOME empty_immutable_tops /\
  get_tenv empty_immutable_cx = type_env empty_immutable_tops /\
  (!src ts. get_module_code empty_immutable_cx src = SOME ts ==> src = NONE)
Proof
  simp[empty_immutable_cx_def, empty_evaluation_context_def,
       empty_call_txn_def, get_module_code_def, get_tenv_def] >>
  EVAL_TAC >> simp[]
QED

Theorem empty_immutable_body_inv:
  body_inv empty_immutable_tops empty_immutable_unit.cu_context
    empty_immutable_ce empty_immutable_cx
Proof
  simp[body_inv_def, empty_immutable_program_supported,
       empty_immutable_cx_metadata, empty_immutable_cx_def,
       empty_immutable_ce_def, empty_immutable_constructor_probe,
       build_compile_env_ce_func_ids, build_compile_env_ce_func_param_types,
       build_compile_env_ce_func_info, build_compile_env_ce_func_return_type] >>
  conj_tac
  >- (qexistsl [`empty_immutable_policy`, `empty_immutable_unit`] >>
      conj_tac
      >- (qexists `[]` >> simp[empty_immutable_lowering_unit]) >>
      simp[empty_immutable_policy_def]) >>
  conj_tac
  >- (irule build_compile_env_struct_metadata_acyclic >> EVAL_TAC >> simp[]) >>
  simp[build_compile_env_def, empty_immutable_tops_def,
       cenv_module_pins_def, build_flag_info_def, allocate_args_def] >>
  EVAL_TAC >> simp[]
QED
