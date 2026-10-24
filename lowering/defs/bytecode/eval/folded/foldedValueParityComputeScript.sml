(* Shared checked computations and the runtime/deploy composition boundary. *)
Theory foldedValueParityCompute
Ancestors
  compileVyper contractABI exprLowering supportedProgram concretizeMemLocDefs
  codegenReadyCompute byte option alist integer_word
Libs
  cv_transLib wordsLib finite_mapLib vyperCheckContractFrontendLib jsonASTLib
  evalCompilerBytecodeLib memoryStoreWitnessLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]);

Theorem parity_uint_selector[compute]:
  function_selector "f" [Uint 256] = [179w; 222w; 100w; 139w]
Proof
  CONV_TAC cv_eval
QED

Theorem parity_nullary_selector[compute]:
  function_selector "f" [] = [38w; 18w; 31w; 240w]
Proof
  CONV_TAC cv_eval
QED

val () = cv_auto_trans largest_pow_base_def;
Theorem parity_cube_base_bound[compute]:
  largest_pow_base 3 256 F = 48740834812604276470692694
Proof
  CONV_TAC cv_eval
QED

Definition parity_policy_def:
  parity_policy = THE (resolve_o1_policy (o1_policy all_capabilities))
End

Theorem parity_policy_resolved:
  resolve_o1_policy (o1_policy all_capabilities) = SOME parity_policy
Proof
  simp[parity_policy_def] >> EVAL_TAC
QED

Definition parity_runtime_def:
  parity_runtime tops =
    case lower_vyper_runtime_unit tops parity_policy of
      NONE => NONE
    | SOME unit =>
        checked_unit_pipeline
          (λrp u. run_venom_pipeline (K T) (K T) (K T) rp o1_pipeline_spec u)
          (K SOME) parity_policy unit
End

Definition parity_deploy_def:
  parity_deploy tops runtime =
    case lower_vyper_deploy_unit tops parity_policy runtime of
      NONE => NONE
    | SOME unit =>
        checked_unit_pipeline
          (λrp u. run_venom_pipeline (K T) (K T) (K T) rp o1_pipeline_spec u)
          (K SOME) parity_policy unit
End

Theorem parity_compile_stages:
  parity_runtime tops = SOME runtime ∧
  parity_deploy tops runtime = SOME deploy ⇒
  compile_vyper (K SOME) (o1_policy all_capabilities) tops =
    SOME (deploy, runtime)
Proof
  strip_tac >>
  simp[compile_vyper_def, compile_vyper_with_def, parity_policy_resolved] >>
  Cases_on `lower_vyper_runtime_unit tops parity_policy` >>
  gvs[parity_runtime_def] >>
  Cases_on `lower_vyper_deploy_unit tops parity_policy runtime` >>
  gvs[parity_deploy_def]
QED
