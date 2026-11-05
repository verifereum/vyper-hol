Theory bodyPtrBytestringBuiltinsSourceFrame
Ancestors
  compileVyper venomCompilerTypes bodySim
  bodyPtrBytestringBuiltinsOrderRun

(* Concrete policy abbreviation for the empty-program source-frame probe. *)
Definition order_frame_policy_def:
  order_frame_policy = <|
    rpol_target := (K T);
    rpol_frontend_dispatch := Linear;
    rpol_final_assembly := FAP_Optimize
  |>
End

Theorem order_frame_lowering_exists:
  IS_SOME (lower_vyper_runtime_unit [] order_frame_policy)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

(* Name the computed unit without duplicating its instruction-list literal. *)
Definition order_frame_unit_def:
  order_frame_unit = THE (lower_vyper_runtime_unit [] order_frame_policy)
End

Theorem order_frame_lowering:
  lower_vyper_runtime_unit [] order_frame_policy = SOME order_frame_unit
Proof
  mp_tac order_frame_lowering_exists >>
  Cases_on `lower_vyper_runtime_unit [] order_frame_policy` >>
  simp[order_frame_unit_def]
QED

(* Supply the empty main module required by the source body invariant. *)
Definition order_frame_cx_def:
  order_frame_cx = empty_evaluation_context with
    sources := [(empty_call_txn.target, [(NONE, [])])]
End

Theorem order_frame_body_inv:
  body_inv [] order_frame_unit.cu_context order_run_env order_frame_cx
Proof
  rw[body_inv_def]
  >- EVAL_TAC
  >- (qexistsl_tac [`order_frame_policy`, `order_frame_unit`] >>
      simp[order_frame_lowering, order_frame_cx_def,
        vyperContextTheory.empty_evaluation_context_def,
        order_run_env_def, build_compile_env_def,
        order_frame_policy_def, venomPolicyTypesTheory.all_capabilities_def] >>
      EVAL_TAC)
  >> EVAL_TAC
  >> gvs[vyperContextTheory.get_tenv_def, order_frame_cx_def,
      vyperContextTheory.empty_evaluation_context_def,
      vyperContextTheory.type_env_all_modules_def,
      vyperContextTheory.type_env_for_module_def]
QED
