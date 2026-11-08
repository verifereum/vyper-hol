(* A complete source caller, rather than an unregistered raw target function. *)
Theory augAssignNestedCallerProbe
Ancestors
  augAssignNestedNormalizedProbe compileVyper vyperCompiler vyperTypeSystem
  bodySim vyperTypeInvariants vyperContext analysisSimDefs
Libs finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])

Definition nested_caller_tops_def:
  nested_caller_tops = nested_reach_tops ++
    [FunctionDecl Internal Nonpayable F F "probe" [] [] NoneT
      [AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1)); Return NONE]]
End

Definition nested_caller_cx_def:
  nested_caller_cx = nested_valid_cx with sources := [(0w,[(NONE,nested_caller_tops)])]
End

Definition nested_caller_env_def:
  nested_caller_env = nested_premise_env with fn_sigs :=
    nested_premise_env.fn_sigs |+ ((NONE,"probe"),
      <|param_types := []; num_defaults := 0; ret_ty := NoneT|>)
End

Definition nested_caller_unit_def:
  nested_caller_unit = THE
    (lower_vyper_runtime_unit nested_caller_tops nested_premise_policy)
End

Definition nested_caller_cenv_def:
  nested_caller_cenv = (build_compile_env nested_caller_tops Internal Nonpayable
    "probe" [] NoneT [] F) with ce_target := K T
End

Theorem nested_caller_unsupported:
  ~supported_program nested_caller_tops
Proof
  EVAL_TAC
QED

Theorem nested_caller_internal_call_present:
  supported_stmts_expr_exists expr_internal_call_root
    [AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1)); Return NONE]
Proof
  EVAL_TAC
QED
