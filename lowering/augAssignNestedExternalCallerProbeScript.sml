(* External visibility permits the saved-place index call in the source caller. *)
Theory augAssignNestedExternalCallerProbe
Ancestors
  augAssignNestedCallerProbe compileVyper vyperCompiler bodySim
Libs finite_mapLib computeLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])

Definition nested_external_tops_def:
  nested_external_tops = nested_reach_tops ++
    [FunctionDecl External Nonpayable F F "probe" [] [] NoneT
      [AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1)); Return NONE]]
End

Definition nested_external_cx_def:
  nested_external_cx = nested_valid_cx with sources := [(0w,[(NONE,nested_external_tops)])]
End

Definition nested_external_env_def:
  nested_external_env = nested_caller_env
End

Definition nested_external_unit_def:
  nested_external_unit = THE
    (lower_vyper_runtime_unit nested_external_tops nested_premise_policy)
End

Theorem nested_external_supported:
  supported_program nested_external_tops
Proof
  EVAL_TAC
QED

