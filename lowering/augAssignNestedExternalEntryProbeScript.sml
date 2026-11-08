(* Applicability of the actual External caller slice, separate from semantics. *)
Theory augAssignNestedExternalEntryProbe
Ancestors
  augAssignNestedExternalCallerProbe compileVyper moduleLowering stmtLowering
  selectorDispatch exprLoweringProps stmtSimDefs
Libs finite_mapLib computeLib supportedEvalLib

val () = supportedEvalLib.configure ()
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])

Definition nested_external_slice_cenv_def:
  nested_external_slice_cenv = build_compile_env nested_external_tops External Nonpayable
    "probe" [] NoneT
    [AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1)); Return NONE] F
End

Definition nested_external_slice_start_def:
  nested_external_slice_start = SND
    ((do fallback <- fresh_label "fallback";
         compile_selector_dispatch_linear [(3075143081,"fn_probe")] fallback;
         new_block "fn_probe";
         compile_entry_checks 4 F
      od) (initial_compile_state "__entry"))
End

Definition nested_external_slice_end_def:
  nested_external_slice_end = SND
    (stmt_env nested_external_slice_cenv NoLoop NoneT
      (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
        (Literal (BaseT (UintT 256)) (IntL 1))) nested_external_slice_start)
End

Definition nested_external_entry_fn_def:
  nested_external_entry_fn = THE
    (lookup_function "__entry" nested_external_unit.cu_context.ctx_functions)
End

Theorem nested_external_slice_position:
  nested_external_slice_start.cs_current_bb = "fn_probe" /\
  LENGTH nested_external_slice_start.cs_current_insts = 3 /\
  ~block_is_terminated nested_external_slice_start
Proof
  EVAL_TAC
QED

