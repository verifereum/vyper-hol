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


Theorem nested_external_slice_ret_ty[local]:
  stmt_env nested_external_slice_cenv NoLoop NoneT
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1))) =
  stmt_env nested_external_slice_cenv NoLoop (BaseT BoolT)
    (AugAssign (BaseT (UintT 256)) nested_reach_target Sub
      (Literal (BaseT (UintT 256)) (IntL 1)))
Proof
  simp[loweringPostsTheory.stmt_env_def, compile_stmt_def,
       declare_stmt_local_def]
QED

Theorem nested_external_slice_label[local]:
  nested_external_slice_end.cs_current_bb = "fn_probe"
Proof
  rewrite_tac[nested_external_slice_end_def, nested_external_slice_cenv_def,
    nested_external_compile_env] >>
  CONV_TAC (LAND_CONV (RESTR_EVAL_CONV [``function_selector``, ``calldata_method_id``])) >> REFL_TAC
QED

(* Shared concrete output avoids repeating compilation in block witnesses. *)
Definition nested_external_insts_def:
  nested_external_insts = MAP (\(n,opc,args,outs).
    <|inst_id := n; inst_opcode := opc; inst_operands := args; inst_outputs := outs|>)
  [(10,CALLVALUE,[],["%6"]);
   (11,ISZERO,[Var "%6"],["%7"]);
   (12,ASSERT,[Var "%7"],[]);
   (13,SLOAD,[Lit 0w],["%8"]);
   (14,LT,[Lit 0w;Var "%8"],["%9"]);
   (15,ISZERO,[Var "%9"],["%10"]);
   (16,OR,[Lit 0w;Var "%10"],["%11"]);
   (17,ISZERO,[Var "%11"],["%12"]);
   (18,ASSERT,[Var "%12"],[]);
   (19,ADD,[Lit 0w;Lit 1w],["%13"]);
   (20,MUL,[Lit 0w;Lit 2w],["%14"]);
   (21,ADD,[Var "%13";Var "%14"],["%15"]);
   (22,SLOAD,[Var "%15"],["%16"]);
   (23,LT,[Lit 0w;Var "%16"],["%17"]);
   (24,ISZERO,[Var "%17"],["%18"]);
   (25,OR,[Lit 0w;Var "%18"],["%19"]);
   (26,ISZERO,[Var "%19"],["%20"]);
   (27,ASSERT,[Var "%20"],[]);
   (28,ADD,[Var "%15";Lit 1w],["%21"]);
   (29,MUL,[Lit 0w;Lit 1w],["%22"]);
   (30,ADD,[Var "%21";Var "%22"],["%23"]);
   (31,ALLOCA,[Lit 32w],["%24"]);
   (32,INVOKE,[Label "internal 0 f()_runtime"],["%25"]);
   (33,ADD,[Var "%24";Lit 0w],["%26"]);
   (34,MSTORE,[Var "%26";Var "%25"],[]);
   (35,MLOAD,[Var "%24"],["%27"]);
   (36,LT,[Var "%27";Lit 1w],["%28"]);
   (37,ISZERO,[Var "%28"],["%29"]);
   (38,OR,[Lit 0w;Var "%29"],["%30"]);
   (39,ISZERO,[Var "%30"],["%31"]);
   (40,ASSERT,[Var "%31"],[]);
   (41,MUL,[Var "%27";Lit 1w],["%32"]);
   (42,ADD,[Var "%23";Var "%32"],["%33"]);
   (43,SLOAD,[Var "%33"],["%34"]);
   (44,SUB,[Var "%34";Lit 1w],["%35"]);
   (45,GT,[Var "%35";Var "%34"],["%36"]);
   (46,ISZERO,[Var "%36"],["%37"]);
   (47,ASSERT,[Var "%37"],[]);
   (48,SSTORE,[Var "%33";Var "%35"],[])]
End

Theorem nested_external_slice_insts[local]:
  nested_external_slice_end.cs_current_insts = nested_external_insts
Proof
  rewrite_tac[nested_external_slice_end_def, nested_external_slice_cenv_def,
    nested_external_compile_env] >>
  CONV_TAC (LAND_CONV (RESTR_EVAL_CONV [``function_selector``, ``calldata_method_id``])) >>
  simp[nested_external_insts_def]
QED

Theorem nested_external_slice_emitted[local]:
  emitted_blocks nested_external_slice_start nested_external_slice_end = []
Proof
  rewrite_tac[nested_external_slice_end_def, nested_external_slice_cenv_def,
    nested_external_compile_env] >>
  CONV_TAC (LAND_CONV (RESTR_EVAL_CONV [``function_selector``, ``calldata_method_id``])) >>
  REFL_TAC
QED

