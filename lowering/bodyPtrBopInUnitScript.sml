Theory bodyPtrBopInUnit
Ancestors
  bodyPtrBopInUnitPackaging bodyPtrBopInUnitMetadata bodyPtrBopInSourceFrame
  compileVyper vyperCompiler

(* Name the actual selector without evaluating its cryptographic hash. *)
Definition equality_selector_def:
  equality_selector = FST (compute_selector (type_env equality_tops) "probe" [])
End

Theorem equality_lower_runtime:
  lower_vyper_runtime_unit equality_tops probe_policy =
    SOME <| cu_context := equality_runtime_context equality_selector;
            cu_data_segment := [] |>
Proof
  simp[lower_vyper_runtime_unit_def, equality_classification, equality_nkeys,
       equality_selectors, GSYM equality_external_package_def,
       equality_external_package_target, compute_selector_def,
       equality_selector_def, equality_run_lowering] >>
  simp[package_fallback_fn_def, set_fallback_package_target_def,
       equality_run_lowering] >> EVAL_TAC
QED

(* This is the entry function actually packaged by the runtime compiler. *)
Definition equality_runtime_function_def:
  equality_runtime_function sel = HD (equality_runtime_context sel).ctx_functions
End

Theorem equality_function_member:
  MEM (equality_runtime_function sel) (equality_runtime_context sel).ctx_functions /\
  (equality_runtime_function sel).fn_name = "__entry"
Proof
  EVAL_TAC
QED

Theorem equality_function_eq:
  MAP (\i. (i.inst_id,i.inst_opcode,i.inst_operands,i.inst_outputs))
    (FILTER (\i. i.inst_opcode = EQ) (fn_insts (equality_runtime_function sel))) =
  [(6,EQ,[Var "%4"; Lit (n2w sel)],["%5"]);
   (23,EQ,[Var "%10"; Var "%13"],["%14"])]
Proof
  EVAL_TAC
QED

Theorem equality_function_lookup:
  lookup_function "__entry" (equality_runtime_context sel).ctx_functions =
    SOME (equality_runtime_function sel)
Proof
  EVAL_TAC
QED
