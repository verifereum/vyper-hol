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
  `compute_immutables_len (get_struct_fields (make_struct_fields_map equality_tops))
     equality_tops < 24576` by EVAL_TAC >>
  `external_return_buffer_ok equality_external_package` by
    simp[equality_external_package_def, package_external_fn_def,
         external_return_buffer_ok_def, compileEnvTheory.is_word_type_def] >>
  `fn_allocs_ok equality_tops
     (View,F,F,"probe",[],[],BaseT BoolT,[Return (SOME equality_fixture)])` by
    EVAL_TAC >>
  `~external_has_defaults
     (View,F,F,"probe",[],([]:expr list),BaseT BoolT,
      [Return (SOME equality_fixture)])` by
    simp[external_has_defaults_def] >>
  simp[lower_vyper_runtime_unit_def, equality_classification,
       contextTheory.global_nonreentrant_slot_def,
       equality_selectors, GSYM equality_external_package_def,
       equality_external_package_target, compute_selector_def,
       equality_selector_def, equality_run_lowering] >>
  simp[package_fallback_fn_def, set_fallback_package_target_def,
       equality_run_lowering] >> simp[external_has_defaults_def]
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
