(* Exact Python-oracle bytecode checks for evaluator-small scalar operator fixtures. *)

Theory evalCompilerBytecodeScalarOperators
Ancestors evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

Theorem scalar_bits_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities) scalar_bits_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_bits.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_shifts_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities) scalar_shifts_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_shifts.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_compare_eq_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_compare_eq_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_compare_eq.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_compare_order_uint_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_compare_order_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_compare_order_uint.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_compare_order_int_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_compare_order_int_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_compare_order_int.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_minmax_uint_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_minmax_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_minmax_uint.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_minmax_int_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    scalar_minmax_int_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_minmax_int.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_unary_i2w_neg_num:
  ∀n. i2w (-&n) = -n2w n
Proof
  Cases_on `n` >> simp[i2w_def]
QED
val () = computeLib.upd_compset
  (computeLib.add_thms [scalar_unary_i2w_neg_num])
val scalar_unary_policy_eval = EVAL
  ``resolve_o1_policy (o1_policy prague_capabilities)``
val scalar_unary_rpolicy = optionSyntax.dest_some
  (rhs (concl scalar_unary_policy_eval))
val scalar_unary_lower_runtime_eval = save_thm
  ("scalar_unary_lower_runtime_eval",
   EVAL ``lower_vyper_runtime_unit scalar_unary_program
      ^scalar_unary_rpolicy``)
val scalar_unary_runtime_unit = optionSyntax.dest_some
  (rhs (concl scalar_unary_lower_runtime_eval))
Theorem scalar_unary_lower_runtime_computed: T
Proof
  simp[]
QED
val scalar_unary_pipeline_eval = save_thm
  ("scalar_unary_pipeline_eval",
   EVAL ``run_venom_pipeline (K T) (K T) (K T)
      ^scalar_unary_rpolicy o1_pipeline_spec ^scalar_unary_runtime_unit``)
val scalar_unary_out = optionSyntax.dest_some
  (rhs (concl scalar_unary_pipeline_eval))
val scalar_unary_final_unit = rhs (concl (EVAL
  ``(^scalar_unary_out).po_unit``))
Theorem scalar_unary_pipeline_computed: T
Proof
  simp[]
QED
val scalar_unary_finalize_eval = save_thm
  ("scalar_unary_finalize_eval",
   EVAL ``finalize_codegen (K SOME) ^scalar_unary_rpolicy
      ^scalar_unary_final_unit``)
val scalar_unary_runtime_bytes = optionSyntax.dest_some
  (rhs (concl scalar_unary_finalize_eval))
val scalar_unary_lower_deploy_eval = save_thm
  ("scalar_unary_lower_deploy_eval",
   EVAL ``lower_vyper_deploy_unit scalar_unary_program
      ^scalar_unary_rpolicy ^scalar_unary_runtime_bytes``)
val scalar_unary_deploy_unit = optionSyntax.dest_some
  (rhs (concl scalar_unary_lower_deploy_eval))
val scalar_unary_deploy_pipeline_eval = save_thm
  ("scalar_unary_deploy_pipeline_eval",
   EVAL ``run_venom_pipeline (K T) (K T) (K T)
      ^scalar_unary_rpolicy o1_pipeline_spec ^scalar_unary_deploy_unit``)
val scalar_unary_deploy_out = optionSyntax.dest_some
  (rhs (concl scalar_unary_deploy_pipeline_eval))
val scalar_unary_final_deploy_unit = rhs (concl (EVAL
  ``(^scalar_unary_deploy_out).po_unit``))
val scalar_unary_finalize_deploy_eval = save_thm
  ("scalar_unary_finalize_deploy_eval",
   EVAL ``finalize_codegen (K SOME) ^scalar_unary_rpolicy
      ^scalar_unary_final_deploy_unit``)
val scalar_unary_compile_step0 = SIMP_CONV pure_ss
  [compileVyperTheory.compile_vyper_def,
   compileVyperTheory.compile_vyper_with_def,
   compileVyperTheory.checked_unit_pipeline_def,
   optionTheory.option_case_def, boolTheory.COND_CLAUSES,
   scalar_unary_policy_eval, scalar_unary_lower_runtime_eval,
   scalar_unary_pipeline_eval, scalar_unary_finalize_eval,
   scalar_unary_lower_deploy_eval, scalar_unary_deploy_pipeline_eval,
   scalar_unary_finalize_deploy_eval, LET_THM, pairTheory.FST,
   pairTheory.SND, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  ``compile_vyper (K SOME) (o1_policy prague_capabilities)
      scalar_unary_program``
val scalar_unary_compile_eval = TRANS scalar_unary_compile_step0
  (EVAL (rhs (concl scalar_unary_compile_step0)))
val scalar_unary_oracle_eq = EQT_ELIM (EVAL (mk_eq
  (rhs (concl scalar_unary_compile_eval),
   ``SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_unary.hex")``)))
val scalar_unary_matches_python_oracle = save_thm
  ("scalar_unary_matches_python_oracle",
   TRANS scalar_unary_compile_eval scalar_unary_oracle_eq)
