(* Checked runtime-pipeline staging for the scalar_convert_decimal fixture. *)

Theory evalCompilerBytecodeScalarConvertDecimal
Ancestors evalCompilerBytecodeScalarWordEval evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``type_bounds``)
    |> computeLib.add_thms
         [scalar_decimal_type_bounds_eval,
          scalar_int8_type_bounds_eval,
          scalar_int256_type_bounds_eval,
          w2n_scalar_decimal_lo_word_eval,
          w2n_scalar_decimal_hi_word_eval,
          w2i_scalar_decimal_lo_word_eval,
          w2i_scalar_decimal_hi_word_eval,
          scalar_decimal_lo_word_eq_word,
          word_eq_scalar_decimal_lo_word,
          scalar_decimal_hi_word_eq_word,
          word_eq_scalar_decimal_hi_word,
          w2n_scalar_int256_min_word_eval,
          w2i_scalar_int256_min_word_eval,
          w2n_scalar_int256_max_word_eval,
          w2i_scalar_int256_max_word_eval,
          scalar_int256_min_word_eq_word,
          word_eq_scalar_int256_min_word,
          scalar_int256_max_word_eq_word,
          word_eq_scalar_int256_max_word,
          compileEnvTheory.type_bounds_def])
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``mk_convert_op``)
    |> (fn cs' => computeLib.scrub_const cs' ``compile_type_convert``)
    |> (fn cs' => computeLib.scrub_const cs' ``compile_type_builtin_dispatch``)
    |> (fn cs' => computeLib.scrub_const cs' ``compile_expr``)
    |> computeLib.add_thms
         [scalar_compile_expr_decimal_literal_to_int8_eval,
          scalar_dispatch_convert_decimal_literal_to_int8_eval,
          scalar_mk_convert_bytes32_to_decimal_eval,
          scalar_compile_convert_bytes32_to_decimal_eval,
          scalar_mk_convert_decimal_to_int8_eval,
          scalar_compile_convert_decimal_to_int8_eval])
val () = Globals.max_print_depth := 20

Definition scalar_convert_decimal_runtime_pipeline_def:
  scalar_convert_decimal_runtime_pipeline tops =
    case resolve_o1_policy (o1_policy all_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME unit =>
            OPTION_MAP (λout. (rpolicy,out))
              (run_venom_pipeline (K T) (K T) (K T)
                 rpolicy o1_pipeline_spec unit)
End

val scalar_convert_decimal_policy_eval = save_thm
  ("scalar_convert_decimal_policy_eval",
   EVAL ``resolve_o1_policy (o1_policy all_capabilities)``)
Theorem scalar_convert_decimal_policy_computed: T
Proof
  simp[]
QED
val scalar_convert_decimal_resolved_policy = optionSyntax.dest_some
  (rhs (concl scalar_convert_decimal_policy_eval))
val scalar_convert_decimal_package_eval = save_thm
  ("scalar_convert_decimal_package_eval",
   EVAL ``package_external_fn scalar_convert_decimal_program F
      (assign_nkeys scalar_convert_decimal_program 0)
      (let (ext_fns,int_fns,fb,ctor) =
         classify_functions scalar_convert_decimal_program
       in HD ext_fns)``)
Theorem scalar_convert_decimal_package_computed: T
Proof
  simp[]
QED
val () = computeLib.upd_compset
  (computeLib.add_thms [scalar_convert_decimal_package_eval])

(* Stage source lowering around the single expensive function body. *)
val scalar_convert_decimal_tops = ``scalar_convert_decimal_program``
val scalar_convert_decimal_type_env_eval = save_thm
  ("scalar_convert_decimal_type_env_eval",
   EVAL ``type_env ^scalar_convert_decimal_tops``)
val scalar_convert_decimal_type_env =
  rhs (concl scalar_convert_decimal_type_env_eval)
val scalar_convert_decimal_nkeys_eval = save_thm
  ("scalar_convert_decimal_nkeys_eval",
   EVAL ``assign_nkeys ^scalar_convert_decimal_tops 0``)
val scalar_convert_decimal_nkeys = rhs (concl scalar_convert_decimal_nkeys_eval)
val scalar_convert_decimal_classify_eval = save_thm
  ("scalar_convert_decimal_classify_eval",
   EVAL ``classify_functions ^scalar_convert_decimal_tops``)
val scalar_convert_decimal_classified =
  rhs (concl scalar_convert_decimal_classify_eval)
val scalar_convert_decimal_external_sources =
  #1 (pairSyntax.dest_pair scalar_convert_decimal_classified)
val scalar_convert_decimal_classified_tail1 =
  #2 (pairSyntax.dest_pair scalar_convert_decimal_classified)
val scalar_convert_decimal_internal_sources =
  #1 (pairSyntax.dest_pair scalar_convert_decimal_classified_tail1)
val scalar_convert_decimal_classified_tail2 =
  #2 (pairSyntax.dest_pair scalar_convert_decimal_classified_tail1)
val scalar_convert_decimal_fallback_source =
  #1 (pairSyntax.dest_pair scalar_convert_decimal_classified_tail2)
val scalar_convert_decimal_selectors_eval = save_thm
  ("scalar_convert_decimal_selectors_eval",
   EVAL ``build_selectors ^scalar_convert_decimal_type_env
      ^scalar_convert_decimal_external_sources``)
val scalar_convert_decimal_selectors =
  rhs (concl scalar_convert_decimal_selectors_eval)
val scalar_convert_decimal_external_fns_eval = save_thm
  ("scalar_convert_decimal_external_fns_eval",
   EVAL ``MAP (set_external_package_target
                 (^scalar_convert_decimal_resolved_policy).rpol_target o
               package_external_fn ^scalar_convert_decimal_tops F
                 ^scalar_convert_decimal_nkeys)
      ^scalar_convert_decimal_external_sources``)
val scalar_convert_decimal_external_fns =
  rhs (concl scalar_convert_decimal_external_fns_eval)
val scalar_convert_decimal_internal_fns_eval = save_thm
  ("scalar_convert_decimal_internal_fns_eval",
   EVAL ``MAP (set_internal_package_target
                 (^scalar_convert_decimal_resolved_policy).rpol_target o
               package_internal_fn ^scalar_convert_decimal_tops F
                 ^scalar_convert_decimal_nkeys F 0)
      ^scalar_convert_decimal_internal_sources``)
val scalar_convert_decimal_internal_fns =
  rhs (concl scalar_convert_decimal_internal_fns_eval)
val scalar_convert_decimal_fallback_fn_eval = save_thm
  ("scalar_convert_decimal_fallback_fn_eval",
   EVAL ``set_fallback_package_target
      (^scalar_convert_decimal_resolved_policy).rpol_target
      (package_fallback_fn ^scalar_convert_decimal_tops F
        ^scalar_convert_decimal_nkeys ^scalar_convert_decimal_fallback_source)``)
val scalar_convert_decimal_fallback_fn =
  rhs (concl scalar_convert_decimal_fallback_fn_eval)
val scalar_convert_decimal_state0_eval = save_thm
  ("scalar_convert_decimal_state0_eval",
   EVAL ``initial_compile_state "__entry"``)
val scalar_convert_decimal_state0 = rhs (concl scalar_convert_decimal_state0_eval)
val scalar_convert_decimal_fallback_label_eval = save_thm
  ("scalar_convert_decimal_fallback_label_eval",
   EVAL ``fresh_label "fallback" ^scalar_convert_decimal_state0``)
val scalar_convert_decimal_fallback_label_pair =
  rhs (concl scalar_convert_decimal_fallback_label_eval)
val scalar_convert_decimal_fallback_label =
  #1 (pairSyntax.dest_pair scalar_convert_decimal_fallback_label_pair)
val scalar_convert_decimal_state1 =
  #2 (pairSyntax.dest_pair scalar_convert_decimal_fallback_label_pair)
val scalar_convert_decimal_linear_selectors_eval = save_thm
  ("scalar_convert_decimal_linear_selectors_eval",
   EVAL ``MAP (λ(sel,lbl,_). (sel,lbl)) ^scalar_convert_decimal_selectors``)
val scalar_convert_decimal_linear_selectors =
  rhs (concl scalar_convert_decimal_linear_selectors_eval)
val scalar_convert_decimal_dispatch_eval = save_thm
  ("scalar_convert_decimal_dispatch_eval",
   EVAL ``compile_selector_dispatch_linear
      ^scalar_convert_decimal_linear_selectors
      ^scalar_convert_decimal_fallback_label ^scalar_convert_decimal_state1``)
val scalar_convert_decimal_dispatch_pair =
  rhs (concl scalar_convert_decimal_dispatch_eval)
val scalar_convert_decimal_state2 =
  #2 (pairSyntax.dest_pair scalar_convert_decimal_dispatch_pair)
fun scalar_convert_decimal_dest_tuple tm =
  if pairSyntax.is_pair tm then
    let val (x,xs) = pairSyntax.dest_pair tm
    in x :: scalar_convert_decimal_dest_tuple xs end
  else [tm]
val (scalar_convert_decimal_external_fn_terms,_) =
  listSyntax.dest_list scalar_convert_decimal_external_fns
val scalar_convert_decimal_external_fields =
  scalar_convert_decimal_dest_tuple
    (hd scalar_convert_decimal_external_fn_terms)
val scalar_convert_decimal_entry =
  List.nth (scalar_convert_decimal_external_fields,0)
val scalar_convert_decimal_cenv =
  List.nth (scalar_convert_decimal_external_fields,1)
val scalar_convert_decimal_pos_args =
  List.nth (scalar_convert_decimal_external_fields,2)
val scalar_convert_decimal_min_cds =
  List.nth (scalar_convert_decimal_external_fields,3)
val scalar_convert_decimal_is_payable =
  List.nth (scalar_convert_decimal_external_fields,4)
val scalar_convert_decimal_is_nr =
  List.nth (scalar_convert_decimal_external_fields,5)
val scalar_convert_decimal_nkey =
  List.nth (scalar_convert_decimal_external_fields,6)
val scalar_convert_decimal_use_trans =
  List.nth (scalar_convert_decimal_external_fields,7)
val scalar_convert_decimal_is_view =
  List.nth (scalar_convert_decimal_external_fields,8)
val scalar_convert_decimal_body =
  List.nth (scalar_convert_decimal_external_fields,9)
val scalar_convert_decimal_ret_type =
  List.nth (scalar_convert_decimal_external_fields,10)
val scalar_convert_decimal_new_block_eval = save_thm
  ("scalar_convert_decimal_new_block_eval",
   EVAL ``new_block ^scalar_convert_decimal_entry
      ^scalar_convert_decimal_state2``)
val scalar_convert_decimal_state3 = #2 (pairSyntax.dest_pair
  (rhs (concl scalar_convert_decimal_new_block_eval)))
val scalar_convert_decimal_entry_checks_eval = save_thm
  ("scalar_convert_decimal_entry_checks_eval",
   EVAL ``compile_entry_checks ^scalar_convert_decimal_min_cds
      ^scalar_convert_decimal_is_payable ^scalar_convert_decimal_state3``)
val scalar_convert_decimal_state4 = #2 (pairSyntax.dest_pair
  (rhs (concl scalar_convert_decimal_entry_checks_eval)))
val scalar_convert_decimal_register_args_eval = save_thm
  ("scalar_convert_decimal_register_args_eval",
   EVAL ``compile_register_positional_args ^scalar_convert_decimal_cenv
      ^scalar_convert_decimal_pos_args 4 ^scalar_convert_decimal_state4``)
val scalar_convert_decimal_register_args_pair =
  rhs (concl scalar_convert_decimal_register_args_eval)
val scalar_convert_decimal_body_cenv =
  #1 (pairSyntax.dest_pair scalar_convert_decimal_register_args_pair)
val scalar_convert_decimal_state5 =
  #2 (pairSyntax.dest_pair scalar_convert_decimal_register_args_pair)
val scalar_convert_decimal_collect_locals_eval = save_thm
  ("scalar_convert_decimal_collect_locals_eval",
   EVAL ``collect_locals ^scalar_convert_decimal_body``)
val scalar_convert_decimal_locals =
  rhs (concl scalar_convert_decimal_collect_locals_eval)
val scalar_convert_decimal_reserve_locals_eval = save_thm
  ("scalar_convert_decimal_reserve_locals_eval",
   EVAL ``reserve_local_ptrs ^scalar_convert_decimal_body_cenv
      ^scalar_convert_decimal_locals ^scalar_convert_decimal_state5``)
val scalar_convert_decimal_reserve_pair =
  rhs (concl scalar_convert_decimal_reserve_locals_eval)
val scalar_convert_decimal_body_cenv2 =
  #1 (pairSyntax.dest_pair scalar_convert_decimal_reserve_pair)
val scalar_convert_decimal_state6 =
  #2 (pairSyntax.dest_pair scalar_convert_decimal_reserve_pair)
val scalar_convert_decimal_ret_ty = optionSyntax.dest_some
  scalar_convert_decimal_ret_type
val (scalar_convert_decimal_stmt_terms,_) =
  listSyntax.dest_list scalar_convert_decimal_body
val scalar_convert_decimal_stmt = hd scalar_convert_decimal_stmt_terms
val scalar_convert_decimal_stmt_step1 = SIMP_CONV (srw_ss())
  [stmtLoweringTheory.compile_stmt_def,
   exprLoweringTheory.lower_value_def,
   scalar_compile_expr_decimal_literal_to_int8_eval,
   scalar_compile_convert_decimal_to_int8_eval,
   compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def, LET_THM, pairTheory.FST,
   pairTheory.SND, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  ``compile_stmt ^scalar_convert_decimal_body_cenv2 NoLoop
      ^scalar_convert_decimal_ret_ty ^scalar_convert_decimal_stmt
      ^scalar_convert_decimal_state6``
val scalar_convert_decimal_stmt_eval = save_thm
  ("scalar_convert_decimal_stmt_eval",
   TRANS scalar_convert_decimal_stmt_step1
     (EVAL (rhs (concl scalar_convert_decimal_stmt_step1))))
Theorem scalar_convert_decimal_stmt_computed: T
Proof
  simp[]
QED
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``compile_stmt``)
    |> computeLib.add_thms [scalar_convert_decimal_stmt_eval])
val scalar_convert_decimal_compile_stmts_defs =
  CONJUNCTS stmtLoweringTheory.compile_stmt_def
val scalar_convert_decimal_compile_stmts_cons_def =
  valOf (List.find
    (fn th => can (match_term ``compile_stmts c l t (s::ss)``)
      (lhs (concl (SPEC_ALL th))))
    scalar_convert_decimal_compile_stmts_defs)
val scalar_convert_decimal_compile_stmts_nil_def =
  valOf (List.find
    (fn th => can (match_term ``compile_stmts c l t []``)
      (lhs (concl (SPEC_ALL th))))
    scalar_convert_decimal_compile_stmts_defs)
val scalar_convert_decimal_block_terminated_eval = EVAL
  ``block_is_terminated ^scalar_convert_decimal_state6``
val scalar_convert_decimal_stmts_step1 = RATOR_CONV (REWR_CONV
  scalar_convert_decimal_compile_stmts_cons_def)
  ``compile_stmts ^scalar_convert_decimal_body_cenv2 NoLoop
      ^scalar_convert_decimal_ret_ty ^scalar_convert_decimal_body
      ^scalar_convert_decimal_state6``
val scalar_convert_decimal_stmts_step2 = SIMP_CONV pure_ss
  [compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_get_def, compileEnvTheory.comp_return_def,
   scalar_convert_decimal_block_terminated_eval,
   scalar_convert_decimal_stmt_eval,
   scalar_convert_decimal_compile_stmts_nil_def,
   boolTheory.COND_CLAUSES, LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl scalar_convert_decimal_stmts_step1))
val scalar_convert_decimal_stmts_eval = save_thm
  ("scalar_convert_decimal_stmts_eval",
   TRANS scalar_convert_decimal_stmts_step1
     scalar_convert_decimal_stmts_step2)
Theorem scalar_convert_decimal_stmts_computed: T
Proof
  simp[]
QED
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``compile_stmts``)
    |> computeLib.add_thms
  [scalar_convert_decimal_new_block_eval,
   scalar_convert_decimal_entry_checks_eval,
   scalar_convert_decimal_register_args_eval,
   scalar_convert_decimal_collect_locals_eval,
   scalar_convert_decimal_reserve_locals_eval,
   scalar_convert_decimal_stmts_eval])
val scalar_convert_decimal_state7 = #2 (pairSyntax.dest_pair
  (rhs (concl scalar_convert_decimal_stmts_eval)))
val scalar_convert_decimal_block_terminated7_eval = EVAL
  ``block_is_terminated ^scalar_convert_decimal_state7``
val scalar_convert_decimal_guarded_body_eval = save_thm
  ("scalar_convert_decimal_guarded_body_eval",
   SIMP_CONV pure_ss
    [moduleLoweringTheory.compile_guarded_body_def,
     scalar_convert_decimal_collect_locals_eval,
     scalar_convert_decimal_reserve_locals_eval,
     scalar_convert_decimal_stmts_eval,
     scalar_convert_decimal_block_terminated7_eval,
     compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
     compileEnvTheory.comp_return_def, compileEnvTheory.comp_get_def,
     boolTheory.COND_CLAUSES, LET_THM, pairTheory.FST, pairTheory.SND,
     pairTheory.UNCURRY_DEF, pairTheory.pair_case_def,
     optionTheory.option_case_def]
    ``compile_guarded_body ^scalar_convert_decimal_body_cenv
       ^scalar_convert_decimal_is_nr ^scalar_convert_decimal_nkey
       ^scalar_convert_decimal_use_trans ^scalar_convert_decimal_is_view
       ^scalar_convert_decimal_body ^scalar_convert_decimal_ret_type
       ^scalar_convert_decimal_state5``)
val scalar_convert_decimal_external_body_eval = save_thm
  ("scalar_convert_decimal_external_body_eval",
   SIMP_CONV pure_ss
    [moduleLoweringTheory.compile_external_function_body_def,
     scalar_convert_decimal_register_args_eval,
     scalar_convert_decimal_guarded_body_eval,
     compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
     compileEnvTheory.comp_return_def, LET_THM, pairTheory.FST,
     pairTheory.SND, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
    ``compile_external_function_body ^scalar_convert_decimal_cenv
       ^scalar_convert_decimal_pos_args ^scalar_convert_decimal_is_nr
       ^scalar_convert_decimal_nkey ^scalar_convert_decimal_use_trans
       ^scalar_convert_decimal_is_view ^scalar_convert_decimal_body
       ^scalar_convert_decimal_ret_type ^scalar_convert_decimal_state4``)
val scalar_convert_decimal_external_bodies_eval = save_thm
  ("scalar_convert_decimal_external_bodies_eval",
   SIMP_CONV pure_ss
    [moduleLoweringTheory.compile_external_fn_bodies_def,
     scalar_convert_decimal_new_block_eval,
     scalar_convert_decimal_entry_checks_eval,
     scalar_convert_decimal_external_body_eval,
     compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
     compileEnvTheory.comp_return_def, LET_THM, pairTheory.FST,
     pairTheory.SND, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
    ``compile_external_fn_bodies ^scalar_convert_decimal_external_fns
       ^scalar_convert_decimal_state2``)
Theorem scalar_convert_decimal_external_bodies_computed: T
Proof
  simp[]
QED
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs'
         ``compile_external_fn_bodies``)
    |> computeLib.add_thms
  [scalar_convert_decimal_type_env_eval, scalar_convert_decimal_nkeys_eval,
   scalar_convert_decimal_classify_eval, scalar_convert_decimal_selectors_eval,
   scalar_convert_decimal_external_fns_eval,
   scalar_convert_decimal_internal_fns_eval,
   scalar_convert_decimal_fallback_fn_eval,
   scalar_convert_decimal_state0_eval,
   scalar_convert_decimal_fallback_label_eval,
   scalar_convert_decimal_linear_selectors_eval,
   scalar_convert_decimal_dispatch_eval,
   scalar_convert_decimal_external_bodies_eval])
val scalar_convert_decimal_external_bodies_pair =
  rhs (concl scalar_convert_decimal_external_bodies_eval)
val scalar_convert_decimal_state8 =
  #2 (pairSyntax.dest_pair scalar_convert_decimal_external_bodies_pair)
val scalar_convert_decimal_fallback_block_eval = save_thm
  ("scalar_convert_decimal_fallback_block_eval",
   EVAL ``new_block ^scalar_convert_decimal_fallback_label
      ^scalar_convert_decimal_state8``)
val scalar_convert_decimal_state9 = #2 (pairSyntax.dest_pair
  (rhs (concl scalar_convert_decimal_fallback_block_eval)))
val scalar_convert_decimal_fallback_revert_eval = save_thm
  ("scalar_convert_decimal_fallback_revert_eval",
   EVAL ``emit_inst REVERT [Lit 0w; Lit 0w] []
      ^scalar_convert_decimal_state9``)
val scalar_convert_decimal_state10 = #2 (pairSyntax.dest_pair
  (rhs (concl scalar_convert_decimal_fallback_revert_eval)))
val scalar_convert_decimal_internal_bodies_eval = save_thm
  ("scalar_convert_decimal_internal_bodies_eval",
   EVAL ``compile_internal_fn_bodies ^scalar_convert_decimal_internal_fns
      ^scalar_convert_decimal_state10``)
val scalar_convert_decimal_state11 = #2 (pairSyntax.dest_pair
  (rhs (concl scalar_convert_decimal_internal_bodies_eval)))
val scalar_convert_decimal_entry_info_eval = save_thm
  ("scalar_convert_decimal_entry_info_eval",
   EVAL ``build_dense_entry_info ^scalar_convert_decimal_selectors
      ^scalar_convert_decimal_external_fns``)
val scalar_convert_decimal_entry_info =
  rhs (concl scalar_convert_decimal_entry_info_eval)
val scalar_convert_decimal_generate_runtime_step0 =
  RATOR_CONV (REWR_CONV moduleLoweringTheory.compile_generate_runtime_def)
    ``compile_generate_runtime ^scalar_convert_decimal_selectors
       ^scalar_convert_decimal_external_fns
       ^scalar_convert_decimal_internal_fns
       ^scalar_convert_decimal_fallback_fn Linear 0 0 []
       ^scalar_convert_decimal_entry_info ^scalar_convert_decimal_state0``
val scalar_convert_decimal_generate_runtime_step1 = SIMP_CONV pure_ss
  [venomPolicyTypesTheory.dispatch_strategy_case_def,
   optionTheory.option_case_def,
   compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def,
   scalar_convert_decimal_fallback_label_eval,
   scalar_convert_decimal_linear_selectors_eval,
   scalar_convert_decimal_dispatch_eval,
   scalar_convert_decimal_external_bodies_eval,
   scalar_convert_decimal_fallback_block_eval,
   scalar_convert_decimal_fallback_revert_eval,
   scalar_convert_decimal_internal_bodies_eval,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl scalar_convert_decimal_generate_runtime_step0))
val scalar_convert_decimal_generate_runtime_eval = save_thm
  ("scalar_convert_decimal_generate_runtime_eval",
   TRANS scalar_convert_decimal_generate_runtime_step0
     scalar_convert_decimal_generate_runtime_step1)
val scalar_convert_decimal_extract_context_eval = save_thm
  ("scalar_convert_decimal_extract_context_eval",
   EVAL ``extract_context_with_internals "__entry"
      ^scalar_convert_decimal_internal_fns ^scalar_convert_decimal_state11``)
val scalar_convert_decimal_context_data = optionSyntax.dest_some
  (rhs (concl scalar_convert_decimal_extract_context_eval))
val scalar_convert_decimal_context =
  #1 (pairSyntax.dest_pair scalar_convert_decimal_context_data)
val scalar_convert_decimal_policy_ok_eval = EVAL
  ``lowering_policy_ok ^scalar_convert_decimal_resolved_policy``
val scalar_convert_decimal_context_ok_eval = EVAL
  ``lowering_context_ok ^scalar_convert_decimal_context``
val scalar_convert_decimal_dispatch_policy_eval = EVAL
  ``(^scalar_convert_decimal_resolved_policy).rpol_frontend_dispatch``
val scalar_convert_decimal_run_lowering_term =
  ``run_lowering ^scalar_convert_decimal_selectors
      ^scalar_convert_decimal_external_fns
      ^scalar_convert_decimal_internal_fns
      ^scalar_convert_decimal_fallback_fn
      ^scalar_convert_decimal_resolved_policy 0 0 []
      ^scalar_convert_decimal_entry_info "__entry"``
val scalar_convert_decimal_run_lowering_step0 = REWR_CONV
  vyperCompilerTheory.run_lowering_def
  scalar_convert_decimal_run_lowering_term
val scalar_convert_decimal_run_lowering_step1 = PURE_REWRITE_CONV
  [scalar_convert_decimal_policy_ok_eval,
   scalar_convert_decimal_state0_eval,
   scalar_convert_decimal_dispatch_policy_eval]
  (rhs (concl scalar_convert_decimal_run_lowering_step0))
val scalar_convert_decimal_run_lowering_step2 = SIMP_CONV pure_ss
  [boolTheory.COND_CLAUSES, optionTheory.option_case_def,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl scalar_convert_decimal_run_lowering_step1))
val scalar_convert_decimal_run_lowering_step3 = PURE_REWRITE_CONV
  [scalar_convert_decimal_generate_runtime_eval]
  (rhs (concl scalar_convert_decimal_run_lowering_step2))
val scalar_convert_decimal_run_lowering_step4 = SIMP_CONV pure_ss
  [scalar_convert_decimal_extract_context_eval,
   scalar_convert_decimal_context_ok_eval,
   boolTheory.COND_CLAUSES, optionTheory.option_case_def,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl scalar_convert_decimal_run_lowering_step3))
val scalar_convert_decimal_run_lowering_eval = save_thm
  ("scalar_convert_decimal_run_lowering_eval",
   TRANS scalar_convert_decimal_run_lowering_step0
     (TRANS scalar_convert_decimal_run_lowering_step1
       (TRANS scalar_convert_decimal_run_lowering_step2
         (TRANS scalar_convert_decimal_run_lowering_step3
           scalar_convert_decimal_run_lowering_step4))))
val scalar_convert_decimal_runtime_unit_eval = save_thm
  ("scalar_convert_decimal_runtime_unit_eval",
   SIMP_CONV pure_ss
    ([compileVyperTheory.lower_vyper_runtime_unit_def,
      scalar_convert_decimal_type_env_eval,
      scalar_convert_decimal_nkeys_eval,
      scalar_convert_decimal_classify_eval,
      scalar_convert_decimal_selectors_eval,
      scalar_convert_decimal_external_fns_eval,
      scalar_convert_decimal_internal_fns_eval,
      scalar_convert_decimal_fallback_fn_eval,
      scalar_convert_decimal_entry_info_eval,
      scalar_convert_decimal_run_lowering_eval,
      LET_THM, pairTheory.FST, pairTheory.SND,
      pairTheory.UNCURRY_DEF, pairTheory.pair_case_def] @
     CONJUNCTS
       venomCompilerTypesTheory.resolved_compiler_policy_accessors)
    ``lower_vyper_runtime_unit scalar_convert_decimal_program
       ^scalar_convert_decimal_resolved_policy``)
Theorem scalar_convert_decimal_runtime_unit_computed: T
Proof
  simp[]
QED
val () = computeLib.upd_compset (computeLib.add_thms
  [scalar_convert_decimal_policy_eval,
   scalar_convert_decimal_runtime_unit_eval])

val scalar_convert_decimal_runtime_unit = optionSyntax.dest_some
  (rhs (concl scalar_convert_decimal_runtime_unit_eval))
val scalar_convert_decimal_pre_walk_eval = save_thm
  ("scalar_convert_decimal_pre_walk_eval",
   EVAL ``run_pipeline_stages ^scalar_convert_decimal_resolved_policy
      o1_pipeline_spec.ps_pre_walk_stages
      ^scalar_convert_decimal_runtime_unit
      (init_ir_supply ^scalar_convert_decimal_runtime_unit)``)
Theorem scalar_convert_decimal_pre_walk_computed: T
Proof
  simp[]
QED
val scalar_convert_decimal_pre_pair = optionSyntax.dest_some
  (rhs (concl scalar_convert_decimal_pre_walk_eval))
val scalar_convert_decimal_pre_unit =
  #1 (pairSyntax.dest_pair scalar_convert_decimal_pre_pair)
val scalar_convert_decimal_pre_supply =
  #2 (pairSyntax.dest_pair scalar_convert_decimal_pre_pair)
val scalar_convert_decimal_fcg_eval = EVAL
  ``fcg_analyze (^scalar_convert_decimal_pre_unit).cu_context``
val scalar_convert_decimal_walk_unit_eval = EVAL
  ``prune_unit_fcg_unreachable ^scalar_convert_decimal_pre_unit
      ^(rhs (concl scalar_convert_decimal_fcg_eval))``
val scalar_convert_decimal_walk_unit =
  rhs (concl scalar_convert_decimal_walk_unit_eval)
val scalar_convert_decimal_entry_eval = EVAL
  ``(^scalar_convert_decimal_pre_unit).cu_context.ctx_entry``
val scalar_convert_decimal_entry = optionSyntax.dest_some
  (rhs (concl scalar_convert_decimal_entry_eval))
val scalar_convert_decimal_order_eval = EVAL
  ``fcg_postorder ^(rhs (concl scalar_convert_decimal_fcg_eval))
      ^scalar_convert_decimal_entry``
val scalar_convert_decimal_walk_eval = save_thm
  ("scalar_convert_decimal_walk_eval",
   EVAL ``run_callee_first ^scalar_convert_decimal_resolved_policy
      o1_fn_passes ^(rhs (concl scalar_convert_decimal_order_eval))
      ^scalar_convert_decimal_walk_unit ^scalar_convert_decimal_pre_supply``)
Theorem scalar_convert_decimal_walk_computed: T
Proof
  simp[]
QED
val scalar_convert_decimal_walk_pair = optionSyntax.dest_some
  (rhs (concl scalar_convert_decimal_walk_eval))
val scalar_convert_decimal_walked_unit =
  #1 (pairSyntax.dest_pair scalar_convert_decimal_walk_pair)
val scalar_convert_decimal_walked_supply =
  #2 (pairSyntax.dest_pair scalar_convert_decimal_walk_pair)
val scalar_convert_decimal_post_walk_eval = save_thm
  ("scalar_convert_decimal_post_walk_eval",
   EVAL ``run_pipeline_stages ^scalar_convert_decimal_resolved_policy
      o1_pipeline_spec.ps_post_walk_stages
      ^scalar_convert_decimal_walked_unit
      ^scalar_convert_decimal_walked_supply``)
Theorem scalar_convert_decimal_post_walk_computed: T
Proof
  simp[]
QED
val scalar_convert_decimal_post_pair = optionSyntax.dest_some
  (rhs (concl scalar_convert_decimal_post_walk_eval))
val scalar_convert_decimal_final_checked_unit =
  #1 (pairSyntax.dest_pair scalar_convert_decimal_post_pair)
val scalar_convert_decimal_initial_checks_eval = EVAL
  ``pipeline_spec_wf ^scalar_convert_decimal_resolved_policy o1_pipeline_spec /\
    unit_wf ^scalar_convert_decimal_runtime_unit /\
    raw_static_inputs_wf (^scalar_convert_decimal_runtime_unit).cu_context``
val scalar_convert_decimal_pre_acyclic_eval = EVAL
  ``reachable_fcg_acyclic
      (^scalar_convert_decimal_pre_unit).cu_context
      ^(rhs (concl scalar_convert_decimal_fcg_eval))``
val scalar_convert_decimal_final_unit_wf = EQT_ELIM
  (EVAL ``unit_wf ^scalar_convert_decimal_final_checked_unit``)
val scalar_convert_decimal_final_labels_wf = EQT_ELIM
  (EVAL ``unit_labels_wf ^scalar_convert_decimal_final_checked_unit``)
val scalar_convert_decimal_final_target_safe = EQT_ELIM
  (EVAL ``context_target_safe
      (^scalar_convert_decimal_resolved_policy).rpol_target
      (^scalar_convert_decimal_final_checked_unit).cu_context``)
val scalar_convert_decimal_final_layout_wf = EQT_ELIM
  (EVAL ``concretized_static_layouts_wf
      (^scalar_convert_decimal_final_checked_unit).cu_context``)
val scalar_convert_decimal_final_fmp_wf = EQT_ELIM
  (EVAL ``fmp_lowered_context_wf
      (^scalar_convert_decimal_final_checked_unit).cu_context``)
val scalar_convert_decimal_final_acyclic = EQT_ELIM
  (EVAL ``reachable_fcg_acyclic
      (^scalar_convert_decimal_final_checked_unit).cu_context
      (fcg_analyze
        (^scalar_convert_decimal_final_checked_unit).cu_context)``)
val scalar_convert_decimal_final_codegen_ready = EQT_ELIM
  (EVAL ``codegen_ready
      (^scalar_convert_decimal_final_checked_unit).cu_context``)
val scalar_convert_decimal_final_checks_eval = EQT_INTRO (LIST_CONJ
  [scalar_convert_decimal_final_unit_wf,
   scalar_convert_decimal_final_labels_wf,
   scalar_convert_decimal_final_target_safe,
   scalar_convert_decimal_final_layout_wf,
   scalar_convert_decimal_final_fmp_wf,
   scalar_convert_decimal_final_acyclic,
   scalar_convert_decimal_final_codegen_ready])
Theorem scalar_convert_decimal_final_checks_computed: T
Proof
  simp[]
QED
val scalar_convert_decimal_spec_pre_eval = EVAL
  ``o1_pipeline_spec.ps_pre_walk_stages``
val scalar_convert_decimal_spec_prune_eval = EVAL
  ``o1_pipeline_spec.ps_prune_unreachable``
val scalar_convert_decimal_spec_acyclic_eval = EVAL
  ``o1_pipeline_spec.ps_require_acyclic_calls``
val scalar_convert_decimal_spec_passes_eval = SIMP_CONV (srw_ss())
  [venomPassScheduleTheory.o1_pipeline_spec_def]
  ``o1_pipeline_spec.ps_fn_passes``
val scalar_convert_decimal_spec_post_eval = EVAL
  ``o1_pipeline_spec.ps_post_walk_stages``
val scalar_convert_decimal_spec_final_asm_eval = EVAL
  ``o1_pipeline_spec.ps_final_assembly``
val scalar_convert_decimal_initial_check_rules = map EQT_INTRO
  (CONJUNCTS (EQT_ELIM scalar_convert_decimal_initial_checks_eval))
val scalar_convert_decimal_final_check_rules = map EQT_INTRO
  (CONJUNCTS (EQT_ELIM scalar_convert_decimal_final_checks_eval))
val scalar_convert_decimal_pipeline_rules =
  scalar_convert_decimal_initial_check_rules @
  [scalar_convert_decimal_pre_walk_eval,
   scalar_convert_decimal_spec_pre_eval,
   scalar_convert_decimal_fcg_eval,
   scalar_convert_decimal_spec_prune_eval,
   scalar_convert_decimal_walk_unit_eval,
   scalar_convert_decimal_spec_acyclic_eval,
   scalar_convert_decimal_pre_acyclic_eval,
   scalar_convert_decimal_entry_eval,
   scalar_convert_decimal_spec_passes_eval,
   scalar_convert_decimal_order_eval,
   scalar_convert_decimal_walk_eval,
   scalar_convert_decimal_post_walk_eval,
   scalar_convert_decimal_spec_post_eval] @
  scalar_convert_decimal_final_check_rules @
  [scalar_convert_decimal_spec_final_asm_eval]
val scalar_convert_decimal_admin_rules =
  [LET_THM, COND_CLAUSES, NOT_CLAUSES, boolTheory.AND_CLAUSES,
   combinTheory.K_THM, optionTheory.option_case_compute,
   optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
   pairTheory.pair_case_thm]
val scalar_convert_decimal_admin_rewrites = List.concat
  (map (CONJUNCTS o SPEC_ALL) scalar_convert_decimal_admin_rules)
val scalar_convert_decimal_admin_conv = FIRST_CONV
  (BETA_CONV :: map REWR_CONV scalar_convert_decimal_admin_rewrites)
fun scalar_convert_decimal_repeat_admin 0 tm = REFL tm
  | scalar_convert_decimal_repeat_admin n tm =
      (case total (ONCE_DEPTH_CONV scalar_convert_decimal_admin_conv) tm of
         NONE => REFL tm
       | SOME th => TRANS th
           (scalar_convert_decimal_repeat_admin (n - 1) (rhs (concl th))))
fun scalar_convert_decimal_apply_stage stage_th current =
  case total (ONCE_DEPTH_CONV (REWR_CONV stage_th))
         (rhs (concl current)) of
    NONE => current
  | SOME staged => let
      val admin = scalar_convert_decimal_repeat_admin 30
        (rhs (concl staged))
    in TRANS current (TRANS staged admin) end
fun scalar_convert_decimal_apply_stages current [] = current
  | scalar_convert_decimal_apply_stages current (th::ths) =
      scalar_convert_decimal_apply_stages
        (scalar_convert_decimal_apply_stage th current) ths
val scalar_convert_decimal_run_pipeline_initial0 = SIMP_CONV pure_ss
  [venomPipelineDriverTheory.run_venom_pipeline_def]
  ``run_venom_pipeline (K T) (K T) (K T)
      ^scalar_convert_decimal_resolved_policy o1_pipeline_spec
      ^scalar_convert_decimal_runtime_unit``
val scalar_convert_decimal_run_pipeline_initial = TRANS
  scalar_convert_decimal_run_pipeline_initial0
  (scalar_convert_decimal_repeat_admin 30
    (rhs (concl scalar_convert_decimal_run_pipeline_initial0)))
val scalar_convert_decimal_run_pipeline_eval = save_thm
  ("scalar_convert_decimal_run_pipeline_eval",
   scalar_convert_decimal_apply_stages
     scalar_convert_decimal_run_pipeline_initial
     scalar_convert_decimal_pipeline_rules)
fun scalar_convert_decimal_try_conv conv tm =
  case total conv tm of NONE => REFL tm | SOME th => th
val scalar_convert_decimal_runtime_pipeline_step0 = REWR_CONV
  scalar_convert_decimal_runtime_pipeline_def
  ``scalar_convert_decimal_runtime_pipeline
      scalar_convert_decimal_program``
val scalar_convert_decimal_runtime_pipeline_step1 =
  scalar_convert_decimal_try_conv
    (PURE_REWRITE_CONV [scalar_convert_decimal_policy_eval])
  (rhs (concl scalar_convert_decimal_runtime_pipeline_step0))
val scalar_convert_decimal_runtime_pipeline_step2 =
  scalar_convert_decimal_try_conv (SIMP_CONV pure_ss
    [optionTheory.option_case_def, LET_THM,
     pairTheory.FST, pairTheory.SND,
     pairTheory.UNCURRY_DEF, pairTheory.pair_case_def])
  (rhs (concl scalar_convert_decimal_runtime_pipeline_step1))
val scalar_convert_decimal_runtime_pipeline_step3 =
  scalar_convert_decimal_try_conv
    (PURE_REWRITE_CONV [scalar_convert_decimal_runtime_unit_eval])
  (rhs (concl scalar_convert_decimal_runtime_pipeline_step2))
val scalar_convert_decimal_runtime_pipeline_step4 =
  scalar_convert_decimal_try_conv (SIMP_CONV pure_ss
    [optionTheory.option_case_def, LET_THM,
     pairTheory.FST, pairTheory.SND,
     pairTheory.UNCURRY_DEF, pairTheory.pair_case_def])
  (rhs (concl scalar_convert_decimal_runtime_pipeline_step3))
val scalar_convert_decimal_runtime_pipeline_step5 =
  scalar_convert_decimal_try_conv
    (PURE_REWRITE_CONV [scalar_convert_decimal_run_pipeline_eval])
  (rhs (concl scalar_convert_decimal_runtime_pipeline_step4))
val scalar_convert_decimal_runtime_pipeline_step6 =
  scalar_convert_decimal_try_conv (SIMP_CONV pure_ss
    [optionTheory.OPTION_MAP_DEF, optionTheory.option_case_def, LET_THM,
     pairTheory.FST, pairTheory.SND,
     pairTheory.UNCURRY_DEF, pairTheory.pair_case_def])
  (rhs (concl scalar_convert_decimal_runtime_pipeline_step5))
val scalar_convert_decimal_runtime_pipeline_eval = save_thm
  ("scalar_convert_decimal_runtime_pipeline_eval",
   TRANS scalar_convert_decimal_runtime_pipeline_step0
    (TRANS scalar_convert_decimal_runtime_pipeline_step1
     (TRANS scalar_convert_decimal_runtime_pipeline_step2
      (TRANS scalar_convert_decimal_runtime_pipeline_step3
       (TRANS scalar_convert_decimal_runtime_pipeline_step4
        (TRANS scalar_convert_decimal_runtime_pipeline_step5
          scalar_convert_decimal_runtime_pipeline_step6))))))

Definition scalar_convert_decimal_runtime_compile_def:
  scalar_convert_decimal_runtime_compile tops =
    case scalar_convert_decimal_runtime_pipeline tops of
      NONE => NONE
    | SOME (rpolicy,out) =>
        if out.po_final_assembly <> rpolicy.rpol_final_assembly then NONE
        else finalize_codegen (K SOME) rpolicy out.po_unit
End

(* Cache the concrete analyses and stack plan before asking the evaluator to
   finish code generation.  This keeps the decimal type bounds opaque through
   the branch-heavy generic planner. *)
val scalar_convert_decimal_pipeline_value =
  rhs (concl scalar_convert_decimal_runtime_pipeline_eval)
val scalar_convert_decimal_rp_out =
  optionSyntax.dest_some scalar_convert_decimal_pipeline_value
val scalar_convert_decimal_rpolicy = #1 (pairSyntax.dest_pair scalar_convert_decimal_rp_out)
val scalar_convert_decimal_out = #2 (pairSyntax.dest_pair scalar_convert_decimal_rp_out)
val scalar_convert_decimal_unit_eval = EVAL ``(^scalar_convert_decimal_out).po_unit``
val scalar_convert_decimal_unit = rhs (concl scalar_convert_decimal_unit_eval)
val scalar_convert_decimal_fn = rhs (concl (EVAL
  ``HD (^scalar_convert_decimal_unit).cu_context.ctx_functions``))
val scalar_convert_decimal_liveness_eval = save_thm
  ("scalar_convert_decimal_liveness_eval",
   EVAL ``liveness_analyze ^scalar_convert_decimal_fn``)
val scalar_convert_decimal_dfg_eval = save_thm
  ("scalar_convert_decimal_dfg_eval",
   EVAL ``dfg_build_function ^scalar_convert_decimal_fn``)
val scalar_convert_decimal_cfg_eval = save_thm
  ("scalar_convert_decimal_cfg_eval", EVAL ``cfg_analyze ^scalar_convert_decimal_fn``)
val scalar_convert_decimal_liveness = rhs (concl scalar_convert_decimal_liveness_eval)
val scalar_convert_decimal_dfg = rhs (concl scalar_convert_decimal_dfg_eval)
val scalar_convert_decimal_cfg = rhs (concl scalar_convert_decimal_cfg_eval)
val scalar_convert_decimal_max_eom_eval = EVAL
  ``max_live_eom (^scalar_convert_decimal_unit).cu_context``
val scalar_convert_decimal_max_eom = optionSyntax.dest_some
  (rhs (concl scalar_convert_decimal_max_eom_eval))
val scalar_convert_decimal_generate_fn_plan = save_thm
  ("scalar_convert_decimal_generate_fn_plan", prove
    (``∀spill labels.
        generate_fn_plan ^scalar_convert_decimal_fn spill labels =
        generate_fn_plan_analyzed ^scalar_convert_decimal_liveness
          ^scalar_convert_decimal_dfg ^scalar_convert_decimal_cfg
          ^scalar_convert_decimal_fn spill labels``,
     simp[stackPlanGenTheory.generate_fn_plan_def,
          scalar_convert_decimal_liveness_eval,
          scalar_convert_decimal_dfg_eval, scalar_convert_decimal_cfg_eval]))
val () = computeLib.upd_compset (computeLib.add_thms
  [scalar_convert_decimal_liveness_eval, scalar_convert_decimal_dfg_eval,
   scalar_convert_decimal_cfg_eval, scalar_convert_decimal_generate_fn_plan])
val scalar_convert_decimal_plan_eval = save_thm
  ("scalar_convert_decimal_plan_eval", EVAL
    ``generate_fn_plan_analyzed ^scalar_convert_decimal_liveness
       ^scalar_convert_decimal_dfg ^scalar_convert_decimal_cfg ^scalar_convert_decimal_fn
       ^scalar_convert_decimal_max_eom 0``)
val scalar_convert_decimal_plan = rhs (concl scalar_convert_decimal_plan_eval)
val scalar_convert_decimal_concrete_fn_plan = save_thm
  ("scalar_convert_decimal_concrete_fn_plan", prove
    (``generate_fn_plan ^scalar_convert_decimal_fn ^scalar_convert_decimal_max_eom 0 =
        ^scalar_convert_decimal_plan``,
     simp[scalar_convert_decimal_generate_fn_plan,
          scalar_convert_decimal_plan_eval]))
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``generate_fn_plan``)
    |> computeLib.add_thms [scalar_convert_decimal_concrete_fn_plan])
val scalar_convert_decimal_context_plan_step1 = SIMP_CONV (srw_ss())
  [stackPlanGenTheory.generate_context_plan_def,
   stackPlanGenTheory.generate_context_plan_with_def,
   scalar_convert_decimal_max_eom_eval,
   stackPlanGenTheory.generate_context_regions_def,
   stackPlanGenTheory.finish_context_plan_def]
  ``generate_context_plan (^scalar_convert_decimal_unit).cu_context``
val scalar_convert_decimal_context_plan_step2 =
  EVAL (rhs (concl scalar_convert_decimal_context_plan_step1))
val scalar_convert_decimal_actual_plan_call = find_term
  (can (match_term ``generate_fn_plan f spill labels``))
  (rhs (concl scalar_convert_decimal_context_plan_step2))
val scalar_convert_decimal_actual_plan_args =
  #2 (strip_comb scalar_convert_decimal_actual_plan_call)
val scalar_convert_decimal_actual_fn = hd scalar_convert_decimal_actual_plan_args
val scalar_convert_decimal_actual_liveness_eval =
  EVAL ``liveness_analyze ^scalar_convert_decimal_actual_fn``
val scalar_convert_decimal_actual_dfg_eval =
  EVAL ``dfg_build_function ^scalar_convert_decimal_actual_fn``
val scalar_convert_decimal_actual_cfg_eval =
  EVAL ``cfg_analyze ^scalar_convert_decimal_actual_fn``
val scalar_convert_decimal_actual_liveness =
  rhs (concl scalar_convert_decimal_actual_liveness_eval)
val scalar_convert_decimal_actual_dfg = rhs (concl scalar_convert_decimal_actual_dfg_eval)
val scalar_convert_decimal_actual_cfg = rhs (concl scalar_convert_decimal_actual_cfg_eval)
val scalar_convert_decimal_actual_plan_eval = EVAL
  ``generate_fn_plan_analyzed ^scalar_convert_decimal_actual_liveness
      ^scalar_convert_decimal_actual_dfg ^scalar_convert_decimal_actual_cfg
      ^scalar_convert_decimal_actual_fn ^scalar_convert_decimal_max_eom 0``
val scalar_convert_decimal_actual_generate_step1 =
  REWR_CONV stackPlanGenTheory.generate_fn_plan_def
    ``generate_fn_plan ^scalar_convert_decimal_actual_fn
        ^scalar_convert_decimal_max_eom 0``
val scalar_convert_decimal_actual_generate_step2 = PURE_REWRITE_CONV
  [scalar_convert_decimal_actual_liveness_eval,
   scalar_convert_decimal_actual_dfg_eval,
   scalar_convert_decimal_actual_cfg_eval]
  (rhs (concl scalar_convert_decimal_actual_generate_step1))
val scalar_convert_decimal_actual_generate_step3 =
  REWR_CONV scalar_convert_decimal_actual_plan_eval
    (rhs (concl scalar_convert_decimal_actual_generate_step2))
val scalar_convert_decimal_actual_generate_fn_plan =
  TRANS scalar_convert_decimal_actual_generate_step1
    (TRANS scalar_convert_decimal_actual_generate_step2
      scalar_convert_decimal_actual_generate_step3)
val scalar_convert_decimal_context_plan_step3 = PURE_REWRITE_CONV
  [scalar_convert_decimal_actual_generate_fn_plan]
  (rhs (concl scalar_convert_decimal_context_plan_step2))
val scalar_convert_decimal_context_plan_eval = save_thm
  ("scalar_convert_decimal_context_plan_eval",
   TRANS scalar_convert_decimal_context_plan_step1
    (TRANS scalar_convert_decimal_context_plan_step2
      (TRANS scalar_convert_decimal_context_plan_step3
        (EVAL (rhs (concl scalar_convert_decimal_context_plan_step3))))))
val scalar_convert_decimal_context_plan = optionSyntax.dest_some
  (rhs (concl scalar_convert_decimal_context_plan_eval))
val scalar_convert_decimal_target_wf_eval = EVAL
  ``target_capabilities_wf (^scalar_convert_decimal_rpolicy).rpol_target``
val scalar_convert_decimal_context_safe_eval = EVAL
  ``context_target_safe (^scalar_convert_decimal_rpolicy).rpol_target
      (^scalar_convert_decimal_unit).cu_context``
val scalar_convert_decimal_codegen_step1 = SIMP_CONV (srw_ss())
  [codegenTheory.codegen_assembly_def,
   scalar_convert_decimal_target_wf_eval,
   scalar_convert_decimal_context_safe_eval,
   scalar_convert_decimal_context_plan_eval,
   optionTheory.option_case_compute,
   optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
   LET_THM, NOT_CLAUSES, COND_CLAUSES]
  ``codegen_assembly ^scalar_convert_decimal_rpolicy ^scalar_convert_decimal_unit``
val scalar_convert_decimal_codegen_step2 =
  EVAL (rhs (concl scalar_convert_decimal_codegen_step1))
val scalar_convert_decimal_codegen_assembly_eval = save_thm
  ("scalar_convert_decimal_codegen_assembly_eval",
   TRANS scalar_convert_decimal_codegen_step1 scalar_convert_decimal_codegen_step2)
val scalar_convert_decimal_out_final_assembly_eval =
  EVAL ``(^scalar_convert_decimal_out).po_final_assembly``
val scalar_convert_decimal_rpolicy_final_assembly_eval =
  EVAL ``(^scalar_convert_decimal_rpolicy).rpol_final_assembly``
val scalar_convert_decimal_runtime_accessors =
  CONJUNCTS venomCompilerTypesTheory.pipeline_output_accessors @
  CONJUNCTS venomCompilerTypesTheory.resolved_compiler_policy_accessors

Theorem scalar_convert_decimal_runtime_matches_python_oracle:
  scalar_convert_decimal_runtime_compile scalar_convert_decimal_program =
    SOME (SND ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_decimal.hex"))
Proof
  simp_tac pure_ss
    ([scalar_convert_decimal_runtime_compile_def,
      scalar_convert_decimal_runtime_pipeline_eval,
      optionTheory.option_case_compute,
      optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
      pairTheory.pair_case_thm, LET_THM, COND_CLAUSES,
      REFL_CLAUSE, NOT_CLAUSES,
      scalar_convert_decimal_unit_eval,
      scalar_convert_decimal_out_final_assembly_eval,
      scalar_convert_decimal_rpolicy_final_assembly_eval] @
     scalar_convert_decimal_runtime_accessors) >>
  PURE_REWRITE_TAC [codegenTheory.finalize_codegen_identity] >>
  PURE_REWRITE_TAC [scalar_convert_decimal_codegen_assembly_eval] >>
  EVAL_TAC
QED

Definition scalar_convert_decimal_deploy_compile_def:
  scalar_convert_decimal_deploy_compile tops runtime =
    case resolve_o1_policy (o1_policy all_capabilities) of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_deploy_unit tops rpolicy runtime of
          NONE => NONE
        | SOME unit =>
            checked_unit_pipeline
              (λrp u. run_venom_pipeline (K T) (K T) (K T)
                 rp o1_pipeline_spec u)
              (K SOME) rpolicy unit
End

Theorem scalar_convert_decimal_deploy_matches_python_oracle:
  scalar_convert_decimal_deploy_compile scalar_convert_decimal_program
    (SND ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_decimal.hex")) =
    SOME (FST ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_decimal.hex"))
Proof
  EVAL_TAC
QED

Theorem scalar_convert_decimal_compile_staged:
  compile_vyper (K SOME) (o1_policy all_capabilities) tops =
    case scalar_convert_decimal_runtime_compile tops of
      NONE => NONE
    | SOME runtime =>
        OPTION_MAP (λdeploy. (deploy,runtime))
          (scalar_convert_decimal_deploy_compile tops runtime)
Proof
  simp[compile_vyper_def, compile_vyper_with_def,
       scalar_convert_decimal_runtime_compile_def,
       scalar_convert_decimal_runtime_pipeline_def,
       scalar_convert_decimal_deploy_compile_def,
       checked_unit_pipeline_def] >>
  rpt CASE_TAC >> gvs[]
QED

Theorem scalar_convert_decimal_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_convert_decimal_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_convert_decimal.hex")
Proof
  PURE_REWRITE_TAC [scalar_convert_decimal_compile_staged] >>
  PURE_REWRITE_TAC [scalar_convert_decimal_runtime_matches_python_oracle] >>
  simp_tac pure_ss
    [optionTheory.option_case_compute,
     optionTheory.IS_SOME_DEF, optionTheory.THE_DEF,
     optionTheory.OPTION_MAP_DEF, LET_THM, COND_CLAUSES,
     scalar_convert_decimal_deploy_matches_python_oracle] >>
  EVAL_TAC
QED
