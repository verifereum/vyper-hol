(* Exact Python-oracle bytecode checks for evaluator-small wei/modular fixtures. *)

Theory evalCompilerBytecodeScalarWeiModular
Ancestors evalCompilerSubsetScalars compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = Globals.max_print_depth := 20

Theorem scalar_wei_small_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_wei_small_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_wei_small.hex")
Proof
  EVAL_TAC
QED

Theorem scalar_wei_large_matches_python_oracle:
  compile_vyper (K SOME) (o1_policy all_capabilities)
    scalar_wei_large_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_wei_large.hex")
Proof
  EVAL_TAC
QED

val scalar_modular_policy_eval = save_thm
  ("scalar_modular_policy_eval",
   EVAL ``resolve_o1_policy (o1_policy all_capabilities)``)
val scalar_modular_rpolicy = optionSyntax.dest_some
  (rhs (concl scalar_modular_policy_eval))

(* Keep the mutual-recursion implementation relation out of concrete
   evaluation by exposing only the selected public equations. *)
val scalar_modular_compile_expr_eq =
  exprLoweringTheory.compile_expr_component_eq
Theorem scalar_modular_compile_expr_name:
  compile_expr cenv ty (Name nty n) st =
  compile_name_vv cenv nty n st
Proof
  simp[scalar_modular_compile_expr_eq,
       vyperASTTheory.expr_type_def]
QED

Theorem scalar_modular_compile_expr_addmod:
  compile_expr cenv ty
    (Builtin bty AddMod [Name aty a; Name cty b; Name mty m]) st =
  compile_addmod_names cenv
    (expr_type (Builtin bty AddMod
      [Name aty a; Name cty b; Name mty m]))
    aty a cty b mty m st
Proof
  simp[scalar_modular_compile_expr_eq]
QED

Theorem scalar_modular_compile_expr_mulmod:
  compile_expr cenv ty
    (Builtin bty MulMod [Name aty a; Name cty b; Name mty m]) st =
  compile_mulmod_names cenv
    (expr_type (Builtin bty MulMod
      [Name aty a; Name cty b; Name mty m]))
    aty a cty b mty m st
Proof
  simp[scalar_modular_compile_expr_eq]
QED

Theorem scalar_modular_compile_expr_powmod256:
  compile_expr cenv ty
    (Builtin bty PowMod256 [Name aty a; Name cty b]) st =
  compile_powmod256_names cenv
    (expr_type (Builtin bty PowMod256 [Name aty a; Name cty b]))
    aty a cty b st
Proof
  simp[scalar_modular_compile_expr_eq]
QED

val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``compile_expr``)
    |> computeLib.add_thms
         [scalar_modular_compile_expr_name,
          scalar_modular_compile_expr_addmod,
          scalar_modular_compile_expr_mulmod,
          scalar_modular_compile_expr_powmod256])

(* Stage source lowering so the three external bodies are evaluated and
   checkpointed independently. *)
val scalar_modular_tops = ``scalar_modular_program``
val scalar_modular_type_env_eval = save_thm
  ("scalar_modular_type_env_eval",
   EVAL ``type_env ^scalar_modular_tops``)
val scalar_modular_type_env = rhs (concl scalar_modular_type_env_eval)
val scalar_modular_nkeys_eval = save_thm
  ("scalar_modular_nkeys_eval",
   EVAL ``assign_nkeys ^scalar_modular_tops 0``)
val scalar_modular_nkeys = rhs (concl scalar_modular_nkeys_eval)
val scalar_modular_classify_eval = save_thm
  ("scalar_modular_classify_eval",
   EVAL ``classify_functions ^scalar_modular_tops``)
val scalar_modular_classified = rhs (concl scalar_modular_classify_eval)
val scalar_modular_external_sources =
  #1 (pairSyntax.dest_pair scalar_modular_classified)
val scalar_modular_classified_tail1 =
  #2 (pairSyntax.dest_pair scalar_modular_classified)
val scalar_modular_internal_sources =
  #1 (pairSyntax.dest_pair scalar_modular_classified_tail1)
val scalar_modular_classified_tail2 =
  #2 (pairSyntax.dest_pair scalar_modular_classified_tail1)
val scalar_modular_fallback_source =
  #1 (pairSyntax.dest_pair scalar_modular_classified_tail2)
val scalar_modular_selectors_eval = save_thm
  ("scalar_modular_selectors_eval",
   EVAL ``build_selectors ^scalar_modular_type_env
      ^scalar_modular_external_sources``)
val scalar_modular_selectors = rhs (concl scalar_modular_selectors_eval)
val scalar_modular_external_fns_eval = save_thm
  ("scalar_modular_external_fns_eval",
   EVAL ``MAP (set_external_package_target
                 (^scalar_modular_rpolicy).rpol_target o
               package_external_fn ^scalar_modular_tops F
                 ^scalar_modular_nkeys)
      ^scalar_modular_external_sources``)
val scalar_modular_external_fns =
  rhs (concl scalar_modular_external_fns_eval)
val scalar_modular_internal_fns_eval = save_thm
  ("scalar_modular_internal_fns_eval",
   EVAL ``MAP (set_internal_package_target
                 (^scalar_modular_rpolicy).rpol_target o
               package_internal_fn ^scalar_modular_tops F
                 ^scalar_modular_nkeys F 0)
      ^scalar_modular_internal_sources``)
val scalar_modular_internal_fns =
  rhs (concl scalar_modular_internal_fns_eval)
val scalar_modular_fallback_fn_eval = save_thm
  ("scalar_modular_fallback_fn_eval",
   EVAL ``set_fallback_package_target
      (^scalar_modular_rpolicy).rpol_target
      (package_fallback_fn ^scalar_modular_tops F ^scalar_modular_nkeys
        ^scalar_modular_fallback_source)``)
val scalar_modular_fallback_fn =
  rhs (concl scalar_modular_fallback_fn_eval)
val scalar_modular_state0_eval = save_thm
  ("scalar_modular_state0_eval",
   EVAL ``initial_compile_state "__entry"``)
val scalar_modular_state0 = rhs (concl scalar_modular_state0_eval)
val scalar_modular_fallback_label_eval = save_thm
  ("scalar_modular_fallback_label_eval",
   EVAL ``fresh_label "fallback" ^scalar_modular_state0``)
val scalar_modular_fallback_label_pair =
  rhs (concl scalar_modular_fallback_label_eval)
val scalar_modular_fallback_label =
  #1 (pairSyntax.dest_pair scalar_modular_fallback_label_pair)
val scalar_modular_state1 =
  #2 (pairSyntax.dest_pair scalar_modular_fallback_label_pair)
val scalar_modular_linear_selectors_eval = save_thm
  ("scalar_modular_linear_selectors_eval",
   EVAL ``MAP (λ(sel,lbl,_). (sel,lbl)) ^scalar_modular_selectors``)
val scalar_modular_linear_selectors =
  rhs (concl scalar_modular_linear_selectors_eval)
val scalar_modular_dispatch_eval = save_thm
  ("scalar_modular_dispatch_eval",
   EVAL ``compile_selector_dispatch_linear
      ^scalar_modular_linear_selectors ^scalar_modular_fallback_label
      ^scalar_modular_state1``)
val scalar_modular_dispatch_pair = rhs (concl scalar_modular_dispatch_eval)
val scalar_modular_state2 =
  #2 (pairSyntax.dest_pair scalar_modular_dispatch_pair)

(* Lower each external package one layer at a time.  In particular, keep the
   recursive body/list compilers out of EVAL: only the single Return statement
   for each fixture function is evaluated directly. *)
fun scalar_modular_dest_tuple tm =
  if pairSyntax.is_pair tm then
    let val (x,xs) = pairSyntax.dest_pair tm
    in x :: scalar_modular_dest_tuple xs end
  else [tm]
val (scalar_modular_external_fn_terms,_) =
  listSyntax.dest_list scalar_modular_external_fns
val scalar_modular_add_mod_package =
  List.nth (scalar_modular_external_fn_terms,0)
val scalar_modular_mul_mod_package =
  List.nth (scalar_modular_external_fn_terms,1)
val scalar_modular_pow_mod_package =
  List.nth (scalar_modular_external_fn_terms,2)

val scalar_modular_compile_stmts_defs =
  CONJUNCTS stmtLoweringTheory.compile_stmt_def
val scalar_modular_compile_stmts_cons_def =
  valOf (List.find
    (fn th => can (match_term ``compile_stmts c l t (s::ss)``)
      (lhs (concl (SPEC_ALL th))))
    scalar_modular_compile_stmts_defs)
val scalar_modular_compile_stmts_nil_def =
  valOf (List.find
    (fn th => can (match_term ``compile_stmts c l t []``)
      (lhs (concl (SPEC_ALL th))))
    scalar_modular_compile_stmts_defs)
val scalar_modular_external_body_defs =
  CONJUNCTS moduleLoweringTheory.compile_external_fn_bodies_def
val scalar_modular_external_body_cons_def =
  valOf (List.find
    (fn th => can (match_term ``compile_external_fn_bodies (f::fs)``)
      (lhs (concl (SPEC_ALL th))))
    scalar_modular_external_body_defs)
val scalar_modular_external_body_nil_def =
  valOf (List.find
    (fn th => can (match_term ``compile_external_fn_bodies []``)
      (lhs (concl (SPEC_ALL th))))
    scalar_modular_external_body_defs)
val () = computeLib.upd_compset
  (fn cs => computeLib.scrub_const cs ``compile_external_fn_bodies``)
fun scalar_modular_stage_external_function prefix package current =
  let
    val fields = scalar_modular_dest_tuple package
    val entry = List.nth (fields,0)
    val cenv = List.nth (fields,1)
    val pos_args = List.nth (fields,2)
    val min_cds = List.nth (fields,3)
    val is_payable = List.nth (fields,4)
    val is_nr = List.nth (fields,5)
    val nkey = List.nth (fields,6)
    val use_trans = List.nth (fields,7)
    val is_view = List.nth (fields,8)
    val body = List.nth (fields,9)
    val ret_type = List.nth (fields,10)
    val (_,current_args) = strip_comb (rhs (concl current))
    val state0 = List.nth (current_args,1)
    val new_block_eval = save_thm
      (prefix ^ "_new_block_eval",
       EVAL ``new_block ^entry ^state0``)
    val state1 = #2 (pairSyntax.dest_pair
      (rhs (concl new_block_eval)))
    val entry_checks_eval = save_thm
      (prefix ^ "_external_entry_checks_eval",
       EVAL ``compile_entry_checks ^min_cds ^is_payable ^state1``)
    val state2 = #2 (pairSyntax.dest_pair
      (rhs (concl entry_checks_eval)))
    val register_args_eval = save_thm
      (prefix ^ "_register_args_eval",
       EVAL ``compile_register_positional_args ^cenv ^pos_args 4 ^state2``)
    val register_args_pair = rhs (concl register_args_eval)
    val body_cenv = #1 (pairSyntax.dest_pair register_args_pair)
    val state3 = #2 (pairSyntax.dest_pair register_args_pair)
    val collect_locals_eval = save_thm
      (prefix ^ "_collect_locals_eval",
       EVAL ``collect_locals ^body``)
    val locals = rhs (concl collect_locals_eval)
    val reserve_locals_eval = save_thm
      (prefix ^ "_reserve_locals_eval",
       EVAL ``reserve_local_ptrs ^body_cenv ^locals ^state3``)
    val reserve_pair = rhs (concl reserve_locals_eval)
    val body_cenv2 = #1 (pairSyntax.dest_pair reserve_pair)
    val state4 = #2 (pairSyntax.dest_pair reserve_pair)
    val ret_ty = optionSyntax.dest_some ret_type
    val (stmt_terms,_) = listSyntax.dest_list body
    val stmt = hd stmt_terms
    val stmt_expr = find_term
      (can (match_term ``Builtin ty builtin args``)) stmt
    val stmt_expr_eval = save_thm
      (prefix ^ "_stmt_expr_eval",
       EVAL ``compile_expr ^body_cenv2 ^ret_ty ^stmt_expr ^state4``)
    val () = computeLib.upd_compset
      (computeLib.add_thms [stmt_expr_eval])
    val stmt_lower_value_step = SIMP_CONV (srw_ss())
      [exprLoweringTheory.lower_value_def, stmt_expr_eval,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
       LET_THM, pairTheory.FST, pairTheory.SND,
       pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
      ``lower_value compile_expr ^body_cenv2 ^ret_ty
         ^stmt_expr ^state4``
    val stmt_lower_value_eval = save_thm
      (prefix ^ "_stmt_lower_value_eval",
       TRANS stmt_lower_value_step
         (EVAL (rhs (concl stmt_lower_value_step))))
    val stmt_expr_pair = rhs (concl stmt_expr_eval)
    val stmt_value0 = #1 (pairSyntax.dest_pair stmt_expr_pair)
    val stmt_state0 = #2 (pairSyntax.dest_pair stmt_expr_pair)
    val stmt_unwrap_eval = save_thm
      (prefix ^ "_stmt_unwrap_eval",
       EVAL ``unwrap_value ^body_cenv2 ^stmt_value0 ^stmt_state0``)
    val stmt_unwrap_pair = rhs (concl stmt_unwrap_eval)
    val stmt_operand = #1 (pairSyntax.dest_pair stmt_unwrap_pair)
    val stmt_state = #2 (pairSyntax.dest_pair stmt_unwrap_pair)
    val stmt_external_return_eval = save_thm
      (prefix ^ "_stmt_external_return_eval",
       EVAL ``compile_external_return (SOME ^stmt_operand) T
          (^body_cenv2).ce_raw_return
          (^body_cenv2).ce_ret_enc_info
          (^body_cenv2).ce_max_return_size F 0 F F ^stmt_state``)
    val stmt_step1 = SIMP_CONV (srw_ss())
      [stmtLoweringTheory.compile_stmt_def,
       exprLoweringTheory.lower_value_def, stmt_expr_eval,
       stmt_lower_value_eval, stmt_external_return_eval,
       compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, LET_THM,
       pairTheory.FST, pairTheory.SND,
       pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
      ``compile_stmt ^body_cenv2 NoLoop ^ret_ty ^stmt ^state4``
    val stmt_step1_eval = save_thm
      (prefix ^ "_stmt_step1_eval", stmt_step1)
    val stmt_eval = save_thm
      (prefix ^ "_stmt_eval",
       TRANS stmt_step1_eval (EVAL (rhs (concl stmt_step1_eval))))
    val block_terminated4_eval = EVAL
      ``block_is_terminated ^state4``
    val stmts_step1 = RATOR_CONV
      (REWR_CONV scalar_modular_compile_stmts_cons_def)
      ``compile_stmts ^body_cenv2 NoLoop ^ret_ty ^body ^state4``
    val stmts_step2 = SIMP_CONV pure_ss
      [compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_get_def, compileEnvTheory.comp_return_def,
       block_terminated4_eval, stmt_eval,
       scalar_modular_compile_stmts_nil_def,
       boolTheory.COND_CLAUSES, LET_THM, pairTheory.FST, pairTheory.SND,
       pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
      (rhs (concl stmts_step1))
    val stmts_eval = save_thm
      (prefix ^ "_stmts_eval", TRANS stmts_step1 stmts_step2)
    val state5 = #2 (pairSyntax.dest_pair
      (rhs (concl stmts_eval)))
    val block_terminated5_eval = EVAL
      ``block_is_terminated ^state5``
    val guarded_body_eval = save_thm
      (prefix ^ "_guarded_body_eval",
       SIMP_CONV pure_ss
        [moduleLoweringTheory.compile_guarded_body_def,
         collect_locals_eval, reserve_locals_eval, stmts_eval,
         block_terminated5_eval,
         compileEnvTheory.comp_bind_def,
         compileEnvTheory.comp_ignore_bind_def,
         compileEnvTheory.comp_return_def, compileEnvTheory.comp_get_def,
         boolTheory.COND_CLAUSES, LET_THM, pairTheory.FST, pairTheory.SND,
         pairTheory.UNCURRY_DEF, pairTheory.pair_case_def,
         optionTheory.option_case_def]
        ``compile_guarded_body ^body_cenv ^is_nr ^nkey ^use_trans
            ^is_view ^body ^ret_type ^state3``)
    val external_body_eval = save_thm
      (prefix ^ "_external_body_eval",
       SIMP_CONV pure_ss
        [moduleLoweringTheory.compile_external_function_body_def,
         register_args_eval, guarded_body_eval,
         compileEnvTheory.comp_bind_def,
         compileEnvTheory.comp_ignore_bind_def,
         compileEnvTheory.comp_return_def, LET_THM,
         pairTheory.FST, pairTheory.SND,
         pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
        ``compile_external_function_body ^cenv ^pos_args ^is_nr ^nkey
            ^use_trans ^is_view ^body ^ret_type ^state2``)
    val cons_unfold = RATOR_CONV
      (REWR_CONV scalar_modular_external_body_cons_def)
      (rhs (concl current))
    val cons_assembled = SIMP_CONV pure_ss
      [new_block_eval, entry_checks_eval, external_body_eval,
       compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, LET_THM,
       pairTheory.FST, pairTheory.SND,
       pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
      (rhs (concl cons_unfold))
  in
    save_thm (prefix ^ "_body_eval",
      TRANS current (TRANS cons_unfold cons_assembled))
  end

val scalar_modular_external_bodies_initial = REFL
  ``compile_external_fn_bodies ^scalar_modular_external_fns
      ^scalar_modular_state2``
val scalar_modular_add_mod_body_eval =
  scalar_modular_stage_external_function "scalar_modular_add_mod"
    scalar_modular_add_mod_package scalar_modular_external_bodies_initial
Theorem scalar_modular_add_mod_body_computed: T
Proof
  simp[]
QED
val scalar_modular_mul_mod_body_eval =
  scalar_modular_stage_external_function "scalar_modular_mul_mod"
    scalar_modular_mul_mod_package scalar_modular_add_mod_body_eval
Theorem scalar_modular_mul_mod_body_computed: T
Proof
  simp[]
QED
val scalar_modular_pow_mod_body_eval =
  scalar_modular_stage_external_function "scalar_modular_pow_mod"
    scalar_modular_pow_mod_package scalar_modular_mul_mod_body_eval
Theorem scalar_modular_pow_mod_body_computed: T
Proof
  simp[]
QED
val scalar_modular_external_bodies_nil_step = RATOR_CONV
  (REWR_CONV scalar_modular_external_body_nil_def)
  (rhs (concl scalar_modular_pow_mod_body_eval))
val scalar_modular_external_bodies_eval = save_thm
  ("scalar_modular_external_bodies_eval",
   TRANS scalar_modular_pow_mod_body_eval
     (TRANS scalar_modular_external_bodies_nil_step
       (EVAL (rhs (concl scalar_modular_external_bodies_nil_step)))))
Theorem scalar_modular_external_bodies_computed: T
Proof
  simp[]
QED
val () = computeLib.upd_compset
  (computeLib.add_thms [scalar_modular_external_bodies_eval])
val scalar_modular_external_bodies_pair =
  rhs (concl scalar_modular_external_bodies_eval)
val scalar_modular_state8 =
  #2 (pairSyntax.dest_pair scalar_modular_external_bodies_pair)
val scalar_modular_fallback_block_eval = save_thm
  ("scalar_modular_fallback_block_eval",
   EVAL ``new_block ^scalar_modular_fallback_label
      ^scalar_modular_state8``)
val scalar_modular_state9 = #2 (pairSyntax.dest_pair
  (rhs (concl scalar_modular_fallback_block_eval)))
val scalar_modular_fallback_revert_eval = save_thm
  ("scalar_modular_fallback_revert_eval",
   EVAL ``emit_inst REVERT [Lit 0w; Lit 0w] []
      ^scalar_modular_state9``)
val scalar_modular_state10 = #2 (pairSyntax.dest_pair
  (rhs (concl scalar_modular_fallback_revert_eval)))
val scalar_modular_internal_bodies_eval = save_thm
  ("scalar_modular_internal_bodies_eval",
   EVAL ``compile_internal_fn_bodies ^scalar_modular_internal_fns
      ^scalar_modular_state10``)
val scalar_modular_state11 = #2 (pairSyntax.dest_pair
  (rhs (concl scalar_modular_internal_bodies_eval)))
val scalar_modular_entry_info_eval = save_thm
  ("scalar_modular_entry_info_eval",
   EVAL ``build_dense_entry_info ^scalar_modular_selectors
      ^scalar_modular_external_fns``)
val scalar_modular_entry_info = rhs (concl scalar_modular_entry_info_eval)
val scalar_modular_generate_runtime_step0 =
  RATOR_CONV (REWR_CONV moduleLoweringTheory.compile_generate_runtime_def)
    ``compile_generate_runtime ^scalar_modular_selectors
       ^scalar_modular_external_fns ^scalar_modular_internal_fns
       ^scalar_modular_fallback_fn Linear 0 0 []
       ^scalar_modular_entry_info ^scalar_modular_state0``
val scalar_modular_generate_runtime_step1 = SIMP_CONV pure_ss
  [venomPolicyTypesTheory.dispatch_strategy_case_def,
   optionTheory.option_case_def,
   compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
   compileEnvTheory.comp_return_def,
   scalar_modular_fallback_label_eval,
   scalar_modular_linear_selectors_eval,
   scalar_modular_dispatch_eval,
   scalar_modular_external_bodies_eval,
   scalar_modular_fallback_block_eval,
   scalar_modular_fallback_revert_eval,
   scalar_modular_internal_bodies_eval,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl scalar_modular_generate_runtime_step0))
val scalar_modular_generate_runtime_eval = save_thm
  ("scalar_modular_generate_runtime_eval",
   TRANS scalar_modular_generate_runtime_step0
     scalar_modular_generate_runtime_step1)
val scalar_modular_extract_context_eval = save_thm
  ("scalar_modular_extract_context_eval",
   EVAL ``extract_context_with_internals "__entry"
      ^scalar_modular_internal_fns ^scalar_modular_state11``)
val scalar_modular_context_data = optionSyntax.dest_some
  (rhs (concl scalar_modular_extract_context_eval))
val scalar_modular_context =
  #1 (pairSyntax.dest_pair scalar_modular_context_data)
val scalar_modular_policy_ok_eval = EVAL
  ``lowering_policy_ok ^scalar_modular_rpolicy``
val scalar_modular_context_ok_eval = EVAL
  ``lowering_context_ok ^scalar_modular_context``
val scalar_modular_dispatch_policy_eval = EVAL
  ``(^scalar_modular_rpolicy).rpol_frontend_dispatch``
val scalar_modular_run_lowering_term =
  ``run_lowering ^scalar_modular_selectors ^scalar_modular_external_fns
      ^scalar_modular_internal_fns ^scalar_modular_fallback_fn
      ^scalar_modular_rpolicy 0 0 [] ^scalar_modular_entry_info "__entry"``
val scalar_modular_run_lowering_step0 = REWR_CONV
  vyperCompilerTheory.run_lowering_def scalar_modular_run_lowering_term
val scalar_modular_run_lowering_step1 = PURE_REWRITE_CONV
  [scalar_modular_policy_ok_eval, scalar_modular_state0_eval,
   scalar_modular_dispatch_policy_eval]
  (rhs (concl scalar_modular_run_lowering_step0))
val scalar_modular_run_lowering_step2 = SIMP_CONV pure_ss
  [boolTheory.COND_CLAUSES, optionTheory.option_case_def,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl scalar_modular_run_lowering_step1))
val scalar_modular_run_lowering_step3 = PURE_REWRITE_CONV
  [scalar_modular_generate_runtime_eval]
  (rhs (concl scalar_modular_run_lowering_step2))
val scalar_modular_run_lowering_step4 = SIMP_CONV pure_ss
  [scalar_modular_extract_context_eval, scalar_modular_context_ok_eval,
   boolTheory.COND_CLAUSES, optionTheory.option_case_def,
   LET_THM, pairTheory.FST, pairTheory.SND,
   pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  (rhs (concl scalar_modular_run_lowering_step3))
val scalar_modular_run_lowering_eval = save_thm
  ("scalar_modular_run_lowering_eval",
   TRANS scalar_modular_run_lowering_step0
    (TRANS scalar_modular_run_lowering_step1
     (TRANS scalar_modular_run_lowering_step2
      (TRANS scalar_modular_run_lowering_step3
        scalar_modular_run_lowering_step4))))
val scalar_modular_lower_runtime_eval = save_thm
  ("scalar_modular_lower_runtime_eval",
   SIMP_CONV pure_ss
    ([compileVyperTheory.lower_vyper_runtime_unit_def,
      scalar_modular_type_env_eval, scalar_modular_nkeys_eval,
      scalar_modular_classify_eval, scalar_modular_selectors_eval,
      scalar_modular_external_fns_eval, scalar_modular_internal_fns_eval,
      scalar_modular_fallback_fn_eval, scalar_modular_entry_info_eval,
      scalar_modular_run_lowering_eval,
      LET_THM, pairTheory.FST, pairTheory.SND,
      pairTheory.UNCURRY_DEF, pairTheory.pair_case_def] @
     CONJUNCTS
       venomCompilerTypesTheory.resolved_compiler_policy_accessors)
    ``lower_vyper_runtime_unit scalar_modular_program
       ^scalar_modular_rpolicy``)
val scalar_modular_runtime_unit = optionSyntax.dest_some
  (rhs (concl scalar_modular_lower_runtime_eval))
Theorem scalar_modular_lower_runtime_computed: T
Proof
  simp[]
QED
val scalar_modular_pipeline_eval = save_thm
  ("scalar_modular_pipeline_eval",
   EVAL ``run_venom_pipeline (K T) (K T) (K T)
      ^scalar_modular_rpolicy o1_pipeline_spec ^scalar_modular_runtime_unit``)
val scalar_modular_out = optionSyntax.dest_some
  (rhs (concl scalar_modular_pipeline_eval))
val scalar_modular_final_unit = rhs (concl (EVAL
  ``(^scalar_modular_out).po_unit``))
Theorem scalar_modular_pipeline_computed: T
Proof
  simp[]
QED
val scalar_modular_finalize_eval = save_thm
  ("scalar_modular_finalize_eval",
   EVAL ``finalize_codegen (K SOME) ^scalar_modular_rpolicy
      ^scalar_modular_final_unit``)
val scalar_modular_runtime_bytes = optionSyntax.dest_some
  (rhs (concl scalar_modular_finalize_eval))
val scalar_modular_lower_deploy_eval = save_thm
  ("scalar_modular_lower_deploy_eval",
   EVAL ``lower_vyper_deploy_unit scalar_modular_program
      ^scalar_modular_rpolicy ^scalar_modular_runtime_bytes``)
val scalar_modular_deploy_unit = optionSyntax.dest_some
  (rhs (concl scalar_modular_lower_deploy_eval))
val scalar_modular_deploy_pipeline_eval = save_thm
  ("scalar_modular_deploy_pipeline_eval",
   EVAL ``run_venom_pipeline (K T) (K T) (K T)
      ^scalar_modular_rpolicy o1_pipeline_spec ^scalar_modular_deploy_unit``)
val scalar_modular_deploy_out = optionSyntax.dest_some
  (rhs (concl scalar_modular_deploy_pipeline_eval))
val scalar_modular_final_deploy_unit = rhs (concl (EVAL
  ``(^scalar_modular_deploy_out).po_unit``))
val scalar_modular_finalize_deploy_eval = save_thm
  ("scalar_modular_finalize_deploy_eval",
   EVAL ``finalize_codegen (K SOME) ^scalar_modular_rpolicy
      ^scalar_modular_final_deploy_unit``)
val scalar_modular_compile_step0 = SIMP_CONV pure_ss
  [compileVyperTheory.compile_vyper_def,
   compileVyperTheory.compile_vyper_with_def,
   compileVyperTheory.checked_unit_pipeline_def,
   optionTheory.option_case_def, boolTheory.COND_CLAUSES,
   scalar_modular_policy_eval, scalar_modular_lower_runtime_eval,
   scalar_modular_pipeline_eval, scalar_modular_finalize_eval,
   scalar_modular_lower_deploy_eval, scalar_modular_deploy_pipeline_eval,
   scalar_modular_finalize_deploy_eval, LET_THM, pairTheory.FST,
   pairTheory.SND, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  ``compile_vyper (K SOME) (o1_policy all_capabilities)
      scalar_modular_program``
val scalar_modular_compile_eval = TRANS scalar_modular_compile_step0
  (EVAL (rhs (concl scalar_modular_compile_step0)))
val scalar_modular_oracle_eq = EQT_ELIM (EVAL (mk_eq
  (rhs (concl scalar_modular_compile_eval),
   ``SOME ^(evalCompilerBytecodeLib.read_hex_bytes "scalar_modular.hex")``)))
val scalar_modular_matches_python_oracle = save_thm
  ("scalar_modular_matches_python_oracle",
   TRANS scalar_modular_compile_eval scalar_modular_oracle_eq)
