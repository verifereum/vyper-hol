(* Exact staged Python-oracle bytecode check for static ABI encode/decode. *)

Theory evalCompilerBytecodeAbiStatic
Ancestors evalCompilerSubsetAbiBuiltins compileVyper concretizeMemLocDefs stackPlanGenCompute alist byte integer_word option cv_std
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps [".."]
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])
val () = computeLib.upd_compset
  (fn cs => cs
    |> (fn cs' => computeLib.scrub_const cs' ``reduce_depth_plan``)
    |> (fn cs' => computeLib.scrub_const cs'
         ``generate_block_insts_plan``)
    |> computeLib.add_thms
         [reduce_depth_plan_compute, generate_block_insts_plan_compute])
val () = Globals.max_print_depth := 20

Definition abi_static_n2w_def[nocompute]:
  abi_static_n2w n : bytes32 = n2w n
End

Theorem word_of_bytes_be_bytes32_abi_static:
  (word_of_bytes_be bs : bytes32) =
    abi_static_n2w
      (num_of_bytes (be_bytes (dimindex (:256) DIV 8) [] bs))
Proof
  PURE_REWRITE_TAC[abi_static_n2w_def] >>
  irule word_of_bytes_be_eq_num_of_bytes >> EVAL_TAC
QED

Theorem w2n_abi_static_n2w[compute]:
  w2n (abi_static_n2w n) = n MOD dimword (:256)
Proof
  simp[abi_static_n2w_def]
QED

Theorem get_byte_set_byte_bytes32_abi_static:
  get_byte a (set_byte a b (w : bytes32) be) be = b
Proof
  simp[byteTheory.get_byte_set_byte]
QED

Theorem get_byte_set_byte_irrelevant_bytes32_abi_static:
  w2n (a : bytes32) MOD 32 <> w2n a' MOD 32 ==>
  get_byte a' (set_byte a b (w : bytes32) be) be = get_byte a' w be
Proof
  simp[byteTheory.get_byte_set_byte_irrelevant]
QED

Theorem word_to_bytes_be_bytes32_genlist_abi_static:
  word_to_bytes_be (w : bytes32) =
    GENLIST (λi. get_byte (n2w i) w T) 32
Proof
  simp[listTheory.LIST_EQ_REWRITE, byteTheory.word_to_bytes_be_def,
       byteTheory.word_to_bytes_def, byteTheory.EL_word_to_bytes_aux]
QED

Theorem word_of_bytes_be_word_to_bytes_be_abi_static:
  word_of_bytes_be (word_to_bytes_be (w : bytes32)) = w
Proof
  simp[byteTheory.word_to_bytes_be_def, byteTheory.word_of_bytes_be_def,
       byteTheory.word_of_bytes_word_to_bytes]
QED

val () = computeLib.upd_compset (computeLib.add_thms
  [word_of_bytes_be_bytes32_abi_static, w2n_abi_static_n2w])

val abi_static_policy_eval = save_thm
  ("abi_static_policy_eval",
   EVAL ``resolve_o1_policy (o1_policy all_capabilities)``)
val abi_static_rpolicy = optionSyntax.dest_some
  (rhs (concl abi_static_policy_eval))
val abi_static_lower_runtime_eval = save_thm
  ("abi_static_lower_runtime_eval",
   EVAL ``lower_vyper_runtime_unit task090_abi_static_program
       ^abi_static_rpolicy``)
val abi_static_runtime_unit = optionSyntax.dest_some
  (rhs (concl abi_static_lower_runtime_eval))
Theorem abi_static_lower_runtime_computed: T
Proof
  simp[]
QED
val abi_static_pre_walk_eval = save_thm
  ("abi_static_pre_walk_eval",
   EVAL ``run_pipeline_stages ^abi_static_rpolicy
       o1_pipeline_spec.ps_pre_walk_stages ^abi_static_runtime_unit
       (init_ir_supply ^abi_static_runtime_unit)``)
Theorem abi_static_pre_walk_computed: T
Proof
  simp[]
QED
val abi_static_pre_pair = optionSyntax.dest_some
  (rhs (concl abi_static_pre_walk_eval))
val abi_static_pre_unit = #1 (pairSyntax.dest_pair abi_static_pre_pair)
val abi_static_pre_supply = #2 (pairSyntax.dest_pair abi_static_pre_pair)
val abi_static_fcg_eval = EVAL
  ``fcg_analyze (^abi_static_pre_unit).cu_context``
val abi_static_walk_unit_eval = EVAL
  ``prune_unit_fcg_unreachable ^abi_static_pre_unit
      ^(rhs (concl abi_static_fcg_eval))``
val abi_static_walk_unit = rhs (concl abi_static_walk_unit_eval)
val abi_static_entry_eval = EVAL
  ``(^abi_static_pre_unit).cu_context.ctx_entry``
val abi_static_entry = optionSyntax.dest_some
  (rhs (concl abi_static_entry_eval))
val abi_static_order_eval = EVAL
  ``fcg_postorder ^(rhs (concl abi_static_fcg_eval)) ^abi_static_entry``
val abi_static_walk_eval = save_thm
  ("abi_static_walk_eval",
   EVAL ``run_callee_first ^abi_static_rpolicy o1_fn_passes
       ^(rhs (concl abi_static_order_eval)) ^abi_static_walk_unit
       ^abi_static_pre_supply``)
Theorem abi_static_walk_computed: T
Proof
  simp[]
QED
val abi_static_walk_pair = optionSyntax.dest_some
  (rhs (concl abi_static_walk_eval))
val abi_static_walked_unit = #1 (pairSyntax.dest_pair abi_static_walk_pair)
val abi_static_walked_supply = #2 (pairSyntax.dest_pair abi_static_walk_pair)
val abi_static_post_walk_eval = save_thm
  ("abi_static_post_walk_eval",
   EVAL ``run_pipeline_stages ^abi_static_rpolicy
       o1_pipeline_spec.ps_post_walk_stages ^abi_static_walked_unit
       ^abi_static_walked_supply``)
Theorem abi_static_post_walk_computed: T
Proof
  simp[]
QED
val abi_static_post_pair = optionSyntax.dest_some
  (rhs (concl abi_static_post_walk_eval))
val abi_static_final_checked_unit = #1 (pairSyntax.dest_pair abi_static_post_pair)
val abi_static_final_supply = #2 (pairSyntax.dest_pair abi_static_post_pair)
val abi_static_initial_checks_eval = EVAL
  ``pipeline_spec_wf ^abi_static_rpolicy o1_pipeline_spec /\
    unit_wf ^abi_static_runtime_unit /\
    raw_static_inputs_wf (^abi_static_runtime_unit).cu_context``
val abi_static_pre_acyclic_eval = EVAL
  ``reachable_fcg_acyclic (^abi_static_pre_unit).cu_context
      ^(rhs (concl abi_static_fcg_eval))``
val abi_static_final_unit_wf = save_thm
  ("abi_static_final_unit_wf", EQT_ELIM
    (EVAL ``unit_wf ^abi_static_final_checked_unit``))
val abi_static_final_labels_wf = save_thm
  ("abi_static_final_labels_wf", EQT_ELIM
    (EVAL ``unit_labels_wf ^abi_static_final_checked_unit``))
val abi_static_final_target_safe = save_thm
  ("abi_static_final_target_safe", EQT_ELIM
    (EVAL ``context_target_safe (^abi_static_rpolicy).rpol_target
      (^abi_static_final_checked_unit).cu_context``))
val abi_static_final_layout_wf = save_thm
  ("abi_static_final_layout_wf", EQT_ELIM
    (EVAL ``concretized_static_layouts_wf
      (^abi_static_final_checked_unit).cu_context``))
val abi_static_final_fmp_wf = save_thm
  ("abi_static_final_fmp_wf", EQT_ELIM
    (EVAL ``fmp_lowered_context_wf
      (^abi_static_final_checked_unit).cu_context``))
val abi_static_final_acyclic = save_thm
  ("abi_static_final_acyclic", EQT_ELIM
    (EVAL ``reachable_fcg_acyclic
      (^abi_static_final_checked_unit).cu_context
      (fcg_analyze (^abi_static_final_checked_unit).cu_context)``))
val abi_static_final_codegen_ready = save_thm
  ("abi_static_final_codegen_ready", EQT_ELIM
    (EVAL ``codegen_ready (^abi_static_final_checked_unit).cu_context``))
val abi_static_final_checks_eval = save_thm
  ("abi_static_final_checks_eval", EQT_INTRO (LIST_CONJ
    [abi_static_final_unit_wf, abi_static_final_labels_wf,
     abi_static_final_target_safe, abi_static_final_layout_wf,
     abi_static_final_fmp_wf, abi_static_final_acyclic,
     abi_static_final_codegen_ready]))
Theorem abi_static_final_checks_computed: T
Proof
  simp[]
QED
val abi_static_spec_pre_eval = EVAL
  ``o1_pipeline_spec.ps_pre_walk_stages``
val abi_static_spec_prune_eval = EVAL
  ``o1_pipeline_spec.ps_prune_unreachable``
val abi_static_spec_acyclic_eval = EVAL
  ``o1_pipeline_spec.ps_require_acyclic_calls``
val abi_static_spec_passes_eval = SIMP_CONV (srw_ss())
  [venomPassScheduleTheory.o1_pipeline_spec_def]
  ``o1_pipeline_spec.ps_fn_passes``
val abi_static_spec_post_eval = EVAL
  ``o1_pipeline_spec.ps_post_walk_stages``
val abi_static_spec_final_asm_eval = EVAL
  ``o1_pipeline_spec.ps_final_assembly``
val abi_static_initial_check_rules = map EQT_INTRO
  (CONJUNCTS (EQT_ELIM abi_static_initial_checks_eval))
val abi_static_final_check_rules = map EQT_INTRO
  (CONJUNCTS (EQT_ELIM abi_static_final_checks_eval))
val abi_static_pipeline_rules =
  abi_static_initial_check_rules @
  [abi_static_pre_walk_eval, abi_static_spec_pre_eval,
   abi_static_fcg_eval, abi_static_spec_prune_eval,
   abi_static_walk_unit_eval, abi_static_spec_acyclic_eval,
   abi_static_pre_acyclic_eval, abi_static_entry_eval,
   abi_static_spec_passes_eval, abi_static_order_eval,
   abi_static_walk_eval, abi_static_post_walk_eval,
   abi_static_spec_post_eval] @ abi_static_final_check_rules @
  [abi_static_spec_final_asm_eval]
val abi_static_admin_rules =
  [LET_THM, COND_CLAUSES, NOT_CLAUSES, boolTheory.AND_CLAUSES,
   combinTheory.K_THM, optionTheory.option_case_compute,
   optionTheory.IS_SOME_DEF,
   optionTheory.THE_DEF, pairTheory.pair_case_thm]
val abi_static_admin_rewrites = List.concat
  (map (CONJUNCTS o SPEC_ALL) abi_static_admin_rules)
val abi_static_admin_conv = FIRST_CONV
  (BETA_CONV :: map REWR_CONV abi_static_admin_rewrites)
fun abi_static_repeat_admin 0 tm = REFL tm
  | abi_static_repeat_admin n tm =
      (case total (ONCE_DEPTH_CONV abi_static_admin_conv) tm of
         NONE => REFL tm
       | SOME th => TRANS th
           (abi_static_repeat_admin (n - 1) (rhs (concl th))))
fun abi_static_apply_stage stage_th current =
  case total (ONCE_DEPTH_CONV (REWR_CONV stage_th)) (rhs (concl current)) of
    NONE => current
  | SOME staged => let
      val admin = abi_static_repeat_admin 30 (rhs (concl staged))
    in TRANS current (TRANS staged admin) end
fun abi_static_apply_stages current [] = current
  | abi_static_apply_stages current (th::ths) =
      abi_static_apply_stages (abi_static_apply_stage th current) ths
val abi_static_run_pipeline_initial0 = SIMP_CONV pure_ss
  [venomPipelineDriverTheory.run_venom_pipeline_def]
  ``run_venom_pipeline (K T) (K T) (K T)
       ^abi_static_rpolicy o1_pipeline_spec ^abi_static_runtime_unit``
val abi_static_run_pipeline_initial = TRANS abi_static_run_pipeline_initial0
  (abi_static_repeat_admin 30
    (rhs (concl abi_static_run_pipeline_initial0)))
val abi_static_run_pipeline_eval = save_thm
  ("abi_static_run_pipeline_eval",
   abi_static_apply_stages abi_static_run_pipeline_initial
     abi_static_pipeline_rules)
Theorem abi_static_pipeline_computed: T
Proof
  simp[]
QED
val abi_static_pipeline_out = optionSyntax.dest_some
  (rhs (concl abi_static_run_pipeline_eval))
val abi_static_final_unit = rhs (concl (EVAL
  ``(^abi_static_pipeline_out).po_unit``))

val abi_static_max_eom_eval = save_thm
  ("abi_static_max_eom_eval", EVAL
    ``max_live_eom (^abi_static_final_unit).cu_context``)
val abi_static_max_eom = optionSyntax.dest_some
  (rhs (concl abi_static_max_eom_eval))
val abi_static_final_fn_eval = EVAL
  ``HD (^abi_static_final_unit).cu_context.ctx_functions``
val abi_static_final_fn = rhs (concl abi_static_final_fn_eval)
fun abi_static_w2n_eval w = let
  val bytes_th = SIMP_CONV (srw_ss())
    [word_to_bytes_be_bytes32_genlist_abi_static,
     get_byte_set_byte_bytes32_abi_static,
     get_byte_set_byte_irrelevant_bytes32_abi_static]
    ``word_to_bytes_be ^w``
  val roundtrip = INST [``w:bytes32`` |-> w]
    word_of_bytes_be_word_to_bytes_be_abi_static
  val step1 = BETA_RULE (AP_TERM ``λx:bytes32. w2n x`` (SYM roundtrip))
  val step2 = BETA_RULE (AP_TERM
    ``λbs. w2n (word_of_bytes_be bs : bytes32)`` bytes_th)
  val decoded = TRANS step1 step2
  val expose = SIMP_CONV bool_ss
    [word_of_bytes_be_bytes32_abi_static, w2n_abi_static_n2w]
    (rhs (concl decoded))
in
  TRANS decoded (TRANS expose (EVAL (rhs (concl expose))))
end
fun abi_static_normalize_word w = let
  val w2n_th = abi_static_w2n_eval w
  val numeral = rhs (concl w2n_th)
  val normalized = ``n2w ^numeral : bytes32``
  val normalized_w2n = EVAL ``w2n ^normalized``
  val same_num = TRANS w2n_th (SYM normalized_w2n)
in
  EQ_MP (ISPECL [w,normalized] wordsTheory.w2n_11) same_num
end
val abi_static_set_byte_words = List.foldl
  (fn (tm,ws) => if List.exists (aconv tm) ws then ws else tm::ws) []
  (find_terms (can (match_term ``set_byte a b w be : bytes32``))
    abi_static_final_fn)
val abi_static_word_normalizations =
  map abi_static_normalize_word abi_static_set_byte_words
val abi_static_final_fn_normalized_eval =
  if null abi_static_word_normalizations then REFL abi_static_final_fn
  else PURE_REWRITE_CONV abi_static_word_normalizations abi_static_final_fn
val abi_static_final_fn_normalized =
  rhs (concl abi_static_final_fn_normalized_eval)
val abi_static_plan_canonical_eval = EVAL
  ``canonical_param_prefix ^abi_static_final_fn_normalized``
val abi_static_plan_live_eval = save_thm
  ("abi_static_plan_live_eval",
   EVAL ``liveness_analyze ^abi_static_final_fn_normalized``)
val abi_static_plan_dfg_eval = EVAL
  ``dfg_build_function ^abi_static_final_fn_normalized``
val abi_static_plan_cfg_eval = EVAL
  ``cfg_analyze ^abi_static_final_fn_normalized``
val abi_static_plan_entry_eval = EVAL
  ``fn_entry_label ^abi_static_final_fn_normalized``
val abi_static_plan_entry = optionSyntax.dest_some
  (rhs (concl abi_static_plan_entry_eval))
val abi_static_plan_initial_state_eval = EVAL
  ``(init_plan_state ^abi_static_max_eom) with ps_label_counter := 0``
val abi_static_plan_initial_state =
  rhs (concl abi_static_plan_initial_state_eval)
val abi_static_plan_aux_fuel_step1 = save_thm
  ("abi_static_plan_aux_fuel_step1",
   EVAL ``generate_fn_plan_aux_fuel 30
      ^(rhs (concl abi_static_plan_live_eval))
      ^(rhs (concl abi_static_plan_dfg_eval))
      ^(rhs (concl abi_static_plan_cfg_eval)) ^abi_static_final_fn_normalized
      [^abi_static_plan_entry] [] ^abi_static_plan_initial_state``)
Theorem abi_static_plan_aux_fuel_step1_computed: T
Proof
  simp[]
QED
val abi_static_plan_aux_fuel_eval = abi_static_plan_aux_fuel_step1
val abi_static_plan_aux_result = optionSyntax.dest_some
  (rhs (concl abi_static_plan_aux_fuel_eval))
val abi_static_plan_aux_sound = CONJUNCT1
  (SPEC ``30`` generate_plan_fuel_some)
val abi_static_plan_aux_eval = MATCH_MP
  (SPEC_ALL abi_static_plan_aux_sound)
  abi_static_plan_aux_fuel_eval
val abi_static_plan_analyzed_eval = save_thm
  ("abi_static_plan_analyzed_eval",
   SIMP_CONV (srw_ss())
    [stackPlanGenTheory.generate_fn_plan_analyzed_def,
     abi_static_plan_canonical_eval, abi_static_plan_entry_eval,
     abi_static_plan_initial_state_eval, abi_static_plan_aux_eval]
    ``generate_fn_plan_analyzed
        ^(rhs (concl abi_static_plan_live_eval))
        ^(rhs (concl abi_static_plan_dfg_eval))
        ^(rhs (concl abi_static_plan_cfg_eval))
        ^abi_static_final_fn_normalized ^abi_static_max_eom 0``)
val abi_static_fn_plan_step1 = REWR_CONV
  stackPlanGenTheory.generate_fn_plan_def
  ``generate_fn_plan ^abi_static_final_fn_normalized ^abi_static_max_eom 0``
val abi_static_fn_plan_step2 = PURE_REWRITE_CONV
  [abi_static_plan_live_eval, abi_static_plan_dfg_eval,
   abi_static_plan_cfg_eval]
  (rhs (concl abi_static_fn_plan_step1))
val abi_static_fn_plan_step3 = REWR_CONV abi_static_plan_analyzed_eval
  (rhs (concl abi_static_fn_plan_step2))
val abi_static_normalized_fn_plan_eval =
  TRANS abi_static_fn_plan_step1
    (TRANS abi_static_fn_plan_step2 abi_static_fn_plan_step3)
val abi_static_fn_plan_congruence = BETA_RULE (AP_TERM
  ``λfn. generate_fn_plan fn ^abi_static_max_eom 0``
  abi_static_final_fn_normalized_eval)
val abi_static_fn_plan_eval = save_thm
  ("abi_static_fn_plan_eval",
   TRANS abi_static_fn_plan_congruence abi_static_normalized_fn_plan_eval)
Theorem abi_static_fn_plan_computed: T
Proof
  simp[]
QED
val () = computeLib.upd_compset (computeLib.add_thms
  [abi_static_max_eom_eval, abi_static_fn_plan_eval])
val abi_static_context_plan_eval = save_thm
  ("abi_static_context_plan_eval",
   EVAL ``generate_context_plan (^abi_static_final_unit).cu_context``)
val abi_static_context_plan = optionSyntax.dest_some
  (rhs (concl abi_static_context_plan_eval))
val abi_static_plan_ops_eval = EVAL
  ``context_plan_ops ^abi_static_context_plan``
val abi_static_initial_fmp_eval = EVAL
  ``(^abi_static_context_plan).cp_initial_fmp``
val abi_static_execute_plan_eval = save_thm
  ("abi_static_execute_plan_eval",
   EVAL ``execute_plan ^(rhs (concl abi_static_initial_fmp_eval))
       ^(rhs (concl abi_static_plan_ops_eval))``)
val abi_static_data_asm_eval = EVAL
  ``data_segment_asm (^abi_static_final_unit).cu_data_segment``
val abi_static_raw_asm_eval = EVAL
  ``^(rhs (concl abi_static_execute_plan_eval)) ++
    ^(rhs (concl abi_static_data_asm_eval)) ++ [AsmDataHeader "code_end"]``
val abi_static_raw_asm = rhs (concl abi_static_raw_asm_eval)
val abi_static_target_wf_eval = EVAL
  ``target_capabilities_wf (^abi_static_rpolicy).rpol_target``
val abi_static_context_safe_eval = EVAL
  ``context_target_safe (^abi_static_rpolicy).rpol_target
      (^abi_static_final_unit).cu_context``
val abi_static_assembly_safe_eval = EVAL
  ``assembly_target_safe (^abi_static_rpolicy).rpol_target
      ^abi_static_raw_asm``
val abi_static_codegen_step0 = SIMP_CONV pure_ss
  [codegenTheory.codegen_assembly_def, abi_static_target_wf_eval,
   abi_static_context_safe_eval, abi_static_context_plan_eval,
   optionTheory.option_case_compute, optionTheory.IS_SOME_DEF,
   optionTheory.THE_DEF, LET_THM, NOT_CLAUSES, COND_CLAUSES]
  ``codegen_assembly ^abi_static_rpolicy ^abi_static_final_unit``
val abi_static_codegen_step1 = SIMP_CONV pure_ss
  [abi_static_plan_ops_eval, abi_static_initial_fmp_eval,
   abi_static_execute_plan_eval, abi_static_data_asm_eval,
   abi_static_raw_asm_eval, abi_static_assembly_safe_eval]
  (rhs (concl abi_static_codegen_step0))
val abi_static_codegen_eval = save_thm
  ("abi_static_codegen_eval",
   TRANS abi_static_codegen_step0
     (TRANS abi_static_codegen_step1
       (EVAL (rhs (concl abi_static_codegen_step1)))))
val abi_static_finalize_step0 =
  REWR_CONV codegenTheory.finalize_codegen_identity
    ``finalize_codegen (K SOME) ^abi_static_rpolicy ^abi_static_final_unit``
val abi_static_finalize_step1 = PURE_REWRITE_CONV
  [abi_static_codegen_eval] (rhs (concl abi_static_finalize_step0))
val abi_static_finalize_eval = save_thm
  ("abi_static_finalize_eval",
   TRANS abi_static_finalize_step0
     (TRANS abi_static_finalize_step1
       (EVAL (rhs (concl abi_static_finalize_step1)))))
val abi_static_runtime_bytes = optionSyntax.dest_some
  (rhs (concl abi_static_finalize_eval))

val abi_static_lower_deploy_eval = save_thm
  ("abi_static_lower_deploy_eval",
   EVAL ``lower_vyper_deploy_unit task090_abi_static_program
       ^abi_static_rpolicy ^abi_static_runtime_bytes``)
val abi_static_deploy_unit = optionSyntax.dest_some
  (rhs (concl abi_static_lower_deploy_eval))
val abi_static_deploy_pipeline_eval = save_thm
  ("abi_static_deploy_pipeline_eval",
   EVAL ``run_venom_pipeline (K T) (K T) (K T)
       ^abi_static_rpolicy o1_pipeline_spec ^abi_static_deploy_unit``)
val abi_static_deploy_out = optionSyntax.dest_some
  (rhs (concl abi_static_deploy_pipeline_eval))
val abi_static_final_deploy_unit = rhs (concl (EVAL
  ``(^abi_static_deploy_out).po_unit``))
val abi_static_finalize_deploy_eval = save_thm
  ("abi_static_finalize_deploy_eval",
   EVAL ``finalize_codegen (K SOME) ^abi_static_rpolicy
       ^abi_static_final_deploy_unit``)

val abi_static_compile_term =
  ``compile_vyper (K SOME) (o1_policy all_capabilities)
      task090_abi_static_program``
val abi_static_compile_step0 = SIMP_CONV pure_ss
  [compileVyperTheory.compile_vyper_def,
   compileVyperTheory.compile_vyper_with_def,
   compileVyperTheory.checked_unit_pipeline_def,
   optionTheory.option_case_def, boolTheory.COND_CLAUSES,
   abi_static_policy_eval, abi_static_lower_runtime_eval,
   abi_static_run_pipeline_eval, abi_static_finalize_eval,
   abi_static_lower_deploy_eval, abi_static_deploy_pipeline_eval,
   abi_static_finalize_deploy_eval, LET_THM, pairTheory.FST,
   pairTheory.SND, pairTheory.UNCURRY_DEF, pairTheory.pair_case_def]
  abi_static_compile_term
val abi_static_compile_eval = TRANS abi_static_compile_step0
  (EVAL (rhs (concl abi_static_compile_step0)))
val abi_static_compile_eval = save_thm
  ("abi_static_compile_eval", abi_static_compile_eval)
Theorem abi_static_compile_computed: T
Proof
  simp[]
QED
val abi_static_oracle_eq = EQT_ELIM (EVAL (mk_eq
  (rhs (concl abi_static_compile_eval),
   ``SOME ^(evalCompilerBytecodeLib.read_hex_bytes "abi_static.hex")``)))
val abi_static_matches_python_oracle = save_thm
  ("abi_static_matches_python_oracle",
   TRANS abi_static_compile_eval abi_static_oracle_eq)
